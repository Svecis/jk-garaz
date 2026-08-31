const http = require('http');
const https = require('https');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const nodemailer = require('nodemailer');
const QRCode = require('qrcode');

const PORT = 3000;
const PUBLIC_BASE_URL = 'https://test.sveckys.top';
const CONFIG_FILE = path.join(__dirname, 'email_config.json');
const AUTH_FILE = path.join(__dirname, 'admin_auth.json');
const BOOKINGS_FILE = path.join(__dirname, 'bookings.json');
const TOKEN_TTL_MS = 12 * 60 * 60 * 1000; // 12 hodín

// Server-side rate limiting for new public bookings (the client-side 15s cooldown
// in index.html is trivially bypassed by clearing localStorage / using a new tab).
const BOOKING_RATE_SHORT_WINDOW_MS = 60 * 1000; // 1 minute
const BOOKING_RATE_SHORT_MAX = 1; // max 1 new booking per IP per minute
const BOOKING_RATE_LONG_WINDOW_MS = 60 * 60 * 1000; // 1 hour
const BOOKING_RATE_LONG_MAX = 5; // max 5 new bookings per IP per hour
const bookingRateLimiter = new Map(); // ip -> array of request timestamps

function getClientIp(req) {
  const xff = req.headers['x-forwarded-for'];
  if (xff) return xff.split(',')[0].trim();
  return req.socket.remoteAddress || 'unknown';
}

function isBookingRateLimited(ip) {
  const now = Date.now();
  let timestamps = (bookingRateLimiter.get(ip) || []).filter(t => now - t < BOOKING_RATE_LONG_WINDOW_MS);

  const recentShort = timestamps.filter(t => now - t < BOOKING_RATE_SHORT_WINDOW_MS);
  if (recentShort.length >= BOOKING_RATE_SHORT_MAX || timestamps.length >= BOOKING_RATE_LONG_MAX) {
    bookingRateLimiter.set(ip, timestamps);
    return true;
  }

  timestamps.push(now);
  bookingRateLimiter.set(ip, timestamps);
  return false;
}

// Periodically drop IPs with no requests in the last hour so this Map doesn't grow forever
setInterval(() => {
  const now = Date.now();
  for (const [ip, timestamps] of bookingRateLimiter) {
    const fresh = timestamps.filter(t => now - t < BOOKING_RATE_LONG_WINDOW_MS);
    if (fresh.length === 0) bookingRateLimiter.delete(ip);
    else bookingRateLimiter.set(ip, fresh);
  }
}, 15 * 60 * 1000).unref();

// =====================================================================
// AT-REST ENCRYPTION (AES-256-GCM) — used for email_config.json and
// bookings.json, both of which hold secrets / customer PII.
// =====================================================================
function encryptJson(obj, keyHex) {
  const key = Buffer.from(keyHex, 'hex');
  const iv = crypto.randomBytes(12);
  const cipher = crypto.createCipheriv('aes-256-gcm', key, iv);
  const plaintext = Buffer.from(JSON.stringify(obj), 'utf8');
  const encrypted = Buffer.concat([cipher.update(plaintext), cipher.final()]);
  const tag = cipher.getAuthTag();
  return { v: 1, iv: iv.toString('hex'), tag: tag.toString('hex'), data: encrypted.toString('hex') };
}

function decryptJson(payload, keyHex) {
  const key = Buffer.from(keyHex, 'hex');
  const iv = Buffer.from(payload.iv, 'hex');
  const tag = Buffer.from(payload.tag, 'hex');
  const decipher = crypto.createDecipheriv('aes-256-gcm', key, iv);
  decipher.setAuthTag(tag);
  const decrypted = Buffer.concat([decipher.update(Buffer.from(payload.data, 'hex')), decipher.final()]);
  return JSON.parse(decrypted.toString('utf8'));
}

function isEncryptedPayload(obj) {
  return !!(obj && typeof obj === 'object' &&
    obj.v === 1 && typeof obj.iv === 'string' && typeof obj.tag === 'string' && typeof obj.data === 'string');
}

// =====================================================================
// ADMIN AUTH: password hashing, TOTP 2FA, signed session tokens
// =====================================================================
const BASE32_ALPHABET = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567';

function base32Encode(buffer) {
  let bits = 0, value = 0, output = '';
  for (const byte of buffer) {
    value = (value << 8) | byte;
    bits += 8;
    while (bits >= 5) {
      output += BASE32_ALPHABET[(value >>> (bits - 5)) & 31];
      bits -= 5;
    }
  }
  if (bits > 0) output += BASE32_ALPHABET[(value << (5 - bits)) & 31];
  return output;
}

function base32Decode(str) {
  str = str.toUpperCase().replace(/=+$/, '');
  let bits = 0, value = 0;
  const bytes = [];
  for (const ch of str) {
    const idx = BASE32_ALPHABET.indexOf(ch);
    if (idx === -1) continue;
    value = (value << 5) | idx;
    bits += 5;
    if (bits >= 8) {
      bytes.push((value >>> (bits - 8)) & 0xff);
      bits -= 8;
    }
  }
  return Buffer.from(bytes);
}

function generateTotpSecret() {
  return base32Encode(crypto.randomBytes(20));
}

function totpCodeForCounter(secretBase32, counter) {
  const key = base32Decode(secretBase32);
  const buf = Buffer.alloc(8);
  buf.writeUInt32BE(Math.floor(counter / 0x100000000), 0);
  buf.writeUInt32BE(counter >>> 0, 4);
  const hmac = crypto.createHmac('sha1', key).update(buf).digest();
  const offset = hmac[hmac.length - 1] & 0xf;
  const code = ((hmac[offset] & 0x7f) << 24 |
    (hmac[offset + 1] & 0xff) << 16 |
    (hmac[offset + 2] & 0xff) << 8 |
    (hmac[offset + 3] & 0xff)) % 1000000;
  return String(code).padStart(6, '0');
}

// Accepts a code from the current or adjacent 30s time-step to tolerate clock drift
function totpVerify(secretBase32, token) {
  if (!token || !/^\d{6}$/.test(token)) return false;
  const counter = Math.floor(Date.now() / 1000 / 30);
  for (let drift = -1; drift <= 1; drift++) {
    if (totpCodeForCounter(secretBase32, counter + drift) === token) return true;
  }
  return false;
}

function hashPassword(password, salt) {
  return crypto.scryptSync(password, salt, 64).toString('hex');
}

function verifyPasswordMatch(password, salt, expectedHash) {
  const provided = Buffer.from(hashPassword(password, salt), 'hex');
  const expected = Buffer.from(expectedHash, 'hex');
  return provided.length === expected.length && crypto.timingSafeEqual(provided, expected);
}

function b64url(buf) {
  return Buffer.from(buf).toString('base64').replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}

function b64urlToBuffer(str) {
  str = str.replace(/-/g, '+').replace(/_/g, '/');
  while (str.length % 4) str += '=';
  return Buffer.from(str, 'base64');
}

function signToken(payload, secret) {
  const body = b64url(JSON.stringify(payload));
  const sig = b64url(crypto.createHmac('sha256', secret).update(body).digest());
  return body + '.' + sig;
}

function verifyToken(token, secret) {
  if (!token || typeof token !== 'string' || !token.includes('.')) return null;
  const [body, sig] = token.split('.');
  const expectedSig = b64url(crypto.createHmac('sha256', secret).update(body).digest());
  const sigBuf = Buffer.from(sig);
  const expectedBuf = Buffer.from(expectedSig);
  if (sigBuf.length !== expectedBuf.length || !crypto.timingSafeEqual(sigBuf, expectedBuf)) return null;
  try {
    const payload = JSON.parse(b64urlToBuffer(body).toString('utf8'));
    if (!payload.exp || Date.now() > payload.exp) return null;
    return payload;
  } catch (e) {
    return null;
  }
}

function maskEmail(email) {
  const [user, domain] = email.split('@');
  if (!domain) return email;
  const visible = user.slice(0, 1);
  return visible + '***@' + domain;
}

function loadOrCreateAdminAuth() {
  if (fs.existsSync(AUTH_FILE)) {
    try {
      const parsed = JSON.parse(fs.readFileSync(AUTH_FILE, 'utf8'));
      // Back-fill the at-rest encryption key for auth files created before it existed
      if (!parsed.dataKey) {
        parsed.dataKey = crypto.randomBytes(32).toString('hex');
        fs.writeFileSync(AUTH_FILE, JSON.stringify(parsed, null, 2), 'utf8');
      }
      return parsed;
    } catch (e) {}
  }
  const initialPassword = crypto.randomBytes(6).toString('hex');
  const salt = crypto.randomBytes(16).toString('hex');
  const auth = {
    passwordSalt: salt,
    passwordHash: hashPassword(initialPassword, salt),
    totpSecret: null,
    totpEnabled: false,
    recoveryEmail: null,
    resetCode: null,
    resetCodeExpiry: null,
    jwtSecret: crypto.randomBytes(32).toString('hex'),
    dataKey: crypto.randomBytes(32).toString('hex')
  };
  fs.writeFileSync(AUTH_FILE, JSON.stringify(auth, null, 2), 'utf8');
  console.log('\n=====================================================');
  console.log(' PRVOTNÉ ADMIN HESLO (uložte si ho, zmeňte pri prvom prihlásení):');
  console.log(' ' + initialPassword);
  console.log('=====================================================\n');
  return auth;
}

let adminAuth = loadOrCreateAdminAuth();
function saveAdminAuth() {
  fs.writeFileSync(AUTH_FILE, JSON.stringify(adminAuth, null, 2), 'utf8');
}

// Simple in-memory brute-force guard for the login endpoint
const loginAttempts = new Map();
function isLockedOut(ip) {
  const entry = loginAttempts.get(ip);
  return !!(entry && entry.lockUntil && entry.lockUntil > Date.now());
}
function registerFailedAttempt(ip) {
  const entry = loginAttempts.get(ip) || { count: 0, lockUntil: 0 };
  entry.count += 1;
  if (entry.count >= 5) {
    entry.lockUntil = Date.now() + 5 * 60 * 1000;
    entry.count = 0;
  }
  loginAttempts.set(ip, entry);
}
function clearAttempts(ip) {
  loginAttempts.delete(ip);
}

function getBearerToken(req) {
  const header = req.headers['authorization'] || '';
  const match = header.match(/^Bearer\s+(.+)$/i);
  return match ? match[1] : null;
}

// Writes a 401 response and returns null if the request isn't authenticated,
// otherwise returns the decoded token payload.
function requireAuth(req, res) {
  const token = getBearerToken(req);
  const payload = token ? verifyToken(token, adminAuth.jwtSecret) : null;
  if (!payload) {
    res.writeHead(401, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({ error: 'Unauthorized' }));
    return null;
  }
  return payload;
}

// =====================================================================
// BOOKINGS PERSISTENCE (bookings.json, encrypted at rest — contains
// customer PII: name, phone, e-mail, license plate, photos, audio)
// =====================================================================
function loadBookings() {
  if (!fs.existsSync(BOOKINGS_FILE)) return [];
  try {
    const parsed = JSON.parse(fs.readFileSync(BOOKINGS_FILE, 'utf8'));
    if (isEncryptedPayload(parsed)) return decryptJson(parsed, adminAuth.dataKey);
    if (Array.isArray(parsed)) return parsed; // legacy plaintext file — re-encrypted on next save
    return [];
  } catch (e) {
    return [];
  }
}

function saveBookings(bookings) {
  fs.writeFileSync(BOOKINGS_FILE, JSON.stringify(encryptJson(bookings, adminAuth.dataKey), null, 2), 'utf8');
}

// =====================================================================
// E-MAIL CONFIG (email_config.json, encrypted at rest — holds the
// Brevo API key / SMTP password)
// =====================================================================
let emailConfig = {
  provider: 'brevo', // 'brevo' or 'custom_smtp'
  recipientEmail: 'servis@automek.sk',
  brevo: {
    senderEmail: '',
    fromEmail: '',
    apiKey: ''
  },
  smtp: {
    host: 'smtp-relay.brevo.com',
    port: 587,
    secure: false,
    auth: {
      user: '',
      pass: ''
    }
  }
};

function saveConfig() {
  try {
    fs.writeFileSync(CONFIG_FILE, JSON.stringify(encryptJson(emailConfig, adminAuth.dataKey), null, 2), 'utf8');
  } catch (e) {
    console.error('Error saving config:', e);
  }
}

if (fs.existsSync(CONFIG_FILE)) {
  try {
    const parsed = JSON.parse(fs.readFileSync(CONFIG_FILE, 'utf8'));
    if (isEncryptedPayload(parsed)) {
      emailConfig = { ...emailConfig, ...decryptJson(parsed, adminAuth.dataKey) };
    } else {
      // Legacy plaintext config from before encryption-at-rest was added — load it once, then re-save encrypted
      emailConfig = { ...emailConfig, ...parsed };
      console.log('[CONFIG] email_config.json bol v čitateľnom formáte — šifrujem ho na disku.');
      saveConfig();
    }
  } catch (e) {}
}

const MIME_TYPES = {
  '.html': 'text/html; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.js': 'application/javascript; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.jpeg': 'image/jpeg',
  '.svg': 'image/svg+xml',
  '.webp': 'image/webp',
  '.wav': 'audio/wav',
  '.mp3': 'audio/mpeg',
  '.ico': 'image/x-icon'
};

// Build the HTML body for a new-booking notification e-mail
function buildBookingEmailHtml(booking) {
  const plateFormatted = (booking.plate || '-').replace(/-/g, ' ').replace(/\s+/g, ' ').trim();
  const orderUrl = PUBLIC_BASE_URL + '/order.html?id=' + encodeURIComponent(booking.id);

  return `
      <div style="font-family:Arial,sans-serif; max-width:600px; margin:0 auto; padding:20px; border:1px solid #e2e8f0; border-radius:10px; background:#ffffff;">
        <h2 style="color:#0f172a; margin-top:0;">Nová servisná zákazka #${booking.id}</h2>
        <p style="color:#64748b; font-size:14px;">Zákazka bola prijatá cez online servisný systém AutoMek.</p>
        <hr style="border:none; border-top:1px solid #e2e8f0; margin:16px 0;" />
        <table style="width:100%; font-size:14px; border-collapse:collapse;">
          <tr><td style="padding:6px 0; color:#64748b; width:140px;"><strong>Zákazník:</strong></td><td style="color:#0f172a;">${booking.customer || '-'}</td></tr>
          <tr><td style="padding:6px 0; color:#64748b;"><strong>Telefón:</strong></td><td style="color:#0f172a;"><a href="tel:${booking.phone}" style="color:#2563eb;">${booking.phone || '-'}</a></td></tr>
          <tr><td style="padding:6px 0; color:#64748b;"><strong>Email:</strong></td><td style="color:#0f172a;">${booking.email || '-'}</td></tr>
          <tr><td style="padding:6px 0; color:#64748b;"><strong>EČV Vozidla:</strong></td><td style="color:#0f172a; font-family:monospace; font-weight:bold;">${plateFormatted}</td></tr>
          <tr><td style="padding:6px 0; color:#64748b;"><strong>Diel:</strong></td><td style="color:#2563eb; font-weight:bold;">[${booking.partCode || 'P'}] ${booking.partName || '-'}</td></tr>
          <tr><td style="padding:6px 0; color:#64748b;"><strong>Termín:</strong></td><td style="color:#0f172a;">${booking.date || '-'} o ${booking.time || '-'}</td></tr>
          <tr><td style="padding:6px 0; color:#64748b;"><strong>Odhadovaná cena:</strong></td><td style="color:#10b981; font-weight:bold;">${booking.price || '-'}</td></tr>
          <tr><td style="padding:6px 0; color:#64748b;"><strong>Popis závady:</strong></td><td style="color:#334155; font-style:italic;">„${booking.problemDesc || 'Bez dodatočného popisu'}“</td></tr>
        </table>
        <div style="margin-top:24px; text-align:center;">
          <a href="${orderUrl}" style="background:#2563eb; color:#ffffff; padding:12px 24px; text-decoration:none; border-radius:6px; font-weight:bold; font-size:14px; display:inline-block;">Otvoriť kartu zákazky v systéme</a>
        </div>
      </div>
    `;
}

// Send an arbitrary e-mail via Brevo HTTP API
function sendViaBrevoApi(apiKey, fromEmail, recipientEmail, subject, htmlContent) {
  return new Promise((resolve, reject) => {
    const payload = JSON.stringify({
      sender: { name: "AutoMek Servis", email: fromEmail },
      to: [{ email: recipientEmail }],
      subject: subject,
      htmlContent: htmlContent
    });

    const options = {
      hostname: 'api.brevo.com',
      port: 443,
      path: '/v3/smtp/email',
      method: 'POST',
      headers: {
        'api-key': apiKey,
        'Content-Type': 'application/json',
        'Accept': 'application/json',
        'Content-Length': Buffer.byteLength(payload)
      }
    };

    const req = https.request(options, (res) => {
      let data = '';
      res.on('data', chunk => { data += chunk; });
      res.on('end', () => {
        try {
          const parsed = JSON.parse(data);
          if (res.statusCode >= 200 && res.statusCode < 300) {
            resolve({ success: true, messageId: parsed.messageId });
          } else {
            reject(new Error(parsed.message || ('HTTP ' + res.statusCode + ': ' + data)));
          }
        } catch (e) {
          if (res.statusCode >= 200 && res.statusCode < 300) resolve({ success: true });
          else reject(new Error('HTTP ' + res.statusCode + ': ' + data));
        }
      });
    });

    req.on('error', (err) => reject(err));
    req.write(payload);
    req.end();
  });
}

// Send an arbitrary e-mail via Brevo SMTP (Nodemailer)
// `login` authenticates to the SMTP relay; `fromEmail` is the verified sender shown in the From: header —
// Brevo treats these as two different things and rejects sends where an unverified address is used as sender.
function sendViaBrevoSmtp(login, key, fromEmail, recipientEmail, subject, htmlContent) {
  const transporter = nodemailer.createTransport({
    host: 'smtp-relay.brevo.com',
    port: 587,
    secure: false,
    auth: {
      user: login,
      pass: key
    }
  });

  return transporter.sendMail({
    from: '"AutoMek Servis" <' + fromEmail + '>',
    to: recipientEmail,
    subject: subject,
    html: htmlContent
  });
}

// Generic e-mail dispatcher: tries Brevo HTTP API first, falls back to SMTP
async function sendEmailGeneric(recipient, subject, htmlContent) {
  const brevoKey = (emailConfig.brevo && emailConfig.brevo.apiKey ? emailConfig.brevo.apiKey : (emailConfig.smtp && emailConfig.smtp.auth ? emailConfig.smtp.auth.pass : '')).trim();
  const brevoLogin = (emailConfig.brevo && emailConfig.brevo.senderEmail ? emailConfig.brevo.senderEmail : (emailConfig.smtp && emailConfig.smtp.auth ? emailConfig.smtp.auth.user : '')).trim();
  // The verified "From" address — falls back to the login for accounts where they're the same
  const fromEmail = ((emailConfig.brevo && emailConfig.brevo.fromEmail) || brevoLogin).trim();

  if (brevoKey && brevoLogin) {
    try {
      // First try Brevo HTTP API (fastest, never blocked by ports)
      return await sendViaBrevoApi(brevoKey, fromEmail, recipient, subject, htmlContent);
    } catch (apiErr) {
      console.warn('[BREVO API error, trying SMTP fallback]:', apiErr.message);
      // Fallback to Brevo SMTP
      return await sendViaBrevoSmtp(brevoLogin, brevoKey, fromEmail, recipient, subject, htmlContent);
    }
  } else {
    throw new Error('Neboli zadané prihlasovacie údaje pre Brevo (Email a API/SMTP kľúč).');
  }
}

// Booking-specific notification
function dispatchNotification(recipient, booking) {
  const plateFormatted = (booking.plate || '-').replace(/-/g, ' ').replace(/\s+/g, ' ').trim();
  const subject = 'AutoMek: Nová zákazka #' + booking.id + ' - ' + (booking.customer || 'Klient') + ' (' + plateFormatted + ')';
  return sendEmailGeneric(recipient, subject, buildBookingEmailHtml(booking));
}

// Build the HTML body for the customer-facing booking confirmation e-mail.
// Intentionally has no link back into the admin system (order.html) — that
// button is only for the internal shop notification in buildBookingEmailHtml.
// The manage link below is a separate, customer-scoped page gated by a random
// per-booking token, not the admin order card.
function buildCustomerConfirmationEmailHtml(booking) {
  const plateFormatted = (booking.plate || '-').replace(/-/g, ' ').replace(/\s+/g, ' ').trim();
  const manageUrl = PUBLIC_BASE_URL + '/moja-rezervacia.html?id=' + encodeURIComponent(booking.id) + '&token=' + encodeURIComponent(booking.manageToken || '');

  return `
      <div style="font-family:Arial,sans-serif; max-width:600px; margin:0 auto; padding:20px; border:1px solid #e2e8f0; border-radius:10px; background:#ffffff;">
        <h2 style="color:#0f172a; margin-top:0;">Rezervácia prijatá — #${booking.id}</h2>
        <p style="color:#64748b; font-size:14px;">Dobrý deň${booking.customer ? ', ' + booking.customer : ''}, vaša rezervácia servisného úkonu bola úspešne prijatá. Nižšie nájdete zhrnutie termínu:</p>
        <hr style="border:none; border-top:1px solid #e2e8f0; margin:16px 0;" />
        <table style="width:100%; font-size:14px; border-collapse:collapse;">
          <tr><td style="padding:6px 0; color:#64748b; width:140px;"><strong>Diel:</strong></td><td style="color:#2563eb; font-weight:bold;">[${booking.partCode || 'P'}] ${booking.partName || '-'}</td></tr>
          <tr><td style="padding:6px 0; color:#64748b;"><strong>Termín:</strong></td><td style="color:#0f172a;">${booking.date || '-'} o ${booking.time || '-'}</td></tr>
          <tr><td style="padding:6px 0; color:#64748b;"><strong>EČV Vozidla:</strong></td><td style="color:#0f172a; font-family:monospace; font-weight:bold;">${plateFormatted}</td></tr>
          <tr><td style="padding:6px 0; color:#64748b;"><strong>Odhadovaná cena:</strong></td><td style="color:#10b981; font-weight:bold;">${booking.price || '-'}</td></tr>
        </table>
        <div style="margin-top:24px; text-align:center;">
          <a href="${manageUrl}" style="background:#2563eb; color:#ffffff; padding:12px 24px; text-decoration:none; border-radius:6px; font-weight:bold; font-size:14px; display:inline-block;">Spravovať moju rezerváciu</a>
        </div>
        <p style="color:#64748b; font-size:13px; margin-top:20px;">Cez odkaz vyššie si viete termín zrušiť alebo presunúť na iný voľný dátum a čas. V prípade otázok nás môžete aj priamo kontaktovať. Tešíme sa na vás!</p>
      </div>
    `;
}

// Customer-facing confirmation (best-effort, never blocks the booking flow)
function dispatchCustomerConfirmation(booking) {
  const subject = 'Potvrdenie rezervácie #' + booking.id + ' — AutoMek';
  return sendEmailGeneric(booking.email, subject, buildCustomerConfirmationEmailHtml(booking));
}

const server = http.createServer((req, res) => {
  const parsedUrl = new URL(req.url, 'http://localhost:' + PORT);
  const pathname = parsedUrl.pathname;

  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Authorization');

  if (req.method === 'OPTIONS') {
    res.writeHead(204);
    res.end();
    return;
  }

  // API ROUTE: Send booking notification
  if (pathname === '/api/send-notification' && req.method === 'POST') {
    const payload = requireAuth(req, res);
    if (!payload) return;
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', async () => {
      try {
        const booking = JSON.parse(body || '{}');
        const targetEmail = emailConfig.recipientEmail || 'servis@automek.sk';

        console.log('\n[BREVO] Odosielam email pre zákazku #' + booking.id + ' na ' + targetEmail);
        const result = await dispatchNotification(targetEmail, booking);
        console.log('[BREVO] Email úspešne odoslaný na ' + targetEmail);

        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: true, to: targetEmail, result }));
      } catch (err) {
        console.error('[BREVO] Chyba odoslania:', err.message);
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: false, error: err.message }));
      }
    });
    return;
  }

  // API ROUTE: Get Settings (admin only — exposes the Brevo API key)
  if (pathname === '/api/get-settings' && req.method === 'GET') {
    const payload = requireAuth(req, res);
    if (!payload) return;
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({
      recipientEmail: emailConfig.recipientEmail || '',
      brevoSender: (emailConfig.brevo && emailConfig.brevo.senderEmail) || (emailConfig.smtp && emailConfig.smtp.auth && emailConfig.smtp.auth.user) || '',
      brevoFromEmail: (emailConfig.brevo && emailConfig.brevo.fromEmail) || '',
      brevoKey: (emailConfig.brevo && emailConfig.brevo.apiKey) || (emailConfig.smtp && emailConfig.smtp.auth && emailConfig.smtp.auth.pass) || ''
    }));
    return;
  }

  // API ROUTE: Save Settings (admin only)
  if (pathname === '/api/save-settings' && req.method === 'POST') {
    const payload = requireAuth(req, res);
    if (!payload) return;
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', () => {
      try {
        const data = JSON.parse(body || '{}');
        if (data.recipientEmail) emailConfig.recipientEmail = data.recipientEmail.trim();

        emailConfig.brevo = emailConfig.brevo || {};
        if (data.brevoSender) emailConfig.brevo.senderEmail = data.brevoSender.trim();
        if (data.brevoFromEmail) emailConfig.brevo.fromEmail = data.brevoFromEmail.trim();
        if (data.brevoKey) emailConfig.brevo.apiKey = data.brevoKey.trim();

        // Also sync to smtp object for compatibility
        emailConfig.smtp = emailConfig.smtp || {};
        emailConfig.smtp.auth = emailConfig.smtp.auth || {};
        if (data.brevoSender) emailConfig.smtp.auth.user = data.brevoSender.trim();
        if (data.brevoKey) emailConfig.smtp.auth.pass = data.brevoKey.trim();

        saveConfig();
        console.log('[CONFIG] Brevo nastavenia boli uložené pre príjemcu:', emailConfig.recipientEmail);

        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: true, recipient: emailConfig.recipientEmail }));
      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: false, error: err.message }));
      }
    });
    return;
  }

  // API ROUTE: Send Test Email (admin only)
  if (pathname === '/api/test-email' && req.method === 'POST') {
    const payload = requireAuth(req, res);
    if (!payload) return;
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', async () => {
      try {
        let reqData = {};
        try { reqData = JSON.parse(body || '{}'); } catch(e){}

        if (reqData.recipientEmail) emailConfig.recipientEmail = reqData.recipientEmail.trim();
        if (reqData.brevoSender) {
          emailConfig.brevo = emailConfig.brevo || {};
          emailConfig.brevo.senderEmail = reqData.brevoSender.trim();
        }
        if (reqData.brevoFromEmail) {
          emailConfig.brevo = emailConfig.brevo || {};
          emailConfig.brevo.fromEmail = reqData.brevoFromEmail.trim();
        }
        if (reqData.brevoKey) {
          emailConfig.brevo = emailConfig.brevo || {};
          emailConfig.brevo.apiKey = reqData.brevoKey.trim();
        }
        saveConfig();

        const targetEmail = emailConfig.recipientEmail;

        const testBooking = {
          id: 'JK-' + Math.floor(100000 + Math.random() * 900000),
          customer: 'Peter Novák (Test)',
          phone: '+421 905 456 789',
          email: targetEmail,
          plate: 'KE 401 BE',
          partName: '2.0 TFSI Motor & Prevodovka',
          partCode: 'E',
          urgency: 'critical',
          date: 'Po, 1. Sep',
          time: '10:00',
          price: '180 €',
          problemDesc: 'Testovacie overenie spojenia s Brevo SMTP / API serverom.'
        };

        console.log('\n[TEST EMAIL] Odosielam Brevo test na: ' + targetEmail);
        const result = await dispatchNotification(targetEmail, testBooking);
        console.log('[TEST EMAIL] Brevo úspešne odoslal test na ' + targetEmail);

        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({
          success: true,
          message: 'Testovací email bol ÚSPEŠNE odoslaný cez Brevo na adresu ' + targetEmail + '!'
        }));
      } catch (err) {
        console.error('[TEST EMAIL] Brevo chyba:', err.message);
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: false, error: err.message }));
      }
    });
    return;
  }

  // =========================================================
  // AUTH ROUTES
  // =========================================================

  // API ROUTE: Login (password, then TOTP 2FA)
  if (pathname === '/api/auth/login' && req.method === 'POST') {
    const ip = req.socket.remoteAddress || 'unknown';
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', async () => {
      try {
        if (isLockedOut(ip)) {
          res.writeHead(429, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Príliš veľa neúspešných pokusov. Skúste to znova o pár minút.' }));
          return;
        }

        const data = JSON.parse(body || '{}');
        const { password, code2fa, setupSecret } = data;

        if (!password || !verifyPasswordMatch(password, adminAuth.passwordSalt, adminAuth.passwordHash)) {
          registerFailedAttempt(ip);
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Nesprávne administrátorské heslo' }));
          return;
        }

        // Step 1 (password only): decide whether 2FA needs to be set up or just verified
        if (!code2fa) {
          if (!adminAuth.totpEnabled) {
            const secret = generateTotpSecret();
            const otpauth = `otpauth://totp/AutoMek:admin?secret=${secret}&issuer=AutoMek&digits=6&period=30`;
            const qrDataUrl = await QRCode.toDataURL(otpauth);
            res.writeHead(200, { 'Content-Type': 'application/json' });
            res.end(JSON.stringify({ success: true, needsSetup: true, setupSecret: secret, qrDataUrl }));
          } else {
            res.writeHead(200, { 'Content-Type': 'application/json' });
            res.end(JSON.stringify({ success: true }));
          }
          return;
        }

        // Step 2: verify the 6-digit TOTP code (against the new secret if enrolling, else the stored one)
        const secretToCheck = setupSecret || adminAuth.totpSecret;
        if (!secretToCheck || !totpVerify(secretToCheck, code2fa)) {
          registerFailedAttempt(ip);
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Neplatný 2FA overovací kód' }));
          return;
        }

        if (setupSecret) {
          adminAuth.totpSecret = setupSecret;
          adminAuth.totpEnabled = true;
          saveAdminAuth();
        }

        clearAttempts(ip);
        const token = signToken({ sub: 'admin', exp: Date.now() + TOKEN_TTL_MS }, adminAuth.jwtSecret);
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: true, token, needsRecoverySetup: !adminAuth.recoveryEmail }));
      } catch (err) {
        res.writeHead(500, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: false, error: err.message }));
      }
    });
    return;
  }

  // API ROUTE: Verify an existing session token
  if (pathname === '/api/auth/verify' && req.method === 'GET') {
    const payload = requireAuth(req, res);
    if (!payload) return;
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({ success: true }));
    return;
  }

  // API ROUTE: Masked recovery-email info (for the "forgot password" screen)
  if (pathname === '/api/auth/recovery-info' && req.method === 'GET') {
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({
      hasRecoveryEmail: !!adminAuth.recoveryEmail,
      maskedEmail: adminAuth.recoveryEmail ? maskEmail(adminAuth.recoveryEmail) : null
    }));
    return;
  }

  // API ROUTE: Set the recovery e-mail (first-login setup, requires a valid session)
  if (pathname === '/api/auth/set-recovery-email' && req.method === 'POST') {
    const payload = requireAuth(req, res);
    if (!payload) return;
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', () => {
      try {
        const data = JSON.parse(body || '{}');
        if (!data.email || !data.email.includes('@')) {
          res.writeHead(400, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Neplatná e-mailová adresa' }));
          return;
        }
        adminAuth.recoveryEmail = data.email.trim();
        saveAdminAuth();
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: true }));
      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: false, error: err.message }));
      }
    });
    return;
  }

  // API ROUTE: Account/security overview for the settings panel (admin only)
  if (pathname === '/api/auth/account-info' && req.method === 'GET') {
    const payload = requireAuth(req, res);
    if (!payload) return;
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({
      totpEnabled: !!adminAuth.totpEnabled,
      recoveryEmail: adminAuth.recoveryEmail || ''
    }));
    return;
  }

  // API ROUTE: Change the admin password while already logged in (admin only)
  if (pathname === '/api/auth/change-password' && req.method === 'POST') {
    const payload = requireAuth(req, res);
    if (!payload) return;
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', () => {
      try {
        const { currentPassword, newPassword } = JSON.parse(body || '{}');

        if (!currentPassword || !verifyPasswordMatch(currentPassword, adminAuth.passwordSalt, adminAuth.passwordHash)) {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Súčasné heslo nie je správne.' }));
          return;
        }
        if (!newPassword || newPassword.length < 6) {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Nové heslo musí mať aspoň 6 znakov.' }));
          return;
        }

        const salt = crypto.randomBytes(16).toString('hex');
        adminAuth.passwordSalt = salt;
        adminAuth.passwordHash = hashPassword(newPassword, salt);
        saveAdminAuth();

        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: true }));
      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: false, error: err.message }));
      }
    });
    return;
  }

  // API ROUTE: Request a password-reset OTP by e-mail
  if (pathname === '/api/auth/request-reset' && req.method === 'POST') {
    (async () => {
      try {
        if (!adminAuth.recoveryEmail) {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Nie je nastavený obnovovací e-mail.' }));
          return;
        }
        const code = String(Math.floor(100000 + Math.random() * 900000));
        adminAuth.resetCode = code;
        adminAuth.resetCodeExpiry = Date.now() + 10 * 60 * 1000;
        saveAdminAuth();

        const html = `<p>Váš overovací kód na obnovenie hesla do AutoMek administrácie je:</p><h2 style="letter-spacing:4px;">${code}</h2><p>Kód platí 10 minút. Ak ste o reset nežiadali, tento e-mail ignorujte.</p>`;
        await sendEmailGeneric(adminAuth.recoveryEmail, 'AutoMek: Kód na obnovenie hesla', html);

        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: true }));
      } catch (err) {
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: false, error: err.message }));
      }
    })();
    return;
  }

  // API ROUTE: Confirm the OTP and set a new password
  if (pathname === '/api/auth/reset-password' && req.method === 'POST') {
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', () => {
      try {
        const { resetCode, newPassword } = JSON.parse(body || '{}');

        if (!adminAuth.resetCode || !adminAuth.resetCodeExpiry || Date.now() > adminAuth.resetCodeExpiry) {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Kód expiroval, vyžiadajte si nový.' }));
          return;
        }
        if (resetCode !== adminAuth.resetCode) {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Nesprávny kód.' }));
          return;
        }
        if (!newPassword || newPassword.length < 6) {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Heslo musí mať aspoň 6 znakov.' }));
          return;
        }

        const salt = crypto.randomBytes(16).toString('hex');
        adminAuth.passwordSalt = salt;
        adminAuth.passwordHash = hashPassword(newPassword, salt);
        adminAuth.resetCode = null;
        adminAuth.resetCodeExpiry = null;
        // Reset via e-mail also clears 2FA — the next login re-enrolls with a fresh QR code.
        // This is what lets you back in if you've lost the phone/app your old TOTP secret was on.
        adminAuth.totpSecret = null;
        adminAuth.totpEnabled = false;
        saveAdminAuth();

        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: true }));
      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: false, error: err.message }));
      }
    });
    return;
  }

  // =========================================================
  // BOOKINGS ROUTES
  // =========================================================

  // API ROUTE: List all bookings (admin only)
  if (pathname === '/api/bookings' && req.method === 'GET') {
    const payload = requireAuth(req, res);
    if (!payload) return;
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify(loadBookings()));
    return;
  }

  // API ROUTE: Which times are already taken on a given day (public — no customer
  // details, just the occupied time strings, so the booking/reschedule calendars
  // can show real availability instead of guess-and-fail).
  if (pathname === '/api/availability' && req.method === 'GET') {
    const date = parsedUrl.searchParams.get('date') || '';
    const bookings = loadBookings();
    const bookedTimes = bookings
      .filter(b => b.date === date && b.status !== 'cancelled')
      .map(b => b.time)
      .filter(Boolean);
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({ bookedTimes }));
    return;
  }

  // API ROUTE: Create or upsert a booking (public — used by the customer-facing booking form)
  if (pathname === '/api/bookings' && req.method === 'POST') {
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', async () => {
      try {
        const booking = JSON.parse(body || '{}');
        if (!booking.id) booking.id = 'JK-' + Math.floor(100000 + Math.random() * 900000);

        const bookings = loadBookings();
        const idx = bookings.findIndex(b => b.id === booking.id);
        const isNew = idx === -1;

        if (isNew && isBookingRateLimited(getClientIp(req))) {
          res.writeHead(429, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Príliš veľa rezervácií z tejto adresy. Skúste to prosím o chvíľu.' }));
          return;
        }

        if (isNew) {
          booking.createdAt = booking.createdAt || new Date().toISOString();
          // Lets the customer manage (view/cancel/reschedule) their own booking later
          // via a link that doesn't require an admin login — see /api/my-booking*.
          booking.manageToken = crypto.randomBytes(24).toString('hex');
          bookings.push(booking);
        } else {
          bookings[idx] = { ...bookings[idx], ...booking };
        }
        saveBookings(bookings);

        if (isNew) {
          const targetEmail = emailConfig.recipientEmail || 'servis@automek.sk';
          dispatchNotification(targetEmail, booking).catch(err => {
            console.warn('[BOOKING] Email notifikácia zlyhala:', err.message);
          });

          if (booking.email && booking.email.includes('@')) {
            dispatchCustomerConfirmation(booking).catch(err => {
              console.warn('[BOOKING] Potvrdzovací email zákazníkovi zlyhal:', err.message);
            });
          }
        }

        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify(isNew ? booking : bookings[idx]));
      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: false, error: err.message }));
      }
    });
    return;
  }

  // API ROUTE: Update / delete a single booking (admin only)
  if (pathname.startsWith('/api/bookings/') && (req.method === 'PUT' || req.method === 'DELETE')) {
    const payload = requireAuth(req, res);
    if (!payload) return;

    const id = decodeURIComponent(pathname.slice('/api/bookings/'.length));
    const bookings = loadBookings();
    const idx = bookings.findIndex(b => b.id === id);
    if (idx === -1) {
      res.writeHead(404, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ success: false, error: 'Zákazka nenájdená' }));
      return;
    }

    if (req.method === 'DELETE') {
      bookings.splice(idx, 1);
      saveBookings(bookings);
      res.writeHead(200, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ success: true }));
      return;
    }

    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', () => {
      try {
        const updates = JSON.parse(body || '{}');
        bookings[idx] = { ...bookings[idx], ...updates };
        saveBookings(bookings);
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify(bookings[idx]));
      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: false, error: err.message }));
      }
    });
    return;
  }

  // =========================================================
  // CUSTOMER SELF-SERVICE ROUTES (public, gated by id + per-booking manageToken —
  // not admin auth). Lets a customer view/cancel/reschedule only their own booking
  // via the link sent in the confirmation e-mail.
  // =========================================================

  function findOwnBooking(bookings, id, token) {
    if (!id || !token) return -1;
    return bookings.findIndex(b => b.id === id && b.manageToken && b.manageToken === token);
  }

  if (pathname === '/api/my-booking' && req.method === 'GET') {
    const id = parsedUrl.searchParams.get('id');
    const token = parsedUrl.searchParams.get('token');
    const bookings = loadBookings();
    const idx = findOwnBooking(bookings, id, token);
    if (idx === -1) {
      res.writeHead(404, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ success: false, error: 'Zákazka nenájdená.' }));
      return;
    }
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify(bookings[idx]));
    return;
  }

  if (pathname === '/api/my-booking/cancel' && req.method === 'POST') {
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', () => {
      try {
        const { id, token } = JSON.parse(body || '{}');
        const bookings = loadBookings();
        const idx = findOwnBooking(bookings, id, token);
        if (idx === -1) {
          res.writeHead(404, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Zákazka nenájdená.' }));
          return;
        }
        if (bookings[idx].status === 'cancelled' || bookings[idx].status === 'completed') {
          res.writeHead(400, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Túto zákazku už nie je možné zrušiť.' }));
          return;
        }
        bookings[idx].status = 'cancelled';
        saveBookings(bookings);
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: true, booking: bookings[idx] }));
      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: false, error: err.message }));
      }
    });
    return;
  }

  if (pathname === '/api/my-booking/reschedule' && req.method === 'POST') {
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', () => {
      try {
        const { id, token, dateIso, date, time } = JSON.parse(body || '{}');
        const bookings = loadBookings();
        const idx = findOwnBooking(bookings, id, token);
        if (idx === -1) {
          res.writeHead(404, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Zákazka nenájdená.' }));
          return;
        }
        if (bookings[idx].status === 'cancelled' || bookings[idx].status === 'completed') {
          res.writeHead(400, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Termín tejto zákazky už nie je možné zmeniť.' }));
          return;
        }
        if (!dateIso || !date || !time || !/^\d{4}-\d{2}-\d{2}$/.test(dateIso) || !/^\d{2}:\d{2}$/.test(time)) {
          res.writeHead(400, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Neplatný dátum alebo čas.' }));
          return;
        }

        const [h, m] = time.split(':').map(Number);
        const target = new Date(dateIso + 'T00:00:00');
        target.setHours(h, m, 0, 0);

        if (isNaN(target.getTime()) || target <= new Date()) {
          res.writeHead(400, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Zvolený termín už uplynul.' }));
          return;
        }
        const dow = target.getDay();
        if (dow === 0 || dow === 6) {
          res.writeHead(400, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Cez víkend máme zatvorené, zvoľte prosím pracovný deň.' }));
          return;
        }

        const conflict = bookings.some((b, i) => i !== idx && b.status !== 'cancelled' && b.date === date && b.time === time);
        if (conflict) {
          res.writeHead(409, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ success: false, error: 'Tento termín je už obsadený, zvoľte prosím iný.' }));
          return;
        }

        bookings[idx].date = date;
        bookings[idx].time = time;
        saveBookings(bookings);
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: true, booking: bookings[idx] }));
      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: false, error: err.message }));
      }
    });
    return;
  }

  // Static files
  let safePath = pathname === '/' ? '/index.html' : pathname;

  // Never serve secrets or source (admin_auth.json holds jwtSecret + dataKey!) or
  // let ../ escape __dirname — this backend's own folder holds both public assets
  // and these files on some deployments, so the extension/path alone isn't enough.
  const BLOCKED_BASENAMES = new Set([
    'admin_auth.json', 'email_config.json', 'bookings.json',
    'server.js', 'package.json', 'package-lock.json'
  ]);
  const requestedBasename = path.basename(safePath);
  const filePath = path.resolve(__dirname, '.' + safePath);
  const isWithinRoot = filePath === __dirname || filePath.startsWith(__dirname + path.sep);

  if (!isWithinRoot || BLOCKED_BASENAMES.has(requestedBasename) || requestedBasename.startsWith('.')) {
    res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end('404 Súbor nenájdený');
    return;
  }

  fs.stat(filePath, (err, stats) => {
    if (err || !stats.isFile()) {
      res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
      res.end('404 Súbor nenájdený');
      return;
    }
    const ext = path.extname(filePath).toLowerCase();
    const contentType = MIME_TYPES[ext] || 'application/octet-stream';
    res.writeHead(200, { 'Content-Type': contentType });
    fs.createReadStream(filePath).pipe(res);
  });
});

server.listen(PORT, () => {
  console.log('AutoMek Server (Brevo) beží na http://localhost:' + PORT);
});
