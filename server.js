const http = require('http');
const https = require('https');
const fs = require('fs');
const path = require('path');
const nodemailer = require('nodemailer');

const PORT = 3000;
const CONFIG_FILE = path.join(__dirname, 'email_config.json');

let emailConfig = {
  provider: 'brevo', // 'brevo' or 'custom_smtp'
  recipientEmail: 'servis@automek.sk',
  brevo: {
    senderEmail: '',
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

if (fs.existsSync(CONFIG_FILE)) {
  try {
    const raw = fs.readFileSync(CONFIG_FILE, 'utf8');
    emailConfig = { ...emailConfig, ...JSON.parse(raw) };
  } catch (e) {}
}

function saveConfig() {
  try {
    fs.writeFileSync(CONFIG_FILE, JSON.stringify(emailConfig, null, 2), 'utf8');
  } catch (e) {
    console.error('Error saving config:', e);
  }
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

// Send via Brevo HTTP API
function sendViaBrevoApi(apiKey, senderEmail, recipientEmail, booking) {
  return new Promise((resolve, reject) => {
    const plateFormatted = (booking.plate || '-').replace(/-/g, ' ').replace(/\s+/g, ' ').trim();
    
    const orderUrl = 'http://localhost:' + PORT + '/order.html?id=' + encodeURIComponent(booking.id);

    const htmlContent = `
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

    const payload = JSON.stringify({
      sender: { name: "AutoMek Servis", email: senderEmail },
      to: [{ email: recipientEmail }],
      subject: 'AutoMek: Nová zákazka #' + booking.id + ' - ' + (booking.customer || 'Klient') + ' (' + plateFormatted + ')',
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

// Send via Brevo SMTP (Nodemailer)
function sendViaBrevoSmtp(login, key, recipientEmail, booking) {
  const transporter = nodemailer.createTransport({
    host: 'smtp-relay.brevo.com',
    port: 587,
    secure: false,
    auth: {
      user: login,
      pass: key
    }
  });

  const plateFormatted = (booking.plate || '-').replace(/-/g, ' ').replace(/\s+/g, ' ').trim();
  const orderUrl = 'http://localhost:' + PORT + '/order.html?id=' + encodeURIComponent(booking.id);

  return transporter.sendMail({
    from: '"AutoMek Servis" <' + login + '>',
    to: recipientEmail,
    subject: 'AutoMek: Nová zákazka #' + booking.id + ' - ' + (booking.customer || 'Klient') + ' (' + plateFormatted + ')',
    html: '<h3>Nová zákazka #' + booking.id + '</h3><p>Zákazník: ' + booking.customer + ' (' + booking.phone + ')</p><p>EČV: ' + plateFormatted + '</p><p>Diel: [' + booking.partCode + '] ' + booking.partName + '</p><p>Termín: ' + booking.date + ' o ' + booking.time + '</p><p>Cena: ' + booking.price + '</p><p><a href="' + orderUrl + '">Otvoriť kartu zákazky</a></p>'
  });
}

// Main dispatcher
async function dispatchNotification(recipient, booking) {
  const brevoKey = (emailConfig.brevo && emailConfig.brevo.apiKey ? emailConfig.brevo.apiKey : (emailConfig.smtp && emailConfig.smtp.auth ? emailConfig.smtp.auth.pass : '')).trim();
  const brevoSender = (emailConfig.brevo && emailConfig.brevo.senderEmail ? emailConfig.brevo.senderEmail : (emailConfig.smtp && emailConfig.smtp.auth ? emailConfig.smtp.auth.user : '')).trim();

  if (brevoKey && brevoSender) {
    try {
      // First try Brevo HTTP API (fastest, never blocked by ports)
      return await sendViaBrevoApi(brevoKey, brevoSender, recipient, booking);
    } catch (apiErr) {
      console.warn('[BREVO API error, trying SMTP fallback]:', apiErr.message);
      // Fallback to Brevo SMTP
      return await sendViaBrevoSmtp(brevoSender, brevoKey, recipient, booking);
    }
  } else {
    throw new Error('Neboli zadané prihlasovacie údaje pre Brevo (Email a API/SMTP kľúč).');
  }
}

const server = http.createServer((req, res) => {
  const parsedUrl = new URL(req.url, 'http://localhost:' + PORT);
  const pathname = parsedUrl.pathname;

  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type');

  if (req.method === 'OPTIONS') {
    res.writeHead(204);
    res.end();
    return;
  }

  // API ROUTE: Send booking notification
  if (pathname === '/api/send-notification' && req.method === 'POST') {
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

  // API ROUTE: Get Settings
  if (pathname === '/api/get-settings' && req.method === 'GET') {
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({
      recipientEmail: emailConfig.recipientEmail || '',
      brevoSender: (emailConfig.brevo && emailConfig.brevo.senderEmail) || (emailConfig.smtp && emailConfig.smtp.auth && emailConfig.smtp.auth.user) || '',
      brevoKey: (emailConfig.brevo && emailConfig.brevo.apiKey) || (emailConfig.smtp && emailConfig.smtp.auth && emailConfig.smtp.auth.pass) || ''
    }));
    return;
  }

  // API ROUTE: Save Settings
  if (pathname === '/api/save-settings' && req.method === 'POST') {
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', () => {
      try {
        const data = JSON.parse(body || '{}');
        if (data.recipientEmail) emailConfig.recipientEmail = data.recipientEmail.trim();
        
        emailConfig.brevo = emailConfig.brevo || {};
        if (data.brevoSender) emailConfig.brevo.senderEmail = data.brevoSender.trim();
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

  // API ROUTE: Send Test Email
  if (pathname === '/api/test-email' && req.method === 'POST') {
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

  // Static files
  let safePath = pathname === '/' ? '/index.html' : pathname;
  let filePath = path.join(__dirname, safePath);

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
