/* Local development server — never deployed, never used by the website.
 *
 * The site needs PHP to run api.php, and a plain file server gives you the app in "this browser only"
 * mode: no shared open play, no scheduled list, no roster import. This stands in for api.php using
 * nothing but Node, so everything works on your machine exactly as it does on the website.
 *
 *   node dev-server.js            then open http://localhost:8765
 *   node dev-server.js 3000       to use a different port
 *
 * It reads the real admin PIN hash straight out of api.php, so you log in with the same PIN as the live
 * site. It stores data in the same data/*.json files the host uses, and those are all git-ignored, so
 * nothing you do here can reach the website.
 *
 * To test two admin devices at once, open http://localhost:8765 in one tab and http://127.0.0.1:8765 in
 * another: different origins mean separate logins and separate browser storage, same server.
 */
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');

const ROOT = __dirname;
const DATA = path.join(ROOT, 'data');
const PORT = Number(process.argv[2]) || 8765;

const F = {
  openplays: path.join(DATA, 'openplays.json'),
  upcoming: path.join(DATA, 'upcoming.json'),
  seed: path.join(DATA, 'upcoming.seed.json'),
  live: path.join(DATA, 'live.json'),
};

/* ---- the admin PIN ----
 * By default it is the one the website uses, read straight out of api.php so the two never drift.
 * Set DEV_PIN to use a throwaway PIN instead, handy if you would rather not type the club's real one:
 *   DEV_PIN=test1234 node dev-server.js            (macOS / Linux)
 *   set DEV_PIN=test1234 && node dev-server.js     (Windows cmd)
 *   $env:DEV_PIN="test1234"; node dev-server.js    (PowerShell)
 */
const crypto = require('crypto');
function adminKeyFixed() {
  const override = (process.env.DEV_PIN || '').trim();
  if (override) return crypto.createHash('sha256').update(override).digest('hex');
  try {
    const php = fs.readFileSync(path.join(ROOT, 'api.php'), 'utf8');
    const m = php.match(/ADMIN_KEY_FIXED\s*=\s*'([a-f0-9]*)'/i);
    return m ? m[1].toLowerCase() : '';
  } catch (_) { return ''; }
}
const ADMIN_KEY = adminKeyFixed();
const PIN_SOURCE = (process.env.DEV_PIN || '').trim() ? 'DEV_PIN=' + process.env.DEV_PIN.trim()
                 : ADMIN_KEY ? 'the same one the website uses'
                 : 'any 8+ characters (no PIN set in api.php)';

/* ---- tiny json helpers ---- */
const readJson = (file, fallback) => {
  try { return JSON.parse(fs.readFileSync(file, 'utf8')); } catch (_) { return fallback; }
};
const writeJson = (file, value) => {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file + '.tmp', JSON.stringify(value, null, file === F.upcoming ? 2 : 0));
  fs.renameSync(file + '.tmp', file);
};
/* Mirrors cleanEvents() in api.php: drop malformed entries, trim, and give every event an id — the seed
   file ships without one, and the app matches events by id. */
function cleanEvents(list) {
  const out = [];
  for (const e of Array.isArray(list) ? list : []) {
    if (!e || typeof e !== 'object') continue;
    const start = String(e.start || '');
    if (!/^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}$/.test(start)) continue;
    let rsvp = String(e.rsvp || '').trim();
    if (rsvp && !/^https?:\/\//i.test(rsvp)) rsvp = '';
    out.push({
      id: String(e.id || '').replace(/[^A-Za-z0-9_-]/g, '') || ('up_' + crypto.randomBytes(4).toString('hex')),
      title: String(e.title || '').trim().slice(0, 120),
      start,
      venue: String(e.venue || '').trim().slice(0, 120),
      rsvp: rsvp.slice(0, 300),
    });
    if (out.length >= 60) break;
  }
  out.sort((a, b) => a.start.localeCompare(b.start));
  return out;
}
function readUpcoming() {
  if (!fs.existsSync(F.upcoming) && fs.existsSync(F.seed)) {
    writeJson(F.upcoming, cleanEvents(readJson(F.seed, [])));      // seed has no ids; give it some
  }
  return cleanEvents(readJson(F.upcoming, []));
}
function readLive() {
  const j = readJson(F.live, null);
  return j && typeof j === 'object' ? { version: j.version | 0, updatedAt: j.updatedAt | 0, state: j.state ?? null }
                                    : { version: 0, updatedAt: 0, state: null };
}

/* ---- multipart form parsing, enough for what the app sends ---- */
function parseForm(buf, contentType) {
  const out = {};
  const m = /boundary=(?:"([^"]+)"|([^;]+))/.exec(contentType || '');
  if (!m) return out;
  const parts = buf.toString('binary').split('--' + (m[1] || m[2]));
  for (const part of parts) {
    const hit = /name="([^"]+)"\r\n\r\n([\s\S]*)\r\n$/.exec(part);
    if (hit) out[hit[1]] = Buffer.from(hit[2], 'binary').toString('utf8');
  }
  return out;
}

/* ---- an event's own details, the same way api.php reads them ---- */
const RSVP_HOSTS = ['reclub.co'];
function rsvpHostAllowed(url) {
  let host = '';
  try { host = new URL(url).hostname.toLowerCase(); } catch (_) { return false; }
  return RSVP_HOSTS.some(ok => host === ok || host.endsWith('.' + ok));
}
const decodeEntities = s => String(s)
  .replace(/&#x([0-9a-f]+);/gi, (_, h) => String.fromCodePoint(parseInt(h, 16)))
  .replace(/&#(\d+);/g, (_, d) => String.fromCodePoint(Number(d)))
  .replace(/&quot;/g, '"').replace(/&apos;/g, "'").replace(/&nbsp;/g, ' ')
  .replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&amp;/g, '&');
const MONTHS = ['jan','feb','mar','apr','may','jun','jul','aug','sep','oct','nov','dec'];
const DAYS = ['sun','mon','tue','wed','thu','fri','sat'];
function rsvpYearFor(mon, day, weekday) {
  const today = new Date(); today.setHours(0, 0, 0, 0);
  const want = DAYS.indexOf(weekday.slice(0, 3).toLowerCase());
  let best = null;
  for (const off of [-1, 0, 1]) {
    const y = today.getFullYear() + off;
    const d = new Date(y, mon - 1, day);
    if (d.getMonth() !== mon - 1 || d.getDate() !== day) continue;
    if (want >= 0 && d.getDay() !== want) continue;
    if (d < new Date(today.getTime() - 14 * 864e5)) continue;
    if (!best || d < best) best = d;
  }
  return (best || today).getFullYear();
}
function parseRsvpEvent(html) {
  const out = { title: '', start: '', venue: '' };
  const t = /<title>([^<]*)<\/title>/i.exec(html);
  if (t) out.title = decodeEntities(t[1]).trim().replace(/^\s*Reclub\s+/i, '').trim();
  const rows = [...html.matchAll(/<p class="text-sm font-semibold"[^>]*>([^<]{1,120})<\/p>/gi)].map(m => decodeEntities(m[1]).trim());
  for (let i = 0; i < rows.length; i++) {
    const d = /^(\w{3,9}),\s*(\w{3,9})\s+(\d{1,2})\s*@\s*(\d{1,2}):(\d{2})\s*(AM|PM)$/i.exec(rows[i]);
    if (!d) continue;
    const mon = MONTHS.indexOf(d[2].slice(0, 3).toLowerCase()) + 1;
    if (!mon) continue;
    let hour = Number(d[4]) % 12; if (/pm/i.test(d[6])) hour += 12;
    const year = rsvpYearFor(mon, Number(d[3]), d[1]);
    const p2 = n => String(n).padStart(2, '0');
    out.start = year + '-' + p2(mon) + '-' + p2(Number(d[3])) + 'T' + p2(hour) + ':' + p2(Number(d[5]));
    if (rows[i + 1]) out.venue = rows[i + 1].slice(0, 120);
    break;
  }
  return out;
}
/* ---- the confirmed players on an RSVP page, the same way api.php reads them ---- */
function parseRsvpNames(html) {
  const lower = html.toLowerCase();
  const start = lower.indexOf('confirmed');
  if (start < 0) return { names: [], guests: 0 };
  const end = lower.indexOf('waitlisted', start);
  const block = end < 0 ? html.slice(start) : html.slice(start, end);
  const re = new RegExp('<p class="[^"]*truncate[^"]*"[^>]*>([^<]{1,60})<\\/p>', 'gi');
  let guests = 0;
  const names = [...block.matchAll(re)]
    .map(x => x[1].replace(/\s+/g, ' ').trim())
    .filter(n => n && !/^\+\d+$/.test(n) && n.length <= 40)
    // "Ken +1" is one player who brought a guest, not a player called "Ken +1"
    .map(n => { const t = /^(.*?)\s*\+(\d+)$/.exec(n); if (t && t[1].trim()) { guests += Number(t[2]); return t[1].trim(); } return n; });
  for (const g of block.matchAll(/>\+(\d+)</g)) guests += Number(g[1]);
  // Not every confirmed player has a name on the page, so report the heading's total too.
  const c = /Confirmed[^0-9]{0,40}(\d+)/i.exec(block);
  return { names, guests, total: c ? Number(c[1]) : 0 };
}

const TYPES = {
  '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8', '.json': 'application/json; charset=utf-8',
  '.png': 'image/png', '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg',
  '.webp': 'image/webp', '.svg': 'image/svg+xml', '.ico': 'image/x-icon',
};

const send = (res, code, body, type) => {
  res.writeHead(code, { 'Content-Type': type || 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(body);
};
const json = (res, code, obj) => send(res, code, JSON.stringify(obj));

async function handleApi(req, res, url, body) {
  const action = url.searchParams.get('action') || body.action || '';
  const key = (req.headers['x-admin-key'] || body.key || '').toLowerCase();
  const isAdmin = ADMIN_KEY ? key === ADMIN_KEY : key.length >= 8;
  const needAdmin = () => { json(res, 401, { ok: false, error: 'Admin PIN required' }); return false; };

  switch (action) {
    case 'status':
      return json(res, 200, { server: true, pin: true });
    case 'login':
      return json(res, 200, isAdmin ? { ok: true } : { ok: false, reason: 'wrong' });
    case 'claim':
      return json(res, 409, { ok: false, error: 'An admin PIN already exists' });

    case 'upcoming':
      return json(res, 200, { events: readUpcoming() });
    case 'saveUpcoming': {
      if (!isAdmin) return needAdmin();
      let events; try { events = JSON.parse(body.events); } catch (_) { return json(res, 400, { ok: false, error: 'Bad events payload' }); }
      if (!Array.isArray(events)) return json(res, 400, { ok: false, error: 'Bad events payload' });
      const cleaned = cleanEvents(events);
      writeJson(F.upcoming, cleaned);
      return json(res, 200, { ok: true, events: cleaned });
    }

    case 'live': {
      const live = readLive();
      const v = url.searchParams.get('v');
      if (v !== null && Number(v) === live.version) return json(res, 200, { version: live.version, same: true });
      return json(res, 200, live);
    }
    case 'saveLive': {
      if (!isAdmin) return needAdmin();
      let st; try { st = JSON.parse(body.state); } catch (_) { return json(res, 400, { ok: false, error: 'Bad live payload' }); }
      if (!st || !st.players || !st.queue || !st.courts) return json(res, 400, { ok: false, error: 'Bad live payload' });
      const cur = readLive();
      const base = Number(body.base);
      if (base !== cur.version) return json(res, 409, { ok: false, conflict: true, ...cur });
      const live = { version: cur.version + 1, updatedAt: Date.now(), state: st };
      writeJson(F.live, live);
      return json(res, 200, { ok: true, version: live.version, updatedAt: live.updatedAt });
    }

    case 'publish': {
      if (!isAdmin) return needAdmin();
      let s; try { s = JSON.parse(body.session); } catch (_) { return json(res, 400, { ok: false, error: 'Bad session payload' }); }
      const list = readJson(F.openplays, []);
      s.photos = [];
      const i = list.findIndex(x => String(x.id) === String(s.id));
      if (i >= 0) list[i] = s; else list.push(s);
      list.sort((a, b) => (b.endedAt || 0) - (a.endedAt || 0));
      writeJson(F.openplays, list);
      return json(res, 200, { ok: true, photos: [] });
    }
    case 'delete': {
      if (!isAdmin) return needAdmin();
      writeJson(F.openplays, readJson(F.openplays, []).filter(x => String(x.id) !== String(body.id)));
      return json(res, 200, { ok: true });
    }
    case 'upload': case 'deletePhoto':
      // Photos are stored on the host; locally we just report an empty album so the page still works.
      return json(res, 200, { ok: true, photos: [] });

    case 'rsvpLookup': {
      if (!isAdmin) return needAdmin();
      const url = String(body.url || '').trim();
      if (!/^https:\/\//i.test(url)) return json(res, 400, { ok: false, error: 'Paste the full https link' });
      if (!rsvpHostAllowed(url)) return json(res, 400, { ok: false, error: 'Only ' + RSVP_HOSTS.join(', ') + ' links can be read' });
      try {
        const r = await fetch(url, { headers: { 'User-Agent': 'KimchiJjigaePickleballClub/1.0 (+roster import, local dev)' } });
        if (!r.ok) return json(res, 502, { ok: false, error: 'Could not reach that page' });
        const html = await r.text();
        return json(res, 200, { ok: true, ...parseRsvpEvent(html), ...parseRsvpNames(html) });
      } catch (e) { return json(res, 502, { ok: false, error: 'Could not reach that page' }); }
    }

    case 'rsvp': {
      if (!isAdmin) return needAdmin();
      const ev = readUpcoming().find(e => String(e.id) === String(body.id));
      if (!ev) return json(res, 404, { ok: false, error: 'That open play is not on the schedule' });
      if (!ev.rsvp) return json(res, 400, { ok: false, error: 'That open play has no RSVP link' });
      try {
        const r = await fetch(ev.rsvp, { headers: { 'User-Agent': 'KimchiJjigaePickleballClub/1.0 (+roster import, local dev)' } });
        if (!r.ok) return json(res, 502, { ok: false, error: 'Could not reach the RSVP page' });
        return json(res, 200, { ok: true, ...parseRsvpNames(await r.text()) });
      } catch (e) {
        return json(res, 502, { ok: false, error: 'Could not reach the RSVP page' });
      }
    }

    default:
      return json(res, 404, { ok: false, error: 'Unknown action' });
  }
}

http.createServer((req, res) => {
  const url = new URL(req.url, 'http://localhost');
  const chunks = [];
  req.on('data', c => chunks.push(c));
  req.on('end', async () => {
    try {
      if (url.pathname === '/api.php') {
        const body = parseForm(Buffer.concat(chunks), req.headers['content-type']);
        return await handleApi(req, res, url, body);
      }
      let p = decodeURIComponent(url.pathname);
      if (p === '/') p = '/index.html';
      const file = path.join(ROOT, p);
      if (!file.startsWith(ROOT)) return send(res, 403, 'Forbidden', 'text/plain');
      fs.readFile(file, (err, data) => {
        if (err) return send(res, 404, 'Not found', 'text/plain');
        send(res, 200, data, TYPES[path.extname(file).toLowerCase()] || 'application/octet-stream');
      });
    } catch (e) {
      json(res, 500, { ok: false, error: String(e && e.message || e) });
    }
  });
}).listen(PORT, () => {
  console.log('Kimchi Jjigae Pickleball Club — local dev server');
  console.log('  app:     http://localhost:' + PORT);
  console.log('  2nd device: http://127.0.0.1:' + PORT + '   (separate login, same server)');
  console.log('  admin PIN: ' + PIN_SOURCE);
  console.log('  data:    data/live.json, data/upcoming.json, data/openplays.json  (all git-ignored)');
  console.log('Press Ctrl+C to stop.');
});
