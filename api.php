<?php
/* Kimchi Jjigae Pickleball Club — publishing endpoint.
 *
 * The website keeps one official record of finished open plays in data/openplays.json and the
 * photos in data/photos/<sessionId>/. The browser app reads the JSON directly; only admins write,
 * through this file. The admin PIN is the credential: the app sends SHA-256(pin) in the
 * X-Admin-Key header, and a password_hash of that is kept in data/.admin (the first PIN claims it).
 *
 * GET  ?action=status                        -> { server:true, pin:bool }
 * POST ?action=claim        key              -> set the admin key if none exists yet
 * POST ?action=login        key              -> { ok, reason? }
 * POST ?action=publish      key, session     -> upsert one open play (JSON string); server keeps its own photo list
 * POST ?action=delete       key, id          -> remove an open play and its photos
 * POST ?action=upload       key, id, file    -> add a photo to an open play; returns the full photo list
 * POST ?action=deletePhoto  key, id, photo   -> remove one photo
 * GET  ?action=upcoming                      -> { events:[...] }  scheduled open plays (seeded from data/upcoming.seed.json)
 * POST ?action=saveUpcoming key, events      -> replace the scheduled list (JSON array)
 */
declare(strict_types=1);
header('Content-Type: application/json; charset=utf-8');
header('Cache-Control: no-store');

const DATA_DIR   = __DIR__ . '/data';
const PHOTO_DIR  = DATA_DIR . '/photos';
const DATA_FILE  = DATA_DIR . '/openplays.json';
const ADMIN_FILE = DATA_DIR . '/.admin';
const LOCK_FILE  = DATA_DIR . '/.lock';
const UP_FILE    = DATA_DIR . '/upcoming.json';       // live list, edited by admins in the app
const UP_SEED    = DATA_DIR . '/upcoming.seed.json';  // committed starting point, used once when the live file is missing
const MAX_EVENTS = 60;
/* Fixed admin PIN (optional). Leave empty to let the first PIN entered on the site claim admin (stored in
 * data/.admin). To set or change the PIN by hand, put the SHA-256 hex of the PIN here — on any machine:
 *   node -e "console.log(require('crypto').createHash('sha256').update('YOUR_PIN').digest('hex'))"
 * A PIN set here overrides data/.admin. */
const ADMIN_KEY_FIXED = 'e877153ecba1c2858b9f0a8168dbf6f4eeb13c21d1f9b8d8fd814bf7d0635969';
const MAX_BYTES  = 12 * 1024 * 1024;
const MAX_PHOTOS = 60;
const MAX_SESSION_JSON = 4 * 1024 * 1024;

function out(array $o, int $code = 200): void { http_response_code($code); echo json_encode($o, JSON_UNESCAPED_UNICODE | JSON_UNESCAPED_SLASHES); exit; }
function fail(string $msg, int $code = 400): void { out(['ok' => false, 'error' => $msg], $code); }
function cleanId(?string $s): string { return preg_replace('/[^A-Za-z0-9_-]/', '', (string)$s); }
function adminHash(): ?string { return is_file(ADMIN_FILE) ? trim((string)file_get_contents(ADMIN_FILE)) : null; }
function pinIsSet(): bool { return ADMIN_KEY_FIXED !== '' || adminHash() !== null; }
function keyMatches(string $k): bool {
  if ($k === '') return false;
  if (ADMIN_KEY_FIXED !== '') return hash_equals(strtolower(ADMIN_KEY_FIXED), strtolower($k));
  $h = adminHash(); return $h !== null && password_verify($k, $h);
}
function keyFromRequest(): string {
  // Header first (logged-in admin), else the form field (login/claim). An empty header must fall through.
  $k = (string)($_SERVER['HTTP_X_ADMIN_KEY'] ?? '');
  if ($k === '') $k = (string)($_POST['key'] ?? '');
  return preg_replace('/[^a-f0-9:]/i', '', $k);
}
function requireAdmin(): void {
  if (!keyMatches(keyFromRequest())) { usleep(300000); fail('Admin PIN required', 401); }
}
function requirePost(): void { if ($_SERVER['REQUEST_METHOD'] !== 'POST') fail('POST only', 405); }

/* ---- the JSON file, always edited under a lock ---- */
function withLock(callable $fn) {
  $lk = fopen(LOCK_FILE, 'c'); if (!$lk || !flock($lk, LOCK_EX)) fail('Busy, try again', 503);
  try { return $fn(); } finally { flock($lk, LOCK_UN); fclose($lk); }
}
function readAll(): array {
  if (!is_file(DATA_FILE)) return [];
  $j = json_decode((string)file_get_contents(DATA_FILE));
  return is_array($j) ? $j : [];
}
function writeAll(array $list): void {
  usort($list, fn($a, $b) => (($b->endedAt ?? 0) <=> ($a->endedAt ?? 0)));
  $tmp = DATA_FILE . '.tmp';
  if (file_put_contents($tmp, json_encode(array_values($list), JSON_UNESCAPED_UNICODE | JSON_UNESCAPED_SLASHES)) === false) fail('Cannot write data file', 500);
  if (!rename($tmp, DATA_FILE)) fail('Cannot replace data file', 500);
  @chmod(DATA_FILE, 0644);
}
function findIdx(array $list, string $id): int { foreach ($list as $i => $s) if (cleanId((string)($s->id ?? '')) === $id) return $i; return -1; }
function photoList(string $id): array {
  $d = PHOTO_DIR . '/' . $id; $res = [];
  foreach (is_dir($d) ? (glob($d . '/*.jpg') ?: []) : [] as $f) {
    $pid = basename($f, '.jpg');
    $res[] = ['id' => $pid, 'url' => 'data/photos/' . $id . '/' . $pid . '.jpg', 'addedAt' => filemtime($f) * 1000];
  }
  usort($res, fn($a, $b) => $a['addedAt'] <=> $b['addedAt']);
  return $res;
}

function readUpcoming(): array {
  if (!is_file(UP_FILE) && is_file(UP_SEED)) @copy(UP_SEED, UP_FILE);
  if (!is_file(UP_FILE)) return [];
  $j = json_decode((string)file_get_contents(UP_FILE), true);
  return is_array($j) ? array_values($j) : [];
}
/* Keep only well-formed events; anything else is dropped rather than stored. */
function cleanEvents(array $in): array {
  $out = [];
  foreach ($in as $e) {
    if (!is_array($e)) continue;
    $start = (string)($e['start'] ?? '');
    if (!preg_match('/^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}$/', $start)) continue;
    $rsvp = trim((string)($e['rsvp'] ?? ''));
    if ($rsvp !== '' && (!filter_var($rsvp, FILTER_VALIDATE_URL) || !preg_match('#^https?://#i', $rsvp))) $rsvp = '';
    $out[] = [
      'id'    => cleanId((string)($e['id'] ?? '')) ?: ('up_' . bin2hex(random_bytes(4))),
      'title' => mb_substr(trim((string)($e['title'] ?? '')), 0, 120),
      'start' => $start,
      'venue' => mb_substr(trim((string)($e['venue'] ?? '')), 0, 120),
      'rsvp'  => mb_substr($rsvp, 0, 300),
    ];
    if (count($out) >= MAX_EVENTS) break;
  }
  usort($out, fn($a, $b) => strcmp($a['start'], $b['start']));
  return $out;
}

if (!is_dir(PHOTO_DIR) && !mkdir(PHOTO_DIR, 0755, true)) fail('data/photos folder missing and cannot be created', 500);

$action = $_GET['action'] ?? $_POST['action'] ?? '';
switch ($action) {
  case 'status':
    out(['server' => true, 'pin' => pinIsSet()]);

  case 'claim':
    requirePost();
    if (pinIsSet()) fail('An admin PIN already exists', 409);
    $k = keyFromRequest(); if (strlen($k) < 8) fail('Bad key');
    if (file_put_contents(ADMIN_FILE, password_hash($k, PASSWORD_DEFAULT), LOCK_EX) === false) fail('Cannot save PIN', 500);
    @chmod(ADMIN_FILE, 0600);
    out(['ok' => true]);

  case 'login':
    requirePost();
    if (!pinIsSet()) out(['ok' => false, 'reason' => 'nopin']);
    if (keyMatches(keyFromRequest())) out(['ok' => true]);
    usleep(300000); out(['ok' => false, 'reason' => 'wrong']);

  case 'publish':
    requirePost(); requireAdmin();
    $raw = (string)($_POST['session'] ?? '');
    if ($raw === '' || strlen($raw) > MAX_SESSION_JSON) fail('Bad session payload');
    $s = json_decode($raw);
    if (!is_object($s) || !isset($s->id)) fail('Bad session payload');
    $id = cleanId((string)$s->id); if ($id === '' || $id === 'live') fail('Bad session id');
    $photos = withLock(function () use ($s, $id) {
      $list = readAll(); $i = findIdx($list, $id);
      $s->photos = photoList($id);                  // the server owns the photo list
      if ($i >= 0) $list[$i] = $s; else $list[] = $s;
      writeAll($list);
      return $s->photos;
    });
    out(['ok' => true, 'photos' => $photos]);

  case 'delete':
    requirePost(); requireAdmin();
    $id = cleanId($_POST['id'] ?? ''); if ($id === '') fail('Bad session id');
    withLock(function () use ($id) {
      $list = readAll(); $i = findIdx($list, $id);
      if ($i >= 0) { array_splice($list, $i, 1); writeAll($list); }
      $d = PHOTO_DIR . '/' . $id;
      if (is_dir($d)) { foreach (glob($d . '/*') ?: [] as $f) @unlink($f); @rmdir($d); }
    });
    out(['ok' => true]);

  case 'upload':
    requirePost(); requireAdmin();
    $id = cleanId($_POST['id'] ?? ''); if ($id === '' || $id === 'live') fail('Bad session id');
    if (!isset($_FILES['file']) || $_FILES['file']['error'] !== UPLOAD_ERR_OK) fail('No file received');
    $f = $_FILES['file'];
    if ($f['size'] > MAX_BYTES) fail('File too large');
    $info = @getimagesize($f['tmp_name']);
    if (!$info || !in_array($info[2], [IMAGETYPE_JPEG, IMAGETYPE_PNG, IMAGETYPE_WEBP, IMAGETYPE_GIF], true)) fail('Not an image');
    if (count(photoList($id)) >= MAX_PHOTOS) fail('Photo limit reached for this open play');
    $d = PHOTO_DIR . '/' . $id;
    if (!is_dir($d) && !mkdir($d, 0755, true)) fail('Cannot create folder', 500);
    $pid = 'ph_' . (int)round(microtime(true) * 1000) . '_' . bin2hex(random_bytes(3));
    $dest = $d . '/' . $pid . '.jpg'; $saved = false;
    if (function_exists('imagecreatefromstring')) {          // re-encode so only a real JPEG lands on disk
      $img = @imagecreatefromstring((string)file_get_contents($f['tmp_name']));
      if ($img) { $saved = imagejpeg($img, $dest, 82); imagedestroy($img); }
    }
    if (!$saved) {
      if ($info[2] !== IMAGETYPE_JPEG) fail('Server cannot convert this image; upload a JPEG');
      $saved = move_uploaded_file($f['tmp_name'], $dest);
    }
    if (!$saved) fail('Could not write file', 500);
    @chmod($dest, 0644);
    $photos = withLock(function () use ($id) {
      $list = readAll(); $i = findIdx($list, $id);
      if ($i < 0) { $list[] = (object)['id' => $id, 'photos' => []]; $i = count($list) - 1; }
      $list[$i]->photos = photoList($id);
      writeAll($list);
      return $list[$i]->photos;
    });
    out(['ok' => true, 'photos' => $photos]);

  case 'deletePhoto':
    requirePost(); requireAdmin();
    $id = cleanId($_POST['id'] ?? ''); $pid = cleanId($_POST['photo'] ?? '');
    if ($id === '' || $pid === '') fail('Bad id');
    $p = PHOTO_DIR . '/' . $id . '/' . $pid . '.jpg';
    if (is_file($p)) unlink($p);
    $photos = withLock(function () use ($id) {
      $list = readAll(); $i = findIdx($list, $id);
      if ($i >= 0) { $list[$i]->photos = photoList($id); writeAll($list); return $list[$i]->photos; }
      return [];
    });
    $d = PHOTO_DIR . '/' . $id; if (is_dir($d) && !glob($d . '/*')) @rmdir($d);
    out(['ok' => true, 'photos' => $photos]);

  case 'upcoming':
    out(['events' => readUpcoming()]);

  case 'saveUpcoming':
    requirePost(); requireAdmin();
    $raw = (string)($_POST['events'] ?? '');
    if ($raw === '' || strlen($raw) > 512 * 1024) fail('Bad events payload');
    $in = json_decode($raw, true);
    if (!is_array($in)) fail('Bad events payload');
    $events = cleanEvents($in);
    $saved = withLock(function () use ($events) {
      $tmp = UP_FILE . '.tmp';
      if (file_put_contents($tmp, json_encode($events, JSON_UNESCAPED_UNICODE | JSON_UNESCAPED_SLASHES | JSON_PRETTY_PRINT)) === false) fail('Cannot write events', 500);
      if (!rename($tmp, UP_FILE)) fail('Cannot replace events file', 500);
      @chmod(UP_FILE, 0644);
      return $events;
    });
    out(['ok' => true, 'events' => $saved]);

  default:
    fail('Unknown action', 404);
}
