// Browser viewer and setup page for the encrypted X Digest site (Jack, 2026-10-20); public, holds no secrets.
// Same scheme as lib/x-digest-crypto.mjs: PBKDF2-SHA256(passcode, salt, iter) -> P-256 scalar d; the
// per-publish content key is sealed to d·G with ephemeral ECDH + HKDF-SHA256 + AES-GCM.
(function () {
  'use strict';
  var subtle = crypto.subtle, enc = new TextEncoder();
  var P = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffffn;
  var N = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551n;
  var GX = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296n;
  var GY = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5n;
  var WRAP_INFO = 'x-digest-v1 content-key wrap', DB = 'x-digest', REMEMBER_MS = 90 * 864e5;
  // Keep/Delete inbox (Jack, 2026-10-20: "keep delete button, make them work"): a tap PUTs decisions/<day>-<n>.json
  // into the private repo xhliu/digest-inbox with Jack's own fine-grained token; the Mac polls it (x-digest-inbox-poll.sh),
  // runs Bajie's decide.mjs and writes results/<day>-<n>.json back. The token is sealed to the lock's public key, like
  // the content key, so only an unlocked page can open it, and it is only ever sent to api.github.com.
  var INBOX_REPO = 'xhliu/digest-inbox', GH_API = 'https://api.github.com', TOKEN_INFO = 'x-digest-v1 inbox token';
  var INBOX = { inboxKey: inboxKey, putDecision: putDecision, archiveAll: archiveAll, readStates: readStates, statusText: statusText, sealToken: sealToken, openToken: openToken };
  if (typeof document === 'undefined') { if (typeof module !== 'undefined') module.exports = INBOX; return; }
  var body = document.body, root = body.getAttribute('data-root') || './';

  function b64u(bytes) { var s = ''; bytes = new Uint8Array(bytes); for (var i = 0; i < bytes.length; i++) s += String.fromCharCode(bytes[i]); return btoa(s).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, ''); }
  function unb64u(s) { s = String(s).replace(/-/g, '+').replace(/_/g, '/'); while (s.length % 4) s += '='; var b = atob(s), o = new Uint8Array(b.length); for (var i = 0; i < b.length; i++) o[i] = b.charCodeAt(i); return o; }
  function toBig(bytes) { var h = ''; for (var i = 0; i < bytes.length; i++) h += bytes[i].toString(16).padStart(2, '0'); return BigInt('0x' + (h || '0')); }
  function toBytes(n) { var h = n.toString(16).padStart(64, '0'), o = new Uint8Array(32); for (var i = 0; i < 32; i++) o[i] = parseInt(h.substr(i * 2, 2), 16); return o; }
  function md(a) { a %= P; return a < 0n ? a + P : a; }
  function inv(a) { var r = 1n, b = md(a), e = P - 2n; while (e > 0n) { if (e & 1n) r = r * b % P; b = b * b % P; e >>= 1n; } return r; }
  // Jacobian point arithmetic on P-256 (a = -3); only used to turn the derived scalar into its public point.
  function dbl(p) {
    if (p[2] === 0n) return p;
    var y2 = md(p[1] * p[1]), s = md(4n * p[0] * y2), z2 = md(p[2] * p[2]), m = md(3n * (p[0] - z2) * (p[0] + z2));
    var x = md(m * m - 2n * s); return [x, md(m * (s - x) - 8n * y2 * y2), md(2n * p[1] * p[2])];
  }
  function add(p, q) {
    if (p[2] === 0n) return q; if (q[2] === 0n) return p;
    var z1 = md(p[2] * p[2]), z2 = md(q[2] * q[2]), u1 = md(p[0] * z2), u2 = md(q[0] * z1), s1 = md(p[1] * z2 * q[2]), s2 = md(q[1] * z1 * p[2]);
    if (u1 === u2) return s1 === s2 ? dbl(p) : [1n, 1n, 0n];
    var h = md(u2 - u1), r = md(s2 - s1), h2 = md(h * h), h3 = md(h2 * h), v = md(u1 * h2);
    var x = md(r * r - h3 - 2n * v); return [x, md(r * (v - x) - s1 * h3), md(h * p[2] * q[2])];
  }
  function pubFromScalar(d) {
    var R = [1n, 1n, 0n], Q = [GX, GY, 1n];
    while (d > 0n) { if (d & 1n) R = add(R, Q); Q = dbl(Q); d >>= 1n; }
    var zi = inv(R[2]), zi2 = md(zi * zi), out = new Uint8Array(65);
    out[0] = 4; out.set(toBytes(md(R[0] * zi2)), 1); out.set(toBytes(md(R[1] * zi2 * zi)), 33); return out;
  }
  function normalize(p) { return String(p).normalize('NFKC').trim().replace(/\s+/g, ' '); }
  function deriveScalar(passcode, salt, iter) {
    return subtle.importKey('raw', enc.encode(normalize(passcode)), 'PBKDF2', false, ['deriveBits']).then(function (k) {
      return subtle.deriveBits({ name: 'PBKDF2', hash: 'SHA-256', salt: salt, iterations: iter }, k, 256);
    }).then(function (bits) { var d = toBig(new Uint8Array(bits)) % N; return d === 0n ? 1n : d; });
  }
  function eq(a, b) { if (a.length !== b.length) return false; for (var i = 0; i < a.length; i++) if (a[i] !== b[i]) return false; return true; }

  // ---------- Keep/Delete inbox helpers (pure; test-workflow.sh loads them in node) ----------
  // Day lists use <day>-<n>; the rolling inbox (Jack, 2026-10-26) uses inbox-<n>, n = the story's stable number.
  function inboxKey(day, n) {
    if (day === 'inbox') return /^[1-9]\d{0,4}$/.test(String(n)) ? 'inbox-' + n : null;
    return /^\d{4}-\d{2}-\d{2}$/.test(String(day)) && /^[1-9]\d{0,3}$/.test(String(n)) ? day + '-' + n : null;
  }
  function gh(api, token, method, p, body) {
    var h = { Authorization: 'Bearer ' + token, Accept: 'application/vnd.github+json' };
    if (body) h['Content-Type'] = 'application/json';
    return fetch(api + '/repos/' + INBOX_REPO + (p ? '/contents/' + p : ''), { method: method, cache: 'no-store', headers: h, body: body ? JSON.stringify(body) : undefined });
  }
  function httpError(r) { var e = new Error('HTTP ' + r.status); e.status = r.status; return e; }
  // Create-only (no sha): a second tap, or a second device, gets 422 because the file exists, so it is already queued.
  function putDecision(api, token, day, n, verb) {
    var key = inboxKey(day, n);
    if (!key || (verb !== 'keep' && verb !== 'delete')) return Promise.reject(new Error('bad decision'));
    var json = JSON.stringify({ verb: verb, at: new Date().toISOString() });
    return gh(api, token, 'PUT', 'decisions/' + key + '.json', { message: verb + ' ' + key, content: btoa(json) }).then(function (r) {
      if (r.status === 200 || r.status === 201 || r.status === 422) return { state: 'queued', verb: verb };
      throw httpError(r);
    });
  }
  // "Archive all" on the inbox's news pile: one delete decision per story, one after another; a failure stops the rest.
  function archiveAll(api, token, ns, onEach) {
    var out = {};
    return ns.reduce(function (p, n) {
      return p.then(function () { return putDecision(api, token, 'inbox', n, 'delete'); }).then(function (s) { out[n] = s; if (onEach) onEach(n, s); });
    }, Promise.resolve()).then(function () { return out; });
  }
  function getJson(api, token, p) {
    return gh(api, token, 'GET', p).then(function (r) {
      if (r.status === 404) return null;
      if (!r.ok) throw httpError(r);
      return r.json();
    });
  }
  function fileJson(api, token, p) {
    return getJson(api, token, p).then(function (f) {
      if (!f || !f.content) return null;
      try { return JSON.parse(atob(String(f.content).replace(/\s/g, ''))); } catch (e) { return {}; }
    });
  }
  // keys -> { key: {state: queued|done|failed|ignored, verb, folder, why} } for the keys that have a decision.
  function readStates(api, token, keys) {
    var names = function (list) { var o = {}; (Array.isArray(list) ? list : []).forEach(function (f) { o[f.name] = 1; }); return o; };
    return Promise.all([getJson(api, token, 'decisions'), getJson(api, token, 'results')]).then(function (ls) {
      var dec = names(ls[0]), res = names(ls[1]), out = {};
      return Promise.all(keys.map(function (k) {
        if (res[k + '.json']) return fileJson(api, token, 'results/' + k + '.json').then(function (r) { r = r || {}; out[k] = { state: r.status || 'failed', folder: r.folder, why: r.why }; });
        if (dec[k + '.json']) return fileJson(api, token, 'decisions/' + k + '.json').then(function (d) { out[k] = { state: 'queued', verb: d && d.verb }; });
      })).then(function () { return out; });
    });
  }
  function statusText(s) {
    if (!s) return '';
    if (s.state === 'queued') return '⏳ Queued' + (s.verb ? ' (' + (s.verb === 'delete' ? 'Delete' : 'Keep') + ')' : '') + ', filing on the Mac…';
    if (s.state === 'done') return s.folder === 'Archived' ? '🗑 Archived' : '✓ Saved';
    if (s.state === 'ignored') return 'Ignored (' + (s.why || 'not in the current list') + ')';
    return '⚠️ Failed (' + (s.why || 'unknown') + '). Decide it in Telegram.';
  }
  // ECIES to the lock's public key, same construction as the content-key seal: anyone can seal, only the passcode opens.
  function tokenKek(shared, ephPub, use) {
    return subtle.importKey('raw', shared, 'HKDF', false, ['deriveKey']).then(function (hk) {
      return subtle.deriveKey({ name: 'HKDF', hash: 'SHA-256', salt: ephPub, info: enc.encode(TOKEN_INFO) }, hk, { name: 'AES-GCM', length: 256 }, false, [use]);
    });
  }
  function sealToken(token, lockPub) {
    var eph, ephPub, iv = crypto.getRandomValues(new Uint8Array(12));
    return subtle.generateKey({ name: 'ECDH', namedCurve: 'P-256' }, true, ['deriveBits']).then(function (k) {
      eph = k; return subtle.exportKey('raw', k.publicKey);
    }).then(function (raw) {
      ephPub = new Uint8Array(raw);
      return subtle.importKey('raw', lockPub, { name: 'ECDH', namedCurve: 'P-256' }, false, []);
    }).then(function (pub) { return subtle.deriveBits({ name: 'ECDH', public: pub }, eph.privateKey, 256); }).then(function (shared) {
      return tokenKek(shared, ephPub, 'encrypt');
    }).then(function (kek) { return subtle.encrypt({ name: 'AES-GCM', iv: iv }, kek, enc.encode(token)); }).then(function (ct) {
      return { eph: b64u(ephPub), iv: b64u(iv), ct: b64u(ct) };
    });
  }
  function openToken(rec, priv) {
    var ephPub = unb64u(rec.eph);
    return subtle.importKey('raw', ephPub, { name: 'ECDH', namedCurve: 'P-256' }, false, []).then(function (eph) {
      return subtle.deriveBits({ name: 'ECDH', public: eph }, priv, 256);
    }).then(function (shared) { return tokenKek(shared, ephPub, 'decrypt'); }).then(function (kek) {
      return subtle.decrypt({ name: 'AES-GCM', iv: unb64u(rec.iv) }, kek, unb64u(rec.ct));
    }).then(function (b) { return new TextDecoder().decode(b); });
  }

  // ---------- setup page ----------
  if (body.getAttribute('data-mode') === 'setup') { setup(); return; }
  function setup() {
    var $ = function (id) { return document.getElementById(id); }, words = [], wordSet = {};
    fetch(root + 'words.txt').then(function (r) { return r.text(); }).then(function (t) {
      words = t.split('\n').filter(Boolean); words.forEach(function (w) { wordSet[w] = 1; }); $('gen').disabled = false; check();
    });
    function bits(p) {
      p = normalize(p); if (!p) return 0;
      var toks = p.toLowerCase().split(/[\s\-_.]+/).filter(Boolean), total = 0, wb = Math.log2(words.length || 1);
      var seen = {};
      toks.forEach(function (t) {
        if (seen[t]) return; seen[t] = 1;
        if (wordSet[t]) { total += wb; return; }
        var pool = (/[a-z]/.test(t) ? 26 : 0) + (/[A-Z]/.test(t) ? 26 : 0) + (/[0-9]/.test(t) ? 10 : 0) + (/[^a-zA-Z0-9]/.test(t) ? 33 : 0);
        var uniq = Object.keys(t.split('').reduce(function (o, c) { o[c] = 1; return o; }, {})).length;
        total += Math.min(t.length, uniq * 1.5) * Math.log2(pool || 1);
      });
      if (toks.length === 1 && !wordSet[toks[0]]) {
        var raw = p, pool2 = (/[a-z]/.test(raw) ? 26 : 0) + (/[A-Z]/.test(raw) ? 26 : 0) + (/[0-9]/.test(raw) ? 10 : 0) + (/[^a-zA-Z0-9]/.test(raw) ? 33 : 0);
        total = Math.min(total, raw.length * Math.log2(pool2 || 1));
      }
      return Math.floor(total);
    }
    function check() {
      var a = $('p1').value, b = $('p2').value, n = bits(a), ok = n >= 60 && a === b;
      $('meter').textContent = a ? ('Strength: about ' + n + ' bits' + (n >= 60 ? ' ✓' : ' — need 60+ (e.g. 5 random words)')) : '';
      $('meter').className = n >= 60 ? 'ok' : 'bad';
      $('match').textContent = b && a !== b ? 'The two entries do not match.' : '';
      $('make').disabled = !ok; return ok;
    }
    $('p1').oninput = $('p2').oninput = check;
    $('gen').onclick = function () {
      var out = [], r = new Uint32Array(1);
      while (out.length < 5) { crypto.getRandomValues(r); var lim = Math.floor(4294967296 / words.length) * words.length; if (r[0] < lim) out.push(words[r[0] % words.length]); }
      $('p1').value = $('p2').value = out.join(' '); $('p1').type = 'text'; check();
    };
    $('make').onclick = function () {
      if (!check()) return;
      $('make').disabled = true; $('status').textContent = 'Deriving key (600,000 PBKDF2 rounds)…';
      var salt = crypto.getRandomValues(new Uint8Array(16)), iter = 600000, t0 = performance.now();
      deriveScalar($('p1').value, salt, iter).then(function (d) {
        var lock = { v: 1, kdf: 'PBKDF2-SHA256', iter: iter, salt: b64u(salt), pub: b64u(pubFromScalar(d)) };
        $('lock').value = b64u(enc.encode(JSON.stringify(lock)));
        $('status').textContent = 'Done in ' + Math.round(performance.now() - t0) + ' ms. Copy the lock code below. Keep the passcode somewhere safe: it is never stored or sent, and nobody can recover it.';
        $('out').hidden = false; $('make').disabled = false;
      }, function (e) { $('status').textContent = 'Failed: ' + e; $('make').disabled = false; });
    };
    $('copy').onclick = function () { $('lock').select(); (navigator.clipboard ? navigator.clipboard.writeText($('lock').value) : Promise.reject()).then(function () { $('copy').textContent = 'Copied ✓'; }, function () { document.execCommand('copy'); $('copy').textContent = 'Copied ✓'; }); };
  }

  // ---------- viewer ----------
  var path = body.getAttribute('data-path'), manifest, ui = document.getElementById('xl'), priv = null, ckRaw = null;
  // The live bookmarks list can carry Jack's inbox token inside the encrypted payload (Jack, 2026-10-23: "no pasting").
  var builtInToken = null;
  function show(id, text) { var el = document.getElementById(id); if (el) el.textContent = text || ''; }
  function idb(fn) {
    return new Promise(function (res, rej) {
      var o = indexedDB.open(DB, 1);
      o.onupgradeneeded = function () { o.result.createObjectStore('keys'); };
      o.onerror = function () { rej(o.error); };
      o.onsuccess = function () { var tx = o.result.transaction('keys', 'readwrite'), r = fn(tx.objectStore('keys')); tx.oncomplete = function () { res(r && r.result); }; tx.onerror = function () { rej(tx.error); }; };
    });
  }
  function forget() {
    try { sessionStorage.clear(); } catch (e) {}
    return idb(function (s) { s.delete('gh'); return s.delete('device'); }).catch(function () {}).then(function () { location.reload(); });
  }
  function importPriv(d, pub) {
    return subtle.importKey('jwk', { kty: 'EC', crv: 'P-256', d: b64u(toBytes(d)), x: b64u(pub.slice(1, 33)), y: b64u(pub.slice(33)), ext: false },
      { name: 'ECDH', namedCurve: 'P-256' }, false, ['deriveBits']);
  }
  function openSeal(priv) {
    var s = manifest.seal, ephPub = unb64u(s.eph);
    return subtle.importKey('raw', ephPub, { name: 'ECDH', namedCurve: 'P-256' }, false, []).then(function (eph) {
      return subtle.deriveBits({ name: 'ECDH', public: eph }, priv, 256);
    }).then(function (shared) { return subtle.importKey('raw', shared, 'HKDF', false, ['deriveKey']); }).then(function (hk) {
      return subtle.deriveKey({ name: 'HKDF', hash: 'SHA-256', salt: ephPub, info: enc.encode(WRAP_INFO) }, hk, { name: 'AES-GCM', length: 256 }, false, ['decrypt']);
    }).then(function (kek) { return subtle.decrypt({ name: 'AES-GCM', iv: unb64u(s.iv) }, kek, unb64u(s.key)); });
  }
  function useRaw(raw) {
    ckRaw = raw;
    try { sessionStorage.setItem('xd-ck-' + manifest.id, b64u(raw)); } catch (e) {}
    return subtle.importKey('raw', raw, 'AES-GCM', false, ['decrypt']);
  }
  function fetchBlob(key, name) {
    return fetch(root + name).then(function (r) { if (!r.ok) throw new Error('HTTP ' + r.status + ' for ' + name); return r.arrayBuffer(); }).then(function (buf) {
      var b = new Uint8Array(buf);
      return subtle.decrypt({ name: 'AES-GCM', iv: b.slice(0, 12), additionalData: enc.encode(name) }, key, b.slice(12));
    });
  }
  function gunzip(buf) { return new Response(new Blob([buf]).stream().pipeThrough(new DecompressionStream('gzip'))).text(); }
  function sitePath(url) {
    var base = new URL(root, location.href).href, u = new URL(url, location.href);
    if (u.origin !== location.origin || u.href.indexOf(base) !== 0) return null;
    return decodeURIComponent(u.href.slice(base.length).split('#')[0].split('?')[0]);
  }

  function render(key) {
    var t0 = performance.now(), map;
    show('st', 'Decrypting…');
    return fetchBlob(key, manifest.map).then(gunzip).then(function (j) {
      map = JSON.parse(j); var ent = map[path];
      var tk = map[String(path).replace(/index\.html$/, '') + 'inbox.token'];
      builtInToken = tk ? function () { return fetchBlob(key, tk.b).then(function (b) { return new TextDecoder().decode(b).trim() || null; }, function () { return null; }); } : null;
      if (!ent) throw new Error('This page is not in the current publish.');
      return fetchBlob(key, ent.b).then(gunzip);
    }).then(function (html) {
      var doc = new DOMParser().parseFromString(html, 'text/html'), pending = [];
      doc.querySelectorAll('[src]').forEach(function (el) {
        var p = sitePath(el.getAttribute('src'));
        if (p === null) return;
        // Audio/video decrypt on demand (a bookmarks list is ~25 MB); unpublished audio says so instead of 404ing.
        if (/^(AUDIO|VIDEO)$/.test(el.tagName)) {
          el.removeAttribute('src');
          if (map[p]) { el.setAttribute('data-xa', p); el.setAttribute('preload', 'none'); } else {
            var na = doc.createElement('span'); na.className = 'muted'; na.textContent = 'No audio (older list)'; el.replaceWith(na);
          }
          return;
        }
        if (map[p]) { el.setAttribute('data-xs', p); el.removeAttribute('src'); }
      });
      // The page's own Keep/Delete script posts to the local server; here the buttons go through the inbox instead.
      doc.querySelectorAll('script').forEach(function (s) { if (/bookmarks\/decide/.test(s.textContent)) s.remove(); });
      doc.querySelectorAll('a[href]').forEach(function (a) {
        var p = sitePath(a.getAttribute('href'));
        if (p === null || !/\.(m4a|mp3|mp4)$/i.test(p)) return;
        if (map[p]) { a.setAttribute('data-xa', p); a.removeAttribute('target'); } else a.remove();
      });
      var foot = doc.createElement('div');
      foot.setAttribute('style', 'text-align:center;padding:18px 0 28px;font:12px -apple-system,sans-serif;opacity:.7');
      var fb = 'style="font:inherit;background:none;border:1px solid currentColor;border-radius:12px;padding:2px 10px;color:inherit;cursor:pointer"';
      foot.innerHTML = '🔒 End-to-end encrypted · <button type="button" id="xd-forget" ' + fb + '>Forget this device</button><span id="xd-disc-w" hidden> · <button type="button" id="xd-disc" ' + fb + '>Disconnect buttons</button></span>';
      doc.body.appendChild(foot);
      var pageMs = performance.now() - t0;
      document.open(); document.write('<!doctype html>' + doc.documentElement.outerHTML); document.close();
      document.getElementById('xd-forget').onclick = forget;
      initDecide();
      document.querySelectorAll('[data-xs]').forEach(function (el) {
        var ent = map[el.getAttribute('data-xs')];
        pending.push(fetchBlob(key, ent.b).then(function (buf) { el.setAttribute('src', URL.createObjectURL(new Blob([buf], { type: ent.t }))); }, function () {}));
      });
      // On-demand media: the first play or "Open audio" fetches and decrypts the whole file into a blob URL,
      // which iOS Safari plays and seeks without range requests.
      var media = {};
      function mediaUrl(p) {
        if (!media[p]) media[p] = fetchBlob(key, map[p].b).then(function (buf) { return URL.createObjectURL(new Blob([buf], { type: map[p].t })); });
        return media[p];
      }
      document.querySelectorAll('audio[data-xa],video[data-xa]').forEach(function (el) {
        // Safari shows no usable control for a source-less <audio>, so a button loads it. load() inside the tap
        // unlocks the element, so play() still counts as user-initiated after the async decrypt.
        var btn = document.createElement('button');
        btn.type = 'button'; btn.className = 'xd-play'; btn.textContent = '▶ Load & play';
        btn.setAttribute('style', 'font:inherit;padding:6px 14px;border-radius:16px;border:1px solid currentColor;background:none;color:inherit;cursor:pointer');
        el.style.display = 'none';
        el.parentNode.insertBefore(btn, el);
        btn.addEventListener('click', function () {
          btn.disabled = true; btn.textContent = 'Decrypting…';
          try { el.load(); } catch (e) {}
          mediaUrl(el.getAttribute('data-xa')).then(function (u) {
            el.src = u; el.style.display = ''; btn.remove();
            var pr = el.play(); if (pr && pr.catch) pr.catch(function () {});
          }, function () { btn.disabled = false; btn.textContent = '▶ Load & play (retry)'; });
        });
      });
      document.querySelectorAll('a[data-xa]').forEach(function (a) {
        a.addEventListener('click', function (ev) {
          ev.preventDefault();
          var w = window.open('', '_blank');
          mediaUrl(a.getAttribute('data-xa')).then(function (u) { if (w) w.location = u; else location.href = u; });
        });
      });
      return Promise.all(pending).then(function () {
        window.__xdTiming = { pageMs: Math.round(pageMs), totalMs: Math.round(performance.now() - t0), assets: pending.length };
        document.documentElement.setAttribute('data-xd-done', '1');
      });
    });
  }

  // ---------- Keep/Delete buttons ----------
  var connectText = 'Paste a GitHub fine-grained token that can reach only ' + INBOX_REPO + ', with Contents: Read and write. Stored on this device only, encrypted; never sent anywhere except api.github.com.';
  function sessionKey() { return subtle.importKey('raw', ckRaw, 'AES-GCM', false, ['encrypt', 'decrypt']); }
  function cacheToken(token) {
    // Pages opened later this session have the content key but maybe not the passcode key: keep a copy under the content key.
    if (!ckRaw) return Promise.resolve();
    var iv = crypto.getRandomValues(new Uint8Array(12));
    return sessionKey().then(function (k) { return subtle.encrypt({ name: 'AES-GCM', iv: iv, additionalData: enc.encode('xd-token') }, k, enc.encode(token)); })
      .then(function (ct) { try { sessionStorage.setItem('xd-tk-' + manifest.id, b64u(iv) + '.' + b64u(ct)); } catch (e) {} }, function () {});
  }
  function loadPriv() {
    if (priv) return Promise.resolve(priv);
    return idb(function (s) { return s.get('device'); }).then(function (rec) {
      return rec && rec.exp >= Date.now() && rec.pub === manifest.lock.pub ? (priv = rec.key) : null;
    }, function () { return null; });
  }
  function storedToken() { return idb(function (s) { return s.get('gh'); }).then(function (r) { return r && r.pub === manifest.lock.pub ? r : null; }, function () { return null; }); }
  function getToken() {
    var c = null;
    try { c = sessionStorage.getItem('xd-tk-' + manifest.id); } catch (e) {}
    var fromSession = c && ckRaw ? sessionKey().then(function (k) {
      var parts = c.split('.');
      return subtle.decrypt({ name: 'AES-GCM', iv: unb64u(parts[0]), additionalData: enc.encode('xd-token') }, k, unb64u(parts[1]));
    }).then(function (b) { return new TextDecoder().decode(b); }, function () { return null; }) : Promise.resolve(null);
    return fromSession.then(function (t) {
      if (t) return t;
      return storedToken().then(function (rec) {
        // No token connected on this device: use the one sealed into this list's payload, if any.
        if (!rec) return builtInToken ? builtInToken() : null;
        return loadPriv().then(function (p) {
          if (!p) return null;
          return openToken(rec, p).then(function (t) { return cacheToken(t).then(function () { return t; }); }, function () { return null; });
        });
      });
    });
  }
  function disconnect() {
    try { sessionStorage.removeItem('xd-tk-' + manifest.id); } catch (e) {}
    return idb(function (s) { return s.delete('gh'); }).catch(function () {}).then(function () { location.reload(); });
  }
  function askToken() {
    return new Promise(function (resolve) {
      var bx = document.createElement('div');
      bx.setAttribute('style', 'position:fixed;inset:0;z-index:99;background:rgba(0,0,0,.6);display:flex;align-items:center;justify-content:center;font:15px/1.45 -apple-system,sans-serif');
      bx.innerHTML = '<div style="width:min(92vw,420px);background:#171a1f;color:#e7e9ea;border:1px solid #3a3e44;border-radius:14px;padding:20px"><b style="font-size:18px">Connect buttons</b><p id="xd-ct" style="color:#8b919a;font-size:14px"></p><input id="xd-tok" type="password" autocomplete="off" placeholder="github_pat_…" style="width:100%;box-sizing:border-box;padding:11px;border-radius:10px;border:1px solid #3a3e44;background:#0f1115;color:inherit;font:16px -apple-system,sans-serif"><div id="xd-cerr" style="color:#e5735f;font-size:14px;min-height:20px;margin:8px 0"></div><div style="display:flex;gap:8px;justify-content:flex-end"><button type="button" id="xd-cno" style="font:inherit;padding:9px 14px;border-radius:10px;border:1px solid #3a3e44;background:none;color:inherit">Cancel</button><button type="button" id="xd-cok" style="font:600 15px -apple-system,sans-serif;padding:9px 14px;border-radius:10px;border:0;background:#e7e9ea;color:#0f1115">Connect</button></div></div>';
      document.body.appendChild(bx);
      var $ = function (id) { return document.getElementById(id); };
      $('xd-ct').textContent = connectText; $('xd-tok').focus();
      $('xd-cno').onclick = function () { bx.remove(); resolve(null); };
      $('xd-cok').onclick = function () {
        var t = $('xd-tok').value.trim();
        if (!t) return;
        $('xd-cok').disabled = true; $('xd-cerr').textContent = 'Checking…';
        gh(GH_API, t, 'GET', '').then(function (r) {
          if (!r.ok) throw new Error(r.status === 404 ? 'this token cannot see ' + INBOX_REPO : 'GitHub said HTTP ' + r.status);
          return r.json();
        }).then(function (repo) {
          if (repo.permissions && !repo.permissions.push) throw new Error('this token cannot write to ' + INBOX_REPO);
          return sealToken(t, unb64u(manifest.lock.pub));
        }).then(function (rec) {
          rec.pub = manifest.lock.pub;
          return idb(function (s) { return s.put(rec, 'gh'); }).catch(function () {});
        }).then(function () { return cacheToken(t); }).then(function () { bx.remove(); resolve(t); }, function (e) {
          $('xd-cok').disabled = false; $('xd-cerr').textContent = 'Not connected: ' + (e && e.message || e);
        });
      };
    });
  }
  function initDecide() {
    var items = [];
    document.querySelectorAll('.decide').forEach(function (el) {
      var key = inboxKey(el.getAttribute('data-day'), el.getAttribute('data-n'));
      if (!key) return;
      var it = el.closest('.item'), m = it && it.querySelector('.dmsg');
      if (!m) { m = document.createElement('div'); m.className = 'dmsg'; (it || el.parentNode).insertBefore(m, (it ? it.querySelector('.ihd') : el).nextSibling); }
      items.push({ el: el, key: key, msg: m, day: el.getAttribute('data-day'), n: el.getAttribute('data-n') });
    });
    if (!items.length) return;
    var timer = null, known = {};
    function apply(it, s) {
      if (s) known[it.key] = s;
      s = known[it.key];
      it.el.querySelectorAll('button').forEach(function (b) { b.disabled = !!s; });
      it.msg.textContent = statusText(s);
      // Fold when decided (Jack, 2026-10-24: "Fold when read, either delete or keep"); a failed result unfolds.
      var sec = it.el.closest('.item');
      if (!sec || !s) return;
      var tag = sec.querySelector('.ihd .tag');
      if (s.state === 'queued' || s.state === 'done') {
        if (window.xdDone) window.xdDone(sec, 1000); else { sec.classList.add('folded'); sec.classList.remove('unfold'); }
        if (tag) { tag.className = 'tag done'; tag.textContent = s.state === 'done' ? statusText(s) : '⏳ Queued'; }
        if (s.state === 'done') it.msg.textContent = '';
      } else if (s.state === 'failed' || s.state === 'ignored') {
        if (window.xdUndone) window.xdUndone(sec); else sec.classList.remove('folded');
      }
    }
    function refresh() {
      timer = null;
      return getToken().then(function (t) {
        if (!t) return;
        document.getElementById('xd-disc-w').hidden = false;
        return readStates(GH_API, t, items.map(function (i) { return i.key; })).then(function (st) {
          items.forEach(function (it) { if (st[it.key] || !known[it.key]) apply(it, st[it.key]); });
          if (items.some(function (it) { return known[it.key] && known[it.key].state === 'queued'; })) timer = setTimeout(refresh, 10000);
        });
      }).catch(function () { if (!timer) timer = setTimeout(refresh, 10000); });
    }
    items.forEach(function (it) {
      it.el.querySelectorAll('button[data-verb]').forEach(function (b) {
        b.onclick = function () {
          var verb = b.getAttribute('data-verb');
          it.el.querySelectorAll('button').forEach(function (x) { x.disabled = true; });
          it.msg.textContent = 'Sending…';
          var sec = it.el.closest('.item'), unfold = function () { if (!sec) return; if (window.xdUndone) window.xdUndone(sec); else sec.classList.remove('folded'); };
          if (sec) { sec.classList.add('folded'); sec.classList.remove('unfold'); } // optimistic fold on the tap; moves into Done once queued
          getToken().then(function (t) { return t || askToken(); }).then(function (t) {
            if (!t) { unfold(); apply(it); return; }
            document.getElementById('xd-disc-w').hidden = false;
            return putDecision(GH_API, t, it.day, it.n, verb).then(function (s) {
              apply(it, s);
              if (timer) clearTimeout(timer);
              timer = setTimeout(refresh, 3000);
            });
          }).catch(function (e) {
            unfold();
            apply(it);
            it.msg.textContent = e && (e.status === 401 || e.status === 403) ? 'GitHub refused the token (HTTP ' + e.status + '). Disconnect buttons and connect again.' : 'Not sent: ' + (e && e.message || e) + '. Try again.';
          });
        };
      });
    });
    document.querySelectorAll('[data-archive]').forEach(function (btn) {
      btn.onclick = function () {
        var pile = btn.closest('.pile');
        var todo = items.filter(function (it) { return it.day === 'inbox' && pile && pile.contains(it.el) && !known[it.key] && it.el.querySelector('button[data-verb="delete"]:not(.chg)'); });
        if (!todo.length) { btn.textContent = 'Nothing left'; return; }
        if (!confirm('Archive all ' + todo.length + ' news stories? Each one is filed to Archived.')) return;
        btn.disabled = true; btn.textContent = 'Archiving…';
        getToken().then(function (t) { return t || askToken(); }).then(function (t) {
          if (!t) { btn.disabled = false; btn.textContent = 'Archive all'; return; }
          document.getElementById('xd-disc-w').hidden = false;
          var byN = {}; todo.forEach(function (it) { byN[it.n] = it; it.msg.textContent = 'Sending…'; });
          return archiveAll(GH_API, t, todo.map(function (it) { return it.n; }), function (n, st) { apply(byN[n], st); }).then(function () {
            btn.textContent = 'Archive all'; btn.disabled = false;
            if (timer) clearTimeout(timer);
            timer = setTimeout(refresh, 3000);
          });
        }).catch(function (e) {
          btn.disabled = false; btn.textContent = 'Archive all';
          todo.forEach(function (it) { if (!known[it.key]) it.msg.textContent = 'Not sent: ' + (e && e.message || e) + '. Try again.'; });
        });
      };
    });
    document.getElementById('xd-disc').onclick = disconnect;
    storedToken().then(function (r) { if (r) document.getElementById('xd-disc-w').hidden = false; });
    refresh();
  }

  function tryRemembered() {
    var raw = null;
    try { raw = sessionStorage.getItem('xd-ck-' + manifest.id); } catch (e) {}
    if (raw) return useRaw(unb64u(raw));
    return idb(function (s) { return s.get('device'); }).then(function (rec) {
      if (!rec || rec.exp < Date.now() || rec.pub !== manifest.lock.pub) return null;
      priv = rec.key;
      return openSeal(rec.key).then(function (r) { return useRaw(new Uint8Array(r)); }, function () { return null; });
    }, function () { return null; });
  }

  function unlock(ev) {
    ev.preventDefault();
    var pass = document.getElementById('pw').value, remember = document.getElementById('rm').checked, lock = manifest.lock, btn = document.getElementById('go');
    if (!pass) return;
    btn.disabled = true; show('err'); show('st', 'Checking passcode…');
    deriveScalar(pass, unb64u(lock.salt), lock.iter).then(function (d) {
      var pub = pubFromScalar(d);
      if (!eq(pub, unb64u(lock.pub))) { var e = new Error('wrong'); e.wrong = true; throw e; }
      return importPriv(d, pub);
    }).then(function (p) {
      priv = p;
      return openSeal(priv).then(function (raw) {
        if (!remember) return raw;
        return idb(function (s) { return s.put({ key: priv, pub: lock.pub, exp: Date.now() + REMEMBER_MS }, 'device'); }).then(function () { return raw; }, function () { return raw; });
      });
    }).then(function (raw) { return useRaw(new Uint8Array(raw)); }).then(render).catch(function (e) {
      btn.disabled = false; show('st');
      show('err', e && e.wrong ? 'Wrong passcode. Try again.' : 'Could not decrypt: ' + (e && e.message || e));
    });
  }

  document.getElementById('fg').onclick = forget;
  fetch(root + 'manifest.json', { cache: 'no-store' }).then(function (r) { return r.json(); }).then(function (m) {
    manifest = m;
    // IndexedDB can hang (private browsing, locked-down Safari, headless): never let it hide the prompt.
    var remembered = Promise.race([tryRemembered().catch(function () { return null; }), new Promise(function (res) { setTimeout(function () { res(null); }, 2000); })]);
    return remembered.then(function (key) {
      if (key) return render(key).catch(function (e) { show('err', String(e && e.message || e)); ui.hidden = false; });
      ui.hidden = false; document.getElementById('f').onsubmit = unlock; document.getElementById('pw').focus();
    });
  }).catch(function (e) { ui.hidden = false; show('err', 'Could not load: ' + (e && e.message || e)); });
})();
