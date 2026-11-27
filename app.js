'use strict';
/* JBD BMS PWA — Web Bluetooth, протокол JBD (Xiaoxiang) */
const VERSION = '1.10.1';
const SVC = 0xff00, RX = 0xff01, TX = 0xff02;
// Felicity Solar (FLA/FLB/LPBF): текстові команди, відповідь JSON
const FEL_SVC = '6e6f736a-4643-4d44-8fa9-0fafd005e455';
const FEL_RX = '49535458-8341-43f4-a9d4-ec0e34729bb3';
const FEL_TX = '49535258-184d-4bd9-bc61-20c647249616';
let driver = 'jbd';             // 'jbd' | 'fel' | 'ffe0' (визначення) | 'atorch' | 'jk' | 'generic'
// Atorch DL24 / DL24P / DL24M (електронне навантаження): FFE0/FFE1, пакети FF 55 01 <тип> …
const AT_SVC = 0xffe0, AT_CH = 0xffe1;
// Daly Smart BMS (серія H/K/M/S, протокол D2/Modbus): FFF0/FFF1(notify)/FFF2(write), кадри 0xD2
const DALY_SVC = 0xfff0, DALY_RX = 0xfff1, DALY_TX = 0xfff2;
let atBuf = [], atDev = 2, atLast = null, atRawHex = '';
// загальновідомі сервіси, щоб для невідомих пристроїв показати GATT-карту
const PROBE_SVCS = [0xff00, 0xffe0, 0xffe5, 0xfff0, 0xffd0, 0xffc0, 0xffb0, 0xffa0, 0xff10, 0xff12, 0xfe95, 0xfee0, 0xfee7, 0xfee9, 0xfd00, 0xae00, 0xae30, 0xa002,
  0x180a, 0x180f, 0x181c, 0x1910,
  '6e400001-b5a3-f393-e0a9-e50e24dcca9e',   // Nordic UART
  '0000ffe0-0000-1000-8000-00805f9b34fb', '49535343-fe7d-4ae5-8fa9-9fafd205e455', // Microchip ISSC
  '0000fe00-0000-1000-8000-00805f9b34fb', '00010203-0405-0607-0809-0a0b0c0d1910'];
let felBuf = '', felWaiter = null, felRaw = null, felInfo = null;
const $ = id => document.getElementById(id);
const hex = a => Array.from(a, b => b.toString(16).padStart(2, '0')).join(' ');
const fmt = (v, d) => (v == null || isNaN(v)) ? '—' : v.toFixed(d).replace('.', ',');
const sleep = ms => new Promise(r => setTimeout(r, ms));
$('ver').textContent = VERSION;

/* ---------- стан ---------- */
let dev = null, rxCh = null, txCh = null, buf = [], waiter = null;
let queue = Promise.resolve(), busy = 0, pollTimer = null, pollMs = 2000;
let basic = null, cellsMv = [];
const hist = [];               // {t, v, a}
let csvOn = false; const csvRows = [];
let params = null;             // {key: raw}
let edits = {};                // {key: raw}
let devStrings = {};
let openGroups = new Set(['bat']);
let filter = 'all';

/* ---------- лог ---------- */
const logLines = [];
function log(s, poll) {
  if (poll && !$('logPoll').checked) return;
  logLines.unshift(new Date().toLocaleTimeString('uk-UA') + ' ' + s);
  if (logLines.length > 300) logLines.length = 300;
  $('log').textContent = logLines.join('\n');
}
$('bLogClr').onclick = () => { logLines.length = 0; $('log').textContent = ''; };
function toast(s, ms = 2500) { const t = $('toast'); t.textContent = s; t.style.display = 'block'; clearTimeout(t._h); t._h = setTimeout(() => t.style.display = 'none', ms); }

/* ---------- протокол ---------- */
function chk(b) { let s = 0; for (const x of b) s += x; s = (0x10000 - s) & 0xffff; return [s >> 8, s & 0xff]; }
function frame(rw, reg, data) { const body = [reg, data.length, ...data]; return new Uint8Array([0xdd, rw, ...body, ...chk(body), 0x77]); }

function onNotify(e) {
  buf.push(...new Uint8Array(e.target.value.buffer));
  while (buf.length) {
    const s = buf.indexOf(0xdd);
    if (s < 0) { buf = []; return; }
    if (s > 0) buf = buf.slice(s);
    if (buf.length < 4) return;
    const len = buf[3], total = len + 7;
    if (buf.length < total) return;
    const p = buf.slice(0, total); buf = buf.slice(total);
    if (p[total - 1] !== 0x77) { log('пошкоджений пакет ' + hex(p)); continue; }
    if (waiter && waiter.reg === p[1]) { const w = waiter; waiter = null; clearTimeout(w.t); w.res({ status: p[2], data: p.slice(4, 4 + len) }); }
  }
}

function rawCmd(rw, reg, data = [], quiet = false, timeout = 3000) {
  if (!txCh) return Promise.reject(new Error('не підключено'));
  const f = frame(rw, reg, data);
  log('→ ' + hex(f), quiet);
  const p = new Promise((res, rej) => {
    waiter = { reg, res, t: setTimeout(() => { waiter = null; rej(new Error('тайм-аут 0x' + reg.toString(16))); }, timeout) };
  });
  return (async () => {
    for (let i = 0; i < f.length; i += 20) await txCh.writeValueWithoutResponse(f.slice(i, i + 20));
    const r = await p;
    log('← 0x' + reg.toString(16).padStart(2, '0') + (r.status ? ' ПОМИЛКА ' + r.status : ' ok') + ' ' + hex(r.data), quiet && !r.status);
    return r;
  })();
}
// послідовна черга: одна транзакція за раз
function exclusive(fn) {
  const run = queue.then(async () => { busy++; try { return await fn(); } finally { busy--; } });
  queue = run.catch(() => {});
  return run;
}
const rd = (reg, q) => rawCmd(0xa5, reg, [], q);
const wr = (reg, data) => rawCmd(0x5a, reg, data);
const u16 = (d, i) => (d[i] << 8) | d[i + 1];
const s16 = (d, i) => { const v = u16(d, i); return v & 0x8000 ? v - 0x10000 : v; };

async function enterFactory(pw) {
  if (pw) {
    const a = Array.from(new TextEncoder().encode(pw));
    const r = await wr(0x06, [a.length, ...a]);
    if (r.status) throw new Error('пароль відхилено');
  }
  const r = await wr(0x00, [0x56, 0x78]);
  if (r.status) throw new Error('BMS не дозволила вхід у режим налаштувань');
}
const exitNoSave = () => wr(0x01, [0x00, 0x00]).catch(() => {});
const exitSave = () => wr(0x01, [0x28, 0x28]);
let lastPw = '';

/* ---------- підключення ---------- */
let connState = 'off';          // off | conn | on
let cancelConn = false;
function extraUuids() {
  try { return (localStorage.getItem('jbd_extra_uuids') || '').split(/[\s,;]+/).map(x => x.trim().toLowerCase()).filter(Boolean)
    .map(x => /^[0-9a-f]{4}$/.test(x) ? parseInt(x, 16) : x).filter(x => typeof x === 'number' || /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/.test(x)); } catch (_) { return []; }
}
// підключення до вже дозволеного пристрою без сканування (якщо Chrome підтримує getDevices)
let zombiesCleared = false;
async function clearZombies() {
  // з минулої сесії міг лишитись відкритий GATT: тоді пристрій не рекламує себе і не з'являється у вікні пошуку
  try {
    if (!navigator.bluetooth?.getDevices) return;
    const list = await navigator.bluetooth.getDevices();
    for (const d of list) { try { if (d.gatt?.connected) { d.gatt.disconnect(); log('закрив залишкове з\'єднання: ' + (d.name || d.id)); } } catch (_) {} }
  } catch (_) {}
}
async function renderKnown() {
  const box = $('known'); if (!box) return;
  if (!zombiesCleared) { zombiesCleared = true; await clearZombies(); }
  let list = [];
  try { if (navigator.bluetooth?.getDevices) list = await navigator.bluetooth.getDevices(); } catch (_) {}
  knownDevs = list;
  if (connState !== 'off' || !list.length) { box.innerHTML = ''; return; }
  box.innerHTML = '<div class="dsub" style="width:100%;margin-bottom:2px">Швидке підключення (без пошуку):</div>' +
    list.map((d, i) => `<button class="pill" data-known="${i}" style="height:34px;margin:0 6px 6px 0;background:#1f6feb;border-color:#1f6feb">${(d.name || d.id).replace(/</g, '&lt;')}</button>`).join('');
}
let knownDevs = [];
async function connectKnown(d) {
  cancelConn = false;
  try { if (dev?.gatt?.connected) { manualDisc = true; dev.gatt.disconnect(); await sleep(300); } } catch (_) {}
  dev = d;
  if (dev.gatt?.connected) { try { dev.gatt.disconnect(); await sleep(400); } catch (_) {} }
  dev.removeEventListener?.('gattserverdisconnected', onDisc);
  dev.addEventListener('gattserverdisconnected', onDisc);
  setConn('conn');
  log('швидке підключення: ' + (d.name || d.id));
  try { await gattConnect(); }
  catch (e) {
    if (cancelConn) { setConn('off'); return; }
    setConn('off'); log('помилка: ' + e.message);
    toast('Не вдалося без сканування — пристрій поза зоною або вже підключений. Спробуйте «Підключити».', 5000);
  }
}
let scanTimes = [];
function showScanHint(t) { const el = $('scanHint'); if (!el) return; if (t) { el.textContent = t; el.style.display = ''; } else el.style.display = 'none'; }
async function connect() {
  if (!navigator.bluetooth) { toast('Web Bluetooth недоступний. Відкрийте в Chrome на Android.', 4000); return; }
  cancelConn = false;
  const now = Date.now(); scanTimes = scanTimes.filter(t => now - t < 30000); scanTimes.push(now);
  if (scanTimes.length >= 4) showScanHint('Android блокує частий пошук Bluetooth (понад 5 за 30 с). Якщо вікно порожнє — зачекайте ~30 с, або скористайтесь кнопкою швидкого підключення вгорі, або вимкніть і ввімкніть Bluetooth.');
  await clearZombies();
  // стара сесія могла лишити GATT-з'єднання: підключений пристрій не рекламує себе і не з'являється у списку
  try { if (dev?.gatt?.connected) { manualDisc = true; dev.gatt.disconnect(); await sleep(300); } } catch (_) {}
  try {
    let wide = false; try { wide = localStorage.getItem('jbd_wide_probe') === '1'; } catch (_) {}
    dev = await navigator.bluetooth.requestDevice({ acceptAllDevices: true, optionalServices: [...new Set([SVC, FEL_SVC, AT_SVC, DALY_SVC, ...(wide ? PROBE_SVCS : []), ...extraUuids()])] });
    dev.addEventListener('gattserverdisconnected', onDisc);
    setConn('conn');
    await gattConnect();
  } catch (e) {
    if (cancelConn) { log('підключення скасовано'); setConn('off'); return; }
    setConn('off'); log('помилка: ' + e.message);
    if (e.name === 'NotFoundError') showScanHint('Пошук нічого не знайшов. Варіанти: кнопка швидкого підключення вгорі (без пошуку); зачекати ~30 с через обмеження Android; або вимкнути/ввімкнути Bluetooth.');
    else toast(e.message);
    try { if (dev?.gatt?.connected) { manualDisc = true; dev.gatt.disconnect(); } } catch (_) {}
  }
}
// список доступних сервісів; якщо пристрій розриває з'єднання — одна повторна спроба
async function listServices(gatt) {
  for (let i = 0; i < 2; i++) {
    try {
      if (!dev.gatt.connected) gatt = await dev.gatt.connect();
      return { gatt, svcs: await gatt.getPrimaryServices() };
    } catch (e) {
      if (/No Services/i.test(e.message)) return { gatt, svcs: [] };
      log('читання сервісів: ' + e.message + (i ? '' : ' — повторюю'));
      if (cancelConn) throw new Error('скасовано');
      await sleep(800);
    }
  }
  return { gatt, svcs: [] };
}
const shortU = u => { const m = /^0000([0-9a-f]{4})-0000-1000-8000-00805f9b34fb$/.exec(u); return m ? m[1] : u; };
async function gattConnect() {
  let gatt = await dev.gatt.connect();
  if (cancelConn) throw new Error('скасовано');
  const r = await listServices(gatt); gatt = r.gatt;
  const svcs = r.svcs, has = u => svcs.find(s => shortU(s.uuid) === (typeof u === 'number' ? u.toString(16).padStart(4, '0') : u));
  const hasChar = async (srv, u) => { try { return srv ? await srv.getCharacteristic(u) : null; } catch (_) { return null; } };
  let srv = null;
  if ((srv = has(SVC))) driver = 'jbd';
  else if ((srv = has(FEL_SVC))) driver = 'fel';
  else if ((srv = has(AT_SVC)) && (await hasChar(srv, AT_CH))) driver = 'ffe0';
  else if ((srv = has(DALY_SVC)) && (await hasChar(srv, DALY_RX))) driver = 'daly-probe';
  else { driver = 'generic'; return genConnect(svcs); }
  showScanHint('');
  log('тип пристрою: ' + ({ jbd: 'JBD BMS', fel: 'Felicity Solar', 'ffe0': 'сервіс FFE0 (UART-модуль) — визначаю: JK BMS чи Atorch…', 'daly-probe': 'сервіс FFF0 — перевіряю Daly…' })[driver]);
  if (driver === 'fel') return felConnect(srv);
  if (driver === 'ffe0') return atConnect(srv, svcs);
  if (driver === 'daly-probe') return dalyConnect(srv, svcs);
  rxCh = await srv.getCharacteristic(RX);
  txCh = await srv.getCharacteristic(TX);
  rxCh.addEventListener('characteristicvaluechanged', onNotify);
  await rxCh.startNotifications();
  buf = [];
  $('dName').textContent = dev.name || 'JBD BMS';
  setConn('on');
  applyDriverUi();
  if (!params) $('pBody').innerHTML = '<div class="empty">Натисніть «Прочитати з BMS»</div>';
  log('підключено: ' + (dev.name || dev.id));
  await exclusive(async () => {
    try { const r = await rd(0x05); if (!r.status) devStrings.hw = new TextDecoder().decode(new Uint8Array(r.data)).replace(/\0/g, ''); } catch (_) {}
  });
  renderDevInfo();
  startPoll();
}

/* ---------- Felicity ---------- */
async function felConnect(srv) {
  rxCh = await srv.getCharacteristic(FEL_RX);
  const tx = await srv.getCharacteristic(FEL_TX);
  rxCh.addEventListener('characteristicvaluechanged', felNotify);
  // перше підключення: Android покаже запит на створення пари — PIN 123456
  for (let i = 0; ; i++) {
    try { await rxCh.startNotifications(); break; }
    catch (e) {
      if (i >= 4) throw new Error('Не вдалося створити пару з батареєю (' + e.message + '). Створіть пару в налаштуваннях Bluetooth, PIN 123456');
      log('створення пари: ' + e.message + ' — очікую PIN…');
      toast('Підтвердіть створення пари, PIN 123456', 6000);
      await sleep(6000);
    }
  }
  txCh = tx; felBuf = '';
  $('dName').textContent = dev.name || 'Felicity';
  setConn('on');
  log('підключено: ' + (dev.name || dev.id));
  applyDriverUi();
  try { felInfo = await exclusive(() => felCmd('get dev basice infor')); } catch (e) { log('basic infor: ' + e.message); }
  setConn('on');
  renderDevInfo();
  startPoll();
}
function felNotify(e) {
  const part = new TextDecoder().decode(new Uint8Array(e.target.value.buffer));
  if (part.startsWith('{')) felBuf = '';
  felBuf += part;
  if (felBuf.length > 20000) felBuf = '';
  if (!felBuf.trimEnd().endsWith('}')) return;
  let j; try { j = JSON.parse(felBuf); } catch (_) { return; }   // ще не весь JSON
  felBuf = '';
  log('← ' + JSON.stringify(j).slice(0, 400), !$('logPoll').checked);
  if (felWaiter) { const w = felWaiter; felWaiter = null; clearTimeout(w.t); w.res(j); }
}
async function felWrite(bytes) {
  try { await txCh.writeValueWithResponse(bytes); }
  catch (e) {
    try { await txCh.writeValueWithoutResponse(bytes); }
    catch (_) { for (let i = 0; i < bytes.length; i += 20) await txCh.writeValueWithoutResponse(bytes.slice(i, i + 20)); }
  }
}
async function felCmd(cmd, timeout = 4000) {
  if (!txCh) throw new Error('не підключено');
  const full = 'wifilocalMonitor:' + cmd;
  for (let attempt = 0; attempt < 3; attempt++) {
    log('→ ' + full, cmd === 'get dev real infor');
    felBuf = '';
    const p = new Promise((res, rej) => { felWaiter = { res, t: setTimeout(() => { felWaiter = null; rej(new Error('тайм-аут')); }, timeout) }; });
    await felWrite(new TextEncoder().encode(full));
    try { return await p; } catch (e) { if (attempt === 2) throw new Error(cmd + ': немає відповіді'); }
  }
}
const felNum = v => { const n = Number(v); return isFinite(n) ? n : null; };
const felRow = (j, k, r = 0) => (Array.isArray(j?.[k]) && Array.isArray(j[k][r])) ? j[k][r].map(felNum) : [];
function felParse(j) {
  const batt = [felRow(j, 'BattList', 0), felRow(j, 'BattList', 1)];
  const soc = felRow(j, 'BatsocList', 0);
  const cells = felRow(j, 'BatcelList', 0).filter(x => x != null && x > 0 && x < 6000);
  const temps = felRow(j, 'BtemList', 0).filter(x => x != null && x !== 0x7fff && Math.abs(x) < 2000).map(x => x / 10);
  const capMah = soc[2] ?? null;
  const o = {
    fel: true,
    v: (batt[0][0] ?? 0) / 1000,
    a: (batt[1][0] ?? 0) / 10,
    soc: Math.round((soc[0] ?? 0) / 100),
    nominal: capMah != null ? capMah / 1000 : null,
    remain: capMah != null && soc[0] != null ? soc[0] * capMah / 1e7 : null,
    cycles: felNum(j.BatCycle ?? j.CycleCnt ?? j.Cycle) ?? '—',
    cells: cells.length, temps, bal: 0, prot: 0, fet: null,
    warn: felNum(j.Bwarn) || 0, fault: felNum(j.Bfault) || 0,
    soh: soc[1] != null ? soc[1] / 10 : null,
    boardTemps: felRow(j, 'BTemp', 1).filter(x => x != null && x !== 0x7fff && x !== 65535 && Math.abs(x) < 2000).map(x => x / 10),
    limits: (() => { const v = felRow(j, 'LVolCur', 0), c = felRow(j, 'LVolCur', 1); return v.length ? { cvl: v[0] / 10, dvl: v[1] / 10, ccl: c[0], dcl: c[1] } : null; })(),
    state: felNum(j.Bstate), estate: felNum(j.Estate), bmsDate: j.date || null,
    type: j.Type, subType: j.SubType, sn: j.DevSN,
  };
  return { o, cells };
}
async function felPoll() {
  const j = await exclusive(() => felCmd('get dev real infor'));
  if (j.CommVer != null && j.CommVer !== 1) log('увага: CommVer=' + j.CommVer + ' (очікувалось 1)');
  felRaw = j;
  const { o, cells } = felParse(j);
  basic = o; cellsMv = cells;
  if (document.querySelector('#v-srv.act')) renderDevInfo();
}
function applyDriverUi() {
  try { applyDriverUi0(); } catch (e) { log('інтерфейс застарів (' + e.message + ') — перезавантажую'); hardReload(); }
}
function applyDriverUi0() {
  const probe = driver === 'ffe0';
  const gen = driver === 'generic' || probe;
  const at = driver === 'atorch' || gen;
  const jk = driver === 'jk';
  const fel = driver === 'fel' || at || jk || driver === 'daly';     // «не JBD»: ховаємо EEPROM-функції
  $('genCard').style.display = driver === 'generic' ? '' : 'none';
  $('genMon').style.display = gen ? '' : 'none';
  $('genMonT').textContent = probe ? 'Визначаю тип пристрою…' : 'Невідомий пристрій';
  $('genMonP').textContent = probe ? 'Пристрій має сервіс FFE0: чекаю відповіді JK BMS або Atorch (до 6 с).' : 'Підключено в універсальному режимі. Карта BLE-сервісів, усі вхідні дані і відправка команд — у вкладці «Сервіс».';
  $('mosBox').style.display = driver === 'jbd' ? '' : 'none';
  jkPwInit();
  $('cTitle').closest('.card').style.display = at ? 'none' : '';
  $('prot').closest('.card').style.display = at ? 'none' : '';
  $('atCard').style.display = driver === 'atorch' ? '' : 'none';
  $('temps').closest('.wrap').querySelectorAll('.card').forEach(c => { if (c.querySelector('#chV')) c.style.display = gen ? 'none' : ''; });
  $('felRawTitle').textContent = at ? 'Сирий пакет Atorch (hex)' : 'Сирі дані BMS (JSON)';
  ['bBackup', 'bRestore', 'bCalZero', 'bCalCell', 'bCnt'].forEach(id => $(id).disabled = fel);
  [$('bBackup').closest('.card'), $('bCalZero').closest('.card')].forEach(c => c.style.display = fel ? 'none' : '');
  $('bCnt').closest('.bitrow').style.display = fel ? 'none' : '';
  $('pFilt').style.display = fel ? 'none' : '';
  $('felRawCard').style.display = fel && !gen ? '' : 'none';
  $('felRawTitle').textContent = jk ? 'Сирий кадр JK (hex)' : driver === 'daly' ? 'Сирий кадр Daly (hex)' : $('felRawTitle').textContent;
  if (driver !== 'fel') $('limCard').style.display = 'none';
  if (!at) $('temps').style.display = '';
  if (fel) {
    if (jk) {
      $('pInfo').textContent = 'JK BMS';
      $('bReadP').disabled = false;
      renderJkParams();
    } else if (at) {
      $('pInfo').textContent = gen ? 'Невідомий пристрій: параметрів немає' : 'Atorch DL24: параметрів EEPROM немає';
      $('pBody').innerHTML = '<div class="card"><div class="ct">Atorch DL24</div><p class="lbl" style="font-size:14px">Керування навантаженням — кнопками на вкладці «Моніторинг» (як кнопки на самому приладі). Сирий пакет — у «Сервісі».</p></div>';
      $('bReadP').disabled = true;
    } else if (driver === 'daly') {
      $('pInfo').textContent = 'Daly BMS';
      $('pBody').innerHTML = '<div class="card"><div class="ct">Daly Smart BMS</div><p class="lbl" style="font-size:14px">Моніторинг працює. Зміна параметрів Daly — наступним кроком, після звірки даних з офіційним застосунком. Сирий кадр — у «Сервісі».</p></div>';
      $('bReadP').disabled = true;
    } else {
    $('pInfo').textContent = 'Felicity: зміна параметрів ще не підтримується';
    $('pBody').innerHTML = '<div class="card"><div class="ct">Felicity Solar</div><p class="lbl" style="font-size:14px">Протокол налаштувань Felicity не опублікований. Щоб додати запис параметрів, потрібен Bluetooth-лог (HCI snoop) з телефона, поки офіційний застосунок Fsolar змінює параметр.</p><p class="lbl" style="font-size:14px">Моніторинг працює повністю. Сирі дані BMS — у вкладці «Сервіс».</p></div>';
    $('bReadP').disabled = true;
    }
  } else $('bReadP').disabled = false;
}
function renderFelRaw() {
  $('felRaw').textContent = felRaw ? JSON.stringify(felRaw, null, 1) : '—';
}

/* ---------- універсальний режим (невідомий пристрій) ---------- */
let genChars = [], genMap = [];
const PROPS = ['read', 'write', 'writeWithoutResponse', 'notify', 'indicate'];
const asciiOf = a => Array.from(a, b => b >= 32 && b < 127 ? String.fromCharCode(b) : '.').join('');
async function genConnect(svcs) {
  genChars = []; genMap = ['GATT-карта ' + (dev.name || dev.id) + ':'];
  if (!svcs.length) genMap.push('  жодного з відомих застосунку сервісів не знайдено — додайте UUID у «Сервіс → Універсальний режим»');
  for (const sv of svcs) {
    genMap.push('  сервіс ' + sv.uuid);
    let chars = [];
    try { chars = await sv.getCharacteristics(); } catch (e) { genMap.push('    (характеристики недоступні: ' + e.message + ')'); }
    for (const c of chars) {
      const pr = PROPS.filter(k => c.properties[k]);
      genMap.push('    хар. ' + c.uuid + ' [' + pr.join(',') + ']');
      genChars.push({ svc: sv.uuid, ch: c, props: pr });
    }
  }
  genMap.forEach(l => log(l));
  $('dName').textContent = dev.name || 'Невідомий пристрій';
  setConn('on');
  applyDriverUi();
  renderGen();
  // підписка на всі notify/indicate — усе, що прийде, видно в журналі
  for (const g of genChars) if (g.props.includes('notify') || g.props.includes('indicate')) {
    try {
      g.ch.addEventListener('characteristicvaluechanged', e => { const d = new Uint8Array(e.target.value.buffer); log('← [' + shortU(g.ch.uuid) + '] ' + hex(d) + '  |' + asciiOf(d) + '|'); });
      await g.ch.startNotifications();
      log('підписано на ' + shortU(g.ch.uuid));
    } catch (e) { log('підписка ' + shortU(g.ch.uuid) + ': ' + e.message); }
  }
  // характеристики з read — прочитати один раз
  for (const g of genChars) if (g.props.includes('read')) {
    try { const v = new Uint8Array((await g.ch.readValue()).buffer); log('читання [' + shortU(g.ch.uuid) + '] ' + hex(v) + '  |' + asciiOf(v) + '|'); } catch (_) {}
  }
  txCh = genChars.find(g => g.props.includes('write') || g.props.includes('writeWithoutResponse'))?.ch || { generic: true };
}
function renderGen() {
  const w = genChars.filter(g => g.props.includes('write') || g.props.includes('writeWithoutResponse'));
  $('genCh').innerHTML = w.length ? w.map((g, i) => `<option value="${genChars.indexOf(g)}">${shortU(g.ch.uuid)} (${g.props.filter(p => p.startsWith('write')).join('/')})</option>`).join('') : '<option value="">немає характеристик на запис</option>';
  $('genSend').disabled = !w.length;
  $('genMapBox').textContent = genMap.join('\n');
}
async function genSend() {
  const g = genChars[+$('genCh').value]; if (!g) return;
  const raw = $('genData').value.trim(); if (!raw) return;
  let bytes;
  if ($('genMode').value === 'hex') {
    const h = raw.replace(/0x/gi, '').replace(/[^0-9a-f]/gi, '');
    if (!h.length || h.length % 2) return toast('Hex: парна кількість символів 0-9 a-f');
    bytes = new Uint8Array(h.match(/../g).map(x => parseInt(x, 16)));
  } else bytes = new TextEncoder().encode(raw.replace(/\\r/g, '\r').replace(/\\n/g, '\n'));
  log('→ [' + shortU(g.ch.uuid) + '] ' + hex(bytes) + '  |' + asciiOf(bytes) + '|');
  try {
    if (g.props.includes('write')) await g.ch.writeValueWithResponse(bytes); else await g.ch.writeValueWithoutResponse(bytes);
  } catch (e) { toast(e.message); log('запис: ' + e.message); }
}

/* ---------- Atorch DL24 ---------- */
let svcsAll = null;
async function atConnect(srv, svcs) {
  svcsAll = svcs;
  const ch = await srv.getCharacteristic(AT_CH);
  rxCh = ch; txCh = ch; atBuf = [];
  ch.addEventListener('characteristicvaluechanged', atNotify);
  ch.addEventListener('characteristicvaluechanged', jkNotify);
  jkBuf = []; jkLast = 0; jkInfo = null; jkInfoRaw = null; jkSeen = false; jkInfoLogged = false; jkSet = null; jkSettings = null; jkEdits = {}; jkSane = false;
  await ch.startNotifications();
  $('dName').textContent = dev.name || 'FFE0';
  // JK BMS відповідає лише на запит: просимо інформацію про пристрій (0x97), потім дані банок (0x96)
  setTimeout(() => jkSend(0x97).catch(() => {}), 300);
  setTimeout(() => jkSend(0x96).catch(() => {}), 1200);
  setConn('on');
  log('підключено: ' + (dev.name || dev.id));
  applyDriverUi();
  renderDevInfo();
  startPoll();   // для Atorch опитування лише перемальовує — дані приходять самі раз на секунду
  setTimeout(async () => {
    if (driver === 'ffe0' && dev?.gatt?.connected) {
      log('FFE0 є, але ні Atorch, ні JK не відповіли — переходжу в універсальний режим');
      stopPoll(); driver = 'generic';
      try { await rxCh.stopNotifications(); } catch (_) {}
      rxCh.removeEventListener?.('characteristicvaluechanged', atNotify);
      rxCh.removeEventListener?.('characteristicvaluechanged', jkNotify);
      await genConnect(svcsAll || []);
    }
    renderDevInfo();
  }, 6000);
}
const u24 = (d, i) => (d[i] << 16) | (d[i + 1] << 8) | d[i + 2];
const u32 = (d, i) => ((d[i] << 24) >>> 0) + (d[i + 1] << 16) + (d[i + 2] << 8) + d[i + 3];
function atNotify(e) {
  atBuf.push(...new Uint8Array(e.target.value.buffer));
  for (;;) {
    let s = -1;
    for (let i = 0; i + 1 < atBuf.length; i++) if (atBuf[i] === 0xff && atBuf[i + 1] === 0x55) { s = i; break; }
    if (s < 0) { if (atBuf.length > 200) atBuf = []; return; }
    if (s > 0) atBuf = atBuf.slice(s);
    if (atBuf.length < 4) return;
    const t = atBuf[2];
    const len = t === 0x01 ? 36 : t === 0x02 ? 8 : t === 0x03 ? 10 : 36;   // 01 звіт, 02 відповідь на команду
    if (atBuf.length < len) return;
    const p = atBuf.slice(0, len); atBuf = atBuf.slice(len);
    if (t === 0x01) atParse(p); else log('← Atorch ' + hex(p));
  }
}
function atParse(p) {
  if (driver !== 'ffe0' && driver !== 'atorch') return;
  if (driver === 'ffe0') {
    driver = 'atorch';
    log('отримано пакет Atorch — це електронне навантаження Atorch');
    $('dName').textContent = dev.name || 'Atorch DL24';
    applyDriverUi(); renderDevInfo();
  }
  atDev = p[3];
  atRawHex = hex(p);
  if (atDev !== 0x02) { log('Atorch: тип пристрою 0x' + atDev.toString(16) + ' (очікувався 0x02 DC) — розбір може бути неточним'); }
  const o = {
    v: u24(p, 4) / 10,
    a: u24(p, 7) / 1000,
    ah: u24(p, 10) / 100,
    wh: u32(p, 13) * 10,
    temp: (p[24] << 8) | p[25],
    h: (p[26] << 8) | p[27], m: p[28], s: p[29],
  };
  o.w = o.v * o.a;
  atLast = o;
  basic = { at: true, v: o.v, a: -o.a, soc: null, remain: null, nominal: null, cycles: '—', cells: 0, temps: [o.temp], bal: 0, prot: 0, fet: null };
  cellsMv = [];
}
async function atCmd(code) {
  if (!txCh) return toast('Не підключено');
  const f = [0xff, 0x55, 0x11, atDev || 0x02, code, 0, 0, 0, 0];
  const sum = f.slice(2).reduce((a, b) => a + b, 0);
  f.push((sum & 0xff) ^ 0x44);
  log('→ Atorch ' + hex(f));
  try { await txCh.writeValueWithResponse(new Uint8Array(f)); }
  catch (_) { await txCh.writeValueWithoutResponse(new Uint8Array(f)); }
}
const AT_CMDS = { resetWh: 0x01, resetAh: 0x02, resetTime: 0x03, resetAll: 0x05, plus: 0x11, minus: 0x12, setup: 0x31, enter: 0x32 };
function renderAtorch() {
  const o = atLast; if (!o) return;
  $('mV').textContent = fmt(o.v, 1);
  $('mA').textContent = fmt(o.a, 3) + ' A';
  $('mW').textContent = fmt(o.w, 1) + ' W';
  $('mSoc').textContent = fmt(o.ah, 2);
  $('mSoc').nextElementSibling.style.display = 'none';
  $('mCap').textContent = 'Ah · ' + fmt(o.wh, 0) + ' Wh';
  $('gauge').style.background = 'conic-gradient(#0B6BCB 0 100%)';
  $('mState').textContent = (o.a > 0.001 ? 'Навантаження увімкнене' : 'Струм 0') + ' · ' + o.h + ':' + String(o.m).padStart(2, '0') + ':' + String(o.s).padStart(2, '0');
  $('mAlert').className = 'alert';
  $('atBody').innerHTML =
    `<div class="kv"><span>Ємність</span><b class="mono">${fmt(o.ah, 2)} Ah</b></div>` +
    `<div class="kv"><span>Енергія</span><b class="mono">${fmt(o.wh, 0)} Wh</b></div>` +
    `<div class="kv"><span>Час роботи</span><b class="mono">${o.h}:${String(o.m).padStart(2, '0')}:${String(o.s).padStart(2, '0')}</b></div>` +
    `<div class="kv"><span>Температура</span><b class="mono">${o.temp} °C</b></div>`;
  $('temps').innerHTML = '';
  drawChart($('chV'), hist.map(h => h.v), '#0B6BCB', $('hRange'), 'V', 2);
  drawChart($('chA'), hist.map(h => -h.a), '#B45309', $('hRangeA'), 'A', 3, true);
  if (document.querySelector('#v-srv.act')) $('felRaw').textContent = atRawHex;
}


/* ---------- JK BMS (JK02, BLE FFE0/FFE1) ---------- */
let jkInfoLogged = false, jkInfoRaw = null;
let jkBuf = [], jkLast = 0, jkInfo = null, jkSeen = false, jkSw = 0, jkOffs = 0, jkRaw = null, jkSettings = null;
const JK_HDR = [0x55, 0xaa, 0xeb, 0x90], JK_LEN = 300;
const le = (d, i, n, signed) => { let v = 0; for (let k = n - 1; k >= 0; k--) v = v * 256 + d[i + k]; if (signed && v >= 2 ** (8 * n - 1)) v -= 2 ** (8 * n); return v; };
async function jkSend(cmd, value = []) {
  if (!txCh || txCh.generic) return;
  const f = [0xaa, 0x55, 0x90, 0xeb, cmd, value.length, ...value];
  while (f.length < 19) f.push(0);
  f.push(f.reduce((a, b) => a + b, 0) & 0xff);
  log('→ JK ' + hex(f), cmd === 0x96 && jkSeen);
  try { await txCh.writeValueWithoutResponse(new Uint8Array(f)); } catch (_) { await txCh.writeValueWithResponse(new Uint8Array(f)); }
}
function jkNotify(e) {
  let d = Array.from(new Uint8Array(e.target.value.buffer));
  if (d.length >= 4 && d[0] === 0x41 && d[1] === 0x54 && d[2] === 0x0d && d[3] === 0x0a) d = d.slice(4);   // «AT\r\n» від BLE-модуля
  if (!d.length) return;
  const startsHdr = JK_HDR.every((b, i) => d[i] === b);
  if (startsHdr) jkBuf = [];
  else if (!jkBuf.length) return;
  jkBuf.push(...d);
  if (jkBuf.length < JK_LEN) return;
  const f = jkBuf.slice(0, JK_LEN); jkBuf = [];
  const sum = f.slice(0, JK_LEN - 1).reduce((a, b) => a + b, 0) & 0xff;
  if (sum !== f[JK_LEN - 1]) { log('JK: контрольна сума не збігається, кадр пропущено'); return; }
  jkFrame(f);
}
const jkStr = (f, a, b) => new TextDecoder().decode(new Uint8Array(f.slice(a, b))).replace(/\0.*$/s, '').trim();
// лише друковані ASCII-символи від початку діапазону (для паролів/текстових полів)
function jkText(f, a, b) { let o = ''; for (let i = a; i < b && i < f.length; i++) { const c = f[i]; if (c < 0x20 || c > 0x7e) break; o += String.fromCharCode(c); } return o; }
function jkFrame(f) {
  const type = f[4];
  if (driver !== 'ffe0' && driver !== 'jk') return;
  if (!jkSeen) {
    jkSeen = true; driver = 'jk';
    log('отримано кадр JK — це JK BMS');
    $('dName').textContent = dev.name || 'JK BMS';
    applyDriverUi();
  }
  if (type === 0x03) {
    jkInfoRaw = f.slice();
    jkInfo = { model: jkStr(f, 6, 22), hw: jkStr(f, 22, 30), sw: jkStr(f, 30, 38), name: jkStr(f, 46, 62), sn: jkStr(f, 86, 94),
      connPw: jkText(f, 62, 78), userData: jkText(f, 102, 118), setPw: jkText(f, 118, 134) };
    jkSw = parseInt(jkInfo.sw) || 0;
    jkOffs = jkSw && jkSw < 11 ? -32 : 0;
    if (!jkInfoLogged) log('JK: ' + jkInfo.model + ', hw ' + jkInfo.hw + ', sw ' + jkInfo.sw + (jkOffs ? ' (протокол JK02_24S)' : ' (протокол JK02_32S)'));
    jkInfoLogged = true;
    renderDevInfo(); setConn('on'); jkPwInit();
    return;
  }
  if (type === 0x01) {
    jkSettings = f; jkSetAt = Date.now();
    jkParse(f);
    if (document.querySelector('#v-par.act')) renderJkParams();
    if (jkSetWaiter) { const w = jkSetWaiter; jkSetWaiter = null; w(); }
    return;
  }
  if (type !== 0x02) return;
  jkLast = Date.now(); jkRaw = f;
  const o = jkOffs, h = o >> 1;
  const mask = le(f, 70 + h, 4);
  const n = mask.toString(2).split('').filter(x => x === '1').length || 0;
  const cells = []; for (let i = 0; i < n; i++) cells.push(le(f, 6 + i * 2, 2));
  const tpos = jkSw >= 14 ? [144, 162, 164, 254, 256, 258] : jkSw >= 11 || !jkSw ? [144, 162, 164, 254] : [130, 132, 134];
  const tmask = f[214 + o];
  const temps = [], tnames = [];
  tpos.forEach((p, i) => { if (tmask & (1 << i)) { const t = le(f, p, 2, true); if (t !== -2000) { temps.push(t / 10); tnames.push(i === 0 ? 'MOS' : i === 3 ? 'MOS 2' : 'T' + (i === 1 ? 1 : i === 2 ? 2 : i - 1)); } } });
  const prob = le(f, 166 + o, 4);
  basic = {
    jk: true,
    v: le(f, 150 + o, 4) / 1000, a: le(f, 158 + o, 4, true) / 1000,
    soc: f[173 + o], remain: le(f, 174 + o, 4) / 1000, nominal: le(f, 178 + o, 4) / 1000,
    cycles: le(f, 182 + o, 4), cycleAh: le(f, 186 + o, 4) / 1000, soh: f[190 + o],
    fet: (f[198 + o] ? 1 : 0) | (f[199 + o] ? 2 : 0),
    cells: n, temps, tnames, bal: 0, prot: 0,
    balCur: le(f, 170 + o, 2, true) / 1000, balOn: !!f[172 + o],
    fault: o ? prob >>> 16 : prob & 0xffff, warn: 0,
  };
  cellsMv = cells;
}
async function jkPoll() {
  if (Date.now() - jkLast > 4000) await jkSend(0x96);   // якщо BMS не шле дані сама — просимо
}


/* ---------- JK: налаштування (кадр 0x01) і запис ---------- */
// Регістр запису = (зсув у кадрі − 6) / 4 + 1; значення — 4 байти little-endian
let jkSet = null, jkEdits = {}, jkSetAt = 0, jkSetWaiter = null, jkSane = false;
const JKP = [
  // [reg, key, група, назва, тип, масштаб, знаків, мін, макс, пара]
  [0x04, 'ovp', 'cell', 'Перезаряд банки', 'v', 0.001, 3, 2, 4.6, 'ovpr'],
  [0x05, 'ovpr', 'cell', null, 'v', 0.001, 3, 2, 4.6],
  [0x02, 'uvp', 'cell', 'Перерозряд банки', 'v', 0.001, 3, 1.5, 4.2, 'uvpr'],
  [0x03, 'uvpr', 'cell', null, 'v', 0.001, 3, 1.5, 4.2],
  [0x0b, 'poff', 'cell', 'Вимкнення BMS', 'v', 0.001, 3, 1.5, 4],
  [0x01, 'sleep', 'cell', 'Напруга сну', 'v', 0.001, 3, 1.5, 4.5],
  [0x09, 'rcv', 'cell', 'Напруга заряду (RCV)', 'v', 0.001, 3, 2, 4.6],
  [0x0a, 'rfv', 'cell', 'Напруга підтримки (RFV)', 'v', 0.001, 3, 2, 4.6],
  [0x07, 'soc100', 'cell', 'SOC 100 %', 'v', 0.001, 3, 2, 4.6],
  [0x08, 'soc0', 'cell', 'SOC 0 %', 'v', 0.001, 3, 1.5, 4.2],
  [0x0c, 'chgoc', 'cur', 'Макс. струм заряду', 'v', 0.001, 1, 0.1, 600],
  [0x0d, 'chgocd', 'cur', 'Затримка OCP заряду', 'i', 1, 0, 0, 3600, null, 'с'],
  [0x0e, 'chgocr', 'cur', 'Відновлення OCP заряду', 'i', 1, 0, 0, 3600, null, 'с'],
  [0x0f, 'dsgoc', 'cur', 'Макс. струм розряду', 'v', 0.001, 1, 0.1, 600],
  [0x10, 'dsgocd', 'cur', 'Затримка OCP розряду', 'i', 1, 0, 0, 3600, null, 'с'],
  [0x11, 'dsgocr', 'cur', 'Відновлення OCP розряду', 'i', 1, 0, 0, 3600, null, 'с'],
  [0x21, 'scpd', 'cur', 'Затримка КЗ', 'i', 1, 0, 0, 100000, null, 'мкс'],
  [0x12, 'scpr', 'cur', 'Відновлення після КЗ', 'i', 1, 0, 0, 3600, null, 'с'],
  [0x14, 'cot', 'temp', 'Заряд: перегрів', 't', 0.1, 1, -40, 120, 'cotr'],
  [0x15, 'cotr', 'temp', null, 't', 0.1, 1, -40, 120],
  [0x18, 'cut', 'temp', 'Заряд: холод', 't', 0.1, 1, -40, 120, 'cutr'],
  [0x19, 'cutr', 'temp', null, 't', 0.1, 1, -40, 120],
  [0x16, 'dot', 'temp', 'Розряд: перегрів', 't', 0.1, 1, -40, 120, 'dotr'],
  [0x17, 'dotr', 'temp', null, 't', 0.1, 1, -40, 120],
  [0x1a, 'mot', 'temp', 'Перегрів MOS', 't', 0.1, 1, -40, 150, 'motr'],
  [0x1b, 'motr', 'temp', null, 't', 0.1, 1, -40, 150],
  [0x06, 'baltrig', 'bal', 'Різниця для балансу', 'v', 0.001, 3, 0.001, 1],
  [0x22, 'balstart', 'bal', 'Напруга старту балансу', 'v', 0.001, 3, 2, 4.6],
  [0x13, 'balcur', 'bal', 'Макс. струм балансу', 'v', 0.001, 1, 0.1, 10],
  [0x1c, 'cells', 'bat', 'Кількість банок', 'i', 1, 0, 1, 32],
  [0x20, 'cap', 'bat', 'Ємність батареї', 'v', 0.001, 1, 1, 2000, null, 'Ah'],
  [0x1d, 'swChg', 'sw', 'Заряд (MOS)', 'b'],
  [0x1e, 'swDsg', 'sw', 'Розряд (MOS)', 'b'],
  [0x1f, 'swBal', 'sw', 'Балансування', 'b'],
].map(a => ({ r: a[0], k: a[1], g: a[2], n: a[3], t: a[4], s: a[5], d: a[6], min: a[7], max: a[8], pair: a[9], u: a[10] ?? (a[4] === 'v' ? (a[5] === 0.001 && a[6] === 1 ? 'A' : 'V') : a[4] === 't' ? '°C' : '') }));
const JKPK = Object.fromEntries(JKP.map(p => [p.k, p]));
// параметри, яких немає в старіших прошивках (BMS віддає 0) — не показуємо поле і не перевіряємо
const JK_OPTIONAL = new Set(['rcv', 'rfv', 'soc100', 'soc0', 'sleep', 'balstart']);
const JK_GROUPS = [['sw', 'Перемикачі'], ['cell', 'Напруга банки'], ['bal', 'Баланс'], ['cur', 'Струм і КЗ'], ['temp', 'Температура'], ['bat', 'Батарея']];
function jkParse(f) {
  const o = {};
  for (const p of JKP) { const off = (p.r - 1) * 4 + 6; o[p.k] = le(f, off, 4, p.t === 't'); }
  jkSet = o;
  // перевірка, що розмітка кадру відповідає цій прошивці — інакше запис вимкнено
  const ok = o.cells >= 1 && o.cells <= 32 && (!cellsMv.length || o.cells === cellsMv.length)
    && o.ovp >= 2000 && o.ovp <= 4600 && o.uvp >= 1500 && o.uvp < o.ovp && o.ovpr <= o.ovp && o.uvpr >= o.uvp
    && [0, 1].includes(o.swChg) && [0, 1].includes(o.swDsg) && [0, 1].includes(o.swBal);
  if (ok !== jkSane) log('JK налаштування: ' + (ok ? 'розмітка підтверджена — запис дозволено' : 'значення не пройшли перевірку — запис вимкнено, скиньте сирий кадр налаштувань'));
  jkSane = ok;
}
const jkDisp = (p, raw) => p.t === 'b' ? (raw ? 'увімк.' : 'вимк.') : p.t === 'i' ? String(raw) : (raw * p.s).toFixed(p.d);
const jkCur = k => (k in jkEdits) ? jkEdits[k] : jkSet?.[k];
function renderJkParams() {
  if (driver !== 'jk') return;
  if (!jkSet) { $('pBody').innerHTML = '<div class="empty">Очікую кадр налаштувань від JK… <button class="btn sm" id="jkReq">Запросити</button></div>'; updateDirtyBar(); return; }
  $('pInfo').textContent = 'Отримано о ' + new Date(jkSetAt).toLocaleTimeString('uk-UA') + (jkSane ? '' : ' · запис вимкнено: розмітка не підтверджена');
  const html = [];
  for (const [g, title] of JK_GROUPS) {
    const ps = JKP.filter(p => p.g === g);
    const dirty = ps.filter(p => p.k in jkEdits).length;
    let body = '';
    if (ps.some(p => p.pair)) body += '<div class="pr head"><span></span><span>Поріг</span><span>Відновл.</span></div>';
    for (const p of ps) {
      if (!p.n) continue;
      if (p.t === 'b') {
        body += `<div class="bitrow"><span>${p.n}${p.k in jkEdits ? ' <span class="was">змінено</span>' : ''}</span><button class="sw ${jkCur(p.k) ? 'on' : ''}" data-jksw="${p.k}" aria-label="${p.n}" ${jkSane ? '' : 'disabled'}></button></div>`;
        continue;
      }
      if (!p.pair && JK_OPTIONAL.has(p.k) && jkSet[p.k] === 0 && !(p.k in jkEdits)) {
        body += `<div class="pr single"><span class="nm">${p.n} <span class="unit">${p.u}</span></span><span class="lbl" style="text-align:right">не використовується</span></div>`;
        continue;
      }
      const inp = q => `<input inputmode="decimal" data-jk="${q.k}" value="${jkDisp(q, jkCur(q.k))}" class="${q.k in jkEdits ? 'ch' : ''}" aria-label="${q.n || q.k}" ${jkSane ? '' : 'disabled'}>`;
      const keys = p.pair ? [p, JKPK[p.pair]] : [p];
      const was = keys.some(q => q.k in jkEdits) ? `<span class="was">було ${keys.map(q => jkDisp(q, jkSet[q.k])).join(' / ')}</span>` : '';
      const nm = `<span class="nm">${p.n} <span class="unit">${p.u}</span>${was}</span>`;
      body += p.pair ? `<div class="pr">${nm}${inp(p)}${inp(JKPK[p.pair])}</div>` : `<div class="pr single">${nm}${inp(p)}</div>`;
    }
    html.push(`<div class="grp open ${dirty ? 'dirty' : ''}"><div class="gh">${title}${dirty ? `<span class="cnt">${dirty} зм.</span>` : ''}</div><div class="gb">${body}</div></div>`);
  }
  $('pBody').innerHTML = html.join('') + '<div class="lbl" style="text-align:center">Регістри JK02. Зміни записуються лише після «Записати…».</div>';
  updateDirtyBar();
}
$('pBody').addEventListener('change', e => {
  const k = e.target.dataset.jk; if (!k || driver !== 'jk') return;
  const p = JKPK[k], v = parseFloat(String(e.target.value).replace(',', '.'));
  if (isNaN(v) || v < p.min || v > p.max) { e.target.classList.add('err'); toast(`${p.n || k}: допустимо ${p.min}…${p.max}`); return; }
  const raw = p.t === 'i' ? Math.round(v) : Math.round(v / p.s);
  if (raw === jkSet[k]) delete jkEdits[k]; else jkEdits[k] = raw;
  renderJkParams();
});
$('pBody').addEventListener('click', e => {
  if (driver !== 'jk') return;
  if (e.target.id === 'jkReq') { jkRequestSettings(); return; }
  const k = e.target.closest('[data-jksw]')?.dataset.jksw; if (!k) return;
  const v = jkCur(k) ? 0 : 1;
  if (v === jkSet[k]) delete jkEdits[k]; else jkEdits[k] = v;
  renderJkParams();
});
function jkValidate(v) {
  const err = [], warn = [];
  if (v.ovpr >= v.ovp) err.push('Відновлення перезаряду має бути нижче порогу');
  if (v.uvpr <= v.uvp) err.push('Відновлення перерозряду має бути вище порогу');
  if (v.uvp >= v.ovp) err.push('Перерозряд вище перезаряду');
  if (v.poff && v.poff >= v.uvp) warn.push('Напруга вимкнення BMS не нижча за поріг перерозряду');
  if (v.rcv && v.rcv > v.ovp) err.push('Напруга заряду (RCV) вища за поріг перезаряду');
  if (v.cotr >= v.cot || v.dotr >= v.dot || v.motr >= v.mot) err.push('Відновлення перегріву має бути нижче порогу');
  if (v.cutr <= v.cut) err.push('Відновлення холоду має бути вище порогу');
  if (v.cells !== jkSet.cells) warn.push(`Кількість банок ${jkSet.cells} → ${v.cells}: перевірте balance-шлейф`);
  if (v.swDsg === 0 && jkSet.swDsg === 1) warn.push('Розряд буде вимкнено — навантаження знеструмиться');
  return { err, warn };
}
async function jkRequestSettings(timeout = 5000) {
  const p = new Promise(res => { jkSetWaiter = res; setTimeout(() => { if (jkSetWaiter === res) { jkSetWaiter = null; res(); } }, timeout); });
  await jkSend(0x97).catch(() => {});
  await sleep(400);
  await jkSend(0x96).catch(() => {});
  await p;
}
const le4 = v => { v = v < 0 ? v + 2 ** 32 : v; return [v & 0xff, (v >>> 8) & 0xff, (v >>> 16) & 0xff, (v >>> 24) & 0xff]; };
async function jkWriteRegs(changes) {
  if ($('jkPwBefore')?.checked) await jkAuth(true);
  for (const c of changes) { await jkSend(c.r, le4(c.neu)); await sleep(350); }
  await sleep(500);
  const before = jkSetAt;
  await jkRequestSettings();
  if (jkSetAt === before) return { verified: false, bad: [] };
  return { verified: true, bad: changes.filter(c => jkSet[c.k] !== c.neu) };
}
async function jkWriteFlow() {
  if (!jkSane) return toast('Запис вимкнено: розмітка налаштувань не підтверджена');
  const keys = Object.keys(jkEdits); if (!keys.length) return;
  const vals = { ...jkSet, ...jkEdits }, v = jkValidate(vals);
  const changes = keys.map(k => { const p = JKPK[k]; return { k, r: p.r, neu: jkEdits[k], label: p.n || (JKP.find(x => x.pair === k)?.n + ' (відновл.)'), oldS: jkDisp(p, jkSet[k]), newS: jkDisp(p, jkEdits[k]) + ' ' + p.u }; });
  try { localStorage.setItem('jbd_jk_backup', JSON.stringify({ date: new Date().toISOString(), device: dev?.name, settings: jkSet })); } catch (_) {}
  const html = `<p class="lbl" style="font-size:14px">Буде змінено ${changes.length}. Поточні налаштування збережено як авто-копію.</p>
    <div class="diff"><div><span>Параметр</span><span>Було</span><span></span><span>Стане</span></div>${changes.map(c => `<div><span>${c.label}</span><s class="mono">${c.oldS}</s><span>→</span><b class="mono">${c.newS}</b></div>`).join('')}</div>
    ${v.err.map(x => `<div class="note bad">${x}</div>`).join('')}${v.warn.map(x => `<div class="note warn">${x}</div>`).join('')}
    ${!v.err.length && !v.warn.length ? '<div class="note ok">Перевірка: значення узгоджені</div>' : ''}`;
  if (!(await sheetConfirm('Записати в JK BMS?', html, 'Записати', !!v.err.length))) return;
  try {
    const r = await jkWriteRegs(changes);
    jkEdits = {}; renderJkParams();
    if (!r.verified) toast('Записано, але BMS не надіслала налаштування для звірки — натисніть «Запросити» пізніше', 5000);
    else if (r.bad.length) sheetConfirm('Розбіжність після запису', r.bad.map(c => `<div class="note bad">${c.label}: очікувалось ${c.newS}, зараз ${jkDisp(JKPK[c.k], jkSet[c.k])}</div>`).join(''), 'Зрозуміло', false, true);
    else toast('Записано і звірено: ' + changes.length);
  } catch (e) { toast(e.message); log('JK запис: ' + e.message); }
}
async function jkSwitch(reg) {
  const p = JKP.find(x => x.r === reg);
  if (!jkSane || !jkSet) return toast('Спочатку дочекайтесь налаштувань JK (вкладка «Параметри»)');
  const neu = jkSet[p.k] ? 0 : 1;
  const ok = await sheetConfirm((neu ? 'Увімкнути ' : 'Вимкнути ') + p.n.toLowerCase() + '?', !neu && reg === 0x1e ? '<div class="note warn">Навантаження буде знеструмлено.</div>' : '', neu ? 'Увімкнути' : 'Вимкнути');
  if (!ok) return;
  const r = await jkWriteRegs([{ k: p.k, r: reg, neu }]);
  toast(r.verified && !r.bad.length ? 'Виконано' : 'Команду надіслано, але підтвердження немає');
}


/* ---------- Daly Smart BMS (D2 / Modbus над BLE) ---------- */
let dalyBuf = [], dalyWaiter = null, dalyLast = 0, dalyInfo = null, dalyRaw = null, dalyMosTemp = null, dalyMosTried = false;
function crc16m(a) { let c = 0xffff; for (const b of a) { c ^= b; for (let i = 0; i < 8; i++) c = (c & 1) ? ((c >>> 1) ^ 0xA001) : (c >>> 1); } return c & 0xffff; }
const u16b = (d, i) => (d[i] << 8) | d[i + 1];
function dalyFrame(dev_id, fct, addr, count) {
  const f = [dev_id, fct, (addr >> 8) & 0xff, addr & 0xff, (count >> 8) & 0xff, count & 0xff];
  const c = crc16m(f); f.push(c & 0xff, (c >> 8) & 0xff); return new Uint8Array(f);
}
function dalyNotify(e) {
  dalyBuf.push(...new Uint8Array(e.target.value.buffer));
  for (;;) {
    const si = dalyBuf.findIndex((b, i) => b === 0xD2 && dalyBuf[i + 1] === 0x03);
    if (si < 0) { if (dalyBuf.length > 300) dalyBuf = []; return; }
    if (si > 0) dalyBuf = dalyBuf.slice(si);
    if (dalyBuf.length < 3) return;
    const total = 3 + dalyBuf[2] + 2;
    if (dalyBuf.length < total) return;
    const p = dalyBuf.slice(0, total); dalyBuf = dalyBuf.slice(total);
    const crc = crc16m(p.slice(0, total - 2));
    if ((p[total - 2] | (p[total - 1] << 8)) !== crc) { log('Daly: CRC не збігається'); continue; }
    log('← Daly ' + hex(p), dalyLast && p[2] === 124);
    if (dalyWaiter && (dalyWaiter.bc == null || dalyWaiter.bc === p[2])) { const w = dalyWaiter; dalyWaiter = null; clearTimeout(w.t); w.res(p); }
  }
}
async function dalyCmd(addr, count, timeout = 3500) {
  if (!txCh) throw new Error('не підключено');
  const bc = count * 2, f = dalyFrame(0xD2, 0x03, addr, count);
  log('→ Daly ' + hex(f), dalyLast && count === 62);
  dalyBuf = [];
  const p = new Promise((res, rej) => { dalyWaiter = { bc, res, t: setTimeout(() => { dalyWaiter = null; rej(new Error('тайм-аут Daly')); }, timeout) }; });
  try { await txCh.writeValueWithoutResponse(f); } catch (_) { await txCh.writeValueWithResponse(f); }
  return p;
}
async function dalyConnect(srv, svcs) {
  rxCh = await srv.getCharacteristic(DALY_RX);
  txCh = await srv.getCharacteristic(DALY_TX);
  rxCh.addEventListener('characteristicvaluechanged', dalyNotify);
  dalyBuf = []; dalyLast = 0; dalyInfo = null; dalyRaw = null; dalyMosTemp = null; dalyMosTried = false;
  await rxCh.startNotifications();
  $('dName').textContent = dev.name || 'Daly BMS';
  setConn('conn');
  log('підключено: ' + (dev.name || dev.id) + ' — пробую Daly D2…');
  try {
    const p = await dalyCmd(0x0000, 62, 5000);
    dalyParse(p); driver = 'daly';
    log('Daly D2 підтверджено');
    setConn('on'); applyDriverUi();
    try { const i = await dalyCmd(0x00A9, 32); dalyInfo = { sw: dalyText(i, 3, 19), hw: dalyText(i, 19, 35) }; } catch (_) {}
    renderDevInfo(); startPoll();
  } catch (e) {
    log('Daly не відповів (' + e.message + ') — універсальний режим');
    driver = 'generic';
    try { await rxCh.stopNotifications(); } catch (_) {}
    rxCh.removeEventListener?.('characteristicvaluechanged', dalyNotify);
    await genConnect(svcs || []);
  }
}
const dalyText = (f, a, b) => { let o = ''; for (let i = a; i < b && i < f.length; i++) { const c = f[i]; if (c >= 0x20 && c <= 0x7e) o += String.fromCharCode(c); } return o.trim(); };
function dalyParse(p) {
  dalyRaw = p; dalyLast = Date.now();
  const H = 3;
  const cc = u16b(p, H + 98);
  const n = Math.min(cc > 0 && cc <= 48 ? cc : 0, 48);
  const cells = []; for (let i = 0; i < n; i++) cells.push(u16b(p, H + i * 2));
  const nt = Math.min(u16b(p, H + 100) || 0, 8);
  const temps = []; const tbase = 32 * 2 + H;
  for (let i = 0; i < nt; i++) { const t = u16b(p, tbase + i * 2) - 40; if (t > -40 && t < 150) temps.push(t); }
  if (dalyMosTemp != null) temps.unshift(dalyMosTemp);
  let prob = 0; for (let i = 0; i < 8; i++) prob = prob * 256 + p[H + 116 + i];
  basic = {
    daly: true,
    v: u16b(p, H + 80) / 10,
    a: (u16b(p, H + 82) - 30000) / 10,
    soc: Math.round(u16b(p, H + 84) / 10),
    remain: u16b(p, H + 96) / 10,
    nominal: null,
    cycles: u16b(p, H + 102),
    cells: n, temps,
    tnames: (dalyMosTemp != null ? ['MOS'] : []).concat(Array.from({ length: nt }, (_, i) => 'T' + (i + 1))),
    bal: 0, prot: 0,
    fet: (u16b(p, H + 106) ? 1 : 0) | (u16b(p, H + 108) ? 2 : 0),
    delta: u16b(p, H + 112),
    fault: prob, warn: 0,
  };
  cellsMv = cells;
}
async function dalyPoll() {
  if (!dalyMosTried) { dalyMosTried = true; try { const m = await dalyCmd(0x003E, 9); const t = u16b(m, 3 + 8) - 40; if (t > -40 && t < 150) dalyMosTemp = t; } catch (_) {} }
  const p = await dalyCmd(0x0000, 62); dalyParse(p);
  if (document.querySelector('#v-srv.act')) renderDevInfo();
}


let manualDisc = false;
function onDisc() {
  const wasOn = connState === 'on';
  txCh = rxCh = null; stopPoll(); setConn('off');
  if (waiter) { clearTimeout(waiter.t); waiter = null; }
  if (felWaiter) { clearTimeout(felWaiter.t); felWaiter = null; }
  if (!manualDisc && !cancelConn && dev && wasOn && driver !== 'generic') { log('зв\'язок втрачено, перепідключення…'); reconnect(); }
  else if (!manualDisc && driver === 'generic') log('пристрій розірвав з\'єднання');
  manualDisc = false;
}
async function reconnect() {
  for (let i = 0; i < 5 && dev && !txCh && !cancelConn; i++) {
    setConn('conn'); await sleep(1500 * (i + 1));
    if (cancelConn) break;
    try { await gattConnect(); return; } catch (e) { log('спроба ' + (i + 1) + ': ' + e.message); }
  }
  setConn('off');
}
function setConn(s) {
  if (s === 'on' && connState !== 'on') { dataTs = 0; basic = null; atLast = null; cellsMv = []; hist.length = 0; setLoading(true); }
  if (s !== 'on') setLoading(false);
  connState = s;
  if (s === 'off') setTimeout(renderKnown, 0); else if ($('known')) $('known').innerHTML = '';
  $('cDot').className = 'dot' + (s === 'on' ? ' on' : '');
  $('cTxt').textContent = s === 'on' ? 'Підключено' : s === 'conn' ? 'Скасувати' : 'Підключити';
  $('dSub').textContent = s === 'on' ? (driver === 'fel' ? 'SN ' + (felInfo?.DevSN || felRaw?.DevSN || '—') : driver === 'generic' ? 'універсальний режим' : (dev?.id?.slice(0, 17) || '') + (devStrings.hw ? ' · ' + devStrings.hw : '')) : s === 'conn' ? 'підключення… (натисніть, щоб скасувати)' : 'не підключено';
  $('swChg').disabled = $('swDsg').disabled = s !== 'on' || !(driver === 'jbd' || driver === 'jk');
}
// кнопка-тригер: Підключити → (Скасувати під час підключення) → Відключити
$('bConn').onclick = async () => {
  if (connState === 'conn') {
    cancelConn = true;
    try { dev?.gatt?.disconnect(); } catch (_) {}
    setConn('off'); log('підключення скасовано');
    return;
  }
  if (connState === 'on') {
    const ok = await sheetConfirm('Відключитися?', '<p>З\'єднання з пристроєм буде закрито.</p>', 'Відключити');
    if (ok) { manualDisc = true; cancelConn = true; try { dev.gatt.disconnect(); } catch (_) {} setConn('off'); }
    return;
  }
  connect();
};

/* ---------- опитування ---------- */
function startPoll() { stopPoll(); poll(); pollTimer = setInterval(poll, pollMs); }
function stopPoll() { clearInterval(pollTimer); pollTimer = null; }
$('selPoll').onchange = e => { pollMs = +e.target.value; if (pollTimer) startPoll(); };
async function poll() {
  if (!txCh || busy) return;
  try {
    if (driver === 'generic' || driver === 'ffe0') return;
    if (driver === 'daly') { await dalyPoll(); } else
    if (driver === 'jk') { await jkPoll(); if (!jkLast) return; if (document.querySelector('#v-srv.act')) renderDevInfo(); } else
    if (driver === 'atorch') { if (!atLast) return; } else
    if (driver === 'fel') await felPoll(); else
    await exclusive(async () => {
      const b = await rd(0x03, true);
      if (!b.status) basic = parseBasic(b.data);
      const c = await rd(0x04, true);
      if (!c.status) { cellsMv = []; for (let i = 0; i + 1 < c.data.length; i += 2) cellsMv.push(u16(c.data, i)); }
    });
    if (basic) {
      const now = Date.now();
      hist.push({ t: now, v: basic.v, a: basic.a });
      while (hist.length && hist[0].t < now - 30 * 60e3) hist.shift();
      if (csvOn) { csvRows.push(driver === 'atorch' ? [new Date(now).toISOString(), atLast.v, atLast.a, atLast.ah, atLast.wh, atLast.temp] : [new Date(now).toISOString(), basic.v, basic.a, basic.soc, basic.remain, ...basic.temps, ...cellsMv.map(x => x / 1000)]); $('csvN').textContent = '(' + csvRows.length + ')'; }
    }
    renderMon();
  } catch (e) { log('опитування: ' + e.message); }
}
function parseBasic(d) {
  const o = {
    v: u16(d, 0) / 100, a: s16(d, 2) / 100, remain: u16(d, 4) / 100, nominal: u16(d, 6) / 100,
    cycles: u16(d, 8), date: u16(d, 10), bal: (u16(d, 14) << 16) | u16(d, 12), prot: u16(d, 16),
    ver: d[18], soc: d[19], fet: d[20], cells: d[21], ntc: d[22], temps: []
  };
  for (let i = 0; i < o.ntc && 23 + i * 2 + 1 < d.length; i++) o.temps.push((u16(d, 23 + i * 2) - 2731) / 10);
  return o;
}
const PROT = ['Перезаряд банки', 'Перерозряд банки', 'Перезаряд пакета', 'Перерозряд пакета', 'Перегрів при заряді', 'Холод при заряді', 'Перегрів при розряді', 'Холод при розряді', 'Струм заряду', 'Струм розряду', 'Коротке замикання', 'Помилка AFE', 'Програмне блокування MOS'];

/* ---------- рендер моніторингу ---------- */
let dataTs = 0;
function setLoading(on) {
  $('gauge').classList.toggle('loading', on);
  if (on) { $('mSoc').textContent = '—'; $('mCap').textContent = 'Отримую дані…'; $('mV').textContent = '—'; $('mA').textContent = '— A'; $('mW').textContent = '— W'; $('mState').textContent = '—'; }
}
function dataTick() {
  if (!dataTs) setLoading(false);
  dataTs = Date.now();
  const d = $('cDot'); d.classList.add('pulse'); setTimeout(() => d.classList.remove('pulse'), 250);
}
function renderMon() {
  if ((driver === 'atorch' && atLast) || (driver !== 'atorch' && basic)) dataTick();
  if (driver === 'atorch') return renderAtorch();
  if (driver === 'generic' || driver === 'ffe0') return;
  const b = basic; if (!b) return;
  $('mV').textContent = fmt(b.v, 2);
  $('mA').textContent = fmt(b.a, 2) + ' A';
  $('mW').textContent = fmt(b.v * b.a, 0) + ' W';
  $('mSoc').textContent = b.soc;
  $('mSoc').nextElementSibling.style.display = '';
  $('mCap').textContent = fmt(b.remain, 1) + ' / ' + fmt(b.nominal, 0) + ' Ah';
  const col = b.soc < 15 ? '#F0A030' : b.soc < 40 ? '#E8C547' : '#34C46E';
  $('gauge').style.background = `conic-gradient(${col} 0 ${b.soc}%, #2A3138 ${b.soc}% 100%)`;
  const st = b.a > 0.05 ? 'Заряд' : b.a < -0.05 ? 'Розряд' : 'Простій';
  let eta = '';
  if (b.a <= -1 && b.remain != null) eta = ' · ~' + fmt(b.remain / -b.a, 1) + ' год';
  if (b.a >= 1 && b.remain != null && b.nominal != null) eta = ' · до повного ~' + fmt((b.nominal - b.remain) / b.a, 1) + ' год';
  const eq = b.cycleAh != null && b.nominal ? b.cycleAh / b.nominal : null;
  $('mState').textContent = st + eta + ' · ' + b.cells + 'S' + (b.soh != null ? ' · SOH ' + fmt(b.soh, 0) + ' %' : '') + (b.cycles !== '—' ? ' · циклів: ' + b.cycles + (eq != null ? ' (екв. ' + fmt(eq, 1) + ')' : '') : '');
  const chg = !!(b.fet & 1), dsg = !!(b.fet & 2);
  $('swChg').classList.toggle('on', chg); $('mChgT').textContent = chg ? 'Увімкнено' : 'Вимкнено';
  $('swDsg').classList.toggle('on', dsg); $('mDsgT').textContent = dsg ? 'Увімкнено' : 'Вимкнено';

  const act = PROT.filter((_, i) => b.prot & (1 << i));
  if (b.fel || b.jk || b.daly) {
    if (b.fault) act.push('Аварія BMS, код 0x' + b.fault.toString(16).toUpperCase());
    if (b.warn) act.push('Попередження BMS, код 0x' + b.warn.toString(16).toUpperCase());
  }
  const al = $('mAlert');
  if (act.length) { al.className = 'alert bad'; al.textContent = 'Спрацював захист: ' + act.join(', '); }
  else if (b.soc <= 10) { al.className = 'alert warn'; al.textContent = 'Низький заряд — зарядіть батарею'; }
  else al.className = 'alert';
  $('prot').innerHTML = act.length ? act.map(x => `<span class="chip bad">${x}</span>`).join('') : '<span class="chip ok">Без спрацювань</span>';

  // банки
  const n = cellsMv.length;
  if (n) {
    const max = Math.max(...cellsMv), min = Math.min(...cellsMv.filter(x => x > 500).concat([max]));
    const avg = cellsMv.reduce((s, x) => s + x, 0) / n;
    $('cTitle').textContent = 'Банки · ' + n + 'S';
    $('cDelta').innerHTML = 'Δ <b class="mono" style="color:var(--ink)">' + (max - min) + ' mV</b>';
    const lo = Number(params?.cuvp ?? 2800), hi = Number(params?.covp ?? 4200);
    const iMax = cellsMv.indexOf(max), iMin = cellsMv.indexOf(min);
    $('cells').innerHTML = cellsMv.map((mv, i) => {
      let c = 'cell';
      if (mv < 500) c += ' zero'; else if (i === iMax && max !== min) c += ' max'; else if (i === iMin && max !== min) c += ' min';
      if (b.bal & (1 << i)) c += ' bal';
      const pct = Math.max(0, Math.min(100, (mv - lo) / (hi - lo) * 100));
      return `<div class="${c}"><span class="lbl">#${i + 1}</span><b class="mono">${(mv / 1000).toFixed(3)}</b><div class="bar"><i style="width:${pct}%"></i></div></div>`;
    }).join('');
    $('cLegend').innerHTML = `<span>макс ${fmt(max / 1000, 3)}</span><span>мін ${fmt(min / 1000, 3)}</span><span>сер ${fmt(avg / 1000, 3)} V</span>` + (b.bal ? '<span style="color:#146C3B">● балансування</span>' : '');
  }
  // температури
  if (b.jk || b.daly) {
    $('temps').innerHTML = b.temps.map((t, i) => `<div class="card"><div class="lbl">${b.tnames[i] || ('T' + (i + 1))}</div><div class="val">${fmt(t, 1)} °C</div></div>`).join('');
    if (b.jk) $('cDelta').innerHTML += b.balOn ? ` · баланс <b class="mono">${fmt(b.balCur, 2)} A</b>` : '';
  } else {
  const tCards = b.fel ? b.temps.map((t, i) => ['Банки T' + (i + 1), t]).concat((b.boardTemps || []).map((t, i) => ['Плата BMS ' + (i + 1), t])) : null;
  if (b.fel) {
    $('temps').innerHTML = tCards.map(([n, t]) => `<div class="card"><div class="lbl">${n}</div><div class="val">${fmt(t, 1)} °C</div></div>`).join('');
    const L = b.limits;
    $('limCard').style.display = L ? '' : 'none';
    if (L) $('limBody').innerHTML =
      `<div class="kv"><span>Напруга заряду (CVL)</span><b class="mono">${fmt(L.cvl, 1)} V</b></div>` +
      `<div class="kv"><span>Напруга відсічки розряду (DVL)</span><b class="mono">${fmt(L.dvl, 1)} V</b></div>` +
      `<div class="kv"><span>Ліміт струму заряду (CCL)</span><b class="mono">${L.ccl ?? '—'}</b></div>` +
      `<div class="kv"><span>Ліміт струму розряду (DCL)</span><b class="mono">${L.dcl ?? '—'}</b></div>` +
      `<div class="hint" style="padding-left:0;padding-right:0">Струми — сирі значення BMS, масштаб не підтверджено</div>`;
  } else
  $('temps').innerHTML = b.temps.map((t, i) => `<div class="card"><div class="lbl">${i === 0 && b.temps.length > 1 ? 'MOS' : 'T' + (b.temps.length > 1 ? i : i + 1)}</div><div class="val">${fmt(t, 1)} °C</div></div>`).join('');
  }
  drawChart($('chV'), hist.map(h => h.v), '#0B6BCB', $('hRange'), 'V', 2);
  drawChart($('chA'), hist.map(h => h.a), '#B45309', $('hRangeA'), 'A', 2, true);
}
function drawChart(cv, arr, color, rangeEl, unit, d, zero) {
  const dpr = window.devicePixelRatio || 1, w = cv.clientWidth, h = 80;
  cv.width = w * dpr; cv.height = h * dpr;
  const g = cv.getContext('2d'); g.scale(dpr, dpr); g.clearRect(0, 0, w, h);
  if (arr.length < 2) { rangeEl.textContent = ''; return; }
  let mn = Math.min(...arr), mx = Math.max(...arr);
  if (zero) { mn = Math.min(mn, 0); mx = Math.max(mx, 0); }
  if (mx - mn < 0.02) { mx += 0.01; mn -= 0.01; }
  rangeEl.textContent = fmt(Math.min(...arr), d) + '…' + fmt(Math.max(...arr), d) + ' ' + unit + ' · ' + Math.round((hist[hist.length - 1].t - hist[0].t) / 60000) + ' хв';
  const y = v => h - 4 - (v - mn) / (mx - mn) * (h - 8);
  g.strokeStyle = '#E3E8ED'; g.lineWidth = 1;
  if (zero) { g.beginPath(); g.moveTo(0, y(0)); g.lineTo(w, y(0)); g.stroke(); }
  g.strokeStyle = color; g.lineWidth = 2; g.beginPath();
  arr.forEach((v, i) => { const x = i / (arr.length - 1) * w; i ? g.lineTo(x, y(v)) : g.moveTo(x, y(v)); });
  g.stroke();
}

/* ---------- MOS ---------- */
async function setMos(which) {
  if (!basic) return;
  if (driver === 'jk') return jkSwitch(which === 'c' ? 0x1d : 0x1e);
  let chg = !!(basic.fet & 1), dsg = !!(basic.fet & 2);
  if (which === 'c') chg = !chg; else dsg = !dsg;
  const what = which === 'c' ? 'заряд' : 'розряд';
  const turningOff = which === 'c' ? !chg : !dsg;
  const ok = await sheetConfirm((turningOff ? 'Вимкнути ' : 'Увімкнути ') + what + '?',
    turningOff && which === 'd' ? '<div class="note warn">Навантаження буде знеструмлено.</div>' : '', turningOff ? 'Вимкнути' : 'Увімкнути');
  if (!ok) return;
  const mask = (chg ? 0 : 1) | (dsg ? 0 : 2);
  try {
    await exclusive(async () => { const r = await wr(0xe1, [0x00, mask]); if (r.status) throw new Error('BMS відхилила команду'); });
    toast('Виконано'); setTimeout(poll, 300);
  } catch (e) { toast(e.message); }
}
$('swChg').onclick = () => setMos('c');
$('swDsg').onclick = () => setMos('d');

/* ---------- параметри: опис регістрів ---------- */
// t: v(scaled number) | temp | int | bits | signed
const P = [
  // батарея
  { k: 'cell_cnt', r: 0x2f, g: 'bat', n: 'Кількість банок', t: 'int', min: 3, max: 32 },
  { k: 'design_cap', r: 0x10, g: 'bat', n: 'Номінальна ємність', t: 'v', s: 0.01, u: 'Ah', d: 2, min: 0.1, max: 650 },
  { k: 'cycle_cap', r: 0x11, g: 'bat', n: 'Ємність циклу', t: 'v', s: 0.01, u: 'Ah', d: 2, min: 0.1, max: 650 },
  { k: 'dsg_rate', r: 0x14, g: 'bat', n: 'Саморозряд', t: 'v', s: 0.1, u: '%', d: 1, min: 0, max: 100 },
  { k: 'shunt', r: 0x2c, g: 'bat', n: 'Опір шунта', t: 'v', s: 0.1, u: 'мОм', d: 1, min: 0.1, max: 100 },
  // напруга банки
  { k: 'covp', r: 0x24, g: 'cell', n: 'Перезаряд', pair: 'covp_rel', t: 'v', s: 0.001, u: 'V', d: 3, min: 2, max: 4.5 },
  { k: 'covp_rel', r: 0x25, g: 'cell', t: 'v', s: 0.001, u: 'V', d: 3, min: 2, max: 4.5, sub: 1 },
  { k: 'cuvp', r: 0x26, g: 'cell', n: 'Перерозряд', pair: 'cuvp_rel', t: 'v', s: 0.001, u: 'V', d: 3, min: 1.5, max: 4 },
  { k: 'cuvp_rel', r: 0x27, g: 'cell', t: 'v', s: 0.001, u: 'V', d: 3, min: 1.5, max: 4, sub: 1 },
  // напруга пакета
  { k: 'povp', r: 0x20, g: 'pack', n: 'Перезаряд', pair: 'povp_rel', t: 'v', s: 0.01, u: 'V', d: 2, min: 3, max: 150 },
  { k: 'povp_rel', r: 0x21, g: 'pack', t: 'v', s: 0.01, u: 'V', d: 2, min: 3, max: 150, sub: 1 },
  { k: 'puvp', r: 0x22, g: 'pack', n: 'Перерозряд', pair: 'puvp_rel', t: 'v', s: 0.01, u: 'V', d: 2, min: 3, max: 150 },
  { k: 'puvp_rel', r: 0x23, g: 'pack', t: 'v', s: 0.01, u: 'V', d: 2, min: 3, max: 150, sub: 1 },
  // струм
  { k: 'chgoc', r: 0x28, g: 'cur', n: 'Макс. струм заряду', t: 'v', s: 0.01, u: 'A', d: 2, min: 0.1, max: 600 },
  { k: 'dsgoc', r: 0x29, g: 'cur', n: 'Макс. струм розряду', t: 'signed', s: 0.01, u: 'A', d: 2, min: 0.1, max: 600 },
  // температура
  { k: 'chgot', r: 0x18, g: 'temp', n: 'Заряд: перегрів', pair: 'chgot_rel', t: 'temp', min: -40, max: 100 },
  { k: 'chgot_rel', r: 0x19, g: 'temp', t: 'temp', min: -40, max: 100, sub: 1 },
  { k: 'chgut', r: 0x1a, g: 'temp', n: 'Заряд: холод', pair: 'chgut_rel', t: 'temp', min: -40, max: 100 },
  { k: 'chgut_rel', r: 0x1b, g: 'temp', t: 'temp', min: -40, max: 100, sub: 1 },
  { k: 'dsgot', r: 0x1c, g: 'temp', n: 'Розряд: перегрів', pair: 'dsgot_rel', t: 'temp', min: -40, max: 100 },
  { k: 'dsgot_rel', r: 0x1d, g: 'temp', t: 'temp', min: -40, max: 100, sub: 1 },
  { k: 'dsgut', r: 0x1e, g: 'temp', n: 'Розряд: холод', pair: 'dsgut_rel', t: 'temp', min: -40, max: 100 },
  { k: 'dsgut_rel', r: 0x1f, g: 'temp', t: 'temp', min: -40, max: 100, sub: 1 },
  // баланс
  { k: 'bal_start', r: 0x2a, g: 'bal', n: 'Напруга старту', t: 'v', s: 0.001, u: 'V', d: 3, min: 2, max: 4.5 },
  { k: 'bal_window', r: 0x2b, g: 'bal', n: 'Різниця для старту', t: 'int', u: 'mV', min: 1, max: 500 },
  // SoC
  { k: 'cap_100', r: 0x12, g: 'soc', n: '100 %', t: 'v', s: 0.001, u: 'V', d: 3, min: 2, max: 4.5 },
  { k: 'cap_80', r: 0x32, g: 'soc', n: '80 %', t: 'v', s: 0.001, u: 'V', d: 3, min: 2, max: 4.5 },
  { k: 'cap_60', r: 0x33, g: 'soc', n: '60 %', t: 'v', s: 0.001, u: 'V', d: 3, min: 2, max: 4.5 },
  { k: 'cap_40', r: 0x34, g: 'soc', n: '40 %', t: 'v', s: 0.001, u: 'V', d: 3, min: 2, max: 4.5 },
  { k: 'cap_20', r: 0x35, g: 'soc', n: '20 %', t: 'v', s: 0.001, u: 'V', d: 3, min: 2, max: 4.5 },
  { k: 'cap_0', r: 0x13, g: 'soc', n: '0 %', t: 'v', s: 0.001, u: 'V', d: 3, min: 1.5, max: 4.5 },
  // функції
  { k: 'func', r: 0x2d, g: 'func', n: 'Функції', t: 'bits', bits: ['Вимикач (switch)', 'Виявлення навантаження', 'Балансування', 'Баланс лише при заряді', 'LED індикатор', 'LED: 5 сегментів'] },
  { k: 'ntc', r: 0x2e, g: 'func', n: 'Датчики NTC', t: 'bits', bits: ['NTC1', 'NTC2', 'NTC3', 'NTC4', 'NTC5', 'NTC6', 'NTC7', 'NTC8'] },
  { k: 'fet_time', r: 0x30, g: 'func', n: 'Затримка MOS', t: 'int', u: 'с', min: 0, max: 65535 },
  { k: 'led_time', r: 0x31, g: 'func', n: 'Час LED', t: 'int', u: 'с', min: 0, max: 65535 },
  // апаратні
  { k: 'covp_hw', r: 0x36, g: 'hw', n: 'Апаратний перезаряд банки', t: 'v', s: 0.001, u: 'V', d: 3, min: 2, max: 5 },
  { k: 'cuvp_hw', r: 0x37, g: 'hw', n: 'Апаратний перерозряд банки', t: 'v', s: 0.001, u: 'V', d: 3, min: 1, max: 4 },
];
const PK = Object.fromEntries(P.map(p => [p.k, p]));
const GROUPS = [
  ['bat', 'Батарея', 'all'], ['cell', 'Напруга банки', 'v'], ['pack', 'Напруга пакета', 'v'], ['cur', 'Струм', 'a'],
  ['temp', 'Температура', 't'], ['bal', 'Баланс', 'b'], ['soc', 'Таблиця SoC (напруга банки)', 'v'],
  ['func', 'Функції', 'all'], ['hw', 'Апаратні захисти', 'v'],
];
const FILTERS = [['all', 'Усі'], ['v', 'Напруга'], ['a', 'Струм'], ['t', 'Температура'], ['b', 'Баланс']];
const PRESETS = {
  NMC: { covp: 4250, covp_rel: 4150, cuvp: 2800, cuvp_rel: 3000, bal_start: 3400, cap_100: 4150, cap_80: 4000, cap_60: 3850, cap_40: 3700, cap_20: 3550, cap_0: 3100, covp_hw: 4300, cuvp_hw: 2500 },
  LFP: { covp: 3650, covp_rel: 3400, cuvp: 2500, cuvp_rel: 2900, bal_start: 3400, cap_100: 3450, cap_80: 3330, cap_60: 3300, cap_40: 3270, cap_20: 3200, cap_0: 2800, covp_hw: 3750, cuvp_hw: 2200 },
  LTO: { covp: 2850, covp_rel: 2700, cuvp: 1800, cuvp_rel: 2000, bal_start: 2400, cap_100: 2700, cap_80: 2550, cap_60: 2450, cap_40: 2350, cap_20: 2250, cap_0: 2000, covp_hw: 2950, cuvp_hw: 1600 },
};

/* raw <-> display */
function toDisp(p, raw) {
  if (raw == null) return null;
  if (p.t === 'temp') return (raw - 2731) / 10;
  if (p.t === 'signed') { const v = raw & 0x8000 ? raw - 0x10000 : raw; return Math.abs(v) * p.s; }
  if (p.t === 'v') return raw * p.s;
  return raw;
}
function toRaw(p, val) {
  if (p.t === 'temp') return Math.round(val * 10) + 2731;
  if (p.t === 'signed') { const orig = params?.[p.k] ?? 0; const neg = (orig & 0x8000) !== 0; let r = Math.round(val / p.s); if (neg) r = (0x10000 - r) & 0xffff; return r; }
  if (p.t === 'v') return Math.round(val / p.s);
  return Math.round(val);
}
const cur = k => (k in edits) ? edits[k] : params?.[k];
const curDisp = k => toDisp(PK[k], cur(k));

/* ---------- читання параметрів ---------- */
async function readParams(pw) {
  if (!txCh) { toast('Спочатку підключіться'); return false; }
  if (driver === 'jk') { $('bReadP').disabled = true; await jkRequestSettings(); $('bReadP').disabled = false; renderJkParams(); if (!jkSet) toast('BMS не надіслала налаштування'); return !!jkSet; }
  if (driver === 'fel') { toast('Для Felicity налаштування поки недоступні'); return false; }
  $('bReadP').disabled = true; $('pInfo').textContent = 'Читаю…';
  try {
    await exclusive(async () => {
      await enterFactory(pw);
      try {
        const raw = {};
        for (let reg = 0x10; reg <= 0x3f; reg++) {
          try { const r = await rd(reg, true); if (!r.status && r.data.length >= 2) raw[reg] = u16(r.data, 0); } catch (_) {}
        }
        const out = {}, miss = [];
        for (const p of P) { if (raw[p.r] != null) out[p.k] = raw[p.r]; else miss.push(p.k); }
        if (!Object.keys(raw).length) throw new Error('регістри не читаються');
        for (const [reg, key] of [[0xa0, 'mfg'], [0xa1, 'model'], [0xa2, 'barcode']]) {
          try { const r = await rd(reg); if (!r.status && r.data.length) devStrings[key] = new TextDecoder().decode(new Uint8Array(r.data.slice(1, 1 + r.data[0]))).replace(/\0/g, ''); } catch (_) {}
        }
        params = out; params._raw = raw; params._miss = miss;
      } finally { await exitNoSave(); }
    });
    lastPw = pw || '';
    edits = {};
    $('pInfo').textContent = 'Прочитано о ' + new Date().toLocaleTimeString('uk-UA') + (params._miss.length ? ' · недоступно: ' + params._miss.length : '');
    renderParams(); renderDevInfo(); renderMon();
    return true;
  } catch (e) {
    $('pInfo').textContent = e.message;
    log('читання параметрів: ' + e.message);
    const pw2 = await sheetPassword(e.message);
    if (pw2 != null) return readParams(pw2);
    return false;
  } finally { $('bReadP').disabled = false; }
}
$('bReadP').onclick = () => readParams(lastPw);

/* ---------- рендер параметрів ---------- */
$('pFilt').innerHTML = FILTERS.map(([k, n]) => `<button data-f="${k}" class="${k === filter ? 'act' : ''}">${n}</button>`).join('');
$('pFilt').onclick = e => { const f = e.target.dataset.f; if (!f) return; filter = f; $('pFilt').querySelectorAll('button').forEach(b => b.classList.toggle('act', b.dataset.f === f)); renderParams(); };

function inputFor(p) {
  const v = curDisp(p.k), ch = p.k in edits;
  if (params[p.k] == null) return '<span class="lbl">н/д</span>';
  const step = p.t === 'temp' ? 0.1 : p.t === 'int' ? 1 : p.s;
  const val = p.t === 'int' ? v : v.toFixed(p.t === 'temp' ? 1 : p.d);
  return `<input inputmode="decimal" data-k="${p.k}" value="${val}" step="${step}" class="${ch ? 'ch' : ''}" aria-label="${p.n || p.k}">`;
}
function wasText(p) { return (p.k in edits) ? (toDisp(p, params[p.k]).toFixed(p.t === 'int' ? 0 : p.t === 'temp' ? 1 : p.d)) : null; }

function renderParams() {
  if (!params) return;
  const html = [];
  for (const [g, title, f] of GROUPS) {
    if (filter !== 'all' && f !== filter) continue;
    const ps = P.filter(p => p.g === g);
    const dirty = ps.filter(p => p.k in edits).length;
    const open = openGroups.has(g) || filter !== 'all';
    let body = '';
    if (g === 'bat') {
      const chem = detectChem();
      body += `<div class="pr single"><span class="nm">Хімія (набір порогів)</span><select id="selChem">${['—', 'NMC', 'LFP', 'LTO'].map(c => `<option ${c === chem ? 'selected' : ''}>${c}</option>`).join('')}</select></div>`;
    }
    const paired = ps.some(p => p.pair);
    if (paired) body += `<div class="pr head"><span></span><span>Поріг</span><span>Відновл.</span></div>`;
    for (const p of ps) {
      if (p.sub) continue;
      if (p.t === 'bits') {
        const v = cur(p.k) ?? 0;
        body += `<div class="hint" style="font-weight:600;color:var(--ink)">${p.n}${p.k in edits ? ' <span class="cnt" style="color:var(--warn)">змінено</span>' : ''}</div>` +
          p.bits.map((b, i) => `<div class="bitrow"><span>${b}</span><button class="sw ${v & (1 << i) ? 'on' : ''}" data-bit="${p.k}:${i}" aria-label="${b}" ${params[p.k] == null ? 'disabled' : ''}></button></div>`).join('');
        continue;
      }
      const u = p.t === 'temp' ? '°C' : (p.u || '');
      const keys = p.pair ? [p, PK[p.pair]] : [p];
      const changed = keys.some(x => x.k in edits && params[x.k] != null);
      const wasS = changed ? keys.map(x => params[x.k] == null ? '—' : dispStr(x, params[x.k]).replace(/ .*$/, '')).join(' / ') : '';
      const nm = `<span class="nm">${p.n} <span class="unit">${u}</span>${changed ? `<span class="was">було ${wasS}</span>` : ''}</span>`;
      if (p.pair) body += `<div class="pr">${nm}${inputFor(p)}${inputFor(PK[p.pair])}</div>`;
      else body += `<div class="pr single">${nm}${inputFor(p)}</div>`;
    }
    if (g === 'pack' && cur('cell_cnt')) {
      const n = cur('cell_cnt');
      body += `<div class="hint">Для ${n}S: поріг банки × ${n} = ${fmt(curDisp('covp') * n, 2)} / ${fmt(curDisp('cuvp') * n, 2)} V <button class="btn sm" id="bPackCalc" style="margin-left:6px">Підставити</button></div>`;
    }
    if (g === 'soc') body += `<div class="hint">Напруга однієї банки, за якою BMS коригує SoC у спокої</div>`;
    html.push(`<div class="grp ${open ? 'open' : ''} ${dirty ? 'dirty' : ''}" data-g="${g}"><button class="gh" data-tg="${g}">${title}${dirty ? `<span class="cnt">${dirty} зм.</span>` : '<span class="lbl">' + (open ? '▾' : '▸') + '</span>'}</button><div class="gb">${body}</div></div>`);
  }
  $('pBody').innerHTML = html.join('') + '<div class="lbl" style="text-align:center">Регістри EEPROM JBD. Зміни застосовуються лише після «Записати».</div>';
  updateDirtyBar();
}
function detectChem() {
  const c = curDisp('covp');
  if (c == null) return '—';
  if (c >= 4.0) return 'NMC'; if (c >= 3.5 && c < 3.8) return 'LFP'; if (c < 3.0) return 'LTO'; return '—';
}
function setEdit(k, raw) {
  if (raw === params[k]) delete edits[k]; else edits[k] = raw;
}
$('pBody').addEventListener('click', e => {
  const tg = e.target.closest('[data-tg]');
  if (tg) { const g = tg.dataset.tg; openGroups.has(g) ? openGroups.delete(g) : openGroups.add(g); renderParams(); return; }
  const bit = e.target.closest('[data-bit]');
  if (bit) { const [k, i] = bit.dataset.bit.split(':'); setEdit(k, (cur(k) ?? 0) ^ (1 << +i)); renderParams(); return; }
  if (e.target.id === 'bPackCalc') {
    const n = cur('cell_cnt');
    for (const [pk, ck] of [['povp', 'covp'], ['povp_rel', 'covp_rel'], ['puvp', 'cuvp'], ['puvp_rel', 'cuvp_rel']])
      setEdit(pk, toRaw(PK[pk], curDisp(ck) * n));
    renderParams();
  }
});
$('pBody').addEventListener('change', e => {
  if (e.target.id === 'selChem') {
    const pr = PRESETS[e.target.value]; if (!pr) return;
    for (const [k, mv] of Object.entries(pr)) if (params[k] != null) setEdit(k, mv); // усі пресетні регістри в mV = raw
    toast('Набір порогів ' + e.target.value + ' підставлено. Перевірте пороги пакета.');
    renderParams(); return;
  }
  const k = e.target.dataset.k; if (!k) return;
  const p = PK[k], v = parseFloat(String(e.target.value).replace(',', '.'));
  if (isNaN(v) || v < p.min || v > p.max) { e.target.classList.add('err'); toast(`${p.n || k}: допустимо ${p.min}…${p.max}`); return; }
  setEdit(k, toRaw(p, v)); renderParams();
});
function updateDirtyBar() {
  const n = Object.keys(driver === 'jk' ? jkEdits : edits).length;
  $('dBar').classList.toggle('show', n > 0 && document.querySelector('#v-par.act') != null);
  $('dTxt').textContent = n + ' ' + (n === 1 ? 'незбережена зміна' : n < 5 ? 'незбережені зміни' : 'незбережених змін');
}
$('bReset').onclick = () => { if (driver === 'jk') { jkEdits = {}; renderJkParams(); return; } edits = {}; renderParams(); };

/* ---------- перевірка ---------- */
function validate(vals) {
  const g0 = k => toDisp(PK[k], vals[k]);
  const err = [], warn = [];
  const has = (...ks) => ks.every(k => vals[k] != null);
  const g = k => g0(k) ?? NaN;   // NaN робить усі порівняння false
  const n = vals.cell_cnt;
  if (g('covp_rel') >= g('covp')) err.push('Банка: відновлення перезаряду має бути нижче порогу');
  if (g('cuvp_rel') <= g('cuvp')) err.push('Банка: відновлення перерозряду має бути вище порогу');
  if (g('povp_rel') >= g('povp')) err.push('Пакет: відновлення перезаряду має бути нижче порогу');
  if (g('puvp_rel') <= g('puvp')) err.push('Пакет: відновлення перерозряду має бути вище порогу');
  if (g('cuvp') >= g('covp')) err.push('Перерозряд банки вище перезаряду');
  if (n && has('povp', 'puvp', 'covp', 'cuvp', 'covp_rel')) {
    const pov = g('povp') / n, puv = g('puvp') / n;
    if (pov > g('covp') * 1.03) warn.push(`Пакетний перезаряд (${fmt(pov, 3)} V/банку) вищий за поріг банки — захист пакета не спрацює раніше`);
    if (pov < g('covp_rel') * 0.9) warn.push(`Пакетний перезаряд (${fmt(pov, 3)} V/банку) значно нижчий за поріг банки — батарея недозаряджатиметься`);
    if (puv < g('cuvp') * 0.9) warn.push(`Пакетний перерозряд (${fmt(puv, 3)} V/банку) нижчий за поріг банки`);
  }
  if (vals.cell_cnt != null && basic && vals.cell_cnt !== params.cell_cnt) warn.push(`Кількість банок ${params.cell_cnt} → ${vals.cell_cnt}: перевірте підключення balance-шлейфа`);
  if (g('chgot_rel') >= g('chgot') || g('dsgot_rel') >= g('dsgot')) err.push('Температура: відновлення перегріву має бути нижче порогу');
  if (g('chgut_rel') <= g('chgut') || g('dsgut_rel') <= g('dsgut')) err.push('Температура: відновлення холоду має бути вище порогу');
  const soc = ['cap_0', 'cap_20', 'cap_40', 'cap_60', 'cap_80', 'cap_100'].map(g);
  if (soc.every(x => !isNaN(x)) && soc.some((x, i) => i && x <= soc[i - 1])) err.push('Таблиця SoC має зростати від 0 % до 100 %');
  return { err, warn };
}

/* ---------- запис ---------- */
function dispStr(p, raw) {
  if (p.t === 'bits') return '0b' + raw.toString(2).padStart(8, '0');
  const v = toDisp(p, raw);
  return (p.t === 'int' ? String(v) : v.toFixed(p.t === 'temp' ? 1 : p.d)) + ' ' + (p.t === 'temp' ? '°C' : p.u || '');
}
async function writeFlow(changes, title, rawRegs) {
  // changes: [{label, reg, old, neu}]
  const vals = { ...params, ...edits };
  const v = rawRegs ? { err: [], warn: ['Відновлення сирих регістрів: перевірка значень обмежена'] } : validate(vals);
  const rows = changes.map(c => `<div><span>${c.label}</span><s class="mono">${c.oldS}</s><span>→</span><b class="mono">${c.newS}</b></div>`).join('');
  const html = `<p class="lbl" style="font-size:14px">Буде змінено ${changes.length}. Перед записом поточна конфігурація збережеться як резервна копія.</p>
    <div class="diff"><div><span>Параметр</span><span>Було</span><span></span><span>Стане</span></div>${rows}</div>
    ${v.err.map(x => `<div class="note bad">${x}</div>`).join('')}
    ${v.warn.map(x => `<div class="note warn">${x}</div>`).join('')}
    ${!v.err.length && !v.warn.length ? '<div class="note ok">Перевірка: значення узгоджені</div>' : ''}
    <label class="f" for="wPw">Пароль BMS (якщо запис закритий)</label><input class="f" id="wPw" value="${lastPw}" placeholder="порожньо" autocomplete="off">`;
  const ok = await sheetConfirm(title, html, 'Записати в EEPROM', !!v.err.length);
  if (!ok) return false;
  const pw = ($('wPw')?.value || '').trim();
  saveAutoBackup();
  try {
    await exclusive(async () => {
      await enterFactory(pw);
      try {
        for (const c of changes) {
          const r = await wr(c.reg, [c.neu >> 8, c.neu & 0xff]);
          if (r.status) throw new Error('BMS відхилила ' + c.label + ' (0x' + c.reg.toString(16) + ')');
        }
        const r = await exitSave(); if (r.status) throw new Error('збереження не підтверджено');
      } catch (e) { await exitNoSave(); throw e; }
    });
    lastPw = pw;
    toast('Записано. Перевіряю…');
    await sleep(800);
    edits = {};
    const before = changes;
    if (await readParams(pw)) {
      const bad = before.filter(c => (params._raw[c.reg] ?? null) !== c.neu);
      if (bad.length) await sheetConfirm('Розбіжність після запису', bad.map(c => `<div class="note bad">${c.label}: очікувалось ${c.newS}</div>`).join(''), 'Зрозуміло', false, true);
      else toast('Записано і звірено: ' + before.length + ' параметр(ів)');
    }
    return true;
  } catch (e) { toast(e.message, 4000); log('запис: ' + e.message); return false; }
}
$('bWrite').onclick = () => {
  if (driver === 'jk') return jkWriteFlow();
  const changes = Object.keys(edits).map(k => {
    const p = PK[k];
    return { label: (p.n || PK[P.find(x => x.pair === k)?.k]?.n + ' (відновл.)') + (GROUPS.find(g => g[0] === p.g) ? ' · ' + GROUPS.find(g => g[0] === p.g)[1].split(' (')[0] : ''), reg: p.r, old: params[k], neu: edits[k], oldS: dispStr(p, params[k]), newS: dispStr(p, edits[k]) };
  });
  writeFlow(changes, 'Записати в BMS?');
};

/* ---------- резервні копії ---------- */
function snapshot() { return { app: 'jbd-pwa', ver: VERSION, date: new Date().toISOString(), device: dev?.name || '', hw: devStrings.hw || '', regs: Object.fromEntries(Object.entries(params?._raw || {}).map(([r, v]) => ['0x' + (+r).toString(16), v])) }; }
function saveAutoBackup() {
  if (!params) return;
  try { localStorage.setItem('jbd_autobackup', JSON.stringify(snapshot())); } catch (_) {}
  renderAutoBk();
}
function renderAutoBk() {
  try { const s = JSON.parse(localStorage.getItem('jbd_autobackup') || 'null'); $('autoBk').innerHTML = s ? `Авто-копія: ${new Date(s.date).toLocaleString('uk-UA')} <button class="btn sm" id="bAutoDl">Завантажити</button>` : ''; } catch (_) {}
}
function download(name, text, type) {
  const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([text], { type })); a.download = name; a.click(); setTimeout(() => URL.revokeObjectURL(a.href), 2000);
}
$('autoBk').onclick = e => { if (e.target.id === 'bAutoDl') download('jbd-autobackup.json', localStorage.getItem('jbd_autobackup'), 'application/json'); };
$('bBackup').onclick = async () => {
  if (!params && !(await readParams(lastPw))) return;
  download(`jbd-${(dev?.name || 'bms').replace(/\W+/g, '_')}-${new Date().toISOString().slice(0, 10)}.json`, JSON.stringify(snapshot(), null, 1), 'application/json');
};
$('bRestore').onclick = () => $('fRestore').click();
$('fRestore').onchange = async e => {
  const f = e.target.files[0]; e.target.value = ''; if (!f) return;
  let j; try { j = JSON.parse(await f.text()); } catch (_) { toast('Не JSON'); return; }
  if (!j.regs) { toast('Невідомий формат файлу'); return; }
  if (!params && !(await readParams(lastPw))) return;
  const skip = new Set([0x15, 0x16, 0x17]); // дата, серійний, цикли
  const changes = [];
  for (const [rs, v] of Object.entries(j.regs)) {
    const reg = parseInt(rs, 16); if (skip.has(reg) || reg < 0x10 || reg > 0x3f) continue;
    const old = params._raw[reg]; if (old == null || old === v) continue;
    const p = P.find(x => x.r === reg);
    changes.push({ label: p ? (p.n || 'відновл. ' + reg.toString(16)) : 'рег. 0x' + reg.toString(16), reg, old, neu: v, oldS: p ? dispStr(p, old) : String(old), newS: p ? dispStr(p, v) : String(v) });
  }
  if (!changes.length) { toast('Конфігурація вже збігається з файлом'); return; }
  writeFlow(changes, 'Відновити з ' + f.name + '?', true);
};

/* ---------- лічильники, калібрування ---------- */
const CNT = ['Коротке замикання', 'Струм заряду', 'Струм розряду', 'Перезаряд банки', 'Перерозряд банки', 'Перегрів (заряд)', 'Холод (заряд)', 'Перегрів (розряд)', 'Холод (розряд)', 'Перезаряд пакета', 'Перерозряд пакета'];
$('bCnt').onclick = async () => {
  try {
    const d = await exclusive(async () => { await enterFactory(lastPw); try { const r = await rd(0xaa); if (r.status) throw new Error('не підтримується'); return r.data; } finally { await exitNoSave(); } });
    $('cntBox').innerHTML = CNT.map((n, i) => 2 * i + 1 < d.length ? `<div class="kv"><span>${n}</span><b class="mono">${u16(d, 2 * i)}</b></div>` : '').join('');
  } catch (e) { toast(e.message); }
};
$('bCalZero').onclick = async () => {
  if (!txCh) return toast('Спочатку підключіться');
  if (basic && Math.abs(basic.a) > 2) return toast('Струм занадто великий — від\'єднайте навантаження і заряд');
  const ok = await sheetConfirm('Калібрувати нуль струму?', '<div class="note warn">Переконайтеся, що через батарею не тече струм: від\'єднані навантаження і зарядний пристрій.</div>', 'Калібрувати');
  if (!ok) return;
  try {
    await exclusive(async () => { await enterFactory(lastPw); try { const r = await wr(0xad, [0, 0]); if (r.status) throw new Error('відхилено'); await exitSave(); } catch (e) { await exitNoSave(); throw e; } });
    toast('Нуль струму відкалібровано');
  } catch (e) { toast(e.message); }
};
$('bCalCell').onclick = async () => {
  if (!cellsMv.length) return toast('Немає даних банок');
  const html = '<p class="lbl" style="font-size:14px">Введіть виміряну мультиметром напругу тільки для тих банок, які треба виправити (V). Порожні не змінюються.</p>' +
    cellsMv.map((mv, i) => `<div class="pr single" style="padding:6px 0"><span class="nm">#${i + 1} <span class="unit">зараз ${(mv / 1000).toFixed(3)}</span></span><input class="mono" inputmode="decimal" data-cal="${i}" placeholder="—" style="width:100%;height:38px;border:1px solid #D5DCE2;border-radius:8px;padding:0 8px"></div>`).join('');
  const ok = await sheetConfirm('Калібрування напруги банок', html, 'Записати');
  if (!ok) return;
  const list = [...document.querySelectorAll('[data-cal]')].map(el => ({ i: +el.dataset.cal, v: parseFloat(el.value.replace(',', '.')) })).filter(x => !isNaN(x.v) && x.v > 1 && x.v < 5);
  if (!list.length) return;
  try {
    await exclusive(async () => {
      await enterFactory(lastPw);
      try { for (const x of list) { const mv = Math.round(x.v * 1000); const r = await wr(0xb0 + x.i, [mv >> 8, mv & 0xff]); if (r.status) throw new Error('банка #' + (x.i + 1) + ' відхилена'); } await exitSave(); }
      catch (e) { await exitNoSave(); throw e; }
    });
    toast('Відкалібровано: ' + list.length);
  } catch (e) { toast(e.message); }
};

/* ---------- CSV ---------- */
$('swCsv').onclick = () => { csvOn = !csvOn; $('swCsv').classList.toggle('on', csvOn); };
$('bCsv').onclick = () => {
  if (!csvRows.length) return toast('Немає записаних даних');
  const nC = Math.max(...csvRows.map(r => r.length)) - 5 - (basic?.temps.length || 0);
  const head = ['time', 'V', 'A', 'SoC', 'Ah', ...(basic?.temps || []).map((_, i) => 'T' + i), ...Array.from({ length: nC }, (_, i) => 'cell' + (i + 1))];
  download('jbd-log-' + new Date().toISOString().slice(0, 16).replace(/:/g, '') + '.csv', [head, ...csvRows].map(r => r.join(';')).join('\n'), 'text/csv');
};

/* ---------- пристрій ---------- */
function renderDevInfo() {
  if (driver === 'daly') {
    const rows = [['Bluetooth-ім\'я', dev?.name], ['Тип', 'Daly Smart BMS (D2)'], ['Прошивка', dalyInfo?.sw], ['Апаратна версія', dalyInfo?.hw], ['Банок', basic?.cells], ['Цикли', basic?.cycles]]
      .filter(r => r[1] != null && r[1] !== '');
    $('devInfo').innerHTML = rows.map(r => `<div class="kv"><span>${r[0]}</span><span>${String(r[1]).replace(/</g, '&lt;')}</span></div>`).join('');
    $('felRaw').textContent = dalyRaw ? hex(dalyRaw) : '—';
    return;
  }
  if (driver === 'ffe0') {
    $('devInfo').innerHTML = `<div class="kv"><span>Bluetooth-ім'я</span><span>${dev?.name || '—'}</span></div><div class="kv"><span>Тип</span><span>визначається…</span></div>`;
    return;
  }
  if (driver === 'jk') {
    const i = jkInfo || {};
    $('devInfo').innerHTML = [['Bluetooth-ім\'я', dev?.name], ['Тип', 'JK BMS'], ['Модель', i.model], ['Апаратна версія', i.hw], ['Прошивка', i.sw], ['Ім\'я в BMS', i.name], ['Серійний номер', i.sn], ['Протокол', jkOffs ? 'JK02_24S' : 'JK02_32S'], ['SOH', basic?.soh != null ? basic.soh + ' %' : null], ['Цикли (лічильник BMS)', basic?.cycles], ['Прокачано через батарею', basic?.cycleAh != null ? fmt(basic.cycleAh, 1) + ' Ah' : null], ['Еквівалент повних циклів', basic?.cycleAh != null && basic?.nominal ? fmt(basic.cycleAh / basic.nominal, 2) : null]]
      .filter(r => r[1] != null && r[1] !== '').map(r => `<div class="kv"><span>${r[0]}</span><span>${String(r[1]).replace(/</g, '&lt;')}</span></div>`).join('');
    $('felRaw').textContent = (jkRaw ? 'Дані (0x02):\n' + hex(jkRaw) : '—') + (jkSettings ? '\n\nНалаштування (0x01):\n' + hex(jkSettings) : '');
    return;
  }
  if (driver === 'generic') {
    $('devInfo').innerHTML = `<div class="kv"><span>Bluetooth-ім'я</span><span>${dev?.name || '—'}</span></div><div class="kv"><span>Тип</span><span>невідомий (універсальний режим)</span></div><div class="kv"><span>Сервісів знайдено</span><span>${new Set(genChars.map(g => g.svc)).size}</span></div>`;
    return;
  }
  if (driver === 'atorch') {
    $('devInfo').innerHTML = [['Bluetooth-ім\'я', dev?.name], ['Тип', atLast ? 'Atorch DL24 (електронне навантаження)' : 'визначається… (є сервіс FFE0, чекаю пакет Atorch)'], ['Код типу в пакеті', atLast ? '0x' + (atDev || 0).toString(16).padStart(2, '0') + (atDev === 2 ? ' (DC)' : '') : '—']]
      .map(r => `<div class="kv"><span>${r[0]}</span><span>${r[1] ?? '—'}</span></div>`).join('');
    $('felRaw').textContent = atRawHex || '—';
    return;
  }
  if (driver === 'fel') {
    const f = felInfo || {};
    const r = felRaw || {};
    const hx = v => v == null ? null : '0x' + Number(v).toString(16).toUpperCase().padStart(4, '0') + ' (' + v + ')';
    const d = r.date && /^\d{14}$/.test(r.date) ? `${r.date.slice(0, 4)}-${r.date.slice(4, 6)}-${r.date.slice(6, 8)} ${r.date.slice(8, 10)}:${r.date.slice(10, 12)}:${r.date.slice(12, 14)}` : r.date;
    const rows = [['Bluetooth-ім\'я', dev?.name], ['Тип BMS', 'Felicity Solar'], ['Тип / підтип', (f.Type ?? r.Type) != null ? (f.Type ?? r.Type) + ' / ' + (r.SubType ?? '—') : null], ['Серійний номер', f.DevSN || r.DevSN], ['Прошивка BMS', f.M1SwVer], ['Версія', f.version],
      ['SOH', basic?.soh != null ? fmt(basic.soh, 1) + ' %' : null], ['Стан BMS (Bstate)', hx(r.Bstate)], ['Стан (Estate)', hx(r.Estate)], ['Годинник BMS', d], ['Цикли', basic?.cycles !== '—' ? basic?.cycles : null]]
      .filter(r => r[1] != null && r[1] !== '');
    $('devInfo').innerHTML = rows.map(r => `<div class="kv"><span>${r[0]}</span><span>${String(r[1]).replace(/</g, '&lt;')}</span></div>`).join('');
    renderFelRaw();
    return;
  }
  const rows = [['Bluetooth-ім\'я', dev?.name], ['Апаратна версія', devStrings.hw], ['Виробник', devStrings.mfg], ['Модель', devStrings.model], ['Штрихкод', devStrings.barcode],
    ['Прошивка', basic ? '0x' + basic.ver.toString(16) + ' (' + basic.ver + ')' : null],
    ['Дата виробництва', basic ? `${((basic.date >> 9) + 2000)}-${String((basic.date >> 5) & 15).padStart(2, '0')}-${String(basic.date & 31).padStart(2, '0')}` : null],
    ['Цикли', basic?.cycles]].filter(r => r[1] != null && r[1] !== '');
  $('devInfo').innerHTML = rows.length ? rows.map(r => `<div class="kv"><span>${r[0]}</span><span>${r[1]}</span></div>`).join('') : '<div class="kv"><span>Не підключено</span><span></span></div>';
}

/* ---------- sheets ---------- */
function sheetConfirm(title, html, okLabel, okDisabled = false, single = false) {
  return new Promise(res => {
    $('sheetC').innerHTML = `<h2>${title}</h2>${html}<div class="row2">${single ? '' : '<button class="btn" id="sNo">Скасувати</button>'}<button class="btn amb" id="sYes" ${okDisabled ? 'disabled' : ''}>${okLabel}</button></div>`;
    $('sheetBg').classList.add('show');
    const done = v => { $('sheetBg').classList.remove('show'); res(v); };
    $('sYes').onclick = () => done(true);
    if (!single) $('sNo').onclick = () => done(false);
    $('sheetBg').onclick = e => { if (e.target === $('sheetBg')) done(false); };
  });
}
async function sheetPassword(msg) {
  const ok = await sheetConfirm('Доступ до налаштувань', `<div class="note bad">${msg}</div><label class="f" for="pPw">Пароль BMS</label><input class="f" id="pPw" placeholder="напр. 000000" autocomplete="off">`, 'Спробувати');
  return ok ? ($('pPw')?.value || '').trim() : null;
}

/* ---------- вкладки ---------- */
document.querySelector('.tabs').onclick = e => {
  const b = e.target.closest('button'); if (!b) return;
  document.querySelectorAll('.tabs button').forEach(x => x.classList.toggle('act', x === b));
  document.querySelectorAll('.view').forEach(v => v.classList.toggle('act', v.id === 'v-' + b.dataset.v));
  updateDirtyBar();
  if (b.dataset.v === 'mon') renderMon();
  if (b.dataset.v === 'par' && driver === 'jk') renderJkParams();
  if (b.dataset.v === 'srv') { renderDevInfo(); renderAutoBk(); }
  window.scrollTo(0, 0);
};
window.addEventListener('beforeunload', e => { if (Object.keys(edits).length) { e.preventDefault(); e.returnValue = ''; } });
window.addEventListener('resize', () => renderMon());

/* ---------- PWA ---------- */
if ('serviceWorker' in navigator) navigator.serviceWorker.register('sw.js').catch(e => log('SW: ' + e.message));
renderAutoBk(); renderDevInfo();
$('bFelCopy').onclick = async () => { try { await navigator.clipboard.writeText(driver === 'atorch' ? atRawHex : (driver === 'jk' || driver === 'daly') ? $('felRaw').textContent : JSON.stringify(felRaw, null, 1)); toast('Скопійовано'); } catch (_) { toast('Не вдалося скопіювати'); } };
$('atCard').addEventListener('click', async e => {
  const k = e.target.closest('[data-at]')?.dataset.at; if (!k) return;
  if (k === 'resetAll' && !(await sheetConfirm('Скинути всі лічильники?', '<p>Ah, Wh і час роботи на навантаженні буде обнулено.</p>', 'Скинути'))) return;
  try { await atCmd(AT_CMDS[k]); setTimeout(() => renderMon(), 1200); } catch (er) { toast(er.message); }
});

/* ---------- універсальний режим: UI ---------- */
$('genSend').onclick = genSend;
$('genCopy').onclick = async () => { try { await navigator.clipboard.writeText(genMap.join('\n')); toast('Скопійовано'); } catch (_) { toast('Не вдалося скопіювати'); } };
try { $('genUuids').value = localStorage.getItem('jbd_extra_uuids') || ''; } catch (_) {}
$('genUuidsSave').onclick = () => { try { localStorage.setItem('jbd_extra_uuids', $('genUuids').value.trim()); toast('Збережено. Діє з наступного підключення'); } catch (_) { toast('Не вдалося зберегти'); } };
$('bLogCopy').onclick = async () => { try { await navigator.clipboard.writeText(logLines.join('\n')); toast('Журнал скопійовано'); } catch (_) { toast('Не вдалося скопіювати'); } };

/* ---------- захист від змішаних версій (стара index.html + новий app.js) ---------- */
async function hardReload() {
  try { sessionStorage.setItem('jbd_reloaded', VERSION); } catch (_) {}
  try { for (const k of await caches.keys()) await caches.delete(k); } catch (_) {}
  location.reload();
}
(() => {
  const pageVer = document.querySelector('meta[name="app-ver"]')?.content;
  let done = null; try { done = sessionStorage.getItem('jbd_reloaded'); } catch (_) {}
  if (pageVer !== VERSION && done !== VERSION) { log('версії не збігаються: сторінка ' + (pageVer || '?') + ', код ' + VERSION + ' — оновлюю'); hardReload(); }
})();

/* ---------- звільняти Bluetooth при закритті/згортанні сторінки ---------- */
function releaseBt() {
  try { if (dev?.gatt?.connected) { manualDisc = true; cancelConn = true; stopPoll(); dev.gatt.disconnect(); } } catch (_) {}
}
window.addEventListener('pagehide', releaseBt);
window.addEventListener('beforeunload', releaseBt);

$('known').addEventListener('click', e => { const i = e.target.closest('[data-known]')?.dataset.known; if (i != null && knownDevs[+i]) connectKnown(knownDevs[+i]); });
renderKnown();

try { $('genWide').checked = localStorage.getItem('jbd_wide_probe') === '1'; } catch (_) {}
$('genWide').onchange = e => { try { localStorage.setItem('jbd_wide_probe', e.target.checked ? '1' : '0'); } catch (_) {} toast(e.target.checked ? 'Розширений список увімкнено — діє з наступного підключення' : 'Розширений список вимкнено'); };

/* ---------- JK: паролі (розділ у «Сервіс») ---------- */
const jkPwKey = () => 'jbd_jkpw_' + (dev?.name || 'jk');
function jkPwInit() {
  if (driver !== 'jk') { $('jkPwCard').style.display = 'none'; return; }
  $('jkPwCard').style.display = '';
  const c = jkInfo?.connPw, p = jkInfo?.setPw;
  const row = (lbl, v) => `<div class="kv"><span>${lbl}</span><b class="mono" style="user-select:all">${v ? v.replace(/</g, '&lt;') : '—'}</b></div>`;
  $('jkPwRead').innerHTML = (c != null || p != null)
    ? '<div class="lbl" style="margin-bottom:4px">Прочитано з BMS:</div>' + row('Пароль на підключення', c) + row('Пароль на налаштування', p) + '<div class="lbl" style="margin-top:4px">Притисніть значення, щоб виділити й скопіювати.</div>'
    : '<div class="lbl">Паролі зчитуються з кадру пристрою після підключення…</div>';
  // підставляємо прочитаний пароль на налаштування, якщо поле порожнє і нема збереженого
  let saved = ''; try { saved = localStorage.getItem(jkPwKey()) || ''; } catch (_) {}
  $('jkPw').value = saved || p || '';
}
function jkPwOut(t) { const el = $('jkPwOut'); el.style.display = ''; el.textContent = t; }
$('jkPwSave').onclick = () => {
  try { localStorage.setItem(jkPwKey(), $('jkPw').value.trim()); toast('Пароль збережено на цьому телефоні'); } catch (_) { toast('Не вдалося зберегти'); }
};
// експериментальна авторизація: надсилаємо пароль ASCII у поле пароля/керування (рег. 0xC9 за відкритими розборами)
async function jkAuth(quiet) {
  const pw = ($('jkPw').value || '').trim();
  if (!pw) { if (!quiet) toast('Введіть пароль'); return; }
  const bytes = Array.from(new TextEncoder().encode(pw));
  await jkSend(0xC9, bytes);
  if (!quiet) { log('JK: надіслано пароль на рег. 0xC9 (' + pw.length + ' символів) — дивіться відповідь у «Протокол обміну»'); toast('Пароль надіслано (експеримент)'); }
}
$('jkPwAuth').onclick = () => jkAuth(false).catch(e => toast(e.message));
// пошук пароля у кадрах пристрою (0x03) і налаштувань (0x01)
$('jkPwFind').onclick = async () => {
  jkPwOut('Читаю кадри…');
  try { await jkRequestSettings(); } catch (_) {}
  const pw = ($('jkPw').value || '').trim();
  const lines = [];
  const dump = (name, f) => {
    if (!f) { lines.push(name + ': немає кадру'); return; }
    const arr = Array.from(f);
    lines.push('── ' + name + ' (' + arr.length + ' байт) ──');
    lines.push('ASCII: ' + asciiOf(arr));
    if (pw) {
      const a = Array.from(new TextEncoder().encode(pw));
      let at = -1;
      for (let i = 0; i + a.length <= arr.length; i++) if (a.every((b, j) => arr[i + j] === b)) { at = i; break; }
      lines.push(a.length && at >= 0 ? '✓ введений пароль знайдено у зсуві ' + at : '✗ введеного пароля в цьому кадрі немає');
    }
  };
  dump('Кадр пристрою 0x03', jkInfoRaw);
  dump('Кадр налаштувань 0x01', jkSettings);
  if (!pw) lines.push('Підказка: введіть відомий пароль вище і натисніть знову — застосунок покаже, де він лежить у кадрі.');
  jkPwOut(lines.join('\n'));
  log('JK: пошук пароля в кадрах виконано');
};
