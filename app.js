'use strict';
/* JBD BMS PWA — Web Bluetooth, протокол JBD (Xiaoxiang) */
const VERSION = '1.0.0';
const SVC = 0xff00, RX = 0xff01, TX = 0xff02;
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
    if (p[total - 1] !== 0x77) { log('битий пакет ' + hex(p)); continue; }
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
async function connect() {
  if (!navigator.bluetooth) { toast('Web Bluetooth недоступний. Відкрийте в Chrome на Android.', 4000); return; }
  try {
    dev = await navigator.bluetooth.requestDevice({ acceptAllDevices: true, optionalServices: [SVC] });
    dev.addEventListener('gattserverdisconnected', onDisc);
    setConn('conn');
    await gattConnect();
  } catch (e) { setConn('off'); log('помилка: ' + e.message); if (e.name !== 'NotFoundError') toast(e.message); }
}
async function gattConnect() {
  const srv = await (await dev.gatt.connect()).getPrimaryService(SVC);
  rxCh = await srv.getCharacteristic(RX);
  txCh = await srv.getCharacteristic(TX);
  rxCh.addEventListener('characteristicvaluechanged', onNotify);
  await rxCh.startNotifications();
  buf = [];
  $('dName').textContent = dev.name || 'JBD BMS';
  setConn('on');
  log('підключено: ' + (dev.name || dev.id));
  await exclusive(async () => {
    try { const r = await rd(0x05); if (!r.status) devStrings.hw = new TextDecoder().decode(new Uint8Array(r.data)).replace(/\0/g, ''); } catch (_) {}
  });
  renderDevInfo();
  startPoll();
}
let manualDisc = false;
function onDisc() {
  txCh = rxCh = null; stopPoll(); setConn('off');
  if (waiter) { clearTimeout(waiter.t); waiter = null; }
  if (!manualDisc && dev) { log('зв\'язок втрачено, перепідключення…'); reconnect(); }
  manualDisc = false;
}
async function reconnect() {
  for (let i = 0; i < 5 && dev && !txCh; i++) {
    setConn('conn'); await sleep(1500 * (i + 1));
    try { await gattConnect(); return; } catch (e) { log('спроба ' + (i + 1) + ': ' + e.message); }
  }
  setConn('off');
}
function setConn(s) {
  $('cDot').className = 'dot' + (s === 'on' ? ' on' : '');
  $('cTxt').textContent = s === 'on' ? 'Підключено' : s === 'conn' ? 'Підключення…' : 'Підключити';
  $('dSub').textContent = s === 'on' ? (dev?.id?.slice(0, 17) || '') + (devStrings.hw ? ' · ' + devStrings.hw : '') : 'не підключено';
  $('swChg').disabled = $('swDsg').disabled = s !== 'on';
}
$('bConn').onclick = async () => {
  if (txCh) {
    const ok = await sheetConfirm('Відключитися?', '<p>З\'єднання з BMS буде закрито.</p>', 'Відключити');
    if (ok) { manualDisc = true; dev.gatt.disconnect(); }
  } else connect();
};

/* ---------- опитування ---------- */
function startPoll() { stopPoll(); poll(); pollTimer = setInterval(poll, pollMs); }
function stopPoll() { clearInterval(pollTimer); pollTimer = null; }
$('selPoll').onchange = e => { pollMs = +e.target.value; if (pollTimer) startPoll(); };
async function poll() {
  if (!txCh || busy) return;
  try {
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
      if (csvOn) { csvRows.push([new Date(now).toISOString(), basic.v, basic.a, basic.soc, basic.remain, ...basic.temps, ...cellsMv.map(x => x / 1000)]); $('csvN').textContent = '(' + csvRows.length + ')'; }
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
const PROT = ['Перезаряд банки', 'Переразряд банки', 'Перезаряд пакета', 'Переразряд пакета', 'Перегрів при заряді', 'Холод при заряді', 'Перегрів при розряді', 'Холод при розряді', 'Струм заряду', 'Струм розряду', 'Коротке замикання', 'Помилка AFE', 'Програмне блокування MOS'];

/* ---------- рендер моніторингу ---------- */
function renderMon() {
  const b = basic; if (!b) return;
  $('mV').textContent = fmt(b.v, 2);
  $('mA').textContent = fmt(b.a, 2) + ' A';
  $('mW').textContent = fmt(b.v * b.a, 0) + ' W';
  $('mSoc').textContent = b.soc;
  $('mCap').textContent = fmt(b.remain, 1) + ' / ' + fmt(b.nominal, 0) + ' Ah';
  const col = b.soc < 15 ? '#F0A030' : b.soc < 40 ? '#E8C547' : '#34C46E';
  $('gauge').style.background = `conic-gradient(${col} 0 ${b.soc}%, #2A3138 ${b.soc}% 100%)`;
  const st = b.a > 0.05 ? 'Заряд' : b.a < -0.05 ? 'Розряд' : 'Простій';
  let eta = '';
  if (b.a < -0.05) eta = ' · ~' + fmt(b.remain / -b.a, 1) + ' год';
  if (b.a > 0.05) eta = ' · до повного ~' + fmt((b.nominal - b.remain) / b.a, 1) + ' год';
  $('mState').textContent = st + eta + ' · ' + b.cells + 'S · ' + b.cycles + ' циклів';
  const chg = !!(b.fet & 1), dsg = !!(b.fet & 2);
  $('swChg').classList.toggle('on', chg); $('mChgT').textContent = chg ? 'Увімкнено' : 'Вимкнено';
  $('swDsg').classList.toggle('on', dsg); $('mDsgT').textContent = dsg ? 'Увімкнено' : 'Вимкнено';

  const act = PROT.filter((_, i) => b.prot & (1 << i));
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
    $('cells').innerHTML = cellsMv.map((mv, i) => {
      let c = 'cell';
      if (mv < 500) c += ' zero'; else if (mv === max && max !== min) c += ' max'; else if (mv === min && max !== min) c += ' min';
      if (b.bal & (1 << i)) c += ' bal';
      const pct = Math.max(0, Math.min(100, (mv - lo) / (hi - lo) * 100));
      return `<div class="${c}"><span class="lbl">#${i + 1}</span><b class="mono">${(mv / 1000).toFixed(3)}</b><div class="bar"><i style="width:${pct}%"></i></div></div>`;
    }).join('');
    $('cLegend').innerHTML = `<span>макс ${fmt(max / 1000, 3)}</span><span>мін ${fmt(min / 1000, 3)}</span><span>сер ${fmt(avg / 1000, 3)} V</span>` + (b.bal ? '<span style="color:#146C3B">● балансування</span>' : '');
  }
  // температури
  $('temps').innerHTML = b.temps.map((t, i) => `<div class="card"><div class="lbl">${i === 0 && b.temps.length > 1 ? 'MOS' : 'T' + (b.temps.length > 1 ? i : i + 1)}</div><div class="val">${fmt(t, 1)} °C</div></div>`).join('');
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
  { k: 'cuvp', r: 0x26, g: 'cell', n: 'Переразряд', pair: 'cuvp_rel', t: 'v', s: 0.001, u: 'V', d: 3, min: 1.5, max: 4 },
  { k: 'cuvp_rel', r: 0x27, g: 'cell', t: 'v', s: 0.001, u: 'V', d: 3, min: 1.5, max: 4, sub: 1 },
  // напруга пакета
  { k: 'povp', r: 0x20, g: 'pack', n: 'Перезаряд', pair: 'povp_rel', t: 'v', s: 0.01, u: 'V', d: 2, min: 3, max: 150 },
  { k: 'povp_rel', r: 0x21, g: 'pack', t: 'v', s: 0.01, u: 'V', d: 2, min: 3, max: 150, sub: 1 },
  { k: 'puvp', r: 0x22, g: 'pack', n: 'Переразряд', pair: 'puvp_rel', t: 'v', s: 0.01, u: 'V', d: 2, min: 3, max: 150 },
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
  { k: 'func', r: 0x2d, g: 'func', n: 'Функції', t: 'bits', bits: ['Вимикач (switch)', 'Детект навантаження', 'Балансування', 'Баланс лише при заряді', 'LED індикатор', 'LED: 5 сегментів'] },
  { k: 'ntc', r: 0x2e, g: 'func', n: 'Датчики NTC', t: 'bits', bits: ['NTC1', 'NTC2', 'NTC3', 'NTC4', 'NTC5', 'NTC6', 'NTC7', 'NTC8'] },
  { k: 'fet_time', r: 0x30, g: 'func', n: 'Затримка MOS', t: 'int', u: 'с', min: 0, max: 65535 },
  { k: 'led_time', r: 0x31, g: 'func', n: 'Час LED', t: 'int', u: 'с', min: 0, max: 65535 },
  // апаратні
  { k: 'covp_hw', r: 0x36, g: 'hw', n: 'Апаратний перезаряд банки', t: 'v', s: 0.001, u: 'V', d: 3, min: 2, max: 5 },
  { k: 'cuvp_hw', r: 0x37, g: 'hw', n: 'Апаратний переразряд банки', t: 'v', s: 0.001, u: 'V', d: 3, min: 1, max: 4 },
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
      body += `<div class="pr single"><span class="nm">Хімія (пресет порогів)</span><select id="selChem">${['—', 'NMC', 'LFP', 'LTO'].map(c => `<option ${c === chem ? 'selected' : ''}>${c}</option>`).join('')}</select></div>`;
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
    toast('Пресет ' + e.target.value + ' підставлено. Перевірте пороги пакета.');
    renderParams(); return;
  }
  const k = e.target.dataset.k; if (!k) return;
  const p = PK[k], v = parseFloat(String(e.target.value).replace(',', '.'));
  if (isNaN(v) || v < p.min || v > p.max) { e.target.classList.add('err'); toast(`${p.n || k}: допустимо ${p.min}…${p.max}`); return; }
  setEdit(k, toRaw(p, v)); renderParams();
});
function updateDirtyBar() {
  const n = Object.keys(edits).length;
  $('dBar').classList.toggle('show', n > 0 && document.querySelector('#v-par.act') != null);
  $('dTxt').textContent = n + ' ' + (n === 1 ? 'незбережена зміна' : n < 5 ? 'незбережені зміни' : 'незбережених змін');
}
$('bReset').onclick = () => { edits = {}; renderParams(); };

/* ---------- перевірка ---------- */
function validate(vals) {
  const g0 = k => toDisp(PK[k], vals[k]);
  const err = [], warn = [];
  const has = (...ks) => ks.every(k => vals[k] != null);
  const g = k => g0(k) ?? NaN;   // NaN робить усі порівняння false
  const n = vals.cell_cnt;
  if (g('covp_rel') >= g('covp')) err.push('Банка: відновлення перезаряду має бути нижче порогу');
  if (g('cuvp_rel') <= g('cuvp')) err.push('Банка: відновлення переразряду має бути вище порогу');
  if (g('povp_rel') >= g('povp')) err.push('Пакет: відновлення перезаряду має бути нижче порогу');
  if (g('puvp_rel') <= g('puvp')) err.push('Пакет: відновлення переразряду має бути вище порогу');
  if (g('cuvp') >= g('covp')) err.push('Переразряд банки вище перезаряду');
  if (n && has('povp', 'puvp', 'covp', 'cuvp', 'covp_rel')) {
    const pov = g('povp') / n, puv = g('puvp') / n;
    if (pov > g('covp') * 1.03) warn.push(`Пакетний перезаряд (${fmt(pov, 3)} V/банку) вище банкового — захист пакета не спрацює раніше`);
    if (pov < g('covp_rel') * 0.9) warn.push(`Пакетний перезаряд (${fmt(pov, 3)} V/банку) суттєво нижче банкового — недозаряд`);
    if (puv < g('cuvp') * 0.9) warn.push(`Пакетний переразряд (${fmt(puv, 3)} V/банку) нижче банкового`);
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
const CNT = ['Коротке замикання', 'Струм заряду', 'Струм розряду', 'Перезаряд банки', 'Переразряд банки', 'Перегрів (заряд)', 'Холод (заряд)', 'Перегрів (розряд)', 'Холод (розряд)', 'Перезаряд пакета', 'Переразряд пакета'];
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
  if (b.dataset.v === 'srv') { renderDevInfo(); renderAutoBk(); }
  window.scrollTo(0, 0);
};
window.addEventListener('beforeunload', e => { if (Object.keys(edits).length) { e.preventDefault(); e.returnValue = ''; } });
window.addEventListener('resize', () => renderMon());

/* ---------- PWA ---------- */
if ('serviceWorker' in navigator) navigator.serviceWorker.register('sw.js').catch(e => log('SW: ' + e.message));
renderAutoBk(); renderDevInfo();
