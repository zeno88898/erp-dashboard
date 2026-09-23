'use strict';
/**
 * 库存看板生成器 v2（对接海外仓 + 账号密码 + 智能图表）
 * 读取 db.json（海外仓API同步的真实数据） -> 跑备货引擎 -> 生成自包含 HTML
 * 功能:
 *  - 登录保护: 账号+密码(SHA-256哈希比对, 轻量防护)
 *  - 对接状态: 显示海外仓系统/接口/同步时间, 明确数据来源
 *  - 智能图表: 预警等级环形图 / 出库TopN饼图 / 日销量走势(实际)+需求预测(统计模型, 按日期) / 月度出库趋势折线+线性回归预测
 *             / SKU点击展开: 近N天实际日销量折线+模型预测日销外推曲线
 *  - 备货数据: 预测日销D(WMA加权)/安全库存SS(Z×σ×√L)/可售天数/再订货点/目标库存/建议补货量/最晚下单日期
 */
const path = require('path');
const fs = require('fs');
const crypto = require('crypto');
const restock = require('./restock');

const DAY_MS = 86400000;
const CHART_JS_PATH = path.join(__dirname, '..', 'vendor', 'chart.umd.js');

function dstr(d) {
  return d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0');
}
function addDays(base, n) {
  return dstr(new Date(base.getTime() + n * DAY_MS));
}
function fmt(n, digits) {
  if (n === null || n === undefined || isNaN(n)) return '—';
  return Number(n).toLocaleString('zh-CN', { maximumFractionDigits: digits === undefined ? 0 : digits });
}
function esc(s) {
  return String(s == null ? '' : s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

/** 最小二乘线性回归: y = a + b*x, 返回 {a, b}; 样本<2返回null */
function linreg(values) {
  const n = values.length;
  if (n < 2) return null;
  let sx = 0, sy = 0, sxy = 0, sxx = 0;
  values.forEach((y, i) => { sx += i; sy += y; sxy += i * y; sxx += i * i; });
  const denom = n * sxx - sx * sx;
  if (!denom) return null;
  const b = (n * sxy - sx * sy) / denom;
  const a = (sy - b * sx) / n;
  return { a, b };
}

/** salesDaily -> 全历史月度出库序列 [{m:'2026-07', qty}, ...] */
function monthlySeries(salesDaily) {
  const map = {};
  for (const byDay of Object.values(salesDaily)) {
    for (const [date, qty] of Object.entries(byDay)) {
      const m = date.slice(0, 7);
      if (/^\d{4}-\d{2}$/.test(m)) map[m] = (map[m] || 0) + qty;
    }
  }
  return Object.keys(map).sort().map(m => ({ m, qty: map[m] }));
}

/* ==================== 多仓库备货视图（美国富皇美运 / 德国盘古 同口径） ====================
 * buildRestockView 把「store 形态」的数据源换算成备货看板的完整视图(与美国仓口径一致):
 *   storeLike.data = { inventory:[{sku,qty}], inTransit:{sku:qty}, salesDaily:{sku:{'YYYY-MM-DD':qty}}, skuMeta:{sku:{name}} }
 * 返回 { rows, stats, charts, paramObj, flowCount } —— 字段与美国仓内联逻辑完全同构, 前端可直接切换数据集重绘。
 */
function buildRestockView(storeLike, policy, opts) {
  policy = policy || {}; opts = opts || {};
  const now = opts.now || new Date();
  const chartDays = opts.chartDays || 60;
  const topN = opts.topN || 10;
  const lead = (policy.productionDays || 30) + (policy.shippingDays || 40);
  const safety = policy.safetyStockDays || 15;
  const cycle = policy.restockCycleDays || 30;
  const ropDays = lead + safety;
  const targetDays = cycle + lead + safety;
  const slv = policy.serviceLevel === undefined || policy.serviceLevel === null ? 0.95 : Number(policy.serviceLevel);
  const pz = restock.zScore(slv);
  const maxSd = policy.maxSafetyDays === undefined || policy.maxSafetyDays === null ? 30 : policy.maxSafetyDays;
  const _dw = policy.demandWeights || {};
  const _dwn = { d7: Math.round((Number(_dw.d7) || 0.4) * 100), d30: Math.round((Number(_dw.d30) || 0.3) * 100), d60: Math.round((Number(_dw.d60) || 0.3) * 100) };

  const salesDaily = storeLike.data.salesDaily || {};
  const skuMeta = storeLike.data.skuMeta || {};

  const rows = restock.evaluateAll(storeLike, policy).map(e => {
    let lastOrderDay = null, lastOrderInDays = null, stockoutDay = null, arriveDay = null;
    if (e.rate > 0) {
      const coverF = e.position / e.rate;
      stockoutDay = addDays(now, Math.floor(coverF));
      const ropD = e.ropDays || ropDays;
      const slack = Math.ceil(e.coverDays - ropD);
      lastOrderInDays = slack;
      lastOrderDay = addDays(now, slack);
      arriveDay = addDays(now, lead);
    }
    const meta = skuMeta[e.sku];
    return Object.assign({}, e, {
      name: (meta && meta.name) ? meta.name : '',
      lastOrderInDays, lastOrderDay, stockoutDay, arriveDay
    });
  });

  const stats = {
    total: rows.length,
    withStock: rows.filter(r => r.position > 0).length,
    red: rows.filter(r => r.level === 'red').length,
    orange: rows.filter(r => r.level === 'orange').length,
    yellow: rows.filter(r => r.level === 'yellow').length,
    toOrder: rows.filter(r => r.suggest > 0).length,
    totalQty: rows.reduce((s, r) => s + r.position, 0)
  };

  // 近 chartDays 天各 SKU 出库量
  const dateKeys = [];
  for (let i = chartDays - 1; i >= 0; i--) dateKeys.push(dstr(new Date(now.getTime() - i * DAY_MS)));
  const recentBySku = {};
  for (const [sku, byDay] of Object.entries(salesDaily)) {
    let sum = 0;
    for (const d of dateKeys) sum += byDay[d] || 0;
    if (sum > 0) recentBySku[sku] = sum;
  }
  // 月度出库趋势 + 线性回归预测(未来3个月)
  const monthly = monthlySeries(salesDaily);
  let monthlyReg = null;
  if (monthly.length >= 2) {
    const r = linreg(monthly.map(x => x.qty));
    if (r) {
      const lastM = monthly[monthly.length - 1].m;
      const forecast = [];
      for (let i = 1; i <= 3; i++) {
        const t = new Date(lastM + '-01');
        t.setMonth(t.getMonth() + i);
        const m = t.getFullYear() + '-' + String(t.getMonth() + 1).padStart(2, '0');
        forecast.push({ m, qty: Math.max(0, Math.round(r.a + r.b * (monthly.length - 1 + i))) });
      }
      monthlyReg = { slope: r.b, intercept: r.a, forecast };
    }
  }
  const skuSeries = {};
  for (const sku of Object.keys(recentBySku)) {
    const byDay = salesDaily[sku];
    const arr = dateKeys.map(d => byDay[d] || 0);
    if (arr.some(v => v > 0)) skuSeries[sku] = arr;
  }
  const skuReg = {};
  for (const [sku, arr] of Object.entries(skuSeries)) {
    const r = linreg(arr);
    if (r) {
      const fc = [];
      for (let i = 1; i <= 7; i++) fc.push(Math.max(0, Math.round(r.a + r.b * (arr.length - 1 + i))));
      skuReg[sku] = { slope: r.b, forecast: fc };
    }
  }
  const skuMonthly = {};
  for (const [sku, byDay] of Object.entries(salesDaily)) {
    const map = {};
    for (const [date, qty] of Object.entries(byDay)) {
      const m = date.slice(0, 7);
      if (/^\d{4}-\d{2}$/.test(m)) map[m] = (map[m] || 0) + qty;
    }
    const arr = Object.keys(map).sort().map(m => ({ m, qty: map[m] }));
    if (arr.length) skuMonthly[sku] = arr;
  }
  const nameOf = sku => (skuMeta[sku] && skuMeta[sku].name) || '';
  let top10 = Object.entries(recentBySku).sort((a, b) => b[1] - a[1]).slice(0, topN).map(([sku, qty]) => ({ sku, qty, name: nameOf(sku) }));
  let topByHistory = false;
  if (!top10.length) {
    const hist = {};
    for (const [sku, byDay] of Object.entries(salesDaily)) {
      let sum = 0;
      for (const q of Object.values(byDay)) sum += q;
      if (sum > 0) hist[sku] = sum;
    }
    top10 = Object.entries(hist).sort((a, b) => b[1] - a[1]).slice(0, topN).map(([sku, qty]) => ({ sku, qty, name: nameOf(sku) }));
    topByHistory = true;
  }
  let flowCount = 0;
  for (const byDay of Object.values(salesDaily)) for (const q of Object.values(byDay)) flowCount += q;

  // 单 SKU 全历史逐日出库 + 未来 fcDays 天预测(周六周日不发货, 周末量摊到工作日)
  const fcDays = (opts.forecastDays) || 14;
  const fcDates = [];
  for (let i = 1; i <= fcDays; i++) fcDates.push(dstr(new Date(now.getTime() + i * DAY_MS)));
  const today0 = new Date(now.getFullYear(), now.getMonth(), now.getDate());
  const skuDaily = {};
  for (const r of rows) {
    const byDay = salesDaily[r.sku] || {};
    const keys = Object.keys(byDay).filter(d => /^\d{4}-\d{2}-\d{2}$/.test(d)).sort();
    const dates = [], hist = [];
    if (keys.length) {
      let t = new Date(keys[0] + 'T00:00:00');
      if (t.getTime() > today0.getTime()) t = today0;
      for (; t.getTime() <= today0.getTime(); t = new Date(t.getTime() + DAY_MS)) {
        const ds = dstr(t);
        dates.push(ds); hist.push(byDay[ds] || 0);
      }
    }
    const rate = r.rate || 0;
    const sw = hist.slice(-56);
    const wkSum = [0, 0, 0, 0, 0, 0, 0], wkCnt = [0, 0, 0, 0, 0, 0, 0];
    for (let i = 0; i < sw.length; i++) {
      const wd = new Date(dates[dates.length - sw.length + i] + 'T00:00:00').getDay();
      wkSum[wd] += sw[i]; wkCnt[wd]++;
    }
    let workAvg = 0, workN = 0;
    for (let i = 1; i <= 5; i++) { workAvg += wkSum[i]; workN += wkCnt[i]; }
    workAvg = workN ? workAvg / workN : 0;
    let wf = [0, 1.4, 1.4, 1.4, 1.4, 1.4, 0];
    if (workAvg > 0 && workN >= 10) {
      wf = wkSum.map((s, i) => {
        if (i === 0 || i === 6) return 0;
        const avg = wkCnt[i] ? s / wkCnt[i] : workAvg;
        return Math.min(3, Math.max(0.25, avg / workAvg));
      });
      const mean = wf.reduce((a, b) => a + b, 0) / 5;
      if (mean > 0) wf = wf.map((x, i) => (i === 0 || i === 6) ? 0 : x / mean * (7 / 5));
    }
    const pred = fcDates.map(ds => {
      const wd = new Date(ds + 'T00:00:00').getDay();
      if (wd === 0 || wd === 6) return 0;
      return Math.round(rate * wf[wd] * 10) / 10;
    });
    skuDaily[r.sku] = { dates, hist, pred, rate, wf: wf.map(x => Math.round(x * 100) / 100) };
  }

  const charts = {
    levelDist: { red: stats.red, orange: stats.orange, yellow: stats.yellow, ok: Math.max(0, stats.total - stats.red - stats.orange - stats.yellow) },
    top10, topByHistory, monthly, monthlyReg, skuSeries, skuReg, skuMonthly, skuDaily,
    fcDates, fcDays, dates: dateKeys, chartDays, topN
  };
  const paramObj = { lead, safety, cycle, ropDays, targetDays, productionDays: policy.productionDays || 30, shippingDays: policy.shippingDays || 40, serviceLevel: slv, z: pz, maxSafetyDays: maxSd, w: _dwn, sigmaWindowDays: policy.sigmaWindowDays || 30 };
  return { rows, stats, charts, paramObj, flowCount };
}

/** 把 data/pangu.json 转成 buildRestockView 需要的 store 形态（德国盘古仓） */
function panguStoreLike(pgRaw) {
  const stock = (pgRaw && pgRaw.stock) || [];
  const sales = (pgRaw && pgRaw.sales) || [];
  const wMap = (pgRaw && pgRaw.skuWeight) || {};
  const inventory = [], inTransit = {}, salesDaily = {}, skuMeta = {};
  for (const r of stock) {
    inventory.push({ sku: r.sku, qty: r.qty || 0 });
    inTransit[r.sku] = (inTransit[r.sku] || 0) + (r.loading || 0);      // loading = 在途/待入库
    skuMeta[r.sku] = { name: r.name || (wMap[r.sku] && wMap[r.sku].name) || '' };
  }
  for (const s of sales) {
    if (!s.sku || !s.date) continue;
    const o = salesDaily[s.sku] || (salesDaily[s.sku] = {});
    o[s.date] = (o[s.date] || 0) + (s.qty || 0);
    if (!skuMeta[s.sku]) skuMeta[s.sku] = { name: (wMap[s.sku] && wMap[s.sku].name) || '' };
  }
  for (const sku of Object.keys(wMap)) if (!skuMeta[sku]) skuMeta[sku] = { name: wMap[sku].name || '' };
  return { data: { inventory, inTransit, salesDaily, skuMeta, lastSyncAt: null } };
}

/**
 * 生成看板 HTML
 * @param {object} store Store实例
 * @param {object} cfg 配置
 * @param {string} warehouseLabel 仓库说明
 * @param {object} extra {generatedAt, syncAt}
 */
function generateDashboard(store, cfg, warehouseLabel, extra) {
  const policy = cfg.policy || {};
  const dashCfg = cfg.dashboard || {};
  const lead = (policy.productionDays || 30) + (policy.shippingDays || 40);
  const safety = policy.safetyStockDays || 15;
  const cycle = policy.restockCycleDays || 30;
  const ropDays = lead + safety;
  const targetDays = cycle + lead + safety;
  const chartDays = dashCfg.chartDays || 60;
  const topN = dashCfg.topN || 10;

  // ---------- 备货计算 ----------
  const evals = restock.evaluateAll(store, policy);
  const now = new Date();
  const rows = evals.map(e => {
    let lastOrderDay = null, lastOrderInDays = null, stockoutDay = null, arriveDay = null;
    if (e.rate > 0) {
      const coverF = e.position / e.rate;
      stockoutDay = addDays(now, Math.floor(coverF));
      const ropD = e.ropDays || ropDays;               // 新模型: ROP 折算天数; 旧口径兜底
      const slack = Math.ceil(e.coverDays - ropD);
      lastOrderInDays = slack;
      lastOrderDay = addDays(now, slack);
      arriveDay = addDays(now, lead);
    }
    const meta = store.data.skuMeta && store.data.skuMeta[e.sku];
    return Object.assign({}, e, {
      name: meta && meta.name ? meta.name : '',
      lastOrderInDays, lastOrderDay, stockoutDay, arriveDay
    });
  });

  const stats = {
    total: rows.length,
    withStock: rows.filter(r => r.position > 0).length,
    red: rows.filter(r => r.level === 'red').length,
    orange: rows.filter(r => r.level === 'orange').length,
    yellow: rows.filter(r => r.level === 'yellow').length,
    toOrder: rows.filter(r => r.suggest > 0).length,
    totalQty: rows.reduce((s, r) => s + r.position, 0)
  };

  const generatedAt = (extra && extra.generatedAt) || dstr(now) + ' ' + String(now.getHours()).padStart(2, '0') + ':' + String(now.getMinutes()).padStart(2, '0');
  const syncAt = (extra && extra.syncAt) || (store.data.lastSyncAt ? new Date(store.data.lastSyncAt * 1000).toLocaleString('zh-CN') : '尚未同步');

  // ---------- 图表数据 ----------
  // 以 db.json 的 salesDaily 为底, 再用 trace.json 的出库明细覆盖(不是相加!)。
  // 注意两点, 都是踩过的坑:
  //  1) db.json 的销量同步(lastOutboundSync)可能落后于 trace 溯源(每次重建现拉),
  //     不补的话日销走势图尾部会出现一段"零线"假数据, 看起来像数据丢了;
  //  2) 两个数据源的同一天数值口径不同(出库单日期按美西时间, 库存流水按中国时间,
  //     存在约1天的错位)。所以只能"以 trace 为准做覆盖", 绝不能累加,
  //     否则重叠日会被算两遍, 出库量凭空翻倍。
  const salesDaily = {};
  for (const [sku, byDay] of Object.entries(store.data.salesDaily || {})) {
    salesDaily[sku] = Object.assign({}, byDay);
  }
  const traceSrc = (extra && extra.trace) || null;
  if (traceSrc && Array.isArray(traceSrc.outbound)) {
    // 先按 sku×date 聚合 trace 出库量, 再整日覆盖
    const ta = {};
    for (const t of traceSrc.outbound) {
      const d = String(t.date || '');
      if (!/^\d{4}-\d{2}-\d{2}$/.test(d)) continue;
      const q = Number(t.qty) || 0;
      if (q <= 0) continue;
      const k = t.sku + '|' + d;
      ta[k] = (ta[k] || 0) + q;
    }
    // 只覆盖 trace 确实有出库记录的日期; db 独有的历史日期保持原样
    for (const k of Object.keys(ta)) {
      const i = k.lastIndexOf('|');
      const sku = k.slice(0, i), d = k.slice(i + 1);
      const byDay = salesDaily[sku] || (salesDaily[sku] = {});
      byDay[d] = ta[k];
    }
  }
  // 近 chartDays 天各SKU出库量
  const dateKeys = [];
  for (let i = chartDays - 1; i >= 0; i--) dateKeys.push(dstr(new Date(now.getTime() - i * DAY_MS)));
  const recentBySku = {};
  for (const [sku, byDay] of Object.entries(salesDaily)) {
    let sum = 0;
    for (const d of dateKeys) sum += byDay[d] || 0;
    if (sum > 0) recentBySku[sku] = sum;
  }

  // 月度出库趋势 + 线性回归预测(未来3个月)
  const monthly = monthlySeries(salesDaily);
  let monthlyReg = null;
  if (monthly.length >= 2) {
    const r = linreg(monthly.map(x => x.qty));
    if (r) {
      const lastM = monthly[monthly.length - 1].m;
      const forecast = [];
      for (let i = 1; i <= 3; i++) {
        const t = new Date(lastM + '-01');
        t.setMonth(t.getMonth() + i);
        const m = t.getFullYear() + '-' + String(t.getMonth() + 1).padStart(2, '0');
        forecast.push({ m, qty: Math.max(0, Math.round(r.a + r.b * (monthly.length - 1 + i))) });
      }
      monthlyReg = { slope: r.b, intercept: r.a, forecast };
    }
  }

  // 近 chartDays 天日销量序列（仅对有近期出库的SKU, 用于点击展开详情图）
  const skuSeries = {};
  for (const sku of Object.keys(recentBySku)) {
    const byDay = salesDaily[sku];
    const arr = dateKeys.map(d => byDay[d] || 0);
    if (arr.some(v => v > 0)) skuSeries[sku] = arr;
  }
  const skuReg = {};
  for (const [sku, arr] of Object.entries(skuSeries)) {
    const r = linreg(arr);
    if (r) {
      const fc = [];
      for (let i = 1; i <= 7; i++) fc.push(Math.max(0, Math.round(r.a + r.b * (arr.length - 1 + i))));
      skuReg[sku] = { slope: r.b, forecast: fc };
    }
  }
  // SKU 月度序列（全历史, 供详情页在无近期数据时降级展示）
  const skuMonthly = {};
  for (const [sku, byDay] of Object.entries(salesDaily)) {
    const map = {};
    for (const [date, qty] of Object.entries(byDay)) {
      const m = date.slice(0, 7);
      if (/^\d{4}-\d{2}$/.test(m)) map[m] = (map[m] || 0) + qty;
    }
    const arr = Object.keys(map).sort().map(m => ({ m, qty: map[m] }));
    if (arr.length) skuMonthly[sku] = arr;
  }
  // Top10: 优先近 chartDays 天; 若空则降级为全历史(标注 byHistory=true)
  let top10 = Object.entries(recentBySku)
    .sort((a, b) => b[1] - a[1]).slice(0, topN)
    .map(([sku, qty]) => ({ sku, qty, name: (store.data.skuMeta && store.data.skuMeta[sku] && store.data.skuMeta[sku].name) || '' }));
  let topByHistory = false;
  if (!top10.length) {
    const hist = {};
    for (const [sku, byDay] of Object.entries(salesDaily)) {
      let sum = 0;
      for (const q of Object.values(byDay)) sum += q;
      if (sum > 0) hist[sku] = sum;
    }
    top10 = Object.entries(hist).sort((a, b) => b[1] - a[1]).slice(0, topN)
      .map(([sku, qty]) => ({ sku, qty, name: (store.data.skuMeta && store.data.skuMeta[sku] && store.data.skuMeta[sku].name) || '' }));
    topByHistory = true;
  }

  // 出库流水总条数
  let flowCount = 0;
  for (const byDay of Object.values(salesDaily)) for (const q of Object.values(byDay)) flowCount += q;

  // ---------- 认证 ----------
  const authCfg = dashCfg.auth || {};
  const auth = {
    enabled: !!authCfg.enabled,
    usernameHash: authCfg.username ? crypto.createHash('sha256').update(String(authCfg.username)).digest('hex') : '',
    passHash: authCfg.password ? crypto.createHash('sha256').update(String(authCfg.password)).digest('hex') : ''
  };

  // ---------- 内嵌 Chart.js ----------
  let chartJs = '';
  try { chartJs = fs.readFileSync(CHART_JS_PATH, 'utf8').replace(/<\/script>/gi, '<\\/script>'); } catch (e) { /* 缺库时图表区显示提示 */ }

  // 统计模型展示参数
  const slv = policy.serviceLevel === undefined || policy.serviceLevel === null ? 0.95 : Number(policy.serviceLevel);
  const pz = restock.zScore(slv);
  const maxSd = policy.maxSafetyDays === undefined || policy.maxSafetyDays === null ? 30 : policy.maxSafetyDays;
  const _dw = policy.demandWeights || {};
  const _dwn = { d7: Math.round((Number(_dw.d7) || 0.4) * 100), d30: Math.round((Number(_dw.d30) || 0.3) * 100), d60: Math.round((Number(_dw.d60) || 0.3) * 100) };

  // 单 SKU 走势: 每 SKU 全历史逐日出库(含0补齐) + 未来 fcDays 天波动预测
  // 周六周日不发货(预测=0)，但周末累积的订单并入周一等发货日 → 整周发货总量仍=7D。
  // wf 由近期(≤56天)历史统计各星期几平均出库/工作日总体日均得形状，
  // 再缩放使 5 个工作日系数均值=7/5=1.4(=把周末的量摊回工作日)，夹在 [0.25,3] 防极端值。
  // 周一通常最高(周六日订单累积一起发)，由数据自动体现。
  const fcDays = dashCfg.forecastDays || 14;
  const fcDates = [];
  for (let i = 1; i <= fcDays; i++) fcDates.push(dstr(new Date(now.getTime() + i * DAY_MS)));
  const today0 = new Date(now.getFullYear(), now.getMonth(), now.getDate());
  const skuDaily = {};
  for (const r of rows) {
    const byDay = salesDaily[r.sku] || {};
    const keys = Object.keys(byDay).filter(d => /^\d{4}-\d{2}-\d{2}$/.test(d)).sort();
    const dates = [], hist = [];
    if (keys.length) {
      let t = new Date(keys[0] + 'T00:00:00');
      if (t.getTime() > today0.getTime()) t = today0;
      for (; t.getTime() <= today0.getTime(); t = new Date(t.getTime() + DAY_MS)) {
        const ds = dstr(t);
        dates.push(ds); hist.push(byDay[ds] || 0);
      }
    }
    const rate = r.rate || 0;
    // 星期系数: 取近期最多56天历史; 周六周日强制 0(不发货)
    const sw = hist.slice(-56);
    const wkSum = [0, 0, 0, 0, 0, 0, 0], wkCnt = [0, 0, 0, 0, 0, 0, 0];
    for (let i = 0; i < sw.length; i++) {
      const wd = new Date(dates[dates.length - sw.length + i] + 'T00:00:00').getDay();
      wkSum[wd] += sw[i]; wkCnt[wd]++;
    }
    let workAvg = 0, workN = 0;
    for (let i = 1; i <= 5; i++) { workAvg += wkSum[i]; workN += wkCnt[i]; }
    workAvg = workN ? workAvg / workN : 0;
    let wf = [0, 1.4, 1.4, 1.4, 1.4, 1.4, 0];   // 索引0=周日 6=周六 → 0(不发货); 工作日默认摊平=1.4
    if (workAvg > 0 && workN >= 10) {
      wf = wkSum.map((s, i) => {
        if (i === 0 || i === 6) return 0;
        const avg = wkCnt[i] ? s / wkCnt[i] : workAvg;
        return Math.min(3, Math.max(0.25, avg / workAvg));
      });
      const mean = wf.reduce((a, b) => a + b, 0) / 5;
      if (mean > 0) wf = wf.map((x, i) => (i === 0 || i === 6) ? 0 : x / mean * (7 / 5));
    }
    const pred = fcDates.map(ds => {
      const wd = new Date(ds + 'T00:00:00').getDay();
      if (wd === 0 || wd === 6) return 0;
      return Math.round(rate * wf[wd] * 10) / 10;
    });
    skuDaily[r.sku] = { dates, hist, pred, rate, wf: wf.map(x => Math.round(x * 100) / 100) };
  }

  const dataJson = JSON.stringify(rows);
  const paramObj = { lead, safety, cycle, ropDays, targetDays, productionDays: policy.productionDays || 30, shippingDays: policy.shippingDays || 40, serviceLevel: slv, z: pz, maxSafetyDays: maxSd, w: _dwn, sigmaWindowDays: policy.sigmaWindowDays || 30 };
  const params = JSON.stringify(paramObj);
  const chartsJson = JSON.stringify({ levelDist: { red: stats.red, orange: stats.orange, yellow: stats.yellow, ok: Math.max(0, stats.total - stats.red - stats.orange - stats.yellow) }, top10, topByHistory, monthly, monthlyReg, skuSeries, skuReg, skuMonthly, skuDaily, fcDates, fcDays, dates: dateKeys, chartDays, topN });
  const authJson = JSON.stringify(auth);
  const source = { warehouse: warehouseLabel || '美国仓', api: '富皇美运 OpenAPI · 库存 getSkuDetailList / 销量 出库单+库存流水', generatedAt, syncAt, skuCount: stats.total, flowCount };
  const sourceJson = JSON.stringify(source);

  // ---------- 出库溯源(FIFO)数据 ----------
  const trace = (extra && extra.trace) || null;
  const traceJson = JSON.stringify(trace ? Object.assign({ has: true }, trace) : { has: false });
  const tst = (trace && trace.stats) || {};
  const tOut = tst.outCount || 0, tMatched = tst.matchedCount || 0, tRate = tst.matchedRate || 0, tUn = tst.unmatchedCount || 0, tIn = tst.inboundCount || 0;
  // 入库批次按唯一RO分组(同一RO可能含多个SKU/仓库行, 出口单号按整批RO一致)
  const inGroups = [];
  const inIdx = {};
  if (trace && Array.isArray(trace.inbound)) {
    for (const b of trace.inbound) {
      let g = inIdx[b.ro];
      if (!g) {
        g = inIdx[b.ro] = { ro: b.ro, roDate: b.roDate, skus: new Set(), whs: new Set(), total: 0, used: 0, exportNo: '', exportTracking: '', exportWh: '' };
        inGroups.push(g);
      }
      g.skus.add(b.sku);
      g.whs.add(b.warehouse);
      g.total += b.total || 0;
      g.used += b.used || 0;
      if (b.exportNo && !g.exportNo) g.exportNo = b.exportNo;
      if (b.exportTracking && !g.exportTracking) g.exportTracking = b.exportTracking;
      if (b.exportWh && !g.exportWh) g.exportWh = b.exportWh;
    }
    for (const g of inGroups) g.remain = Math.max(0, g.total - g.used);
  }
  // 入库批次分组(唯一RO) 直接内嵌给前端渲染(分页/头程费用)
  const ingroupsJson = JSON.stringify(inGroups);
  // ---- PI & 头程发货数据(本机录入 data/pis.json / freight_batches.json, 由 src/pi-server.js 维护) ----
  const piRaw = (extra && extra.pi) || null;
  const PIF = {
    has: !!(piRaw && ((piRaw.pis || []).length || (piRaw.batches || []).length)),
    pis: (piRaw && piRaw.pis) || [],
    batches: (piRaw && piRaw.batches) || []
  };
  const pifJson = JSON.stringify(PIF);
  // ---- 速卖通订单数据(data/ae_orders.json, 由 src/pi-server.js API 维护; 看板重建时注入静态快照) ----
  const aeRaw = (extra && extra.ae) || null;
  const AE_LIST = (aeRaw && aeRaw.list) || [];
  const aeJson = JSON.stringify({ has: !!AE_LIST.length, list: AE_LIST });
  // ---- 盘古德国仓数据(data/pangu.json, 由 src/pangu-sync.js 维护; 看板重建时注入静态快照) ----
  const pgRaw = (extra && extra.pangu) || null;
  // ---- 多仓库备货视图: 德国盘古仓(与美国仓同一套备货口径, 参数可用 cfg.pangu.policy 覆盖) ----
  const dePolicy = Object.assign({}, policy, (cfg && cfg.pangu && cfg.pangu.policy) || {});
  let deJson = 'null';
  if (pgRaw && ((pgRaw.stock || []).length || (pgRaw.sales || []).length)) {
    const deView = buildRestockView(panguStoreLike(pgRaw), dePolicy, { now, chartDays, topN, forecastDays: dashCfg.forecastDays || 14 });
    const deSource = {
      warehouse: '德国盘古仓 ' + ((pgRaw.warehouses || []).join('/') || 'C2/A3'),
      api: '盘古 ECCANG OpenAPI · 库存 getProductInventory / 销量 getOrderList(已发货)',
      generatedAt,
      syncAt: pgRaw.fetchedAt ? new Date(pgRaw.fetchedAt).toLocaleString('zh-CN') : '尚未同步',
      skuCount: deView.stats.total,
      flowCount: deView.flowCount
    };
    deJson = JSON.stringify({
      label: '德国 · 盘古海外仓 ' + ((pgRaw.warehouses || []).join('/') || ''),
      rows: deView.rows, charts: deView.charts, stats: deView.stats, source: deSource, param: deView.paramObj
    });
  }
  const statsJson = JSON.stringify(stats);
  const whSet = new Set();
  if (trace) {
    for (const b of trace.inbound || []) whSet.add(b.warehouse);
    for (const u of trace.unmatched || []) whSet.add(u.warehouse);
  }
  const whChips = [...whSet].sort().map(w => '<span class="chip" data-f="' + esc(w) + '">' + esc(w) + '</span>').join('');

  return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>海外仓智能备货看板</title>
<style>
:root{--bg:#0a0e17;--card:#141a28;--card2:#1a2133;--line:#26304a;--line2:#1e2740;--txt:#e6ebf5;--sub:#8b97b3;--blue:#4d8ff0;--blue-bg:#152743;--teal:#2ec4a6;--teal-bg:#0f2e2a;
/* ---- 深色科技风工作台配色 ---- */
--side-w:236px;--aside:#0d121e;--aside2:#080b14;--side-line:#1e2740;--side-txt:#8b97b3;--accent:#4d8ff0;--accent2:#7c5cff;
/* 深色主题下表格/徽标底色 */
--th:#1a2133;--row-hover:#1b2438;--row-line:#1e2740}
*{box-sizing:border-box;margin:0;padding:0}
body{background:var(--bg);color:var(--txt);font-family:-apple-system,"PingFang SC","Microsoft YaHei",sans-serif;font-size:14px;line-height:1.6}
/* ============ 左侧导航(深色) ============ */
.side{position:fixed;left:0;top:0;bottom:0;width:var(--side-w);background:linear-gradient(180deg,var(--aside) 0%,var(--aside2) 100%);z-index:60;display:flex;flex-direction:column;overflow-y:auto;overflow-x:hidden;transition:width .18s ease;-webkit-user-select:none;user-select:none}
.side::-webkit-scrollbar{width:6px}
.side::-webkit-scrollbar-thumb{background:#2c3654;border-radius:3px}
.side::-webkit-scrollbar-track{background:transparent}
.side-brand{display:flex;align-items:center;gap:10px;padding:16px 16px 14px;color:#fff;font-size:15px;font-weight:700;letter-spacing:.4px;white-space:nowrap;border-bottom:1px solid var(--side-line);cursor:pointer}
.side-brand .logo{width:27px;height:27px;border-radius:8px;background:linear-gradient(135deg,var(--accent) 0%,#8b5cf6 100%);display:inline-flex;align-items:center;justify-content:center;font-size:14px;flex:0 0 auto}
.side-brand .vw{margin-left:auto;color:#7c88ab;font-size:13px;font-weight:400;padding:0 4px}
.nav-grp{display:flex;align-items:center;gap:9px;padding:9px 16px;color:rgba(255,255,255,.9);font-size:13px;font-weight:600;cursor:pointer;border-radius:0;transition:background .14s;white-space:nowrap}
.nav-grp:hover{background:rgba(255,255,255,.07)}
.nav-grp .ic{width:16px;text-align:center;font-size:13px;color:#8b95b5;flex:0 0 auto}
.nav-grp .ar{margin-left:auto;color:#5d678a;font-size:10px;transition:transform .2s;flex:0 0 auto}
.nav-grp.open .ar{transform:rotate(180deg)}
.nav-sub{display:none;padding:1px 0 5px}
.nav-grp.open+.nav-sub{display:block}
.nav-sub .nav-it{display:flex;align-items:center;gap:8px;padding:7px 16px 7px 41px;color:var(--side-txt);font-size:12.5px;cursor:pointer;white-space:nowrap;border-left:3px solid transparent;transition:all .14s}
.nav-sub .nav-it:hover{color:#fff;background:rgba(255,255,255,.06)}
.nav-sub .nav-it.on{color:#fff;font-weight:600;background:linear-gradient(90deg,rgba(77,107,255,.34),rgba(77,107,255,.06));border-left-color:var(--accent)}
.nav-sub .nav-it .nbadge{margin-left:auto;min-width:18px;text-align:center;font-size:10.5px;font-weight:600;padding:0 6px;border-radius:20px;background:rgba(255,255,255,.15);color:#fff}
.nav-sub .nav-it.on .nbadge{background:var(--accent)}
.nav-sub .nav-it.soon{color:#5c6684;cursor:default}
.nav-sub .nav-it.soon::after{content:'待接入';margin-left:auto;font-size:10px;color:#5c6684;border:1px solid #2f3a58;border-radius:20px;padding:0 6px}
.nav-sub .nav-it.soon:hover{background:transparent;color:#5c6684}
.side-foot{margin-top:auto;padding:12px 16px;border-top:1px solid var(--side-line);color:#6f7a9c;font-size:11px;line-height:1.9;white-space:normal;word-break:break-all}
.side-foot b{color:#9aa6c9;font-weight:600;display:block;margin-bottom:2px}
.side-foot .sy{color:#8894b8}
/* 收起态: 只留图标 */
body.side-mini{--side-w:58px}
body.side-mini .side-brand .tx,body.side-mini .nav-grp .tx,body.side-mini .nav-grp .ar{display:none}
body.side-mini .nav-grp{justify-content:center;padding:10px 0}
body.side-mini .side-brand{justify-content:center;padding:16px 0 14px}
body.side-mini .side-brand .vw{display:none}
body.side-mini .side-foot{display:none}
body.side-mini .nav-sub .nav-it{padding:8px 0;font-size:0;justify-content:center}
body.side-mini .nav-sub .nav-it .nbadge,body.side-mini .nav-sub .nav-it.soon::after{display:none}
/* ============ 表单控件深色基线 ============
   兜底: 任何未被 .toolbar/.fm-field/.prod-row/.pager 等作用域覆盖的原生控件,
   都不会再露出浏览器默认的白底/黑字(深色主题下最刺眼的一类残留) */
input:not([type=checkbox]):not([type=radio]):not([type=range]):not([type=file]),
select,textarea{background:var(--card2);color:var(--txt);border-color:var(--line)}
input::placeholder,textarea::placeholder{color:#6b7690}
select option{background:#141a28;color:var(--txt)}
/* 日期选择器的原生日历图标默认是黑色, 深色底下看不见, 反相成浅色 */
input[type=date]::-webkit-calendar-picker-indicator{filter:invert(.75);cursor:pointer;opacity:.8}
input[type=number]::-webkit-inner-spin-button{filter:invert(.75)}
/* 筛选栏内的下拉(出库溯源 SKU/窗口、速卖通 月份/状态、日销日期窗)统一深色 */
.filter select,.filters select,.toolbar select,.fbar select,.sel-w select,select#dSkuSel,select#dWin,select#aeOvWin,select#aeMonth,select#aeSt,select#fPiImpFile{background:var(--card2);color:var(--txt);border:1px solid var(--line);border-radius:6px;padding:4px 8px;font-size:12.5px;outline:none;cursor:pointer}
/* ============ 右侧主区 ============ */
/* 注意: .side 是固定定位的兄弟节点, .wrap 只负责 margin-left 让位, 不用 flex 避免 fixed 子元素参与布局 */
.wrap{margin-left:var(--side-w);min-height:100vh;transition:margin-left .18s ease}
.topbar{position:sticky;top:0;z-index:50;display:flex;align-items:center;gap:12px;flex-wrap:wrap;background:var(--card);border-bottom:1px solid var(--line);padding:0 18px;min-height:54px}
.topbar .tb-bread{display:flex;align-items:center;gap:8px;font-size:15px;font-weight:700}
.topbar .tb-bread .ico{width:24px;height:24px;border-radius:7px;background:var(--blue-bg);color:var(--blue);display:inline-flex;align-items:center;justify-content:center;font-size:12px}
.topbar .tb-sub{font-size:12px;color:var(--sub);padding-left:10px;border-left:1px solid var(--line);white-space:nowrap}
.topbar .tb-right{margin-left:auto;display:flex;align-items:center;gap:10px;flex-wrap:wrap;justify-content:flex-end}
.topbar .who{display:inline-flex;align-items:center;gap:7px;font-size:12px;color:var(--sub);white-space:nowrap}
.topbar .who .av{width:23px;height:23px;border-radius:50%;background:linear-gradient(135deg,var(--blue) 0%,#6f9fe0 100%);color:#fff;display:inline-flex;align-items:center;justify-content:center;font-size:11px;font-weight:700}
.tb-ic{width:31px;height:31px;border:1px solid var(--line);background:var(--card2);border-radius:8px;color:var(--sub);cursor:pointer;font-size:13px;line-height:1;display:inline-flex;align-items:center;justify-content:center;transition:all .14s;flex:0 0 auto}
.tb-ic:hover{border-color:var(--blue);color:var(--blue)}
.tb-ic.on{background:var(--blue);border-color:var(--blue);color:#fff}
.content{padding:16px 18px 54px;min-width:0}
/* 顶部 tab 已改为左侧导航; 隐藏旧的横向 tab 条(保留节点兼容脚本) */
.tabs{display:none}
header{display:none}
.btn{border:1px solid var(--line);background:var(--card2);border-radius:8px;padding:6px 14px;font-size:13px;cursor:pointer;color:var(--sub)}
.btn:hover{border-color:var(--blue);color:var(--blue)}
.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:12px;margin-bottom:16px}
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:14px 16px}
.card .num{font-size:26px;font-weight:600}
/* 速卖通顶部卡片 & 经营总览KPI: 全排数字统一字号/字重/等宽数字(用户要求字体观感一致) */
#aeCards .num,#aeOvKpis .num{font-size:clamp(15px,1.5vw,20px);font-weight:700;font-variant-numeric:tabular-nums;letter-spacing:-.2px;white-space:nowrap}
.card .lbl{color:var(--sub);font-size:12px;margin-top:2px}
.card.red .num{color:#f07575}.card.orange .num{color:#e8a24e}.card.yellow .num{color:#dcbb5e}.card.green .num{color:#5fc47a}.card.blue .num{color:#6aa4f5}.card.teal .num{color:#35cdb0}
.panel{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:16px 18px;margin-bottom:16px}
.panel h2{font-size:15px;font-weight:600;margin-bottom:12px;display:flex;align-items:center;gap:8px;flex-wrap:wrap}
.panel h2 .tag{font-size:11px;font-weight:400;color:var(--sub);background:var(--bg);border:1px solid var(--line);border-radius:20px;padding:1px 10px}
.formula{display:grid;grid-template-columns:repeat(auto-fit,minmax(240px,1fr));gap:10px}
.f-item{background:var(--blue-bg);border-radius:10px;padding:10px 14px}
.f-item .k{color:var(--blue);font-weight:600;font-size:13px}
.f-item .v{font-size:13px;margin-top:2px}
.f-item .v b{font-size:16px}
.source-line{display:flex;flex-wrap:wrap;gap:6px 18px;font-size:13px;color:var(--txt)}
.source-line .ok{color:#5fc47a;font-weight:600}
.source-line .kv{color:var(--sub)}
.charts{display:grid;grid-template-columns:repeat(auto-fit,minmax(300px,1fr));gap:12px;margin-bottom:16px}
.chart-card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:14px 16px}
.chart-card h3{font-size:14px;font-weight:600;margin-bottom:4px}
.chart-card .sub{color:var(--sub);font-size:11px;margin-bottom:10px}
.chart-card h3 .tag{font-size:11px;font-weight:400;color:var(--sub);background:var(--bg);border:1px solid var(--line);border-radius:20px;padding:1px 10px;margin-left:4px}
.dc-head{display:flex;align-items:center;justify-content:space-between;gap:10px;flex-wrap:wrap;margin-bottom:4px}
.dc-tools{display:flex;align-items:center;gap:6px}
.dc-tools select,#dWin{max-width:300px;padding:5px 10px;border:1px solid var(--line);border-radius:8px;font-size:12px;background:var(--card2);color:var(--txt);outline:none;cursor:pointer}
.dc-slider{display:flex;align-items:center;gap:10px;margin-top:9px}
.dc-slider input[type=range]{flex:1;accent-color:var(--blue);cursor:pointer;background:transparent;height:18px;appearance:none;-webkit-appearance:none}
.dc-slider input[type=range]::-webkit-slider-runnable-track{height:5px;border-radius:3px;background:var(--line2);border:1px solid var(--line)}
.dc-slider input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:14px;height:14px;margin-top:-6px;border-radius:50%;background:var(--blue);border:2px solid #141a28;box-shadow:0 0 0 1px var(--blue)}
.dc-slider input[type=range]::-moz-range-track{height:5px;border-radius:3px;background:var(--line2)}
.dc-slider input[type=range]::-moz-range-thumb{width:12px;height:12px;border:2px solid #141a28;border-radius:50%;background:var(--blue)}
.dc-slider .mono{font-size:11px;white-space:nowrap;font-family:ui-monospace,Consolas,monospace}
.logic-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(215px,1fr));gap:8px 12px}
.lg{display:flex;align-items:baseline;justify-content:space-between;gap:10px;border:1px solid var(--line);border-radius:9px;padding:7px 11px;font-size:12px;background:var(--bg)}
.lg .k{color:var(--sub);white-space:nowrap}
.lg .v{font-weight:700;text-align:right;font-family:ui-monospace,Consolas,monospace;font-size:13px}
.lg .v small{font-weight:400;color:var(--sub);font-family:inherit}
.lg.warn{background:#2a2413;border-color:#4d4018}
.lg.bad{background:#2d1a1a;border-color:#57302c}
.chart-box{position:relative;height:230px}
.toolbar{display:flex;gap:10px;flex-wrap:wrap;align-items:center;margin-bottom:12px}
.toolbar input{flex:1;min-width:220px;padding:9px 14px;border:1px solid var(--line);border-radius:8px;font-size:14px;outline:none;background:var(--card2);color:var(--txt)}
.toolbar input::placeholder{color:#6a7690}
.toolbar input:focus{border-color:var(--blue)}
.chips{display:flex;gap:6px;flex-wrap:wrap}
.chip{padding:6px 14px;border:1px solid var(--line);border-radius:20px;font-size:13px;cursor:pointer;background:var(--card2);color:var(--sub);user-select:none}
.chip.on{background:var(--blue);border-color:var(--blue);color:#fff}
/* 备货看板 数据源切换条(美国富皇美运 / 德国盘古) */
.wh-bar{display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:14px;padding:10px 14px;background:var(--card);border:1px solid var(--line);border-radius:12px}
.wh-bar .wh-lbl{font-size:12px;color:var(--sub);font-weight:600;letter-spacing:.5px}
.wh-bar .chip{font-size:13.5px;padding:7px 16px;font-weight:600}
.wh-bar .wh-note{font-size:12px;color:var(--sub);margin-left:auto}
table{width:100%;border-collapse:collapse;background:var(--card);border:1px solid var(--line);border-radius:12px;overflow:hidden}
thead th{background:var(--th);text-align:left;font-size:12px;color:var(--sub);font-weight:600;padding:10px 12px;border-bottom:1px solid var(--line);white-space:nowrap}
tbody td{padding:9px 12px;border-bottom:1px solid var(--row-line);font-size:13px;white-space:nowrap}
tbody tr{cursor:pointer}
tbody tr:hover{background:var(--row-hover)}
tbody tr:last-child td{border-bottom:none}
.mono{font-family:Consolas,Menlo,monospace;font-size:12.5px}
.num-r{text-align:right}
.badge{display:inline-block;min-width:56px;text-align:center;padding:2px 10px;border-radius:20px;font-size:12px;font-weight:600}
.lv-red{background:#3a1d1d;color:#f08a8a}
.lv-orange{background:#3a2c14;color:#e5a84e}
.lv-yellow{background:#352d16;color:#d9b95c}
.lv-green{background:#1d3320;color:#7fc98a}
.lv-gray{background:#242a38;color:#9aa5bd}
.due{font-weight:600}
.due.over{color:#f08a8a}
.due.soon{color:#e5a84e}
.due.ok{color:#7fc98a}
footer{color:var(--sub);font-size:12px;margin-top:18px;text-align:center;line-height:1.9}
/* 旧横向 tab 样式(已由左侧导航替代) */
.tab{display:none}
.tab-badge{display:inline-block;min-width:20px;text-align:center;padding:1px 7px;border-radius:20px;font-size:11px;background:var(--blue);color:#fff;margin-left:6px}
/* 溯源进度条 */
.bar{height:6px;background:#1e2740;border-radius:4px;overflow:hidden;min-width:72px}
.bar i{display:block;height:100%;background:var(--teal);border-radius:4px}
.bar.amber i{background:#e8a24e}
.bar.red i{background:#e06060}
.matched-ok{color:#5fc47a;font-weight:600}
.matched-no{color:#f07575;font-weight:600}
.trace-note{background:#2a2413;border:1px solid #4d4018;border-radius:10px;padding:12px 16px;font-size:12.5px;color:#d9b95c;margin-top:16px;line-height:1.9}
.trace-note b{color:#e5a84e}
.trace-tip{background:var(--blue-bg);border:1px solid #23456e;border-radius:10px;padding:12px 16px;font-size:12.5px;color:#9dc0f0;margin-top:14px;line-height:1.9}
.trace-tip b{color:#bcd8f7}
.dim{color:#aab4c2}
.empty{text-align:center;color:var(--sub);padding:40px 0}
/* 登录 */
.login-mask{position:fixed;inset:0;background:radial-gradient(900px 520px at 22% 12%,#16294a 0%,#0a0e17 62%),linear-gradient(135deg,#0a0e17 0%,#0d1424 100%);display:flex;align-items:center;justify-content:center;z-index:999}
/* 未登录时隐藏整个工作台外壳(含左侧导航), 避免登录页旁边露出侧栏 */
body.locked .side,body.locked .wrap{display:none}
.login-card{background:var(--card);border:1px solid var(--line);border-radius:16px;padding:36px 40px;width:340px;box-shadow:0 20px 60px rgba(0,0,0,.6)}
.login-card h2{font-size:19px;font-weight:600;text-align:center;margin-bottom:4px}
.login-card .sub{color:var(--sub);font-size:12px;text-align:center;margin-bottom:22px}
.login-card input{width:100%;padding:11px 14px;border:1px solid var(--line);border-radius:8px;font-size:14px;margin-bottom:12px;outline:none;background:var(--card2);color:var(--txt)}
.login-card input:focus{border-color:var(--blue)}
.login-card button{width:100%;padding:11px;background:var(--blue);color:#fff;border:none;border-radius:8px;font-size:15px;font-weight:600;cursor:pointer}
.login-card button:hover{opacity:.92}
.login-card .err{color:#f08a8a;font-size:12px;text-align:center;margin-top:10px;min-height:16px}
.login-card .remember{display:flex;align-items:center;gap:6px;font-size:12px;color:var(--sub);margin:-2px 0 12px;cursor:pointer;user-select:none}
.login-card .remember input{width:auto;margin:0;accent-color:var(--blue)}
.login-foot{color:#9db8d6;font-size:11px;text-align:center;margin-top:16px}
/* SKU详情弹窗 */
.modal-mask{position:fixed;inset:0;background:rgba(5,8,15,.72);display:none;align-items:center;justify-content:center;z-index:1000;padding:20px}
.modal{background:var(--card);border:1px solid var(--line);border-radius:14px;width:760px;max-width:100%;max-height:90vh;overflow:auto;padding:22px 24px}
.modal h2{font-size:16px;font-weight:600;display:flex;align-items:center;gap:10px;flex-wrap:wrap}
.modal .close{float:right;border:none;background:none;font-size:20px;cursor:pointer;color:var(--sub)}
.detail-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:10px;margin:14px 0}
.d-item{background:var(--bg);border-radius:10px;padding:10px 12px}
.d-item .k{color:var(--sub);font-size:11px}
.d-item .v{font-size:16px;font-weight:600;margin-top:2px}
.d-item .v.red{color:#f07575}.d-item .v.orange{color:#e8a24e}
.trend-note{color:var(--sub);font-size:11px;margin:6px 0 4px}
/* 分页条 */
.pager{display:flex;align-items:center;gap:8px;margin-top:10px;flex-wrap:wrap}
.pager .pg-info{color:var(--sub);font-size:12px;margin-right:auto}
.pager .pg-cur{font-size:12px;color:var(--sub)}
.pager select{border:1px solid var(--line);border-radius:6px;padding:3px 6px;font-size:12px;background:var(--card2);color:var(--sub);outline:none;cursor:pointer}
.btn.small{padding:2px 10px;font-size:12px;border-radius:6px}
.btn:disabled{opacity:.45;cursor:default}
.btn:disabled:hover{border-color:var(--line);color:var(--sub)}
.btn.pending{background:var(--blue);border-color:var(--blue);color:#fff;box-shadow:0 0 0 2px rgba(77,143,240,.22)}
.btn.pending:hover{background:#2f6fd0;color:#fff;border-color:#2f6fd0}
/* PI & 头程费用 */
.pfee{font-weight:600;white-space:nowrap}
.pfee.dim{color:#aab4c2;font-weight:400}
.fee-head{font-size:12px;color:var(--sub);font-weight:600}
.b-pi{background:#1b2c4a;color:#8fb8f0}
.b-in{background:#1d3320;color:#7fc98a}
.b-wait{background:#352d16;color:#d9b95c}
.pi-gap{font-size:12px;color:var(--sub)}
.v-bar{height:6px;background:#1e2740;border-radius:4px;overflow:hidden;min-width:60px;display:inline-block;vertical-align:middle}
.v-bar i{display:block;height:100%;background:var(--teal);border-radius:4px}
.v-bar.amber i{background:#e8a24e}
.v-bar.red i{background:#e06060}
/* PI & 头程页 */
.tagline{background:var(--bg);border:1px dashed var(--line);border-radius:10px;padding:12px 16px;font-size:13px;line-height:2;color:var(--txt)}
.pi-sub td{background:var(--card2);border-bottom:1px solid var(--row-line);padding:4px 12px}
.pi-sub table{width:100%;border:none;background:transparent}
.pi-sub th{background:transparent;font-size:11px;color:var(--sub);font-weight:600;padding:4px 8px;border:none;text-align:left}
.pi-sub th.num-r,.pi-sub td.num-r{text-align:right}
.pi-sub td{padding:3px 8px;border:none;font-size:12px;white-space:nowrap;border-bottom:none}
.pi-sub .mono{font-size:12px}
.row-note{color:var(--sub);font-size:11px}
/* ---- 在线录入 (pi-v2) ---- */
.btn.primary{background:var(--blue);border-color:var(--blue);color:#fff}
.btn.primary:hover{background:#2f6fd0;color:#fff}
.btn.danger{color:#f08a8a;border-color:#57302c}
.btn.danger:hover{border-color:#e06060;color:#f07575}
.hd-right{margin-left:auto;display:inline-flex;gap:6px}
.hd-right .btn{font-size:12px;padding:4px 12px}
.entry-st{border-radius:10px;padding:10px 16px;font-size:13px;margin-bottom:14px;line-height:1.8}
.entry-st.live{background:#172c1b;border:1px solid #2f5236;color:#8fd39a}
.entry-st.ro{background:#2a2413;border:1px solid #4d4018;color:#d9b95c}
.entry-st .dot{display:inline-block;width:8px;height:8px;border-radius:50%;margin-right:6px;vertical-align:1px}
.entry-st.live .dot{background:#7fc98a}
.entry-st.ro .dot{background:#e5a84e}
.entry-st .act{margin-left:10px;color:var(--blue);cursor:pointer;text-decoration:underline}
.toolbar .dt{flex:0 0 auto;min-width:0;width:150px;padding:8px 10px;font-size:13px}
.toolbar .dt-sep{color:var(--sub);font-size:12px}
.toolbar .btn{flex:0 0 auto}
.op-td{width:104px;text-align:right;white-space:nowrap}
.op-td .op-a{color:var(--blue);cursor:pointer;margin-right:10px;font-size:12px}
.op-td .op-d{color:#f07575;cursor:pointer;font-size:12px}
.op-td .op-a:hover{text-decoration:underline}
.op-td .op-d:hover{text-decoration:underline}
/* 录入表单弹窗 */
#fmModal .modal{width:900px}
.fm-grid{display:grid;grid-template-columns:1fr 1fr;gap:10px 16px;margin:14px 0 6px}
.fm-grid .full{grid-column:1/-1}
.fm-field{display:flex;flex-direction:column;gap:3px}
.fm-field label{font-size:12px;color:var(--sub);font-weight:600}
.fm-field input,.fm-field select{width:100%;padding:8px 10px;border:1px solid var(--line);border-radius:8px;font-size:13px;outline:none;background:var(--card2);color:var(--txt)}
.fm-field input:focus,.fm-field select:focus{border-color:var(--blue)}
.fm-field .hint{font-size:11px;color:var(--sub)}
.fm-field .hint .rate-pv{color:#2ec4a6;font-size:13px}
.fm-row-btn{font-size:12px;color:var(--blue);background:var(--card2);border:1px dashed #35507a;border-radius:8px;padding:6px 10px;cursor:pointer;margin:2px 0 8px}
.fm-row-btn:hover{background:var(--blue-bg)}
.prod-head,.prod-row{display:grid;grid-template-columns:1.1fr 1.7fr .65fr .8fr .7fr 30px;gap:6px;align-items:center}
.prod-head.with-reb,.prod-row.with-reb{grid-template-columns:.88fr 1.18fr .45fr .6fr .5fr .64fr .64fr 26px}
/* 批次表单: 首列为「归属 PI」(一柜混装多个 PI 时按 PI 统计发货进度) */
.prod-head.with-pi,.prod-row.with-pi{grid-template-columns:1fr 1.05fr 1.25fr .5fr .68fr .68fr 30px}
.prod-row .pr-pi{font-size:12px;padding:6px 4px}
.pi-reb-sum{display:flex;flex-wrap:wrap;gap:6px 18px;align-items:center;background:var(--card2);border:1px dashed #35507a;border-radius:8px;padding:8px 12px;margin:8px 0 10px;font-size:12.5px}
.pi-reb-sum b{font-size:14px}
.pi-reb-sum .net{border-left:1px solid var(--line);padding-left:16px}
.pi-reb-sum .net b{font-size:15px;color:var(--blue)}
.prod-head span{font-size:11px;color:var(--sub);font-weight:600}
.prod-row input,.prod-row select{width:100%;padding:6px 8px;border:1px solid var(--line);border-radius:6px;font-size:12.5px;outline:none;background:var(--card2);color:var(--txt)}
.prod-row input:focus{border-color:var(--blue)}
.prod-row .rm{border:none;background:none;color:#f08a8a;font-size:17px;cursor:pointer;line-height:1}
.fm-err{color:#f08a8a;font-size:12.5px;min-height:18px;margin:2px 0 6px}
.fm-err.ok{color:#7fc98a}
.fm-bar{display:flex;justify-content:flex-end;gap:10px;border-top:1px solid var(--line);padding-top:14px;margin-top:6px}
.fm-bar .btn{padding:8px 22px;font-size:14px}
/* 列多的宽表一律用横向滑轨浏览: 面板保持正常宽度, 表格超出部分左右拖动 */
.tbl-scroll{overflow:auto;padding-bottom:4px}
/* 宽表不压缩列: 保持每列可读的最小宽度, 让右滑轨去滚动, 避免列被挤成一条 */
.tbl-scroll table{min-width:max-content}
.tbl-scroll th,.tbl-scroll td{white-space:nowrap}
.tbl-scroll th{padding:8px 10px}
.tbl-scroll td{padding:7px 10px}
.tbl-scroll::-webkit-scrollbar{height:11px;width:11px}
.tbl-scroll::-webkit-scrollbar-track{background:#141a28;border-radius:6px}
.tbl-scroll::-webkit-scrollbar-thumb{background:#33405e;border-radius:6px;border:2px solid #141a28}
.tbl-scroll::-webkit-scrollbar-thumb:hover{background:#45557a}
/* 头程发货批次表: 列多, 表头不换行(靠滑轨横向浏览), 单号类单元格允许折行 */
.pb-tbl{min-width:100%}
.pb-tbl thead th{white-space:nowrap;vertical-align:bottom}
.pb-tbl tbody td{vertical-align:top}
.pb-tbl .pi-stack{line-height:1.5;white-space:nowrap}
.pb-tbl .tno-l1{display:block;white-space:nowrap}
.pb-tbl .tno-l2{display:block;white-space:nowrap;margin-top:2px}
.pb-tbl .op-td{white-space:nowrap}
.pb-tbl .sku-info{margin-top:6px;font-size:12px;color:var(--sub);line-height:1.5}
/* ---- 速卖通智能表格 (ae smart-grid) ---- */
.ae-viewbar{display:inline-flex;gap:0;border:1px solid var(--line);border-radius:9px;overflow:hidden;margin:0 0 12px;background:var(--card2)}
.ae-vtab{padding:8px 18px;font-size:13px;cursor:pointer;color:var(--sub);border-right:1px solid var(--line);user-select:none;white-space:nowrap}
.ae-vtab:last-child{border-right:none}
.ae-vtab:hover{background:var(--blue-bg)}
.ae-vtab.active{background:var(--blue);color:#fff;font-weight:600}
.ae-grid{border-collapse:separate;border-spacing:0;width:max-content;min-width:100%}
.ae-grid th{position:sticky;top:0;z-index:5;background:var(--th);font-size:12px;padding:9px 8px;border-bottom:2px solid var(--line);border-right:1px solid var(--line2);white-space:nowrap;color:var(--sub)}
.ae-grid th:last-child{border-right:none}
.ae-grid td{border-bottom:1px solid var(--row-line);border-right:1px solid var(--line2);font-size:12.5px;padding:5px 8px;white-space:nowrap}
.ae-grid td.ae-c{cursor:cell}
.ae-grid tr:hover td{background:var(--row-hover)}
.ae-grid tr:hover td.ae-num{background:var(--row-hover)}
.ae-grid .rowno{color:var(--sub);font-size:11px;text-align:center;cursor:default;background:#171e2e;min-width:34px}
.ae-grid tfoot td{border-top:2px solid var(--line);background:#171e2e;font-weight:700;font-size:12.5px;position:sticky;bottom:0;z-index:4}
.ae-cell-inp{width:100%;min-width:80px;border:2px solid var(--blue);border-radius:4px;padding:2px 5px;font-size:12.5px;outline:none;background:var(--card);color:var(--txt);font-family:inherit;box-sizing:border-box}
.ae-num{text-align:right}
.ae-cnt{color:var(--sub);font-size:12.5px;margin-left:auto}
@media(max-width:1180px){body{--side-w:58px}body .side-brand .tx,body .nav-grp .tx,body .nav-grp .ar{display:none}body .side-foot{display:none}body .side-brand,body .nav-grp{justify-content:center}body .side-brand{padding:16px 0 14px}body .nav-grp{padding:10px 0}body .side-brand .vw{display:none}body .nav-sub .nav-it{justify-content:center;padding:8px 0;font-size:0}body .nav-sub .nav-it .nbadge,body .nav-sub .nav-it.soon::after{display:none}}
@media(max-width:760px){.content{padding:12px 10px 40px}.topbar{padding:0 10px}.topbar .tb-sub{display:none}tbody td{padding:8px}.modal{width:100%}.fm-grid{grid-template-columns:1fr}}
</style>
</head>
<body>
<div class="login-mask" id="login">
  <div>
    <div class="login-card">
      <h2>▣ 海外仓库存看板</h2>
      <p class="sub">数据对接富皇美运海外仓系统</p>
      <input id="u" placeholder="账号" autocomplete="username">
      <input id="p" type="password" placeholder="密码" autocomplete="current-password">
      <label class="remember" title="勾选后本浏览器下次打开自动进入看板，无需再输账号密码"><input type="checkbox" id="rm" checked> 记住我 · 本浏览器自动登录</label>
      <button onclick="doLogin()">进入看板</button>
      <p class="err" id="loginErr"></p>
    </div>
    <p class="login-foot">账号密码由管理员在 config.json 中配置 · 改密后需重新生成部署</p>
  </div>
</div>

<div class="wrap" id="app" style="display:none">
<!-- ==================== 左侧导航: 运营工作台(模块化, 后续新模块直接加一组 nav-grp) ==================== -->
<aside class="side" id="side">
  <div class="side-brand" title="海外仓运营工作台 · 点击收起/展开导航" onclick="sideToggle()">
    <span class="logo">▣</span><span class="tx">海外仓运营台</span><span class="vw">«</span>
  </div>

  <div class="nav-grp open" data-grp="stock" onclick="navGrp('stock')">
    <span class="ic">▤</span><span class="tx">库存与备货</span><span class="ar">▾</span>
  </div>
  <div class="nav-sub">
    <div class="nav-it on" data-t="stock" onclick="switchTab('stock')"><span>备货看板</span></div>
    <div class="nav-it soon"><span>库存预警订阅</span></div>
    <div class="nav-it soon"><span>智能补货计划</span></div>
  </div>

  <div class="nav-grp open" data-grp="chain" onclick="navGrp('chain')">
    <span class="ic">⇄</span><span class="tx">供应链</span><span class="ar">▾</span>
  </div>
  <div class="nav-sub">
    <div class="nav-it" data-t="trace" onclick="switchTab('trace')"><span>出库溯源</span><span class="nbadge" id="navBadgeTrace" style="display:none">0</span></div>
    <div class="nav-it" data-t="pi" onclick="switchTab('pi')"><span>PI &amp; 头程</span><span class="nbadge" id="navBadgePi" style="display:none">0</span></div>
    <div class="nav-it soon"><span>采购与供应商</span></div>
  </div>

  <div class="nav-grp open" data-grp="ops" onclick="navGrp('ops')">
    <span class="ic">◎</span><span class="tx">运营中心</span><span class="ar">▾</span>
  </div>
  <div class="nav-sub">
    <div class="nav-it" data-t="ae" onclick="switchTab('ae')"><span>速卖通订单</span><span class="nbadge" id="navBadgeAe" style="display:none">0</span></div>
    <div class="nav-it soon"><span>营销活动</span></div>
    <div class="nav-it soon"><span>定价与利润</span></div>
  </div>

  <div class="nav-grp" data-grp="content" onclick="navGrp('content')">
    <span class="ic">✎</span><span class="tx">内容与素材</span><span class="ar">▾</span>
  </div>
  <div class="nav-sub">
    <div class="nav-it soon"><span>卖点图 / 商品素材</span></div>
    <div class="nav-it soon"><span>多语言文案</span></div>
  </div>

  <div class="nav-grp" data-grp="sys" onclick="navGrp('sys')">
    <span class="ic">⚙</span><span class="tx">系统设置</span><span class="ar">▾</span>
  </div>
  <div class="nav-sub">
    <div class="nav-it soon"><span>数据源与接口</span></div>
    <div class="nav-it soon"><span>人员权限</span></div>
  </div>

  <div class="side-foot">
    <b>美国 · 富皇美运 / 德国 · 盘古</b>
    <span class="sy">数据同步：<span id="sideSync">—</span></span>
  </div>
</aside>

<!-- ==================== 顶部工具栏(面包屑 + 操作) ==================== -->
<div class="topbar">
  <div class="tb-bread"><span class="ico">▣</span><span id="tbTitle">备货看板</span></div>
  <span class="tb-sub" id="tbSub">库存与备货 · 海外仓实时库存与补货建议</span>
  <div class="tb-right">
    <button class="tb-ic" id="btnWhSw" title="美国仓 / 德国仓 数据源切换" onclick="whToggle()">⇆</button>
    <button class="tb-ic" id="btnSide" title="收起 / 展开左侧导航" onclick="sideToggle()">◧</button>
    <span class="who">账号：admin<span class="av">A</span></span>
    <button class="btn" onclick="doLogout()">退出</button>
  </div>
</div>

<div class="content">
<!-- 旧横向 tab 保留为隐藏节点, 脚本与徽标逻辑继续复用 -->
<div class="tabs" style="display:none">
  <span class="tab on" data-t="stock" onclick="switchTab('stock')">备货看板</span>
  <span class="tab" data-t="trace" onclick="switchTab('trace')">出库溯源<span class="tab-badge" id="traceBadge">0</span></span>
  <span class="tab" data-t="pi" onclick="switchTab('pi')">PI &amp; 头程<span class="tab-badge" id="piBadge" style="display:none">0</span></span>
  <span class="tab" data-t="ae" onclick="switchTab('ae')">速卖通订单<span class="tab-badge" id="aeBadge" style="display:none">0</span></span>
  <span id="aeShopWrap" style="display:none;margin-left:10px;align-self:center;white-space:nowrap">
    <span style="font-size:12px;color:var(--sub);margin-right:4px">店铺</span>
    <select id="aeShop" title="按速卖通店铺筛选（当前：迈科深圳，后续可扩展其他店）" style="padding:4px 8px;font-size:12.5px;border:1px solid var(--line);border-radius:6px;background:var(--card2);color:var(--txt)"><option value="">全部店铺</option></select>
  </span>
</div>
<div id="tab-stock">

<div class="wh-bar">
  <span class="wh-lbl">数据源</span>
  <span class="chip on" data-w="us" onclick="switchWh('us')">美国 · 富皇美运</span>
  <span class="chip" data-w="de" id="whDe" onclick="switchWh('de')" style="display:none">德国 · 盘古海外仓</span>
  <span class="wh-note" id="whNote"></span>
</div>

<div class="cards">
  <div class="card blue"><div class="num" data-k="total">${fmt(stats.total)}</div><div class="lbl">SKU 总数</div></div>
  <div class="card green"><div class="num" data-k="withStock">${fmt(stats.withStock)}</div><div class="lbl">有库存 SKU</div></div>
  <div class="card red"><div class="num" data-k="red">${fmt(stats.red)}</div><div class="lbl">紧急缺货</div></div>
  <div class="card orange"><div class="num" data-k="orange">${fmt(stats.orange)}</div><div class="lbl">预警中</div></div>
  <div class="card yellow"><div class="num" data-k="toOrder">${fmt(stats.toOrder)}</div><div class="lbl">建议下单</div></div>
  <div class="card"><div class="num" data-k="totalQty">${fmt(stats.totalQty)}</div><div class="lbl">在库+在途 总件数</div></div>
</div>

<div class="panel">
  <h2>海外仓系统对接状态 <span class="tag">数据实时来自海外仓系统</span></h2>
  <div class="source-line" id="srcLine">
    <span>系统：<b>${esc(source.warehouse)}</b></span>
    <span class="ok">✓ 库存接口已连通（${fmt(source.skuCount)} 个 SKU）</span>
    <span class="ok">✓ 销量接口已连通（累计 ${fmt(source.flowCount)} 件出库流水）</span>
    <span class="kv">接口：${esc(source.api)}</span>
    <span class="kv">最近同步：${esc(source.syncAt)}</span>
  </div>
</div>

<div class="panel">
  <h2>备货参数与逻辑 <span class="tag">统计补货模型 v2</span></h2>
  <div class="formula">
    <div class="f-item"><div class="k">预测日销 D</div><div class="v">${paramObj.w.d7}%×近7天日均 ＋ ${paramObj.w.d30}%×近30天 ＋ ${paramObj.w.d60}%×近60天（多阶段加权移动平均）</div></div>
    <div class="f-item"><div class="k">提前期 L</div><div class="v">生产 ${paramObj.productionDays} 天 ＋ 海运 ${paramObj.shippingDays} 天 = <b>${paramObj.lead} 天</b></div></div>
    <div class="f-item"><div class="k">安全库存 SS</div><div class="v">Z × σ × √L（服务水平 ${(paramObj.serviceLevel * 100).toFixed(0)}% → Z=${paramObj.z.toFixed(2)}，σ=近 ${paramObj.sigmaWindowDays} 天日销标准差，上限 ${paramObj.maxSafetyDays} 天需求）</div></div>
    <div class="f-item"><div class="k">再订货点 ROP</div><div class="v">D × ${paramObj.lead} ＋ SS，低于此值尽快下单</div></div>
    <div class="f-item"><div class="k">目标水位 S*</div><div class="v">D × (${paramObj.cycle}＋${paramObj.lead}) ＋ SS（覆盖一个备货周期到上架）</div></div>
    <div class="f-item"><div class="k">建议补货量 Q</div><div class="v">S* −（在库＋在途），不足才补</div></div>
  </div>
</div>

<div class="charts" id="chartsWrap">
  <div class="chart-card">
    <h3>预警等级分布</h3>
    <p class="sub">全部 SKU 的备货状态占比</p>
    <div class="chart-box"><canvas id="cLevel"></canvas></div>
  </div>
  <div class="chart-card">
    <h3>出库量 Top${topN}（近 ${chartDays} 天）</h3>
    <p class="sub" id="topSub">各 SKU 近期出库件数占比</p>
    <div class="chart-box"><canvas id="cTop"></canvas></div>
  </div>
  <div class="chart-card" style="grid-column:1/-1">
    <div class="dc-head">
      <h3 style="margin:0">日销量走势 &amp; 需求预测（单 SKU）</h3>
      <span class="dc-tools"><span class="dim" style="font-size:11px">SKU</span>
        <select id="dSkuSel" onchange="selDaily()" title="选择要查看的 SKU"></select></span>
    </div>
    <p class="sub" id="dailySub">单 SKU 全历史实际日销（蓝）· 未来 ${dashCfg.forecastDays || 14} 天波动预测（绿虚线，周六周日不发货=0，累积订单并入周一等发货日）· 下方轨道可拖动浏览全部日期</p>
    <div class="chart-box" id="dailyBox" style="height:230px"><canvas id="cDaily"></canvas></div>
    <div class="dc-slider">
      <span id="dWinA" class="mono dim"></span>
      <input type="range" id="dRange" min="0" max="0" value="0" oninput="onDailyRange()" title="拖动浏览全部历史日期">
      <span id="dWinB" class="mono dim"></span>
      <select id="dWin" onchange="onDailyRange()" title="可视窗口宽度">
        <option value="30">30天</option>
        <option value="60">60天</option>
        <option value="90" selected>90天</option>
        <option value="180">180天</option>
        <option value="all">全部</option>
      </select>
    </div>
  </div>
  <div class="chart-card" style="grid-column:1/-1">
    <h3 style="margin:0">备货逻辑明细（<span id="lSkuName" class="mono">—</span>）<span class="tag">统计补货模型 v2</span></h3>
    <div id="logicGrid" class="logic-grid" style="margin-top:10px"></div>
  </div>
  <div class="chart-card">
    <h3>月度出库趋势 &amp; 线性回归预测</h3>
    <p class="sub" id="trendSub">全历史月度出库 + 最小二乘回归趋势线 + 未来 3 个月预测</p>
    <div class="chart-box"><canvas id="cTrend"></canvas></div>
  </div>
</div>

<div class="toolbar">
  <input id="q" type="text" placeholder="搜索 SKU 或商品名称…（点击任意行查看出库趋势与备货明细）">
  <div class="chips" id="chips">
    <span class="chip on" data-f="all">全部</span>
    <span class="chip" data-f="red">紧急</span>
    <span class="chip" data-f="orange">预警</span>
    <span class="chip" data-f="yellow">建议下单</span>
    <span class="chip" data-f="ok">正常</span>
    <span class="chip" data-f="gray">无数据</span>
  </div>
</div>

<div class="tbl-scroll">
<table>
<thead><tr>
  <th>SKU</th><th>商品名称</th><th class="num-r">在库</th><th class="num-r">在途</th><th class="num-r">合计</th>
  <th class="num-r">日均销量</th><th class="num-r">可售天数</th><th class="num-r">安全库存</th><th>状态</th>
  <th class="num-r">再订货点</th><th class="num-r">目标库存</th><th class="num-r">建议补货</th><th>最晚下单日期</th>
</tr></thead>
<tbody id="tbody"></tbody>
</table>
</div>
<div id="stockPager" style="margin-bottom:10px"></div>
<p class="empty" id="empty" style="display:none">没有匹配的 SKU</p>

<footer>
  数据来源：${esc(source.warehouse)} · 富皇美运 OpenAPI（库存快照 + 出库单/库存流水，云端每30分钟自动同步）<br>
  预测日销 D = ${paramObj.w.d7}%×μ7 ＋ ${paramObj.w.d30}%×μ30 ＋ ${paramObj.w.d60}%×μ60（多阶段加权）· 安全库存 SS = Z×σ×√${paramObj.lead}（Z=${paramObj.z.toFixed(2)}，σ=近 ${paramObj.sigmaWindowDays} 天日销标准差）<br>
  最晚下单日期 = 今天 +（可售天数 − ROP折算天数）；预计今日下单，${paramObj.lead} 天后（建议到货日）入仓上架 · 此页面每次数据同步后自动更新
</footer>
</div>

<div id="tab-trace" style="display:none">
  <div class="cards">
    <div class="card blue"><div class="num">${fmt(tOut)}</div><div class="lbl">出库单总数</div></div>
    <div class="card green"><div class="num">${fmt(tMatched)}</div><div class="lbl">已匹配入库批次</div></div>
    <div class="card"><div class="num">${tRate}%</div><div class="lbl">匹配率</div></div>
    <div class="card red"><div class="num">${fmt(tUn)}</div><div class="lbl">未匹配</div></div>
    <div class="card amber"><div class="num">${fmt(tIn)}</div><div class="lbl">入库批次</div></div>
  </div>

  <div class="panel">
    <h2>出库单 → 入库批次（FIFO 先进先出溯源） <span class="tag">数据来自库存流水，每次同步自动更新</span></h2>
    <div class="toolbar">
      <input id="tq" type="text" placeholder="搜索 SKU / 客户参考号(平台订单号) / 出库单号 / 入库单号 / 仓库…（回车或点搜索）" title="输入后按回车或点右侧「搜索」按钮才会筛选">
      <button class="btn small" id="tqBtn" title="点击执行搜索" onclick="tqSearch()">🔍 搜索</button>
      <span class="dt-sep">出库日期</span>
      <input id="tds" class="dt" type="date" title="出库日期(起)">
      <span class="dt-sep">至</span>
      <input id="tde" class="dt" type="date" title="出库日期(止)">
      <button class="btn small" title="导出当前筛选结果为 CSV（可用 Excel 打开）" onclick="exportTraceCsv()">⤓ 导出 CSV</button>
    </div>
    <div class="chips" id="tchips" style="margin-bottom:12px">
      <span class="chip on" data-f="all">全部</span>
      <span class="chip" data-f="unmatched">未匹配</span>
      ${whChips}
    </div>
    <div class="tbl-scroll">
    <table>
      <thead><tr>
        <th>出库单号(DO)</th><th>客户参考号</th><th>SKU</th><th>仓库</th><th class="num-r">数量</th><th>出库时间</th>
        <th>来源入库单号</th><th class="num-r">入库数量</th><th>入库时间</th><th class="num-r">出库重量(kg)</th><th class="num-r">海运费用均摊(元/kg)</th><th class="num-r">头程费用</th><th>状态</th>
      </tr></thead>
      <tbody id="traceTbody"></tbody>
    </table>
    </div>
    <div id="tracePager"></div>
    <p class="empty" id="traceEmpty" style="display:none">没有匹配的出库单</p>
    <div class="trace-tip">
      <b>怎么读这张表：</b>OMS 出库单详情本身不显示来源入库单，这里按行业标准 <b>FIFO（先进先出）</b>推算——同一 SKU 在同一仓库内，出库按时间顺序从<b>最早入库的批次</b>开始扣减。一笔出库跨两个批次时会拆成两行分别记录。<b>客户参考号</b>为出库单在 FDR 系统的参考号（一般对应平台订单号），可用于对账；匹配到的<b>入库单号</b>就是你核算海运费时该对应到的那批货。
    </div>
  </div>

  <div class="panel">
    <h2>入库批次消耗汇总 <span class="tag">出口单号/柜号来自 OMS · 头程费用来自 PI/批次录入</span></h2>
    <div class="tbl-scroll">
    <table>
      <thead><tr>
        <th>SKU</th><th>仓库</th><th>入库单号</th><th>出口单号</th><th>柜号/货运跟踪号</th><th>入库日期</th><th class="num-r">入库总量</th><th class="num-r">已出库消耗</th><th class="num-r">剩余库存</th><th>消耗率</th><th class="num-r">已出库重量(kg)</th><th class="num-r">海运费用均摊(元/kg)</th><th class="num-r">头程费用</th>
      </tr></thead>
      <tbody id="inTbody"></tbody>
    </table>
    </div>
    <div id="inPager"></div>
    <div class="trace-note">
      <b>头程费用说明（重量口径）：</b>「海运费用均摊」= 关联该入库单的头程批次总费用 ÷ 该批总毛重（<b>元/kg</b>）；「头程费用」= 海运费用均摊 × 本行<b>已出库重量</b>，其中已出库重量 = <b>海外仓 WMS 的 SKU 单件重量 × 出库件数</b>（首次同步后自动带出，无档案的 SKU 按该批次平均单重估算并标注「估算」）。费用来自「PI &amp; 头程」页录入的头程发货批次（本机双击 <b>pi-entry.bat</b> 在线填写，保存后本页自动更新）。<br>
      <b>出口单号说明：</b>「出口单号」为 OMS 入库订单上登记的出口单号（整柜入库时通常为<b>集装箱柜号</b>），「柜号/货运跟踪号」为集装箱柜号或物流跟踪号，两者用于定位该批货对应的海运提单与费用账单，也用于与头程批次自动关联。<br>
      <b>未匹配说明：</b>${fmt(tUn)} 单未匹配，多为系统启用前的<b>期初库存</b>（早于最早入库流水）或仓库历史数据缺失；费用显示 — 的入库批次表示尚未录入头程费用或未关联入库单号。
    </div>
  </div>
</div>

<div id="tab-pi" style="display:none">
  <div class="cards" id="piCards"></div>

  <div class="panel" id="piGuide">
    <h2>PI &amp; 头程费用 数据入口 <span class="tag">直接在本页录入</span></h2>
    <div id="entrySt" class="entry-st ro"><span class="dot"></span><span id="entryStTxt">正在检测本机录入服务…</span></div>
    <div class="tagline">
      <b>录入：</b>在下方「PI 单列表」点 <b>＋ 新增 PI 单</b>（记录每次备货的形式发票与产品成本单价，支持<b>含税/未税口径 + 税率</b>，自动折算两种金额）；在「头程发货批次」点 <b>＋ 新增发货批次</b>（<b>手动选择关联的 PI 单号</b>——一个 PI 可分多次发货；<b>一柜/一个入库单也可混装多个 PI</b>，把单号用「、」一起填上即可，每行产品标注归属 PI；记录 SKU 数量 / 总毛重 / 总费用，并填写或<b>自动匹配入库单号</b>）。未发货的 PI 在列表中显示「待发货」状态。已录数据可随时<b>编辑 / 删除</b>。<br>
      <b>汇总：</b>本页自动汇总每张入库单的头程费用。每批发货均按 <b>总费用 ÷ 总毛重 折算「海运费用均摊 XX 元/kg」</b>（重量口径，物流按重量计费时用它核算），「出库溯源」据此按 <b>元/kg × 出库重量</b> 核算每单头程成本（出库重量取自海外仓 WMS 的 SKU 重量档案）。<b>均摊只算头程运费，不含入库费用（卸货费）</b>。
    </div>
  </div>

  <div class="panel" id="piFilesPanel">
    <h2>PI 表格库 <span class="tag">上传自制 PI 表格归档：备货海外仓 / 样品单</span>
      <span class="hd-right">
        <button class="btn primary small pi-add-btn" onclick="pfPick('stock')">⬆ 上传备货海外仓 PI</button>
        <button class="btn small pi-add-btn" style="margin-left:8px" onclick="pfPick('sample')">⬆ 上传样品单 PI</button>
      </span>
    </h2>
    <div class="ae-viewbar" style="margin-bottom:10px">
      <div class="ae-vtab active" id="pfTabStock" onclick="pfTab('stock')">备货海外仓 PI <span class="tag" id="pfCntStock"></span></div>
      <div class="ae-vtab" id="pfTabSample" onclick="pfTab('sample')">样品单 PI <span class="tag" id="pfCntSample"></span></div>
    </div>
    <div class="toolbar" style="margin-bottom:8px"><span style="color:var(--sub);font-size:12px" id="pfHint">支持 .xlsx / .xls / .csv，单文件 ≤ 10MB；上传后可随时在线预览内容或下载。</span><input type="file" id="pfInput" accept=".xlsx,.xls,.csv" style="display:none" onchange="pfUpload()"></div>
    <div class="tbl-scroll">
    <table>
      <thead><tr>
        <th>文件名</th><th class="num-r">大小</th><th>上传时间</th><th>工作表</th><th>操作</th>
      </tr></thead>
      <tbody id="pfTbody"></tbody>
    </table>
    </div>
    <p class="empty" id="pfEmpty" style="display:none">该分类还没有上传 PI 表格，点右上角「⬆ 上传」按钮选择文件。</p>
  </div>

  <div class="panel" id="piListPanel">
    <h2>PI 单列表 <span class="tag">每次备货一张，记录产品成本单价</span>
      <span class="hd-right"><button class="btn primary small pi-add-btn" onclick="piAdd()">＋ 新增 PI 单</button></span>
    </h2>
    <div class="toolbar">
      <input id="piq" type="text" placeholder="搜索 PI 单号 / SKU / 供应商…">
    </div>
    <div class="tbl-scroll">
    <table>
      <thead><tr>
        <th>PI 单号</th><th>日期</th><th>供应商</th><th>币种</th><th class="num-r">产品数</th><th class="num-r">备货数量</th><th class="num-r">含税金额</th><th class="num-r">未税金额</th><th class="num-r">税率</th><th class="num-r">发货批次</th><th>状态</th><th>操作</th>
      </tr></thead>
      <tbody id="piTbody"></tbody>
    </table>
    </div>
    <div id="piPager"></div>
    <p class="empty" id="piEmpty" style="display:none">还没有 PI 单，点右上角「＋ 新增 PI 单」录入。</p>
  </div>

  <div class="panel">
    <h2>头程发货批次 <span class="tag">头程均摊按重量(元/kg)核算 · 不含卸货费</span>
      <span class="hd-right"><span class="row-note" id="pbSkuWAt" style="margin-right:8px"></span><button class="btn small" onclick="skuWRefresh()">⟳ 同步 SKU 重量/尺寸</button><button class="btn primary small pi-add-btn" onclick="batchAdd()">＋ 新增发货批次</button></span>
    </h2>
    <div class="toolbar">
      <input id="pbq" type="text" placeholder="搜索 PI 单号 / 出口单号 / 柜号 / 跟踪号 / 入库单号…">
    </div>
    <div class="tbl-scroll">
    <table class="pb-tbl">
      <thead><tr>
        <th>PI 单号</th><th>批次</th><th>目的国/仓库</th><th>发货日期</th><th class="num-r">件数</th><th class="num-r">总毛重<br>(kg)</th><th class="num-r">头程总费用</th><th class="num-r">头程均摊费用<br>(元/kg)</th><th>柜号 / 货运跟踪号</th><th>入库单号</th><th>入库日期</th><th class="num-r">卸货费</th><th>方式</th><th>头程物流商</th><th>关联状态</th><th class="op-th">操作</th>
      </tr></thead>
      <tbody id="pbTbody"></tbody>
    </table>
    </div>
    <div id="pbPager"></div>
    <p class="empty" id="pbEmpty" style="display:none">还没有发货批次，点右上角「＋ 新增发货批次」录入。</p>
  </div>

  <div class="panel">
    <h2>均摊口径说明 <span class="tag">只算头程运费 · 不含卸货费</span></h2>
    <p class="pi-gap" style="margin-bottom:6px">口径：<b>头程均摊费用（元/kg）= 该批次头程总费用 ÷ 该批总毛重</b>；出库溯源按 <b>「均摊成本(元/kg) × 出库重量(kg)」</b> 核算每单头程费——出库重量取自<b>海外仓 WMS 的 SKU 重量档案</b>（每件重量 × 出库件数，各 SKU 单件重量/尺寸见批次<b>编辑窗口</b>，可用批次表右上角「⟳ 同步 SKU 重量/尺寸」刷新）。<b style="color:#e8a24e">以上只按头程运费计算，不含卸货费</b>——卸货费单独列示（<b>已接通富皇 OMS 后台账单自动同步</b>，按入库单号对应；未覆盖的单可手填），由业务按需手动分摊，不参与任何均摊。成本单价见 PI 单明细（可点击 PI 单号展开查看）。「关联状态」表示该批次入库单号是否已出现在 FDR 库存流水的入库批次里（溯源可用）。</p>
  </div>
</div>

<div id="tab-ae" style="display:none">
  <div class="cards" id="aeCards"></div>

  <div class="panel" id="aeOv">
    <h2>经营总览 <span class="tag" id="aeOvTag">按销售日期 · 全部店铺合计</span></h2>
    <p class="pi-gap" id="aeOvNote" style="margin-bottom:12px"></p>
    <div id="aeOvToday" style="display:grid;grid-template-columns:repeat(auto-fit,minmax(230px,1fr));gap:12px;margin-bottom:16px"></div>
    <div class="cards" id="aeOvKpis" style="margin-bottom:16px;grid-template-columns:repeat(auto-fit,minmax(165px,1fr))"></div>
    <p style="margin:2px 0 6px;font-weight:600;font-size:12.5px">每日销量 &amp; 销售额趋势 <span style="font-weight:400;color:var(--sub)">（逐日连续，无销售日期=0；日期滑轨可平移浏览历史）</span></p>
    <div class="chart-box" style="height:300px" id="aeOvDailyBox"><canvas id="aeOvDaily"></canvas></div>
    <div class="toolbar" id="aeOvTools" style="margin-top:9px;margin-bottom:14px">
      <span class="dt-sep">窗口</span>
      <select id="aeOvWin" onchange="aeOvApplyWin()" title="显示多少天的趋势">
        <option value="all" selected>全部日期</option><option value="30">近 30 天</option><option value="60">近 60 天</option><option value="90">近 90 天</option><option value="180">近 180 天</option>
      </select>
      <input type="range" id="aeOvRange" min="0" max="0" value="0" disabled oninput="aeOvApplyWin()" title="左右拖动浏览更早/更晚日期" style="flex:1 1 200px;max-width:360px">
      <span class="mono" id="aeOvWinA" style="font-size:11.5px;color:var(--sub)"></span><span id="aeOvWinB" class="mono" style="font-size:11.5px;color:var(--sub)"></span>
    </div>
    <div style="display:flex;gap:14px;flex-wrap:wrap;align-items:flex-start;margin-top:2px">
      <div style="flex:1 1 520px;min-width:330px">
        <p style="margin:0 0 6px;font-weight:600;font-size:12.5px">各 SKU 月度出货量 <span style="font-weight:400;color:var(--sub)">（分组柱=每月出货件数，一色一 SKU；悬停查看销售额/订单数）</span></p>
        <div class="chart-box" style="height:255px" id="aeOvSkuBox"><canvas id="aeOvSku"></canvas></div>
      </div>
      <div style="flex:1 1 460px;min-width:330px">
        <p style="margin:0 0 6px;font-weight:600;font-size:12.5px">各 SKU × 月度出货明细</p>
        <div class="tbl-scroll" style="max-height:255px">
        <table>
          <thead id="aeOvSkuHd"></thead>
          <tbody id="aeOvSkuTb"></tbody>
        </table>
        </div>
      </div>
    </div>
  </div>

  <div class="panel" id="aeSheet">
    <h2>速卖通订单 · 智能表格 <span class="tag">点单元格直接编辑，回车保存；利润自动核算</span>
      <span class="hd-right">
        <button class="btn small ae-export-btn" onclick="aeExport()" title="导出带公式的 Excel：利润/毛利率/合计均为真实公式，财务可直接二次核对">⬇ 导出 Excel（带公式）</button>
        <button class="btn primary small ae-add-btn" onclick="aeAdd()">＋ 新增订单</button>
      </span>
    </h2>
    <div id="aeEntrySt" class="entry-st ro"><span class="dot"></span><span>录入服务状态与「PI &amp; 头程」一致（共用同一服务）</span></div>

    <div class="ae-viewbar">
      <span class="ae-vtab active" data-v="detail" onclick="aeSetView('detail')">☰ 订单明细</span>
      <span class="ae-vtab" data-v="month" onclick="aeSetView('month')">📅 月度利润汇总</span>
    </div>

    <div id="aeDetailView">
      <div class="toolbar">
        <input id="aeq" type="text" placeholder="搜索订单号 / 店铺 / SKU / 仓库 / 备注…">
        <span class="dt-sep">月份</span>
        <select id="aeMonth" title="按订单日期月份筛选"><option value="">全部月份</option></select>
        <span class="dt-sep" id="aeStSep" style="display:none">状态</span>
        <select id="aeSt" style="display:none" title="到账状态筛选">
          <option value="">全部状态</option><option value="已放款">已放款</option><option value="预估">预估</option>
        </select>
        <span class="ae-cnt" id="aeCnt"></span>
      </div>
      <div class="tbl-scroll" style="max-height:70vh">
      <table class="ae-grid">
        <thead><tr>
          <th class="rowno">#</th>
          <th>日期</th><th>订单号</th><th>店铺</th><th>产品SKU</th><th>仓库</th><th class="num-r">数量</th><th class="num-r">销售金额</th><th class="num-r">佣金</th>
          <th class="num-r">预计可得</th><th class="num-r">平台营销费</th><th class="num-r">头程费用</th><th class="num-r">上架费$</th><th class="num-r">仓储费$</th><th class="num-r">出库+尾程$</th>
          <th class="num-r">到账金额</th><th>到账时间</th><th class="num-r">成本总额$</th><th class="num-r">汇率</th>
          <th class="num-r">利润</th><th class="num-r">毛利率</th><th>状态</th><th>备注</th><th>操作</th>
        </tr></thead>
        <tbody id="aeTbody"></tbody>
        <tfoot id="aeFoot"></tfoot>
      </table>
      </div>
      <div id="aePager"></div>
      <p class="empty" id="aeEmpty" style="display:none">还没有速卖通订单，点右上角「＋ 新增订单」录入第一单。</p>
      <div class="tagline">
        <b>编辑：</b>直接点击单元格修改，回车或点别处即保存；订单号是唯一键，新增后不可改。<br>
        <b>币种口径：</b>¥＝人民币（销售金额/佣金/预计可得/平台营销费/头程费用/到账金额）；$＝美元（上架费/仓储费/出库+尾程/成本总额，利润公式中×汇率折算）。<b>核算口径（与你的 Excel 一致）：</b>每单利润 = 到账金额 − 头程费用 −（上架费 + 仓储费 + 出库尾程 + 产品成本总额）× 汇率；未放款单按「预计可得 − 平台营销费用」估算。毛利率 = 利润 ÷ 销售金额。<br>
        <b>导出：</b>「导出 Excel（带公式）」生成给财务的核对表 —— 利润 / 毛利率 / 月度汇总全部是<b>真实 Excel 公式</b>（非写死的数值），财务改动任何费用或汇率后自动重算，可直接二次核对。
      </div>
    </div>

    <div id="aeMonthView" style="display:none">
      <div class="tbl-scroll">
      <table>
        <thead><tr>
          <th>月份</th><th class="num-r">订单数</th><th class="num-r">件数</th><th class="num-r">销售金额</th><th class="num-r">到账金额</th>
          <th class="num-r">平台营销费</th><th class="num-r">头程运费</th><th class="num-r">海外仓费用<br><span class="row-note">上架+仓储+尾程</span></th><th class="num-r">产品成本</th>
          <th class="num-r">净利润</th><th class="num-r">毛利率</th>
        </tr></thead>
        <tbody id="aeMonthTbody"></tbody>
      </table>
      </div>
      <p class="empty" id="aeMonthEmpty" style="display:none">暂无订单数据：点「＋ 新增订单」逐单录入。</p>
    </div>
  </div>
</div>
</div><!-- /.content -->

<!-- 录入表单弹窗 (PI / 头程批次) -->
<div class="modal-mask" id="fmModal"><div class="modal" id="fmBox"></div></div>

<div class="modal-mask" id="modal">
  <div class="modal">
    <button class="close" onclick="closeModal()">×</button>
    <h2 id="mTitle"></h2>
    <div class="detail-grid" id="mGrid"></div>
    <div id="mChartWrap">
      <p class="trend-note" id="mNote"></p>
      <div class="chart-box" style="height:240px"><canvas id="cSku"></canvas></div>
    </div>
  </div>
</div>

<script>${chartJs}</script>
<script>
var ROWS = ${dataJson};
var params = ${params};
var CHARTS = ${chartsJson};
var STATS = ${statsJson};
var DEVIEW = ${deJson};
var AUTH = ${authJson};
var SOURCE = ${sourceJson};
var TRACE = ${traceJson};
var PIF = ${pifJson};
var AE = ${aeJson};
var DASH_VERSION = 'pi-v2';
params.chartTopN = ${topN};
var LEVEL = {red:'lv-red',orange:'lv-orange',yellow:'lv-yellow',ok:'lv-green',gray:'lv-gray'};
var LABEL = {red:'紧急',orange:'预警',yellow:'建议下单',ok:'正常',gray:'无数据'};

/* ---------- 登录 ---------- */
function sha256(ascii){
  function rightRotate(v,a){return(v>>>a)|(v<<(32-a))}
  var maxWord=Math.pow(2,32),L='length',i,j,res='',words=[],abit=ascii[L]*8;
  var hash=sha256.h=sha256.h||[],k=sha256.k=sha256.k||[],pc=k[L],comp={};
  for(var c=2;pc<64;c++){if(!comp[c]){for(i=0;i<313;i+=c)comp[i]=c;hash[pc]=(Math.pow(c,.5)*maxWord)|0;k[pc++]=(Math.pow(c,1/3)*maxWord)|0}}
  ascii+='\\x80';while(ascii[L]%64-56)ascii+='\\x00';
  for(i=0;i<ascii[L];i++){j=ascii.charCodeAt(i);if(j>>8)return '';words[i>>2]|=j<<((3-i)%4)*8}
  words[words[L]]=((abit/maxWord)|0);words[words[L]]=abit;
  for(j=0;j<words[L];){var w=words.slice(j,j+=16),oh=hash.slice(0,8);hash=hash.slice(0,8);
    for(i=0;i<64;i++){var w15=w[i-15],w2=w[i-2],a0=hash[0],e=hash[4];
      var t1=hash[7]+(rightRotate(e,6)^rightRotate(e,11)^rightRotate(e,25))+((e&hash[5])^((~e)&hash[6]))+k[i]+(w[i]=(i<16)?w[i]:(w[i-16]+(rightRotate(w15,7)^rightRotate(w15,18)^(w15>>>3))+w[i-7]+(rightRotate(w2,17)^rightRotate(w2,19)^(w2>>>10)))|0);
      var t2=(rightRotate(a0,2)^rightRotate(a0,13)^rightRotate(a0,22))+((a0&hash[1])^(a0&hash[2])^(hash[1]&hash[2]));
      hash=[(t1+t2)|0].concat(hash);hash[4]=(hash[4]+t1)|0}
    for(i=0;i<8;i++)hash[i]=(hash[i]+oh[i])|0}
  for(i=0;i<8;i++){for(j=3;j+1;j--){var b=(hash[i]>>(j*8))&255;res+=((b<16)?0:'')+b.toString(16)}}
  return res;
}
function doLogin(){
  var u=document.getElementById('u').value.trim(),p=document.getElementById('p').value;
  if(AUTH.enabled && (sha256(u)!==AUTH.usernameHash || sha256(p)!==AUTH.passHash)){
    document.getElementById('loginErr').textContent='账号或密码错误，请重试';return;
  }
  var ph=sha256(p); /* 仅存哈希: 供登录过期时静默自动重登 */
  var rm=document.getElementById('rm').checked;
  if(rm){
    try{localStorage.setItem('dash_ok','1');localStorage.setItem('dash_user',u);localStorage.setItem('dash_pass',ph);}catch(e){}
    sessionStorage.removeItem('dash_ok');
  }else{
    sessionStorage.setItem('dash_ok','1');sessionStorage.setItem('dash_user',u);sessionStorage.setItem('dash_pass',ph);
    localStorage.removeItem('dash_ok');
  }
  fetchToken(rm); /* 向后端换写令牌(云端/本地服务均支持; 无后端时静默忽略) */
  document.body.classList.remove('locked');
  document.getElementById('login').style.display='none';
  document.getElementById('app').style.display='block';
  setTimeout(bootTab,50);
}
function doLogout(){try{localStorage.removeItem('dash_ok');localStorage.removeItem('dash_user');localStorage.removeItem('dash_pass');localStorage.removeItem('dash_token');}catch(e){}sessionStorage.removeItem('dash_ok');sessionStorage.removeItem('dash_user');sessionStorage.removeItem('dash_pass');sessionStorage.removeItem('dash_token');location.reload()}
/* 默认上锁: 未通过校验前隐藏工作台外壳, 避免登录页旁露出左侧导航 */
document.body.classList.add('locked');
if(!AUTH.enabled){document.body.classList.remove('locked');document.getElementById('login').style.display='none';document.getElementById('app').style.display='block';}
else if(localStorage.getItem('dash_ok')||sessionStorage.getItem('dash_ok')){document.body.classList.remove('locked');document.getElementById('login').style.display='none';document.getElementById('app').style.display='block';setTimeout(bootTab,50);}
else{
  var savedUser='';
  try{savedUser=localStorage.getItem('dash_user')||sessionStorage.getItem('dash_user')||'';}catch(e){}
  if(savedUser){document.getElementById('u').value=savedUser;document.getElementById('p').focus();}
  else{document.getElementById('u').focus();}
}
document.getElementById('p').addEventListener('keydown',function(e){if(e.key==='Enter')doLogin()});

/* ---------- 图表 ---------- */
/* 登录/加载完成后: 先绘备货看板图表, 再恢复上次停留的 tab(如 PI/速卖通), 避免每次刷新跳回首屏 */
function bootTab(){
  /* 恢复上次的左栏收起状态 + 同步顶栏数据源按钮 */
  try{ if(localStorage.getItem('dash_side')==='1'){ document.body.classList.add('side-mini'); var vw=document.querySelector('.side-brand .vw'); if(vw)vw.textContent='»'; } }catch(e){}
  var el=document.getElementById('sideSync'); if(el)el.textContent='${esc(syncAt)}';
  try{ initCharts(); }catch(e){}
  var w=''; try{ w=localStorage.getItem('dash_wh')||''; }catch(e){}
  if(w==='de'&&VIEWS.de){ try{ switchWh('de'); }catch(e){} }
  else { var n=document.getElementById('whNote'); if(n)n.textContent='富皇美运 4 仓聚合 · 库存+出库流水'; }
  var t=''; try{ t=localStorage.getItem('dash_tab')||sessionStorage.getItem('dash_tab')||''; }catch(e){}
  syncNav(['trace','pi','ae'].indexOf(t)>=0?t:'stock');
  if(['trace','pi','ae'].indexOf(t)>=0){ try{ switchTab(t); }catch(e){} }
}
var cLevel=null,cTop=null,cTrend=null,cDaily=null,cSku=null;
var LEVEL_COLORS={red:'#e06060',orange:'#e5a84e',yellow:'#d9b95c',ok:'#4fae62',gray:'#8b97b3'};
/* 前端最小二乘线性回归 */
function linreg2(vals){var n=vals.length;if(n<2)return null;var sx=0,sy=0,sxy=0,sxx=0;for(var i=0;i<n;i++){sx+=i;sy+=vals[i];sxy+=i*vals[i];sxx+=i*i}var dn=n*sxx-sx*sx;if(!dn)return null;var b=(n*sxy-sx*sy)/dn;return{a:(sy-b*sx)/n,b:b}}
var chartsReady=false;
/* 深色主题: 统一 Chart.js 的全局默认色(坐标轴/网格/图例/提示), 避免逐图重复设置 */
function applyDarkChartDefaults(){
  if(typeof Chart==='undefined'||!Chart.defaults)return;
  try{
    var AX='#8b97b3', GRID='rgba(255,255,255,.07)';
    Chart.defaults.color=AX;
    Chart.defaults.borderColor=GRID;
    if(Chart.defaults.scale&&Chart.defaults.scale.grid){ Chart.defaults.scale.grid.color=GRID; Chart.defaults.scale.grid.borderColor=GRID; }
    if(Chart.defaults.scale&&Chart.defaults.scale.ticks){ Chart.defaults.scale.ticks.color=AX; }
    if(Chart.defaults.plugins&&Chart.defaults.plugins.legend&&Chart.defaults.plugins.legend.labels){ Chart.defaults.plugins.legend.labels.color=AX; }
    if(Chart.defaults.plugins&&Chart.defaults.plugins.tooltip){
      Chart.defaults.plugins.tooltip.backgroundColor='#1e2740';
      Chart.defaults.plugins.tooltip.titleColor='#e6ebf5';
      Chart.defaults.plugins.tooltip.bodyColor='#c3ccdf';
      Chart.defaults.plugins.tooltip.borderColor='#33405e';
      Chart.defaults.plugins.tooltip.borderWidth=1;
    }
  }catch(e){}
}
function initCharts(){
  if(chartsReady)return; chartsReady=true;
  if(typeof Chart==='undefined'){return;}
  applyDarkChartDefaults();
  // 1) 预警等级环形图
  var ld=CHARTS.levelDist;
  var lv=Chart.getChart('cLevel'); if(lv)lv.destroy();
  cLevel=new Chart(document.getElementById('cLevel'),{type:'doughnut',
    data:{labels:['紧急缺货','预警中','建议下单','正常'],
      datasets:[{data:[ld.red,ld.orange,ld.yellow,Math.max(0,ld.ok)],backgroundColor:[LEVEL_COLORS.red,LEVEL_COLORS.orange,LEVEL_COLORS.yellow,LEVEL_COLORS.ok],borderWidth:2,borderColor:'#141a28'}]},
    options:{responsive:true,maintainAspectRatio:false,plugins:{legend:{position:'right',labels:{boxWidth:12,font:{size:12}}}}}});
  // 2) 出库Top10饼图(近chartDays天, 无数据自动降级全历史)
  var tt=CHARTS.top10;
  document.getElementById('topSub').textContent=CHARTS.topByHistory?('近 '+CHARTS.chartDays+' 天无出库记录，已自动切换为全历史累计出库占比'):('各 SKU 近 '+CHARTS.chartDays+' 天出库件数占比');
  if(tt.length){
    var tc=Chart.getChart('cTop'); if(tc)tc.destroy();
    var palette=['#4d8ff0','#2ec4a6','#7c5cff','#e5a84e','#48c9e6','#5fbf7f','#d97bb0','#9aa8f0','#e0c060','#e06060'];
    cTop=new Chart(document.getElementById('cTop'),{type:'pie',
      data:{labels:tt.map(function(x){return x.sku+(x.name?(' '+x.name):'')}),
        datasets:[{data:tt.map(function(x){return x.qty}),backgroundColor:palette.slice(0,tt.length),borderWidth:1,borderColor:'#141a28'}]},
      options:{responsive:true,maintainAspectRatio:false,plugins:{legend:{position:'right',labels:{boxWidth:12,font:{size:11}}},tooltip:{callbacks:{label:function(ctx){return ctx.label+': '+ctx.parsed+' 件 ('+ctx.parsed+' 件出库)'}}}}}});
  } else {
    document.getElementById('cTop').parentNode.innerHTML='<p class="empty" style="padding:70px 0">近 '+CHARTS.chartDays+' 天暂无出库记录<br>正式环境接入真实订单后自动显示</p>';
  }
  // 3) 月度趋势 + 线性回归
  var mt=CHARTS.monthly;
  if(mt.length>=2){
    var tc2=Chart.getChart('cTrend'); if(tc2)tc2.destroy();
    var labels=mt.map(function(x){return x.m});
    var main={label:'月度出库',data:mt.map(function(x){return x.qty}),borderColor:'#4d8ff0',backgroundColor:'rgba(77,143,240,.16)',fill:true,tension:.25,pointRadius:3};
    var ds=[main];
    var reg=CHARTS.monthlyReg;
    if(reg){
      // 回归线(仅覆盖历史区间起止)
      var histYs=mt.map(function(x){return Math.max(0,Math.round(reg.intercept+reg.slope*(mt.indexOf(x))))});
      ds.push({label:'线性回归趋势',data:histYs,borderColor:'#e06060',borderDash:[6,4],borderWidth:2,pointRadius:0,fill:false});
      // 预测(虚线延伸)
      var fc=reg.forecast;
      var fcLabels=labels.concat(fc.map(function(x){return x.m}));
      var fcData=labels.map(function(){return null}).concat(fc.map(function(x){return x.qty}));
      ds.push({label:'未来3月预测',data:fcData,borderColor:'#2ec4a6',borderDash:[3,3],borderWidth:2,pointRadius:4,pointStyle:'rectRot',fill:false});
      labels=fcLabels;
    }
    var slopeTxt=reg?(' · 斜率 b='+(reg.slope>=0?'+':'')+reg.slope.toFixed(2)+(reg.slope>=0?'（上行）':'（下行）')):'';
    document.getElementById('trendSub').textContent='全历史月度出库 · 最小二乘回归'+slopeTxt+' · 未来3个月预测';
    cTrend=new Chart(document.getElementById('cTrend'),{type:'line',
      data:{labels:labels,datasets:ds},
      options:{responsive:true,maintainAspectRatio:false,interaction:{mode:'index',intersect:false},
        scales:{y:{beginAtZero:true,ticks:{precision:0}}},
        plugins:{legend:{labels:{boxWidth:14,font:{size:11}}},tooltip:{callbacks:{label:function(ctx){return (ctx.dataset.label||'')+': '+ctx.parsed.y+' 件'}}}}}});
  } else {
    document.getElementById('cTrend').parentNode.innerHTML='<p class="empty" style="padding:70px 0">暂无出库流水数据<br>正式环境接入后自动显示趋势与回归预测</p>';
  }
  // 4) 单 SKU 日销量走势(全历史) + 未来 fcDays 模型预测 + 备货逻辑明细
  initDaily();
}

/* ---------- 单 SKU 走势 & 备货逻辑 ---------- */
var dCur=null,dStart=0;
function dRow(sku){ for(var i=0;i<ROWS.length;i++){ if(String(ROWS[i].sku)===String(sku)) return ROWS[i]; } return null; }
function dData(){ var o=(CHARTS.skuDaily||{})[dCur]; return o?o:{dates:[],hist:[],pred:[],rate:0}; }
function dFmtDate(y){ return String(y).slice(5); }
function dSkuLabel(){
  var s=document.getElementById('dSkuSel'); if(!s)return;
  var html='';
  for(var i=0;i<ROWS.length;i++){
    var r=ROWS[i];
    html+='<option value="'+esc2(r.sku)+'"'+(dCur===String(r.sku)?' selected':'')+'>'+esc2(r.sku)+(r.name?(' · '+esc2(r.name)):'')+'</option>';
  }
  s.innerHTML=html;
}
function selDaily(){ dCur=String(document.getElementById('dSkuSel').value); dStart=0; drawDaily(); }
function renderLogic(){
  var box=document.getElementById('logicGrid'); if(!box)return;
  var r=dRow(dCur);
  var nm=document.getElementById('lSkuName');
  if(!r){ if(nm)nm.textContent='—'; box.innerHTML=''; return; }
  if(nm)nm.textContent=r.sku+(r.name?(' · '+r.name):'');
  var w=params.w||{d7:40,d30:30,d60:30};
  var L=params.lead||0, R=params.cycle||0;
  var rate=r.rate||0;
  var pos=r.position||0;
  var lvCls=(r.level==='red'||r.level==='orange')?'bad':(r.level==='yellow'?'warn':'');
  function it(k,v,cls){ return '<div class="lg '+(cls||'')+'"><span class="k">'+k+'</span><span class="v">'+v+'</span></div>'; }
  var h='';
  // 1. 预测日销 D (主公式)
  h+=it('预测日销 D','= '+fmt(rate,2)+' 件/天'+(r.level?'':''));
  // 2-4. μ7/μ30/μ60 权重
  h+=it('近7天日均 μ7','<small>权重'+w.d7+'%</small> '+fmt(r.mu7,2));
  h+=it('近30天日均 μ30','<small>权重'+w.d30+'%</small> '+fmt(r.mu30,2));
  h+=it('近60天日均 μ60','<small>权重'+w.d60+'%</small> '+fmt(r.mu60,2));
  // 5. σ
  h+=it('日销波动 σ','近'+params.sigmaWindowDays+'天 '+fmt(r.sigma,2));
  // 6. 服务水平/Z
  h+=it('服务水平 / Z',((r.serviceLevel*100)||95).toFixed(0)+'% / Z='+fmt(r.z,2));
  // 7. SS
  h+=it('安全库存 SS=Zσ√L',(rate>0)?(fmt(r.ss)+' 件<small>≈'+fmt(r.ssDays,1)+'天</small>'):'—');
  // 8. ROP
  h+=it('再订货点 ROP=D×L+SS',(rate>0)?(fmt(r.rop)+' 件<small>≈'+fmt(r.ropDays,1)+'天</small>'):'—');
  // 9. S*
  h+=it('目标水位 S*=D×(R+L)+SS',(rate>0)?(fmt(r.orderUpTo)+' 件'):'—');
  // 10. 当前库存
  h+=it('在库＋在途',fmt(r.onHand)+' + '+fmt(r.inTransit)+' = <b style="font-size:14px">'+fmt(pos)+'</b>');
  // 11. 可售天数
  h+=it('可售天数',r.rate>0?fmt(r.coverDays,1)+' 天':(pos>0?'∞':'0'));
  // 12. 建议补货 Q
  h+=it('建议补货 Q=max(0,S*−pos)',r.suggest>0?('<b style="color:#f07575">'+fmt(r.suggest)+' 件</b>'):(r.level==='red'||r.level==='orange'?'0':'充足'));
  // 13. 状态
  h+=it('当前状态', '<span class="badge '+LEVEL[r.level]+'">'+LABEL[r.level]+'</span>', lvCls);
  // 14. 星期规律系数(波动预测用)
  var sd=dData();
  if(sd&&sd.wf&&rate>0){
    var wn=['日','一','二','三','四','五','六'], ws='';
    for(var wi=0;wi<7;wi++){
      if(wi===0||wi===6){ ws+=(wi?' ':'')+'周'+wn[wi]+'·不发货(0)'; }
      else{ ws+=(wi?' ':'')+'周'+wn[wi]+'×'+sd.wf[wi]; }
    }
    h+='<div class="lg" style="grid-column:1/-1"><span class="k">星期规律系数（周六周日不发货=0，累积订单并入发货日·周一通常最高；工作日系数均值=1.4×D，整周总量=7D）</span><span class="v" style="font-size:12px">'+ws+'</span></div>';
  }
  box.innerHTML=h;
}
function drawDaily(){
  var dd=Chart.getChart('cDaily'); if(dd)dd.destroy();
  var o=dData();
  var sub=document.getElementById('dailySub');
  var histDates=o.dates||[], hist=o.hist||[], pred=o.pred||[];
  var fcN=pred.length;
  var fcAll=CHARTS.fcDates||[];
  var labels=histDates.map(dFmtDate);
  for(var i=0;i<fcN;i++) labels.push((fcAll[i]||'').slice(5));
  var total=labels.length;
  renderLogic();
  var wrap=document.getElementById('dailyBox');
  if(!total){
    if(sub)sub.textContent='SKU '+dCur+'：暂无历史出库记录，模型预测日销 D='+fmt(o.rate,2)+' 件/天';
    if(wrap)wrap.innerHTML='<p class="empty" style="padding:52px 0">该 SKU 暂无历史出库数据</p>';
    var r0=document.getElementById('dRange'); if(r0){r0.min=0;r0.max=0;r0.value=0;r0.disabled=true;}
    var sA=document.getElementById('dWinA'),sB=document.getElementById('dWinB');
    if(sA)sA.textContent=''; if(sB)sB.textContent='';
    return;
  }
  if(wrap&&!wrap.querySelector('#cDaily'))wrap.innerHTML='<canvas id="cDaily"></canvas>';
  var cv=document.getElementById('cDaily');
  var histDs={label:'每日实际出库',data:hist,borderColor:'#4d8ff0',backgroundColor:'rgba(77,143,240,.16)',fill:true,tension:.25,pointRadius:hist.length>220?0:1.4};
  var ds=[histDs];
  if(fcN){
    var nullPad=hist.map(function(){return null});
    ds.push({label:'未来'+fcN+'天波动预测',data:nullPad.concat(pred),borderColor:'#2ec4a6',borderDash:[4,3],borderWidth:2,pointRadius:2,fill:false});
  }
  var ws=document.getElementById('dWin'); var wMode=ws?ws.value:'90';
  var win=wMode==='all'?total:(parseInt(wMode,10)||90); if(win>total)win=total;
  var maxStart=Math.max(0,total-win);
  if(dStart>maxStart)dStart=maxStart; if(dStart<0)dStart=0;
  var rng=document.getElementById('dRange');
  if(rng){ rng.min=0; rng.max=maxStart; rng.value=dStart; rng.disabled=(wMode==='all'||maxStart<=0); }
  var full=histDates.concat(fcAll).slice(0,total);
  var sA=document.getElementById('dWinA'),sB=document.getElementById('dWinB');
  if(sA)sA.textContent=total+' 天 · '+(full[dStart]||'').slice(5);
  if(sB)sB.textContent=' ~ '+(full[Math.min(total-1,dStart+win-1)]||'').slice(5);
  if(sub)sub.textContent='蓝线=实际日销量（全历史 '+histDates.length+' 天，含0）· 绿虚线=未来 '+fcN+' 天波动预测：周六周日不发货=0（累积订单并入周一等发货日），整周发货总量=7×D('+fmt(o.rate,2)+'件/天)· 拖动轨道浏览';
  cDaily=new Chart(cv,{type:'line',
    data:{labels:labels,datasets:ds},
    options:{responsive:true,maintainAspectRatio:false,interaction:{mode:'index',intersect:false},
      scales:{x:{min:dStart,max:dStart+win-1,ticks:{maxTicksLimit:12,maxRotation:0,autoSkip:true}},y:{beginAtZero:true,ticks:{precision:0}}},
      plugins:{legend:{labels:{boxWidth:14,font:{size:11}}},tooltip:{callbacks:{label:function(ctx){return (ctx.dataset.label||'')+': '+ctx.parsed.y+' 件'}}}}}});
}
function onDailyRange(){
  var rng=document.getElementById('dRange');
  var v=rng?parseInt(rng.value,10):0;
  if(!isNaN(v)&&v>=0)dStart=v;
  drawDaily();
}
function initDaily(){
  /* 默认选中"近期真的在出库"的 SKU。
     直接用 ROWS[0] 会挑到按缺货紧急度排序的第一位(SKU 名顺序恰好偏好),
     可能是个近 30 天零出库的 SKU, 一进来就是一条平线, 观感像数据缺失。
     这里优先取近 30 天出库量最大的 SKU, 都为零时再退回 ROWS[0]。 */
  dCur=null;
  var best=-1, bestQty=0;
  for(var i=0;i<ROWS.length;i++){
    var d=(CHARTS.skuDaily||{})[String(ROWS[i].sku)];
    if(!d||!d.hist||!d.hist.length)continue;
    var s=0,n=d.hist.length;
    for(var j=Math.max(0,n-30);j<n;j++)s+=d.hist[j]||0;
    if(s>bestQty){bestQty=s;best=String(ROWS[i].sku);}
  }
  dCur=(best!==null)?best:(ROWS.length?String(ROWS[0].sku):null);
  dSkuLabel();
  if(!dCur){ var s=document.getElementById('dailySub'); if(s)s.textContent='暂无可展示的 SKU'; return; }
  drawDaily();
}

/* ---------- 表格 ---------- */
var q='',f='all';
function cell(v,cls,align){return '<td'+(align?' class="num-r '+cls+'"':' class="'+cls+'"')+'>'+v+'</td>'}

/* ---------- 备货看板 多仓库数据源切换(美国富皇美运 / 德国盘古), 与速卖通按店铺切换同一交互 ---------- */
var WH='us', VIEWS={};
(function(){
  VIEWS.us={label:(SOURCE&&SOURCE.warehouse)||'美国仓',rows:ROWS,charts:CHARTS,stats:STATS,source:SOURCE,param:params};
  if(DEVIEW&&DEVIEW.rows&&DEVIEW.rows.length){ VIEWS.de=DEVIEW; var b=document.getElementById('whDe'); if(b)b.style.display=''; }
})();
var CHARTS_SKELETON=null;
function whCur(){ return VIEWS[WH]||VIEWS.us; }
function updateKpis(st){
  st=st||{};
  var els=document.querySelectorAll('#tab-stock [data-k]');
  for(var i=0;i<els.length;i++){ var k=els[i].getAttribute('data-k'); els[i].textContent=fmt(st[k]||0); }
}
function updateSource(s){
  var el=document.getElementById('srcLine'); if(!el||!s)return;
  el.innerHTML='<span>系统：<b>'+esc2(s.warehouse)+'</b></span>'
    +'<span class="ok">✓ 库存接口已连通（'+fmt(s.skuCount)+' 个 SKU）</span>'
    +'<span class="ok">✓ 销量接口已连通（累计 '+fmt(s.flowCount)+' 件出库流水）</span>'
    +'<span class="kv">接口：'+esc2(s.api)+'</span>'
    +'<span class="kv">最近同步：'+esc2(s.syncAt)+'</span>';
}
function rebuildCharts(){
  var wrap=document.getElementById('chartsWrap'); if(!wrap)return;
  if(CHARTS_SKELETON===null){ CHARTS_SKELETON=wrap.innerHTML; }
  else { wrap.innerHTML=CHARTS_SKELETON; }
  chartsReady=false; dCur=null; dStart=0;
  if(typeof Chart!=='undefined'){ ['cLevel','cTop','cTrend','cDaily','cSku'].forEach(function(id){ var c=Chart.getChart(id); if(c)c.destroy(); }); }
  initCharts();
}
function switchWh(k){
  if(!VIEWS[k]||k===WH)return;
  WH=k;
  var v=VIEWS[k];
  ROWS=v.rows; CHARTS=v.charts;
  var chips=document.querySelectorAll('.wh-bar .chip');
  for(var i=0;i<chips.length;i++){ if(chips[i].getAttribute('data-w')===k)chips[i].classList.add('on'); else chips[i].classList.remove('on'); }
  var note=document.getElementById('whNote');
  if(note)note.textContent=(k==='de')?'盘古海外仓 · 库存+近90天已发货订单':'富皇美运 4 仓聚合 · 库存+出库流水';
  var sw=document.getElementById('btnWhSw'); if(sw)sw.classList.toggle('on',k==='de');
  updateKpis(v.stats); updateSource(v.source);
  f='all'; q='';
  var qi=document.getElementById('q'); if(qi)qi.value='';
  var cs=document.querySelectorAll('#chips .chip');
  for(var j=0;j<cs.length;j++){ if(cs[j].getAttribute('data-f')==='all')cs[j].classList.add('on'); else cs[j].classList.remove('on'); }
  render(); rebuildCharts();
  try{ localStorage.setItem('dash_wh',k); }catch(e){}
}
function esc2(s){return String(s==null?'':s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;')}
/* ---------- 多国海外仓: 目的国家 ---------- */
var COUNTRY_OPTS=['美国','德国','英国','法国','日本','澳大利亚','加拿大','其他'];
/* 国家 -> 常见仓库代码建议(输入提示) */
var WH_SUGGEST={ '美国':['LAXYYC','LAX11','LAX03','SAV02'], '德国':[], '英国':[], '法国':[], '日本':[], '澳大利亚':[], '加拿大':[], '其他':[] };
function guessCountryOf(wh){
  var w=String(wh||'').toUpperCase().trim();
  if(/^(LAX|SAV)/.test(w))return '美国';      /* 富皇美运(FDR)美国仓 */
  if(/^(DE|BER|HAM|FRA)/.test(w))return '德国'; /* 盘古德国仓(二期, 预留) */
  return '';
}
function countryOpts(sel){
  var h='';
  COUNTRY_OPTS.forEach(function(c){ h+='<option'+(c===sel?' selected':'')+'>'+c+'</option>'; });
  return h;
}
/* 国家+仓库 单元格展示: 国家不为空且非"其他"时显示 "🇺🇸"? 用文字: 国家 · 仓库 */
function countryCell(b){
  var c=b&&b.country?b.country:(guessCountryOf(b&&b.warehouse)||'');
  var w=b&&b.warehouse?String(b.warehouse):'';
  if(!c&&!w)return '<span class="dim">—</span>';
  if(!c)return esc2(w);
  if(!w)return esc2(c);
  return c==='其他'?esc2(w):esc2(c+' · '+w);
}
/* 国家变更时联动仓库输入建议 */
function onWhCountry(){
  var sel=document.getElementById('fBCountry');
  var wh=document.getElementById('fBWh');
  var dl=document.getElementById('fBWhList');
  if(!sel)return;
  var c=sel.value;
  if(dl)dl.innerHTML=(WH_SUGGEST[c]||[]).map(function(w){return '<option value="'+w+'">';}).join('');
  var hint=document.getElementById('fBWhHint');
  if(hint)hint.textContent=(WH_SUGGEST[c]&&WH_SUGGEST[c].length)?('常见仓：'+WH_SUGGEST[c].join(' / ')):'';
}
function fmt(n,d){if(n===null||n===undefined||isNaN(n))return '—';return Number(n).toLocaleString('zh-CN',{maximumFractionDigits:(d===undefined?0:d)})}
function dueCell(r){
  if(r.rate<=0) return cell('<span style="color:var(--sub)">—</span>');
  if(r.position<=0) return cell('<span class="due over">立即下单</span>');
  var d=r.lastOrderInDays;
  var cls=d<0?'over':(d<=30?'soon':'ok');
  var txt=d<0?('已超期 '+(-d)+' 天'):(d===0?'今天':' '+d+' 天后');
  return cell('<span class="due '+cls+'">'+txt+'<br><span class="mono" style="color:var(--sub);font-size:12px">'+r.lastOrderDay+'</span></span>');
}
function render(){
  var kw=q.trim().toLowerCase();
  var list=ROWS.filter(function(r){
    if(f!=='all'&&r.level!==f)return false;
    if(!kw)return true;
    return String(r.sku).toLowerCase().indexOf(kw)>=0||String(r.name||'').toLowerCase().indexOf(kw)>=0;
  });
  var tb=document.getElementById('tbody'),empty=document.getElementById('empty');
  empty.style.display=list.length?'none':'block';
  tb.innerHTML=list.map(function(r){
    var badge='<span class="badge '+LEVEL[r.level]+'">'+LABEL[r.level]+'</span>';
    return '<tr data-sku="'+esc2(r.sku)+'">'+
      cell('<span class="mono">'+esc2(r.sku)+'</span>','')+
      cell(esc2(r.name||'—'),'')+
      cell(fmt(r.onHand),'','r')+cell(fmt(r.inTransit),'','r')+cell('<b>'+fmt(r.position)+'</b>','','r')+
      cell(fmt(r.rate,2),'','r')+
      cell(r.rate>0?fmt(r.coverDays,1):(r.position>0?'∞':'—'),'','r')+
      cell(r.rate>0?fmt(r.ss):'—','','r')+
      cell(badge,'')+
      cell(fmt(r.rop),'','r')+cell(fmt(r.orderUpTo),'','r')+
      cell(r.suggest>0?'<b style="color:#f07575">'+fmt(r.suggest)+'</b>':(r.suggest===0?'0':'—'),'','r')+
      dueCell(r)+
    '</tr>';
  }).join('');
}
document.getElementById('q').addEventListener('input',function(e){q=e.target.value;render()});
document.getElementById('chips').addEventListener('click',function(e){
  var c=e.target.closest('.chip');if(!c)return;
  document.querySelectorAll('.chip').forEach(function(x){x.classList.remove('on')});
  c.classList.add('on');f=c.dataset.f;render();
});
/* 点击行 -> 打开SKU详情(数据来源用data-sku属性, 避免引号转义问题) */
document.getElementById('tbody').addEventListener('click',function(e){
  var tr=e.target.closest('tr'); if(!tr)return;
  var sku=tr.getAttribute('data-sku');
  if(sku) openDetail(sku);
});
render();

/* ---------- 通用分页 (pi-v2) ---------- */
var PAGE_ST={},PAGE_TOTAL={},PAGER_HOOKS={};
function pageSlice(arr,key,size){
  size=size||30;
  var st=PAGE_ST[key]||0,mx=Math.max(1,Math.ceil(arr.length/size));
  if(st>=mx)st=mx-1; if(st<0)st=0; PAGE_ST[key]=st;
  return {list:arr.slice(st*size,(st+1)*size),st:st,mx:mx};
}
function pageBar(key,total,size){
  size=size||30;
  var st=PAGE_ST[key]||0,mx=Math.max(1,Math.ceil(total/size));
  if(st>=mx)st=mx-1; if(st<0)st=0; PAGE_ST[key]=st; PAGE_TOTAL[key]=mx;
  if(total<=size&&st===0)return '';
  var h='<div class="pager"><span class="pg-info">共 '+total+' 条 · 第 '+(st+1)+' / '+mx+' 页</span>';
  h+='<button class="btn small" data-a="first"'+(st>0?'':' disabled')+'>« 首页</button>';
  h+='<button class="btn small" data-a="prev"'+(st>0?'':' disabled')+'>‹ 上一页</button>';
  h+='<button class="btn small" data-a="next"'+(st<mx-1?'':' disabled')+'>下一页 ›</button>';
  h+='<button class="btn small" data-a="last"'+(st<mx-1?'':' disabled')+'>末页 »</button>';
  h+='<input class="pg-num" type="number" min="1" max="'+mx+'" value="'+(st+1)+'" title="跳转到第几页" style="width:64px;padding:4px 6px;border:1px solid var(--line);border-radius:6px;font-size:12px;outline:none;background:var(--card2);color:var(--txt)">';
  return h+'</div>';
}
function setPager(key,total,size){
  var el=document.getElementById(key+'Pager'); if(!el)return;
  el.innerHTML=pageBar(key,total,size);
}
function bindPagers(){
  ['trace','in','pi','pb','ae'].forEach(function(k){
    var el=document.getElementById(k+'Pager'); if(!el||el._h)return; el._h=1;
    el.addEventListener('click',function(e){
      var b=e.target.closest('button'); if(!b||!b.dataset.a)return;
      var st=PAGE_ST[k]||0,mx=PAGE_TOTAL[k]||1;
      if(b.dataset.a==='first')st=0; else if(b.dataset.a==='prev')st=Math.max(0,st-1);
      else if(b.dataset.a==='next')st=Math.min(mx-1,st+1); else if(b.dataset.a==='last')st=mx-1;
      PAGE_ST[k]=st;
      var fn=PAGER_HOOKS[k]; if(fn)fn();
    });
    el.addEventListener('change',function(e){
      if(!e.target.classList.contains('pg-num'))return;
      var v=parseInt(e.target.value,10),mx=PAGE_TOTAL[k]||1;
      if(!isNaN(v)){ PAGE_ST[k]=Math.min(Math.max(0,v-1),mx-1); var fn=PAGER_HOOKS[k]; if(fn)fn(); }
    });
  });
}
/* ---------- 出库溯源 tab ---------- */
var TRACE_ITEMS=[],tq='',tf='all',tds='',tde='',TRACE_VIEW=[];
var TRACE_FILT='';
/* ---------- 工作台外壳: 左侧导航 / 顶栏 / 面包屑 ---------- */
/* 模块注册表: 以后新增运营模块(如营销活动、内容素材)只要在这里加一行 + 页面加一个 #tab-xxx 容器即可 */
var MODULE_META={
  stock:{grp:'stock', title:'备货看板', sub:'库存与备货 · 海外仓实时库存与补货建议'},
  trace:{grp:'chain', title:'出库溯源', sub:'供应链 · 出库单 FIFO 溯源与头程成本核算'},
  pi:{grp:'chain', title:'PI & 头程', sub:'供应链 · PI 单、发货批次与头程费用录入'},
  ae:{grp:'ops', title:'速卖通订单', sub:'运营中心 · 订单明细与利润核算'}
};
function sideToggle(){
  var mini=document.body.classList.toggle('side-mini');
  var vw=document.querySelector('.side-brand .vw'); if(vw)vw.textContent=mini?'»':'«';
  try{ localStorage.setItem('dash_side',mini?'1':'0'); }catch(e){}
  setTimeout(function(){ try{ window.dispatchEvent(new Event('resize')); }catch(e){} },230);
}
function navGrp(g){
  var el=document.querySelector('.nav-grp[data-grp="'+g+'"]'); if(!el)return;
  el.classList.toggle('open');
}
/* 美国 / 德国 数据源切换(顶栏 ⇆ 按钮, 与页内 chips 同一逻辑) */
function whToggle(){
  var k=(WH==='de')?'us':'de';
  if(!VIEWS[k]){ alert('德国仓数据尚未接入或本页快照未包含，暂无法切换。'); return; }
  switchWh(k);
}
function syncNav(name){
  try{ localStorage.setItem('dash_tab',name); }catch(e){}
  var meta=MODULE_META[name]||{grp:'stock',title:name,sub:''};
  /* 左侧导航高亮 */
  document.querySelectorAll('.nav-sub .nav-it').forEach(function(x){
    x.classList.toggle('on', x.getAttribute('data-t')===name);
  });
  /* 自动展开所在分组 */
  document.querySelectorAll('.nav-grp').forEach(function(g){
    g.classList.toggle('open', g.getAttribute('data-grp')===meta.grp);
  });
  var t=document.getElementById('tbTitle'), s=document.getElementById('tbSub');
  if(t)t.textContent=meta.title;
  if(s)s.textContent=meta.sub;
}
function switchTab(name){
  syncNav(name);
  document.querySelectorAll('.tab').forEach(function(x){x.classList.remove('on')});
  var tab=document.querySelector('.tab[data-t="'+name+'"]'); if(tab)tab.classList.add('on');
  var shWrap=document.getElementById('aeShopWrap');
  if(shWrap)shWrap.style.display=(name==='ae')?'inline-block':'none';
  ['stock','trace','pi','ae'].forEach(function(t){
    var el=document.getElementById('tab-'+t);
    if(el)el.style.display=(name===t)?'block':'none';
  });
  if(name==='trace'){
    if(!TRACE_ITEMS.length) buildTraceItems();
    if(!IN_READY) buildInbound();   /* 先建 RO_FEE 费用索引, 主表费用列依赖它 */
    renderTrace();
    renderInbound();
  }
  if(name==='pi'){
    if(!PI_READY) buildPi();
    renderPiAll();
  }
  if(name==='ae'){
    if(!AE_READY) buildAe();
    renderAeAll();
  }
}
function buildTraceItems(){
  TRACE_ITEMS=[];
  if(!TRACE||!TRACE.has)return;
  /* 入库单号 -> 该批次的入库总量(total) 索引。
     注意: 早期版本这里误写成 roQty:t.qty(把"入库数量"填成了"出库数量"),
     导致溯源表里 入库数量 恒等于 数量 列, 看起来像数据丢失。现改为取批次真实总量。 */
  var roTotal={};
  (TRACE.inbound||[]).forEach(function(b){ if(b&&b.ro) roTotal[b.ro]=(Number(b.total)||0); });
  (TRACE.outbound||[]).forEach(function(t){
    var rt=roTotal[t.ro];
    TRACE_ITEMS.push({do:t.do,reference:t.reference||'',sku:t.sku,warehouse:t.warehouse,qty:t.qty,date:t.date,ro:t.ro,roQty:(rt!==undefined?rt:''),roDate:t.roDate,matched:true,reason:''});
  });
  (TRACE.unmatched||[]).forEach(function(u){
    TRACE_ITEMS.push({do:u.do,reference:u.reference||'',sku:u.sku,warehouse:u.warehouse,qty:u.qty,date:u.date,ro:'—',roQty:0,roDate:'—',matched:false,reason:u.reason||''});
  });
  TRACE_ITEMS.sort(function(a,b){return a.date<b.date?1:(a.date>b.date?-1:0)});
  var badge=document.getElementById('traceBadge'); if(badge)badge.textContent=TRACE_ITEMS.length;
  var nb=document.getElementById('navBadgeTrace'); if(nb){ nb.style.display=(TRACE_ITEMS.length?'':'none'); nb.textContent=TRACE_ITEMS.length; }
}
function feeTds(t){
  /* 出库重量(kg) + 海运费用均摊(元/kg) + 头程费用 = 元/kg × 出库重量
     出库重量只取决于 SKU 重量档案(海外仓 WMS), 与是否已录费用无关;
     档案缺失时用该入库单批次的平均单重估算(标注); 未录费用的批次重量照常显示, 仅费用列 — */
  var w='<span class="dim">—</span>', u='<span class="dim">—</span>', f='<span class="dim">—</span>';
  var g=(t.matched&&t.ro&&t.ro!=='—'&&RO_FEE&&RO_FEE[t.ro])?RO_FEE[t.ro]:null;
  var uw=skuWeightKg(t.sku), est=false;
  if(!uw&&g&&g.avgUnitKg>0){ uw=g.avgUnitKg; est=true; }
  var wk=(Number(t.qty)||0)*uw;
  if(wk>0){
    w=fmt(wk,2)+' kg'+(est?' <span class="row-note" title="该 SKU 无 WMS 重量档案，按该入库单批次平均单件重量估算">估算</span>':'');
  }
  if(g&&g.perKg>0){
    u='<span class="pfee">'+money3(g.perKg,g.cur)+'</span>';
    if(wk>0)f='<span class="pfee">'+money(g.perKg*wk,g.cur,2)+'</span>';
  }
  return '<td class="num-r">'+w+'</td><td class="num-r">'+u+'</td><td class="num-r">'+f+'</td>';
}
function traceRow(t){
  var st=t.matched?'<span class="matched-ok">✓ 已匹配</span>':'<span class="matched-no" title="'+esc2(t.reason||'')+'">✗ 未匹配</span>';
  return '<tr>'+
    '<td class="mono">'+esc2(t.do)+'</td>'+
    '<td class="mono">'+(t.reference?esc2(t.reference):'<span class="dim">—</span>')+'</td>'+
    '<td class="mono">'+esc2(t.sku)+'</td>'+
    '<td>'+esc2(t.warehouse)+'</td>'+
    '<td class="num-r">'+fmt(t.qty)+'</td>'+
    '<td class="mono">'+esc2(t.date)+'</td>'+
    '<td class="mono">'+esc2(t.ro)+'</td>'+
    '<td class="num-r">'+(t.roQty?fmt(t.roQty):'—')+'</td>'+
    '<td class="mono">'+esc2(t.roDate)+'</td>'+
    feeTds(t)+
    '<td>'+st+'</td>'+
  '</tr>';
}
function renderTrace(){
  var empty=document.getElementById('traceEmpty'),tb=document.getElementById('traceTbody');
  var pgEl=document.getElementById('tracePager');
  if(!TRACE||!TRACE.has){
    if(tb)tb.innerHTML='';
    if(empty){empty.style.display='block';empty.textContent='暂无出库溯源数据（运行数据同步后自动生成）';}
    if(pgEl)pgEl.innerHTML='';
    return;
  }
  var kw=tq.trim().toLowerCase();
  var fk=tq+'|'+tf+'|'+tds+'|'+tde;
  if(fk!==TRACE_FILT){ TRACE_FILT=fk; PAGE_ST.trace=0; }
  TRACE_VIEW=TRACE_ITEMS.filter(function(t){
    if(tf==='unmatched'&&t.matched)return false;
    if(tf!=='all'&&tf!=='unmatched'&&t.warehouse!==tf)return false;
    if(tds&&String(t.date)<tds)return false;
    if(tde&&String(t.date)>tde)return false;
    if(!kw)return true;
    return String(t.do).toLowerCase().indexOf(kw)>=0||String(t.reference).toLowerCase().indexOf(kw)>=0||String(t.ro).toLowerCase().indexOf(kw)>=0||String(t.sku).toLowerCase().indexOf(kw)>=0||String(t.warehouse).toLowerCase().indexOf(kw)>=0;
  });
  empty.style.display=TRACE_VIEW.length?'none':'block';
  var pg=pageSlice(TRACE_VIEW,'trace');
  tb.innerHTML=pg.list.map(traceRow).join('');
  setPager('trace',TRACE_VIEW.length);
}
/* 导出当前筛选结果 CSV (带 BOM, Excel 可直接打开) */
function csvCell(v){ v=String(v==null?'':v); if(/[",\\r\\n]/.test(v))v='"'+v.replace(/"/g,'""')+'"'; return v; }
function downloadFile(name,text){
  var blob=new Blob(['\ufeff'+text],{type:'text/csv;charset=utf-8'});
  var a=document.createElement('a'); a.href=URL.createObjectURL(blob); a.download=name;
  document.body.appendChild(a); a.click();
  setTimeout(function(){URL.revokeObjectURL(a.href);if(a.remove)a.remove();},300);
}
function exportTraceCsv(){
  if(!TRACE_VIEW||!TRACE_VIEW.length){ alert('当前没有可导出的记录（请先调整搜索/日期/状态筛选）'); return; }
  var head=['出库单号DO','客户参考号','SKU','仓库','数量','出库时间','来源入库单号','入库数量','入库时间','出库重量kg','海运费用均摊(元/kg)','头程费用','状态'];
  var lines=[head.join(',')];
  TRACE_VIEW.forEach(function(t){
    var w='',u='',f='';
    if(t.matched&&t.ro!=='—'&&RO_FEE&&RO_FEE[t.ro]&&RO_FEE[t.ro].perKg>0){
      var g=RO_FEE[t.ro];
      var uw=skuWeightKg(t.sku)||g.avgUnitKg;
      var wk=(Number(t.qty)||0)*uw;
      w=wk.toFixed(2); u=g.perKg.toFixed(4); f=(g.perKg*wk).toFixed(2);
    }
    lines.push([t.do,t.reference,t.sku,t.warehouse,t.qty,t.date,t.ro,t.roQty||'',t.roDate,w,u,f,t.matched?'已匹配':'未匹配'].map(csvCell).join(','));
  });
  var d=new Date();
  var ds=d.getFullYear()+String(d.getMonth()+1).padStart(2,'0')+String(d.getDate()).padStart(2,'0');
  downloadFile('出库FIFO溯源_'+ds+'.csv',lines.join('\\r\\n'));
}
var tqEl=document.getElementById('tq');
function tqSearch(){ var q=tqEl||document.getElementById('tq'); if(!q)return; tq=q.value; var btn=document.getElementById('tqBtn'); if(btn){ btn.classList.remove('pending'); } renderTrace(); }
if(tqEl){
  tqEl.addEventListener('keydown',function(e){if(e.key==='Enter'){e.preventDefault();tqSearch();}});
  tqEl.addEventListener('input',function(e){
    var btn=document.getElementById('tqBtn');
    if(btn){ btn.classList.toggle('pending', e.target.value!==tq); }
  });
}
var tdsEl=document.getElementById('tds');
if(tdsEl)tdsEl.addEventListener('change',function(e){tds=e.target.value;renderTrace()});
var tdeEl=document.getElementById('tde');
if(tdeEl)tdeEl.addEventListener('change',function(e){tde=e.target.value;renderTrace()});
var tcEl=document.getElementById('tchips');
if(tcEl)tcEl.addEventListener('click',function(e){
  var c=e.target.closest('.chip'); if(!c)return;
  document.querySelectorAll('#tchips .chip').forEach(function(x){x.classList.remove('on')});
  c.classList.add('on'); tf=c.dataset.f; renderTrace();
});
buildTraceItems();

/* ---------- 入库批次消耗汇总 (溯源 tab 下方表) ---------- */
var IN_READY=false, IN_ROWS=[], RO_FEE={};
/* SKU 重量/尺寸档案(海外仓 WMS 同步): {sku:{weightKg, weightRaw, weightUnit, dimsCm, warehouse}} */
var SKU_W={}, SKU_W_AT='';
function skuWeightKg(sku){ var r=SKU_W[String(sku||'')]; return (r&&Number(r.weightKg)>0)?Number(r.weightKg):0; }
function skuDimsOf(sku){ var r=SKU_W[String(sku||'')]; return (r&&r.dimsCm)?String(r.dimsCm):''; }
/* 批次内出现的 SKU 去重清单(带单件重量/尺寸), 供批次表「入库重量 / 入库尺寸」列使用 */
function batchSkuList(b){
  var seen={},out=[];
  ((b&&b.products)||[]).forEach(function(p){
    var k=String(p.sku||''); if(!k||seen[k])return; seen[k]=1;
    out.push({sku:k, w:skuWeightKg(k), d:skuDimsOf(k)});
  });
  return out;
}
/* 多行小字单元格: pick 返回空/0 时该行不显示; 多 SKU 时行首带 SKU 便于区分 */
function skuLinesCell(rows,pick,suffix){
  var ok=rows.filter(function(r){ var v=pick(r); return v&&v!=='x'; });
  if(!ok.length)return '<span class="dim">—</span>';
  var multi=rows.length>1;
  return ok.map(function(r){
    return '<span class="row-note" style="display:block;white-space:normal" title="'+esc2(r.sku)+'">'+
      (multi?(esc2(r.sku)+' '):'')+esc2(String(pick(r))+(suffix||''))+'</span>';
  }).join('');
}
/* 关联状态: 该批次入库单号是否已出现在 FDR 库存流水的入库批次里(决定 FIFO 溯源能否命中) */
function traceStatusCell(b){
  if(!b||!b.ro)return '<span class="dim" style="color:#e8a24e">未填入库单号</span>';
  var list=(typeof TRACE!=='undefined'&&TRACE&&TRACE.inbound)||[];
  var key=String(b.ro).toUpperCase();
  var ok=list.some(function(x){return String(x.ro||'').toUpperCase()===key;});
  return ok?'<span class="matched-ok">✓ 已在溯源</span>'
    :'<span class="badge b-wait" title="该入库单号尚未出现在 FDR 库存流水入库批次中（可能为最新入库或流水窗口未覆盖）">入库流水未见</span>';
}
/* 运费币种: 新批次存 freightCurrency; 老批次回落原 currency 字段 */
function freightCurOf(b){ return b.freightCurrency||b.currency||'CNY'; }
function buildRoFeeIndex(){
  var idx={};
  (PIF.batches||[]).forEach(function(b){
    if(!b.ro)return;
    var g=idx[b.ro]||(idx[b.ro]={qty:0,kg:0,freight:0,cur:freightCurOf(b),desc:[]});
    var q=0;(b.products||[]).forEach(function(p){q+=Number(p.qty)||0;});
    g.qty+=q; g.kg+=Number(b.grossWeightKg)||0; g.freight+=Number(b.totalFreight)||0;
    g.cur=freightCurOf(b);
    g.desc.push((b.piNo||'')+(b.batchNo?('#'+b.batchNo):''));
  });
  /* perKg = 海运费用均摊(元/kg); avgUnitKg = 批次平均单重(无 WMS 重量档案时的估算回退) */
  Object.keys(idx).forEach(function(ro){
    var g=idx[ro];
    g.perKg=(g.kg>0&&g.freight>0)?(g.freight/g.kg):0;
    g.avgUnitKg=g.qty>0?(g.kg/g.qty):0;
  });
  return idx;
}
function buildInbound(){
  IN_READY=true;
  RO_FEE=buildRoFeeIndex();
  IN_ROWS=((TRACE&&TRACE.inbound)||[]).slice().sort(function(a,b){
    return String(a.roDate||'')<String(b.roDate||'')?1:(String(a.roDate||'')>String(b.roDate||'')?-1:0);
  });
}
function inboundRow(b){
  var total=Number(b.total)||0, used=Number(b.used)||0, remain=Number(b.remain)||0;
  var rate=total>0?(used/total):0;
  var cls=rate>=1?'red':(rate>=0.85?'amber':'');
  var bar='<span class="v-bar '+(cls||'')+'" title="已消耗 '+fmt(used)+' / 入库 '+fmt(total)+'"><i style="width:'+Math.min(100,Math.round(rate*100))+'%"></i></span> <span class="row-note">'+fmt(used)+'/'+fmt(total)+'</span>';
  var g=RO_FEE[b.ro];
  var usedKgCell='<span class="dim">—</span>', feeCellTxt='<span class="dim">—</span>', perKgCell='<span class="dim">—</span>';
  /* 已出库重量只取决于 SKU 重量档案, 与是否已录费用无关; 未录费用的批次仅费用列 — */
  var uw=skuWeightKg(b.sku), est=false;
  if(!uw&&g&&g.avgUnitKg>0){ uw=g.avgUnitKg; est=true; }
  if(uw>0){
    usedKgCell=fmt((Number(used)||0)*uw,2)+' kg'+(est?' <span class="row-note" title="该 SKU 无 WMS 重量档案，按批次平均单件重量估算">估算</span>':'');
  }
  if(g&&g.perKg>0){
    perKgCell=money3(g.perKg,g.cur)+'<br><span class="row-note">'+esc2(g.desc.join('、'))+'</span>';
    feeCellTxt=(uw>0)?money(g.perKg*(Number(used)||0)*uw,g.cur,2):'<span class="dim">—</span>';
  }
  return '<tr>'+
    '<td class="mono">'+esc2(b.sku)+'</td>'+
    '<td>'+esc2(b.warehouse)+'</td>'+
    '<td class="mono">'+esc2(b.ro)+'</td>'+
    '<td class="mono">'+esc2(b.exportNo||'—')+'</td>'+
    '<td class="mono">'+esc2(b.exportTracking||'—')+'</td>'+
    '<td class="mono">'+esc2(b.roDate||'—')+'</td>'+
    '<td class="num-r">'+fmt(total)+'</td>'+
    '<td class="num-r">'+fmt(used)+'</td>'+
    '<td class="num-r">'+(remain>0?'<b style="color:#2ec4a6">'+fmt(remain)+'</b>':fmt(remain))+'</td>'+
    '<td>'+bar+'</td>'+
    '<td class="num-r">'+usedKgCell+'</td>'+
    '<td class="num-r">'+perKgCell+'</td>'+
    '<td class="num-r">'+feeCellTxt+'</td>'+
  '</tr>';
}
function renderInbound(){
  var tb=document.getElementById('inTbody'), empty=document.getElementById('inEmpty');
  if(!tb)return;
  if(!IN_ROWS.length){
    if(empty)empty.style.display='block';
    tb.innerHTML='';
    var pe=document.getElementById('inPager'); if(pe)pe.innerHTML='';
    return;
  }
  if(empty)empty.style.display='none';
  var pg=pageSlice(IN_ROWS,'in');
  tb.innerHTML=pg.list.map(inboundRow).join('');
  setPager('in',IN_ROWS.length);
}

/* ---------- PI & 头程 tab ---------- */
var PI_READY=false, PIS=[], BATCHES=[], PIQ='', PBQ='';
var PIS_VIEW=[], BATCH_VIEW=[];
var PIQ_LAST='', PBQ_LAST='';
/* 在线录入(优先同源=云端服务; 回退本机 pi-server 8899) */
var LIVE=false, PI_TRYED=false, FM_TYPE='', FM_EDIT=null;
var API_BASE='', API_CAND=[];
(function(){
  var c=[];
  try{ var o=location.origin; if(o&&o!=='null'&&/^https?:/.test(o))c.push(o); }catch(e){}
  c.push('http://127.0.0.1:8899');
  API_CAND=c;
})();
function resolveApiBase(){
  return new Promise(function(resolve){
    if(API_BASE){return resolve(API_BASE);}
    var i=0;
    (function next(){
      if(i>=API_CAND.length){return resolve('');}
      var b=API_CAND[i++];
      var x=new XMLHttpRequest();
      try{ x.open('GET',b+'/api/ping',true); }catch(e){ return next(); }
      x.timeout=2500;
      x.onload=function(){ try{ var j=JSON.parse(x.responseText); if(j&&j.ok){ API_BASE=b; return resolve(b); } }catch(e){} next(); };
      x.onerror=function(){ next(); };
      x.ontimeout=function(){ next(); };
      x.send();
    })();
  });
}
function getToken(){ try{ return localStorage.getItem('dash_token')||sessionStorage.getItem('dash_token')||''; }catch(e){ return ''; } }
function saveToken(t,remember){ try{ (remember?localStorage:sessionStorage).setItem('dash_token',t); }catch(e){} }
function fetchToken(remember){
  resolveApiBase().then(function(b){
    if(!b)return;
    var u='',p='';
    try{ u=document.getElementById('u').value.trim(); p=document.getElementById('p').value; }catch(e){}
    apiJsonRaw('POST',b+'/api/login',{user:u,pass:p}).then(function(r){
      if(r.status===200&&r.body&&r.body.ok&&r.body.token)saveToken(r.body.token,remember);
    }).catch(function(){});
  });
}
/* 静默自动重登: 用记住的账号+密码哈希换新 token(服务器接受 sha256 密码) */
var RELOGIN_BUSY=false;
function reloginSilent(){
  if(RELOGIN_BUSY)return Promise.resolve(false);
  RELOGIN_BUSY=true;
  var u='',ph='';
  try{
    u=localStorage.getItem('dash_user')||sessionStorage.getItem('dash_user')||'';
    ph=localStorage.getItem('dash_pass')||sessionStorage.getItem('dash_pass')||'';
  }catch(e){}
  if(!u||!ph){ RELOGIN_BUSY=false; return Promise.resolve(false); }
  return apiJsonRaw('POST',API_BASE+'/api/login',{user:u,pass:ph}).then(function(r){
    RELOGIN_BUSY=false;
    if(r.status===200&&r.body&&r.body.ok&&r.body.token){
      var remember=!!localStorage.getItem('dash_ok');
      saveToken(r.body.token,remember);
      return true;
    }
    return false;
  }).catch(function(){ RELOGIN_BUSY=false; return false; });
}
/* 无凭据可自动重登时: 回到登录页让用户重新登录 */
function kickToLogin(){
  try{ localStorage.removeItem('dash_ok'); localStorage.removeItem('dash_token'); }catch(e){}
  sessionStorage.removeItem('dash_ok'); sessionStorage.removeItem('dash_token');
  var lg=document.getElementById('login'), ap=document.getElementById('app');
  if(lg&&ap&&lg.style.display!=='none')return;
  if(lg&&ap){ lg.style.display='flex'; ap.style.display='none'; var err=document.getElementById('loginErr'); if(err)err.textContent='登录已过期，请重新登录'; }
}
var CUR_SYM={CNY:'¥',USD:'$',EUR:'€',HKD:'HK$',GBP:'£'};
function money(v,cur,d){
  if(v===null||v===undefined||isNaN(v))return '—';
  var sym=CUR_SYM[cur]||(cur?cur+' ':'');
  return sym+Number(v).toLocaleString('zh-CN',{maximumFractionDigits:(d===undefined?2:d)});
}
/* 元/kg 单价: 恒 3 位小数 —— money() 会丢尾零(2.000 显示成 2), 比价时列不齐 */
function money3(v,cur){
  if(v===null||v===undefined||isNaN(v))return '—';
  var sym=CUR_SYM[cur]||(cur?cur+' ':'');
  return sym+Number(v).toLocaleString('zh-CN',{minimumFractionDigits:3,maximumFractionDigits:3});
}
function multiCur(map){
  var keys=Object.keys(map);
  if(!keys.length)return '—';
  if(keys.length===1)return money(map[keys[0]],keys[0],0);
  return keys.map(function(k){return money(map[k],k,0)}).join(' + ');
}
function batchQty(b){ return (b.products||[]).reduce(function(s,p){return s+(Number(p.qty)||0)},0); }
/* 一个批次(一柜/一个入库单)可混装多个 PI: piNo 支持「、,;」等分隔; 新数据另存 piNos 数组 */
function batchPiList(b){
  if(b&&b.piNos&&b.piNos.length)return b.piNos.map(function(s){return String(s).trim().toUpperCase()}).filter(function(s){return s});
  return String((b&&b.piNo)||'').split(/[,，、;；\\/\\s+]+/).map(function(s){return s.trim().toUpperCase()}).filter(function(s){return s});
}
function batchHasPi(b,piNo){ return batchPiList(b).indexOf(String(piNo||'').trim().toUpperCase())>=0; }
function isMixedBatch(b){ return batchPiList(b).length>1; }
/* 产品行归属哪个 PI: 优先行内 piNo; 单 PI 批次直接归该 PI; 旧混装数据按 SKU 反查(唯一命中才算) */
function prodPiOf(p,b){
  if(p&&p.piNo)return String(p.piNo).trim().toUpperCase();
  var list=batchPiList(b);
  if(list.length===1)return list[0];
  var hit=list.filter(function(pn){
    var pi=PIS.filter(function(x){return x.piNo===pn})[0];
    return pi&&(pi.products||[]).some(function(x){return String(x.sku)===String(p&&p.sku)});
  });
  return hit.length===1?hit[0]:'';
}
function batchQtyForPi(b,piNo){
  var want=String(piNo||'').trim().toUpperCase();
  return (b.products||[]).filter(function(p){return prodPiOf(p,b)===want}).reduce(function(s,p){return s+(Number(p.qty)||0)},0);
}
function batchShippedQty(piNo){
  return BATCHES.filter(function(b){return batchHasPi(b,piNo)}).reduce(function(s,b){return s+batchQtyForPi(b,piNo)},0);
}
function batchCountOf(piNo){ return BATCHES.filter(function(b){return batchHasPi(b,piNo)}).length; }
/* WMS(富皇美运 FDR) 入库单同步缓存: 入库日期/状态, /api/wms-inbound 自动刷新 */
var WMSIB={};
/* 富皇 OMS 后台入库费用同步缓存: 按入库单号(RO) → 卸货费/入库费, /api/oms-fee 自动刷新 */
var OMSFEE={};
function ibCurOf(b){ return (b&&b.inboundFeeCurrency)||'USD'; }
function ibDateOf(b){
  if(!b||!b.ro)return '';
  var w=WMSIB[String(b.ro).toUpperCase()];
  var d=w&&!w.missing&&(w.checkinDate||w.putawayDate||'');
  if(!d){ /* WMS 未覆盖时回落 FDR 库存流水的入库日期 */
    var t=((typeof TRACE!=='undefined'&&TRACE&&TRACE.inbound)||[]).filter(function(x){return String(x.ro).toUpperCase()===String(b.ro).toUpperCase()})[0];
    if(t&&t.roDate)d=t.roDate;
  }
  return d?String(d).slice(0,10):'';
}
function ibDateCell(b){
  var d=ibDateOf(b);
  if(d)return '<span title="WMS 入库日期（自动同步）">'+esc2(d)+'</span>';
  var w=b&&b.ro?WMSIB[String(b.ro).toUpperCase()]:null;
  if(w&&!w.missing&&w.estimatedDate)return '<span class="dim" title="WMS 预计到仓 '+esc2(w.estimatedDate)+'（尚未入库）">预计 '+esc2(String(w.estimatedDate).slice(0,10))+'</span>';
  return '<span class="dim">—</span>';
}
/* WMS 入库单缓存里的物流公司(富皇登记的 freight_company)。
   注: 用户明确「头程物流商我们自己填，你溯源不到」→ 当前 UI 不再自动带出, 此函数保留备用。 */
function wmsCarrierOf(ro){
  if(!ro)return '';
  var w=WMSIB[String(ro).toUpperCase()];
  return (w&&!w.missing&&w.freightCompany)?String(w.freightCompany):'';
}
/* 卸货费: 优先取富皇 OMS 后台自动同步值(按入库单号 RO 对应, 币种随账单);
   手填值作为补充 —— 仅当 OMS 查不到该入库单费用时(如 FBA/盘古德国仓不在富皇 WMS)才展示 */
function omsFeeOf(b){
  if(!b||!b.ro)return null;
  var r=OMSFEE[String(b.ro).toUpperCase()];
  return (r&&Number(r.unloadFee)>0)?r:null;
}
function ibFeeInfo(b){
  var manual=Number(b&&b.inboundFee)||0;
  var w=omsFeeOf(b);
  if(w)return {amt:Number(w.unloadFee)||0,cur:w.currency||'USD',src:'wms',billNo:w.billNo||'',date:w.date||'',manual:manual};
  if(manual)return {amt:manual,cur:ibCurOf(b),src:'manual',manual:manual};
  return null;
}
function ibFeeCell(b){
  var f=ibFeeInfo(b);
  if(!f)return '<span class="dim">—</span>';
  if(f.src==='wms'){
    var tip='富皇 OMS 自动同步的卸货费'+(f.billNo?('（账单 '+f.billNo+(f.date?('，'+String(f.date).slice(0,10)):'')+'）'):'');
    if(f.manual&&Math.abs(f.manual-f.amt)>0.005)tip+='；手填值 '+piMoney(f.manual,ibCurOf(b))+' 已被同步值覆盖';
    return '<span title="'+esc2(tip)+'">'+piMoney(f.amt,f.cur)+'</span>';
  }
  return '<span title="手动填写（富皇 OMS 暂无该入库单费用）">'+piMoney(f.amt,f.cur)+'</span>';
}
/* PI 金额口径: 产品行单价按录入口径记账; 含税总额/未税总额按 税率 折算 */
function piTotal(pi){ return (pi.products||[]).reduce(function(s,p){return s+(Number(p.amount)||0)},0); }
function piAmtInc(pi){ var t=piTotal(pi), r=Number(pi.taxRate)||0; return (pi.taxIncluded===false)?(t*(1+r/100)):t; }
function piAmtEx(pi){ var t=piTotal(pi), r=Number(pi.taxRate)||0; return (pi.taxIncluded===false)?t:(t/(1+r/100)); }
function piTaxLabel(pi){
  var r=Number(pi.taxRate)||0;
  return (pi.taxIncluded===false?'未税':'含税')+(r?(r%1?fmt(r,2):fmt(r,0))+'%':'');
}
function buildPi(){
  PI_READY=true;
  PIS=(PIF&&PIF.pis)||[];
  BATCHES=(PIF&&PIF.batches)||[];
  BATCHES.forEach(function(b){ if(b.products) b._qty=batchQty(b); });
  /* WMS 入库单缓存(入库日期列自动回填): 拉到后重渲染 */
  apiJson('GET',API_BASE+'/api/wms-inbound').then(function(r){
    if(r.status===200&&r.body&&r.body.list){ WMSIB=r.body.list||{}; if(PI_READY)renderPiAll(); }
  }).catch(function(){});
  /* 富皇 OMS 入库费用(卸货费自动同步): 拉到后重渲染 */
  apiJson('GET',API_BASE+'/api/oms-fee').then(function(r){
    if(r.status===200&&r.body&&r.body.byRo){ OMSFEE=r.body.byRo||{}; if(PI_READY)renderPiAll(); }
  }).catch(function(){});
  /* 海外仓 WMS 的 SKU 重量/尺寸档案(溯源按 kg 计费的数据源): 拉到后重渲染 */
  apiJson('GET',API_BASE+'/api/sku-weight').then(function(r){
    if(r.status===200&&r.body&&r.body.list){ SKU_W=r.body.list||{}; SKU_W_AT=r.body.updatedAt||''; if(PI_READY)renderPiAll(); }
  }).catch(function(){});
  // 徽标
  var badge=document.getElementById('piBadge');
  if(badge){ if(PIS.length){badge.style.display='';badge.textContent=PIS.length;} else badge.style.display='none'; }
  // 搜索框绑定
  var piqEl=document.getElementById('piq');
  if(piqEl && !piqEl._h){ piqEl._h=1; piqEl.addEventListener('input',function(e){PIQ=e.target.value;renderPiAll();}); }
  var pbqEl=document.getElementById('pbq');
  if(pbqEl && !pbqEl._h){ pbqEl._h=1; pbqEl.addEventListener('input',function(e){PBQ=e.target.value;renderPiAll();}); }
  // PI 行: 操作(编辑/删除) + 点击展开产品明细
  var tb=document.getElementById('piTbody');
  if(tb && !tb._h){ tb._h=1; tb.addEventListener('click',function(e){
    var op=e.target.closest('[data-op]');
    var tr=e.target.closest('tr'); if(!tr||!tr.hasAttribute('data-pino'))return;
    var pino=tr.getAttribute('data-pino');
    if(op){
      if(!LIVE){ piReadonlyTip(); return; }
      if(op.getAttribute('data-op')==='edit') piEdit(pino);
      else if(op.getAttribute('data-op')==='del') piDel(pino);
      return;
    }
    var nx=tr.nextSibling;
    if(nx && nx.classList && nx.classList.contains('pi-sub') && nx.getAttribute('data-for')===pino){ nx.parentNode.removeChild(nx); return; }
    if(nx && nx.classList && nx.classList.contains('pi-sub')) nx.parentNode.removeChild(nx);
    var pi=PIS.filter(function(p){return p.piNo===pino})[0];
    if(!pi)return;
    var sub=document.createElement('tr'); sub.className='pi-sub'; sub.setAttribute('data-for',pino);
    sub.innerHTML='<td colspan="12"><table><tr><th>SKU</th><th>商品名称</th><th class="num-r">数量</th><th class="num-r">成本单价</th><th class="num-r">退税率</th><th class="num-r">退税后单价</th><th class="num-r">金额</th></tr>'+
      (pi.products||[]).map(function(p){
        var rb=Number(p.rebate)||0;
        return '<tr><td class="mono">'+esc2(p.sku)+'</td><td>'+esc2(p.name||'—')+'</td>'+
          '<td class="num-r">'+fmt(p.qty)+'</td>'+
          '<td class="num-r">'+piMoney(p.unitPrice,pi.currency)+'</td>'+
          '<td class="num-r">'+(rb?fmt(rb,1)+'%':'<span class="dim">—</span>')+'</td>'+
          '<td class="num-r">'+(rb?piMoney(piRebUnit(p,pi),pi.currency):'<span class="dim">—</span>')+'</td>'+
          '<td class="num-r">'+piMoney(p.amount,pi.currency)+'</td></tr>';
      }).join('')+
      '<tr style="background:#1a2133"><td colspan="4" style="text-align:right"><b>价格口径</b></td><td colspan="3">'+esc2(piTaxLabel(pi))+' · 含税 '+piMoney(piAmtInc(pi),pi.currency)+' / 未税 '+piMoney(piAmtEx(pi),pi.currency)+'</td></tr>'+
      ((pi.products||[]).some(function(p){return Number(p.rebate)>0;})?
        '<tr style="background:#14273a"><td colspan="7" style="text-align:right">出口退税合计 <b style="color:#2ec4a6">'+piMoney(piRebateTotal(pi),pi.currency)+'</b> &nbsp;→&nbsp; 最终成本(合同−退税) <b>'+piMoney(piNetTotal(pi),pi.currency)+'</b></td></tr>':'')+
      '</table></td>';
    tr.parentNode.insertBefore(sub, tr.nextSibling);
  }); }
  // 批次行: 操作(编辑/删除) + 点击展开 SKU 明细(同 PI 列表交互)
  var pb=document.getElementById('pbTbody');
  if(pb && !pb._h){ pb._h=1; pb.addEventListener('click',function(e){
    var op=e.target.closest('[data-op]');
    var tr=e.target.closest('tr'); if(!tr||!tr.hasAttribute('data-bid'))return;
    var bid=tr.getAttribute('data-bid');
    if(op){
      if(!LIVE){ piReadonlyTip(); return; }
      if(op.getAttribute('data-op')==='edit') batchEdit(bid);
      else if(op.getAttribute('data-op')==='del') batchDel(bid);
      return;
    }
    var nx=tr.nextSibling;
    if(nx && nx.classList && nx.classList.contains('pi-sub') && nx.getAttribute('data-for')===bid){ nx.parentNode.removeChild(nx); return; }
    if(nx && nx.classList && nx.classList.contains('pi-sub')) nx.parentNode.removeChild(nx);
    var b=BATCHES.filter(function(x){return x.id===bid})[0]; if(!b)return;
    var mixed=isMixedBatch(b);
    var piOfRow=function(p){ var pn=prodPiOf(p,b); return pn?(PIS.filter(function(x){return x.piNo===pn})[0]||null):null; };
    var curOfRow=function(p){ var pi=piOfRow(p); return (pi&&pi.currency)||b.currency||'CNY'; };
    var prods=b.products||[];
    /* 退税后成本价: 按该行归属 PI 的含税/未税口径计算; 无归属 PI 的退化为批次行单价 */
    var netOf=function(p){ var pi=piOfRow(p); return pi?piRebUnit(p,pi):(Number(p.unitPrice)||0); };
    /* 混装批次各 PI 币种可能不同: 分币种合计, 不跨币种相加 */
    var sumMap={};
    prods.forEach(function(p){ var c=curOfRow(p); sumMap[c]=(sumMap[c]||0)+(Number(p.qty)||0)*netOf(p); });
    var sumTxt=Object.keys(sumMap).map(function(k){ return piMoney(sumMap[k],k); }).join(' + ')||'—';
    var piSum=[]; /* 各 PI 发货件数小计(混装时逐 PI 列出, 便于核对进度) */
    if(mixed){ batchPiList(b).forEach(function(pn){ piSum.push(pn+' '+fmt(batchQtyForPi(b,pn))+' 件'); }); }
    var sub=document.createElement('tr'); sub.className='pi-sub'; sub.setAttribute('data-for',bid);
    sub.innerHTML='<td colspan="16"><table><tr>'+(mixed?'<th>归属 PI</th>':'')+'<th>SKU</th><th>商品名称</th><th class="num-r">发货数量</th><th class="num-r">退税后成本价</th><th class="num-r">金额</th></tr>'+
      (prods.length?prods.map(function(p){
        var net=netOf(p), c=curOfRow(p), pn=prodPiOf(p,b);
        return '<tr>'+(mixed?('<td class="mono">'+(pn?esc2(pn):'<span class="dim">—</span>')+'</td>'):'')+
          '<td class="mono">'+esc2(p.sku)+'</td><td>'+esc2(p.name||'—')+'</td>'+
          '<td class="num-r">'+fmt(p.qty)+'</td>'+
          '<td class="num-r">'+piMoney(net,c)+'</td>'+
          '<td class="num-r">'+piMoney((Number(p.qty)||0)*net,c)+'</td></tr>';
      }).join(''):'<tr><td colspan="'+(mixed?6:5)+'" class="dim">该批次无产品明细（编辑后保存可补齐）</td></tr>')+
      '<tr style="background:#1a2133"><td colspan="'+(mixed?3:2)+'" style="text-align:right"><b>发货总件数</b>'+(piSum.length?(' <span class="row-note">（'+esc2(piSum.join(' · '))+'）</span>'):'')+'</td><td class="num-r"><b>'+fmt(batchQty(b))+'</b></td>'+
      '<td style="text-align:right">退税后成本合计</td><td class="num-r"><b>'+sumTxt+'</b></td></tr>'+
      '</table></td>';
    tr.parentNode.insertBefore(sub, tr.nextSibling);
  }); }
  // 点击遮罩关闭表单
  var fm=document.getElementById('fmModal');
  if(fm && !fm._h){ fm._h=1; fm.addEventListener('click',function(e){ if(e.target===this)closeFm(); }); }
}
function piStatusBadge(pi){
  var n=batchCountOf(pi.piNo);
  if(!n)return '<span class="badge b-wait">待发货</span>';
  var shipped=batchShippedQty(pi.piNo), total=(pi.products||[]).reduce(function(s,p){return s+(Number(p.qty)||0)},0);
  if(shipped>=total&&total>0)return '<span class="badge b-in">已发完</span>';
  return '<span class="badge b-pi">发货中 '+fmt(shipped)+'/'+fmt(total)+'</span>';
}
function piRow(pi){
  var n=batchCountOf(pi.piNo);
  return '<tr data-pino="'+esc2(pi.piNo)+'">'+
    '<td class="mono" style="cursor:pointer;color:#6aa4f5;text-decoration:underline dotted" title="点击查看产品明细">'+esc2(pi.piNo)+'</td>'+
    '<td class="mono">'+esc2(pi.date||'—')+'</td>'+
    '<td>'+esc2(pi.supplier||'—')+'</td>'+
    '<td>'+esc2(pi.currency||'CNY')+'</td>'+
    '<td class="num-r">'+(pi.products||[]).length+'</td>'+
    '<td class="num-r">'+fmt((pi.products||[]).reduce(function(s,p){return s+(Number(p.qty)||0)},0))+'</td>'+
    '<td class="num-r"><b>'+money(piAmtInc(pi),pi.currency,2)+'</b></td>'+
    '<td class="num-r">'+money(piAmtEx(pi),pi.currency,2)+'</td>'+
    '<td class="num-r">'+(Number(pi.taxRate)||0?esc2(piTaxLabel(pi)):'<span class="dim">—</span>')+'</td>'+
    '<td class="num-r">'+(n?('<span class="badge b-pi">'+n+'</span>'):'<span class="dim">—</span>')+'</td>'+
    '<td>'+piStatusBadge(pi)+'</td>'+
    '<td class="op-td"><span class="op-a" data-op="edit">编辑</span><span class="op-d" data-op="del">删除</span></td>'+
  '</tr>';
}
function renderPiAll(){
  var piTb=document.getElementById('piTbody'), piEmpty=document.getElementById('piEmpty');
  var pbTb=document.getElementById('pbTbody'), pbEmpty=document.getElementById('pbEmpty');
  /* 统计卡 */
  var cards=document.getElementById('piCards');
  if(cards){
    var incMap={},exMap={};
    PIS.forEach(function(p){
      var i=piAmtInc(p), e=piAmtEx(p), c=p.currency||'CNY';
      if(i){incMap[c]=(incMap[c]||0)+i;}
      if(e){exMap[c]=(exMap[c]||0)+e;}
    });
    var fMap={};
    BATCHES.forEach(function(b){ var f=Number(b.totalFreight)||0; if(f){var c=freightCurOf(b); fMap[c]=(fMap[c]||0)+f;} });
    var roCnt=BATCHES.filter(function(b){return b.ro}).length;
    var totalQty=PIS.reduce(function(s,p){return s+(p.products||[]).reduce(function(s2,x){return s2+(Number(x.qty)||0)},0)},0);
    var waitCnt=PIS.filter(function(p){return !batchCountOf(p.piNo)}).length;
    cards.innerHTML=
      '<div class="card blue"><div class="num">'+fmt(PIS.length)+'</div><div class="lbl">PI 单数</div></div>'+
      '<div class="card yellow"><div class="num">'+fmt(waitCnt)+'</div><div class="lbl">未发货 PI</div></div>'+
      '<div class="card green"><div class="num">'+fmt(totalQty)+'</div><div class="lbl">备货总件数</div></div>'+
      '<div class="card orange"><div class="num" style="font-size:20px">'+multiCur(incMap)+'</div><div class="lbl">含税金额合计</div></div>'+
      '<div class="card orange"><div class="num" style="font-size:20px">'+multiCur(exMap)+'</div><div class="lbl">未税金额合计</div></div>'+
      '<div class="card"><div class="num">'+fmt(BATCHES.length)+'</div><div class="lbl">头程发货批次</div></div>'+
      '<div class="card green"><div class="num">'+fmt(roCnt)+'</div><div class="lbl">已关联入库单</div></div>'+
      '<div class="card yellow"><div class="num" style="font-size:20px">'+multiCur(fMap)+'</div><div class="lbl">头程费用合计</div></div>';
  }
  /* PI 单列表 (分页) */
  var kw=PIQ.trim().toLowerCase();
  if(kw!==PIQ_LAST){ PIQ_LAST=kw; PAGE_ST.pi=0; } /* 搜索变化回第1页 */
  PIS_VIEW=PIS.filter(function(p){
    if(!kw)return true;
    return String(p.piNo).toLowerCase().indexOf(kw)>=0||String(p.supplier||'').toLowerCase().indexOf(kw)>=0||
      (p.products||[]).some(function(x){return String(x.sku).toLowerCase().indexOf(kw)>=0});
  }).sort(function(a,b){return a.piNo<b.piNo?-1:1});
  if(piEmpty)piEmpty.style.display=PIS_VIEW.length?'none':'block';
  if(piTb){ var pg1=pageSlice(PIS_VIEW,'pi'); piTb.innerHTML=pg1.list.map(piRow).join(''); setPager('pi',PIS_VIEW.length); }
  /* 头程批次 (分页) */
  var kw2=PBQ.trim().toLowerCase();
  if(kw2!==PBQ_LAST){ PBQ_LAST=kw2; PAGE_ST.pb=0; } /* 搜索变化回第1页 */
  BATCH_VIEW=BATCHES.filter(function(b){
    if(!kw2)return true;
    var hay=String(b.piNo||'')+' '+String(b.batchNo||'')+' '+String(b.exportNo||'')+' '+String(b.containerNo||'')+' '+String(b.trackingNo||'')+' '+String(b.ro||'')+' '+String(b.warehouse||'')+' '+String(b.country||'')+' '+String(b.carrier||'')+' '+(countryCell(b)||'');
    (b.products||[]).forEach(function(p){hay+=' '+String(p.sku||'');});
    return hay.toLowerCase().indexOf(kw2)>=0;
  }).sort(function(a,b){return String(a.shipDate||'')<String(b.shipDate||'')?1:-1});
  if(pbEmpty)pbEmpty.style.display=BATCH_VIEW.length?'none':'block';
  if(pbTb){
    var pg2=pageSlice(BATCH_VIEW,'pb');
    pbTb.innerHTML=pg2.list.map(function(b){
      var q=b._qty||batchQty(b);
      var fc=freightCurOf(b);
      var kg=Number(b.grossWeightKg)||0;
      var perKg=(kg>0&&(Number(b.totalFreight)||0)>0)?((Number(b.totalFreight)||0)/kg):0;
      /* 列顺序(用户拍板): PI单号(竖排)/批次/目的国/发货日期/件数/毛重/总费用/均摊 → 柜号·跟踪号(上下)/入库单号/入库日期/卸货费 → 方式/物流商 → 关联状态/操作 */
      var piArr=batchPiList(b);
      var piCell=piArr.length?('<span class="pi-stack">'+piArr.map(function(pn){return esc2(pn);}).join('<br>')+'</span>'):'<span class="dim">—</span>';
      return '<tr data-bid="'+esc2(b.id||'')+'">'+
        '<td class="mono" style="cursor:pointer;color:#6aa4f5;text-decoration:underline dotted" title="点击查看 SKU 明细">'+piCell+'</td>'+
        '<td class="mono">'+esc2(b.batchNo||'1')+'</td>'+
        '<td>'+countryCell(b)+'</td>'+
        '<td class="mono">'+esc2(b.shipDate||'—')+'</td>'+
        '<td class="num-r">'+fmt(q)+'</td>'+
        '<td class="num-r">'+fmt(kg,1)+'</td>'+
        '<td class="num-r"><b>'+money(b.totalFreight,fc,2)+'</b></td>'+
        '<td class="num-r">'+(perKg>0?('<b style="color:#2ec4a6">'+money3(perKg,fc)+'</b>'):'<span class="dim">—</span>')+'</td>'+
        '<td class="mono"><span class="tno-l1">'+(b.containerNo?esc2(b.containerNo):'<span class="dim">—</span>')+'</span><span class="tno-l2">'+(b.trackingNo?esc2(b.trackingNo):'<span class="dim">—</span>')+'</span></td>'+
        '<td class="mono">'+(b.ro?('<b style="color:#6aa4f5">'+esc2(b.ro)+'</b>'):'<span class="dim">未填</span>')+'</td>'+
        '<td class="mono">'+ibDateCell(b)+'</td>'+
        '<td class="num-r">'+ibFeeCell(b)+'</td>'+
        '<td>'+esc2(b.method||'海运')+'</td>'+
        '<td>'+(b.carrier?esc2(b.carrier):'<span class="dim">—</span>')+'</td>'+
        '<td>'+traceStatusCell(b)+'</td>'+
        '<td class="op-td"><span class="op-a" data-op="edit">编辑</span><span class="op-d" data-op="del">删除</span></td>'+
      '</tr>';
    }).join('');
    setPager('pb',BATCH_VIEW.length);
  }
  /* 入库单对照区/物流商比价/SKU 重量档案三块面板已按用户要求删除：
     关联状态并入批次表末列，入库重量/尺寸并入批次表，物流商手填。 */
  updPbSkuWAt();
}

/* SKU 重量/尺寸档案与物流商比价面板已删除；skuWRefresh 供批次表右上角「⟳ 同步 SKU 重量/尺寸」使用 */
function skuWRefresh(){
  if(!LIVE)return piReadonlyTip();
  var btn=event&&event.target; if(btn){btn.disabled=true;btn.textContent='同步中…';}
  apiJson('GET',API_BASE+'/api/sku-weight?force=1&cb='+Date.now()).then(function(r){
    if(btn){btn.disabled=false;btn.textContent='⟳ 同步 SKU 重量/尺寸';}
    if(r.status===200&&r.body&&r.body.list){
      SKU_W=r.body.list||{}; SKU_W_AT=r.body.updatedAt||'';
      RO_FEE=buildRoFeeIndex();
      renderPiAll(); renderTrace(); renderInbound();
      alert('已同步 '+Object.keys(SKU_W).length+' 个 SKU 的重量/尺寸档案（海外仓 WMS）');
    } else alert('同步失败：'+((r.body&&r.body.error)||'海外仓 WMS 未返回数据'));
  }).catch(function(){ if(btn){btn.disabled=false;btn.textContent='⟳ 同步 SKU 重量/尺寸';} alert('无法连接录入服务，同步失败'); });
}
/* 批次表右上角的同步时间提示 */
function updPbSkuWAt(){
  var el=document.getElementById('pbSkuWAt'); if(!el)return;
  var n=Object.keys(SKU_W).length;
  el.innerHTML=n?('SKU 档案 '+n+' 个 · 同步于 '+esc2(SKU_W_AT||'—')):'';
}

/* ================ 速卖通订单 / 月度利润 tab ================ */var AE_READY=false, AE_LIST=(AE&&AE.list)||[];
var AE_MONTH='', AE_ST='', AE_SHOP='', AE_Q='', AE_Q_LAST='';
var AE_VIEW=[];
/* 成本/汇率建议(从已有订单统计: 单件成本$众数, 最近汇率) */
var AE_SUG={cost:{},fx:{}};
function aeRebuildSug(){
  AE_SUG={cost:{},fx:{}};
  AE_LIST.forEach(function(o){
    var unit=o.qty>0?(o.cost||0)/o.qty:0;
    if(unit){ var c=AE_SUG.cost[o.sku]; if(!c||Math.abs(c-99)>1) { /* 取第一个非零作参考 */ } AE_SUG.cost[o.sku]=unit; }
    var fx=o.fx||0; if(fx)AE_SUG.fx[o.sku]=fx;
  });
}
function aeProfit(o){
  if(!o)return null;
  var fx=Number(o.fx)||0;
  if(fx<=0)return null;
  var base=(o.received===null||o.received===undefined||o.received==='')?((Number(o.estReceive)||0)-(Number(o.marketing)||0)):Number(o.received);
  var usd=(Number(o.shelfFee)||0)+(Number(o.storageFee)||0)+(Number(o.lastMile)||0)+(Number(o.cost)||0);
  /* 保留4位小数汇总(与 Excel 逐行缓存值一致)，避免逐行先舍到分再求和产生累计误差 */
  return Math.round((base-(Number(o.freight)||0)-usd*fx)*10000)/10000;
}
function aeStatus(o){ return (o.receivedAt)?'已放款':'预估'; }
function aeProfitCell(o){
  var p=aeProfit(o);
  if(p===null)return '<span class="dim">—</span>';
  return '<span style="color:'+(p>=0?'#ef6b5e':'#2ec4a6')+';font-weight:600">'+(p>=0?'+':'')+money(p,'CNY',2)+'</span>';
}
function aeMarginCell(o){
  var p=aeProfit(o);
  if(p===null)return '<span class="dim">—</span>';
  var sale=Number(o.sale)||0;
  if(!sale)return '<span class="dim">—</span>';
  var m=p/sale*100;
  return '<span style="color:'+(m>=0?'#ef6b5e':'#2ec4a6')+'">'+(m>=0?'+':'')+m.toFixed(2)+'%</span>';
}
function aeStatusBadge(o){
  return (o.receivedAt)
    ?'<span class="badge b-in">已放款</span>'
    :'<span class="badge b-wait" title="尚未放款，利润按「预计可得−平台营销」估算；补录到账金额/时间后自动实算">预估</span>';
}
/* ===== 经营总览：今日行 + KPI + 每日销量趋势(独立栏+日期滑轨) + SKU 出货（全部店铺全局口径） ===== */
var AE_OV_SIG='', AE_OV_CTX=null, AE_OVWIN={m:'all',right:-1};
var AE_WDAYS=['周日','周一','周二','周三','周四','周五','周六'];
/* 预置速卖通店铺: 下拉/录入表单可直选; 订单数据中出现的新店会自动并入选项 */
var AE_PRESET_SHOPS=['迈科深圳','迈科香港','法国 LITH ENERGY'];
function aeShopOptionsHtml(){
  var s={};
  (AE_PRESET_SHOPS||[]).forEach(function(x){s[x]=1;});
  (AE_LIST||[]).forEach(function(o){s[aeShopOf(o)]=1;});
  return Object.keys(s).map(function(k){return '<option value="'+esc2(k)+'">';}).join('');
}
/* 店铺名统一口径: 无 shop 的历史单视为默认店(迈科深圳), 迁移后即显式带 shop */
function aeShopOf(o){ return (o&&o.shop&&String(o.shop).trim())?String(o.shop).trim():'迈科深圳'; }
function aeOvDstr(d){ return d.getFullYear()+'-'+String(d.getMonth()+1).padStart(2,'0')+'-'+String(d.getDate()).padStart(2,'0'); }
function aeOvPrevMonth(ym){ var y=parseInt(ym.slice(0,4),10),m=parseInt(ym.slice(5,7),10); if(m===1){y--;m=12;}else{m--;} return y+'-'+String(m).padStart(2,'0'); }
function aeOvWeekRange(){
  var d=new Date(),o={};
  d.setDate(d.getDate()-((d.getDay()+6)%7)-7);   /* 上周一 */
  o.from=aeOvDstr(d);
  d.setDate(d.getDate()+6);                       /* 上周日 */
  o.to=aeOvDstr(d);
  return o;
}
function aeOvCurWeekRange(){
  var d=new Date(),o={};
  d.setDate(d.getDate()-((d.getDay()+6)%7));      /* 本周一 */
  o.from=aeOvDstr(d);
  d.setDate(d.getDate()+6);                        /* 本周日 */
  o.to=aeOvDstr(d);
  return o;
}
/* 销售额显示: 恒两位小数(用户要求销售额精确到分) */
function aeMoney(v){ return (v===null||v===undefined||isNaN(v))?'—':'¥'+Number(v).toLocaleString('zh-CN',{minimumFractionDigits:2,maximumFractionDigits:2}); }
function aeOvKpi(num,lbl,sub,cls){
  return '<div class="card '+cls+'" style="min-width:150px"><div class="num">'+num+'</div>'+
    '<div class="lbl">'+lbl+'</div>'+(sub?'<div class="lbl" style="font-size:10.5px;opacity:.72;margin-top:1px">'+sub+'</div>':'')+'</div>';
}
function aeOvAgg(rows,f){
  var A={n:0,qty:0,sale:0};
  rows.forEach(function(o){ if(f&&!f(o))return; A.n++; A.qty+=(Number(o.qty)||0); A.sale+=(Number(o.sale)||0); });
  return A;
}
function aeOvTodayCard(num,lbl,sub,grad){
  return '<div style="border-radius:12px;padding:14px 18px;background:'+grad+';color:#fff;border:1px solid rgba(255,255,255,.10);box-shadow:0 2px 10px rgba(0,0,0,.28)">'+
    '<div style="font-size:12px;opacity:.88;margin-bottom:3px">'+lbl+'</div>'+
    '<div style="font-size:30px;font-weight:700;line-height:1.15">'+num+'</div>'+
    '<div style="font-size:11px;opacity:.84;margin-top:5px">'+sub+'</div></div>';
}
/* 各 SKU × 月度聚合: months=有销量的月份(升序,yyyy-mm); mm[mo][sku]={qty,sale,n};
 * skuList=各 SKU 合计, 按出货件数降序。供「各 SKU 月度出货」图与矩阵表共用(同一份口径)。 */
function aeOvSkuAgg(rows){
  var mm={}, months=[], tot={};
  rows.forEach(function(o){
    var dt=o.date||'', k=o.sku||'(未填)';
    var t=tot[k]||(tot[k]={sku:k,qty:0,sale:0,n:0});
    t.qty+=(Number(o.qty)||0); t.sale+=(Number(o.sale)||0); t.n++;
    if(!/^\\d{4}-\\d{2}$/.test(dt.slice(0,7)))return;
    var mo=dt.slice(0,7);
    if(months.indexOf(mo)<0)months.push(mo);
    var mk=mm[mo]||(mm[mo]={});
    var g=mk[k]||(mk[k]={qty:0,sale:0,n:0});
    g.qty+=(Number(o.qty)||0); g.sale+=(Number(o.sale)||0); g.n++;
  });
  months.sort();
  var skuList=Object.keys(tot).map(function(k){return tot[k];}).sort(function(a,b){return b.qty-a.qty;});
  return {months:months, mm:mm, skuList:skuList};
}
function aeOvRender(){
  if(!AE_READY)return;
  var kp=document.getElementById('aeOvKpis');
  var note=document.getElementById('aeOvNote');
  var td=document.getElementById('aeOvToday');
  if(!kp||!note)return;
  var rows=(AE_SHOP)?(AE_LIST||[]).filter(function(o){return aeShopOf(o)===AE_SHOP;}):(AE_LIST||[]);
  var now=new Date();
  var today=aeOvDstr(now);
  var cm=today.slice(0,7), lm=aeOvPrevMonth(cm), wk=aeOvWeekRange(), twk=aeOvCurWeekRange();
  /* 店铺口径标签: 标题tag/说明/今日卡均显示当前统计的店铺 */
  var shopAll=[];(AE_LIST||[]).forEach(function(o){var s=aeShopOf(o);if(shopAll.indexOf(s)<0)shopAll.push(s);});
  var shopLbl=AE_SHOP||(shopAll.length===1?shopAll[0]:('全部店铺'+(shopAll.length>1?('('+shopAll.length+'家)'):'')));
  var ovTag=document.getElementById('aeOvTag');
  if(ovTag)ovTag.innerHTML='按销售日期 · '+esc2(shopLbl)+'（跟随顶部「店铺」筛选，增改订单自动刷新）';
  var tot=aeOvAgg(rows);
  var TDc=aeOvAgg(rows,function(o){return o.date===today;});
  var LMc=aeOvAgg(rows,function(o){return o.date&&o.date.slice(0,7)===lm;});
  var CMc=aeOvAgg(rows,function(o){return o.date&&o.date.slice(0,7)===cm;});
  var WKc=aeOvAgg(rows,function(o){return o.date&&o.date>=wk.from&&o.date<=wk.to;});
  var TWc=aeOvAgg(rows,function(o){return o.date&&o.date>=twk.from&&o.date<=twk.to;});
  var min='',max='';
  rows.forEach(function(o){ if(o.date){ if(!min||o.date<min)min=o.date; if(!max||o.date>max)max=o.date; } });
  note.innerHTML='统计店铺：<b>'+esc2(shopLbl)+'</b>（切换顶部「店铺」下拉，本区即按该店重算）。口径：按 <b>销售日期</b>（订单「日期」列）；<b>今日</b>= '+today+'（'+AE_WDAYS[now.getDay()]+'）；上月 <b>'+lm+'</b> · 本月 <b>'+cm+'</b>（至今）· 上周 <b>'+wk.from+' ~ '+wk.to+'</b> · 本周 <b>'+twk.from+' ~ '+twk.to+'</b>。销售额统一保留两位小数；每日销量曲线逐日连续，无销售日期按 0 计；录入/修改订单后自动重算。';
  /* 今日独立行(便于截图发群) */
  if(td){
    var hh=String(now.getHours()).padStart(2,'0')+':'+String(now.getMinutes()).padStart(2,'0');
    var tsub='（'+AE_WDAYS[now.getDay()]+'）· '+TDc.n+' 单 · 截至 '+hh;
    var tqsub='（'+AE_WDAYS[now.getDay()]+'）· 出库 '+fmt(TDc.qty)+' 件 / '+TDc.n+' 单'+(TDc.n?'':'（暂无出单，录单后自动刷新）');
    td.innerHTML=
      aeOvTodayCard(aeMoney(TDc.sale),'今日销售额（¥）· '+esc2(shopLbl),today+tsub,'linear-gradient(135deg,#4d8ff0,#123c6e)')+
      aeOvTodayCard(fmt(TDc.qty)+' 件','今日销量 · '+esc2(shopLbl),today+tqsub,'linear-gradient(135deg,#2ec4a6,#0a4636)');
  }
  kp.innerHTML=
    aeOvKpi(aeMoney(tot.sale),'累计销售额','首单 '+min+' 起 · '+tot.n+' 单','blue')+
    aeOvKpi(fmt(tot.qty),'累计销量(件)','全部 '+tot.n+' 笔订单','green')+
    aeOvKpi(aeMoney(LMc.sale),'上月销售额',lm+' 全月 · '+LMc.n+' 单','blue')+
    aeOvKpi(fmt(LMc.qty),'上月销量(件)',lm,'green')+
    aeOvKpi(aeMoney(CMc.sale),'本月销售额',cm+' 至今 · '+CMc.n+' 单','blue')+
    aeOvKpi(fmt(CMc.qty),'本月销量(件)',cm+' 至今','green')+
    aeOvKpi(aeMoney(WKc.sale),'上周销售额',wk.from+' ~ '+wk.to+' · '+WKc.n+' 单','orange')+
    aeOvKpi(fmt(WKc.qty),'上周销量(件)',wk.from.slice(5)+' ~ '+wk.to.slice(5),'orange')+
    aeOvKpi(aeMoney(TWc.sale),'本周销售额',twk.from+' ~ '+twk.to+' · '+TWc.n+' 单','teal')+
    aeOvKpi(fmt(TWc.qty),'本周销量(件)',twk.from.slice(5)+' ~ '+twk.to.slice(5),'teal');
  /* SKU × 月度出货明细表(动态月列; 与右侧月度柱图同一份聚合口径) */
  var SK=aeOvSkuAgg(rows);
  var hd=document.getElementById('aeOvSkuHd'), tb=document.getElementById('aeOvSkuTb');
  if(hd&&tb){
    if(SK.months.length){
      var my0=SK.months[0].slice(0,4), my1=SK.months[SK.months.length-1].slice(0,4);
      hd.innerHTML='<tr><th>SKU</th>'+
        SK.months.map(function(m){return '<th class="num-r" title="'+m+'">'+(my0===my1?(m.slice(5)+'月'):m)+'</th>';}).join('')+
        '<th class="num-r">合计件</th><th class="num-r">销售金额</th><th class="num-r">订单数</th></tr>';
      tb.innerHTML=SK.skuList.map(function(g){
        return '<tr><td>'+esc2(g.sku)+'</td>'+
          SK.months.map(function(m){
            var v=(SK.mm[m][g.sku]||{qty:0}).qty;
            return '<td class="num-r"'+(v?'':' style="color:#c9c9c9"')+'>'+(v?v:0)+'</td>';
          }).join('')+
          '<td class="num-r"><b>'+fmt(g.qty)+'</b></td>'+
          '<td class="num-r">'+aeMoney(g.sale)+'</td><td class="num-r">'+fmt(g.n)+'</td></tr>';
      }).join('');
    } else {
      hd.innerHTML='<tr><th>SKU</th><th class="num-r">合计件</th><th class="num-r">销售金额</th><th class="num-r">订单数</th></tr>';
      tb.innerHTML='<tr><td colspan="4" style="text-align:center;color:#999;padding:14px">暂无订单数据</td></tr>';
    }
  }
  /* 图表仅在数据变化时重建(避免搜索/翻页触发闪烁); ae tab 未显示时延后到切回再画 */
  var sig=(AE_SHOP||'*')+'|'+rows.length+':'+rows.map(function(o){return o.date+'|'+(o.qty||0)+'|'+Math.round((Number(o.sale)||0));}).join(',');
  if(sig===AE_OV_SIG)return;
  AE_OV_SIG=sig;
  var pan=document.getElementById('tab-ae');
  if(pan&&pan.style.display==='none')return;
  drawAeOvCharts(rows,min,max,today,SK);
}
function drawAeOvCharts(rows,min,max,today,SK){
  var dOld=Chart.getChart('aeOvDaily'); if(dOld)dOld.destroy();
  var sOld=Chart.getChart('aeOvSku'); if(sOld)sOld.destroy();
  var dBox=document.getElementById('aeOvDailyBox');
  var sBox=document.getElementById('aeOvSkuBox');
  var r0=document.getElementById('aeOvRange');
  if(!rows.length){
    if(dBox)dBox.innerHTML='<p class="empty" style="padding:60px 0">暂无订单：录入第一单后自动生成每日销量平滑曲线</p>';
    if(sBox)sBox.innerHTML='<p class="empty" style="padding:40px 0">暂无订单数据</p>';
    if(r0){r0.min=0;r0.max=0;r0.value=0;r0.disabled=true;}
    var a0=document.getElementById('aeOvWinA'),b0=document.getElementById('aeOvWinB');
    if(a0)a0.textContent=''; if(b0)b0.textContent='';
    return;
  }
  if(dBox&&!dBox.querySelector('#aeOvDaily'))dBox.innerHTML='<canvas id="aeOvDaily"></canvas>';
  if(sBox&&!sBox.querySelector('#aeOvSku'))sBox.innerHTML='<canvas id="aeOvSku"></canvas>';
  /* 图1: 逐日销量(件) + 销售额(¥) 平滑曲线, 首单日 → 今天(或末单日); 整行独立一栏 + 日期滑轨 */
  var cv=document.getElementById('aeOvDaily');
  var end=(max>today)?max:today;
  var labels=[],fullD=[],q=[],s=[],dm={},d=new Date(min+'T00:00:00');
  rows.forEach(function(o){ var dt=o.date||''; var g=dm[dt]||(dm[dt]={q:0,s:0}); g.q+=(Number(o.qty)||0); g.s+=(Number(o.sale)||0); });
  while(true){
    var ds=aeOvDstr(d);
    labels.push(ds.slice(5));
    fullD.push(ds);
    var g=dm[ds];
    q.push(g?g.q:0); s.push(g?Math.round(g.s*100)/100:0);
    if(ds>=end)break;
    d.setDate(d.getDate()+1);
  }
  AE_OV_CTX={fullD:fullD};
  var total=labels.length;
  var wm=AE_OVWIN.m||'all';
  var win=(wm==='all')?total:(parseInt(wm,10)||total); if(win>total)win=total; if(win<1)win=1;
  var hi=AE_OVWIN.right;
  if(isNaN(hi)||hi<win-1||hi>total-1)hi=total-1;
  var lo=hi-win+1;
  if(wm==='all'||total<=1){ if(r0){r0.min=0;r0.max=0;r0.value=0;r0.disabled=true;} lo=0; hi=total-1; }
  else if(r0){ r0.min=win-1; r0.max=total-1; r0.value=hi; r0.disabled=false; }
  AE_OVWIN.right=hi;
  aeOvWinTxt(wm,win,lo,hi,total);
  new Chart(cv,{type:'line',
    data:{labels:labels,datasets:[
      {label:'日销量(件)',data:q,borderColor:'#4d8ff0',backgroundColor:'rgba(77,143,240,.16)',fill:true,cubicInterpolationMode:'monotone',borderWidth:2,pointRadius:0,pointHoverRadius:3},
      {label:'日销售额(¥)',data:s,yAxisID:'y1',borderColor:'#ef6b5e',backgroundColor:'rgba(176,58,46,.05)',fill:false,cubicInterpolationMode:'monotone',borderWidth:1.6,borderDash:[5,3],pointRadius:0,pointHoverRadius:3}
    ]},
    options:{responsive:true,maintainAspectRatio:false,interaction:{mode:'index',intersect:false},
      scales:{x:{min:(wm==='all')?undefined:lo,max:(wm==='all')?undefined:hi,ticks:{maxTicksLimit:14,maxRotation:0,autoSkip:true,font:{size:10.5}}},
        y:{beginAtZero:true,ticks:{precision:0,font:{size:10.5}},title:{display:true,text:'件 / 天',font:{size:10.5}}},
        y1:{position:'right',beginAtZero:true,grid:{drawOnChartArea:false},ticks:{font:{size:10.5},callback:function(v){return v>=1000?(v/1000).toFixed(1)+'k':'¥'+v;}},title:{display:true,text:'¥ / 天',font:{size:10.5}}}},
      plugins:{legend:{labels:{boxWidth:12,font:{size:11}}},
        tooltip:{callbacks:{
          title:function(items){ return fullD[items[0].dataIndex]||''; },
          label:function(ctx){
            var y=ctx.parsed.y;
            return (ctx.dataset.label||'')+': '+(ctx.dataset.yAxisID==='y1'?aeMoney(y):fmt(y)+' 件');
          }
        }}
      }
    }
  });
  /* 图2: 各 SKU 月度出货量(件) 纵向分组柱 — x=有销量月份, 每 SKU 一组同色柱 */
  var bcv=document.getElementById('aeOvSku');
  if(!SK)SK=aeOvSkuAgg(rows);
  var mLbl=(function(){
    if(!SK.months.length)return [];
    var y0=SK.months[0].slice(0,4), y1=SK.months[SK.months.length-1].slice(0,4);
    return SK.months.map(function(m){ return (y0===y1)?(m.slice(5)+'月'):m; });
  })();
  var palette=['#4d8ff0','#2ec4a6','#7c5cff','#e5a84e','#48c9e6','#d97bb0'];
  new Chart(bcv,{type:'bar',
    data:{labels:mLbl,datasets:SK.skuList.map(function(g,i){
      return {label:g.sku,
        data:SK.months.map(function(m){return (SK.mm[m][g.sku]||{qty:0}).qty;}),
        backgroundColor:palette[i%palette.length],borderRadius:3,
        barPercentage:.82,categoryPercentage:.6,maxBarThickness:40};
    })},
    options:{responsive:true,maintainAspectRatio:false,interaction:{mode:'index',intersect:false},
      scales:{x:{ticks:{font:{size:10.5},maxRotation:0,autoSkip:true,maxTicksLimit:24}},
        y:{beginAtZero:true,ticks:{precision:0,font:{size:10.5}},title:{display:true,text:'件 / 月',font:{size:10.5}}}},
      plugins:{legend:{position:'bottom',labels:{boxWidth:12,font:{size:11}}},
        tooltip:{callbacks:{
          title:function(items){ return SK.months[items[0].dataIndex]||''; },
          label:function(ctx){
            var g=(SK.mm[SK.months[ctx.dataIndex]]||{})[ctx.dataset.label];
            return (ctx.dataset.label||'')+': '+fmt(ctx.parsed.y)+' 件';
          },
          afterBody:function(items){
            var g=(SK.mm[SK.months[items[0].dataIndex]]||{})[items[0].dataset.label];
            return ['销售金额 '+aeMoney(g?g.sale:0),'订单 '+fmt(g?g.n:0)+' 单'];
          }
        }}
      }
    }
  });
}
function aeOvWinTxt(wm,win,lo,hi,total){
  var A=document.getElementById('aeOvWinA'),B=document.getElementById('aeOvWinB');
  if(!A&&!B)return;
  var f=AE_OV_CTX?AE_OV_CTX.fullD:null;
  if(A)A.textContent=(f?(total+' 天 · '):'')+((wm!=='all'&&f&&f[lo])?String(f[lo]).slice(5):'');
  if(B)B.textContent=(wm==='all'||!f)?'（全部日期）':' ~ '+String(f[hi]||'').slice(5);
}
function aeOvApplyWin(){
  var sel=document.getElementById('aeOvWin');
  if(sel)AE_OVWIN.m=sel.value;
  var rng=document.getElementById('aeOvRange');
  if(rng&&!rng.disabled)AE_OVWIN.right=parseInt(rng.value,10);
  if(!AE_OV_CTX||!AE_OV_CTX.fullD)return;
  var dOld=Chart.getChart('aeOvDaily'); if(!dOld)return;
  var total=AE_OV_CTX.fullD.length;
  var wm=AE_OVWIN.m||'all';
  var win=(wm==='all')?total:(parseInt(wm,10)||total); if(win>total)win=total; if(win<1)win=1;
  var hi=AE_OVWIN.right; if(isNaN(hi)||hi<win-1||hi>total-1)hi=total-1;
  var lo=hi-win+1;
  if(wm==='all'){ if(rng){rng.min=0;rng.max=0;rng.value=0;rng.disabled=true;} lo=0; hi=total-1; }
  else if(rng){ rng.min=win-1; rng.max=total-1; rng.value=hi; rng.disabled=false; }
  AE_OVWIN.right=hi;
  var o=dOld.options;
  o.scales.x.min=(wm==='all')?undefined:lo;
  o.scales.x.max=(wm==='all')?undefined:hi;
  dOld.update('none');
  aeOvWinTxt(wm,win,lo,hi,total);
}
function buildAe(){
  AE_READY=true;
  var badge=document.getElementById('aeBadge');
  if(badge){ if(AE_LIST.length){badge.style.display='';badge.textContent=AE_LIST.length;} else badge.style.display='none'; }
  aeRebuildSug();
  /* 店铺下拉填充(预置店 + 订单数据中出现的新店; 历史单无 shop 视为默认店=迈科深圳) */
  var ss={};
  (AE_PRESET_SHOPS||[]).forEach(function(s){ss[s]=1;});
  AE_LIST.forEach(function(o){ ss[aeShopOf(o)]=1; });
  var shSel=document.getElementById('aeShop');
  if(shSel && !shSel._h){
    shSel._h=1;
    var shopHtml='<option value="">全部店铺</option>';
    Object.keys(ss).sort().forEach(function(s){ shopHtml+='<option value="'+esc2(s)+'">'+esc2(s)+'</option>'; });
    shSel.innerHTML=shopHtml;
    shSel.addEventListener('change',function(e){ AE_SHOP=e.target.value; PAGE_ST.ae=0; renderAeAll(); });
  }
  /* 月份下拉填充 */
  var ms={};
  AE_LIST.forEach(function(o){ if(o.date&&/^\\d{4}-\\d{2}/.test(o.date))ms[o.date.slice(0,7)]=1; });
  var mSel=document.getElementById('aeMonth');
  if(mSel && !mSel._h){
    mSel._h=1;
    var html='<option value="">全部月份</option>';
    Object.keys(ms).sort(function(a,b){return a<b?1:-1}).forEach(function(m){ html+='<option value="'+esc2(m)+'">'+m+'</option>'; });
    mSel.innerHTML=html;
    mSel.addEventListener('change',function(e){ AE_MONTH=e.target.value; PAGE_ST.ae=0; renderAeAll(); });
  }
  var stSel=document.getElementById('aeSt'), stSep=document.getElementById('aeStSep');
  if(stSel){ stSel.style.display=''; if(stSep)stSep.style.display=''; if(!stSel._h){ stSel._h=1; stSel.addEventListener('change',function(e){ AE_ST=e.target.value; PAGE_ST.ae=0; renderAeAll(); }); } }
  /* 搜索 */
  var qEl=document.getElementById('aeq');
  if(qEl && !qEl._h){ qEl._h=1; qEl.addEventListener('input',function(e){ AE_Q=e.target.value; PAGE_ST.ae=0; renderAeAll(); }); }
  /* 行: 单元格内联编辑 + 编辑/删除 */
  var tb=document.getElementById('aeTbody');
  if(tb && !tb._h){ tb._h=1; tb.addEventListener('click',function(e){
    var td=e.target.closest('td.ae-c');
    if(td){ aeCellEdit(td); return; }
    var op=e.target.closest('[data-op]');
    var tr=e.target.closest('tr'); if(!tr||!tr.hasAttribute('data-on')||!op)return;
    if(!LIVE){ piReadonlyTip(); return; }
    var on=tr.getAttribute('data-on');
    if(op.getAttribute('data-op')==='edit') aeEdit(on);
    else if(op.getAttribute('data-op')==='del') aeDel(on);
  }); }
  /* 月度利润表: 点击行筛选月份(自动跳回明细视图) */
  var mtb=document.getElementById('aeMonthTbody');
  if(mtb && !mtb._h){ mtb._h=1; mtb.addEventListener('click',function(e){
    var tr=e.target.closest('tr[data-m]'); if(!tr)return;
    var m=tr.getAttribute('data-m');
    if(m==='__ALL__'){ AE_MONTH=''; }
    else{ AE_MONTH=(AE_MONTH===m)?'':m; }
    var mSel2=document.getElementById('aeMonth');
    if(mSel2)mSel2.value=AE_MONTH;
    PAGE_ST.ae=0; aeSetView('detail'); renderAeAll();
  }); }
}
function renderAeAll(){
  aeOvRender();   /* 经营总览(全局KPI+曲线+SKU出货): 数据变化才重建图表 */
  /* 顶部卡片: 当前筛选(AE_MONTH/AE_ST) */
  var cards=document.getElementById('aeCards');
  if(cards){
    var ls=AE_LIST.filter(aeFilt);
    var sum={n:0,qty:0,sale:0,rcv:0,mkt:0,frt:0,shelf:0,store:0,tail:0,cost:0,fx:0,profit:0};
    ls.forEach(function(o){
      sum.n++; sum.qty+=(Number(o.qty)||0);
      sum.sale+=(Number(o.sale)||0); sum.rcv+=aeBaseAmt(o);
      sum.mkt+=(Number(o.marketing)||0); sum.frt+=(Number(o.freight)||0);
      sum.shelf+=(Number(o.shelfFee)||0); sum.store+=(Number(o.storageFee)||0); sum.tail+=(Number(o.lastMile)||0);
      sum.cost+=(Number(o.cost)||0);
      var p=aeProfit(o); if(p!==null)sum.profit+=p;
    });
    var cur=ls.length?ls[ls.length-1].fx:0;
    var fdr=(sum.shelf+sum.store+sum.tail)*(cur||0);
    var costY=(sum.cost)*(cur||0);
    var lblParts=[];
    if(AE_SHOP){ lblParts.push(esc2(AE_SHOP)); }
    else{
      var _sc=[]; AE_LIST.forEach(function(o){var s=aeShopOf(o);if(_sc.indexOf(s)<0)_sc.push(s);});
      lblParts.push(_sc.length===1?esc2(_sc[0]):('全部店铺'+(_sc.length>1?('('+_sc.length+'家)'):'')));
    }
    if(AE_MONTH)lblParts.push(AE_MONTH+' 订单');
    if(lblParts.length===1)lblParts.push(AE_ST?(AE_ST+' 订单'):'订单');
    var lbl=lblParts.join(' · ');
    cards.innerHTML=
      '<div class="card blue"><div class="num">'+fmt(sum.n)+'</div><div class="lbl">'+lbl+'</div></div>'+
      '<div class="card"><div class="num">'+fmt(sum.qty)+'</div><div class="lbl">总件数</div></div>'+
      '<div class="card green"><div class="num">'+aeMoney(sum.sale)+'</div><div class="lbl">销售金额</div></div>'+
      '<div class="card green"><div class="num">'+aeMoney(sum.rcv)+'</div><div class="lbl">到账金额</div></div>'+
      '<div class="card orange"><div class="num">'+aeMoney(sum.mkt)+'</div><div class="lbl">平台营销费</div></div>'+
      '<div class="card orange"><div class="num">'+aeMoney(sum.frt)+'</div><div class="lbl">头程运费</div></div>'+
      '<div class="card orange"><div class="num">'+aeMoney(fdr)+'</div><div class="lbl">海外仓费用</div></div>'+
      '<div class="card orange"><div class="num">'+aeMoney(costY)+'</div><div class="lbl">产品成本</div></div>'+
      '<div class="card" style="background:linear-gradient(135deg,'+(sum.profit>=0?'rgba(239,107,94,.24)':'rgba(46,196,166,.22)')+',#141a28);border:1px solid '+(sum.profit>=0?'rgba(239,107,94,.42)':'rgba(46,196,166,.38)')+'"><div class="num" style="color:'+(sum.profit>=0?'#ef6b5e':'#2ec4a6')+'">'+aeMoney(sum.profit)+'</div><div class="lbl" style="color:var(--sub)">毛利润(¥)</div></div>'+
      '<div class="card"><div class="num">'+(sum.sale>0?((sum.profit/sum.sale*100).toFixed(2)+'%'):'—')+'</div><div class="lbl">毛利率</div></div>';
  }
  /* 月度利润总览 */
  var mtb=document.getElementById('aeMonthTbody'), mep=document.getElementById('aeMonthEmpty');
  var mm={};
  var shopRows=(AE_SHOP)?AE_LIST.filter(function(o){return aeShopOf(o)===AE_SHOP;}):AE_LIST;
  shopRows.forEach(function(o){
    var m=o.date?o.date.slice(0,7):'';
    if(!/^\\d{4}-\\d{2}$/.test(m))return;
    var g=mm[m]||(mm[m]={m:m,n:0,qty:0,sale:0,rcv:0,mkt:0,frt:0,sf:0,st:0,tl:0,cost:0,pr:0,fx:0});
    g.n++; g.qty+=(Number(o.qty)||0); g.sale+=(Number(o.sale)||0);
    g.rcv+=aeBaseAmt(o); g.mkt+=(Number(o.marketing)||0); g.frt+=(Number(o.freight)||0);
    g.sf+=(Number(o.shelfFee)||0); g.st+=(Number(o.storageFee)||0); g.tl+=(Number(o.lastMile)||0);
    g.cost+=(Number(o.cost)||0);
    var p=aeProfit(o); if(p!==null)g.pr+=p;
    var fx=Number(o.fx)||0; if(fx)g.fx=fx;
  });
  var mKeys=Object.keys(mm).sort(function(a,b){return a<b?1:-1});
  if(mep)mep.style.display=mKeys.length?'none':'block';
  if(mtb){
    var rows='';
    mKeys.forEach(function(m){
      var g=mm[m], cur=g.fx||0;
      var fdr=(g.sf+g.st+g.tl)*cur, costY=g.cost*cur;
      var on=(AE_MONTH===m)?' style="background:#1b2c4a;cursor:pointer"':' style="cursor:pointer"';
      rows+='<tr data-m="'+esc2(m)+'"'+on+' title="点击筛选/取消该月订单">'+
        '<td class="mono"><b>'+esc2(m)+'</b></td><td class="num-r">'+fmt(g.n)+'</td><td class="num-r">'+fmt(g.qty)+'</td>'+
        '<td class="num-r">'+aeMoney(g.sale)+'</td><td class="num-r">'+aeMoney(g.rcv)+'</td>'+
        '<td class="num-r">'+aeMoney(g.mkt)+'</td><td class="num-r">'+aeMoney(g.frt)+'</td>'+
        '<td class="num-r">'+aeMoney(fdr)+'</td><td class="num-r">'+aeMoney(costY)+'</td>'+
        '<td class="num-r"><b style="color:'+(g.pr>=0?'#ef6b5e':'#2ec4a6')+'">'+aeMoney(g.pr)+'</b></td>'+
        '<td class="num-r">'+(g.sale>0?((g.pr/g.sale*100).toFixed(2)+'%'):'—')+'</td></tr>';
    });
    /* 合计(全部) */
    var T={n:0,qty:0,sale:0,rcv:0,mkt:0,frt:0,sf:0,st:0,tl:0,cost:0,pr:0,fx:0};
    Object.keys(mm).forEach(function(m){ var g=mm[m]; ['n','qty','sale','rcv','mkt','frt','sf','st','tl','cost','pr'].forEach(function(k){T[k]+=g[k];}); T.fx=g.fx||T.fx; });
    var tcur=T.fx||0, tfdr=(T.sf+T.st+T.tl)*tcur, tcost=T.cost*tcur;
    rows+='<tr data-m="__ALL__" title="点击回到全部"'+(AE_MONTH===''?' style="background:#1a2133;cursor:pointer"':' style="background:#1a2133;cursor:pointer;font-weight:700')+'>'+
      '<td><b>合计</b></td><td class="num-r">'+fmt(T.n)+'</td><td class="num-r">'+fmt(T.qty)+'</td>'+
      '<td class="num-r">'+aeMoney(T.sale)+'</td><td class="num-r">'+aeMoney(T.rcv)+'</td>'+
      '<td class="num-r">'+aeMoney(T.mkt)+'</td><td class="num-r">'+aeMoney(T.frt)+'</td>'+
      '<td class="num-r">'+aeMoney(tfdr)+'</td><td class="num-r">'+aeMoney(tcost)+'</td>'+
      '<td class="num-r"><b style="color:'+(T.pr>=0?'#ef6b5e':'#2ec4a6')+'">'+aeMoney(T.pr)+'</b></td>'+
      '<td class="num-r">'+(T.sale>0?((T.pr/T.sale*100).toFixed(2)+'%'):'—')+'</td></tr>';
    mtb.innerHTML=rows;
  }
  /* 订单明细(筛选+搜索+分页) */
  var kw=AE_Q.trim().toLowerCase();
  if(kw!==AE_Q_LAST){ AE_Q_LAST=kw; PAGE_ST.ae=0; }
  AE_VIEW=AE_LIST.filter(function(o){
    if(AE_SHOP&&aeShopOf(o)!==AE_SHOP)return false;
    if(AE_MONTH&&(!o.date||o.date.slice(0,7)!==AE_MONTH))return false;
    if(AE_ST&&aeStatus(o)!==AE_ST)return false;
    if(!kw)return true;
    return String(o.orderNo).toLowerCase().indexOf(kw)>=0||aeShopOf(o).toLowerCase().indexOf(kw)>=0||String(o.sku).toLowerCase().indexOf(kw)>=0||String(o.warehouse||'').toLowerCase().indexOf(kw)>=0||String(o.remark||'').toLowerCase().indexOf(kw)>=0;
  }).sort(function(a,b){ return a.date<b.date?1:(a.date>b.date?-1:(a.orderNo<b.orderNo?1:-1)); });
  var empty=document.getElementById('aeEmpty');
  if(empty){
    empty.style.display=AE_VIEW.length?'none':'block';
    empty.textContent=AE_LIST.length?('没有匹配的订单（试试调整月份/状态/搜索）。'):'还没有速卖通订单，点右上角「＋ 新增订单」录入第一单。';
  }
  var tb=document.getElementById('aeTbody');
  if(tb){
    var pg=pageSlice(AE_VIEW,'ae',20);
    tb.innerHTML=pg.list.map(function(o,i){ return aeRow(o,pg.st*20+i+1); }).join('');
    setPager('ae',AE_VIEW.length,20);
    /* 合计行(当前筛选范围 AE_VIEW) */
    var ft=document.getElementById('aeFoot'), cnt=document.getElementById('aeCnt');
    if(cnt)cnt.textContent=AE_LIST.length+' 条记录 · 当前显示 '+AE_VIEW.length+' 条';
    if(ft){
      if(!AE_VIEW.length){ ft.innerHTML=''; }
      else{
        var S={sale:0,rcv:0,mkt:0,frt:0,sf:0,st:0,tl:0,cost:0,pr:0};
        AE_VIEW.forEach(function(o){
          S.sale+=(Number(o.sale)||0); S.rcv+=aeBaseAmt(o); S.mkt+=(Number(o.marketing)||0);
          S.frt+=(Number(o.freight)||0); S.sf+=(Number(o.shelfFee)||0); S.st+=(Number(o.storageFee)||0);
          S.tl+=(Number(o.lastMile)||0); S.cost+=(Number(o.cost)||0);
          var p=aeProfit(o); if(p!==null)S.pr+=p;
        });
        ft.innerHTML='<tr>'+
          '<td class="rowno">Σ</td><td colspan="3">合计（当前筛选 '+AE_VIEW.length+' 单）</td>'+
          '<td></td><td></td>'+
          '<td></td>'+
          '<td class="ae-num">'+(Number(S.sale)?aeMoney(S.sale):'<span class="dim">¥0</span>')+'</td><td></td><td></td>'+
          '<td class="ae-num">'+(Number(S.mkt)?aeMoney(S.mkt):'<span class="dim">¥0</span>')+'</td>'+
          '<td class="ae-num">'+(Number(S.frt)?aeMoney(S.frt):'<span class="dim">¥0</span>')+'</td>'+
          '<td class="ae-num">'+fmt(S.sf,2)+'</td><td class="ae-num">'+fmt(S.st,2)+'</td><td class="ae-num">'+fmt(S.tl,2)+'</td>'+
          '<td class="ae-num">'+(Number(S.rcv)?aeMoney(S.rcv):'<span class="dim">¥0</span>')+'</td><td></td><td class="ae-num">'+fmt(S.cost,2)+'</td><td></td>'+
          '<td class="ae-num" style="color:'+(S.pr>=0?'#ef6b5e':'#2ec4a6')+'">'+money(S.pr,'CNY',0)+'</td>'+
          '<td class="ae-num">'+(S.sale>0?((S.pr/S.sale*100).toFixed(2)+'%'):'—')+'</td>'+
          '<td colspan="3"></td></tr>';
      }
    }
  }
}
function aeFilt(o){
  if(AE_SHOP&&aeShopOf(o)!==AE_SHOP)return false;
  if(AE_MONTH&&(!o.date||o.date.slice(0,7)!==AE_MONTH))return false;
  if(AE_ST&&aeStatus(o)!==AE_ST)return false;
  return true;
}
/* ---- 智能表格: 视图切换(明细 / 月度汇总) ---- */
function aeSetView(v){
  var d=document.getElementById('aeDetailView'), m=document.getElementById('aeMonthView');
  if(d)d.style.display=(v==='detail')?'':'none';
  if(m)m.style.display=(v==='month')?'':'none';
  document.querySelectorAll('.ae-vtab').forEach(function(el){ el.classList.toggle('active',el.getAttribute('data-v')===v); });
  if(v==='month')renderAeAll();
}
/* ---- 智能表格: 单元格内联编辑 ---- */
var AE_EDITING=false;
function aeCellEdit(td){
  if(!LIVE){ piReadonlyTip(); return; }
  if(AE_EDITING)return;
  var on=td.getAttribute('data-on')||(td.closest('tr')&&td.closest('tr').getAttribute('data-on'));
  var k=td.getAttribute('data-k'), ty=td.getAttribute('data-t')||'text';
  if(!on||!k)return;
  var tr=td.closest('tr'); on=tr.getAttribute('data-on');
  var o=AE_LIST.filter(function(x){return x.orderNo===on})[0];
  if(!o)return;
  AE_EDITING=true;
  var cur=(o[k]===null||o[k]===undefined)?'':String(o[k]);
  var inp=document.createElement('input');
  inp.className='ae-cell-inp'; inp.type='text'; inp.value=cur; inp.style.textAlign=(ty==='num')?'right':'left';
  td.innerHTML=''; td.appendChild(inp);
  inp.focus(); inp.select();
  var finished=false;
  var finish=function(save){
    if(finished)return; finished=true; AE_EDITING=false;
    if(!save){ renderAeAll(); return; }
    var v=inp.value.trim();
    if(v===cur){ renderAeAll(); return; }
    if((k==='date'||k==='receivedAt')&&v!==''&&!/^\\d{4}-\\d{2}-\\d{2}$/.test(v)){ alert('日期格式需为 YYYY-MM-DD，如 2026-08-19'); renderAeAll(); return; }
    if(ty==='num'&&v!==''){
      var n=Number(v);
      if(isNaN(n)||n<0){ alert('请输入有效的非负数字'); renderAeAll(); return; }
      v=n;
    }
    var upd={}; Object.keys(o).forEach(function(kk){ upd[kk]=o[kk]; });
    upd[k]=v;
    apiJson('POST',API_BASE+'/api/ae/list',upd).then(function(r){
      if(r.status===200&&r.body&&r.body.ok){
        /* 本地更新即时生效: 不整页重建(避免打断正在进行的连续编辑) */
        var tgt=null;
        AE_LIST.forEach(function(x,i){ if(x.orderNo===on){ tgt=AE_LIST[i]; } });
        if(tgt)Object.assign(tgt,upd);
        aeRebuildSug(); renderAeAll();
      }
      else{ alert((r.body&&r.body.error)?('保存失败：'+r.body.error):'保存失败'); renderAeAll(); }
    }).catch(function(){ alert('无法连接录入服务，保存失败'); renderAeAll(); });
  };
  inp.onblur=function(){ finish(true); };
  inp.onkeydown=function(e){
    if(e.key==='Enter'){ e.preventDefault(); inp.blur(); }
    else if(e.key==='Escape'){ e.preventDefault(); finish(false); }
  };
}
/* ---- 导出 Excel(带公式, 给财务二次核对) ---- */
function aeExport(){
  var build=API_BASE;
  if(build){
    var _t=getToken();
    if(!_t){ aeExportNeedLogin(); return; }
    var send=function(retried){
      var btn=document.querySelector('.ae-export-btn');
      if(btn){btn.disabled=true;btn.textContent='导出中…';}
      var xhr=new XMLHttpRequest();
      xhr.open('GET',build+'/api/ae/export',true);
      xhr.responseType='arraybuffer'; xhr.timeout=30000;
      xhr.setRequestHeader('X-Auth-Token',getToken()||_t);
      xhr.onload=function(){
        if(btn){btn.disabled=false;btn.textContent='⬇ 导出 Excel（带公式）';}
        if(xhr.status===200){
          var blob=new Blob([xhr.response],{type:'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet'});
          var a=document.createElement('a');
          a.href=URL.createObjectURL(blob);
          a.download='速卖通订单利润核对表.xlsx';
          document.body.appendChild(a); a.click(); document.body.removeChild(a);
          setTimeout(function(){ URL.revokeObjectURL(a.href); },5000);
        }else if(xhr.status===401&&!retried){
          /* token 失效: 静默重登后重试一次 */
          reloginSilent().then(function(ok){
            if(ok)send(true);
            else{ aeExportNeedLogin(); }
          });
        }else{
          var msg='导出失败（HTTP '+xhr.status+'）';
          try{ var j=JSON.parse(new TextDecoder('utf-8').decode(xhr.response)); if(j&&j.error)msg+='：'+j.error; }catch(e){}
          alert(msg);
        }
      };
      xhr.onerror=function(){ if(btn){btn.disabled=false;btn.textContent='⬇ 导出 Excel（带公式）';} aeExportCsvFallback(); };
      xhr.ontimeout=function(){ if(btn){btn.disabled=false;btn.textContent='⬇ 导出 Excel（带公式）';} aeExportCsvFallback(); };
      xhr.send();
    };
    send(false);
  }else{
    aeExportCsvFallback();
  }
}
function aeExportNeedLogin(){
  if(getToken()){ alert('导出需要登录：请先在右上角登录（账号 admin / 密码由你设置）。'); return; }
  kickToLogin();
}
/* 只读快照/服务不可用时的兜底: 导出 CSV(数值, 无公式) */
function aeExportCsvFallback(){
  if(!AE_VIEW.length){ alert('当前没有可导出的订单'); return; }
  var cols=[['日期','date'],['订单号','orderNo'],['产品SKU','sku'],['仓库','warehouse'],['数量','qty'],['销售金额','sale'],['佣金','commission'],['预计可得','estReceive'],['平台营销费','marketing'],['头程费用','freight'],['上架费$','shelfFee'],['仓储费$','storageFee'],['出库+尾程$','lastMile'],['到账金额','received'],['到账时间','receivedAt'],['成本总额$','cost'],['汇率','fx'],['利润','__p'],['状态','__s'],['备注','remark']];
  var lines=[cols.map(function(c){return csvCell(c[0]);}).join(',')];
  AE_VIEW.forEach(function(o){
    lines.push(cols.map(function(c){
      if(c[1]==='__p'){ var p=aeProfit(o); return p===null?'':p; }
      if(c[1]==='__s') return aeStatus(o);
      return csvCell(o[c[1]]);
    }).join(','));
  });
  var blob=new Blob(['\ufeff'+lines.join('\\r\\n')],{type:'text/csv;charset=utf-8'});
  var a=document.createElement('a');
  a.href=URL.createObjectURL(blob); a.download='速卖通订单利润表.csv';
  document.body.appendChild(a); a.click(); document.body.removeChild(a);
  alert('当前为只读快照，已导出 CSV（纯数值，不带公式）。带公式的 Excel 导出请在连上录入服务（云端网址）后使用。');
}
function aeBaseAmt(o){ return (o.received===null||o.received===undefined||o.received==='')?((Number(o.estReceive)||0)-(Number(o.marketing)||0)):Number(o.received); }
/* 智能表格行: 可编辑列带 ae-c 标记(data-k=字段 data-t=num/text) */
function aeRow(o,i){
  return '<tr data-on="'+esc2(o.orderNo)+'">'+
    '<td class="rowno">'+i+'</td>'+
    '<td class="mono ae-c" data-k="date" data-t="text" title="点击编辑日期">'+esc2(o.date||'—')+'</td>'+
    '<td class="mono" title="订单号唯一，不可修改">'+esc2(o.orderNo)+'</td>'+
    '<td class="mono ae-c" data-k="shop" data-t="text" title="点击编辑店铺（速卖通店铺，当前：迈科深圳）">'+esc2(aeShopOf(o))+'</td>'+
    '<td class="mono ae-c" data-k="sku" data-t="text" title="点击编辑 SKU">'+esc2(o.sku)+'</td>'+
    '<td class="mono ae-c" data-k="warehouse" data-t="text" title="点击编辑仓库">'+(o.warehouse?esc2(o.warehouse):'<span class="dim">—</span>')+'</td>'+
    '<td class="ae-num ae-c" data-k="qty" data-t="num">'+fmt(o.qty)+'</td>'+
    '<td class="ae-num ae-c" data-k="sale" data-t="num">'+(Number(o.sale)?aeMoney(o.sale):'<span class="dim">¥0</span>')+'</td>'+
    '<td class="ae-num ae-c" data-k="commission" data-t="num">'+(Number(o.commission)?aeMoney(o.commission):'<span class="dim">¥0</span>')+'</td>'+
    '<td class="ae-num ae-c" data-k="estReceive" data-t="num">'+(Number(o.estReceive)?aeMoney(o.estReceive):'<span class="dim">—</span>')+'</td>'+
    '<td class="ae-num ae-c" data-k="marketing" data-t="num">'+(Number(o.marketing)?aeMoney(o.marketing):'<span class="dim">¥0</span>')+'</td>'+
    '<td class="ae-num ae-c" data-k="freight" data-t="num">'+(Number(o.freight)?aeMoney(o.freight):'<span class="dim">¥0</span>')+'</td>'+
    '<td class="ae-num ae-c" data-k="shelfFee" data-t="num">'+(Number(o.shelfFee)?fmt(o.shelfFee,2):'<span class="dim">0</span>')+'</td>'+
    '<td class="ae-num ae-c" data-k="storageFee" data-t="num">'+(Number(o.storageFee)?fmt(o.storageFee,2):'<span class="dim">0</span>')+'</td>'+
    '<td class="ae-num ae-c" data-k="lastMile" data-t="num">'+(Number(o.lastMile)?fmt(o.lastMile,2):'<span class="dim">0</span>')+'</td>'+
    '<td class="ae-num ae-c" data-k="received" data-t="num">'+(o.received?('<b>'+money(o.received,'CNY',2)+'</b>'):'<span class="dim">—</span>')+'</td>'+
    '<td class="mono ae-c" data-k="receivedAt" data-t="text">'+(o.receivedAt?esc2(o.receivedAt):'<span class="dim">—</span>')+'</td>'+
    '<td class="ae-num ae-c" data-k="cost" data-t="num" title="成本总额$ = 单件成本 × 数量">'+money(o.cost,'',2)+'</td>'+
    '<td class="ae-num ae-c" data-k="fx" data-t="num">'+fmt(o.fx,4)+'</td>'+
    '<td class="ae-num">'+aeProfitCell(o)+'</td>'+
    '<td class="ae-num">'+aeMarginCell(o)+'</td>'+
    '<td>'+aeStatusBadge(o)+'</td>'+
    '<td class="ae-c" data-k="remark" data-t="text" title="点击编辑备注" style="max-width:180px;overflow:hidden;text-overflow:ellipsis">'+(o.remark?esc2(o.remark):'<span class="dim">—</span>')+'</td>'+
    '<td class="op-td"><span class="op-a" data-op="edit">编辑</span><span class="op-d" data-op="del">删除</span></td>'+
  '</tr>';
}
function aeAdd(){ if(!LIVE)return piReadonlyTip(); aeForm(null); }
function aeEdit(on){ if(!LIVE)return piReadonlyTip(); var o=AE_LIST.filter(function(x){return x.orderNo===on})[0]; if(o)aeForm(o); }
function aeDel(on){
  if(!LIVE)return piReadonlyTip();
  if(!confirm('确定删除订单 ' + on + ' 吗？'))return;
  apiJson('DELETE',API_BASE+'/api/ae/orders/'+encodeURIComponent(on)).then(function(r){
    if(r.status===200&&r.body&&r.body.ok){ refreshLivePi().then(function(){ alert('订单已删除'); }); }
    else alert((r.body&&r.body.error)?('删除失败：'+r.body.error):'删除失败');
  }).catch(function(){ alert('无法连接录入服务，删除失败'); });
}
function aeSkusHtml(){
  var s={}; AE_LIST.forEach(function(o){ s[o.sku]=1; });
  ['12.8V 100Ah','12.8V 200Ah','25.6V 100Ah'].forEach(function(k){ s[k]=1; });
  return Object.keys(s).sort().map(function(k){ return '<option value="'+esc2(k)+'">'; }).join('');
}
function aeForm(o){
  FM_TYPE='ae'; FM_EDIT=o?(o.orderNo||''):null;
  var v=(function(k,d){ return o&&o[k]!==undefined&&o[k]!==null?o[k]:d; });
  var unit=(o&&o.qty>0&&o.cost)?(Math.round(o.cost/o.qty*100)/100):'';
  var today=todayStr();
  var h='<h2>'+(o?'编辑订单 <span class="mono">'+esc2(o.orderNo)+'</span>':'新增速卖通订单')+'</h2>';
  h+='<div class="fm-grid">';
  h+='<div class="fm-field"><label>订单日期 *</label><input id="fADate" type="date" value="'+esc2(v('date',today))+'"></div>';
  h+='<div class="fm-field"><label>速卖通店铺 *</label><input id="fAShop" list="fAShopList" value="'+esc2(aeShopOf(o))+'" placeholder="迈科深圳"><datalist id="fAShopList">'+aeShopOptionsHtml()+'</datalist><div class="hint">已预置：迈科深圳 / 迈科香港 / 法国 LITH ENERGY（可直接输入新店名）</div></div>';
  h+='<div class="fm-field"><label>订单号 *</label><input id="fAOn" value="'+esc2(v('orderNo',''))+'" placeholder="速卖通订单号" '+(o?'readonly':'')+'></div>';
  h+='<div class="fm-field"><label>产品 SKU *</label><input id="fASku" list="fASkuList" value="'+esc2(v('sku',''))+'" placeholder="如 25.6V 100Ah" onchange="aeSkuAuto()"><datalist id="fASkuList">'+aeSkusHtml()+'</datalist></div>';
  h+='<div class="fm-field"><label>发货仓库 *</label><input id="fAWh" list="fAWhList" value="'+esc2(v('warehouse','美国富皇美运'))+'" placeholder="美国富皇美运 / 德国盘古"><datalist id="fAWhList"><option value="美国富皇美运"><option value="德国盘古"></datalist><div class="hint">美国仓=富皇美运(FDR)，德国仓=盘古</div></div>';
  h+='<div class="fm-field"><label>数量 *</label><input id="fAQty" type="number" min="1" step="1" value="'+esc2(v('qty',1))+'" oninput="aePv()"></div>';
  h+='<div class="fm-field"><label>销售金额(¥)</label><input id="fASale" type="number" min="0" step="0.01" value="'+esc2(v('sale',''))+'" placeholder="0.00" oninput="aePv()"></div>';
  h+='<div class="fm-field"><label>佣金(¥)</label><input id="fAComm" type="number" min="0" step="0.01" value="'+esc2(v('commission',0))+'" oninput="aePv()"></div>';
  h+='<div class="fm-field"><label>预计可得(¥)</label><input id="fAEst" type="number" min="0" step="0.01" value="'+esc2(v('estReceive',''))+'" placeholder="平台预计结算额" oninput="aePv()"></div>';
  h+='<div class="fm-field"><label>平台营销费用(¥)</label><input id="fAMkt" type="number" min="0" step="0.01" value="'+esc2(v('marketing',0))+'" placeholder="0.00" oninput="aePv()"></div>';
  h+='<div class="fm-field"><label>头程费用(¥)</label><input id="fAFrt" type="number" min="0" step="0.01" value="'+esc2(v('freight',0))+'" placeholder="0.00" oninput="aePv()"><div class="hint">中国→海外仓 单件头程×件数</div></div>';
  h+='<div class="fm-field"><label>上架费($)</label><input id="fAShelf" type="number" min="0" step="0.01" value="'+esc2(v('shelfFee',0))+'" placeholder="0.00" oninput="aePv()"></div>';
  h+='<div class="fm-field"><label>仓储费($)</label><input id="fAStore" type="number" min="0" step="0.01" value="'+esc2(v('storageFee',0))+'" placeholder="0.00" oninput="aePv()"></div>';
  h+='<div class="fm-field"><label>出库+尾程($)</label><input id="fATail" type="number" min="0" step="0.01" value="'+esc2(v('lastMile',0))+'" placeholder="0.00" oninput="aePv()"></div>';
  h+='<div class="fm-field"><label>到账金额(¥)</label><input id="fARcv" type="number" min="0" step="0.01" value="'+esc2(v('received',''))+'" placeholder="留空=预估（用预计可得−营销）" oninput="aePv()"></div>';
  h+='<div class="fm-field"><label>到账时间</label><input id="fARcvAt" type="date" value="'+esc2(v('receivedAt',''))+'"><div class="hint">填了即标记「已放款」，利润按到账实算</div></div>';
  h+='<div class="fm-field"><label>产品成本单价($)</label><input id="fAUnit" type="number" min="0" step="0.01" value="'+esc2(unit)+'" placeholder="选 SKU 自动带出" oninput="aePv()"><div class="hint">美元/件；×数量=成本总额</div></div>';
  h+='<div class="fm-field"><label>汇率 P</label><input id="fAFx" type="number" min="0" step="0.0001" value="'+esc2(v('fx',''))+'" placeholder="如 6.80" oninput="aePv()"></div>';
  h+='<div class="fm-field full"><label>备注</label><input id="fARemark" value="'+esc2(v('remark',''))+'" placeholder="选填"></div>';
  h+='</div>';
  h+='<p class="fm-err" id="fmErr"></p>';
  h+='<div id="aePvBox" style="margin:0 0 12px;padding:10px 12px;background:#132a42;border:1px dashed #2c5580;border-radius:8px;font-size:13px;line-height:1.9;color:#9dc0f0">填完关键数据后这里实时显示利润估算</div>';
  h+='<div class="fm-bar"><button class="btn" onclick="closeFm()">取消</button><button class="btn primary" id="fmSave" onclick="saveAe()">保存订单</button></div>';
  fmOpen(h);
  aePv();
}
function aeSkuAuto(){
  var sku=document.getElementById('fASku').value.trim();
  if(!sku)return;
  var costEl=document.getElementById('fAUnit'), fxEl=document.getElementById('fAFx');
  if(costEl&&!costEl.value&&AE_SUG.cost[sku])costEl.value=AE_SUG.cost[sku];
  if(fxEl&&!fxEl.value&&AE_SUG.fx[sku])fxEl.value=AE_SUG.fx[sku];
  aePv();
}
function aeFormVal(k){ var el=document.getElementById(k); return el?el.value:''; }
function aePv(){
  var box=document.getElementById('aePvBox'); if(!box)return;
  var qty=Math.abs(Number(aeFormVal('fAQty')))||0;
  var sale=Number(aeFormVal('fASale'))||0;
  var est=Number(aeFormVal('fAEst'))||0, mkt=Number(aeFormVal('fAMkt'))||0;
  var frt=Number(aeFormVal('fAFrt'))||0;
  var usd=(Number(aeFormVal('fAShelf'))||0)+(Number(aeFormVal('fAStore'))||0)+(Number(aeFormVal('fATail'))||0)+(Number(aeFormVal('fAUnit'))||0)*qty;
  var fx=Number(aeFormVal('fAFx'))||0;
  var rcv=aeFormVal('fARcv');
  var base=(rcv!==''&&rcv!==null)?Number(rcv):(est-mkt);
  var html='';
  if(fx<=0){ box.innerHTML='<span style="color:#B26A00">⚠ 请填写汇率后自动估算利润</span>'; return; }
  var profit=Math.round((base-frt-usd*fx)*100)/100;
  var margin=sale>0?(profit/sale*100):null;
  html='<b style="color:#6aa4f5">到账基准：</b>'+money(Math.max(0,base),'CNY',2)+(rcv===''?'（预估）':'（实算）');
  html+='　<b style="color:#6aa4f5">成本总额：</b>'+money(usd*fx,'CNY',2)+'（$'+fmt(usd,2)+' × '+fx+'）';
  html+='　<b style="color:#ef6b5e">预计利润：'+money(profit,'CNY',2)+'</b>';
  if(margin!==null)html+='　<b>毛利率：'+(margin>=0?'+':'')+margin.toFixed(2)+'%</b>';
  box.innerHTML=html;
}
function saveAe(){
  var date=aeFormVal('fADate'), on=aeFormVal('fAOn').trim(), sku=aeFormVal('fASku').trim();
  var wh=aeFormVal('fAWh').trim();
  var qty=Number(aeFormVal('fAQty'))||0;
  if(!on){ notifyPi('请填写订单号',''); return; }
  if(!sku){ notifyPi('请填写产品 SKU',''); return; }
  if(!wh){ notifyPi('请选择发货仓库（美国富皇美运 / 德国盘古）',''); return; }
  var shop=aeFormVal('fAShop').trim();
  if(!shop){ notifyPi('请填写速卖通店铺（默认：迈科深圳）',''); return; }
  if(qty<=0){ notifyPi('数量必须大于 0',''); return; }
  var body={
    date:date, orderNo:on, shop:shop, sku:sku, warehouse:wh, qty:Math.round(qty),
    sale:aeFormVal('fASale'), commission:aeFormVal('fAComm'),
    estReceive:aeFormVal('fAEst'), marketing:aeFormVal('fAMkt'),
    freight:aeFormVal('fAFrt'), shelfFee:aeFormVal('fAShelf'),
    storageFee:aeFormVal('fAStore'), lastMile:aeFormVal('fATail'),
    received:aeFormVal('fARcv'), receivedAt:aeFormVal('fARcvAt'),
    unitCost:aeFormVal('fAUnit'), fx:aeFormVal('fAFx'), remark:aeFormVal('fARemark')
  };
  var btn=document.getElementById('fmSave'); btn.disabled=true; btn.textContent='保存中…';
  apiJson('POST',API_BASE+'/api/ae/list',body).then(function(r){
    if(r.status===200&&r.body&&r.body.ok){
      refreshLivePi().then(function(){ var isEdit=!!FM_EDIT; closeFm(); alert(isEdit?'订单已更新，页面已刷新':'订单已保存，页面已刷新'); });
    }else{ btn.disabled=false; btn.textContent='保存订单'; notifyPi((r.body&&r.body.error)?r.body.error:'保存失败',''); }
  }).catch(function(){ btn.disabled=false; btn.textContent='保存订单'; notifyPi('无法连接录入服务，保存失败',''); });
}

/* ================= 在线录入 (pi-v2: 直接在本页录 PI / 头程批次) ================= */
/* 底层请求(无 401 重试) */
function apiJsonRaw(method,url,body){
  return new Promise(function(resolve,reject){
    var xhr=new XMLHttpRequest();
    try{ xhr.open(method,url,true); }catch(e){ reject(e); return; }
    xhr.timeout=8000;
    if(body)xhr.setRequestHeader('Content-Type','application/json');
    var mt=String(method||'GET').toUpperCase();
    if(mt!=='GET'){ var _t=getToken(); if(_t)xhr.setRequestHeader('X-Auth-Token',_t); }
    xhr.onload=function(){
      var j=null; try{ j=JSON.parse(xhr.responseText); }catch(e){}
      if(xhr.status===401){
        try{ localStorage.removeItem('dash_token'); sessionStorage.removeItem('dash_token'); }catch(e2){}
      }
      resolve({status:xhr.status,body:j});
    };
    xhr.onerror=function(){ reject(new Error('network')); };
    xhr.ontimeout=function(){ reject(new Error('timeout')); };
    xhr.send(body?JSON.stringify(body):null);
  });
}
/* 请求(写操作遇 401 → 静默自动重登 → 重放一次) */
function apiJson(method,url,body){
  return apiJsonRaw(method,url,body).then(function(r){
    if(r.status!==401)return r;
    return reloginSilent().then(function(ok){
      if(!ok){ kickToLogin(); return r; }
      return apiJsonRaw(method,url,body);
    });
  });
}
function setEntrySt(live,txt){
  var st=document.getElementById('entrySt');
  if(!st)return;
  st.className='entry-st '+(live?'live':'ro');
  var t=document.getElementById('entryStTxt'); if(t)t.textContent=txt;
  /* 只读模式隐藏新增按钮 */
  var btns=document.querySelectorAll('.pi-add-btn,.ae-add-btn');
  for(var i=0;i<btns.length;i++)btns[i].style.display=live?'':'none';
}
function isSameOriginMode(){
  try{ var o=location.origin; return !!(o&&o!=='null'&&API_CAND.length&&o===API_CAND[0]); }catch(e){ return false; }
}
function initPiLive(){
  if(PI_TRYED)return; PI_TRYED=true;
  var roTxt='当前为只读快照，录入功能不可用。可能原因：① 通过云端网址访问但云端录入服务暂时不可用；② 本地打开但录入服务(8899)未运行。';
  resolveApiBase().then(function(){
    if(!API_BASE){ LIVE=false; setEntrySt(false,roTxt); probeLnaHint(); return null; }
    return apiJson('GET',API_BASE+'/api/ping');
  }).then(function(r){
    if(r&&r.status===200&&r.body&&r.body.ok){
      LIVE=true;
      var where=isSameOriginMode()?'云端服务':'本机录入服务(127.0.0.1:8899)';
      setEntrySt(true,'✓ 已连接'+where+' —— 可直接在本页新增 / 编辑 / 删除 PI 单、头程发货批次与速卖通订单，保存立即生效。');
      if(!getToken())reloginSilent();   /* 自动登录但令牌缺失/过期时静默补齐 */
      return refreshLivePi();
    }
    LIVE=false; setEntrySt(false,roTxt); probeLnaHint();
    return null;
  }).catch(function(){
    LIVE=false; setEntrySt(false,roTxt); probeLnaHint();
  });
}
function probeLnaHint(){
  var t=document.getElementById('entryStTxt'); if(!t)return;
  if(isSameOriginMode()){
    /* 同源(云端)探测失败 → 服务本身不可用, 不是浏览器权限问题 */
    t.innerHTML += '<br><b style="color:#e8a24e">云端录入服务暂不可用</b>——页面数据仍可查看，请稍后刷新；若持续如此请联系管理员检查服务状态。';
    return;
  }
  try{
    if(!navigator.permissions||!navigator.permissions.query)return;
    navigator.permissions.query({name:'local-network-access'}).then(function(st){
      if(st.state==='prompt'){
        t.innerHTML += '<br><b style="color:#e8a24e">👆 请在弹出的浏览器提示中点「允许」</b>（Chrome 142+ 需授权网页访问本机录入服务；若没看到弹窗，点地址栏左侧图标，或到 chrome://settings/content/localNetworkAccess 把 <b>'+(location.hostname||'')+'</b> 设为允许后刷新）';
      }else if(st.state==='granted'){
        t.innerHTML += '<br>已授权但仍未连接——请确认本机录入服务(8899)正在运行';
      }
    }).catch(function(){});
  }catch(e){}
}
function refreshLivePi(){
  return Promise.all([
    apiJson('GET',API_BASE+'/api/pis'),
    apiJson('GET',API_BASE+'/api/batches'),
    apiJson('GET',API_BASE+'/api/ae/list'),
    apiJson('GET',API_BASE+'/api/sku-weight')
  ]).then(function(res){
    var p=res[0],b=res[1],ae=res[2],sw=res[3];
    if(p.status===200&&p.body&&p.body.list)PIF.pis=p.body.list;
    if(b.status===200&&b.body&&b.body.list)PIF.batches=b.body.list;
    if(sw&&sw.status===200&&sw.body&&sw.body.list){ SKU_W=sw.body.list||{}; SKU_W_AT=sw.body.updatedAt||''; }
    PIS=PIF.pis||[]; BATCHES=(PIF.batches||[]).slice();
    BATCHES.forEach(function(x){ if(x.products)x._qty=batchQty(x); });
    var badge=document.getElementById('piBadge');
    badge.style.display=(PIS.length?'':'none'); if(PIS.length)badge.textContent=PIS.length;
    var nb2=document.getElementById('navBadgePi'); if(nb2){ nb2.style.display=(PIS.length?'':'none'); if(PIS.length)nb2.textContent=PIS.length; }
    RO_FEE=buildRoFeeIndex();                 /* 头程费用索引随批次更新 */
    pfLoad();                                 /* PI 表格库列表同步刷新 */
    if(PI_READY)renderPiAll();                /* 当前停留在 PI tab 时立即刷新 */
    /* 速卖通订单同步刷新 */
    if(ae.status===200&&ae.body&&ae.body.list){ AE_LIST=ae.body.list; aeRebuildSug(); }
    var aeBadge=document.getElementById('aeBadge');
    if(aeBadge){ if(AE_LIST.length){aeBadge.style.display='';aeBadge.textContent=AE_LIST.length;} else aeBadge.style.display='none'; }
    var nbAe=document.getElementById('navBadgeAe');
    if(nbAe){ if(AE_LIST.length){nbAe.style.display='';nbAe.textContent=AE_LIST.length;} else nbAe.style.display='none'; }
    /* 月份下拉存在则同步可选项 */
    var mSel=document.getElementById('aeMonth');
    if(mSel&&mSel._h){
      var ms={},cur=mSel.value;
      AE_LIST.forEach(function(o){ if(o.date&&/^\\d{4}-\\d{2}/.test(o.date))ms[o.date.slice(0,7)]=1; });
      var html='<option value="">全部月份</option>';
      Object.keys(ms).sort(function(a,b){return a<b?1:-1}).forEach(function(m){ html+='<option value="'+esc2(m)+'"'+(m===cur?' selected':'')+'>'+m+'</option>'; });
      mSel.innerHTML=html;
    }
    if(AE_READY)renderAeAll();                /* 当前停留在 ae tab 时立即刷新 */
    if(document.getElementById('tab-trace').style.display==='block'){ renderTrace(); renderInbound(); }
    return true;
  });
}
function piReadonlyTip(){ alert('当前为只读快照，无法修改。请在有本机录入服务的电脑上打开本页（或让助理代录）。'); }
/* ================= PI 表格库 (自制 PI Excel 上传归档: 备货海外仓 / 样品单) ================= */
var PF_CAT='stock', PF_LIST=[], PF_BIND=false;
function pfTab(c){
  PF_CAT=c;
  var a=document.getElementById('pfTabStock'), b=document.getElementById('pfTabSample');
  if(a)a.className='ae-vtab'+(c==='stock'?' active':'');
  if(b)b.className='ae-vtab'+(c==='sample'?' active':'');
  pfRender();
}
function pfLoad(){
  if(!API_BASE)return Promise.resolve(false);
  return apiJson('GET',API_BASE+'/api/pi-files').then(function(r){
    if(r.status===200&&r.body&&r.body.list){ PF_LIST=r.body.list; pfRender(); return true; }
    return false;
  }).catch(function(){ return false; });
}
function pfRender(){
  var tb=document.getElementById('pfTbody'), em=document.getElementById('pfEmpty');
  if(!tb)return;
  var c1=document.getElementById('pfCntStock'), c2=document.getElementById('pfCntSample');
  var nS=0,nP=0;
  PF_LIST.forEach(function(f){ if(f.cat==='sample')nP++; else nS++; });
  if(c1)c1.textContent=nS?('('+nS+')'):'';
  if(c2)c2.textContent=nP?('('+nP+')'):'';
  var rows=PF_LIST.filter(function(f){return f.cat===PF_CAT;});
  if(!rows.length){ tb.innerHTML=''; if(em)em.style.display='block'; return; }
  if(em)em.style.display='none';
  tb.innerHTML=rows.map(function(f){
    var kb=f.size>1048576?((f.size/1048576).toFixed(1)+' MB'):(Math.max(1,Math.round(f.size/1024))+' KB');
    var sheets=(f.preview&&f.preview.sheetNames&&f.preview.sheetNames.length)?esc2(f.preview.sheetNames.join('、')):'—';
    var prev=f.preview?'<span class="op-a" data-op="preview">预览</span> · ':'';
    return '<tr data-pfid="'+esc2(f.id)+'">'+
      '<td><b>'+esc2(f.name)+'</b></td>'+
      '<td class="num-r">'+kb+'</td>'+
      '<td>'+esc2(f.uploadedAt)+'</td>'+
      '<td>'+sheets+'</td>'+
      '<td class="op-td">'+prev+
      '<a href="'+API_BASE+'/api/pi-files/download/'+esc2(f.id)+'">下载</a> · '+
      '<span class="op-d" data-op="del">删除</span></td></tr>';
  }).join('');
  if(!PF_BIND){
    PF_BIND=true;
    tb.addEventListener('click',function(e){
      var op=e.target.closest('[data-op]');
      if(!op)return;
      var tr=e.target.closest('tr'); if(!tr||!tr.hasAttribute('data-pfid'))return;
      var id=tr.getAttribute('data-pfid');
      if(op.getAttribute('data-op')==='preview')pfPreview(id);
      else if(op.getAttribute('data-op')==='del')pfDel(id);
    });
  }
}
function pfPick(cat){
  if(!LIVE)return piReadonlyTip();
  pfTab(cat);
  var inp=document.getElementById('pfInput'); if(!inp)return;
  inp.value=''; inp.click();
}
function pfUpload(){
  var inp=document.getElementById('pfInput');
  var f=inp&&inp.files&&inp.files[0]; if(!f)return;
  if(!LIVE){ piReadonlyTip(); return; }
  if(f.size>10*1024*1024){ alert('文件超过 10MB 上限，请压缩后再传'); return; }
  var cat=PF_CAT, hint=document.getElementById('pfHint'), oldTxt='支持 .xlsx / .xls / .csv，单文件 ≤ 10MB；上传后可随时在线预览内容或下载。';
  var reader=new FileReader();
  reader.onload=function(){
    var b64=String(reader.result).split(',')[1]||'';
    if(!b64){ alert('读取文件失败'); return; }
    if(hint)hint.textContent='正在上传「'+f.name+'」…';
    apiJson('POST',API_BASE+'/api/pi-files',{cat:cat,name:f.name,dataB64:b64}).then(function(r){
      if(hint)hint.textContent=oldTxt;
      if(r.status===200&&r.body&&r.body.ok){ pfLoad(); alert('上传成功：'+f.name); }
      else alert((r.body&&r.body.error)?('上传失败：'+r.body.error):'上传失败');
    }).catch(function(){ if(hint)hint.textContent=oldTxt; alert('无法连接录入服务，上传失败'); });
  };
  reader.onerror=function(){ alert('读取文件失败'); };
  reader.readAsDataURL(f);
}
function pfPreview(id){
  var f=PF_LIST.filter(function(x){return x.id===id;})[0];
  if(!f)return;
  if(!f.preview){ alert('该文件上传时未生成预览（可能是 .csv 或服务未装解析库），可直接下载查看'); return; }
  var h='<h2>预览：'+esc2(f.name)+' <span class="tag">'+(f.cat==='sample'?'样品单 PI':'备货海外仓 PI')+'</span></h2>';
  h+='<div style="max-height:60vh;overflow:auto">';
  f.preview.sheets.forEach(function(s){
    h+='<p style="margin:10px 0 4px;font-weight:600;font-size:12.5px">工作表：'+esc2(s.name)+'</p>';
    h+='<div class="tbl-scroll"><table style="min-width:100%">';
    s.rows.forEach(function(r,i){
      h+='<tr'+(i===0?' style="background:#1a2133;font-weight:600"':'')+'>';
      r.forEach(function(c){ h+='<td style="white-space:nowrap;border:1px solid #EDF1F6;padding:4px 8px;font-size:12px">'+esc2(c)+'</td>'; });
      h+='</tr>';
    });
    h+='</table></div>';
  });
  h+='</div><div class="fm-bar"><a class="btn" href="'+API_BASE+'/api/pi-files/download/'+esc2(f.id)+'">⬇ 下载原文件</a><button class="btn" onclick="closeFm()">关闭</button></div>';
  fmOpen(h);
}
function pfDel(id){
  if(!LIVE)return piReadonlyTip();
  var f=PF_LIST.filter(function(x){return x.id===id;})[0]; if(!f)return;
  if(!confirm('确定删除「'+f.name+'」吗？删除后不可恢复。'))return;
  apiJson('DELETE',API_BASE+'/api/pi-files/'+encodeURIComponent(id)).then(function(r){
    if(r.status===200&&r.body&&r.body.ok){ pfLoad(); alert('已删除'); }
    else alert((r.body&&r.body.error)?('删除失败：'+r.body.error):'删除失败');
  }).catch(function(){ alert('无法连接录入服务，删除失败'); });
}
/* --- 表单框架 --- */
function fmOpen(html){
  var m=document.getElementById('fmModal');
  document.getElementById('fmBox').innerHTML=html;
  m.style.display='flex';
}
function closeFm(){ document.getElementById('fmModal').style.display='none'; document.getElementById('fmBox').innerHTML=''; FM_TYPE=''; FM_EDIT=null; }
function notifyPi(msg,ok){ var el=document.getElementById('fmErr'); if(el){ el.textContent=msg; el.className='fm-err '+(ok?'ok':''); } }
function todayStr(){ var d=new Date(); return d.getFullYear()+'-'+String(d.getMonth()+1).padStart(2,'0')+'-'+String(d.getDate()).padStart(2,'0'); }
function curOptions(sel){
  var h='';['CNY','USD','EUR','HKD','GBP'].forEach(function(c){ h+='<option'+(c===sel?' selected':'')+'>'+c+'</option>'; });
  return h;
}
/* 表单货币符号: 取当前打开表单(批次 fBCur / PI fPiCur)的币种, 同步到表头 .cur-sym 与金额列 */
function curSymNow(){
  var el=document.getElementById('fBCur')||document.getElementById('fPiCur');
  var c=el?el.value:'CNY';
  return CUR_SYM[c]||(c?c+' ':'¥');
}
/* 表头货币符号可点击切换 ¥/$（与币种下拉双向联动） */
function toggleFormCur(){
  var el=document.getElementById('fBCur')||document.getElementById('fPiCur'); if(!el)return;
  el.value=(el.value==='USD')?'CNY':'USD';
  el.dispatchEvent(new Event('change'));
}
function curSymBtn(){
  return '<span class="cur-sym" onclick="toggleFormCur()" title="点击切换 人民币¥ / 美金$（与币种下拉联动）" style="cursor:pointer;border-bottom:1px dashed #888">¥</span>';
}
function updProdCurSym(){
  var sym=curSymNow();
  var box=document.getElementById('fmBox'); if(!box)return;
  var sp=box.querySelectorAll('.cur-sym');
  for(var i=0;i<sp.length;i++)sp[i].textContent=sym;
  var rows=box.querySelectorAll('#fmProds .prod-row');
  for(var j=0;j<rows.length;j++){
    var q=Number(rows[j].querySelector('.pr-qty').value)||0;
    var p=Number(rows[j].querySelector('.pr-price').value)||0;
    var amt=rows[j].querySelector('.pr-amt');
    if(amt)amt.value=(q>0&&p>0)?sym+(q*p).toFixed(2):'—';
  }
}
function prodHead(){
  var sym=curSymBtn();
  if(FM_TYPE==='pi')return '<div class="prod-head with-reb" style="margin-top:6px"><span>SKU *</span><span>商品名称</span><span>数量 *</span><span>成本单价 '+sym+'</span><span>退税率%</span><span>退税后单价</span><span>金额 '+sym+'</span><span></span></div>';
  if(FM_TYPE==='batch')return '<div class="prod-head with-pi" style="margin-top:6px"><span>归属 PI</span><span>SKU *</span><span>商品名称</span><span>数量 *</span><span>成本单价(退税后) '+sym+'</span><span>退税后金额 '+sym+'</span><span></span></div>';
  return '<div class="prod-head" style="margin-top:6px"><span>SKU *</span><span>商品名称</span><span>数量 *</span><span>成本单价(退税后) '+sym+'</span><span>退税后金额 '+sym+'</span><span></span></div>';
}
/* 产品明细下方「总件数」自动汇总: 随各行数量输入/删行/带出实时刷新 */
function updProdTotalQty(){
  var el=document.getElementById('prodTotalN'); if(!el)return;
  var n=0, rows=document.querySelectorAll('#fmProds .prod-row');
  for(var i=0;i<rows.length;i++)n+=(Number(rows[i].querySelector('.pr-qty').value)||0);
  el.textContent=fmt(n);
}
function prodTotalBar(){
  return '<div id="prodTotalBar" style="margin:8px 0 4px;padding:7px 12px;background:#16233a;border:1px solid #26304a;border-radius:8px;font-size:13px;color:#b8c4dc;display:flex;gap:18px;align-items:center">'+
    '<span>📦 总件数：<b id="prodTotalN" style="font-size:15px;color:#6aa4f5">0</b> <span style="font-size:12px;color:var(--sub)">（按各行数量自动汇总）</span></span>'+
    '<span id="prodTotalRows" style="font-size:12px;color:var(--sub)"></span></div>';
}
/* --- PI 单 新增/编辑/删除 --- */
function piAdd(){ if(!LIVE)return piReadonlyTip(); piForm(null); }
function piEdit(piNo){ if(!LIVE)return piReadonlyTip(); var pi=PIS.filter(function(p){return p.piNo===piNo})[0]; if(pi)piForm(pi); }
function piDel(piNo){
  if(!LIVE)return piReadonlyTip();
  if(!confirm('确定删除 PI 单 '+piNo+' 吗？其下所有发货批次将一并删除！'))return;
  apiJson('DELETE',API_BASE+'/api/pis/'+encodeURIComponent(piNo)).then(function(r){
    if(r.status===200&&r.body&&r.body.ok){ refreshLivePi().then(function(){ alert('已删除 PI 单 '+piNo); }); }
    else alert((r.body&&r.body.error)?('删除失败：'+r.body.error):'删除失败');
  }).catch(function(){ alert('无法连接本机录入服务，删除失败'); });
}
function piForm(pi){
  FM_TYPE='pi'; FM_EDIT=pi?pi.piNo:null;
  var h='<h2>'+(pi?'编辑 PI 单 <span class="mono">'+esc2(pi.piNo)+'</span>':'新增 PI 单')+'</h2>';
  /* 从 PI 表格库一键导入(上传过的自制 PI Excel 自动填入) */
  if(LIVE&&typeof PF_LIST!=='undefined'&&PF_LIST.length){
    h+='<div class="fm-field full" style="display:flex;gap:8px;align-items:center;background:#16233a;border:1px solid #26304a;border-radius:8px;padding:8px 10px;margin-bottom:2px">'+
      '<span style="font-size:12.5px;font-weight:600;white-space:nowrap">📥 从 PI 表格库导入：</span>'+
      '<select id="fPiImpFile" style="flex:1;min-width:0;padding:5px 6px">'+
      PF_LIST.map(function(f){ return '<option value="'+esc2(f.id)+'">'+(f.cat==='sample'?'[样品单] ':'[备货] ')+esc2(f.name)+'</option>'; }).join('')+
      '</select>'+
      '<button type="button" class="btn small" onclick="piImportFill()">自动填入</button></div>';
  }
  h+='<div class="fm-grid">';
  h+='<div class="fm-field"><label>PI 单号 *</label><input id="fPiNo" value="'+esc2(pi?pi.piNo:'')+'" placeholder="如 PI20260901"'+(pi?' disabled':'')+'><div class="hint">每次备货一张；保存后单号不可改</div></div>';
  h+='<div class="fm-field"><label>PI 日期</label><input id="fPiDate" type="date" value="'+esc2(pi?(pi.date||todayStr()):todayStr())+'"></div>';
  h+='<div class="fm-field full"><label>供应商</label><input id="fPiSup" value="'+esc2(pi?pi.supplier:'')+'" placeholder="如 深圳某某新能源科技"></div>';
  h+='<div class="fm-field"><label>币种</label><select id="fPiCur" onchange="updProdCurSym()">'+curOptions(pi?(pi.currency||'CNY'):'CNY')+'</select></div>';
  h+='<div class="fm-field"><label>价格口径</label><select id="fPiTaxInc"><option value="inc"'+(pi&&pi.taxIncluded===false?'':' selected')+'>含税单价</option><option value="ex"'+(pi&&pi.taxIncluded===false?' selected':'')+'>未税单价</option></select><div class="hint">产品行单价按此口径录入</div></div>';
  h+='<div class="fm-field"><label>税率 (%)</label><input id="fPiTaxRate" type="number" min="0" max="100" step="0.5" value="'+(pi?Number(pi.taxRate)||'':'')+'" placeholder="如 13"><div class="hint">用于折算含税/未税总额，如 13 表示 13%</div></div>';
  h+='<div class="fm-field"><label>备注</label><input id="fPiRemark" value="'+esc2(pi?pi.remark:'')+'"></div>';
  h+='</div>'+prodHead()+'<div id="fmProds"></div>'+prodTotalBar();
  h+='<div id="piRebSum" class="pi-reb-sum"></div>';
  h+='<button type="button" class="fm-row-btn" onclick="addProdRow()">＋ 添加产品行</button>';
  h+='<p class="fm-err" id="fmErr"></p>';
  h+='<div class="fm-bar"><button class="btn" onclick="closeFm()">取消</button><button class="btn primary" id="fmSave" onclick="savePi()">保存 PI 单</button></div>';
  fmOpen(h);
  var rows=(pi&&pi.products&&pi.products.length)?pi.products:[{sku:'',name:'',qty:'',unitPrice:''}];
  rows.forEach(addProdRow);
  if(pi)document.getElementById('fPiNo').setAttribute('readonly','readonly');
  /* 退税实时测算: 数量/单价/退税率/税率/口径 变化即刷新汇总条 */
  var pib=document.getElementById('fmProds');
  if(pib&&!pib._rb){ pib._rb=1; pib.addEventListener('input',function(){ if(FM_TYPE==='pi')updPiRebSum(); }); }
  var trEl=document.getElementById('fPiTaxRate');
  if(trEl&&!trEl._rb){ trEl._rb=1; trEl.addEventListener('input',function(){ if(FM_TYPE==='pi')updPiRebSum(); }); }
  var icEl=document.getElementById('fPiTaxInc');
  if(icEl&&!icEl._rb){ icEl._rb=1; icEl.addEventListener('change',function(){ if(FM_TYPE==='pi')updPiRebSum(); }); }
  updPiRebSum();
  updProdCurSym();
}
/* --- 从 PI 表格库自动填入 PI 单表单(智能识别表头: PI单号/日期/供应商/币种/税率/SKU/品名/数量/单价) --- */
function piImportFill(){
  var sel=document.getElementById('fPiImpFile'); if(!sel||!sel.value)return;
  var f=PF_LIST.filter(function(x){return x.id===sel.value;})[0]; if(!f)return;
  notifyPi('正在解析「'+f.name+'」…','');
  apiJson('GET',API_BASE+'/api/pi-files/parse/'+encodeURIComponent(f.id)).then(function(r){
    if(!(r.status===200&&r.body&&r.body.ok&&r.body.sheets)){
      notifyPi((r.body&&r.body.error)?('导入失败：'+r.body.error):'导入失败：文件无法解析（仅支持 xlsx/xls/csv）','');
      return;
    }
    var sheets=r.body.sheets;
    if(!sheets.length){ notifyPi('导入失败：文件没有可解析的数据行',''); return; }
    /* 挑关键词命中最多的工作表 */
    var KW=['pi单号','单号','日期','供应商','币种','sku','型号','description','品名','名称','items','数量','qty','qnty','单价','unitprice','金额','amount','税率'];
    var scSheet=function(s){ var best=0; s.rows.slice(0,10).forEach(function(row){ var sc=0; row.forEach(function(c){ var v=String(c).toLowerCase(); for(var i=0;i<KW.length;i++){ if(v.indexOf(KW[i])>=0){sc++;break;} } }); if(sc>best)best=sc; }); return best; };
    var s=sheets[0];
    sheets.forEach(function(x){ if(scSheet(x)>scSheet(s))s=x; });
    /* 找表头行并建列映射（中英文表头通吃: Description=SKU, QNTY/QUANTITY=数量, UNIT PRICE=单价, AMOUNT=金额） */
    var hi=-1,hs=-1,cols={};
    s.rows.slice(0,15).forEach(function(row,i){
      var c={},sc=0;
      row.forEach(function(v,j){
        var t=String(v).toLowerCase().replace(/\\s+/g,'');
        function has(){ for(var k=0;k<arguments.length;k++){ if(t.indexOf(arguments[k])>=0)return true; } return false; }
        if(c.pi===undefined&&has('pi单号','pi号','单号')){c.pi=j;sc++;}
        if(c.date===undefined&&has('日期')){c.date=j;sc++;}
        if(c.sup===undefined&&has('供应商','厂家')){c.sup=j;sc++;}
        if(c.cur===undefined&&has('币种','币别','货币')){c.cur=j;sc++;}
        if(c.tax===undefined&&has('税率')){c.tax=j;sc++;}
        if(c.sku===undefined&&has('sku','型号','description')){c.sku=j;sc++;}
        if(c.name===undefined&&has('品名','商品名称','名称','items')){c.name=j;sc++;}
        if(c.qty===undefined&&has('数量','qty','qnty','quantity')){c.qty=j;sc++;}
        if(c.price===undefined&&has('单价','unitprice')){c.price=j;sc++;}
        if(c.amt===undefined&&has('金额','总价','amount')){c.amt=j;sc++;}
        if(c.reb===undefined&&has('退税率','退税','rebate')){c.reb=j;sc++;}
      });
      if(sc>hs){hs=sc;hi=i;cols=c;}
    });
    if(hi<0||(cols.sku===undefined&&cols.name===undefined)){ notifyPi('导入失败：未识别到表头（表头需含 SKU/Description 与 数量/QNTY 列）',''); return; }
    var prods=[],piNo='',sup='',cur='',taxR='',piDate='',piNoE='',piDateE='';
    /* PI单号/日期常嵌在表格上方文字里（如 "PI: ML20260721145" / "DATE: 2026-7-21"），全表扫描兜底 */
    s.rows.forEach(function(row){
      (row||[]).forEach(function(v){
        var t=String(v==null?'':v);
        if(!piNoE){ var m=t.match(/(?:^|[^a-z])pi\\s*[:：]\\s*([a-z0-9][a-z0-9\\-\\/]*)/i); if(m)piNoE=m[1]; }
        if(!piDateE){ var d=t.match(/date\\s*[:：]\\s*(\\d{4}[-\\/.]\\d{1,2}[-\\/.]\\d{1,2})/i); if(d)piDateE=d[1]; }
      });
    });
    for(var i=hi+1;i<s.rows.length;i++){
      var row=s.rows[i]; if(!row||!row.length)continue;
      var g=function(k){ return cols[k]!==undefined?String(row[cols[k]]==null?'':row[cols[k]]).trim():''; };
      var sku=g('sku')||g('name');
      var qty=parseFloat(String(g('qty')).replace(/[^\\d.\\-]/g,''));
      var price=parseFloat(String(g('price')).replace(/[^\\d.\\-]/g,''));
      if(!sku||isNaN(qty)||qty<=0)continue;               /* 跳过空行/合计行 */
      var reb=cols.reb!==undefined?parseFloat(String(g('reb')).replace(/[^\\d.\\-]/g,'')):NaN;
      prods.push({sku:sku,name:g('name'),qty:qty,unitPrice:isNaN(price)?'':price,rebate:isNaN(reb)?0:Math.min(100,Math.max(0,reb))});
      if(!piNo&&cols.pi!==undefined)piNo=g('pi');
      if(!piDate&&cols.date!==undefined)piDate=g('date');
      if(!sup&&cols.sup!==undefined)sup=g('sup');
      if(!cur&&cols.cur!==undefined)cur=g('cur');
      if(!taxR&&cols.tax!==undefined)taxR=g('tax');
    }
    if(!prods.length){ notifyPi('导入失败：未识别到产品明细行（需 SKU/Description + 数量/QNTY>0）',''); return; }
    if(!piNo)piNo=piNoE;
    if(!piDate)piDate=piDateE;
    if(!sup){ /* 供应商列缺失时取表格顶部卖方公司名（如 MK ENERGY(SHENZHEN) CO.,LTD.） */
      for(var r0=0;r0<Math.min(hi,s.rows.length)&&!sup;r0++){
        var rw=s.rows[r0]||[];
        for(var c0=0;c0<rw.length&&c0<6;c0++){
          var t0=String(rw[c0]==null?'':rw[c0]).trim();
          if(t0&&t0.length<90&&/(ltd|limited|inc)\\b/i.test(t0)&&!/^(to|address|add)\\b/i.test(t0)){ sup=t0; break; }
        }
      }
    }
    if(!cur){ /* 币种无列时从表头文字/价格符号推断 */
      var htxt='';
      s.rows.slice(0,hi+1).forEach(function(row){ (row||[]).forEach(function(v){ htxt+=String(v==null?'':v)+'|'; }); });
      var hlow=htxt.toLowerCase();
      if(hlow.indexOf('usd')>=0||hlow.indexOf('us$')>=0)cur='USD';
      else if(hlow.indexOf('eur')>=0||hlow.indexOf('€')>=0)cur='EUR';
      else if(hlow.indexOf('rmb')>=0||hlow.indexOf('cny')>=0)cur='CNY';
      else if(htxt.indexOf('$')>=0)cur='USD';
    }
    /* 填表单 */
    var noEl=document.getElementById('fPiNo');
    if(piNo&&!noEl.value)noEl.value=piNo;
    if(piDate){ var dm=String(piDate).match(/(\\d{4})[-\\/.](\\d{1,2})[-\\/.](\\d{1,2})/); if(dm)document.getElementById('fPiDate').value=dm[1]+'-'+('0'+dm[2]).slice(-2)+'-'+('0'+dm[3]).slice(-2); }
    if(sup)document.getElementById('fPiSup').value=sup;
    var curMap={'cny':'CNY','rmb':'CNY','人民币':'CNY','usd':'USD','美元':'USD','eur':'EUR','欧元':'EUR','hkd':'HKD','港币':'HKD','gbp':'GBP','英镑':'GBP'};
    var cv=curMap[String(cur).toLowerCase()]||'';
    if(cv)document.getElementById('fPiCur').value=cv;
    var tv=parseFloat(String(taxR).replace(/[^\\d.\\-]/g,''));
    if(!isNaN(tv)&&tv>0&&tv<=100)document.getElementById('fPiTaxRate').value=tv;
    var incEl=document.getElementById('fPiTaxInc');
    if(incEl)incEl.value='inc';   /* PI表格单价均为含税价；未税金额由税率折算 */
    document.getElementById('fmProds').innerHTML='';
    prods.forEach(addProdRow);
    if(FM_TYPE==='pi')updPiRebSum();
    updProdCurSym();
    notifyPi('已从「'+f.name+'」（工作表：'+s.name+'）自动填入 '+prods.length+' 行产品；单价按含税口径填入，税率/未税金额请核对补填','ok');
  }).catch(function(){ notifyPi('无法连接录入服务，导入失败',''); });
}
function savePi(){
  var no=document.getElementById('fPiNo').value.trim().toUpperCase();
  if(!no){ notifyPi('请填写 PI 单号',''); return; }
  var products=collectProds(); if(!products)return;
  var taxInc=document.getElementById('fPiTaxInc').value==='inc';
  var body={ piNo:no, date:document.getElementById('fPiDate').value, supplier:document.getElementById('fPiSup').value.trim(), currency:document.getElementById('fPiCur').value, taxIncluded:taxInc, taxRate:Number(document.getElementById('fPiTaxRate').value)||0, remark:document.getElementById('fPiRemark').value.trim(), products:products };
  var btn=document.getElementById('fmSave'); btn.disabled=true; btn.textContent='保存中…';
  apiJson('POST',API_BASE+'/api/pis',body).then(function(r){
    if(r.status===200&&r.body&&r.body.ok){
      refreshLivePi().then(function(){ var isEdit=!!FM_EDIT; closeFm(); alert(isEdit?'PI 单已更新，页面已刷新':'PI 单已保存，页面已刷新'); });
    }else{ btn.disabled=false; btn.textContent='保存 PI 单'; notifyPi((r.body&&r.body.error)?r.body.error:'保存失败',''); }
  }).catch(function(){ btn.disabled=false; btn.textContent='保存 PI 单'; notifyPi('无法连接本机录入服务（127.0.0.1:8899），请确认服务已运行',''); });
}
/* --- 产品明细行 --- */
/* 批次表单行首的「归属 PI」下拉: 选项来自当前「关联 PI 单」输入框(支持一柜混装多个 PI) */
function piSelHtml(cur){
  var el=document.getElementById('fBPi');
  var list=batchPiList({piNo:(el&&el.value)||''});
  var c=String(cur||'').trim().toUpperCase();
  if(c&&list.indexOf(c)<0)list=list.concat([c]);
  var h='<select class="pr-pi" title="该行产品属于哪个 PI（混装批次按 PI 统计发货进度与退税后成本）"><option value="">—</option>';
  list.forEach(function(pn){ h+='<option value="'+esc2(pn)+'"'+(pn===c?' selected':'')+'>'+esc2(pn)+'</option>'; });
  return h+'</select>';
}
/* 关联 PI 输入框变化后, 刷新所有产品行的归属下拉选项(保留已选值) */
function refreshPiSel(){
  var sels=document.querySelectorAll('#fmProds .pr-pi');
  for(var i=0;i<sels.length;i++){
    var keep=sels[i].value;
    var tmp=document.createElement('div'); tmp.innerHTML=piSelHtml(keep);
    sels[i].parentNode.replaceChild(tmp.firstChild,sels[i]);
  }
}
function addProdRow(p){
  p=p||{};
  var box=document.getElementById('fmProds'); if(!box)return;
  var reb=FM_TYPE==='pi';
  var batch=FM_TYPE==='batch';
  var row=document.createElement('div');
  row.className='prod-row'+(reb?' with-reb':'')+(batch?' with-pi':'');
  row.innerHTML=
    (batch?piSelHtml(p.piNo||''):'')+
    '<input class="pr-sku" value="'+esc2(p.sku||'')+'" placeholder="12.8V100AH">'+
    '<input class="pr-name" value="'+esc2(p.name||'')+'" placeholder="商品名称（选填）">'+
    '<input class="pr-qty" type="number" min="1" step="1" value="'+(p.qty?Number(p.qty):'')+'" placeholder="0">'+
    '<input class="pr-price" type="number" min="0" step="0.01" value="'+(p.unitPrice?Number(p.unitPrice):'')+'" placeholder="0.00">'+
    (reb?'<input class="pr-rebate" type="number" min="0" max="100" step="0.1" value="'+(p.rebate||p.rebate===0?Number(p.rebate):'')+'" placeholder="0" title="该产品出口退税率(%)，如锂电池 6">':'')+
    (reb?'<input class="pr-net" readonly placeholder="—" title="退税后单价 = 成本单价 − 单价/(1+增值税率)×退税率（未税口径=单价×(1−退税率)）" style="background:#14271f;text-align:right;color:#2ec4a6;font-weight:600">':'')+
    '<input class="pr-amt" readonly placeholder="—" style="background:#1a2133;text-align:right">'+
    '<button type="button" class="rm" title="删除该行">×</button>';
  var qty=row.querySelector('.pr-qty'),price=row.querySelector('.pr-price'),amt=row.querySelector('.pr-amt');
  var upd=function(){ amt.value=(qty.value!==''&&price.value!=='')?curSymNow()+(Number(qty.value)*Number(price.value)).toFixed(2):'—'; updProdTotalQty(); };
  qty.addEventListener('input',upd); price.addEventListener('input',upd);
  var skuIn=row.querySelector('.pr-sku');
  if(skuIn)skuIn.addEventListener('input',updBatchSkuInfo);
  row.querySelector('.rm').addEventListener('click',function(){ box.removeChild(row); if(FM_TYPE==='pi')updPiRebSum(); updProdTotalQty(); updBatchSkuInfo(); });
  box.appendChild(row);
  updProdTotalQty();
  if(batch)updBatchSkuInfo();
}
function collectProds(){
  var rows=document.querySelectorAll('#fmProds .prod-row'),out=[];
  for(var i=0;i<rows.length;i++){
    var r=rows[i];
    var sku=r.querySelector('.pr-sku').value.trim().toUpperCase();
    var qty=Number(r.querySelector('.pr-qty').value);
    if(!sku&&!qty)continue;
    if(!sku){ notifyPi('第 '+(i+1)+' 行 SKU 不能为空',''); return null; }
    if(!qty||qty<=0){ notifyPi('第 '+(i+1)+' 行数量必须大于 0',''); return null; }
    var o={ sku:sku, name:r.querySelector('.pr-name').value.trim(), qty:Math.round(qty), unitPrice:Number(r.querySelector('.pr-price').value)||0 };
    var piEl=r.querySelector('.pr-pi');           /* 批次表单: 该行归属的 PI(混装时区分) */
    if(piEl&&piEl.value)o.piNo=piEl.value.trim().toUpperCase();
    var rbEl=r.querySelector('.pr-rebate');
    if(rbEl)o.rebate=Math.min(100,Math.max(0,Number(rbEl.value)||0));
    out.push(o);
  }
  if(!out.length){ notifyPi('至少需要一行产品',''); return null; }
  return out;
}
/* --- 出口退税: 退税 = Σ 数量×单价 ÷(1+增值税率) × 退税率(含税口径) 或 数量×未税单价×退税率(未税口径); 最终成本 = 合同价 − 退税 --- */
function piMoney(v,cur){ return (v===null||v===undefined||isNaN(v))?'—':(CUR_SYM[cur]||(cur?cur+' ':' '))+Number(v).toLocaleString('zh-CN',{minimumFractionDigits:2,maximumFractionDigits:2}); }
function piVatRate(pi){ var r=Number(pi.taxRate)||0; return r>0?r:13; }
/* 表单内实时退税后单价: 读取当前表单的口径/税率 */
function piNetUnitLive(up,rb){
  var incEl=document.getElementById('fPiTaxInc'), inc=!(incEl&&incEl.value==='ex');
  var trEl=document.getElementById('fPiTaxRate'), r=Number(trEl?trEl.value:0)||0; if(r<=0)r=13;
  up=Number(up)||0; rb=Number(rb)||0;
  if(!up)return 0;
  if(!rb)return up;
  return inc? up-(up/(1+r/100))*(rb/100) : up*(1-rb/100);   /* 含税: 价−价/(1+税率)×退税率; 未税: 价×(1−退税率) */
}
function piRebUnit(p,pi){ /* 单件退税后成本 */
  var up=Number(p.unitPrice)||0, rb=Number(p.rebate)||0;
  if(!up||!rb)return up;
  if(pi.taxIncluded===false)return up*(1-rb/100);          /* 未税口径 */
  return up-(up/(1+piVatRate(pi)/100))*(rb/100);           /* 含税口径: 合同价-合同价/(1+税率)*退税率 */
}
function piRebateTotal(pi){ /* 出口退税合计 */
  var r=piVatRate(pi), inc=pi.taxIncluded!==false;
  return (pi.products||[]).reduce(function(s,p){
    var q=Number(p.qty)||0, up=Number(p.unitPrice)||0, rb=Number(p.rebate)||0;
    if(!q||!up||!rb)return s;
    var base=inc?up/(1+r/100):up;
    return s+q*base*(rb/100);
  },0);
}
function piNetTotal(pi){ return piTotal(pi)-piRebateTotal(pi); } /* 最终成本合计 = 合同价合计 − 出口退税合计 */
function updPiRebSum(){
  var el=document.getElementById('piRebSum'); if(!el)return;
  var curEl=document.getElementById('fPiCur'), cur=curEl?curEl.value:'CNY';
  var incEl=document.getElementById('fPiTaxInc'), inc=!(incEl&&incEl.value==='ex');
  var trEl=document.getElementById('fPiTaxRate'), r=Number(trEl?trEl.value:0)||0; if(r<=0)r=13;
  var rows=document.querySelectorAll('#fmProds .prod-row');
  var contract=0,reb=0;
  for(var i=0;i<rows.length;i++){
    var q=Number(rows[i].querySelector('.pr-qty').value)||0;
    var up=Number(rows[i].querySelector('.pr-price').value)||0;
    var rbEl=rows[i].querySelector('.pr-rebate');
    var rb=rbEl?(Number(rbEl.value)||0):0;
    var netEl=rows[i].querySelector('.pr-net');                    /* 每行退税后单价实时刷新 */
    if(netEl)netEl.value=(up>0)?piNetUnitLive(up,rb).toFixed(2):'—';
    if(!q||!up)continue;
    var amt=q*up; contract+=amt;
    if(rb){ var base=inc?up/(1+r/100):up; reb+=q*base*(rb/100); }
  }
  var M=function(v){ return piMoney(v,cur); };
  el.innerHTML=
    '<span>口径 <b>'+(inc?'含税':'未税')+'</b> · 增值税率 <b>'+(Number(trEl?trEl.value:0)||13)+'</b>%（退税=含税÷(1+税率)×退税率）</span>'+
    '<span>合同价合计 <b>'+M(contract)+'</b></span>'+
    '<span>出口退税合计 <b style="color:#2ec4a6">'+M(reb)+'</b></span>'+
    '<span class="net">最终成本（合同−退税）<b>'+M(contract-reb)+'</b></span>';
}
/* --- 头程发货批次 新增/编辑/删除 --- */
function batchAdd(){ if(!LIVE)return piReadonlyTip(); batchForm(null); }
function batchEdit(id){ if(!LIVE)return piReadonlyTip(); var b=BATCHES.filter(function(x){return x.id===id})[0]; if(b)batchForm(b); }
function batchDel(id){
  if(!LIVE)return piReadonlyTip();
  if(!confirm('确定删除该发货批次吗？'))return;
  apiJson('DELETE',API_BASE+'/api/batches/'+encodeURIComponent(id)).then(function(r){
    if(r.status===200&&r.body&&r.body.ok){ refreshLivePi().then(function(){ alert('已删除发货批次'); }); }
    else alert((r.body&&r.body.error)?('删除失败：'+r.body.error):'删除失败');
  }).catch(function(){ alert('无法连接本机录入服务，删除失败'); });
}
function batchForm(b){
  FM_TYPE='batch'; FM_EDIT=b?(b.id||''):null;
  /* 运费币种独立于产品币种: 海运费大多人民币报价, 默认 CNY; 老批次回落原 currency 字段 */
  FRT_CUR=b?(b.freightCurrency||b.currency||'CNY'):'CNY';
  /* 入库费用(卸货费)币种独立: 目的仓收费多为美金报价, 默认 USD */
  IB_CUR=b?(b.inboundFeeCurrency||'USD'):'USD';
  /* 手动关联 PI: 可自由输入 PI 单号(input+datalist), 已有 PI 显示为建议; 默认不预选任何 PI */
  var sorted=PIS.slice().sort(function(a,c){return a.piNo<c.piNo?-1:1});
  var piOpts='';
  sorted.forEach(function(p){ piOpts+='<option value="'+esc2(p.piNo)+'">'; });
  var selPi=b?(b.piNo||''):'';
  var mOpt='';['海运','空运','快递','铁路','其他'].forEach(function(m){ mOpt+='<option'+(m===(b?b.method:'海运')?' selected':'')+'>'+m+'</option>'; });
  /* 兼容旧数据: 老批次柜号存在合并字段 trackingNo 里, 标准柜号格式(4字母+7数字)自动识别到柜号栏 */
  var contVal=b?(b.containerNo||''):'';
  if(b&&!contVal&&b.trackingNo&&/^[A-Z]{4}\\d{7}$/.test(String(b.trackingNo).trim().toUpperCase())) contVal=String(b.trackingNo).trim().toUpperCase();
  var h='<h2>'+(b?'编辑发货批次 <span class="mono">'+esc2(b.batchNo||'')+'</span>':'新增发货批次')+'</h2>';
  h+='<div class="fm-grid">';
  h+='<div class="fm-field full"><label>关联 PI 单 *<span class="row-note">（可多个，一柜混装）</span></label><input id="fBPi" list="fBPiList" value="'+esc2(selPi)+'" placeholder="如 ML20260107010、ML20260115017" onchange="onBPi()"><datalist id="fBPiList">'+piOpts+'</datalist><div class="hint">一个入库单/一柜可以混装多个 PI：把单号都填上（用「、」或「,」分隔）。选取后自动带出各 PI 的产品行，行首「归属 PI」可逐行调整，数量按实际发运填写</div></div>';
  h+='<div class="fm-field"><label>批次号 *</label><input id="fBBatch" value="'+esc2(b?b.batchNo:'')+'" placeholder="如 0901A"'+(b?' readonly':'')+'><div class="hint">同 PI 下批次号不可重复</div></div>';
  h+='<div class="fm-field"><label>发货日期</label><input id="fBDate" type="date" value="'+esc2(b?(b.shipDate||todayStr()):todayStr())+'"></div>';
  h+='<div class="fm-field"><label>运输方式</label><select id="fBMethod">'+mOpt+'</select></div>';
  /* 头程物流商: 自由文本 + 历史值建议(手填为主, 海外仓不登记该字段) */
  var carrierList=[];
  (PIF.batches||[]).forEach(function(x){ var c=String(x.carrier||'').trim(); if(c&&carrierList.indexOf(c)<0)carrierList.push(c); });
  carrierList.sort();
  var carrierOpts=carrierList.map(function(c){ return '<option value="'+esc2(c)+'">'; }).join('');
  h+='<div class="fm-field"><label>头程物流商</label><input id="fBCarrier" list="fBCarrierList" value="'+esc2(b?(b.carrier||''):'')+'" placeholder="如 富皇美运 / 中外运 / 顺丰国际"><datalist id="fBCarrierList">'+carrierOpts+'</datalist><div class="hint">承运头程的物流公司，<b>由业务自行填写</b>（海外仓 WMS 不登记该字段）；下拉可快速选历史用过的物流商</div></div>';
  h+='<div class="fm-field full"><label>出口单号（整柜发运可填柜号）</label><input id="fBExport" value="'+esc2(b?b.exportNo:'')+'" placeholder="如 MK20260901"></div>';
  h+='<div class="fm-field"><label>柜号（集装箱号）</label><input id="fBContainer" value="'+esc2(contVal)+'" placeholder="如 CMAU1234567 或 TIUU5426781"><div class="hint">整柜运输的集装箱柜号，查物流主要用它</div></div>';
  h+='<div class="fm-field"><label>货运跟踪号</label><input id="fBTrack" value="'+esc2(b?b.trackingNo:'')+'" placeholder="如 SF1234567890 或运单号"><div class="hint">物流承运商跟踪号/运单号（散货、快递常用）</div></div>';
  h+='<div class="fm-field"><label>入库单号</label><input id="fBRo" value="'+esc2(b?b.ro:'')+'" placeholder="可留空自动匹配或手填" oninput="updIbHint()"><div class="hint">各海外仓格式不同，按入库仓的实际单号填写（填后自动带出富皇 OMS 卸货费）</div></div>';
  h+='<div class="fm-field"><label>目的国家 *</label><select id="fBCountry" onchange="onWhCountry()">'+countryOpts(b?(b.country||guessCountryOf(b.warehouse)||'美国'):'美国')+'</select><div class="hint">发往哪个国家的海外仓</div></div>';
  h+='<div class="fm-field full"><label>入库仓库 <span id="fBWhHint" style="font-weight:400;color:var(--sub)"></span></label><input id="fBWh" list="fBWhList" value="'+esc2(b?b.warehouse:'')+'" placeholder="如 SAV02"><datalist id="fBWhList"></datalist><button type="button" class="fm-row-btn" style="margin:6px 0 0" onclick="matchRoNow()">⚡ 按出口单号/柜号自动匹配入库单号</button></div>';
  h+='<div class="fm-field"><label>总毛重 (kg)</label><input id="fBWeight" type="number" min="0" step="0.1" value="'+(b?Number(b.grossWeightKg)||'':'')+'" placeholder="0" oninput="updRatePv()"></div>';
  h+='<div class="fm-field"><label>总费用（头程） <span class="cur-sym-frt" onclick="toggleFreightCur()" title="运费币种可点击切换 人民币¥ / 美金$（运费多为人民币报价，默认 ¥；与产品币种相互独立）" style="cursor:pointer;border-bottom:1px dashed #888;color:var(--sub)">'+(CUR_SYM[FRT_CUR]||'¥')+'</span></label><input id="fBFreight" type="number" min="0" step="0.01" value="'+(b?Number(b.totalFreight)||'':'')+'" placeholder="0.00" oninput="updRatePv()"><div class="hint">均摊成本 ≈ <b class="rate-pv" id="fBRatePv">—</b>（按运费币种，不含卸货费）</div></div>';
  var omsF=omsFeeOf({ro:b?b.ro:''});                        /* 富皇 OMS 自动同步的卸货费(按入库单号) */
  var ibHint=omsF
    ?('已自动同步富皇 OMS 卸货费 <b>'+piMoney(omsF.unloadFee,omsF.currency||'USD')+'</b>'+(omsF.billNo?('（账单 '+esc2(omsF.billNo)+'）'):'')+'；此栏留空即用同步值，填写则优先采用手填')
    :'目的仓收货/卸货费用，按入库单(RO)汇总；已接通富皇 OMS 自动同步，未覆盖的单（如 FBA/盘古德国仓）可手填';
  h+='<div class="fm-field"><label>入库费用（卸货费） <span class="cur-sym-ib" onclick="toggleInboundCur()" title="卸货费币种可点击切换 美金$ / 人民币¥（目的仓收费多为美金报价，默认 $）" style="cursor:pointer;border-bottom:1px dashed #888;color:var(--sub)">'+(CUR_SYM[IB_CUR]||'$')+'</span></label><input id="fBIbFee" type="number" min="0" step="0.01" value="'+(b?Number(b.inboundFee)||'':'')+'" placeholder="'+(omsF?('自动同步 '+Number(omsF.unloadFee).toFixed(2)):'0.00')+'"><div class="hint" id="fBIbHint">'+ibHint+'</div></div>';
  h+='<div class="fm-field"><label>币种（产品成本）</label><select id="fBCur" onchange="updProdCurSym()">'+curOptions(b?(b.currency||'CNY'):'CNY')+'</select></div>';
  h+='<div class="fm-field full"><label>入库重量 / 入库尺寸（单件）</label><div id="fBSkuInfo" class="sku-info" style="margin-top:2px"></div></div>';
  h+='<div class="fm-field full"><label>备注</label><input id="fBRemark" value="'+esc2(b?b.remark:'')+'"></div>';
  h+='</div>'+prodHead()+'<div id="fmProds"></div>'+prodTotalBar();
  h+='<button type="button" class="fm-row-btn" onclick="addProdRow()">＋ 添加产品行</button>';
  h+='<p class="fm-err" id="fmErr"></p>';
  h+='<div class="fm-bar"><button class="btn" onclick="closeFm()">取消</button><button class="btn primary" id="fmSave" onclick="saveBatch()">保存批次</button></div>';
  fmOpen(h);
  /* 产品行: 编辑用原录入行; 新增时按「关联 PI 单」里每个 PI 带出其全部产品(行内标注归属 PI, 数量可改) */
  var prods=(b&&b.products&&b.products.length)?b.products:null;
  if(!prods&&selPi){
    prods=[];
    batchPiList({piNo:selPi}).forEach(function(pn){
      var pi=PIS.filter(function(p){return p.piNo===pn})[0]; if(!pi)return;
      (pi.products||[]).forEach(function(x){ prods.push({sku:x.sku,name:x.name,unitPrice:Number(piRebUnit(x,pi).toFixed(2)),qty:'',piNo:pn}); });
    });
  }
  (prods&&prods.length?prods:[{sku:'',name:'',qty:'',unitPrice:''}]).forEach(addProdRow);
  var fBPi=document.getElementById('fBPi'); if(fBPi)fBPi._prev=fBPi.value;
  updRatePv();
  updBatchSkuInfo();
  onWhCountry();
}
/* 批次表单里的「入库重量 / 入库尺寸」(单件, 海外仓 WMS 同步的 SKU 档案, 只读展示; 不占批次表列位) */
function updBatchSkuInfo(){
  var box=document.getElementById('fBSkuInfo'); if(!box)return;
  var seen={}, skus=[];
  var list=document.querySelectorAll('#fmProds .prod-row .pr-sku');
  for(var i=0;i<list.length;i++){
    var s=String(list[i].value||'').trim(); if(!s)continue;
    var k=s.toUpperCase(); if(seen[k])continue; seen[k]=1; skus.push(k);
  }
  if(!skus.length){ box.innerHTML='<span class="dim">填写产品行（或选好关联 PI 单）后，这里自动显示各 SKU 的单件入库重量与尺寸（取自海外仓 WMS 档案，只读）。</span>'; return; }
  var rows=skus.map(function(s){
    var w=skuWeightKg(s), d=skuDimsOf(s), rec=SKU_W[s]||{};
    var nm=rec.name?String(rec.name):'';
    var ws=w>0?('<b style="color:#2ec4a6">'+w.toFixed(3)+' kg</b>'):'<span style="color:#e8a24e">无档案</span>';
    return '<div style="display:flex;gap:12px;flex-wrap:wrap;padding:4px 0;border-bottom:1px solid var(--row-line)">'
      +'<span class="mono" style="min-width:130px">'+esc2(s)+'</span>'
      +'<span style="flex:1 1 150px;color:var(--sub)">'+esc2(nm)+'</span>'
      +'<span style="min-width:150px">单件 '+ws+'</span>'
      +'<span style="min-width:170px">尺寸 '+(d?esc2(d)+' cm':'<span class="dim">—</span>')+'</span>'
      +'</div>';
  }).join('');
  box.innerHTML='<div style="border:1px solid var(--line);border-radius:8px;padding:6px 10px;max-height:170px;overflow:auto">'+rows+'</div>';
}
/* 运费币种(独立于产品币种): 默认 CNY, 表单 label 符号可点击切换 */
var FRT_CUR='CNY';
/* 入库费用(卸货费)币种: 默认 USD, 可点击切换 */
var IB_CUR='USD';
function toggleInboundCur(){
  IB_CUR=(IB_CUR==='USD')?'CNY':'USD';
  var sp=document.querySelectorAll('.cur-sym-ib');
  for(var i=0;i<sp.length;i++)sp[i].textContent=CUR_SYM[IB_CUR]||IB_CUR;
}
/* 入库单号变化时, 实时提示富皇 OMS 同步到的卸货费 */
function updIbHint(){
  var el=document.getElementById('fBRo'), hint=document.getElementById('fBIbHint'), fee=document.getElementById('fBIbFee');
  if(!el||!hint)return;
  /* 头程物流商由业务自行填写(海外仓不登记该字段), 不做自动带出 */
  var omsF=omsFeeOf({ro:(el.value||'').trim()});
  if(omsF){
    hint.innerHTML='已自动同步富皇 OMS 卸货费 <b>'+piMoney(omsF.unloadFee,omsF.currency||'USD')+'</b>'+(omsF.billNo?('（账单 '+esc2(omsF.billNo)+'）'):'')+'；此栏留空即用同步值，填写则优先采用手填';
    if(fee)fee.placeholder='自动同步 '+Number(omsF.unloadFee).toFixed(2);
  }else{
    hint.innerHTML='目的仓收货/卸货费用，按入库单(RO)汇总；已接通富皇 OMS 自动同步，未覆盖的单（如 FBA/盘古德国仓）可手填';
    if(fee)fee.placeholder='0.00';
  }
}
function toggleFreightCur(){
  FRT_CUR=(FRT_CUR==='USD')?'CNY':'USD';
  var sp=document.querySelectorAll('.cur-sym-frt');
  for(var i=0;i<sp.length;i++)sp[i].textContent=CUR_SYM[FRT_CUR]||FRT_CUR;
  updRatePv();
}
function updRatePv(){
  var el=document.getElementById('fBRatePv'); if(!el)return;
  var w=Number((document.getElementById('fBWeight')||{}).value)||0;
  var f=Number((document.getElementById('fBFreight')||{}).value)||0;
  if(w>0&&f>0)el.innerHTML=money(f/w,FRT_CUR,3)+' <span style="font-weight:400">/kg</span>';
  else el.innerHTML='<span style="font-weight:400;color:var(--sub)">'+(f>0?'请填写总毛重':'请填写总毛重与总费用')+'</span>';
}
function onBPi(){
  var el=document.getElementById('fBPi');
  var raw=(el.value||'').trim().toUpperCase();
  var box=document.getElementById('fmProds');
  if(!box)return;
  var list=batchPiList({piNo:raw});
  if(!list.length){ el._prev=''; refreshPiSel(); return; }   /* 未填写: 不自动带出任何产品 */
  var known=list.filter(function(pn){ return PIS.some(function(p){return p.piNo===pn}) });
  /* 全部为尚未建档的 PI: 只刷新行首归属下拉, 不带出产品行(保存后建档即自动关联) */
  if(!known.length){ el._prev=raw; refreshPiSel(); return; }
  if(box.children.length && !confirm('按「关联 PI 单」重新带出产品行会清空当前已填的行（数量需重填），继续吗？')) {
    el.value=el._prev||'';               /* 用户取消: 回退输入 */
    return;
  }
  el.value=list.join('、');              /* 分隔符归一化, 便于阅读 */
  el._prev=el.value;
  box.innerHTML='';
  /* 带出的是退税后单价(合同价−退税), 无退税率的产品行退化为合同价; 每行标注归属 PI */
  var rows=0;
  list.forEach(function(pn){
    var pi=PIS.filter(function(p){return p.piNo===pn})[0]; if(!pi)return;
    (pi.products||[]).forEach(function(x){ addProdRow({sku:x.sku,name:x.name,unitPrice:Number(piRebUnit(x,pi).toFixed(2)),qty:'',piNo:pn}); rows++; });
  });
  /* 币种跟随该 PI 的计价币种(大部分 PI 美金、少部分人民币), 符号同步 */
  var curSel=document.getElementById('fBCur');
  var curs=known.map(function(pn){ var pi=PIS.filter(function(p){return p.piNo===pn})[0]; return (pi&&pi.currency)||''; }).filter(function(c){return c});
  var uniq=curs.filter(function(c,i){return curs.indexOf(c)===i;});
  if(curSel&&uniq.length===1)curSel.value=uniq[0];
  updProdCurSym();
  notifyPi('已按 '+list.length+' 个 PI 带出 '+rows+' 行产品'+(uniq.length===1?('，币种已同步为 '+uniq[0]):(uniq.length>1?('；各 PI 币种不同（'+uniq.join(' / ')+'），请核对表单币种'):''))+'，请补填数量','');
}
function matchRoNow(){
  var ex=document.getElementById('fBExport').value.trim();
  var ct=document.getElementById('fBContainer').value.trim();
  var tr=document.getElementById('fBTrack').value.trim();
  if(!ex&&!ct&&!tr){ notifyPi('请先填写「出口单号」「柜号」或「货运跟踪号」再自动匹配',''); return; }
  notifyPi('正在匹配…','');
  apiJson('POST',API_BASE+'/api/match-ro',{exportNo:ex,containerNo:ct,trackingNo:tr}).then(function(r){
    if(r.status===200&&r.body&&r.body.ok){
      var ro=document.getElementById('fBRo'); if(ro)ro.value=r.body.ro||'';
      updIbHint();   /* 匹配到入库单号后, 顺带带出富皇 OMS 卸货费提示 */
      var wh=document.getElementById('fBWh'); if(wh&&r.body.warehouse&&!wh.value)wh.value=r.body.warehouse;
      /* 匹配到仓库代码时顺带推断目的国家并回填下拉 */
      var ctry=document.getElementById('fBCountry');
      if(ctry&&r.body.warehouse){ var gc=guessCountryOf(r.body.warehouse); if(gc)ctry.value=gc; onWhCountry(); }
      notifyPi('✓ 匹配成功：入库单号 '+r.body.ro+(r.body.warehouse?(' · 仓库 '+r.body.warehouse):'')+(r.body.status?(' · '+r.body.status):''),true);
    } else notifyPi('未在 OMS 入库单中找到匹配（可手填入库单号，不影响本页汇总）','');
  }).catch(function(){ notifyPi('无法连接本机录入服务',''); });
}
function saveBatch(){
  var piRaw=document.getElementById('fBPi').value.trim().toUpperCase();
  var batchNo=document.getElementById('fBBatch').value.trim();
  var piList=batchPiList({piNo:piRaw});   /* 一个入库单/一柜可混装多个 PI, 用「、」或「,」分隔 */
  if(!piList.length){ notifyPi('请填写关联的 PI 单号（多个用「、」分隔）',''); return; }
  if(!batchNo){ notifyPi('请填写批次号',''); return; }
  if(LIVE&&typeof PIS!=='undefined'&&PIS.length){
    var unknown=piList.filter(function(pn){ return !PIS.some(function(p){return p.piNo===pn}); });
    if(unknown.length){ notifyPi('PI 单号不存在：'+unknown.join('、')+'。请先在「PI 单列表」新增这些 PI 再录批次',''); return; }
  }
  var products=collectProds(); if(!products)return;
  /* 混装批次: 未选归属 PI 的产品行, 若只关联一个 PI 自动归它 */
  if(piList.length===1){ products.forEach(function(p){ if(!p.piNo)p.piNo=piList[0]; }); }
  var body={ piNo:piList.join('、'), piNos:piList, batchNo:batchNo, shipDate:document.getElementById('fBDate').value, method:document.getElementById('fBMethod').value,
    exportNo:document.getElementById('fBExport').value.trim(), containerNo:document.getElementById('fBContainer').value.trim(),
    trackingNo:document.getElementById('fBTrack').value.trim(),
    ro:document.getElementById('fBRo').value.trim(), warehouse:document.getElementById('fBWh').value.trim(),
    carrier:document.getElementById('fBCarrier')?document.getElementById('fBCarrier').value.trim():'',
    country:document.getElementById('fBCountry')?document.getElementById('fBCountry').value:'',
    grossWeightKg:Number(document.getElementById('fBWeight').value)||0, totalFreight:Number(document.getElementById('fBFreight').value)||0,
    freightCurrency:FRT_CUR,
    inboundFee:Number((document.getElementById('fBIbFee')||{}).value)||0, inboundFeeCurrency:IB_CUR,
    currency:document.getElementById('fBCur').value, remark:document.getElementById('fBRemark').value.trim(), products:products };
  /* 新 id 由「PI 组合 + 批次号」决定: 编辑时若改了 PI 组合, 保存后清掉旧记录避免重复 */
  var newId=piList.slice().sort().join('+')+'|'+batchNo;
  var oldId=FM_EDIT||'';
  var btn=document.getElementById('fmSave'); btn.disabled=true; btn.textContent='保存中…';
  apiJson('POST',API_BASE+'/api/batches',body).then(function(r){
    if(r.status===200&&r.body&&r.body.ok){
      var done=function(){ refreshLivePi().then(function(){ var isEdit=!!oldId; closeFm(); alert(isEdit?'发货批次已更新，页面已刷新':'发货批次已保存，页面已刷新'); }); };
      if(oldId&&oldId!==newId){
        apiJson('DELETE',API_BASE+'/api/batches/'+encodeURIComponent(oldId)).then(done).catch(done);
      } else done();
    }else{ btn.disabled=false; btn.textContent='保存批次'; notifyPi((r.body&&r.body.error)?r.body.error:'保存失败',''); }
  }).catch(function(){ btn.disabled=false; btn.textContent='保存批次'; notifyPi('无法连接本机录入服务（127.0.0.1:8899），请确认服务已运行',''); });
}

/* ---------- SKU 详情弹窗 ---------- */
function openDetail(sku){
  var r=ROWS.filter(function(x){return String(x.sku)===sku})[0];
  if(!r)return;
  document.getElementById('mTitle').innerHTML='<span class="mono">'+esc2(r.sku)+'</span>'+(r.name?' · '+esc2(r.name):'')+' <span class="badge '+LEVEL[r.level]+'">'+LABEL[r.level]+'</span>';
  var w=params.w||{d7:40,d30:30,d60:30};
  var g=document.getElementById('mGrid');
  g.innerHTML=
    '<div class="d-item"><div class="k">在库 / 在途</div><div class="v">'+fmt(r.onHand)+' / '+fmt(r.inTransit)+' 件</div></div>'+
    '<div class="d-item"><div class="k">在库+在途 合计</div><div class="v">'+fmt(r.position)+' 件</div></div>'+
    '<div class="d-item"><div class="k">预测日销 D（'+w.d7+'%×μ7＋'+w.d30+'%×μ30＋'+w.d60+'%×μ60）</div><div class="v">'+fmt(r.rate,2)+' 件/天</div></div>'+
    '<div class="d-item"><div class="k">近 7 / 30 / 60 天日均 μ7/μ30/μ60</div><div class="v">'+fmt(r.mu7,2)+' / '+fmt(r.mu30,2)+' / '+fmt(r.mu60,2)+' 件/天</div></div>'+
    '<div class="d-item"><div class="k">日销波动 σ（近 '+params.sigmaWindowDays+' 天样本）</div><div class="v">'+fmt(r.sigma,2)+' 件/天</div></div>'+
    '<div class="d-item"><div class="k">安全库存 SS = Z×σ×√L</div><div class="v">'+(r.rate>0?fmt(r.ss)+' 件（≈'+fmt(r.ssDays,1)+' 天需求）':'—')+'</div></div>'+
    '<div class="d-item"><div class="k">可售天数</div><div class="v '+(r.level==='red'?'red':(r.level==='orange'?'orange':''))+'">'+(r.rate>0?fmt(r.coverDays,1)+' 天':(r.position>0?'∞':'—'))+'</div></div>'+
    '<div class="d-item"><div class="k">再订货点 ROP = D×L＋SS</div><div class="v">'+fmt(r.rop)+(r.rate>0?' 件（≈'+fmt(r.ropDays,1)+' 天）':'')+'</div></div>'+
    '<div class="d-item"><div class="k">目标水位 S* = D×(R＋L)＋SS</div><div class="v">'+fmt(r.orderUpTo)+' 件</div></div>'+
    '<div class="d-item"><div class="k">建议补货量 = S* − 合计</div><div class="v '+(r.suggest>0?'red':'')+'">'+(r.suggest>0?fmt(r.suggest)+' 件':'—')+'</div></div>'+
    '<div class="d-item"><div class="k">最晚下单日期</div><div class="v">'+(r.lastOrderDay||'—')+'</div></div>'+
    '<div class="d-item"><div class="k">建议到货日</div><div class="v">'+(r.arriveDay||'—')+'</div></div>';
  var note=document.getElementById('mNote');
  var arr=CHARTS.skuSeries[sku];
  var monthly=CHARTS.skuMonthly[sku];
  var cv=document.getElementById('cSku');
  if(!cv){ /* 上次显示"暂无数据"时canvas被替换, 恢复 */
    document.getElementById('mChartWrap').innerHTML='<p class="trend-note" id="mNote"></p><div class="chart-box" style="height:240px"><canvas id="cSku"></canvas></div>';
    cv=document.getElementById('cSku');
  }
  var old=Chart.getChart('cSku'); if(old)old.destroy();
  if(arr&&arr.length&&r.rate>0){
    /* 近 chartDays 天实际日销(蓝) + 未来 fcDays 天波动预测(绿虚线, D×星期规律系数) */
    var hL=CHARTS.dates.map(function(x){return x.slice(5)});
    var sd=CHARTS.skuDaily[sku]||{};
    var sdPred=sd.pred||[];
    var sdDatesFull=(sd.dates||[]).map(function(x){return x.slice(5)});
    var fL=(CHARTS.fcDates||[]).map(function(x){return x.slice(5)});
    var fData=hL.map(function(){return null}).concat(sdPred);
    note.textContent='蓝=每日实际出库(件) · 绿虚线=未来 '+CHARTS.fcDays+' 天波动预测：周六周日不发货=0（周末累积订单并入周一等发货日，周一通常最高），整周发货总量=7×D='+fmt(r.rate,2)+'件/天×7';
    cSku=new Chart(cv,{type:'line',
      data:{labels:hL.concat(fL),datasets:[
        {label:'每日实际出库',data:arr,borderColor:'#4d8ff0',backgroundColor:'rgba(77,143,240,.16)',fill:true,tension:.25,pointRadius:1.5},
        {label:'波动预测',data:fData,borderColor:'#2ec4a6',borderDash:[4,3],borderWidth:2,pointRadius:1.5,fill:false}
      ]},
      options:{responsive:true,maintainAspectRatio:false,interaction:{mode:'index',intersect:false},
        scales:{x:{ticks:{maxTicksLimit:14,maxRotation:0,autoSkip:true}},y:{beginAtZero:true,ticks:{precision:0}}},
        plugins:{legend:{labels:{boxWidth:14,font:{size:11}}},tooltip:{callbacks:{label:function(ctx){return (ctx.dataset.label||'')+': '+ctx.parsed.y+' 件'}}}}}});
  } else if(monthly&&monthly.length>=2){
    note.textContent='近 '+CHARTS.chartDays+' 天无出库 → 预测日销 D=0，不触发补货；下图仅展示全历史月度出库供参考';
    cSku=new Chart(cv,{type:'bar',
      data:{labels:monthly.map(function(x){return x.m}),datasets:[{label:'月度出库',data:monthly.map(function(x){return x.qty}),backgroundColor:'rgba(24,95,165,.7)'}]},
      options:{responsive:true,maintainAspectRatio:false,
        scales:{y:{beginAtZero:true,ticks:{precision:0}}},
        plugins:{legend:{display:false},tooltip:{callbacks:{label:function(ctx){return '月度出库: '+ctx.parsed.y+' 件'}}}}}});
  } else if(monthly&&monthly.length===1){
    note.textContent='该 SKU 仅有 1 个月的出库记录（'+monthly[0].m+' 出库 '+monthly[0].qty+' 件），样本不足，暂无法估计日销';
    cv.parentNode.innerHTML='<p class="empty" style="padding:60px 0">出库记录：'+monthly[0].m+' · '+monthly[0].qty+' 件</p>';
  } else {
    note.textContent='该 SKU 没有任何出库记录，模型预测 D=0，暂无趋势图（正式环境接入真实订单后自动显示）';
    cv.parentNode.innerHTML='<p class="empty" style="padding:60px 0">暂无出库数据</p>';
  }
  document.getElementById('modal').style.display='flex';
}
function closeModal(){
  document.getElementById('modal').style.display='none';
  var w=document.getElementById('mChartWrap');
  if(!w.querySelector('canvas')){
    w.innerHTML='<p class="trend-note" id="mNote"></p><div class="chart-box" style="height:240px"><canvas id="cSku"></canvas></div>';
  }
}
document.getElementById('modal').addEventListener('click',function(e){if(e.target===this)closeModal()});

/* ---------- 初始化: 分页事件绑定 + 探测本机录入服务 ---------- */
PAGER_HOOKS={trace:renderTrace,in:renderInbound,pi:renderPiAll,pb:renderPiAll,ae:renderAeAll};
bindPagers();
initPiLive();
</script>
</body>
</html>`;
}

module.exports = { generateDashboard };
