const KEY = process.env.API_FOOTBALL_KEY, BASE = 'https://v3.football.api-sports.io';
const LEAGUES = (process.env.LEAGUE_IDS || '200,39,140,135,78,61').split(',').map(s => s.trim());
const MAX_ODDS = +process.env.MAX_ODDS || 15, TZ = 'Africa/Casablanca';

async function api(p, q) {
  const u = new URL(BASE + p);
  Object.entries(q).forEach(([k, v]) => u.searchParams.set(k, v));
  const r = await fetch(u, { headers: { 'x-apisports-key': KEY } });
  if (!r.ok) throw new Error('API-Football HTTP ' + r.status);
  const j = await r.json(), e = j.errors, msg = Array.isArray(e) ? e[0] : e && Object.values(e)[0];
  if (msg) throw new Error(msg);
  return j;
}
async function allOdds(league, season, date) {
  let page = 1, tot = 1, res = [];
  do { const j = await api('/odds', { league, season, date, page }); res.push(...j.response); tot = j.paging.total; } while (++page <= Math.min(tot, 6));
  return res;
}

// ---- Poisson model ----
const fact = [1, 1, 2, 6, 24, 120, 720, 5040, 40320], N = 8;
const dist = l => Array.from({ length: N }, (_, k) => Math.exp(-l) * l ** k / fact[k]);
const sgn = (x, y) => x > y ? 'Home' : x < y ? 'Away' : 'Draw';
function model(lh, la) {
  const H = dist(lh), A = dist(la), m = { 1: {}, 12: {}, 5: {}, 8: {}, 16: {}, 17: {}, 7: {}, 10: {} };
  let w = 0, d = 0, l = 0, o = 0, b = 0;
  for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) {
    const p = H[i] * A[j];
    i > j ? w += p : i < j ? l += p : d += p;
    if (i + j > 2) o += p; if (i && j) b += p;
    if (i < 5 && j < 5) m[10][i + ':' + j] = p;
  }
  const t = w + d + l; w /= t; d /= t; l /= t; o /= t; b /= t;
  m[1] = { Home: w, Draw: d, Away: l };
  m[12] = { 'Home/Draw': w + d, 'Home/Away': w + l, 'Draw/Away': d + l };
  m[5] = { 'Over 2.5': o, 'Under 2.5': 1 - o };
  m[8] = { Yes: b, No: 1 - b };
  m[16] = { 'Over 1.5': 1 - H[0] - H[1], 'Under 1.5': H[0] + H[1] };
  m[17] = { 'Over 1.5': 1 - A[0] - A[1], 'Under 1.5': A[0] + A[1] };
  const h1 = dist(.45 * lh), a1 = dist(.45 * la), h2 = dist(.55 * lh), a2 = dist(.55 * la);
  for (let i = 0; i < 5; i++) for (let j = 0; j < 5; j++) for (let k = 0; k < 5; k++) for (let n = 0; n < 5; n++) {
    const key = sgn(i, j) + '/' + sgn(i + k, j + n);
    m[7][key] = (m[7][key] || 0) + h1[i] * a1[j] * h2[k] * a2[n];
  }
  return m;
}
const shrink = (x, n) => 1 + (x - 1) * n / (n + 6);
const formPts = f => [...(f || '').slice(-5)].reduce((a, c) => a + (c === 'W' ? 3 : c === 'D' ? 1 : 0), 0);
function lambdas(S, hid, aid, inj) {
  const h = S.by[hid], a = S.by[aid];
  if (!h || !a || h.home.played < 4 || a.away.played < 4) return null;
  const r = (t, k) => ({ gf: t[k].goals.for / t[k].played, ga: t[k].goals.against / t[k].played, n: t[k].played });
  const H = r(h, 'home'), A = r(a, 'away');
  const fm = t => 1 + .05 * (formPts(t.form) - 7.5) / 7.5, im = c => 1 - Math.min(.08, .02 * (c || 0));
  const lh = S.lgH * shrink(H.gf / S.lgH, H.n) * shrink(A.ga / S.lgH, A.n) * fm(h) * im(inj[hid]);
  const la = S.lgA * shrink(A.gf / S.lgA, A.n) * shrink(H.ga / S.lgA, H.n) * fm(a) * im(inj[aid]);
  return { lh, la, n: Math.min(h.home.played, a.away.played), fh: h.form, fa: a.form };
}

const MK = { 1: 'Match winner', 12: 'Double chance', 8: 'BTTS', 5: 'Over/Under 2.5', 16: 'Home goals', 17: 'Away goals', 7: 'HT/FT', 10: 'Correct score' };
const DC = { 'Home/Draw': '1X', 'Home/Away': '12', 'Draw/Away': 'X2' };
function sel(id, v, f) {
  const H = f.teams.home.name, A = f.teams.away.name;
  if (id === 1) return v === 'Home' ? H + ' win' : v === 'Away' ? A + ' win' : 'Draw';
  if (id === 12) return DC[v] + ' (' + v.replace('Home', H).replace('Away', A) + ')';
  if (id === 16) return H + ' ' + v;
  if (id === 17) return A + ' ' + v;
  if (id === 5) return v + ' goals';
  if (id === 8) return 'BTTS ' + v;
  return v;
}

async function build(date) {
  const warn = [], safe = (p, l) => p.catch(e => { warn.push(l + ': ' + e.message); return null; });
  const fx = (await api('/fixtures', { date, timezone: TZ })).response
    .filter(f => f.fixture.status.short === 'NS' && LEAGUES.includes(String(f.league.id)));
  const groups = {};
  fx.forEach(f => (groups[f.league.id + '_' + f.league.season] ||= []).push(f));
  const picks = []; let skipped = 0;
  for (const g of Object.values(groups)) {
    const { id, season, name } = g[0].league;
    const [st, ij, od] = await Promise.all([
      safe(api('/standings', { league: id, season }), name + ' standings'),
      safe(api('/injuries', { league: id, season, date }), name + ' injuries'),
      safe(allOdds(id, season, date), name + ' odds')]);
    const rows = st?.response?.[0]?.league?.standings?.flat() || [];
    if (!rows.length || !od) { skipped += g.length; continue; }
    const sum = f => rows.reduce((a, r) => a + f(r), 0);
    const S = { lgH: sum(r => r.home.goals.for) / sum(r => r.home.played), lgA: sum(r => r.away.goals.for) / sum(r => r.away.played), by: Object.fromEntries(rows.map(r => [r.team.id, r])) };
    const inj = {}; (ij?.response || []).forEach(p => inj[p.team.id] = (inj[p.team.id] || 0) + 1);
    const oddsBy = Object.fromEntries(od.map(o => [o.fixture.id, o.bookmakers]));
    for (const f of g) {
      const bms = oddsBy[f.fixture.id], L = bms && lambdas(S, f.teams.home.id, f.teams.away.id, inj);
      if (!L) { skipped++; continue; }
      const M = model(L.lh, L.la), agg = {};
      for (const bm of bms) for (const bet of bm.bets) {
        if (!M[bet.id]) continue;
        const vals = bet.values.map(v => ({ k: v.value.replace('-', ':'), o: parseFloat(v.odd) })).filter(v => M[bet.id][v.k] !== undefined && v.o > 1);
        const tot = bet.id === 10 ? 1.15 : vals.reduce((a, v) => a + 1 / v.o, 0);
        for (const v of vals) {
          const a = agg[bet.id + '|' + v.k] ||= { id: bet.id, k: v.k, o: 0, bk: '', fair: [] };
          a.fair.push(1 / v.o / tot);
          if (v.o > a.o) { a.o = v.o; a.bk = bm.name; }
        }
      }
      const best = {};
      for (const a of Object.values(agg)) {
        const pm = M[a.id][a.k], fair = a.fair.reduce((x, y) => x + y, 0) / a.fair.length, p = .65 * pm + .35 * fair;
        const minP = a.id === 10 ? .06 : .15;
        if (a.o > MAX_ODDS || p < minP) continue;
        const ev = p * a.o - 1, hard = a.id === 10 || a.id === 7;
        const conf = Math.round(100 * Math.max(0, 1 - Math.abs(pm - fair) / .2) * Math.min(1, L.n / 12) * (hard ? .6 : 1));
        if (!best[a.id] || ev > best[a.id].ev) best[a.id] = {
          fixture: f.fixture.id, league: name, leagueId: id, kickoff: f.fixture.date, home: f.teams.home.name, away: f.teams.away.name,
          mk: a.id, market: MK[a.id], sel: sel(a.id, a.k, f), odd: a.o, bookmaker: a.bk,
          implied: 1 / a.o, pAI: p, ev, conf, risk: p >= .5 ? 'Low' : p >= .3 ? 'Medium' : 'High', score: ev * conf / 100,
          why: `Expected goals ${L.lh.toFixed(2)}–${L.la.toFixed(2)}; model ${(pm * 100).toFixed(0)}% vs market ${(fair * 100).toFixed(0)}% (blended 65/35); form ${L.fh || '?'} / ${L.fa || '?'}; reported absences ${inj[f.teams.home.id] || 0}/${inj[f.teams.away.id] || 0}; sample ${L.n} games.`
        };
      }
      picks.push(...Object.values(best));
    }
  }
  picks.sort((a, b) => b.score - a.score);
  const seen = new Set(), shortlist = [];
  for (const p of picks) {
    if (shortlist.length < 5 && p.ev >= .05 && p.ev <= .5 && p.conf >= 40 && p.odd >= 1.4 && !seen.has(p.fixture)) { seen.add(p.fixture); shortlist.push(p); }
  }
  return { date, picks, shortlist, matches: fx.length, skipped, warnings: warn, generatedAt: new Date().toISOString() };
}

module.exports = async (req, res) => {
  if (!KEY) return res.status(500).json({ error: 'API_FOOTBALL_KEY is missing. In Vercel: Settings > Environment Variables, add it, then Redeploy.' });
  const q = String(req.query.date || '');
  const date = /^\d{4}-\d{2}-\d{2}$/.test(q) ? q : new Date().toLocaleDateString('en-CA', { timeZone: TZ });
  try {
    const d = await build(date);
    res.setHeader('Cache-Control', 'public, s-maxage=600');
    res.status(200).json(d);
  } catch (e) { res.status(502).json({ error: e.message }); }
};
