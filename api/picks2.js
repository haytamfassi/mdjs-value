const FD = 'https://api.football-data.org/v4', OD = 'https://api.the-odds-api.com/v4';
const FDK = process.env.FOOTBALL_DATA_KEY, OK = process.env.ODDS_API_KEY, TZ = 'Africa/Casablanca';
const LEAGUES = (process.env.LEAGUE_CODES || 'PL,PD,SA,BL1,FL1,CL').split(',').map(s => s.trim());
const MAX_ODDS = +process.env.MAX_ODDS || 15;
const SPORT = { PL: 'soccer_epl', PD: 'soccer_spain_la_liga', SA: 'soccer_italy_serie_a', BL1: 'soccer_germany_bundesliga', FL1: 'soccer_france_ligue_one', CL: 'soccer_uefa_champs_league', DED: 'soccer_netherlands_eredivisie', PPL: 'soccer_portugal_primeira_liga' };
async function get(url, headers) {
  const r = await fetch(url, { headers });
  if (!r.ok) { let m = ''; try { m = (await r.json()).message; } catch (e) {} throw new Error('HTTP ' + r.status + (m ? ': ' + m : '')); }
  return r.json();
}
const moDate = iso => new Date(iso).toLocaleDateString('en-CA', { timeZone: TZ });
const norm = s => s.toLowerCase().normalize('NFD').replace(/[\u0300-\u036f]/g, '').replace(/\b(fc|cf|afc|sc|ac|as|ss|us|rc|real|club|de|sv|vfb|vfl|fsv|ssc|and)\b/g, '').replace(/[^a-z0-9]/g, '');
const sameTeam = (a, b) => { a = norm(a); b = norm(b); return a.length > 2 && b.length > 2 && (a === b || a.includes(b) || b.includes(a)); };
const conv = ev => ev.bookmakers.map(b => ({ name: b.title, bets: b.markets.map(mk =>
  mk.key === 'h2h' ? { id: 1, values: mk.outcomes.map(o => ({ value: o.name === ev.home_team ? 'Home' : o.name === ev.away_team ? 'Away' : 'Draw', odd: o.price })) }
  : mk.key === 'totals' ? { id: 5, values: mk.outcomes.filter(o => o.point === 2.5).map(o => ({ value: o.name + ' 2.5', odd: o.price })) } : null).filter(Boolean) }));

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
  const d2 = new Date(Date.parse(date + 'T00:00:00Z') + 864e5).toISOString().slice(0, 10), H = { 'X-Auth-Token': FDK };
  const ms = (await get(`${FD}/matches?dateFrom=${date}&dateTo=${d2}`, H)).matches
    .filter(m => ['TIMED', 'SCHEDULED'].includes(m.status) && LEAGUES.includes(m.competition.code) && moDate(m.utcDate) === date);
  const byC = {}; ms.forEach(m => (byC[m.competition.code] ||= []).push(m));
  const picks = []; let skipped = 0;
  for (const [code, g] of Object.entries(byC)) {
    const name = g[0].competition.name;
    const [st, od] = await Promise.all([
      safe(get(`${FD}/competitions/${code}/standings`, H), name + ' standings'),
      SPORT[code] ? safe(get(`${OD}/sports/${SPORT[code]}/odds?apiKey=${OK}&regions=eu&markets=h2h,totals&oddsFormat=decimal`), name + ' odds') : null]);
    const T = t => st?.standings?.find(s => s.type === t)?.table || [];
    if (!T('HOME').length || !od) { skipped += g.length; continue; }
    const by = {};
    T('HOME').forEach(r => by[r.team.id] = { form: (T('TOTAL').find(x => x.team.id === r.team.id)?.form || '').replace(/,/g, ''), home: { played: r.playedGames, goals: { for: r.goalsFor, against: r.goalsAgainst } } });
    T('AWAY').forEach(r => { if (by[r.team.id]) by[r.team.id].away = { played: r.playedGames, goals: { for: r.goalsFor, against: r.goalsAgainst } }; });
    Object.keys(by).forEach(k => { if (!by[k].away) delete by[k]; });
    const rows = Object.values(by), sum = f => rows.reduce((a, r) => a + f(r), 0);
    const S = { lgH: sum(r => r.home.goals.for) / sum(r => r.home.played), lgA: sum(r => r.away.goals.for) / sum(r => r.away.played), by };
    for (const m of g) {
      const ev = od.find(e => Math.abs(Date.parse(e.commence_time) - Date.parse(m.utcDate)) < 18e5 && (sameTeam(e.home_team, m.homeTeam.name) || sameTeam(e.away_team, m.awayTeam.name)));
      const L = ev && lambdas(S, m.homeTeam.id, m.awayTeam.id, {});
      if (!L) { skipped++; continue; }
      const M = model(L.lh, L.la), agg = {}, best = {};
      for (const bm of conv(ev)) for (const bet of bm.bets) {
        const vals = bet.values.map(v => ({ k: v.value, o: parseFloat(v.odd) })).filter(v => M[bet.id][v.k] !== undefined && v.o > 1);
        const tot = vals.reduce((a, v) => a + 1 / v.o, 0);
        for (const v of vals) {
          const a = agg[bet.id + '|' + v.k] ||= { id: bet.id, k: v.k, o: 0, bk: '', fair: [] };
          a.fair.push(1 / v.o / tot);
          if (v.o > a.o) { a.o = v.o; a.bk = bm.name; }
        }
      }
      const f = { teams: { home: m.homeTeam, away: m.awayTeam } };
      for (const a of Object.values(agg)) {
        const pm = M[a.id][a.k], fair = a.fair.reduce((x, y) => x + y, 0) / a.fair.length, p = .65 * pm + .35 * fair;
        if (a.o > MAX_ODDS || p < .15) continue;
        const ev2 = p * a.o - 1, conf = Math.round(100 * Math.max(0, 1 - Math.abs(pm - fair) / .2) * Math.min(1, L.n / 12));
        if (!best[a.id] || ev2 > best[a.id].ev) best[a.id] = {
          fixture: m.id, league: name, leagueId: code, kickoff: m.utcDate, home: m.homeTeam.name, away: m.awayTeam.name,
          mk: a.id, market: MK[a.id], sel: sel(a.id, a.k, f), odd: a.o, bookmaker: a.bk,
          implied: 1 / a.o, pAI: p, ev: ev2, conf, risk: p >= .5 ? 'Low' : p >= .3 ? 'Medium' : 'High', score: ev2 * conf / 100,
          why: `Expected goals ${L.lh.toFixed(2)}–${L.la.toFixed(2)}; model ${(pm * 100).toFixed(0)}% vs market ${(fair * 100).toFixed(0)}% (blended 65/35); form ${L.fh || '?'} / ${L.fa || '?'}; injuries and lineups not used; sample ${L.n} games.`
        };
      }
      picks.push(...Object.values(best));
    }
  }
  picks.sort((a, b) => b.score - a.score);
  const seen = new Set(), shortlist = [];
  for (const p of picks) if (shortlist.length < 5 && p.ev >= .05 && p.ev <= .5 && p.conf >= 40 && p.odd >= 1.4 && !seen.has(p.fixture)) { seen.add(p.fixture); shortlist.push(p); }
  return { date, picks, shortlist, matches: ms.length, skipped, warnings: warn, generatedAt: new Date().toISOString() };
}

module.exports = async (req, res) => {
  if (!FDK || !OK) return res.status(500).json({ error: 'Missing keys. In Vercel > Settings > Environment Variables add FOOTBALL_DATA_KEY and ODDS_API_KEY, then Redeploy.' });
  const q = String(req.query.date || '');
  const date = /^\d{4}-\d{2}-\d{2}$/.test(q) ? q : moDate(new Date());
  try {
    const d = await build(date);
    res.setHeader('Cache-Control', 'public, s-maxage=21600');
    res.status(200).json(d);
  } catch (e) { res.status(502).json({ error: e.message }); }
};
