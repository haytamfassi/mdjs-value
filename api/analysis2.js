const FD = 'https://api.football-data.org/v4', OD = 'https://api.the-odds-api.com/v4';
const FDK = process.env.FOOTBALL_DATA_KEY, OK = process.env.ODDS_API_KEY, TZ = 'Etc/GMT-1';
const LEAGUES = (process.env.LEAGUE_CODES || 'PL,PD,SA,BL1,BSA').split(',').map(s => s.trim());
const MAX_ODDS = +process.env.MAX_ODDS || 15;
const SPORT = { PL: 'soccer_epl', PD: 'soccer_spain_la_liga', SA: 'soccer_italy_serie_a', BL1: 'soccer_germany_bundesliga', FL1: 'soccer_france_ligue_one', CL: 'soccer_uefa_champs_league', DED: 'soccer_netherlands_eredivisie', PPL: 'soccer_portugal_primeira_liga', ELC: 'soccer_efl_champ', BSA: 'soccer_brazil_campeonato' };
async function get(url, headers, retry = 1) {
  const r = await fetch(url, { headers });
  if (r.status === 429 && retry) { await new Promise(z => setTimeout(z, 8000)); return get(url, headers, 0); }
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
  const picks = [], sums = []; let skipped = 0;
  for (const [code, g] of Object.entries(byC)) {
    const name = g[0].competition.name;
    const [st, od] = await Promise.all([
      safe(get(`${FD}/competitions/${code}/standings`, H), name + ' standings'),
      SPORT[code] ? safe(get(`${OD}/sports/${SPORT[code]}/odds?apiKey=${OK}&regions=eu&markets=h2h,totals&oddsFormat=decimal`), name + ' odds') : null]);
    const T = t => st?.standings?.find(s => s.type === t)?.table || [];
    const TT = T('TOTAL'), ha = T('HOME').length && T('AWAY').length;
    if (!ha && !TT.length) { warn.push(name + ': no standings data'); skipped += g.length; continue; }
    if (!od) { warn.push(name + ': no odds data'); skipped += g.length; continue; }
    const by = {}, st1 = r => ({ played: r.playedGames, goals: { for: r.goalsFor, against: r.goalsAgainst } });
    if (ha) {
      T('HOME').forEach(r => by[r.team.id] = { form: (TT.find(x => x.team.id === r.team.id)?.form || '').replace(/,/g, ''), home: st1(r) });
      T('AWAY').forEach(r => { if (by[r.team.id]) by[r.team.id].away = st1(r); });
      Object.keys(by).forEach(k => { if (!by[k].away) delete by[k]; });
    } else TT.forEach(r => by[r.team.id] = { form: (r.form || '').replace(/,/g, ''), home: st1(r), away: st1(r) });
    const rows = Object.values(by), sum = f => rows.reduce((a, r) => a + f(r), 0);
    const S = { lgH: sum(r => r.home.goals.for) / sum(r => r.home.played), lgA: sum(r => r.away.goals.for) / sum(r => r.away.played), by };
    for (const m of g) {
      const lbl = name + ': ' + m.homeTeam.name + ' v ' + m.awayTeam.name + ': ';
      const ev = od.find(e => Math.abs(Date.parse(e.commence_time) - Date.parse(m.utcDate)) < 108e5 && (sameTeam(e.home_team, m.homeTeam.name) || sameTeam(e.away_team, m.awayTeam.name)));
      if (!ev) { warn.push(lbl + 'no odds event matched (' + od.length + ' events listed)'); skipped++; continue; }
      if (!ev.bookmakers.length) { warn.push(lbl + 'no bookmaker odds yet'); skipped++; continue; }
      const L = lambdas(S, m.homeTeam.id, m.awayTeam.id, {});
      if (!L) { warn.push(lbl + 'team stats missing or under 4 games'); skipped++; continue; }
      const M = model(L.lh, L.la), agg = {}, best = {};
      const topArr = Object.entries(M[10]).sort((a, b) => b[1] - a[1]).slice(0, 3).map(([k, v]) => [k.replace(':', '-'), v]);
      const top = Object.entries(M[10]).sort((a, b) => b[1] - a[1]).slice(0, 3).map(([k, v]) => k.replace(':', '-') + ' (' + (v * 100).toFixed(0) + '%)').join(', ');
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
        const pm = M[a.id][a.k], fair = a.fair.reduce((x, y) => x + y, 0) / a.fair.length, p = .4 * pm + .6 * fair;
        if (a.o > MAX_ODDS || p < .15) continue;
        const ev2 = p * a.o - 1, conf = Math.round(100 * Math.max(0, 1 - Math.abs(pm - fair) / .2) * Math.min(1, L.n / 12));
        if (!best[a.id] || ev2 > best[a.id].ev) best[a.id] = {
          fixture: m.id, league: name, leagueId: code, kickoff: m.utcDate, home: m.homeTeam.name, away: m.awayTeam.name,
          mk: a.id, market: MK[a.id], sel: sel(a.id, a.k, f), odd: a.o, bookmaker: a.bk,
          implied: 1 / a.o, pAI: p, ev: ev2, conf, risk: p >= .5 ? 'Low' : p >= .3 ? 'Medium' : 'High', score: ev2 * conf / 100,
          why: `Expected goals ${L.lh.toFixed(2)}–${L.la.toFixed(2)}; model ${(pm * 100).toFixed(0)}% vs market ${(fair * 100).toFixed(0)}% (blended 40/60); form ${L.fh || '?'} / ${L.fa || '?'}; injuries and lineups not used; sample ${L.n} games; likely scores: ${top} (no exact-score odds available, so no value calc).`
        };
      }
      const fm_ = k => { const a = agg[k]; return a ? a.fair.reduce((x, y) => x + y, 0) / a.fair.length : null; };
      const od_ = k => agg[k] ? agg[k].o : null;
      sums.push({ league: name, kickoff: m.utcDate, home: m.homeTeam.name, away: m.awayTeam.name, xg: [L.lh, L.la], form: [L.fh, L.fa], scores: top, sc: topArr,
        rows: [['Home', M[1].Home, fm_('1|Home'), od_('1|Home')], ['Draw', M[1].Draw, fm_('1|Draw'), od_('1|Draw')], ['Away', M[1].Away, fm_('1|Away'), od_('1|Away')], ['Over 2.5', M[5]['Over 2.5'], fm_('5|Over 2.5'), od_('5|Over 2.5')], ['Under 2.5', M[5]['Under 2.5'], fm_('5|Under 2.5'), od_('5|Under 2.5')]],
        best: Object.values(best).sort((a, b) => b.ev - a.ev)[0] || null });
      picks.push(...Object.values(best));
    }
  }
  picks.sort((a, b) => b.score - a.score);
  const seen = new Set(), shortlist = [];
  for (const p of picks) if (shortlist.length < 5 && p.ev >= .05 && p.ev <= .3 && p.conf >= 45 && p.odd >= 1.4 && !seen.has(p.fixture)) { seen.add(p.fixture); shortlist.push(p); }
  return { date, picks, sums, shortlist, matches: ms.length, skipped, warnings: warn, generatedAt: new Date().toISOString() };
}

const esc = x => String(x).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
const hm = iso => new Date(iso).toLocaleTimeString('en-GB', { timeZone: TZ, hour: '2-digit', minute: '2-digit' });
const pc = x => x == null ? '-' : (x * 100).toFixed(0) + '%';
const IN = '<input class="o" inputmode="decimal" placeholder="odds">';
function page(d, date, err) {
  const groups = {};
  ((d && d.sums) || []).sort((a, b) => a.kickoff.localeCompare(b.kickoff)).forEach(x => (groups[x.league] ||= []).push(x));
  let body = '';
  for (const [lg, arr] of Object.entries(groups)) {
    body += `<h2>${esc(lg)} <span class="c">${arr.length} match${arr.length > 1 ? 'es' : ''}</span></h2>`;
    for (const x of arr) {
      const rows = x.rows.map(([n, pm, mk, od]) => { const p = mk == null ? pm : .4 * pm + .6 * mk, ev = !od ? null : p * od - 1; return `<tr data-p="${p}"><td>${n}</td><td>${pc(pm)}</td><td>${pc(mk)}</td><td>${od ? od.toFixed(2) : '-'}</td><td class="${ev > 0 ? 'pos' : 'neg'}">${ev == null ? '-' : (ev * 100).toFixed(0) + '%'}</td><td>${IN}</td><td class="x"></td></tr>`; }).join('');
      const sc = x.sc.map(([k, v]) => `<tr data-p="${v}"><td>${k}</td><td>${pc(v)}</td><td>${IN}</td><td class="x"></td></tr>`).join('');
      const fav = x.rows.slice(0, 3).sort((a, b) => b[1] - a[1])[0], b = x.best;
      const favName = fav[0] === 'Home' ? x.home : fav[0] === 'Away' ? x.away : 'Draw';
      body += `<div class="m"><b>${esc(x.home)} vs ${esc(x.away)}</b><div class="s">${hm(x.kickoff)} (Morocco, UTC+1) · expected goals ${x.xg[0].toFixed(2)}-${x.xg[1].toFixed(2)}</div><div class="s">Model favourite: ${esc(favName)} (${pc(fav[1])})</div><div class="w"><table><tr><th></th><th>Model</th><th>Market</th><th>Odds</th><th>EV</th><th>MDJS odds</th><th>EV MDJS</th></tr>${rows}</table></div><div class="s">Likely exact scores (model only, type the MDJS odds to get EV):</div><div class="w"><table><tr><th>Score</th><th>Model</th><th>MDJS odds</th><th>EV MDJS</th></tr>${sc}</table></div><div>${b && b.ev > 0 ? `Best value: <b>${esc(b.sel)} @ ${b.odd.toFixed(2)}</b> · EV ${(b.ev * 100).toFixed(0)}% · ${b.risk} risk · conf ${b.conf}%` : 'No value found on this match.'}</div></div>`;
    }
  }
  const sl = d && d.shortlist && d.shortlist.length ? '<h2>Top value picks</h2>' + d.shortlist.map(p => `<div class="m"><b>${esc(p.sel)} @ ${p.odd.toFixed(2)}</b><div class="s">${esc(p.home)} vs ${esc(p.away)} · ${hm(p.kickoff)} · ${esc(p.league)}</div><div>AI ${pc(p.pAI)} vs implied ${pc(p.implied)} · <span class="pos">EV ${(p.ev * 100).toFixed(0)}%</span> · ${p.risk} risk · conf ${p.conf}%</div></div>`).join('') : '';
  const info = err ? `<div class="e">${esc(err)}</div>` : d ? `<div class="s">${d.matches} matches found, ${d.matches - d.skipped} analysed, ${d.skipped} skipped.${d.warnings.length ? ' ' + esc(d.warnings.join(' | ')) : ''}</div>` : '';
  return `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>MDJS analysis</title><style>
:root{--bg:#f6f7f4;--card:#fff;--ink:#17201b;--mute:#5d6b62;--line:#dde3dc;--pos:#0b6b3a;--neg:#b3261e}
@media(prefers-color-scheme:dark){:root{--bg:#0f1511;--card:#18211b;--ink:#e8efe9;--mute:#9bab9f;--line:#2a372e;--pos:#4cc27f;--neg:#ff8a80}}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.5 Georgia,serif;padding:12px;max-width:760px;margin:auto}h1{font-size:1.4rem}h2{font-size:1.1rem;margin:22px 0 8px;border-bottom:2px solid var(--line);padding-bottom:4px}
.c,.s{color:var(--mute);font-size:.85rem}.m{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:10px;margin-bottom:10px}.w{overflow-x:auto}table{border-collapse:collapse;width:100%;font-size:.85rem;margin:6px 0}th,td{text-align:left;padding:3px 6px;border-bottom:1px solid var(--line);white-space:nowrap}.pos{color:var(--pos)}.neg{color:var(--neg)}.e{border:1px solid var(--neg);color:var(--neg);padding:10px;border-radius:6px}a{color:var(--pos)}input,button{font:inherit;padding:6px}.o{width:64px;padding:3px}</style></head><body>
<h1>MDJS analysis by league</h1><div class="s">Probabilities are model estimates, not guarantees. Market odds come from bookmakers via The Odds API, not MDJS: type your MDJS odds in the boxes to get the EV. Model = 40% own estimate + 60% market. Times are Morocco (UTC+1; during Ramadan they would be one hour later).</div>
<form method="get" style="margin:10px 0"><input type="date" name="date" value="${date}"> <button>Go</button></form>${info}${sl}${body || (err ? '' : '<p>No matches found for this date in your leagues.</p>')}
<script>document.addEventListener('input',function(e){var i=e.target;if(i.className!=='o')return;var tr=i.closest('tr'),p=+tr.dataset.p,o=parseFloat(i.value.replace(',','.')),c=tr.querySelector('.x');if(!(o>1)){c.textContent='';return}var ev=p*o-1;c.textContent=(ev*100).toFixed(0)+'%';c.className='x '+(ev>0?'pos':'neg')})</script></body></html>`;
}

module.exports = async (req, res) => {
  const q = String(req.query.date || '');
  const date = /^\d{4}-\d{2}-\d{2}$/.test(q) ? q : moDate(new Date());
  res.setHeader('Content-Type', 'text/html; charset=utf-8');
  if (!FDK || !OK) return res.status(500).send(page(null, date, 'Missing keys: add FOOTBALL_DATA_KEY and ODDS_API_KEY in Vercel, then Redeploy.'));
  try { const d = await build(date); res.setHeader('Cache-Control', 'public, s-maxage=21600'); res.status(200).send(page(d, date)); }
  catch (e) { res.status(502).send(page(null, date, e.message)); }
};
