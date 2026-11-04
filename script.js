/* ---------- scanning ---------- */
function scan(s) {
  const n = s.length, masked = new Array(n), clean = new Array(n), depth = new Int16Array(n), comments = [];
  let d = 0, i = 0;
  const fill = (a, b, ch) => { for (let k = a; k < b; k++) { masked[k] = ch; clean[k] = ch === ' ' ? (s[k] === '\n' ? '\n' : ' ') : s[k]; depth[k] = d; } };
  while (i < n) {
    const c = s[i], c2 = s[i + 1];
    if (c === '-' && c2 === '-') {
      let j = s.indexOf('\n', i); if (j < 0) j = n;
      comments.push({ start: i, end: j, text: s.slice(i + 2, j).trim() });
      fill(i, j, ' '); i = j; continue;
    }
    if (c === '/' && c2 === '*') {
      let j = s.indexOf('*/', i + 2); const inner = j < 0 ? n : j; j = j < 0 ? n : j + 2;
      comments.push({ start: i, end: j, text: s.slice(i + 2, inner).replace(/\s+/g, ' ').trim() });
      fill(i, j, ' '); i = j; continue;
    }
    if (c === "'" || c === '[' || c === '"') {
      let j = i + 1;
      if (c === "'") { while (j < n) { if (s[j] === "'") { if (s[j + 1] === "'") { j += 2; continue; } break; } j++; } }
      else { const close = c === '[' ? ']' : '"'; while (j < n && s[j] !== close) j++; }
      j = Math.min(j + 1, n);
      for (let k = i; k < j; k++) { masked[k] = (k === i || k === j - 1) ? s[k] : 'x'; clean[k] = s[k]; depth[k] = d; }
      i = j; continue;
    }
    if (c === '(') { depth[i] = d; d++; masked[i] = clean[i] = c; i++; continue; }
    if (c === ')') { d = Math.max(0, d - 1); depth[i] = d; masked[i] = clean[i] = c; i++; continue; }
    masked[i] = clean[i] = c; depth[i] = d; i++;
  }
  return { src: s, masked: masked.join(''), clean: clean.join(''), depth, comments };
}

function findTop(sc, re, a, b) {
  const out = []; re.lastIndex = a; let m;
  while ((m = re.exec(sc.masked))) {
    if (m.index >= b) break;
    if (sc.depth[m.index] === 0) out.push({ index: m.index, end: m.index + m[0].length, text: m[0] });
    if (m[0].length === 0) re.lastIndex++;
  }
  return out;
}

const ID = '(?:\\[x*\\]|"x*"|[A-Za-z_#@][\\w#@$]*)';
const NOT_ALIAS = new Set(['where', 'on', 'join', 'left', 'right', 'inner', 'outer', 'full', 'cross', 'group', 'order', 'having', 'union', 'with', 'as', 'and', 'or', 'select', 'from', 'when', 'then']);
const norm = id => id.replace(/^[\["]|[\]"]$/g, '').toLowerCase();
const collapse = code => code.replace(/('(?:[^']|'')*')|\s+/g, (m, str) => str ? str : ' ').trim();

function refsIn(sc, a, b) {
  const M = sc.masked.slice(a, b), O = sc.src.slice(a, b);
  const refs = new Set(), defined = new Set();
  let re = new RegExp(`(${ID})\\s*\\.\\s*(?=[\\["A-Za-z_*])`, 'g'), m;
  while ((m = re.exec(M))) {
    const prev = M[m.index - 1];
    if (prev && /[\w.\]$#@]/.test(prev)) continue;
    refs.add(norm(O.substr(m.index, m[1].length)));
  }
  re = new RegExp(`\\b(?:FROM|JOIN)\\s+${ID}(?:\\s*\\.\\s*${ID})*(?:\\s+AS)?\\s+(${ID})`, 'gi');
  while ((m = re.exec(M))) {
    const st = m.index + m[0].length - m[1].length;
    const al = norm(O.substr(st, m[1].length));
    if (!NOT_ALIAS.has(al)) defined.add(al);
  }
  return { refs, defined };
}

function parseTA(text) {
  let t = text.replace(/\bWITH\s*\([^)]*\)/gi, ' ').trim();
  if (!t) return null;
  if (t[0] === '(') {
    let d = 0, i = 0;
    for (; i < t.length; i++) { if (t[i] === '(') d++; else if (t[i] === ')') { d--; if (d === 0) break; } }
    const rest = t.slice(i + 1).trim().replace(/^AS\s+/i, '');
    return rest ? { table: t.slice(0, i + 1), alias: rest } : null;
  }
  const PART = '(?:\\[[^\\]]*\\]|"[^"]*"|[\\w#@$]+)';
  const m = t.match(new RegExp(`^(${PART}(?:\\s*\\.\\s*${PART})*)(?:\\s+(?:AS\\s+)?(${PART}))?$`, 'i'));
  if (!m) return null;
  const table = m[1].replace(/\s*\.\s*/g, '.');
  const alias = m[2] || table.split('.').pop();
  return { table, alias };
}

/* ---------- parse ---------- */
function parse(sql) {
  const sc = scan(sql), M = sc.masked, n = sql.length, warnings = [];
  if (!sql.trim()) return { error: 'Paste a query on the left to get started.' };
  if (/^\s*WITH\b/i.test(M)) return { error: 'Queries that start with WITH (a CTE) are not supported. Paste the main SELECT on its own.' };
  const sel = findTop(sc, /\bSELECT\b/gi, 0, n)[0];
  if (!sel) return { error: 'Could not find a SELECT in the query.' };
  if (findTop(sc, /\bUNION\b/gi, 0, n).length) return { error: 'UNION queries are not supported. Paste one SELECT at a time.' };
  const from = findTop(sc, /\bFROM\b/gi, sel.end, n)[0];
  if (!from) return { error: 'Could not find the FROM clause.' };
  const where = findTop(sc, /\bWHERE\b/gi, from.end, n)[0];
  const tail = findTop(sc, /\b(?:GROUP\s+BY|HAVING|ORDER\s+BY|OPTION)\b/gi, where ? where.end : from.end, n)[0];
  const fromEnd = where ? where.index : (tail ? tail.index : n);
  const whereEnd = tail ? tail.index : n;
  if (tail) warnings.push(`The ${tail.text.replace(/\s+/g, ' ').toUpperCase()} part was left out of the debug query.`);
  if (findTop(sc, /\bAPPLY\b/gi, from.end, fromEnd).length) return { error: 'CROSS APPLY / OUTER APPLY is not supported.' };
  if (findTop(sc, /,/g, from.end, fromEnd).length) return { error: 'Comma-separated tables in FROM are not supported. Rewrite them as JOIN ... ON.' };

  const jms = findTop(sc, /\b(?:(?:LEFT|RIGHT|FULL)(?:\s+OUTER)?\s+|INNER\s+|CROSS\s+)?JOIN\b/gi, from.end, fromEnd);
  const base = parseTA(sc.clean.slice(from.end, jms.length ? jms[0].index : fromEnd));
  if (!base) return { error: 'Could not read the table after FROM.' };
  base.key = norm(base.alias);
  const joins = [];
  for (let i = 0; i < jms.length; i++) {
    const jm = jms[i], a = jm.end, b = i + 1 < jms.length ? jms[i + 1].index : fromEnd;
    const on = findTop(sc, /\bON\b/gi, a, b)[0];
    const ta = parseTA(sc.clean.slice(a, on ? on.index : b));
    if (!ta) return { error: `Could not read the table in "${collapse(sc.clean.slice(jm.index, b)).slice(0, 80)}".` };
    const type = /^\s*(LEFT|RIGHT|FULL)/i.test(jm.text) ? 'outer' : (/CROSS/i.test(jm.text) ? 'cross' : 'inner');
    const j = { ...ta, key: norm(ta.alias), type, on: on ? sc.clean.slice(on.end, b).trim() : '' };
    j.onRefs = on ? refsIn(sc, on.end, b).refs : new Set();
    joins.push(j);
  }
  const joinMap = new Map(joins.map(j => [j.key, j]));

  // SELECT columns that belong to the base table
  const selCols = [], outCols = [];
  let ss = sel.end, pieces = [];
  for (let i = sel.end; i <= from.index; i++) {
    if (i === from.index || (M[i] === ',' && sc.depth[i] === 0)) { pieces.push(sc.clean.slice(ss, i)); ss = i + 1; }
  }
  const PART = '(?:\\[[^\\]]*\\]|"[^"]*"|[\\w#@$]+)';
  pieces.forEach((p, idx) => {
    let t = p.trim();
    if (idx === 0) t = t.replace(/^DISTINCT\s+/i, '').replace(/^TOP\s*\(?\s*\d+\s*\)?\s*(PERCENT\s+)?/i, '').replace(/^DISTINCT\s+/i, '');
    const m = t.match(new RegExp(`^(${PART})\\s*\\.\\s*(${PART})(?:\\s+(?:AS\\s+)?(${PART}))?$`, 'i'));
    if (m && norm(m[1]) === base.key && m[2] !== '*') { if (!selCols.some(c => c.name === norm(m[3] || m[2]))) selCols.push({ expr: `${m[1]}.${m[2]}${m[3] ? ' AS ' + m[3] : ''}`, name: norm(m[3] || m[2]), out: m[3] || m[2], col: m[2] }); }
    else { const a = t.match(/(?:\bAS\s*|\s)(\[[^\]]*\]|[\w#@$]+)\s*$/i); if (a) outCols.push(norm(a[1])); }
  });

  // WHERE conditions
  const conds = [];
  if (where) {
    const ranges = [];
    if (findTop(sc, /\bOR\b/gi, where.end, whereEnd).length) {
      warnings.push('The WHERE clause has an OR at the top level, so it is checked as one single condition. Wrap OR groups in brackets to get separate flags.');
      ranges.push([where.end, whereEnd]);
    } else {
      let segStart = where.end, between = 0;
      findTop(sc, /\b(?:AND|BETWEEN)\b/gi, where.end, whereEnd).forEach(m => {
        if (/^BETWEEN$/i.test(m.text)) { between++; return; }
        if (between > 0) { between--; return; }
        ranges.push([segStart, m.index]); segStart = m.end;
      });
      ranges.push([segStart, whereEnd]);
    }
    let carry = [];
    ranges.forEach(([a, b]) => {
      const txt = sc.clean.slice(a, b), lead = txt.search(/\S/);
      const cs = sc.comments.filter(c => c.start >= a && c.start < b);
      if (lead < 0) { carry = carry.concat(cs.map(c => c.text)); return; }
      const cStart = a + lead, cEnd = a + txt.replace(/\s+$/, '').length;
      const labels = carry; carry = [];
      cs.forEach(c => {
        if (c.start < cStart) labels.push(c.text);
        else if (c.start >= cEnd) { if (!sql.slice(cEnd, c.start).includes('\n')) labels.push(c.text); else carry.push(c.text); }
      });
      const { refs, defined } = refsIn(sc, cStart, cEnd);
      const used = [...refs].filter(r => joinMap.has(r) && !defined.has(r));
      conds.push({ a: cStart, b: cEnd, code: sc.clean.slice(cStart, cEnd), label: labels.filter(Boolean).join(' / ') || null, used });
    });
  }
  // closure over join ON references
  conds.forEach(c => {
    const S = new Set(c.used); let grew = true;
    while (grew) { grew = false; for (const k of [...S]) for (const r of joinMap.get(k).onRefs) if (joinMap.has(r) && !S.has(r)) { S.add(r); grew = true; } }
    c.S = joins.filter(j => S.has(j.key)).map(j => j.key);
    c.S.forEach(k => { const j = joinMap.get(k); if (j.type === 'outer' && !j._warned) { j._warned = true; warnings.push(`${j.alias} is a LEFT/RIGHT/FULL JOIN but the WHERE clause filters on it, so it is checked like an inner join.`); } });
  });
  if (!selCols.length) warnings.push(`No plain ${base.alias}.column found in the SELECT list, so the debug query returns only the flags. Add ${base.alias}.your_key_column to your SELECT to see which record each row is.`);
  return { sc, base, joins, joinMap, conds, selCols, outCols, warnings };
}

/* ---------- naming ---------- */
function slug(s) { return s.toLowerCase().replace(/[^a-z0-9]+/g, '_').replace(/^_+|_+$/g, '').slice(0, 50) || 'condition'; }
function condName(sc, c) {
  if (c.label) return slug(c.label);
  const M = sc.masked.slice(c.a, c.b), O = sc.src.slice(c.a, c.b);
  if (/^\s*(NOT\s+)?EXISTS\b/i.test(M)) {
    const t = M.match(new RegExp(`\\bFROM\\s+(${ID}(?:\\s*\\.\\s*${ID})*)`, 'i'));
    let tbl = t ? O.substr(t.index + t[0].length - t[1].length, t[1].length) : 'subquery';
    tbl = tbl.split('.').pop().replace(/[\[\]"]/g, '');
    return slug((/^\s*NOT/i.test(M) ? 'not_in_' : 'in_') + tbl);
  }
  const sub = M.match(/\b(NOT\s+)?IN\s*\(\s*SELECT\b/i);
  if (sub) {
    const t = M.match(new RegExp(`\\bFROM\\s+(${ID}(?:\\s*\\.\\s*${ID})*)`, 'i'));
    let tbl = t ? O.substr(t.index + t[0].length - t[1].length, t[1].length) : 'subquery';
    tbl = tbl.split('.').pop().replace(/[\[\]"]/g, '').replace(/_organic_\w+$/i, '').replace(/_target$/i, '');
    return slug((sub[1] ? 'not_in_' : 'in_') + tbl);
  }
  const cols = [], re = new RegExp(`${ID}\\s*\\.\\s*(${ID})`, 'g'); let m;
  while ((m = re.exec(M))) { const col = norm(O.substr(m.index + m[0].length - m[1].length, m[1].length)); if (!cols.includes(col)) cols.push(col); }
  if (!cols.length) cols.push(((M.match(/[A-Za-z_][\w]*/) || ['condition'])[0]).toLowerCase());
  if (/\bOR\b/i.test(M)) return slug(cols.slice(0, 2).join('_or_'));
  let suf = '';
  if (/\bIS\s+NOT\s+NULL\b/i.test(M)) suf = '_not_null';
  else if (/\bIS\s+NULL\b/i.test(M)) suf = '_is_null';
  else if (/\bNOT\s+IN\b/i.test(M)) suf = '_not_in';
  else if (/\bNOT\s+LIKE\b/i.test(M)) suf = '_not_like';
  else if (/\bLIKE\b/i.test(M)) suf = '_like';
  else if (/(!=|<>)\s*''/.test(M)) suf = '_not_blank';
  else if (/!=|<>/.test(M)) suf = '_not_equal';
  return slug(cols[0] + suf);
}

/* ---------- rendering SQL ---------- */
function render(code, pad) {
  const lines = code.replace(/\t/g, '    ').split('\n').map(l => l.replace(/\s+$/, '')).filter(l => l.trim() !== '');
  if (lines.length <= 1) return collapse(code);
  const rest = lines.slice(1), min = Math.min(...rest.map(l => l.match(/^ */)[0].length));
  return lines[0].trim() + '\n' + rest.map(l => pad + l.slice(min)).join('\n');
}
const indent = (s, pad) => s.split('\n').map(l => l ? pad + l : l).join('\n');
const sqlStr = s => { let t = s.replace(/\s+/g, ' ').trim(); if (t.length > 120) t = t.slice(0, 117) + '...'; return "'" + t.replace(/'/g, "''") + "'"; };

/* ---------- LEFT JOIN rewriting: no subqueries in the SELECT list ---------- */
function splitAnd(code) {
  const sc = scan(code), n = code.length;
  if (findTop(sc, /\bOR\b/gi, 0, n).length) return [code.trim()];
  const parts = []; let st = 0, between = 0;
  findTop(sc, /\b(?:AND|BETWEEN)\b/gi, 0, n).forEach(m => {
    if (/^BETWEEN$/i.test(m.text)) { between++; return; }
    if (between > 0) { between--; return; }
    parts.push(sc.clean.slice(st, m.index)); st = m.end;
  });
  parts.push(sc.clean.slice(st));
  return parts.map(p => p.trim()).filter(Boolean);
}
function aliasRefs(code) {
  const sc = scan(code), out = [];
  const re = new RegExp(`(${ID})\\s*\\.\\s*(${ID})`, 'g'); let m;
  while ((m = re.exec(sc.masked))) {
    const prev = sc.masked[m.index - 1];
    if (prev && /[\w.\]$#@]/.test(prev)) continue;
    out.push({ start: m.index, end: m.index + m[0].length, alias: norm(code.substr(m.index, m[1].length)), col: code.substr(m.index + m[0].length - m[2].length, m[2].length) });
  }
  return out;
}
function isExclusion(code) {
  const sc = scan(code), M = sc.masked;
  const m = M.match(new RegExp(`^\\s*(?:NOT\\s+EXISTS\\s*\\(|${ID}(?:\\s*\\.\\s*${ID})*\\s+NOT\\s+IN\\s*\\(\\s*SELECT\\b)`, 'i'));
  if (!m) return false;
  const p = M.indexOf('(', 0 + m[0].search(/\(/));
  let q = p + 1; while (q < M.length && !(M[q] === ')' && sc.depth[q] === sc.depth[p])) q++;
  return q < M.length && !M.slice(q + 1).trim();
}
function wrapOr(s) { return /\bOR\b/i.test(s) && !/^\(/.test(s.trim()) ? '(' + s + ')' : s; }
function makeDerived(ctx, fromSql, inner, condList, kExpr, X) {
  const name = ctx.next(), where = [], on = [], cols = new Map();
  condList.forEach(c => {
    const refs = aliasRefs(c);
    if (!refs.some(r => !inner.has(r.alias))) { where.push(c); return; }
    let s = c;
    refs.filter(r => inner.has(r.alias)).sort((a, b) => b.start - a.start).forEach(r => {
      const key = r.alias + '.' + norm(r.col);
      if (!cols.has(key)) cols.set(key, { expr: c.slice(r.start, r.end).replace(/\s+/g, ''), name: 'c' + (cols.size + 1) });
      s = s.slice(0, r.start) + name + '.' + cols.get(key).name + s.slice(r.end);
    });
    on.push(collapse(s));
  });
  const sel = ['1 AS m'];
  if (kExpr) { sel.push(`${collapse(kExpr)} AS k`); on.unshift(`${name}.k = ${X}`); }
  cols.forEach(v => {
    const dup = kExpr && norm(v.expr) === norm(collapse(kExpr).replace(/\s+/g, ''));
    const i = on.findIndex(o => o.replace(/\s+/g, '').toLowerCase() === `${name}.${v.name}=${X}`.toLowerCase() || o.replace(/\s+/g, '').toLowerCase() === `${X}=${name}.${v.name}`.toLowerCase());
    if (dup && i > 0) { on.splice(i, 1); return; }
    sel.push(`${v.expr} AS ${v.name}`);
  });
  if (!on.length) on.push('1 = 1');
  on.forEach(o => { if (!/^[\w.\[\]]+\s*=\s*[\w.\[\]]+$/.test(o) && o !== '1 = 1' && !ctx.warnedOn) { ctx.warnedOn = true; ctx.warnings.push('One of the lookups links to the main table with something other than a plain "column = column" match, so a person could appear on more than one row. Check the counts if they look too high.'); } });
  ctx.derived.push({ name, sel, from: fromSql, where, on });
  return name;
}
function renderDerived(d) {
  let s = `LEFT JOIN (\n    SELECT DISTINCT ${d.sel.join(', ')}\n    FROM ${d.from}`;
  if (d.where.length) s += '\n    WHERE ' + d.where.map(w => wrapOr(render(w, '          '))).join('\n      AND ');
  return s + `\n) ${d.name} ON ` + d.on.map(wrapOr).join(' AND ');
}
function parseSub(text) {
  const sc = scan(text), n = text.length;
  const sel = findTop(sc, /\bSELECT\b/gi, 0, n)[0]; if (!sel) return null;
  if (findTop(sc, /\b(?:GROUP\s+BY|HAVING|UNION|ORDER\s+BY|EXCEPT|INTERSECT)\b/gi, 0, n).length) return null;
  const from = findTop(sc, /\bFROM\b/gi, sel.end, n)[0]; if (!from) return null;
  const where = findTop(sc, /\bWHERE\b/gi, from.end, n)[0], fEnd = where ? where.index : n;
  const selExpr = sc.clean.slice(sel.end, from.index).trim().replace(/^DISTINCT\s+/i, '').replace(/^TOP\s*\(?\s*\d+\s*\)?\s*(PERCENT\s+)?/i, '').replace(/^DISTINCT\s+/i, '').replace(/\s+AS\s+\S+$/i, '');
  const inner = new Set(refsIn(sc, from.index, fEnd).defined);
  const tre = new RegExp(`\\b(?:FROM|JOIN)\\s+(${ID}(?:\\s*\\.\\s*${ID})*)`, 'gi'); let m;
  while ((m = tre.exec(sc.masked.slice(0, fEnd)))) { const t = text.substr(m.index + m[0].length - m[1].length, m[1].length); inner.add(norm(t.split('.').pop().trim())); }
  return { sel: selExpr, from: collapse(sc.clean.slice(from.end, fEnd)), inner, conds: where ? splitAnd(sc.clean.slice(where.end)) : [] };
}
function rewriteSubqueries(ctx, code) {
  const sc = scan(code), M = sc.masked, reps = [];
  const re = /\b(NOT\s+)?EXISTS\s*\(|\b(NOT\s+)?IN\s*\(\s*SELECT\b/gi; let m;
  while ((m = re.exec(M))) {
    const p = M.indexOf('(', m.index);
    let q = p + 1; while (q < M.length && !(M[q] === ')' && sc.depth[q] === sc.depth[p])) q++;
    if (q >= M.length) continue;
    const isIn = !/EXISTS/i.test(m[0]), neg = !!(isIn ? m[2] : m[1]);
    let a = m.index, X = null;
    if (isIn) {
      const xm = M.slice(0, m.index).match(new RegExp(`(${ID}(?:\\s*\\.\\s*${ID})*)\\s*$`));
      if (!xm) { ctx.warnings.push('Could not read the column before an IN (SELECT ...), so that check was left as it is.'); continue; }
      a = m.index - xm[0].length; X = code.slice(a, a + xm[1].length).replace(/\s+/g, '');
    }
    const sub = parseSub(sc.clean.slice(p + 1, q));
    if (!sub) { ctx.warnings.push('A subquery with GROUP BY, HAVING, ORDER BY or UNION was left as it is. Query Studio may reject it.'); re.lastIndex = q + 1; continue; }
    const name = makeDerived(ctx, sub.from, sub.inner, sub.conds, isIn ? sub.sel : null, X);
    reps.push({ a, b: q + 1, text: `${name}.m IS ${neg ? '' : 'NOT '}NULL` });
    re.lastIndex = q + 1;
  }
  let out = code;
  reps.sort((x, y) => y.a - x.a).forEach(r => { out = out.slice(0, r.a) + r.text + out.slice(r.b); });
  return { code: out, changed: reps.length > 0 };
}

function waterfallSql(res) {
  if (!res.wfFlags.length) return '';
  const parts = res.wfFlags.map(f => '        ' + f.expr);
  return 'SELECT\n    y.combo,\n    COUNT(*) AS n\nFROM (\n    SELECT\n        CONCAT(\'c\',\n' + parts.join(',\n') + '\n        ) AS combo\n    ' +
    res.wfFrom.split('\n').join('\n    ') + '\n) y\nGROUP BY y.combo';
}
function qsCheck(sql) {
  const sc = scan(sql), M = sc.masked, issues = [], seen = {};
  const lineOf = i => sql.slice(0, i).split('\n').length;
  const add = (i, kind, text) => { if (seen[kind + lineOf(i)]) return; seen[kind + lineOf(i)] = 1; issues.push({ line: lineOf(i), text }); };
  let m; const cw = /\bCASE\s+WHEN\b/gi;
  while ((m = cw.exec(M))) {
    const d = sc.depth[m.index], th = /\bTHEN\b/gi; th.lastIndex = m.index; let t;
    while ((t = th.exec(M)) && sc.depth[t.index] !== d) {}
    const seg = M.slice(m.index, t ? t.index : M.length), e = seg.search(/\bEXISTS\s*\(|\bIN\s*\(\s*SELECT\b/i);
    if (e >= 0) add(m.index + e, 'sub', 'A subquery (EXISTS or IN (SELECT ...)) inside CASE WHEN. Query Studio rejects subqueries in the SELECT list.');
  }
  const star = /\*/g;
  while ((m = star.exec(M))) {
    const i = m.index, before = M.slice(0, i).replace(/\s+$/, ''), after = M.slice(i + 1).replace(/^\s+/, '');
    if (before.endsWith('(') && after.startsWith(')')) continue;
    if (/\.$/.test(before)) add(i, 'all', 'alias.* used. Query Studio needs every column listed by name.');
    else if (/\b(SELECT|DISTINCT)$/i.test(before)) add(i, 'sel', 'SELECT * used. List the columns by name.');
    else add(i, 'mul', 'Multiplication (*). Query Studio rejects it here. Use CASE WHEN ... AND ... THEN 1 ELSE 0 END instead.');
  }
  const as = /\bAS\s+([\w#@$]+)/gi;
  while ((m = as.exec(M))) if (m[1].length > 60) add(m.index, 'len', `Column name ${m[1].slice(0, 30)}... is longer than 60 characters.`);
  return issues;
}

function parseCombos(txt, k) {
  const map = {}, re = new RegExp('c([01]{' + k + '})(?![01])[\\s,;|"\':=\\t]*(\\d+)', 'g');
  let m, rows = 0;
  while ((m = re.exec(txt))) { map[m[1]] = (map[m[1]] || 0) + Number(m[2]); rows++; }
  if (!rows) {
    const other = txt.match(/c([01]{2,})/);
    return { error: other ? `These combos have ${other[1].length} digits, but this query has ${k} steps. Paste the result of the waterfall query for the query shown on the left.` : 'No result rows found. Paste the rows from the waterfall query: each has a combo like c1101 and a count n.' };
  }
  return { combos: Object.keys(map).map(b => ({ b, n: map[b] })), rows };
}

function unwrap(sql) {
  const P0 = parse(sql);
  if (P0.error || P0.joins.length || !/^\(/.test(P0.base.table)) return null;
  const pos = P0.sc.clean.indexOf(P0.base.table);
  const inner = pos >= 0 ? sql.slice(pos + 1, pos + P0.base.table.length - 1) : P0.base.table.slice(1, -1);
  const P1 = parse(inner);
  if (P1.error) return null;
  const warnings = [`Your query wraps a subquery (${P0.base.alias}), so the flags check the conditions inside it.`];
  const reAlias = new RegExp('(^|[^\\w.\\]])' + P0.base.alias.replace(/[\[\]]/g, '') + '\\s*\\.\\s*(\\[[^\\]]*\\]|[\\w#@$]+)', 'gi');
  let extra = '';
  P0.conds.forEach(c => {
    const label = collapse(c.code);
    const bare = P1.outCols.filter(n => new RegExp('(^|[^\\w.])' + n + '\\b', 'i').test(c.code.replace(/'(?:[^']|'')*'/g, '')));
    if (bare.length) { warnings.push(`Skipped "${label.slice(0, 50)}": ${bare.join(', ')} is calculated inside the subquery (e.g. ROW_NUMBER keeps one row per person), so it does not remove people.`); return; }
    let ok = true;
    const code = c.code.replace(reAlias, (m, pre, col) => {
      const sc = P1.selCols.find(x => x.name === norm(col));
      if (!sc) { ok = false; return m; }
      return pre + P1.base.alias + '.' + sc.col;
    });
    if (!ok) { warnings.push(`Skipped "${label.slice(0, 50)}": it uses a column that is not a plain ${P1.base.alias}.column inside the subquery.`); return; }
    extra += '\n' + (c.label ? '/* ' + c.label.replace(/\*\//g, '') + ' */\n' : '') + 'AND ' + code;
  });
  const hasWhere = /\bWHERE\b/i.test(P1.sc.masked) && P1.conds.length;
  const sqlOut = inner.replace(/\s+$/, '') + (extra ? (hasWhere ? extra : '\nWHERE 1 = 1' + extra) : '');
  return { sql: sqlOut, warnings };
}

function build(sql, keyCol, keyVals, detail) {
  const U = unwrap(sql);
  if (U) { const r = build(U.sql, keyCol, keyVals, detail); if (!r.error) r.warnings = U.warnings.concat(r.warnings); return r; }
  const P = parse(sql);
  if (P.error) return P;
  const { sc, base, joins, joinMap, conds, selCols } = P;
  const used = new Set(selCols.map(c => c.name)), uniq = n => { let k = n, i = 2; while (used.has(k)) k = `${n}_${i++}`; used.add(k); return k; };

  const groups = new Map(), items = [], filters = [];
  conds.forEach(c => {
    if (!c.S.length && isExclusion(c.code)) { filters.push(c); return; }
    if (!c.S.length) { items.push({ kind: 'base', cond: c }); return; }
    const sig = c.S.join(',');
    let g = groups.get(sig);
    if (!g) { g = { S: c.S, conds: [], aliases: c.S.map(k => joinMap.get(k).alias) }; groups.set(sig, g); items.push({ kind: 'row', group: g }); }
    items.push({ kind: 'jc', cond: c, group: g }); g.conds.push(c); g.last = items[items.length - 1];
  });
  [...groups.values()].filter(g => g.conds.length > 1).forEach(g => items.splice(items.indexOf(g.last) + 1, 0, { kind: 'all', group: g }));
  if (detail === false) for (let i = items.length - 1; i >= 0; i--) { const it = items[i]; if ((it.kind === 'row' && !it.standalone) || (it.kind === 'jc' && it.group.conds.length > 1)) items.splice(i, 1); }
  const covered = new Set([].concat(...[...groups.values()].map(g => g.S)));
  joins.filter(j => j.type === 'inner' && !covered.has(j.key)).reverse().forEach(j => items.unshift({ kind: 'row', group: { S: [j.key], conds: [], aliases: [j.alias] }, standalone: true }));

  const pad1 = '    ';
  const taken = new Set([base.key].concat(joins.map(j => j.key)));
  let jn = 0;
  const ctx = { derived: [], warnings: [], next: () => { let n; do { n = 'lk' + String(++jn).padStart(2, '0'); } while (taken.has(n)); return n; } };
  const groupJoin = (S, cs) => {
    const list = joins.filter(j => S.includes(j.key));
    let from = `${list[0].table} ${list[0].alias}`;
    list.slice(1).forEach(j => { from += ` JOIN ${j.table} ${j.alias}` + (j.on ? ` ON ${collapse(j.on)}` : ''); });
    const condList = (list[0].on ? splitAnd(list[0].on) : []).concat(cs.map(c => c.code.trim()));
    const name = makeDerived(ctx, from, new Set(S), condList, null, null);
    return `CASE WHEN ${name}.m IS NOT NULL THEN 1 ELSE 0 END`;
  };

  const short = (t, max) => { if (t.length > max) { const cut = t.slice(0, max + 1); t = cut.lastIndexOf('_') > 4 ? cut.slice(0, cut.lastIndexOf('_')) : t.slice(0, max); } return t.replace(/_+$/, '') || 'cond'; };
  const shrink = t => t.replace(/_communication/g, '').replace(/_acknowledgement/g, '').replace(/_address/g, '').replace(/_not_null/g, '_nn').replace(/_not_blank/g, '_nb').replace(/^not_in_/, 'excl_').replace(/^users_with_/, '').replace(/^(exclude|excluding|excludng)_/, 'excl_').replace(/device_/g, 'dev_').replace(/segment_/g, 'seg_').replace(/_policy/g, '');
  const lbl = t => t.replace(/\s+/g, ' ').trim();
  let num = 0;
  const fname = base => { num++; return uniq('f' + String(num).padStart(2, '0') + '_' + short(shrink(base), 18)); };
  const flags = items.map(it => { const d0 = ctx.derived.length; const f = (() => {
    const g = it.group, al = g ? g.aliases.join('_') : '';
    const tableTxt = g ? g.S.map(k => { const j = joinMap.get(k); return `${j.alias} (${j.table})`; }).join(' + ') : `${base.alias} (${base.table})`;
    if (it.kind === 'base') {
      const c = it.cond, rw = rewriteSubqueries(ctx, c.code), code = rw.changed ? collapse(rw.code) : render(c.code, pad1 + '    ');
      return { name: fname(condName(sc, c)), expr: `CASE WHEN ${code} THEN 1 ELSE 0 END`, label: lbl(c.label || collapse(c.code)), src: collapse(c.code), table: tableTxt, required: true };
    }
    if (it.kind === 'row') return { name: fname(slug(al) + '_row'), expr: groupJoin(g.S, []), label: lbl(`Has a ${g.aliases.join(' + ')} row`), src: 'Row exists', table: tableTxt, required: !!it.standalone };
    if (it.kind === 'jc') {
      const c = it.cond, nm = c.label ? slug(c.label) : condName(sc, c);
      return { name: fname(nm), expr: groupJoin(g.S, [c]), label: lbl(c.label || `${g.aliases.join(' + ')}: ${collapse(c.code)}`), src: collapse(c.code), table: tableTxt, required: g.conds.length === 1 };
    }
    return { name: fname(slug(al) + '_all'), expr: groupJoin(g.S, g.conds), label: lbl(`${g.aliases.join(' + ')}: has a row meeting all its conditions`), src: '', table: tableTxt, required: true };
  })(); f.code = `${f.expr} AS ${f.name}` + ctx.derived.slice(d0).map(d => '\n' + renderDerived(d)).join(''); return f; });

  const allPass = uniq('all_pass'), firstFailed = uniq('first_failed');
  let filter = '';
  const vals = (keyVals || '').split(',').map(v => v.trim()).filter(Boolean);
  const key = (keyCol || '').trim();
  const keyCond = vals.length && key ? `${base.alias}.${key} ` + (vals.length === 1 ? `= ${sqlStr(vals[0])}` : `IN (${vals.map(sqlStr).join(', ')})`) : null;
  const whereParts = filters.map(c => render(c.code, '      '));
  if (keyCond) whereParts.push(keyCond);
  if (whereParts.length) filter = '\nWHERE ' + whereParts.join('\n  AND ');

  const selectList = selCols.map(c => c.expr).concat(flags.map(f => `${f.expr} AS ${f.name}`));
  const inner = 'SELECT\n' + selectList.map(s => indent(s, pad1).replace(/^ {4}/, pad1)).join(',\n') + `\nFROM ${base.table} ${base.alias}` + ctx.derived.map(d => '\n' + renderDerived(d)).join('') + filter;

  const req = flags.filter(f => f.required);
  const passExpr = req.length ? 'CASE WHEN ' + req.map(f => `x.${f.name} = 1`).join('\n          AND ') + ' THEN 1 ELSE 0 END' : '1';
  const failCase = 'CASE\n' + flags.map(f => `        WHEN x.${f.name} = 0 THEN ${sqlStr(f.name)}`).join('\n') + "\n        ELSE 'PASS'\n    END";
  const outerCols = selCols.map(c => `    x.${c.out}`).concat(flags.map(f => `    x.${f.name}`), [`    ${passExpr} AS ${allPass}`, `    ${flags.length ? failCase : "'PASS'"} AS ${firstFailed}`]);
  const outer = `SELECT\n${outerCols.join(',\n')}\nFROM (\n${indent(inner, pad1)}\n) x`;

  const failNames = new Set();
  const counts = 'SELECT\n    COUNT(*) AS total_records,\n' + flags.map(f => {
    let n = 'fail_' + f.name.replace(/^f_/, ''), k = n, i = 2; while (failNames.has(k)) k = `${n}_${i++}`; failNames.add(k);
    return `    SUM(CASE WHEN x.${f.name} = 0 THEN 1 ELSE 0 END) AS ${k},`;
  }).join('\n') + `\n    SUM(${req.length ? passExpr.replace(/\n {10}/g, '\n              ') : '1'}) AS records_passing_all\nFROM (\n${indent(inner, pad1)}\n) x`;

  /* Waterfall: required flags plus every exclusion as a step (exclusions become lookups here only) */
  const exFlags = filters.map((c, i) => {
    const rw = rewriteSubqueries(ctx, c.code);
    const nm = uniq('e' + String(i + 1).padStart(2, '0') + '_' + short(shrink(c.label ? slug(c.label) : condName(sc, c)), 18));
    return { name: nm, expr: `CASE WHEN ${rw.changed ? collapse(rw.code) : render(c.code, pad1 + '    ')} THEN 1 ELSE 0 END`, label: lbl(c.label || collapse(c.code)) };
  });
  const wfFlags = req.concat(exFlags);
  const wfDerived = ctx.derived.filter(d => wfFlags.some(f => f.expr.indexOf(d.name + '.') >= 0));
  const wfFrom = `FROM ${base.table} ${base.alias}` + wfDerived.map(d => '\n' + renderDerived(d)).join('') + (keyCond ? '\nWHERE ' + keyCond : '');
  const wfSteps = req.map(f => ({ id: f.name, label: f.label, kind: 'include' })).concat(exFlags.map(f => ({ id: f.name, label: f.label, kind: 'exclude' })));

  return { flagsSql: outer, countsSql: counts, wfFrom, wfFlags, wfSteps, baseTable: base.table, flags, filters: filters.map(c => ({ label: lbl(c.label || collapse(c.code)), src: collapse(c.code), code: 'AND ' + render(c.code, '    ') })), warnings: P.warnings.concat(ctx.warnings), base, joins, conds, selCols, allPass, firstFailed, defaultKey: selCols.length ? selCols[0].name : '' };
}



(function () {
  function $(id) { return document.getElementById(id); }
  function esc(s) { return String(s).replace(/[&<>"]/g, function (c) { return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]; }); }
  var KWS = 'SELECT|FROM|WHERE|AND|OR|NOT|EXISTS|CASE|WHEN|THEN|ELSE|END|AS|IN|IS|NULL|JOIN|LEFT|RIGHT|INNER|OUTER|ON|SUM|COUNT|LIKE|BETWEEN|DISTINCT|TOP|CONVERT|CAST|DATEADD|GETDATE|CONCAT|ISNULL|COALESCE|DATE|YEAR';
  function hl(line) {
    var re = new RegExp("('(?:[^']|'')*'?)|(/\\*.*?\\*/)|\\b(f\\d\\d_\\w+|all_pass|first_failed)\\b|\\b(" + KWS + ")\\b|\\b(\\d+(?:\\.\\d+)?)\\b", 'gi');
    var out = '', last = 0, m;
    while ((m = re.exec(line))) {
      out += esc(line.slice(last, m.index));
      if (m[1]) out += '<span class="s">' + esc(m[1]) + '</span>';
      else if (m[2]) out += '<span class="c">' + esc(m[2]) + '</span>';
      else if (m[3]) out += '<span class="f">' + esc(m[3]) + '</span>';
      else if (m[4]) out += '<span class="k">' + esc(m[4]) + '</span>';
      else out += '<span class="n">' + m[5] + '</span>';
      last = re.lastIndex;
    }
    return out + esc(line.slice(last));
  }

  function sqlBlock(code) {
    return '<details class="sqlblock"><summary>Show SQL</summary><pre>' + code.split('\n').map(function (l) { return hl(l); }).join('\n') + '</pre></details>';
  }

  var tab = 'flags', result = null, keyTouched = false, timer = null;

  var wfOrder = [], wfData = null, wfMsg = '', wfOff = {};
  function currentSql() { return result && !result.error ? (tab === 'flags' ? result.flagsSql : tab === 'counts' ? result.countsSql : waterfallSql(result)) : ''; }
  function countWhere(idx) {
    var t = 0;
    wfData.combos.forEach(function (c) { for (var i = 0; i < idx.length; i++) if (c.b.charAt(idx[i]) !== '1') return; t += c.n; });
    return t;
  }
  function wfNumbers() {
    if (!wfData) return null;
    var pos = {}; result.wfSteps.forEach(function (s, i) { pos[s.id] = i; });
    var active = wfOrder.filter(function (id) { return !wfOff[id]; }).map(function (id) { return pos[id]; });
    var out = [countWhere([])];
    for (var j = 0; j < active.length; j++) out.push(countWhere(active.slice(0, j + 1)));
    return out;
  }
  function activeCount() { return wfOrder.filter(function (id) { return !wfOff[id]; }).length; }
  function offCount() { return wfOrder.length - activeCount(); }

  function fmt(n) { return Number(n).toLocaleString('en-US'); }
  function pct(a, b) { return b ? (a / b * 100).toFixed(1).replace(/\.0$/, '') + '%' : '0%'; }

  function renderWf() {
    var box = $('wf');
    box.hidden = tab !== 'wf' || !result || !!result.error;
    if (box.hidden) return;
    var steps = wfOrder.map(function (id) { return result.wfSteps.filter(function (s) { return s.id === id; })[0]; });
    var n = wfNumbers(), total = n ? n[0] : 0, worst = -1, worstDrop = -1;
    if (n) for (var i = 1; i < n.length; i++) if (n[i - 1] - n[i] > worstDrop) { worstDrop = n[i - 1] - n[i]; worst = i; }
    function bar(rem, prev) {
      if (!n) return '<div class="wf-track wf-empty"></div>';
      var w = total ? rem / total * 100 : 0, d = total ? (prev - rem) / total * 100 : 0;
      return '<div class="wf-track"><span class="wf-keep" style="width:' + w + '%"></span>' + (d > 0 ? '<span class="wf-drop" style="left:' + w + '%;width:' + d + '%"></span>' : '') + '</div>';
    }
    var html = '<div class="wf-row wf-start"><div class="wf-move"></div><div class="wf-lbl"><b>Everyone in ' + esc(result.baseTable) + '</b></div>' + bar(total, total) +
      '<div class="wf-num wf-rm"></div><div class="wf-num wf-left"><b>' + (n ? fmt(total) : '-') + '</b>' + (n ? '<small>100%</small>' : '') + '</div></div>';
    var k = 0, shown = 0;
    steps.forEach(function (s, i) {
      var off = !!wfOff[s.id], isWorst = false, rem = 0, prev = 0;
      if (!off) { k++; if (n) { rem = n[k]; prev = n[k - 1]; isWorst = worst === k && worstDrop > 0; } }
      var drop = prev - rem;
      html += '<div class="wf-row' + (isWorst ? ' worst' : '') + (off ? ' off' : '') + '">' +
        '<div class="wf-move"><button class="mv" type="button" data-i="' + i + '" data-d="-1" aria-label="Move up"' + (i === 0 ? ' disabled' : '') + '>&#9650;</button>' +
        '<button class="mv" type="button" data-i="' + i + '" data-d="1" aria-label="Move down"' + (i === steps.length - 1 ? ' disabled' : '') + '>&#9660;</button></div>' +
        '<div class="wf-lbl"><div class="wf-line"><span class="wf-step">' + (off ? '&ndash;' : k) + '</span>' +
        '<span class="wf-text">' + esc(s.label) + '</span>' +
        '<button class="wf-tog" type="button" role="switch" data-id="' + esc(s.id) + '" aria-checked="' + (!off) + '" aria-label="Include this step" title="' + (off ? 'Switched off: this step is ignored' : 'Switch off to see the audience without this step') + '"><span class="knob"></span></button></div>' +
        '<div class="wf-meta"><span class="chip ' + (s.kind === 'include' ? 'req' : 'exc') + '">' + (s.kind === 'include' ? 'Keep if passes' : 'Exclusion') + '</span><code class="wf-id">' + esc(s.id) + '</code>' +
        (isWorst ? '<span class="wf-flag">Biggest drop</span>' : '') + '</div></div>' +
        (off ? '<div class="wf-track wf-empty"></div><div class="wf-num wf-rm"><small>Switched off</small></div><div class="wf-num wf-left"></div>' :
          bar(rem, prev) +
          '<div class="wf-num wf-rm">' + (n ? '<span class="neg">&minus;' + fmt(drop) + '</span><small>' + pct(drop, prev) + ' of previous</small>' : '-') + '</div>' +
          '<div class="wf-num wf-left">' + (n ? '<b>' + fmt(rem) + '</b><small>' + pct(rem, total) + ' of start</small>' : '-') + '</div>') + '</div>';
    });
    if (n) {
      var fin = n[n.length - 1], cmp = '';
      if (offCount()) { var base = countWhere(result.wfSteps.map(function (x, i) { return i; })), dlt = fin - base; cmp = '<small class="wf-cmp">' + (dlt >= 0 ? '+' : '&minus;') + fmt(Math.abs(dlt)) + ' vs all steps on (' + fmt(base) + ')</small>'; }
      html += '<div class="wf-row wf-end"><div class="wf-move"></div><div class="wf-lbl"><b>' + (offCount() ? 'What-if audience' : 'Final audience') + '</b>' +
        (offCount() ? '<div class="wf-meta"><small>' + offCount() + ' step' + (offCount() > 1 ? 's' : '') + ' switched off</small></div>' : '') + '</div>' + bar(fin, fin) +
        '<div class="wf-num wf-rm"><span class="neg">&minus;' + fmt(total - fin) + '</span><small>removed in total</small></div><div class="wf-num wf-left"><b>' + fmt(fin) + '</b><small>' + pct(fin, total) + ' of start</small>' + cmp + '</div></div>';
    }
    $('wfRows').innerHTML = html;
    renderExportBar();
    var msg = $('wfMsg');
    msg.textContent = wfMsg; msg.hidden = !wfMsg;
    msg.className = 'note' + (/^No result|different number/.test(wfMsg) ? '' : ' info');
  }

  function wfTable() {
    var n = wfNumbers(); if (!n) return null;
    var steps = wfOrder.filter(function (id) { return !wfOff[id]; }).map(function (id) { return result.wfSteps.filter(function (s) { return s.id === id; })[0]; });
    var clean = function (v) { return String(v).replace(/[\t\r\n]+/g, ' '); };
    var out = [['Step', 'Condition', 'Flag', 'Removed', '% of previous', 'Left', '% of start'].join('\t')];
    out.push(['0', 'Everyone in ' + result.baseTable, '', '', '', n[0], '100%'].map(clean).join('\t'));
    steps.forEach(function (s, i) { var prev = n[i], rem = n[i + 1]; out.push([i + 1, s.label, s.id, prev - rem, pct(prev - rem, prev), rem, pct(rem, n[0])].map(clean).join('\t')); });
    var fin = n[n.length - 1];
    out.push(['', 'Final audience', '', n[0] - fin, '', fin, pct(fin, n[0])].map(clean).join('\t'));
    return { text: out.join('\n'), fin: fin, start: n[0] };
  }
  function renderExportBar() {
    var x = wfTable(), bar = $('wfExport');
    bar.hidden = !x;
    if (!x) return;
    $('wfFinal').innerHTML = (wfOrder.some(function (id) { return wfOff[id]; }) ? 'What-if audience' : 'Final audience') + ' <b>' + fmt(x.fin) + '</b> <small>' + pct(x.fin, x.start) + ' of ' + fmt(x.start) + '</small>';
  }

  function renderCheck() {
    var el = $('qs');
    if (!result || result.error) { el.hidden = true; return; }
    var issues = qsCheck(currentSql());
    el.hidden = false;
    el.className = 'qs ' + (issues.length ? 'bad' : 'good');
    el.innerHTML = issues.length
      ? '<b>Query Studio check: ' + issues.length + ' possible problem' + (issues.length > 1 ? 's' : '') + '</b><ul>' + issues.map(function (x) { return '<li>Line ' + x.line + ': ' + esc(x.text) + '</li>'; }).join('') + '</ul>'
      : '<b>Query Studio check passed.</b> No subqueries in the SELECT list, no alias.*, and no multiplication.';
  }

  function paint() {
    var notes = $('notes'), code = $('code');
    notes.innerHTML = '';
    renderWf();
    if (!result || result.error) {
      code.innerHTML = '<div class="empty">The debug query appears here once your query can be read.</div>';
      if (result && result.error) notes.innerHTML = '<div class="note err">' + esc(result.error) + '</div>';
      $('flagRows').innerHTML = '<tr><td colspan="5" style="color:var(--muted)">No flags yet.</td></tr>';
      $('stats').innerHTML = ''; $('foot').innerHTML = '';
      renderCheck();
      return;
    }
    var lines = currentSql().split('\n'), rows = '';
    for (var i = 0; i < lines.length; i++) rows += '<tr><td class="ln">' + (i + 1) + '</td><td class="tx">' + (hl(lines[i]) || ' ') + '</td></tr>';
    code.innerHTML = '<table>' + rows + '</table>';
    renderCheck();

    result.warnings.forEach(function (w) { var d = document.createElement('div'); d.className = 'note'; d.textContent = w; notes.appendChild(d); });
    if (tab === 'wf') { var dw = document.createElement('div'); dw.className = 'note info'; dw.textContent = 'Run this once. Each result row is a combo (c followed by one digit per step: 1 = passes, 0 = fails, in the order of the steps listed below when nothing is reordered) and n, the number of people with that combo. Paste all the rows into the Waterfall panel below. After that you can reorder steps and switch them on or off without running it again.'; notes.appendChild(dw); }
    if (tab === 'counts') { var d = document.createElement('div'); d.className = 'note info'; d.textContent = 'Returns a single row: how many people fail each flag, and how many pass everything. Run it in Query Studio to see where your audience drops off.'; notes.appendChild(d); }

    var req = result.flags.filter(function (f) { return f.required; }).length;
    var excl = result.conds.filter(function (c) { return /^\s*NOT\s+EXISTS|\bNOT\s+IN\s*\(\s*SELECT/i.test(c.code); }).length;
    $('stats').innerHTML = [['flags', result.flags.length], ['required', req], ['joined tables', result.joins.length], ['exclusion filters', result.filters.length]]
      .map(function (s) { return '<span class="stat"><b>' + s[1] + '</b>' + s[0] + '</span>'; }).join('');

    var html = '', lastTable = null;
    result.flags.forEach(function (f, i) {
      if (f.table !== lastTable) { html += '<tr class="group"><td colspan="5">' + esc(f.table) + '</td></tr>'; lastTable = f.table; }
      html += '<tr><td class="num">' + (i + 1) + '</td><td><code>' + esc(f.name) + '</code></td><td class="chk">' + esc(f.label) + sqlBlock(f.code) +
        '</td><td class="tblname">' + esc(f.table.split(' (')[0]) + '</td><td>' + (f.required ? '<span class="chip req">Required</span>' : '<span class="chip det">Detail</span>') + '</td></tr>';
    });
    if (result.filters.length) {
      html += '<tr class="group"><td colspan="5">Exclusions: kept as filters in WHERE, no flag</td></tr>';
      result.filters.forEach(function (f) {
        html += '<tr><td class="num">-</td><td><span class="tblname">filter</span></td><td class="chk">' + esc(f.label) + sqlBlock(f.code) +
          '</td><td class="tblname"></td><td><span class="chip det">Filter</span></td></tr>';
      });
    }
    $('flagRows').innerHTML = html;

    var cols = result.selCols.map(function (c) { return c.out; });
    $('foot').innerHTML = '<div><b>Target data extension fields:</b> ' + (cols.length ? '<code>' + esc(cols.join(', ')) + '</code> as Text, ' : '') +
      '<code>' + esc(result.flags.map(function (f) { return f.name; }).concat([result.allPass]).join(', ')) + '</code> as Number, <code>' + esc(result.firstFailed) + '</code> as Text(60).</div>' +
      '<div><b>first_failed</b> shows the flag name of the first check (in the order above) that the person fails, or PASS. Look it up in this table.</div>';
  }

  function run() {
    var sql = $('src').value;
    if (!sql.trim()) { result = { error: 'Paste a query on the left to get started.' }; paint(); return; }
    var r = build(sql, $('keyCol').value, $('keyVal').value);
    if (!r.error && !keyTouched && r.defaultKey && $('keyCol').value !== r.defaultKey) {
      $('keyCol').value = r.defaultKey;
      r = build(sql, r.defaultKey, $('keyVal').value);
    }
    result = r;
    if (!r.error) {
      var ids = r.wfSteps.map(function (s) { return s.id; });
      var same = ids.length === wfOrder.length && ids.every(function (id) { return wfOrder.indexOf(id) >= 0; });
      if (!same) { wfOrder = ids; wfData = null; wfMsg = ''; wfOff = {}; $('wfPaste').value = ''; }
    }
    paint();
  }
  function soon() { clearTimeout(timer); timer = setTimeout(run, 200); }

  $('src').value = '';
  $('src').addEventListener('input', soon);
  $('keyVal').addEventListener('input', soon);
  $('keyCol').addEventListener('input', function () { keyTouched = true; soon(); });
  $('clearBtn').addEventListener('click', function () { $('src').value = ''; $('keyVal').value = ''; $('keyCol').value = ''; keyTouched = false; run(); $('src').focus(); });
  function setTab(t) { tab = t; $('tabFlags').setAttribute('aria-selected', t === 'flags'); $('tabCounts').setAttribute('aria-selected', t === 'counts'); $('tabWf').setAttribute('aria-selected', t === 'wf'); paint(); }
  $('tabFlags').addEventListener('click', function () { setTab('flags'); });
  $('tabCounts').addEventListener('click', function () { setTab('counts'); });
  $('tabWf').addEventListener('click', function () { setTab('wf'); });

  $('wfRows').addEventListener('click', function (e) {
    var tg = e.target.closest('button.wf-tog');
    if (tg) {
      var id = tg.getAttribute('data-id');
      wfOff[id] = !wfOff[id];
      renderWf();
      var t2 = document.querySelector('#wfRows button.wf-tog[data-id="' + id + '"]'); if (t2) t2.focus();
      return;
    }
    var b = e.target.closest('button.mv'); if (!b || b.disabled) return;
    var i = +b.getAttribute('data-i'), j = i + (+b.getAttribute('data-d'));
    var t = wfOrder[i]; wfOrder[i] = wfOrder[j]; wfOrder[j] = t;
    renderWf();
    var again = document.querySelector('#wfRows button.mv[data-i="' + j + '"][data-d="' + b.getAttribute('data-d') + '"]') || document.querySelector('#wfRows button.mv[data-i="' + j + '"]');
    if (again) again.focus();
  });
  $('wfPaste').addEventListener('input', function () {
    var txt = $('wfPaste').value;
    if (!txt.trim()) { wfData = null; wfMsg = ''; renderWf(); return; }
    var r = parseCombos(txt, result.wfSteps.length);
    if (r.error) { wfData = null; wfMsg = r.error; }
    else { wfData = r; wfMsg = 'Read ' + r.rows + ' result row' + (r.rows > 1 ? 's' : '') + ' (' + fmt(countWhereAll(r)) + ' people). Reorder or switch steps on and off: the numbers update without running the query again.'; }
    renderWf();
  });
  function countWhereAll(r) { return r.combos.reduce(function (t, c) { return t + c.n; }, 0); }
  $('wfCopyTable').addEventListener('click', function () {
    var x = wfTable(), btn = this; if (!x) return;
    function done(m) { btn.textContent = m; btn.classList.add('done'); setTimeout(function () { btn.textContent = 'Copy table'; btn.classList.remove('done'); }, 1600); }
    function fb() { var ta = document.createElement('textarea'); ta.value = x.text; ta.style.position = 'fixed'; ta.style.opacity = '0'; document.body.appendChild(ta); ta.select(); var ok = false; try { ok = document.execCommand('copy'); } catch (e) {} document.body.removeChild(ta); done(ok ? 'Copied' : 'Press Ctrl+C'); }
    if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(x.text).then(function () { done('Copied'); }, fb); else fb();
  });
  $('wfClear').addEventListener('click', function () { $('wfPaste').value = ''; wfData = null; wfMsg = ''; renderWf(); });

  $('copyBtn').addEventListener('click', function () {
    var txt = currentSql(), btn = $('copyBtn');
    if (!txt) return;
    function done(msg) { btn.textContent = msg; btn.classList.add('done'); setTimeout(function () { btn.textContent = 'Copy query'; btn.classList.remove('done'); }, 1800); }
    function fallback() {
      var ta = document.createElement('textarea'); ta.value = txt; ta.style.position = 'fixed'; ta.style.opacity = '0';
      document.body.appendChild(ta); ta.select();
      var ok = false; try { ok = document.execCommand('copy'); } catch (e) {}
      document.body.removeChild(ta);
      done(ok ? 'Copied' : 'Press Ctrl+C');
    }
    if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(txt).then(function () { done('Copied'); }, fallback);
    else fallback();
  });
  run();
})();
