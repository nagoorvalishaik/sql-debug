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

function build(sql, keyCol, keyVals) {
  const U = unwrap(sql);
  if (U) { const r = build(U.sql, keyCol, keyVals); if (!r.error) r.warnings = U.warnings.concat(r.warnings); return r; }
  const P = parse(sql);
  if (P.error) return P;
  const { sc, base, joins, joinMap, conds, selCols } = P;
  const used = new Set(selCols.map(c => c.name)), uniq = n => { let k = n, i = 2; while (used.has(k)) k = `${n}_${i++}`; used.add(k); return k; };

  const groups = new Map(), items = [];
  conds.forEach(c => {
    if (!c.S.length) { items.push({ kind: 'base', cond: c }); return; }
    const sig = c.S.join(',');
    let g = groups.get(sig);
    if (!g) { g = { S: c.S, conds: [], aliases: c.S.map(k => joinMap.get(k).alias) }; groups.set(sig, g); items.push({ kind: 'row', group: g }); }
    items.push({ kind: 'jc', cond: c, group: g }); g.conds.push(c); g.last = items[items.length - 1];
  });
  [...groups.values()].filter(g => g.conds.length > 1).forEach(g => items.splice(items.indexOf(g.last) + 1, 0, { kind: 'all', group: g }));
  const covered = new Set([].concat(...[...groups.values()].map(g => g.S)));
  joins.filter(j => j.type === 'inner' && !covered.has(j.key)).reverse().forEach(j => items.unshift({ kind: 'row', group: { S: [j.key], conds: [], aliases: [j.alias] }, standalone: true }));

  const pad1 = '    ';
  const existsBlock = (S, cs) => {
    const list = joins.filter(j => S.includes(j.key)), p = pad1 + '    ';
    let s = 'CASE WHEN EXISTS (\n' + p + `SELECT 1 FROM ${list[0].table} ${list[0].alias}\n`;
    list.slice(1).forEach(j => { s += p + `JOIN ${j.table} ${j.alias}` + (j.on ? ` ON ${collapse(j.on)}` : '') + '\n'; });
    const w = []; if (list[0].on) w.push(collapse(list[0].on));
    cs.forEach(c => { const r = render(c.code, p + '      '); w.push(/\bOR\b/i.test(r) && !/^\(/.test(r) ? '(' + r + ')' : r); });
    if (w.length) s += p + 'WHERE ' + w.join('\n' + p + '  AND ') + '\n';
    return s + pad1 + ') THEN 1 ELSE 0 END';
  };

  const short = (t, max) => { if (t.length > max) { const cut = t.slice(0, max + 1); t = cut.lastIndexOf('_') > 4 ? cut.slice(0, cut.lastIndexOf('_')) : t.slice(0, max); } return t.replace(/_+$/, '') || 'cond'; };
  const shrink = t => t.replace(/_communication/g, '').replace(/_acknowledgement/g, '').replace(/_address/g, '').replace(/_not_null/g, '_nn').replace(/_not_blank/g, '_nb').replace(/^not_in_/, 'excl_').replace(/^users_with_/, '').replace(/^(exclude|excluding|excludng)_/, 'excl_').replace(/device_/g, 'dev_').replace(/segment_/g, 'seg_').replace(/_policy/g, '');
  const lbl = t => { t = t.replace(/\s+/g, ' ').trim(); return t.length > 55 ? t.slice(0, 52) + '...' : t; };
  let num = 0;
  const fname = base => { num++; return uniq('f' + String(num).padStart(2, '0') + '_' + short(shrink(base), 18)); };
  const flags = items.map(it => {
    const g = it.group, al = g ? g.aliases.join('_') : '';
    const tableTxt = g ? g.S.map(k => { const j = joinMap.get(k); return `${j.alias} (${j.table})`; }).join(' + ') : `${base.alias} (${base.table})`;
    if (it.kind === 'base') {
      const c = it.cond, code = render(c.code, pad1 + '    ');
      return { name: fname(condName(sc, c)), expr: `CASE WHEN ${code} THEN 1 ELSE 0 END`, label: lbl(c.label || collapse(c.code)), src: collapse(c.code), table: tableTxt, required: true };
    }
    if (it.kind === 'row') return { name: fname(slug(al) + '_row'), expr: existsBlock(g.S, []), label: lbl(`No ${g.aliases.join(' + ')} row`), src: 'Row exists', table: tableTxt, required: !!it.standalone };
    if (it.kind === 'jc') {
      const c = it.cond, nm = c.label ? slug(c.label) : condName(sc, c);
      return { name: fname(nm), expr: existsBlock(g.S, [c]), label: lbl(c.label || `${g.aliases.join(' + ')}: ${collapse(c.code)}`), src: collapse(c.code), table: tableTxt, required: g.conds.length === 1 };
    }
    return { name: fname(slug(al) + '_all'), expr: existsBlock(g.S, g.conds), label: lbl(`${g.aliases.join(' + ')}: no row meets all conditions`), src: '', table: tableTxt, required: true };
  });

  const allPass = uniq('all_pass'), firstFailed = uniq('first_failed');
  let filter = '';
  const vals = (keyVals || '').split(',').map(v => v.trim()).filter(Boolean);
  const key = (keyCol || '').trim();
  if (vals.length && key) filter = `\nWHERE ${base.alias}.${key} ` + (vals.length === 1 ? `= ${sqlStr(vals[0])}` : `IN (${vals.map(sqlStr).join(', ')})`);

  const selectList = selCols.map(c => c.expr).concat(flags.map(f => `${f.expr} AS ${f.name}`));
  const inner = 'SELECT\n' + selectList.map(s => indent(s, pad1).replace(/^ {4}/, pad1)).join(',\n') + `\nFROM ${base.table} ${base.alias}` + filter;

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

  return { flagsSql: outer, countsSql: counts, flags, warnings: P.warnings, base, joins, conds, selCols, allPass, firstFailed, defaultKey: selCols.length ? selCols[0].name : '' };
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

  var tab = 'flags', result = null, keyTouched = false, timer = null;

  function currentSql() { return result && !result.error ? (tab === 'flags' ? result.flagsSql : result.countsSql) : ''; }

  function paint() {
    var notes = $('notes'), code = $('code');
    notes.innerHTML = '';
    if (!result || result.error) {
      code.innerHTML = '<div class="empty">The debug query appears here once your query can be read.</div>';
      if (result && result.error) notes.innerHTML = '<div class="note err">' + esc(result.error) + '</div>';
      $('flagRows').innerHTML = '<tr><td colspan="5" style="color:var(--muted)">No flags yet.</td></tr>';
      $('stats').innerHTML = ''; $('foot').innerHTML = '';
      return;
    }
    var lines = currentSql().split('\n'), rows = '';
    for (var i = 0; i < lines.length; i++) rows += '<tr><td class="ln">' + (i + 1) + '</td><td class="tx">' + (hl(lines[i]) || ' ') + '</td></tr>';
    code.innerHTML = '<table>' + rows + '</table>';

    result.warnings.forEach(function (w) { var d = document.createElement('div'); d.className = 'note'; d.textContent = w; notes.appendChild(d); });
    if (tab === 'counts') { var d = document.createElement('div'); d.className = 'note info'; d.textContent = 'Returns a single row: how many people fail each flag, and how many pass everything. Run it in Query Studio to see where your audience drops off.'; notes.appendChild(d); }

    var req = result.flags.filter(function (f) { return f.required; }).length;
    var excl = result.conds.filter(function (c) { return /^\s*NOT\s+EXISTS|\bNOT\s+IN\s*\(\s*SELECT/i.test(c.code); }).length;
    $('stats').innerHTML = [['flags', result.flags.length], ['required', req], ['joined tables', result.joins.length], ['exclusions', excl]]
      .map(function (s) { return '<span class="stat"><b>' + s[1] + '</b>' + s[0] + '</span>'; }).join('');

    var html = '', lastTable = null;
    result.flags.forEach(function (f, i) {
      if (f.table !== lastTable) { html += '<tr class="group"><td colspan="5">' + esc(f.table) + '</td></tr>'; lastTable = f.table; }
      var showSrc = f.src && f.src !== 'Row exists' && f.src !== f.label && f.label.indexOf(f.src) < 0;
      html += '<tr><td class="num">' + (i + 1) + '</td><td><code>' + esc(f.name) + '</code></td><td class="chk">' + esc(f.label) +
        (showSrc ? '<span class="src">' + esc(f.src.length > 200 ? f.src.slice(0, 200) + '...' : f.src) + '</span>' : '') +
        '</td><td class="tblname">' + esc(f.table.split(' (')[0]) + '</td><td>' + (f.required ? '<span class="chip req">Required</span>' : '<span class="chip det">Detail</span>') + '</td></tr>';
    });
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
    result = r; paint();
  }
  function soon() { clearTimeout(timer); timer = setTimeout(run, 200); }

  $('src').value = '';
  $('src').addEventListener('input', soon);
  $('keyVal').addEventListener('input', soon);
  $('keyCol').addEventListener('input', function () { keyTouched = true; soon(); });
  $('clearBtn').addEventListener('click', function () { $('src').value = ''; $('keyVal').value = ''; $('keyCol').value = ''; keyTouched = false; run(); $('src').focus(); });
  function setTab(t) { tab = t; $('tabFlags').setAttribute('aria-selected', t === 'flags'); $('tabCounts').setAttribute('aria-selected', t === 'counts'); paint(); }
  $('tabFlags').addEventListener('click', function () { setTab('flags'); });
  $('tabCounts').addEventListener('click', function () { setTab('counts'); });

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
