// Common Thread — LCS dynamic programming engine + interactive UI.
// The algorithms here mirror public/py/lcs_core.py (same recurrence and tie-break rule),
// so the instant browser results and the Python/Biopython results always agree.

const $ = (s) => document.querySelector(s);
const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
const nt = (ch) => `<span class="nt-${ch}">${ch}</span>`;
const pct = (x) => (x == null ? "—" : `${(x * 100).toFixed(1)}%`);
const fmt = (x) => (x == null ? "—" : x.toLocaleString());

const DIAG = 1, UP = 2, LEFT = 3;
const ARROW = { [DIAG]: "↖", [UP]: "↑", [LEFT]: "←" };

const SAMPLES = {
  short: { a: "AGGTCAT", b: "GTTCAGT" },
  mutation: { a: "GATTACAGATTACA", b: "GATCACAGATTTACA" },
  clrs: { a: "ACCGGTCGAGTGCGCGGAAGCCGGCCGAA", b: "GTCGTTCGGAATGCCGTTGCTCTGTAAA" },
  globin: { a: "ATGGTGCATCTGACTCCTGAGGAGAAGTCT", b: "ATGGTGCACCTGACTGATGCTGAGAAGTCT" },
};

// ---------------------------------------------------------------- input
function cleanSequence(raw) {
  const body = raw.split(/\r?\n/).map((l) => l.trim()).filter((l) => l && !l.startsWith(">")).join("");
  const up = body.toUpperCase().replace(/\s+/g, "");
  const kept = up.replace(/[^ACGTUN]/g, "");
  return { seq: kept, dropped: up.length - kept.length, fasta: /^\s*>/.test(raw) };
}

// ---------------------------------------------------------------- algorithms
function buildTable(a, b) {
  const m = a.length, n = b.length, W = n + 1;
  const dp = new Int32Array((m + 1) * W);
  const dir = new Uint8Array((m + 1) * W);
  for (let i = 1; i <= m; i++) {
    const ai = a.charCodeAt(i - 1);
    for (let j = 1; j <= n; j++) {
      const k = i * W + j;
      if (ai === b.charCodeAt(j - 1)) { dp[k] = dp[k - W - 1] + 1; dir[k] = DIAG; }
      else if (dp[k - W] >= dp[k - 1]) { dp[k] = dp[k - W]; dir[k] = UP; }
      else { dp[k] = dp[k - 1]; dir[k] = LEFT; }
    }
  }
  return { dp, dir, m, n, W, at: (i, j) => dp[i * W + j] };
}

function traceback(T, a, i = T.m, j = T.n) {
  const path = [[i, j]], pairs = [];
  let s = "";
  while (i > 0 && j > 0) {
    const d = T.dir[i * T.W + j];
    if (d === DIAG) { s = a[i - 1] + s; pairs.unshift([i - 1, j - 1]); i--; j--; }
    else if (d === UP) i--;
    else j--;
    path.push([i, j]);
  }
  return { lcs: s, path, pairs };
}

function allLcs(T, a, cap = 50) {
  const memo = new Map();
  const go = (i, j) => {
    if (i === 0 || j === 0) return new Set([""]);
    const key = i * T.W + j;
    if (memo.has(key)) return memo.get(key);
    let out;
    if (T.dir[key] === DIAG) out = new Set([...go(i - 1, j - 1)].map((s) => s + a[i - 1]));
    else {
      out = new Set();
      const up = T.at(i - 1, j), left = T.at(i, j - 1);
      if (up >= left) go(i - 1, j).forEach((s) => out.add(s));
      if (left >= up) go(i, j - 1).forEach((s) => out.add(s));
    }
    if (out.size > cap) out = new Set([...out].sort().slice(0, cap));
    memo.set(key, out);
    return out;
  };
  return [...go(T.m, T.n)].sort();
}

function lcsNaive(a, b, cap = 3_000_000) {
  let calls = 0;
  const f = (i, j) => {
    if (++calls > cap) throw new Error("cap");
    if (i === 0 || j === 0) return 0;
    if (a[i - 1] === b[j - 1]) return f(i - 1, j - 1) + 1;
    return Math.max(f(i - 1, j), f(i, j - 1));
  };
  try { return { length: f(a.length, b.length), ops: calls, aborted: false }; }
  catch { return { length: null, ops: calls, aborted: true }; }
}

function lcsMemo(a, b) {
  const W = b.length + 1;
  const memo = new Int32Array((a.length + 1) * W).fill(-1);
  let calls = 0, hits = 0;
  const f = (i, j) => {
    calls++;
    if (i === 0 || j === 0) return 0;
    const k = i * W + j;
    if (memo[k] !== -1) { hits++; return memo[k]; }
    const v = a[i - 1] === b[j - 1] ? f(i - 1, j - 1) + 1 : Math.max(f(i - 1, j), f(i, j - 1));
    memo[k] = v;
    return v;
  };
  return { length: f(a.length, b.length), ops: calls, hits };
}

function lcsTwoRows(a, b) {
  if (b.length > a.length) [a, b] = [b, a];
  let prev = new Int32Array(b.length + 1), cur = new Int32Array(b.length + 1);
  for (let i = 0; i < a.length; i++) {
    for (let j = 1; j <= b.length; j++) {
      cur[j] = a[i] === b[j - 1] ? prev[j - 1] + 1 : Math.max(prev[j], cur[j - 1]);
    }
    [prev, cur] = [cur, prev];
  }
  return { length: prev[b.length], ops: a.length * b.length };
}

function editDistance(a, b) {
  let prev = Array.from({ length: b.length + 1 }, (_, j) => j);
  for (let i = 1; i <= a.length; i++) {
    const cur = [i];
    for (let j = 1; j <= b.length; j++) {
      cur[j] = Math.min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
    }
    prev = cur;
  }
  return prev[b.length];
}

const gc = (s) => (s.length ? (s.split("").filter((c) => c === "G" || c === "C").length / s.length) : 0);

function timed(fn) {
  // Repeat fast functions so the timing is meaningful; slow ones run once.
  let reps = 0, out;
  const t0 = performance.now();
  do { out = fn(); reps++; } while (performance.now() - t0 < 8 && reps < 500);
  return { ...out, ms: (performance.now() - t0) / reps };
}

function compareMethods(a, b) {
  const m = a.length, n = b.length;
  const rows = [];
  rows.push(m + n <= 26
    ? { key: "naive", name: "Naive recursion", cx: "O(2^(m+n)) time · O(m+n) stack", ...(() => { const t0 = performance.now(); const r = lcsNaive(a, b); return { ...r, ms: performance.now() - t0 }; })(), note: "Recomputes the same (i, j) states again and again." }
    : { key: "naive", name: "Naive recursion", cx: "O(2^(m+n)) time · O(m+n) stack", skipped: true, note: "Skipped: exponential for inputs over 26 bases combined. This is the reason DP exists." });
  rows.push(m + n <= 5000
    ? { key: "memo", name: "Top-down memoization", cx: "O(m·n) time · O(m·n) space", ...timed(() => lcsMemo(a, b)), note: "Recursion with a cache. Each state is solved once; repeat visits are cache hits." }
    : { key: "memo", name: "Top-down memoization", cx: "O(m·n) time · O(m·n) space", skipped: true, note: "Skipped: recursion depth too large for the browser stack." });
  rows.push({ key: "tab", name: "Bottom-up tabulation", cx: "O(m·n) time · O(m·n) space", ...timed(() => { const T = buildTable(a, b); return { length: T.at(m, n), ops: m * n }; }), note: "Fills the table row by row. Keeps every state, so the LCS can be reconstructed." });
  rows.push({ key: "rows", name: "Space-optimized (2 rows)", cx: "O(m·n) time · O(min(m,n)) space", ...timed(() => lcsTwoRows(a, b)), note: "Keeps only two rows. Returns the length but cannot recover the subsequence." });
  return rows;
}

// ---------------------------------------------------------------- state
const state = { a: "", b: "", T: null, tb: null, pinned: null, anim: null };

// ---------------------------------------------------------------- rendering: results
function renderAlignment(a, b, pairs) {
  const top = [], bot = [];
  let i = 0, j = 0;
  const push = (x, y, match) => { top.push([x, match]); bot.push([y, match]); };
  for (const [pi, pj] of [...pairs, [a.length, b.length]]) {
    while (i < pi) push(a[i++], "-", false);
    while (j < pj) push("-", b[j++], false);
    if (i < a.length && j < b.length && pi < a.length) { push(a[i++], b[j++], true); }
  }
  const cell = ([c, m]) => `<span class="c ${m ? "m" : ""} ${c === "-" ? "gap" : ""}">${c === "-" ? "-" : nt(c)}</span>`;
  const bars = top.map(([, m]) => `<span class="c">${m ? "│" : " "}</span>`).join("");
  $("#alignment").innerHTML = top.length
    ? `<div class="al-row"><span class="lab">A</span>${top.map(cell).join("")}</div>
       <div class="al-row bars"><span class="lab"></span>${bars}</div>
       <div class="al-row"><span class="lab">B</span>${bot.map(cell).join("")}</div>`
    : `<span class="muted">Enter two sequences above.</span>`;
}

function metric(value, label, desc, meter) {
  return `<div class="metric"><div class="mv">${value}</div><div class="ml">${label}</div><div class="md">${desc}</div>${meter != null ? `<div class="meter"><i style="width:${Math.max(0, Math.min(1, meter)) * 100}%"></i></div>` : ""}</div>`;
}

function renderResults() {
  const { a, b, T, tb } = state;
  const m = a.length, n = b.length, L = tb.lcs.length;
  $("#lcsValue").innerHTML = L ? tb.lcs.split("").map(nt).join("") : `<span class="empty">${m && n ? "No shared bases." : "Waiting for two sequences."}</span>`;
  $("#lcsLen").textContent = L;
  renderAlignment(a, b, tb.pairs);

  const ed = editDistance(a, b);
  const sim = m + n ? (2 * L) / (m + n) : 0;
  const edSim = Math.max(m, n) ? 1 - ed / Math.max(m, n) : 1;
  const hamming = m === n && m ? [...a].filter((c, k) => c !== b[k]).length : null;
  $("#metrics").innerHTML = [
    metric(pct(sim), "LCS similarity", "2·L / (m + n): shared bases relative to the combined length.", sim),
    metric(pct(m ? L / m : 0), "Coverage of A", `${L} of ${m} bases of A are in the LCS.`, m ? L / m : 0),
    metric(pct(n ? L / n : 0), "Coverage of B", `${L} of ${n} bases of B are in the LCS.`, n ? L / n : 0),
    metric(fmt(ed), "Edit distance", "Fewest insertions, deletions and substitutions to turn A into B (Levenshtein DP).", null),
    metric(pct(edSim), "Edit similarity", "1 − edit distance / longer length.", edSim),
    metric(hamming == null ? "n/a" : fmt(hamming), "Hamming distance", hamming == null ? "Only defined when both sequences have the same length." : "Positions that differ, compared base by base.", null),
    metric(`${pct(gc(a))} · ${pct(gc(b))}`, "GC content A · B", "Share of G and C bases in each strand.", null),
    metric(fmt((m + 1) * (n + 1)), "DP states", `(m+1)·(n+1) cells. Each is solved once, in O(1).`, null),
  ].join("");

  const wrap = $("#allLcsWrap");
  if (m * n <= 2500 && L) {
    const list = allLcs(T, a);
    wrap.style.display = "";
    $("#allLcsCount").textContent = `(${list.length}${list.length >= 50 ? "+" : ""} distinct)`;
    $("#allLcs").innerHTML = list.map((s) => `<span class="pill">${s.split("").map(nt).join("")}</span>`).join("");
  } else {
    wrap.style.display = "none";
  }
}

// ---------------------------------------------------------------- rendering: DP table
let cells = [];

function renderTable() {
  stopAnim();
  state.pinned = null;
  const { a, b, T, tb } = state;
  const scroll = $("#tableScroll");
  const size = (T.m + 1) * (T.n + 1);
  cells = [];

  if (!T.m || !T.n) {
    setControls(false);
    scroll.innerHTML = `<p class="muted" style="padding:1rem">Enter two sequences to build the table.</p>`;
    $("#tableNote").textContent = "";
    return;
  }

  if (size > 4900) {
    renderHeatmap(scroll);
    $("#tableNote").textContent = `The table has ${fmt(size)} cells, too many to list individually, so it is drawn as a heatmap: darker cells hold larger LCS lengths and the red line is the traceback path. Use sequences under 70 bases to inspect each cell.`;
    setControls(false);
    return;
  }
  setControls(true);

  const onPath = new Set(tb.path.map(([i, j]) => i * T.W + j));
  const compact = size > 900;
  let h = `<table class="dp ${compact ? "compact" : ""}"><thead><tr><th></th><th>ε<small>0</small></th>`;
  for (let j = 1; j <= T.n; j++) h += `<th data-col="${j}"><span class="nt-${b[j - 1]}">${b[j - 1]}</span><small>${j}</small></th>`;
  h += `</tr></thead><tbody>`;
  for (let i = 0; i <= T.m; i++) {
    h += `<tr><th data-row="${i}">${i ? `<span class="nt-${a[i - 1]}">${a[i - 1]}</span><small>${i}</small>` : `ε<small>0</small>`}</th>`;
    for (let j = 0; j <= T.n; j++) {
      const k = i * T.W + j;
      const d = T.dir[k];
      const cls = [i === 0 || j === 0 ? "base" : "", onPath.has(k) ? "path" : "", onPath.has(k) && d === DIAG ? "take" : "", d === DIAG ? "mt" : ""].join(" ");
      h += `<td class="${cls}" data-i="${i}" data-j="${j}"><span class="ar">${ARROW[d] || ""}</span><span class="v">${T.dp[k]}</span></td>`;
    }
    h += `</tr>`;
  }
  h += `</tbody></table>`;
  scroll.innerHTML = h;
  scroll.querySelectorAll("td").forEach((td) => { cells[+td.dataset.i * T.W + +td.dataset.j] = td; });
  applyToggles();
  $("#tableNote").textContent = `${T.m + 1} × ${T.n + 1} table. The answer, dp[${T.m}][${T.n}] = ${T.at(T.m, T.n)}, is the bottom-right cell. The highlighted path is the traceback that spells "${tb.lcs || "∅"}".`;
  inspect(T.m, T.n);
}

function renderHeatmap(scroll) {
  const { T, tb } = state;
  const c = document.createElement("canvas");
  c.className = "heat";
  c.width = T.n + 1; c.height = T.m + 1;
  const scale = Math.max(1, Math.floor(600 / Math.max(T.m + 1, T.n + 1)));
  c.style.width = `${c.width * scale}px`;
  const ctx = c.getContext("2d");
  const img = ctx.createImageData(c.width, c.height);
  const max = Math.max(1, T.at(T.m, T.n));
  for (let k = 0; k < T.dp.length; k++) {
    const t = T.dp[k] / max;
    img.data[k * 4] = 243 - t * 221; img.data[k * 4 + 1] = 239 - t * 215; img.data[k * 4 + 2] = 230 - t * 201; img.data[k * 4 + 3] = 255;
  }
  for (const [i, j] of tb.path) { const k = (i * T.W + j) * 4; img.data[k] = 230; img.data[k + 1] = 60; img.data[k + 2] = 50; }
  ctx.putImageData(img, 0, 0);
  scroll.innerHTML = "";
  scroll.appendChild(c);
}

function setControls(on) {
  ["#playBtn", "#stepBtn", "#traceBtn", "#resetBtn"].forEach((s) => ($(s).disabled = !on));
}

function applyToggles() {
  const t = $("#tableScroll table");
  if (!t) return;
  t.classList.toggle("no-arrows", !$("#showArrows").checked);
  t.classList.toggle("show-path", $("#showPath").checked);
}

function clearMarks(...names) {
  const root = $("#tableScroll");
  names.forEach((n) => root.querySelectorAll(`.${n}`).forEach((el) => el.classList.remove(n)));
}

function inspect(i, j) {
  const { a, b, T } = state;
  if (!T || !cells.length) return;
  clearMarks("dep", "hl");
  const k = i * T.W + j, v = T.dp[k];
  const A = a.slice(0, i), B = b.slice(0, j);
  let why, deps = [];
  if (i === 0 || j === 0) {
    why = `Base case: ${i === 0 ? "A" : "B"}'s prefix is empty, and an empty string shares nothing.<br/>dp[${i}][${j}] = 0`;
  } else if (a[i - 1] === b[j - 1]) {
    deps = [[i - 1, j - 1]];
    why = `A<sub>${i}</sub> = ${nt(a[i - 1])} equals B<sub>${j}</sub> = ${nt(b[j - 1])}, so this base extends the diagonal.<br/>dp[${i - 1}][${j - 1}] + 1 = ${T.at(i - 1, j - 1)} + 1 = <b>${v}</b> ↖`;
  } else {
    const up = T.at(i - 1, j), left = T.at(i, j - 1);
    deps = [[i - 1, j], [i, j - 1]];
    const from = T.dir[k] === UP ? `↑ from above (drop A<sub>${i}</sub>)` : `← from the left (drop B<sub>${j}</sub>)`;
    why = `A<sub>${i}</sub> = ${nt(a[i - 1])} ≠ B<sub>${j}</sub> = ${nt(b[j - 1])}, so one of them must be dropped.<br/>max(dp[${i - 1}][${j}] = ${up}, dp[${i}][${j - 1}] = ${left}) = <b>${v}</b><br/>${from}${up === left ? "<br/><span class='muted'>Tie: both choices are optimal; this engine prefers ↑.</span>" : ""}`;
  }
  deps.forEach(([di, dj]) => cells[di * T.W + dj]?.classList.add("dep"));
  document.querySelector(`#tableScroll th[data-row="${i}"]`)?.classList.add("hl");
  document.querySelector(`#tableScroll th[data-col="${j}"]`)?.classList.add("hl");
  const sub = traceback(T, a, i, j).lcs;
  $("#inspectorBody").innerHTML = `
    <p class="cellref">dp[${i}][${j}] = ${v}</p>
    <div class="why">${why}</div>
    <p class="prefix"><b>A[1..${i}]</b> = ${A ? A.split("").map(nt).join("") : "ε"}</p>
    <p class="prefix"><b>B[1..${j}]</b> = ${B ? B.split("").map(nt).join("") : "ε"}</p>
    <p class="prefix"><b>LCS of these prefixes</b> = ${sub ? sub.split("").map(nt).join("") : "ε"}</p>
    ${state.pinned ? `<p class="hint">Pinned. Click the cell again to release.</p>` : `<p class="hint">Click to pin this cell and trace back its prefix LCS.</p>`}`;
}

function pinCell(i, j) {
  clearMarks("ppath", "pinned");
  if (state.pinned && state.pinned[0] === i && state.pinned[1] === j) { state.pinned = null; inspect(i, j); return; }
  state.pinned = [i, j];
  const { path } = traceback(state.T, state.a, i, j);
  path.forEach(([pi, pj]) => cells[pi * state.T.W + pj]?.classList.add("ppath"));
  cells[i * state.T.W + j]?.classList.add("pinned");
  inspect(i, j);
}

// ---------------------------------------------------------------- animation
const DELAYS = [700, 450, 280, 170, 100, 55, 28, 12, 5, 1];
const delay = () => DELAYS[+$("#speed").value - 1];

function stopAnim() {
  if (state.anim) clearTimeout(state.anim.timer);
  state.anim = null;
  clearMarks("cur", "trace");
}

function startFill(stepOnly = false) {
  const { T } = state;
  if (!cells.length) return;
  if (!state.anim || state.anim.kind !== "fill") {
    stopAnim();
    clearMarks("ppath", "pinned");
    state.pinned = null;
    for (let i = 1; i <= T.m; i++) for (let j = 1; j <= T.n; j++) cells[i * T.W + j].classList.add("hide");
    $("#tableScroll table").classList.remove("show-path");
    state.anim = { kind: "fill", k: 0 };
  }
  const total = T.m * T.n;
  const tick = () => {
    const A = state.anim;
    if (!A || A.kind !== "fill") return;
    clearMarks("cur");
    if (A.k >= total) { finishFill(); return; }
    const i = Math.floor(A.k / T.n) + 1, j = (A.k % T.n) + 1;
    const td = cells[i * T.W + j];
    td.classList.remove("hide");
    td.classList.add("cur");
    inspect(i, j);
    if (!stepOnly) td.scrollIntoView({ block: "nearest", inline: "nearest" });
    A.k++;
    if (!stepOnly) A.timer = setTimeout(tick, delay());
  };
  if (state.anim.timer) clearTimeout(state.anim.timer);
  tick();
}

function finishFill() {
  stopAnim();
  $("#tableScroll").querySelectorAll(".hide").forEach((el) => el.classList.remove("hide"));
  applyToggles();
  inspect(state.T.m, state.T.n);
}

function startTrace() {
  if (!cells.length) return;
  finishFill();
  const { path } = state.tb;
  state.anim = { kind: "trace", k: 0 };
  const tick = () => {
    const A = state.anim;
    if (!A || A.kind !== "trace") return;
    if (A.k >= path.length) { state.anim = null; return; }
    const [i, j] = path[A.k];
    cells[i * state.T.W + j].classList.add("trace");
    cells[i * state.T.W + j].scrollIntoView({ block: "nearest", inline: "nearest" });
    inspect(i, j);
    A.k++;
    A.timer = setTimeout(tick, Math.max(80, delay() * 3));
  };
  tick();
}

// ---------------------------------------------------------------- rendering: algorithms
function renderAlgorithms() {
  const { a, b } = state;
  const rows = compareMethods(a, b);
  const fastest = rows.filter((r) => !r.skipped && r.ms != null).sort((x, y) => x.ms - y.ms)[0];
  $("#algoGrid").innerHTML = rows.map((r) => `
    <div class="algo ${r.skipped ? "skipped" : ""} ${fastest && r.key === fastest.key ? "best" : ""}">
      <h3>${r.name}</h3>
      <span class="cx">${r.cx}</span>
      <dl>
        <dt>LCS length</dt><dd>${r.skipped || r.length == null ? "—" : r.length}</dd>
        <dt>Subproblem calls</dt><dd>${r.skipped ? "—" : fmt(r.ops)}${r.aborted ? "+" : ""}</dd>
        ${r.hits != null ? `<dt>Cache hits</dt><dd>${fmt(r.hits)}</dd>` : ""}
        <dt>Time</dt><dd>${r.skipped || r.ms == null ? "—" : r.ms < 0.01 ? "&lt;0.01 ms" : `${r.ms.toFixed(r.ms < 1 ? 3 : 1)} ms`}</dd>
      </dl>
      <p class="note">${r.aborted ? "Stopped after 3,000,000 calls without finishing. " : ""}${r.note}${fastest && r.key === fastest.key ? " <b>Fastest on this input.</b>" : ""}</p>
    </div>`).join("");

  const live = rows.filter((r) => !r.skipped && r.ops);
  const maxLog = Math.max(1, ...live.map((r) => Math.log10(r.ops + 1)));
  $("#opsChart").innerHTML = rows.map((r) => {
    const w = r.skipped || !r.ops ? 0 : (Math.log10(r.ops + 1) / maxLog) * 85;
    return `<div class="bar-row"><span>${r.name}</span><div class="bar-track"><div class="bar ${r.key === "naive" ? "naive" : ""}" style="width:${w}%"></div><span class="bar-val" style="left:${w}%">${r.skipped ? "skipped" : fmt(r.ops) + (r.aborted ? "+" : "")}</span></div></div>`;
  }).join("") + `<p class="hint">Tabulation and the two-row version each evaluate exactly m·n = ${fmt(a.length * b.length)} cells. Memoization makes a few more calls because it also visits base cases and cache hits.</p>`;
}

// ---------------------------------------------------------------- Python / Biopython via Pyodide
let pyReady = null;
function loadScript(src) {
  return new Promise((res, rej) => { const s = document.createElement("script"); s.src = src; s.onload = res; s.onerror = () => rej(new Error("Could not load " + src)); document.head.appendChild(s); });
}
function pyStatus(msg, cls = "") { const el = $("#pyStatus"); el.textContent = msg; el.className = `py-status ${cls}`; }

function getPython() {
  if (!pyReady) {
    pyReady = (async () => {
      pyStatus("Loading the Python runtime (Pyodide)…");
      await loadScript("https://cdn.jsdelivr.net/pyodide/v0.26.4/full/pyodide.js");
      const py = await window.loadPyodide();
      pyStatus("Installing Biopython…");
      await py.loadPackage(["biopython"]);
      const src = await (await fetch("/py/lcs_core.py")).text();
      py.FS.writeFile("lcs_core.py", src);
      py.runPython("import sys, os\nsys.path.insert(0, os.getcwd())\nimport lcs_core");
      return py;
    })().catch((e) => { pyReady = null; throw e; });
  }
  return pyReady;
}

function formatAlignment(top, bot, width = 60) {
  let out = "";
  for (let s = 0; s < top.length; s += width) {
    const t = top.slice(s, s + width), u = bot.slice(s, s + width);
    const mid = [...t].map((c, k) => (c === "-" || u[k] === "-" ? " " : c === u[k] ? "|" : ".")).join("");
    out += `A ${String(s + 1).padStart(4)}  ${esc(t)}\n         <span class="m">${mid}</span>\nB ${String(s + 1).padStart(4)}  ${esc(u)}\n\n`;
  }
  return out.trimEnd();
}

async function runPython() {
  const btn = $("#pyBtn");
  btn.disabled = true;
  try {
    const py = await getPython();
    pyStatus("Running lcs_core.analyze() in Python…");
    await new Promise((r) => setTimeout(r, 30)); // let the status paint before the synchronous run
    py.globals.set("seq_a", state.a);
    py.globals.set("seq_b", state.b);
    const r = JSON.parse(py.runPython("lcs_core.analyze_json(seq_a, seq_b)"));
    const agrees = r.lcs === state.tb.lcs;
    const al = r.alignment;
    const M = r.metrics;
    $("#pyOut").innerHTML = `
      <div class="py-grid">
        <div class="py-box"><div class="k">Python LCS</div><div class="v">${esc(r.lcs) || "ε"}</div></div>
        <div class="py-box"><div class="k">Length · matches browser?</div><div class="v">${r.lcs.length} · <span class="${agrees ? "ok" : ""}">${agrees ? "✓ identical" : "differs"}</span></div></div>
        <div class="py-box"><div class="k">LCS similarity · edit distance</div><div class="v">${pct(M.lcs_similarity)} · ${M.edit_distance}</div></div>
        <div class="py-box"><div class="k">GC (Bio.SeqUtils) A · B</div><div class="v">${pct(M.gc_a)} · ${pct(M.gc_b)}</div></div>
      </div>
      ${al ? `
      <div class="py-grid">
        <div class="py-box"><div class="k">Biopython alignment score</div><div class="v">${al.score}</div></div>
        <div class="py-box"><div class="k">Identity</div><div class="v">${pct(al.identity)} <span class="small">(${al.identities}/${al.length})</span></div></div>
        <div class="py-box"><div class="k">Mismatches · gaps</div><div class="v">${al.mismatches} · ${al.gaps}</div></div>
        <div class="py-box"><div class="k">Co-optimal alignments</div><div class="v">${al.optimal_alignments == null ? "very many" : fmt(al.optimal_alignments)}</div></div>
      </div>
      <div><p class="kicker" style="color:#8f8a7e">PairwiseAligner · ${esc(al.scoring)}</p><pre class="aln">${formatAlignment(al.aligned_a, al.aligned_b)}</pre>
      <p class="hint" style="color:#8f8a7e">"|" = identical · "." = substitution · space = gap. Unlike LCS, the scored alignment can pair two different bases (a substitution) instead of opening two gaps.</p></div>` : ""}
      <div>
        <p class="kicker" style="color:#8f8a7e">Python timings (same four approaches)</p>
        <table><thead><tr><th>Method</th><th>Complexity</th><th>Length</th><th>Calls</th><th>Time</th><th>Note</th></tr></thead><tbody>
        ${r.methods.map((x) => `<tr><td>${esc(x.method)}</td><td>${esc(x.complexity)}</td><td class="num">${x.length ?? "—"}</td><td class="num">${fmt(x.operations)}</td><td class="num">${x.time_ms == null ? "—" : x.time_ms.toFixed(3) + " ms"}</td><td>${esc(x.note)}</td></tr>`).join("")}
        </tbody></table>
      </div>
      <div class="py-grid">
        <div class="py-box"><div class="k">Reverse complement A (Bio.Seq)</div><div class="v small">${esc(r.info_a.reverse_complement) || "—"}</div></div>
        <div class="py-box"><div class="k">Reverse complement B</div><div class="v small">${esc(r.info_b.reverse_complement) || "—"}</div></div>
        <div class="py-box"><div class="k">Translation A · B</div><div class="v small">${esc(r.info_a.translation) || "—"}<br/>${esc(r.info_b.translation) || "—"}</div></div>
      </div>`;
    pyStatus(`Done · Python ${r.python_version} · Biopython ${r.biopython_version ?? "?"}`, "ok");
  } catch (e) {
    console.error(e);
    pyStatus(`Python run failed: ${e.message}`, "err");
  } finally {
    btn.disabled = false;
  }
}

// ---------------------------------------------------------------- hero strand
function heroStrand() {
  const el = $("#heroStrand");
  const comp = { A: "T", T: "A", C: "G", G: "C" };
  const seq = "GATTACACGTGCAT";
  const lcsRows = new Set([1, 3, 4, 7, 9, 12]);
  el.innerHTML = seq.split("").map((c, k) => `<div class="strand-row ${lcsRows.has(k) ? "hit" : ""}"><span class="b nt-${c}">${c}</span><i class="rung"></i><span class="b nt-${comp[c]}">${comp[c]}</span></div>`).join("");
  const rows = [...el.children];
  let t = 0;
  const reduce = matchMedia("(prefers-reduced-motion: reduce)").matches;
  const frame = () => {
    rows.forEach((r, k) => {
      const s = Math.sin(t + k * 0.55);
      r.querySelector(".rung").style.width = `${24 + Math.abs(s) * 150}px`;
      r.style.transform = `translateX(${s * 18}px)`;
      r.style.opacity = 0.55 + Math.abs(s) * 0.45;
    });
    t += 0.025;
    if (!reduce) requestAnimationFrame(frame);
  };
  frame();
}

// ---------------------------------------------------------------- wiring
function readInputs() {
  const A = cleanSequence($("#seqA").value), B = cleanSequence($("#seqB").value);
  const limit = 2000;
  const warn = (r, el) => {
    const msgs = [];
    if (r.dropped) msgs.push(`${r.dropped} non-nucleotide character${r.dropped > 1 ? "s" : ""} ignored`);
    if (r.seq.length > limit) msgs.push(`trimmed to the first ${limit} bases`);
    if (r.fasta) msgs.push("FASTA header detected");
    el.textContent = msgs.join(" · ");
  };
  warn(A, $("#warnA")); warn(B, $("#warnB"));
  state.a = A.seq.slice(0, limit);
  state.b = B.seq.slice(0, limit);
  $("#lenA").textContent = `${state.a.length} nt`;
  $("#lenB").textContent = `${state.b.length} nt`;
}

function recompute() {
  readInputs();
  state.T = buildTable(state.a, state.b);
  state.tb = traceback(state.T, state.a);
  renderResults();
  renderTable();
  renderAlgorithms();
  if ($("#pyOut").innerHTML) $("#pyStatus").textContent = "Inputs changed. Run again to refresh the Python results.";
}

function setSample(key) {
  let s = SAMPLES[key];
  if (key === "random") {
    const r = (n) => Array.from({ length: n }, () => "ACGT"[Math.floor(Math.random() * 4)]).join("");
    s = { a: r(10 + Math.floor(Math.random() * 6)), b: r(10 + Math.floor(Math.random() * 6)) };
  }
  $("#seqA").value = s.a;
  $("#seqB").value = s.b;
  recompute();
}

let debounce;
["#seqA", "#seqB"].forEach((s) => $(s).addEventListener("input", () => { clearTimeout(debounce); debounce = setTimeout(recompute, 180); }));
document.querySelectorAll("[data-sample]").forEach((btn) => btn.addEventListener("click", () => setSample(btn.dataset.sample)));
$("#swapBtn").addEventListener("click", () => { const t = $("#seqA").value; $("#seqA").value = $("#seqB").value; $("#seqB").value = t; recompute(); });

const scroll = $("#tableScroll");
scroll.addEventListener("mouseover", (e) => {
  const td = e.target.closest("td");
  if (td && !state.anim && !state.pinned) inspect(+td.dataset.i, +td.dataset.j);
});
scroll.addEventListener("click", (e) => {
  const td = e.target.closest("td");
  if (td && !state.anim) pinCell(+td.dataset.i, +td.dataset.j);
});

$("#playBtn").addEventListener("click", () => startFill(false));
$("#stepBtn").addEventListener("click", () => {
  if (state.anim && state.anim.kind === "fill") clearTimeout(state.anim.timer);
  startFill(true);
});
$("#traceBtn").addEventListener("click", startTrace);
$("#resetBtn").addEventListener("click", () => { finishFill(); clearMarks("ppath", "pinned"); state.pinned = null; });
$("#showArrows").addEventListener("change", applyToggles);
$("#showPath").addEventListener("change", applyToggles);
$("#pyBtn").addEventListener("click", runPython);

heroStrand();
setSample("short");
