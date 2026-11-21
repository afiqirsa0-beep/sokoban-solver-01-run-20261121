// Room-split push-optimal Sokoban solver: A* over push states per room, then the pushes are walked on the full level.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DX = [0, 0, -1, 1], DY = [-1, 1, 0, 0], LET = 'udlr';

const solve = (text: string): string => {
  const rows = text.split('\n').map((r) => r.replace(/\r$/, '')).filter((r) => r.length > 0);
  const H = rows.length, W = Math.max(...rows.map((r) => r.length));
  const at = (x: number, y: number) => (x < 0 || y < 0 || x >= W || y >= H ? '#' : rows[y][x] ?? ' ');
  const floor = (x: number, y: number) => at(x, y) !== '#';
  let px = 0, py = 0;
  const boxes = new Set<number>(), goals = new Set<number>();
  for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
    const c = at(x, y);
    if (c === '@' || c === '+') { px = x; py = y; }
    if (c === '$' || c === '*') boxes.add(y * W + x);
    if (c === '.' || c === '*' || c === '+') goals.add(y * W + x);
  }
  // Rooms: floor components with the hallway row (the player's row) removed.
  const comp = new Map<number, number>();
  const rooms: number[][] = [];
  for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
    if (y === py || !floor(x, y) || comp.has(y * W + x)) continue;
    const cells = [y * W + x]; comp.set(y * W + x, rooms.length);
    for (let i = 0; i < cells.length; i++) {
      const cx = cells[i] % W, cy = (cells[i] - cx) / W;
      for (let d = 0; d < 4; d++) {
        const nx = cx + DX[d], ny = cy + DY[d];
        if (ny !== py && floor(nx, ny) && !comp.has(ny * W + nx)) { comp.set(ny * W + nx, rooms.length); cells.push(ny * W + nx); }
      }
    }
    rooms.push(cells);
  }
  const pushes: [number, number][] = []; // [box cell, direction] in full-grid coordinates
  for (const room of rooms) {
    const rb = room.filter((c) => boxes.has(c));
    if (!rb.length) continue;
    // Local cells: the room plus the hallway cells touching it (the player's entry only).
    const cells = [...room];
    for (const c of room) { const x = c % W, y = (c - x) / W; for (const d of [0, 1]) { const hy = y + DY[d]; if (hy === py && floor(x, hy) && !cells.includes(hy * W + x)) cells.push(hy * W + x); } }
    cells.sort((a, b) => a - b);
    const n = cells.length, id = new Map(cells.map((c, i) => [c, i]));
    const nb = cells.map((c) => { const x = c % W, y = (c - x) / W; return [0, 1, 2, 3].map((d) => id.get((y + DY[d]) * W + x + DX[d]) ?? -1); });
    const inRoom = cells.map((c) => comp.get(c) !== undefined);
    // Reverse pull BFS from goals: min pushes per box cell (Infinity = dead square).
    const dist = new Array<number>(n).fill(Infinity), q: number[] = [];
    for (const c of room) if (goals.has(c)) { dist[id.get(c)!] = 0; q.push(id.get(c)!); }
    for (let i = 0; i < q.length; i++) for (let d = 0; d < 4; d++) {
      const to = nb[q[i]][d], pl = to < 0 ? -1 : nb[to][d];
      if (to >= 0 && pl >= 0 && inRoom[to] && dist[to] === Infinity) { dist[to] = dist[q[i]] + 1; q.push(to); }
    }
    const goalMask = new Array<boolean>(n).fill(false);
    for (const c of room) if (goals.has(c)) goalMask[id.get(c)!] = true;
    // Player entry: the hallway cell adjacent to the room.
    const entry = inRoom.findIndex((v) => !v);
    const norm = (b: number[], p: number) => { // min reachable cell + sorted box key
      const seen = new Uint8Array(n), st = [p]; seen[p] = 1; let m = p;
      for (let i = 0; i < st.length; i++) { const u = st[i]; if (u < m) m = u; for (let d = 0; d < 4; d++) { const v = nb[u][d]; if (v >= 0 && !seen[v] && !b.includes(v)) { seen[v] = 1; st.push(v); } } }
      return { m, seen };
    };
    const keyOf = (b: number[], m: number) => b.reduce((k, v) => k * 64 + v, m);
    const h = (b: number[]) => b.reduce((s, v) => s + dist[v], 0);
    const b0 = rb.map((c) => id.get(c)!).sort((a, b) => a - b);
    const nodes: { b: number[]; p: number; g: number; par: number; mv: number }[] = [];
    const best = new Map<number, number>(), buckets: number[][] = [];
    const add = (b: number[], p: number, g: number, par: number, mv: number) => {
      const { m } = norm(b, p), k = keyOf(b, m);
      if (best.has(k) && best.get(k)! <= g) return;
      best.set(k, g); nodes.push({ b, p: m, g, par, mv });
      const f = g + h(b); (buckets[f] ??= []).push(nodes.length - 1);
    };
    add(b0, entry, 0, -1, -1);
    let goalNode = -1;
    for (let f = 0; goalNode < 0 && f < buckets.length; f++) {
      const bk = buckets[f] ?? [];
      for (let bi = 0; bi < bk.length && goalNode < 0; bi++) {
        const nd = nodes[bk[bi]];
        if (best.get(keyOf(nd.b, nd.p))! < nd.g) continue;
        if (nd.b.every((v) => goalMask[v])) { goalNode = bk[bi]; break; }
        const { seen } = norm(nd.b, nd.p);
        for (let bx = 0; bx < nd.b.length; bx++) for (let d = 0; d < 4; d++) {
          const from = nb[nd.b[bx]][d ^ 1], to = nb[nd.b[bx]][d];
          if (from < 0 || to < 0 || !seen[from] || nd.b.includes(to) || dist[to] === Infinity) continue;
          const nbx = nd.b.slice(); nbx[bx] = to; nbx.sort((a, b) => a - b);
          add(nbx, nd.b[bx], nd.g + 1, bk[bi], cells[nd.b[bx]] * 4 + d);
        }
      }
    }
    if (goalNode < 0) continue; // unsolvable by this model: leave the room alone
    const seq: [number, number][] = [];
    for (let i = goalNode; nodes[i].par >= 0; i = nodes[i].par) seq.push([Math.floor(nodes[i].mv / 4), nodes[i].mv % 4]);
    pushes.push(...seq.reverse());
  }
  // Walk the pushes on the full level.
  let out = '';
  for (const [c, d] of pushes) {
    const tx = (c % W) - DX[d], ty = Math.floor(c / W) - DY[d], goal = ty * W + tx;
    const prev = new Map<number, number>([[py * W + px, -1]]), st = [py * W + px];
    for (let i = 0; i < st.length && !prev.has(goal); i++) for (let e = 0; e < 4; e++) {
      const x = (st[i] % W) + DX[e], y = Math.floor(st[i] / W) + DY[e], v = y * W + x;
      if (floor(x, y) && !boxes.has(v) && !prev.has(v)) { prev.set(v, st[i] * 4 + e); st.push(v); }
    }
    let walk = '';
    for (let v = goal; prev.get(v)! >= 0; v = Math.floor(prev.get(v)! / 4)) walk = LET[prev.get(v)! % 4] + walk;
    out += walk + LET[d].toUpperCase();
    boxes.delete(c); boxes.add(c + DY[d] * W + DX[d]);
    px = c % W; py = Math.floor(c / W);
  }
  return out;
};

for (const id of readdirSync(I).sort()) {
  const moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
