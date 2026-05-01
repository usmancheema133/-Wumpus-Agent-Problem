/* =======================================================
   wumpus.js — Knowledge Base, CNF, Resolution Engine
   ======================================================= */

// ─── KNOWLEDGE BASE ───────────────────────────────────────
class KnowledgeBase {
  constructor() {
    this.clauses = [];      // Array of sets (each set = a clause in CNF)
    this.rawRules = [];     // Human-readable rule strings for logging
    this.inferenceSteps = 0;
    this.resolutionCalls = 0;
  }

  reset() {
    this.clauses = [];
    this.rawRules = [];
    this.inferenceSteps = 0;
    this.resolutionCalls = 0;
  }

  // TELL: Add a clause (already in CNF form, array of literals)
  tell(clause, ruleStr = null) {
    const clauseSet = new Set(clause);
    // Avoid duplicate clauses
    const isDup = this.clauses.some(c =>
      c.size === clauseSet.size && [...c].every(l => clauseSet.has(l))
    );
    if (!isDup) {
      this.clauses.push(clauseSet);
      if (ruleStr) this.rawRules.push(ruleStr);
      return true;
    }
    return false;
  }

  // Tell a biconditional: B_{r,c} <=> (P_{r-1,c} v P_{r+1,c} v P_{r,c-1} v P_{r,c+1})
  // Converted to CNF:
  // (1) ~B v P_n1 v P_n2 v ... (if breeze then at least one neighbor is pit)
  // (2) ~P_ni v B             (if pit in neighbor then breeze)
  tellBreezeRule(r, c, neighbors) {
    const B = `B_${r}_${c}`;
    const notB = `~B_${r}_${c}`;
    const pitLiterals = neighbors.map(([nr, nc]) => `P_${nr}_${nc}`);

    // B => (P_n1 v P_n2 v ...) => (~B v P_n1 v P_n2 v ...)
    const clause1 = [notB, ...pitLiterals];
    this.tell(clause1, `${B} ⇒ (${pitLiterals.join(' ∨ ')})`);

    // FIX: Each P_ni => B becomes (~P_ni v B)
    for (const nPit of pitLiterals) {
      this.tell([`~${nPit}`, B], `${nPit} ⇒ ${B}`);
    }
  }

  tellStenchRule(r, c, neighbors) {
    const S = `S_${r}_${c}`;
    const notS = `~S_${r}_${c}`;
    const wLiterals = neighbors.map(([nr, nc]) => `W_${nr}_${nc}`);

    // S => (W_n1 v W_n2 v ...) => (~S v W_n1 v ...)
    const clause1 = [notS, ...wLiterals];
    this.tell(clause1, `${S} ⇒ (${wLiterals.join(' ∨ ')})`);

    // FIX: Each W_ni => S becomes (~W_ni v S)
    for (const nW of wLiterals) {
      this.tell([`~${nW}`, S], `${nW} ⇒ ${S}`);
    }
  }

  // ─── RESOLUTION REFUTATION ─────────────────────────────
  // To prove α: add ~α to KB and resolve — if contradiction found, α is entailed
  // Returns { entailed: bool, steps: number, log: string[] }
  ask(alpha) {
    this.resolutionCalls++;
    const queryLog = [];

    // Negate alpha
    const negAlpha = negateLiteral(alpha);
    queryLog.push(`ASK: prove ${alpha} by refuting ${negAlpha}`);

    // Clone existing clauses and add ~alpha
    let workingClauses = this.clauses.map(c => new Set(c));
    workingClauses.push(new Set([negAlpha]));

    let steps = 0;
    const maxSteps = 500;
    let changed = true;

    while (changed && steps < maxSteps) {
      changed = false;
      const newClauses = [];

      for (let i = 0; i < workingClauses.length; i++) {
        for (let j = i + 1; j < workingClauses.length; j++) {
          steps++;
          this.inferenceSteps++;
          const resolvents = resolve(workingClauses[i], workingClauses[j]);

          for (const resolvent of resolvents) {
            // Empty clause = contradiction = query is entailed
            if (resolvent.size === 0) {
              queryLog.push(`⊢ CONTRADICTION found after ${steps} steps`);
              queryLog.push(`✓ ${alpha} IS ENTAILED by KB`);
              return { entailed: true, steps, log: queryLog };
            }

            // Check if resolvent is already present
            const alreadyPresent = workingClauses.some(c =>
              c.size === resolvent.size && [...c].every(l => resolvent.has(l))
            ) || newClauses.some(c =>
              c.size === resolvent.size && [...c].every(l => resolvent.has(l))
            );

            if (!alreadyPresent) {
              newClauses.push(resolvent);
              changed = true;
            }
          }
        }
      }

      workingClauses = workingClauses.concat(newClauses);
    }

    queryLog.push(`✗ ${alpha} NOT entailed (no contradiction after ${steps} steps)`);
    return { entailed: false, steps, log: queryLog };
  }
}

// ─── RESOLUTION HELPER ────────────────────────────────────
function resolve(c1, c2) {
  const resolvents = [];
  for (const lit of c1) {
    const negLit = negateLiteral(lit);
    if (c2.has(negLit)) {
      const newClause = new Set([...c1, ...c2]);
      newClause.delete(lit);
      newClause.delete(negLit);
      // Skip tautologies
      if (!isTautology(newClause)) {
        resolvents.push(newClause);
      }
    }
  }
  return resolvents;
}

function negateLiteral(lit) {
  return lit.startsWith('~') ? lit.slice(1) : '~' + lit;
}

function isTautology(clause) {
  for (const lit of clause) {
    if (clause.has(negateLiteral(lit))) return true;
  }
  return false;
}

// ─── WUMPUS WORLD ─────────────────────────────────────────
class WumpusWorld {
  constructor(rows, cols) {
    this.rows = rows;
    this.cols = cols;
    this.kb = new KnowledgeBase();
    this.grid = [];
    this.wumpusPos = null;
    this.goldPos = null;
    this.agentPos = { r: 0, c: 0 };
    this.visited = new Set();
    this.frontier = new Set();
    this.safeCells = new Set();
    this.dangerCells = new Set();
    this.goldFound = false;
    this.alive = true;
    this.moves = 0;   // FIX: starts at 0, incremented only on actual steps
    this.kbLog = [];
    this.resolutionLog = [];
    this._init();
  }

  _init() {
    // Build empty grid
    this.grid = Array.from({ length: this.rows }, (_, r) =>
      Array.from({ length: this.cols }, (_, c) => ({
        r, c,
        state: 'unknown',
        hasBreeze: false,
        hasStench: false,
        hasGold: false,
        hasPit: false,
        hasWumpus: false,
        percepts: []
      }))
    );

    this._placeHazards();

    // Agent starts at (0,0) — mark safe
    this.safeCells.add('0_0');
    this.kb.tell(['~P_0_0'], '~P_{0,0} (start is safe)');
    this.kb.tell(['~W_0_0'], '~W_{0,0} (start is safe)');
    this._logKB('TELL', '~P_0_0 ∧ ~W_0_0 (start cell is safe)');

    // FIX: Use _visitCellInit for the first cell so moves stays 0
    this._visitCellInit(0, 0);
  }

  _placeHazards() {
    const total = this.rows * this.cols;
    const numPits = Math.max(1, Math.floor(total * 0.15));

    let placed = 0;
    while (placed < numPits) {
      const r = Math.floor(Math.random() * this.rows);
      const c = Math.floor(Math.random() * this.cols);
      if ((r === 0 && c === 0) || this.grid[r][c].hasPit) continue;
      this.grid[r][c].hasPit = true;
      placed++;
    }

    // Place Wumpus
    let wr, wc;
    do {
      wr = Math.floor(Math.random() * this.rows);
      wc = Math.floor(Math.random() * this.cols);
    } while ((wr === 0 && wc === 0) || this.grid[wr][wc].hasPit);
    this.grid[wr][wc].hasWumpus = true;
    this.wumpusPos = { r: wr, c: wc };

    // Place Gold
    let gr, gc;
    do {
      gr = Math.floor(Math.random() * this.rows);
      gc = Math.floor(Math.random() * this.cols);
    } while (gr === 0 && gc === 0);
    this.grid[gr][gc].hasGold = true;
    this.goldPos = { r: gr, c: gc };

    // Pre-compute breezes and stenches
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        const nbrs = this._neighbors(r, c);
        if (nbrs.some(([nr, nc]) => this.grid[nr][nc].hasPit)) {
          this.grid[r][c].hasBreeze = true;
        }
        if (nbrs.some(([nr, nc]) => this.grid[nr][nc].hasWumpus)) {
          this.grid[r][c].hasStench = true;
        }
      }
    }
  }

  _neighbors(r, c) {
    const nbrs = [];
    if (r > 0) nbrs.push([r - 1, c]);
    if (r < this.rows - 1) nbrs.push([r + 1, c]);
    if (c > 0) nbrs.push([r, c - 1]);
    if (c < this.cols - 1) nbrs.push([r, c + 1]);
    return nbrs;
  }

  // FIX: Separate init visit (no moves counter increment) vs normal visit
  _visitCellInit(r, c) {
    this.agentPos = { r, c };
    this.visited.add(`${r}_${c}`);
    this._processPercepts(r, c);
  }

  _visitCell(r, c) {
    const cell = this.grid[r][c];
    const key = `${r}_${c}`;
    this.agentPos = { r, c };
    this.visited.add(key);
    this.frontier.delete(key);
    this.moves++;  // Only incremented on agent-driven moves

    // Check for gold
    if (cell.hasGold && !this.goldFound) {
      this.goldFound = true;
    }

    // Check for death
    if (cell.hasPit || cell.hasWumpus) {
      this.alive = false;
      this.dangerCells.add(key);
      return;
    }

    cell.state = 'visited';
    this.safeCells.add(key);
    this._processPercepts(r, c);
  }

  _processPercepts(r, c) {
    const cell = this.grid[r][c];
    const key = `${r}_${c}`;
    cell.state = 'visited';
    this.safeCells.add(key);

    const percepts = [];

    if (cell.hasBreeze) {
      percepts.push('BREEZE');
      this.kb.tell([`B_${r}_${c}`], `B_{${r},${c}} (sensed breeze)`);
      this._logKB('TELL', `B_{${r},${c}} — breeze sensed`);
      const nbrs = this._neighbors(r, c);
      this.kb.tellBreezeRule(r, c, nbrs);
      this._logKB('TELL', `B_{${r},${c}} ⟺ (${nbrs.map(([nr,nc])=>`P_{${nr},${nc}}`).join(' ∨ ')})`);
    } else {
      this.kb.tell([`~B_${r}_${c}`], `~B_{${r},${c}} (no breeze)`);
      this._logKB('TELL', `~B_{${r},${c}} — no breeze`);
      const nbrs = this._neighbors(r, c);
      for (const [nr, nc] of nbrs) {
        const added = this.kb.tell([`~P_${nr}_${nc}`], `~P_{${nr},${nc}}`);
        if (added) this._logKB('TELL', `~P_{${nr},${nc}} — inferred safe from no-breeze`);
      }
    }

    if (cell.hasStench) {
      percepts.push('STENCH');
      this.kb.tell([`S_${r}_${c}`], `S_{${r},${c}} (sensed stench)`);
      this._logKB('TELL', `S_{${r},${c}} — stench sensed`);
      const nbrs = this._neighbors(r, c);
      this.kb.tellStenchRule(r, c, nbrs);
      this._logKB('TELL', `S_{${r},${c}} ⟺ (${nbrs.map(([nr,nc])=>`W_{${nr},${nc}}`).join(' ∨ ')})`);
    } else {
      this.kb.tell([`~S_${r}_${c}`], `~S_{${r},${c}} (no stench)`);
      this._logKB('TELL', `~S_{${r},${c}} — no stench`);
      const nbrs = this._neighbors(r, c);
      for (const [nr, nc] of nbrs) {
        const added = this.kb.tell([`~W_${nr}_${nc}`], `~W_{${nr},${nc}}`);
        if (added) this._logKB('TELL', `~W_{${nr},${nc}} — inferred safe from no-stench`);
      }
    }

    if (cell.hasGold) percepts.push('GLITTER');
    cell.percepts = percepts;

    // Add unvisited neighbors to frontier
    for (const [nr, nc] of this._neighbors(r, c)) {
      const nkey = `${nr}_${nc}`;
      if (!this.visited.has(nkey)) {
        this.frontier.add(nkey);
      }
    }

    this._inferFrontier();
  }

  _inferFrontier() {
    for (const key of this.frontier) {
      const [r, c] = key.split('_').map(Number);
      const cellState = this._queryCellSafety(r, c);
      if (cellState === 'safe') {
        this.safeCells.add(key);
        this.grid[r][c].state = 'safe';
      } else if (cellState === 'danger') {
        this.dangerCells.add(key);
        this.grid[r][c].state = 'danger';
      } else {
        this.grid[r][c].state = 'suspect';
      }
    }
  }

  _queryCellSafety(r, c) {
    const notPit = `~P_${r}_${c}`;
    const notWumpus = `~W_${r}_${c}`;

    const pitRes = this.kb.ask(notPit);
    this._logResolution(`ASK ~P_{${r},${c}}`, pitRes.entailed ? '✓ SAFE from pits' : '? uncertain', pitRes.steps);

    const wRes = this.kb.ask(notWumpus);
    this._logResolution(`ASK ~W_{${r},${c}}`, wRes.entailed ? '✓ SAFE from wumpus' : '? uncertain', wRes.steps);

    if (pitRes.entailed && wRes.entailed) return 'safe';

    const isPit = this.kb.ask(`P_${r}_${c}`);
    const isWumpus = this.kb.ask(`W_${r}_${c}`);
    if (isPit.entailed || isWumpus.entailed) return 'danger';

    return 'unknown';
  }

  chooseNextMove() {
    // Priority 1: unvisited safe frontier cells
    for (const key of this.safeCells) {
      if (!this.visited.has(key)) {
        const [r, c] = key.split('_').map(Number);
        return { r, c };
      }
    }
    // Priority 2: unknown frontier cells (risky but necessary)
    for (const key of this.frontier) {
      if (!this.visited.has(key) && !this.dangerCells.has(key)) {
        const [r, c] = key.split('_').map(Number);
        return { r, c };
      }
    }
    return null;
  }

  step() {
    if (!this.alive) return { done: true, reason: 'dead' };
    if (this.goldFound) return { done: true, reason: 'gold' };

    const next = this.chooseNextMove();
    if (!next) return { done: true, reason: 'stuck' };

    this._visitCell(next.r, next.c);

    if (!this.alive) return { done: true, reason: 'dead' };
    if (this.goldFound) return { done: true, reason: 'gold' };

    return { done: false };
  }

  getCellDisplayState(r, c) {
    const key = `${r}_${c}`;
    const cell = this.grid[r][c];
    if (this.agentPos.r === r && this.agentPos.c === c) return 'agent-here';
    if (this.visited.has(key)) return 'visited';
    if (this.dangerCells.has(key)) return 'danger';
    if (this.safeCells.has(key)) return 'safe';
    if (this.frontier.has(key)) return cell.state || 'suspect';
    return 'unknown';
  }

  getCurrentPercepts() {
    const cell = this.grid[this.agentPos.r][this.agentPos.c];
    return cell.percepts || [];
  }

  _logKB(type, msg) {
    this.kbLog.push({ type, msg, step: this.kb.inferenceSteps });
    if (this.kbLog.length > 100) this.kbLog.shift();
  }

  _logResolution(query, result, steps) {
    this.resolutionLog.push({ query, result, steps });
    if (this.resolutionLog.length > 50) this.resolutionLog.shift();
  }
}

// Export globals for app.js
window.WumpusWorld = WumpusWorld;
window.KnowledgeBase = KnowledgeBase;