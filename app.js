let world = null;
let simulationInterval = null;
let isRunning = false;
let episodeCount = 0;

const SPEED_MAP = { 1: 1200, 2: 800, 3: 500, 4: 250, 5: 100 };

//  INITIALIZATION 
function startSimulation() {
  const rows = parseInt(document.getElementById('rowsSlider').value);
  const cols = parseInt(document.getElementById('colsSlider').value);

  resetInterval();
  world = new WumpusWorld(rows, cols);
  episodeCount++;
  document.getElementById('episodeCount').textContent = episodeCount;

  renderGrid();
  updateMetrics();
  updatePercepts();
  renderKBLog();
  renderResLog();

  setStatus('RUNNING');
  document.getElementById('startBtn').disabled = true;
  document.getElementById('stepBtn').disabled = false;

  const speed = parseInt(document.getElementById('speedSlider').value);
  const delay = SPEED_MAP[speed];

  isRunning = true;
  simulationInterval = setInterval(() => {
    const result = world.step();
    renderGrid();
    updateMetrics();
    updatePercepts();
    renderKBLog();
    renderResLog();

    if (result.done) {
      resetInterval();
      endSimulation(result.reason);
    }
  }, delay);
}

function stepSimulation() {
  if (!world) return;
  resetInterval();
  isRunning = false;

  const result = world.step();
  renderGrid();
  updateMetrics();
  updatePercepts();
  renderKBLog();
  renderResLog();

  if (result.done) {
    endSimulation(result.reason);
  }
}

function resetSimulation() {
  resetInterval();
  world = null;
  isRunning = false;
  episodeCount = 0;
  document.getElementById('episodeCount').textContent = '0';
  document.getElementById('wumpusGrid').innerHTML = '';
  document.getElementById('startBtn').disabled = false;
  document.getElementById('stepBtn').disabled = true;
  document.getElementById('agentStatus').textContent = 'IDLE';
  document.getElementById('agentCoord').textContent = '(1,1)';
  document.getElementById('kbCount').textContent = '0';
  document.getElementById('safeCellCount').textContent = '0';
  document.getElementById('visitedCount').textContent = '0';
  document.getElementById('inferenceSteps').textContent = '0';
  document.getElementById('resolutionCalls').textContent = '0';
  document.getElementById('movesCount').textContent = '0';
  document.getElementById('goldFound').textContent = 'NO';
  document.getElementById('inferenceBar').style.width = '0%';
  document.getElementById('resolutionBar').style.width = '0%';
  document.getElementById('movesBar').style.width = '0%';
  document.getElementById('perceptList').innerHTML = '<span class="percept-none">— none —</span>';
  document.getElementById('kbLog').innerHTML = '<div class="log-placeholder">Awaiting agent start...</div>';
  document.getElementById('resLog').innerHTML = '<div class="log-placeholder">No resolutions yet...</div>';

  setStatus('IDLE');

  // Redraw placeholder grid
  const container = document.getElementById('wumpusGrid');
  const rows = parseInt(document.getElementById('rowsSlider').value);
  const cols = parseInt(document.getElementById('colsSlider').value);
  container.style.gridTemplateColumns = `repeat(${cols}, 1fr)`;
  for (let i = 0; i < rows * cols; i++) {
    const cell = document.createElement('div');
    cell.className = 'cell';
    cell.style.width = '80px';
    cell.style.height = '80px';
    cell.innerHTML = '<span class="cell-coord"></span><span class="cell-icon" style="font-size:1rem;color:var(--text3)">?</span>';
    container.appendChild(cell);
  }
}

function endSimulation(reason) {
  document.getElementById('startBtn').disabled = false;
  document.getElementById('stepBtn').disabled = true;

  const messages = {
    gold: '🏆 GOLD FOUND!',
    dead: '💀 AGENT DIED',
    stuck: '🔒 AGENT STUCK'
  };
  setStatus(messages[reason] || 'DONE');
}

function resetInterval() {
  if (simulationInterval) {
    clearInterval(simulationInterval);
    simulationInterval = null;
  }
}

function setStatus(txt) {
  const el = document.getElementById('agentStatus');
  el.textContent = txt;
  el.style.color = txt.includes('FOUND') ? '#ffd700' :
                   txt.includes('DIED') || txt.includes('DEAD') ? '#ff4d6d' :
                   txt === 'RUNNING' ? '#00ff9d' : '#00d4ff';
}

// GRID RENDERING
function renderGrid() {
  if (!world) return;
  const container = document.getElementById('wumpusGrid');
  const { rows, cols } = world;

  container.style.gridTemplateColumns = `repeat(${cols}, 1fr)`;

  const wrapper = document.querySelector('.grid-wrapper');
  const maxW = wrapper.clientWidth - 40;
  const maxH = wrapper.clientHeight - 40;
  const cellSize = Math.min(90, Math.floor(Math.min(maxW / cols, maxH / rows)));

  if (container.children.length !== rows * cols) {
    container.innerHTML = '';
    for (let r = 0; r < rows; r++) {
      for (let c = 0; c < cols; c++) {
        const cell = document.createElement('div');
        cell.className = 'cell';
        cell.id = `cell_${r}_${c}`;
        cell.style.width = cellSize + 'px';
        cell.style.height = cellSize + 'px';
        container.appendChild(cell);
      }
    }
  }

  for (let r = rows - 1; r >= 0; r--) {
    for (let c = 0; c < cols; c++) {
      updateCell(r, c, cellSize);
    }
  }

  const { r: ar, c: ac } = world.agentPos;
  document.getElementById('agentCoord').textContent = `(${ac + 1},${ar + 1})`;
}

function updateCell(r, c, cellSize) {
  const el = document.getElementById(`cell_${r}_${c}`);
  if (!el) return;

  const displayState = world.getCellDisplayState(r, c);
  const cell = world.grid[r][c];
  const key = `${r}_${c}`;

  const prevClass = el.dataset.state;
  el.className = `cell ${displayState}`;
  el.dataset.state = displayState;

  if (prevClass !== displayState) {
    el.classList.add('cell-reveal');
    setTimeout(() => el.classList.remove('cell-reveal'), 400);
  }

  el.style.width = cellSize + 'px';
  el.style.height = cellSize + 'px';

  let icon = '';
  let label = '';

  if (displayState === 'agent-here') {
    icon = '🤖'; label = 'AGENT';
  } else if (displayState === 'danger') {
    if (cell.hasPit && cell.hasWumpus) { icon = '☠️'; label = 'PIT+WMPS'; }
    else if (cell.hasPit)              { icon = '🕳️'; label = 'PIT'; }
    else if (cell.hasWumpus)           { icon = '👾'; label = 'WUMPUS'; }
    else                               { icon = '⚠️'; label = 'DANGER'; }
  } else if (displayState === 'safe') {
    icon = '✅'; label = 'SAFE';
  } else if (displayState === 'suspect') {
    icon = '❓'; label = 'SUSPECT';
  } else if (displayState === 'visited') {
    icon = cell.hasGold && world.goldFound ? '🏆' : '·';
    label = 'VISITED';
  } else {
    icon = '?'; label = 'UNKNOWN';
  }

  const percepts = [];
  if (world.visited.has(key)) {
    if (cell.hasBreeze) percepts.push('<span class="cell-percept-dot breeze"></span>');
    if (cell.hasStench) percepts.push('<span class="cell-percept-dot stench"></span>');
  }

  el.innerHTML = `
    <span class="cell-coord">${c + 1},${r + 1}</span>
    <span class="cell-icon">${icon}</span>
    <span class="cell-label">${label}</span>
    ${percepts.length ? `<div class="cell-percepts">${percepts.join('')}</div>` : ''}
  `;
}

//  METRICS UPDATE 
function updateMetrics() {
  if (!world) return;
  const kb = world.kb;

  const steps = kb.inferenceSteps;
  const res   = kb.resolutionCalls;
  const moves = world.moves;

  document.getElementById('inferenceSteps').textContent = steps;
  document.getElementById('resolutionCalls').textContent = res;
  document.getElementById('movesCount').textContent = moves;
  document.getElementById('goldFound').textContent = world.goldFound ? '✓ FOUND' : 'NOT YET';
  document.getElementById('kbCount').textContent = kb.clauses.length;
  document.getElementById('safeCellCount').textContent = world.safeCells.size;
  document.getElementById('visitedCount').textContent = world.visited.size;

  document.getElementById('inferenceBar').style.width = Math.min(100, (steps / 300) * 100) + '%';
  document.getElementById('resolutionBar').style.width = Math.min(100, (res / 100) * 100) + '%';
  document.getElementById('movesBar').style.width = Math.min(100, (moves / (world.rows * world.cols)) * 100) + '%';

  if (world.goldFound) {
    document.getElementById('goldFound').style.color = '#ffd700';
  }
}

//  PERCEPT DISPLAY 
function updatePercepts() {
  if (!world) return;
  const percepts = world.getCurrentPercepts();
  const el = document.getElementById('perceptList');

  if (percepts.length === 0) {
    el.innerHTML = '<span class="percept-none">— none —</span>';
    return;
  }

  el.innerHTML = percepts.map(p =>
    `<span class="percept-tag ${p.toLowerCase()}">${p}</span>`
  ).join('');
}

//KB LOG RENDERING 
function renderKBLog() {
  if (!world) return;
  const el = document.getElementById('kbLog');
  const logs = world.kbLog.slice(-20);

  if (logs.length === 0) {
    el.innerHTML = '<div class="log-placeholder">KB empty...</div>';
    return;
  }

  el.innerHTML = logs.map(entry => `
    <div class="log-entry">
      <span class="log-${entry.type.toLowerCase()}">[${entry.type}]</span>
      ${escapeHtml(entry.msg)}
    </div>
  `).join('');
  el.scrollTop = el.scrollHeight;
}

function renderResLog() {
  if (!world) return;
  const el = document.getElementById('resLog');
  const logs = world.resolutionLog.slice(-15);

  if (logs.length === 0) {
    el.innerHTML = '<div class="log-placeholder">No resolutions yet...</div>';
    return;
  }

  el.innerHTML = logs.map(entry => `
    <div class="log-entry">
      <span class="log-ask">${escapeHtml(entry.query)}</span>
      → <span class="log-res">${escapeHtml(entry.result)}</span>
      <span class="log-time">(${entry.steps}steps)</span>
    </div>
  `).join('');
  el.scrollTop = el.scrollHeight;
}

function escapeHtml(str) {
  return String(str)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}

// ─── INIT
window.addEventListener('load', () => {
  // Don't draw placeholder — just set grid dimensions visually
  const container = document.getElementById('wumpusGrid');
  const rows = parseInt(document.getElementById('rowsSlider').value);
  const cols = parseInt(document.getElementById('colsSlider').value);
  container.style.gridTemplateColumns = `repeat(${cols}, 1fr)`;

  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const cell = document.createElement('div');
      cell.className = 'cell';
      cell.id = `cell_${r}_${c}`;   // ✅ Give proper IDs
      cell.style.width = '80px';
      cell.style.height = '80px';
      cell.innerHTML = '<span class="cell-icon" style="font-size:1rem;color:var(--text3)">?</span>';
      container.appendChild(cell);
    }
  }
});