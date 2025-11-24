// ========================================
// CSP Solver Class
// ========================================
class CSP {
  constructor(variables, domains, neighbors, constraintFunc) {
    this.variables = variables;
    this.initialDomains = JSON.parse(JSON.stringify(domains));
    this.domains = JSON.parse(JSON.stringify(domains));
    this.neighbors = neighbors;
    this.constraintFunc = constraintFunc;
    this.assignments = {};
  }

  reset() {
    this.domains = JSON.parse(JSON.stringify(this.initialDomains));
    this.assignments = {};
  }

  // Node Consistency
  *nodeConsistency() {
    for (const variable of this.variables) {
      yield { type: 'process_node', variable };
      
      // In basic CSP, no unary constraints, but we show the process
      const before = [...this.domains[variable]];
      yield { type: 'node_done', variable, before, after: [...this.domains[variable]] };
      
      if (this.domains[variable].length === 0) {
        yield { type: 'failure', variable };
        return false;
      }
    }
    yield { type: 'nc_complete' };
    return true;
  }

  // Edge Consistency (revise all edges once)
  *edgeConsistency() {
    for (const xi of this.variables) {
      for (const xj of this.neighbors[xi]) {
        yield { type: 'process_edge', xi, xj };
        
        const revised = yield* this.revise(xi, xj);
        
        if (this.domains[xi].length === 0) {
          yield { type: 'failure', variable: xi };
          return false;
        }
      }
    }
    yield { type: 'ec_complete' };
    return true;
  }

  // Arc Consistency (AC-3)
  *ac3(queue = null) {
    const workQueue = queue || [];
    
    if (!queue) {
      for (const xi of this.variables) {
        for (const xj of this.neighbors[xi]) {
          workQueue.push([xi, xj]);
        }
      }
    }

    while (workQueue.length > 0) {
      const [xi, xj] = workQueue.shift();
      yield { type: 'process_arc', xi, xj };

      const revised = yield* this.revise(xi, xj);

      if (revised) {
        if (this.domains[xi].length === 0) {
          yield { type: 'failure', variable: xi };
          return false;
        }

        for (const xk of this.neighbors[xi]) {
          if (xk !== xj) {
            workQueue.push([xk, xi]);
          }
        }
      }
    }

    yield { type: 'ac3_complete' };
    return true;
  }

  *revise(xi, xj) {
    let revised = false;
    const toRemove = [];

    for (const vi of this.domains[xi]) {
      let satisfies = false;
      
      for (const vj of this.domains[xj]) {
        if (this.constraintFunc(xi, xj, vi, vj)) {
          satisfies = true;
          break;
        }
      }

      if (!satisfies) {
        toRemove.push(vi);
        revised = true;
      }
    }

    for (const val of toRemove) {
      this.domains[xi] = this.domains[xi].filter(v => v !== val);
      yield { type: 'remove_value', variable: xi, value: val, reason: xj };
    }

    return revised;
  }

  // Backtracking Search
  *backtrackingSearch(useAC3 = false) {
    yield* this.backtrack(useAC3);
  }

  *backtrack(useAC3) {
    if (Object.keys(this.assignments).length === this.variables.length) {
      yield { type: 'solution', assignments: { ...this.assignments } };
      return true;
    }

    const unassigned = this.variables.filter(v => !(v in this.assignments));
    // MRV heuristic
    unassigned.sort((a, b) => this.domains[a].length - this.domains[b].length);
    const variable = unassigned[0];

    yield { type: 'select_variable', variable };

    for (const value of [...this.domains[variable]]) {
      yield { type: 'try_value', variable, value };

      if (this.isConsistent(variable, value)) {
        this.assignments[variable] = value;
        const savedDomains = JSON.parse(JSON.stringify(this.domains));

        // Forward checking
        let consistent = yield* this.forwardCheck(variable, value);

        if (consistent && useAC3) {
          const queue = [];
          for (const neighbor of this.neighbors[variable]) {
            if (!(neighbor in this.assignments)) {
              queue.push([neighbor, variable]);
            }
          }
          consistent = yield* this.ac3(queue);
        }

        if (consistent) {
          const result = yield* this.backtrack(useAC3);
          if (result) return true;
        }

        // Backtrack
        delete this.assignments[variable];
        this.domains = savedDomains;
        yield { type: 'backtrack', variable };
      } else {
        yield { type: 'conflict', variable, value };
      }
    }

    return false;
  }

  isConsistent(variable, value) {
    for (const neighbor of this.neighbors[variable]) {
      if (neighbor in this.assignments) {
        if (!this.constraintFunc(variable, neighbor, value, this.assignments[neighbor])) {
          return false;
        }
      }
    }
    return true;
  }

  *forwardCheck(variable, value) {
    for (const neighbor of this.neighbors[variable]) {
      if (!(neighbor in this.assignments)) {
        const before = [...this.domains[neighbor]];
        this.domains[neighbor] = this.domains[neighbor].filter(v =>
          this.constraintFunc(neighbor, variable, v, value)
        );

        if (this.domains[neighbor].length !== before.length) {
          yield { type: 'forward_check', variable: neighbor, before, after: [...this.domains[neighbor]] };
        }

        if (this.domains[neighbor].length === 0) {
          return false;
        }
      }
    }
    return true;
  }
}

// ========================================
// Visualization & UI Controller
// ========================================
class CSPVisualizer {
  constructor() {
    this.canvas = document.getElementById('canvas');
    this.csp = null;
    this.generator = null;
    this.isRunning = false;
    this.runInterval = null;
    this.nodes = [];
    this.edges = [];
    this.customNodes = [];
    this.customEdges = [];
    this.selectedNode = null;
    
    this.setupEventListeners();
    this.initializeProblem();
  }

  setupEventListeners() {
    document.getElementById('problemType').addEventListener('change', () => this.handleProblemTypeChange());
    document.getElementById('mapSelect').addEventListener('change', () => this.initializeProblem());
    document.getElementById('queensSize').addEventListener('input', (e) => {
      document.getElementById('queensValue').textContent = e.target.value;
      this.initializeProblem();
    });
    document.getElementById('domainInput').addEventListener('change', () => this.initializeProblem());
    document.getElementById('resetBtn').addEventListener('click', () => this.reset());
    document.getElementById('stepBtn').addEventListener('click', () => this.step());
    document.getElementById('runBtn').addEventListener('click', () => this.run());
    document.getElementById('stopBtn').addEventListener('click', () => this.stop());
    document.getElementById('clearCanvas').addEventListener('click', () => this.clearCustomCanvas());
    document.getElementById('speedSlider').addEventListener('input', (e) => {
      document.getElementById('speedValue').textContent = e.target.value + 'ms';
    });

    this.canvas.addEventListener('click', (e) => this.handleCanvasClick(e));
  }

  handleProblemTypeChange() {
    const type = document.getElementById('problemType').value;
    document.getElementById('mapOptions').classList.toggle('hidden', type !== 'map');
    document.getElementById('queensOptions').classList.toggle('hidden', type !== 'nqueens');
    document.getElementById('customMapOptions').classList.toggle('hidden', type !== 'custom');
    
    if (type === 'nqueens') {
      document.getElementById('domainInput').value = '1,2,3,4';
    } else {
      document.getElementById('domainInput').value = 'Red,Green,Blue,Yellow';
    }
    
    this.initializeProblem();
  }

  initializeProblem() {
    const type = document.getElementById('problemType').value;
    
    if (type === 'map') {
      this.initializeMapProblem();
    } else if (type === 'nqueens') {
      this.initializeNQueensProblem();
    } else if (type === 'custom') {
      this.initializeCustomProblem();
    }
    
    this.reset();
  }

  initializeMapProblem() {
    const mapType = document.getElementById('mapSelect').value;
    const maps = {
      australia: {
        nodes: [
          { id: 'WA', x: 100, y: 250 },
          { id: 'NT', x: 200, y: 150 },
          { id: 'SA', x: 250, y: 280 },
          { id: 'Q', x: 380, y: 180 },
          { id: 'NSW', x: 420, y: 320 },
          { id: 'V', x: 380, y: 400 },
          { id: 'T', x: 500, y: 480 }
        ],
        edges: [
          ['WA', 'NT'], ['WA', 'SA'], ['NT', 'SA'], ['NT', 'Q'],
          ['SA', 'Q'], ['SA', 'NSW'], ['SA', 'V'], ['Q', 'NSW'], ['NSW', 'V']
        ]
      },
      usa: {
        nodes: [
          { id: 'A', x: 150, y: 150 },
          { id: 'B', x: 350, y: 120 },
          { id: 'C', x: 550, y: 150 },
          { id: 'D', x: 200, y: 350 },
          { id: 'E', x: 400, y: 320 },
          { id: 'F', x: 600, y: 350 }
        ],
        edges: [
          ['A', 'B'], ['B', 'C'], ['A', 'D'], ['B', 'D'],
          ['B', 'E'], ['C', 'E'], ['D', 'E'], ['E', 'F'], ['C', 'F']
        ]
      },
      europe: {
        nodes: [
          { id: 'FR', x: 200, y: 300 },
          { id: 'DE', x: 350, y: 200 },
          { id: 'ES', x: 120, y: 400 },
          { id: 'IT', x: 350, y: 380 },
          { id: 'CH', x: 320, y: 300 },
          { id: 'BE', x: 280, y: 180 }
        ],
        edges: [
          ['FR', 'DE'], ['FR', 'ES'], ['FR', 'IT'], ['FR', 'CH'], ['FR', 'BE'],
          ['DE', 'CH'], ['DE', 'BE'], ['IT', 'CH'], ['CH', 'DE']
        ]
      }
    };

    const map = maps[mapType];
    this.nodes = map.nodes;
    this.edges = map.edges;
    this.createCSP();
  }

  initializeNQueensProblem() {
    const n = parseInt(document.getElementById('queensSize').value);
    this.nodes = [];
    this.edges = [];

    const spacing = 600 / (n + 1);
    for (let i = 0; i < n; i++) {
      this.nodes.push({
        id: `Q${i + 1}`,
        x: spacing * (i + 1),
        y: 300
      });
    }

    // All queens constrain each other
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        this.edges.push([`Q${i + 1}`, `Q${j + 1}`]);
      }
    }

    this.createCSP();
  }

  initializeCustomProblem() {
    this.nodes = [...this.customNodes];
    this.edges = [...this.customEdges];
    this.createCSP();
  }

  createCSP() {
    const domainInput = document.getElementById('domainInput').value;
    const domain = domainInput.split(',').map(s => s.trim()).filter(s => s);
    
    const variables = this.nodes.map(n => n.id);
    const domains = {};
    variables.forEach(v => domains[v] = [...domain]);

    const neighbors = {};
    variables.forEach(v => neighbors[v] = []);
    this.edges.forEach(([a, b]) => {
      if (!neighbors[a].includes(b)) neighbors[a].push(b);
      if (!neighbors[b].includes(a)) neighbors[b].push(a);
    });

    const constraintFunc = (xi, xj, vi, vj) => {
      // N-Queens constraint
      if (xi.startsWith('Q') && xj.startsWith('Q')) {
        const i = parseInt(xi.substring(1));
        const j = parseInt(xj.substring(1));
        const viNum = parseInt(vi);
        const vjNum = parseInt(vj);
        
        if (viNum === vjNum) return false; // Same column
        if (Math.abs(viNum - vjNum) === Math.abs(i - j)) return false; // Diagonal
        return true;
      }
      
      // Map coloring constraint
      return vi !== vj;
    };

    this.csp = new CSP(variables, domains, neighbors, constraintFunc);
    this.drawGraph();
  }

  drawGraph() {
    this.canvas.innerHTML = '';

    // Draw edges
    this.edges.forEach(([a, b]) => {
      const nodeA = this.nodes.find(n => n.id === a);
      const nodeB = this.nodes.find(n => n.id === b);
      if (!nodeA || !nodeB) return;

      const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
      line.setAttribute('x1', nodeA.x);
      line.setAttribute('y1', nodeA.y);
      line.setAttribute('x2', nodeB.x);
      line.setAttribute('y2', nodeB.y);
      line.classList.add('edge');
      line.setAttribute('data-edge', `${a}-${b}`);
      this.canvas.appendChild(line);
    });

    // Draw nodes
    this.nodes.forEach(node => {
      const g = document.createElementNS('http://www.w3.org/2000/svg', 'g');
      g.classList.add('node');
      g.setAttribute('data-id', node.id);

      const circle = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
      circle.setAttribute('cx', node.x);
      circle.setAttribute('cy', node.y);
      circle.setAttribute('r', 30);
      circle.setAttribute('fill', '#ffffff');
      circle.setAttribute('stroke', '#e8dcc4');

      const text = document.createElementNS('http://www.w3.org/2000/svg', 'text');
      text.setAttribute('x', node.x);
      text.setAttribute('y', node.y + 5);
      text.textContent = node.id;

      const domainText = document.createElementNS('http://www.w3.org/2000/svg', 'text');
      domainText.setAttribute('x', node.x);
      domainText.setAttribute('y', node.y + 50);
      domainText.classList.add('domain-text');
      domainText.setAttribute('text-anchor', 'middle');

      g.appendChild(circle);
      g.appendChild(text);
      g.appendChild(domainText);
      this.canvas.appendChild(g);
    });

    this.updateVisualization();
  }

  updateVisualization(highlight = null) {
    this.nodes.forEach(node => {
      const g = this.canvas.querySelector(`g[data-id="${node.id}"]`);
      if (!g) return;

      const circle = g.querySelector('circle');
      const domainText = g.querySelector('.domain-text');
      
      g.classList.remove('processing');

      if (this.csp.assignments[node.id]) {
        const value = this.csp.assignments[node.id];
        circle.setAttribute('fill', this.getColor(value));
        circle.setAttribute('stroke', '#2c3e50');
        domainText.textContent = `✓ ${value}`;
      } else {
        circle.setAttribute('fill', '#ffffff');
        circle.setAttribute('stroke', '#e8dcc4');
        const domain = this.csp.domains[node.id];
        domainText.textContent = domain ? domain.join(', ') : '';
      }
    });

    // Clear edge highlights
    this.canvas.querySelectorAll('.edge').forEach(edge => {
      edge.classList.remove('active');
    });

    if (highlight) {
      if (highlight.type === 'process_arc' || highlight.type === 'process_edge') {
        const edge = this.canvas.querySelector(`line[data-edge="${highlight.xi}-${highlight.xj}"], line[data-edge="${highlight.xj}-${highlight.xi}"]`);
        if (edge) edge.classList.add('active');
      }
      
      if (highlight.type === 'process_node' || highlight.type === 'select_variable') {
        const g = this.canvas.querySelector(`g[data-id="${highlight.variable}"]`);
        if (g) g.classList.add('processing');
      }
    }
  }

  getColor(value) {
    // Try to return the value if it's a valid color
    const colors = {
      'Red': '#ff6b6b',
      'Green': '#51cf66',
      'Blue': '#4dabf7',
      'Yellow': '#ffd93d',
      'Orange': '#ff922b',
      'Purple': '#cc5de8',
      'Pink': '#f06595',
      'Cyan': '#22b8cf'
    };
    
    return colors[value] || value;
  }

  reset() {
    this.stop();
    if (this.csp) {
      this.csp.reset();
    }
    this.generator = null;
    document.getElementById('solutionSection').classList.add('hidden');
    this.updateStatus('Ready');
    this.log('System reset');
    this.updateVisualization();
  }

  step() {
    if (!this.csp) {
      this.log('No problem loaded');
      return;
    }

    if (!this.generator) {
      const algorithm = document.getElementById('algorithmSelect').value;
      this.generator = this.getAlgorithmGenerator(algorithm);
      this.updateStatus('Running');
    }

    const result = this.generator.next();
    
    if (result.done) {
      this.updateStatus('Complete');
      this.generator = null;
    } else {
      this.handleEvent(result.value);
    }
  }

  run() {
    if (this.isRunning) return;
    
    this.isRunning = true;
    const speed = parseInt(document.getElementById('speedSlider').value);
    
    this.runInterval = setInterval(() => {
      this.step();
      
      if (!this.generator) {
        this.stop();
      }
    }, speed);
  }

  stop() {
    if (this.runInterval) {
      clearInterval(this.runInterval);
      this.runInterval = null;
    }
    this.isRunning = false;
  }

  getAlgorithmGenerator(algorithm) {
    switch (algorithm) {
      case 'node':
        return this.csp.nodeConsistency();
      case 'edge':
        return this.csp.edgeConsistency();
      case 'ac3':
        return this.csp.ac3();
      case 'backtrack':
        return this.csp.backtrackingSearch(false);
      case 'backtrack_ac3':
        return this.csp.backtrackingSearch(true);
      default:
        return this.csp.ac3();
    }
  }

  handleEvent(event) {
    let message = '';
    
    switch (event.type) {
      case 'process_node':
        message = `Processing node ${event.variable}`;
        break;
      case 'process_edge':
        message = `Checking edge ${event.xi} ↔ ${event.xj}`;
        break;
      case 'process_arc':
        message = `Processing arc ${event.xi} → ${event.xj}`;
        break;
      case 'remove_value':
        message = `Removed ${event.value} from ${event.variable}`;
        break;
      case 'select_variable':
        message = `Selected variable ${event.variable}`;
        break;
      case 'try_value':
        message = `Trying ${event.variable} = ${event.value}`;
        break;
      case 'conflict':
        message = `Conflict at ${event.variable} = ${event.value}`;
        break;
      case 'backtrack':
        message = `Backtracking from ${event.variable}`;
        break;
      case 'solution':
        message = '✓ Solution found!';
        this.displaySolution(event.assignments);
        break;
      case 'failure':
        message = `✗ Failed at ${event.variable}`;
        break;
      case 'nc_complete':
        message = 'Node consistency complete';
        break;
      case 'ec_complete':
        message = 'Edge consistency complete';
        break;
      case 'ac3_complete':
        message = 'AC-3 complete';
        break;
    }
    
    if (message) {
      this.log(message);
    }
    
    this.updateVisualization(event);
  }

  displaySolution(assignments) {
    const section = document.getElementById('solutionSection');
    const display = document.getElementById('solutionDisplay');
    
    section.classList.remove('hidden');
    display.innerHTML = '';
    
    Object.entries(assignments).forEach(([variable, value]) => {
      const item = document.createElement('div');
      item.className = 'solution-item';
      
      const varSpan = document.createElement('span');
      varSpan.className = 'solution-var';
      varSpan.textContent = variable;
      
      const valSpan = document.createElement('span');
      valSpan.className = 'solution-val';
      valSpan.textContent = value;
      valSpan.style.background = this.getColor(value);
      
      item.appendChild(varSpan);
      item.appendChild(valSpan);
      display.appendChild(item);
    });
  }

  log(message) {
    const logContent = document.getElementById('logContent');
    const entry = document.createElement('div');
    entry.className = 'log-entry';
    
    const time = new Date().toLocaleTimeString();
    entry.innerHTML = `<span class="log-time">[${time}]</span> ${message}`;
    
    logContent.insertBefore(entry, logContent.firstChild);
    
    // Keep only last 50 entries
    while (logContent.children.length > 50) {
      logContent.removeChild(logContent.lastChild);
    }
  }

  updateStatus(status) {
    document.getElementById('statusText').textContent = status;
  }

  handleCanvasClick(e) {
    if (document.getElementById('problemType').value !== 'custom') return;

    const rect = this.canvas.getBoundingClientRect();
    const x = ((e.clientX - rect.left) / rect.width) * 800;
    const y = ((e.clientY - rect.top) / rect.height) * 600;

    // Check if clicked on existing node
    let clickedNode = null;
    for (const node of this.customNodes) {
      const dist = Math.sqrt((node.x - x) ** 2 + (node.y - y) ** 2);
      if (dist < 30) {
        clickedNode = node;
        break;
      }
    }

    if (clickedNode) {
      if (this.selectedNode && this.selectedNode !== clickedNode) {
        // Create edge
        const edge = [this.selectedNode.id, clickedNode.id];
        const reverseEdge = [clickedNode.id, this.selectedNode.id];
        
        const exists = this.customEdges.some(e => 
          (e[0] === edge[0] && e[1] === edge[1]) || 
          (e[0] === edge[1] && e[1] === edge[0])
        );
        
        if (!exists) {
          this.customEdges.push(edge);
          this.log(`Added edge ${edge[0]} - ${edge[1]}`);
        }
        
        this.selectedNode = null;
        this.initializeProblem();
      } else {
        this.selectedNode = clickedNode;
        this.log(`Selected node ${clickedNode.id}`);
      }
    } else {
      // Create new node
      const id = `N${this.customNodes.length + 1}`;
      this.customNodes.push({ id, x, y });
      this.log(`Added node ${id}`);
      this.initializeProblem();
    }
  }

  clearCustomCanvas() {
    this.customNodes = [];
    this.customEdges = [];
    this.selectedNode = null;
    this.log('Cleared custom canvas');
    this.initializeProblem();
  }
}

// Initialize the visualizer when the page loads
window.addEventListener('DOMContentLoaded', () => {
  new CSPVisualizer();
});
