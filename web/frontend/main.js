const originalFetch = window.fetch;
window.fetch = function (input, init) {
  let url = '';
  if (typeof input === 'string') {
    url = input;
  } else if (input && typeof input === 'object' && input.url) {
    url = input.url;
  }
  
  const isGitHubPages = window.location.hostname.includes('roars.dev') || window.location.hostname.includes('github.io');
  if (isGitHubPages && url.startsWith('/api/')) {
    const targetUrl = 'https://density-capillary-thinning.ngrok-free.dev' + url;
    if (typeof input === 'string') {
      input = targetUrl;
    } else {
      input = { ...input, url: targetUrl };
    }
    url = targetUrl;
  }
  
  if (url.includes('ngrok-free.dev') || window.location.hostname.includes('ngrok-free.dev')) {
    init = init || {};
    init.headers = init.headers || {};
    if (init.headers instanceof Headers) {
      init.headers.set('ngrok-skip-browser-warning', '69420');
    } else if (Array.isArray(init.headers)) {
      init.headers.push(['ngrok-skip-browser-warning', '69420']);
    } else {
      init.headers['ngrok-skip-browser-warning'] = '69420';
    }
  }
  return originalFetch(input, init);
};

let currentInputType = 'c';
let activeJobId = null;
let pollTimer = null;
let startTime = 0;
let elapsedTimer = null;

document.addEventListener('DOMContentLoaded', () => {
  initExamples();
  initEvents();
});

function renderLoadingPlaceholders() {
  const grid = document.getElementById('examples-grid');
  grid.innerHTML = Array(3).fill(0).map(() => `
    <div class="example-card example-card--loading">
      <div class="example-card__name">Loading…</div>
      <div class="example-card__desc">Fetching examples from server</div>
    </div>
  `).join('');
}

async function initExamples() {
  renderLoadingPlaceholders();
  try {
    const res = await fetch('/api/examples');
    if (!res.ok) throw new Error(`HTTP ${res.status}`);
    const data = await res.json();
    
    if (!data.examples || data.examples.length === 0) {
      document.getElementById('examples-grid').innerHTML = '<p style="color: var(--text-muted);">No examples available. Start the backend server to load examples.</p>';
      return;
    }
    
    renderExamples(data.examples);
  } catch (err) {
    console.warn('Could not load examples:', err);
    document.getElementById('examples-grid').innerHTML = `
      <p style="color: var(--text-muted);">
        Could not connect to the backend server. Examples will be available when the server is running.
      </p>
    `;
  }
}

function renderExamples(examples) {
  const grid = document.getElementById('examples-grid');
  grid.innerHTML = '';
  
  examples.forEach((ex, i) => {
    const card = document.createElement('div');
    card.className = 'example-card';
    card.setAttribute('tabindex', '0');
    card.setAttribute('role', 'button');
    card.style.setProperty('--i', i);
    card.innerHTML = `
      <div class="example-card__name">${escapeHtml(ex.name)}</div>
      <p class="example-card__desc">${escapeHtml(ex.description)}</p>
      <div class="example-card__files">
        <span class="example-card__file">${escapeHtml(ex.file)}</span>
        <span class="example-card__file" style="text-transform: uppercase;">${escapeHtml(ex.type)}</span>
      </div>
    `;
    
    const handler = () => loadExample(ex.id, ex.type);
    card.addEventListener('click', handler);
    card.addEventListener('keydown', (e) => {
      if (e.key === 'Enter' || e.key === ' ') {
        e.preventDefault();
        handler();
      }
    });
    
    grid.appendChild(card);
  });
}

async function loadExample(id, type) {
  try {
    setInputType(type);
    const res = await fetch(`/api/example/${id}`);
    if (!res.ok) throw new Error(`HTTP ${res.status}`);
    const data = await res.json();
    if (data.content) {
      document.getElementById('code-input').value = data.content;
    }
  } catch (err) {
    console.error('Failed to fetch example content', err);
  }
}

function setInputType(type) {
  currentInputType = type;
  const btnC = document.getElementById('toggle-c');
  const btnCsv = document.getElementById('toggle-csv');
  const textarea = document.getElementById('code-input');
  
  if (type === 'c') {
    btnC.classList.add('active');
    btnCsv.classList.remove('active');
    textarea.placeholder = '// Enter C program annotated with vtraceX(...) calls...\nint mainQ(int x, int y) {\n    ...\n}';
  } else {
    btnCsv.classList.add('active');
    btnC.classList.remove('active');
    textarea.placeholder = '# Enter execution traces in CSV format...\nvtrace1; I q; I r; I a; I b; I x; I y\nvtrace1; 4; 8; 1; 4; 24; 4';
  }
}

function initEvents() {
  document.getElementById('toggle-c').addEventListener('click', () => setInputType('c'));
  document.getElementById('toggle-csv').addEventListener('click', () => setInputType('csv'));
  document.getElementById('run-btn').addEventListener('click', startJob);
  document.getElementById('cancel-btn').addEventListener('click', cancelJob);
}

async function startJob() {
  const code = document.getElementById('code-input').value.trim();
  if (!code) {
    alert('Please enter program code or trace data.');
    return;
  }

  const options = {
    maxdeg: document.getElementById('maxdeg-input').value ? parseInt(document.getElementById('maxdeg-input').value) : null,
    timeout: parseInt(document.getElementById('timeout-input').value) || 60,
    noeqts: document.getElementById('chk-noeqts').checked,
    noieqs: document.getElementById('chk-noieqs').checked,
    nocongruences: document.getElementById('chk-nocongruences').checked,
    nominmaxplus: document.getElementById('chk-nominmaxplus').checked,
  };

  showState('running');
  startTime = Date.now();
  updateElapsed();
  elapsedTimer = setInterval(updateElapsed, 1000);

  try {
    const res = await fetch('/api/run', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ code, input_type: currentInputType, options })
    });

    const data = await res.json();
    if (res.status === 202 && data.job_id) {
      activeJobId = data.job_id;
      pollTimer = setInterval(pollJobStatus, 1500);
    } else {
      showError(data.error || 'Failed to start job.');
    }
  } catch (err) {
    showError(err.message || 'Network error.');
  }
}

async function pollJobStatus() {
  if (!activeJobId) return;

  try {
    const res = await fetch(`/api/status/${activeJobId}`);
    const data = await res.json();

    if (data.raw_output) {
      document.getElementById('terminal-log').textContent = data.raw_output;
    }

    if (data.status === 'completed') {
      stopPolling();
      renderResults(data);
    } else if (data.status === 'timeout') {
      stopPolling();
      showError('Execution timed out.', 'Timeout');
    } else if (data.status === 'error') {
      stopPolling();
      showError(data.error || 'Execution failed.', 'Execution Error');
    }
  } catch (err) {
    console.error('Error polling status', err);
  }
}

async function cancelJob() {
  if (!activeJobId) return;
  try {
    await fetch(`/api/cancel/${activeJobId}`, { method: 'POST' });
    stopPolling();
    showError('Job cancelled by user.', 'Cancelled');
  } catch (err) {
    console.error('Error cancelling job', err);
  }
}

function stopPolling() {
  if (pollTimer) clearInterval(pollTimer);
  if (elapsedTimer) clearInterval(elapsedTimer);
  pollTimer = null;
  elapsedTimer = null;
}

function updateElapsed() {
  const secs = Math.floor((Date.now() - startTime) / 1000);
  document.getElementById('running-elapsed').textContent = `Elapsed: ${secs}s`;
}

function showState(stateName) {
  const idle = document.getElementById('state-idle');
  const running = document.getElementById('state-running');
  const completed = document.getElementById('state-completed');
  const error = document.getElementById('state-error');

  idle.hidden = stateName !== 'idle';
  running.hidden = stateName !== 'running';
  completed.hidden = stateName !== 'completed';
  error.hidden = stateName !== 'error';

  const visible = {
    idle,
    running,
    completed,
    error
  }[stateName];

  if (visible) {
    visible.classList.remove('fade-in');
    void visible.offsetWidth;
    visible.classList.add('fade-in');
  }
}

function showError(msg, title = 'Error') {
  showState('error');
  document.getElementById('error-title').textContent = title;
  document.getElementById('error-msg').textContent = msg;
}

function renderResults(data) {
  showState('completed');
  const summary = document.getElementById('result-summary');
  summary.innerHTML = `<p style="font-size: 0.9rem; color: var(--text-muted); margin-bottom: 12px;">Completed in <strong>${data.runtime || 0}s</strong> across ${data.locations.length} location(s).</p>`;

  const list = document.getElementById('locations-list');
  list.innerHTML = '';

  if (data.locations.length === 0) {
    list.innerHTML = '<p style="color: var(--text-muted);">No invariants discovered.</p>';
    return;
  }

  data.locations.forEach(loc => {
    const card = document.createElement('div');
    card.className = 'location-card';
    
    let invsHtml = loc.invariants.map(inv => `
      <div class="inv-badge" data-type="${inv.type}">
        <span>${escapeHtml(inv.text)}</span>
        <span class="inv-type-tag">${inv.type}</span>
      </div>
    `).join('');

    card.innerHTML = `
      <div class="location-title">
        <svg class="panel__icon-svg" viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round" style="margin-right: 6px; vertical-align: -2px;"><path d="M21 10c0 7-9 13-9 13s-9-6-9-13a9 9 0 0 1 18 0z"/><circle cx="12" cy="10" r="3"/></svg>
        ${escapeHtml(loc.header || loc.name)}
      </div>
      <div class="inv-badge-list">${invsHtml || '<p style="color: var(--text-muted); font-size: 0.8rem;">No invariants found at this location.</p>'}</div>
    `;
    list.appendChild(card);
  });
}

function escapeHtml(str) {
  return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}
