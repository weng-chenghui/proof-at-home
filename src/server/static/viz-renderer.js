// viz-renderer.js — Shared D3/KaTeX visualization renderers for Proof@Home
// Extracted from conjecture_viz/template.html for reuse on the web UI.

const VIZ_COLORS = ['#58a6ff', '#7ee787', '#d2a8ff', '#f0883e', '#f778ba', '#79c0ff', '#56d364', '#e3b341'];

function renderGraph(container, data, idx) {
  const width = container.clientWidth || 800;
  const height = 500;
  const nodes = (data.nodes || []).map(n => ({ ...n }));
  const edges = (data.edges || []).map(e => ({ ...e }));

  const groups = [...new Set(nodes.map(n => n.group || 'default'))];
  const colorScale = d3.scaleOrdinal().domain(groups).range(VIZ_COLORS);

  const svg = d3.select(container).append('svg').attr('viewBox', `0 0 ${width} ${height}`);

  svg.append('defs').append('marker')
    .attr('id', `arrowhead-${idx}`).attr('viewBox', '0 -5 10 10')
    .attr('refX', 20).attr('refY', 0).attr('markerWidth', 6).attr('markerHeight', 6)
    .attr('orient', 'auto')
    .append('path').attr('d', 'M0,-5L10,0L0,5').attr('fill', '#58a6ff');

  const g = svg.append('g');
  svg.call(d3.zoom().scaleExtent([0.2, 4]).on('zoom', e => g.attr('transform', e.transform)));

  const simulation = d3.forceSimulation(nodes)
    .force('link', d3.forceLink(edges).id(d => d.id).distance(120))
    .force('charge', d3.forceManyBody().strength(-300))
    .force('center', d3.forceCenter(width / 2, height / 2))
    .force('collision', d3.forceCollide().radius(30));

  const link = g.selectAll('.graph-link').data(edges).enter().append('line')
    .attr('class', d => 'graph-link' + (d.directed ? ' graph-link-directed' : ''))
    .style('marker-end', d => d.directed ? `url(#arrowhead-${idx})` : null);

  const edgeLabel = g.selectAll('.graph-edge-label').data(edges.filter(e => e.label)).enter()
    .append('text').attr('class', 'graph-edge-label');

  const node = g.selectAll('.graph-node').data(nodes).enter().append('g')
    .call(d3.drag().on('start', dragStart).on('drag', dragged).on('end', dragEnd));

  node.append('circle').attr('class', 'graph-node-circle').attr('r', 18)
    .attr('fill', d => colorScale(d.group || 'default'))
    .attr('stroke', d => d3.color(colorScale(d.group || 'default')).brighter(0.5));

  node.append('text').attr('class', 'graph-node-label').attr('dy', '0.35em')
    .each(function(d) { renderKaTeX(this, d.label || d.id); });

  edgeLabel.each(function(d) { renderKaTeX(this, d.label); });

  simulation.on('tick', () => {
    link.attr('x1', d => d.source.x).attr('y1', d => d.source.y)
        .attr('x2', d => d.target.x).attr('y2', d => d.target.y);
    node.attr('transform', d => `translate(${d.x},${d.y})`);
    edgeLabel.attr('x', d => (d.source.x + d.target.x) / 2)
             .attr('y', d => (d.source.y + d.target.y) / 2);
  });

  function dragStart(event, d) { if (!event.active) simulation.alphaTarget(0.3).restart(); d.fx = d.x; d.fy = d.y; }
  function dragged(event, d) { d.fx = event.x; d.fy = event.y; }
  function dragEnd(event, d) { if (!event.active) simulation.alphaTarget(0); d.fx = null; d.fy = null; }
}

function renderCD(container, data, idx) {
  // Support both formats: {objects, morphisms} with col/row, or {nodes, edges} with x/y
  const objects = data.objects || data.nodes || [];
  const morphisms = data.morphisms || data.edges || [];

  const cellW = 140, cellH = 100, padX = 80, padY = 60;
  const maxCol = Math.max(0, ...objects.map(o => o.col ?? o.x ?? 0));
  const maxRow = Math.max(0, ...objects.map(o => o.row ?? o.y ?? 0));
  const width = (maxCol + 1) * cellW + padX * 2;
  const height = (maxRow + 1) * cellH + padY * 2;

  const svg = d3.select(container).append('svg').attr('viewBox', `0 0 ${width} ${height}`);

  svg.append('defs').append('marker')
    .attr('id', `cd-arrowhead-${idx}`).attr('viewBox', '0 -5 10 10')
    .attr('refX', 10).attr('refY', 0).attr('markerWidth', 6).attr('markerHeight', 6)
    .attr('orient', 'auto')
    .append('path').attr('d', 'M0,-5L10,0L0,5').attr('fill', '#58a6ff');

  const pos = {};
  objects.forEach(o => {
    const col = o.col ?? o.x ?? 0;
    const row = o.row ?? o.y ?? 0;
    const x = padX + col * cellW + cellW / 2;
    const y = padY + row * cellH + cellH / 2;
    pos[o.id] = { x, y };
  });

  morphisms.forEach(m => {
    const s = pos[m.source], t = pos[m.target];
    if (!s || !t) return;

    const dx = t.x - s.x, dy = t.y - s.y;
    const len = Math.sqrt(dx * dx + dy * dy);
    const offset = 25;
    const sx = s.x + (dx / len) * offset, sy = s.y + (dy / len) * offset;
    const tx = t.x - (dx / len) * offset, ty = t.y - (dy / len) * offset;

    let cls = 'cd-arrow';
    if (m.style === 'dashed') cls += ' cd-arrow-dashed';
    if (m.style === 'double') cls += ' cd-arrow-double';

    svg.append('line')
      .attr('class', cls)
      .attr('x1', sx).attr('y1', sy).attr('x2', tx).attr('y2', ty)
      .attr('marker-end', `url(#cd-arrowhead-${idx})`);

    if (m.label) {
      const lx = (sx + tx) / 2 + (-dy / len) * 14;
      const ly = (sy + ty) / 2 + (dx / len) * 14;
      const label = svg.append('text').attr('class', 'cd-arrow-label').attr('x', lx).attr('y', ly);
      renderKaTeX(label.node(), m.label);
    }
  });

  objects.forEach(o => {
    const p = pos[o.id];
    const text = svg.append('text').attr('class', 'cd-object').attr('x', p.x).attr('y', p.y);
    renderKaTeX(text.node(), o.label || o.id);
  });
}

function renderRegion(container, data) {
  const regions = data.regions || [];
  const labels = data.labels || [];

  const svg = d3.select(container).append('svg').attr('viewBox', '0 0 500 500');

  // Check if regions use flat format (cx/cy/r) or hierarchical format (children)
  const isHierarchical = regions.length > 0 && regions[0].children && !regions[0].cx;

  if (isHierarchical) {
    // Flatten hierarchical regions into nested circles
    const flat = [];
    let idx = 0;
    function flatten(items, depth, cx, cy, maxR) {
      const count = items.length;
      items.forEach((item, i) => {
        const r = maxR / (depth === 0 ? 1 : 1.2);
        const angle = (2 * Math.PI * i) / Math.max(count, 1) - Math.PI / 2;
        const offsetR = depth === 0 ? 0 : maxR * 0.35;
        const x = cx + offsetR * Math.cos(angle);
        const y = cy + offsetR * Math.sin(angle);
        flat.push({ id: item.id, label: item.label || item.id, cx: x, cy: y, r: r, depth: depth, index: idx++ });
        if (item.children) {
          flatten(item.children, depth + 1, x, y, r * 0.55);
        }
      });
    }
    flatten(regions, 0, 250, 250, 200);

    flat.sort((a, b) => a.depth - b.depth); // draw outer first
    flat.forEach((r) => {
      const color = r.color || VIZ_COLORS[r.index % VIZ_COLORS.length];
      svg.append('circle')
        .attr('class', 'region-circle')
        .attr('cx', r.cx).attr('cy', r.cy).attr('r', r.r)
        .attr('fill', color).attr('stroke', color);

      const labelEl = svg.append('text').attr('class', 'region-label')
        .attr('x', r.cx).attr('y', r.cy - r.r * 0.6);
      renderKaTeX(labelEl.node(), r.label);
    });
  } else {
    regions.forEach((r, i) => {
      const color = r.color || VIZ_COLORS[i % VIZ_COLORS.length];
      svg.append('circle')
        .attr('class', 'region-circle')
        .attr('cx', r.cx).attr('cy', r.cy).attr('r', r.r)
        .attr('fill', color).attr('stroke', color);

      const labelEl = svg.append('text').attr('class', 'region-label')
        .attr('x', r.cx).attr('y', r.cy);
      renderKaTeX(labelEl.node(), r.label || r.id);
    });
  }

  labels.forEach(l => {
    const ann = svg.append('text').attr('class', 'region-annotation')
      .attr('x', l.x).attr('y', l.y);
    renderKaTeX(ann.node(), l.text);
  });
}

function renderTable(container, data) {
  const headers = data.headers || [];
  const rows = data.rows || [];
  const caption = data.caption || '';

  let html = '<table class="viz-table">';
  if (caption) html += `<caption>${vizEscapeHtml(caption)}</caption>`;
  html += '<thead><tr>';
  headers.forEach(h => { html += `<th>${vizEscapeHtml(h)}</th>`; });
  html += '</tr></thead><tbody>';
  rows.forEach(row => {
    html += '<tr>';
    (Array.isArray(row) ? row : []).forEach(cell => {
      html += `<td>${vizEscapeHtml(String(cell))}</td>`;
    });
    html += '</tr>';
  });
  html += '</tbody></table>';
  container.innerHTML = html;

  container.querySelectorAll('th, td').forEach(el => {
    const text = el.textContent;
    if (text.includes('\\') || text.includes('_') || text.includes('^')) {
      try {
        katex.render(text, el, { throwOnError: false, displayMode: false });
      } catch(e) { /* keep plain text */ }
    }
  });
}

function renderText(container, data) {
  const content = data.content || '';
  const div = document.createElement('div');
  div.className = 'viz-text-block';
  content.split('\n\n').forEach(para => {
    if (!para.trim()) return;
    const p = document.createElement('p');
    p.innerHTML = para.replace(/\$([^$]+)\$/g, (_, tex) => {
      try { return katex.renderToString(tex, { throwOnError: false }); }
      catch(e) { return tex; }
    });
    div.appendChild(p);
  });
  container.appendChild(div);
}

function renderKaTeX(el, text) {
  if (!text) return;
  // KaTeX outputs HTML which doesn't render inside SVG <text> elements.
  // For SVG context, use textContent directly. Only use KaTeX for HTML elements.
  if (el instanceof SVGElement) {
    el.textContent = text;
    return;
  }
  try {
    katex.render(text, el, { throwOnError: false, displayMode: false });
  } catch (e) {
    el.textContent = text;
  }
}

function vizEscapeHtml(str) {
  const div = document.createElement('div');
  div.textContent = str;
  return div.innerHTML;
}
