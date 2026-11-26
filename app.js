(function () {
  "use strict";

  const FIBER_COLORS = {
    logical_dep: "#1b365d",
    lean_dep: "#166534",
    prose_paraphrase: "#9333ea",
    notation: "#b45309",
    curriculum: "#0284c7",
  };

  const STRATUM_HEX = {
    emerald: { stroke: "#166534", fill: "#f0fdf4", text: "#14532d" },
    sapphire: { stroke: "#1d4ed8", fill: "#eff6ff", text: "#1e3a8a" },
    amber: { stroke: "#b45309", fill: "#fffbeb", text: "#78350f" },
    crimson: { stroke: "#991b1b", fill: "#fef2f2", text: "#7f1d1d" },
    none: { stroke: "#475569", fill: "#f8fafc", text: "#1e293b" },
  };

  let DATA = null;
  let NODE_BY_ID = new Map();
  let ACTIVE_FIBERS = new Set(["logical_dep", "lean_dep", "prose_paraphrase", "notation", "curriculum"]);
  let INCLUDE_PLAN_PUB = false;
  let DAG_ZOOM = 1.0;

  // Fallback for browsers without <dialog closedby="any">
  if (!("closedBy" in HTMLDialogElement.prototype)) {
    const outside = (e, dialog) => {
      const r = dialog.getBoundingClientRect();
      return e.clientX < r.left || e.clientX > r.right || e.clientY < r.top || e.clientY > r.bottom;
    };
    for (const dialog of document.querySelectorAll('dialog[closedby="any"]')) {
      let pressedOutside = false;
      dialog.addEventListener("pointerdown", (e) => {
        pressedOutside = outside(e, dialog);
      });
      dialog.addEventListener("pointerup", (e) => {
        if (pressedOutside && outside(e, dialog)) dialog.close();
      });
    }
  }

  function esc(s) {
    return String(s ?? "")
      .replaceAll("&", "&amp;")
      .replaceAll("<", "&lt;")
      .replaceAll(">", "&gt;")
      .replaceAll('"', "&quot;");
  }

  function badgeStratum(st) {
    const label = st === "none" ? "none" : st;
    return `<span class="badge stratum-${esc(st)}">${esc(label)}</span>`;
  }

  function badgeStatus(status) {
    return `<span class="badge status-${esc(status)}">${esc(status)}</span>`;
  }

  // Accessible Tabs (selection follows focus + hidden="until-found" + beforematch)
  function initTabs() {
    const tabs = Array.from(document.querySelectorAll('[role="tab"]'));
    const panels = Array.from(document.querySelectorAll('[role="tabpanel"]'));

    function selectTab(targetTab, moveFocus) {
      for (const tab of tabs) {
        const selected = tab === targetTab;
        tab.setAttribute("aria-selected", selected ? "true" : "false");
        tab.tabIndex = selected ? 0 : -1;
      }
      for (const panel of panels) {
        const active = panel.getAttribute("aria-labelledby") === targetTab.id;
        if (active) {
          panel.removeAttribute("hidden");
          panel.tabIndex = 0;
        } else {
          panel.setAttribute("hidden", "until-found");
          panel.removeAttribute("tabindex");
        }
      }
      if (moveFocus) {
        targetTab.focus();
        targetTab.scrollIntoView({ block: "nearest", inline: "nearest" });
      }
    }

    tabs.forEach((tab, idx) => {
      tab.addEventListener("click", () => selectTab(tab, false));
      tab.addEventListener("keydown", (e) => {
        let nextIdx = null;
        if (e.key === "ArrowRight") nextIdx = (idx + 1) % tabs.length;
        else if (e.key === "ArrowLeft") nextIdx = (idx - 1 + tabs.length) % tabs.length;
        else if (e.key === "Home") nextIdx = 0;
        else if (e.key === "End") nextIdx = tabs.length - 1;
        if (nextIdx !== null) {
          e.preventDefault();
          selectTab(tabs[nextIdx], true);
        }
      });
    });

    panels.forEach((panel) => {
      panel.addEventListener("beforematch", () => {
        const ownerTab = document.getElementById(panel.getAttribute("aria-labelledby"));
        if (ownerTab) selectTab(ownerTab, false);
      });
    });
  }

  // Modal Node Inspector
  function openNodeInspector(nodeId) {
    const node = NODE_BY_ID.get(nodeId);
    if (!node) return;
    const dialog = document.getElementById("node-inspector");
    const titleEl = document.getElementById("inspector-title");
    const metaEl = document.getElementById("inspector-meta");
    const bodyEl = document.getElementById("inspector-body");

    titleEl.textContent = `${node.id} — ${node.title}`;
    metaEl.innerHTML = [
      `<span class="badge stratum-none">${esc(node.kind)}</span>`,
      `<span class="badge stratum-none">${esc(node.cohort)}</span>`,
      badgeStratum(node.stratum),
      badgeStatus(node.taint_status),
      node.blueprint_tier && node.blueprint_tier !== "none"
        ? `<span class="badge stratum-sapphire">${esc(node.blueprint_tier)}</span>`
        : "",
    ].join(" ");

    const inEdges = DATA.edges.filter((e) => e.dst === node.id);
    const outEdges = DATA.edges.filter((e) => e.src === node.id);

    const sections = [];

    sections.push(`
      <div class="hash-grid">
        <div class="hash-item"><strong>Location:</strong> ${esc(node.file_path)}<br><strong>Pkg / Module:</strong> ${esc(node.formal_pkg)} ${node.module ? `(${esc(node.module)})` : ""}</div>
        <div class="hash-item"><strong>spec_hash:</strong> <code>${esc(node.spec_hash)}</code></div>
        <div class="hash-item"><strong>body_hash:</strong> <code>${esc(node.body_hash)}</code></div>
        <div class="hash-item"><strong>grounding_hash:</strong> <code>${esc(node.grounding_hash)}</code></div>
      </div>
    `);

    if (node.statement) {
      sections.push(`<div><strong>Specification / Mathematical Statement</strong><div class="tex-box">${esc(node.statement)}</div></div>`);
    }

    if (node.plan) {
      const p = node.plan;
      sections.push(`
        <div class="card">
          <h3>Work Item Plan (${esc(p.slice_code)} — Milestone ${esc(p.milestone_num)})</h3>
          <p>${esc(p.summary)}</p>
          <p><strong>Modules:</strong> ${(p.target_modules || []).map((m) => `<code>${esc(m)}</code>`).join(", ") || "—"}</p>
          <p><strong>Deliverables (${(p.deliverable_nodes || []).length}):</strong> ${(p.deliverable_nodes || []).map((d) => `<code>${esc(d)}</code>`).join(", ")}</p>
          ${node.issue ? `<p><strong>GitHub Issue:</strong> <a href="${esc(node.issue.url)}" target="_blank" rel="noopener">#${esc(node.issue.number)} (${esc(node.issue.state)})</a></p>` : ""}
        </div>
      `);
    }

    if (node.pub) {
      sections.push(`
        <div class="card">
          <h3>Publication Sink (${esc(node.pub.channel)} · ${esc(node.pub.sensitivity)})</h3>
          <p><strong>Outputs:</strong> ${(node.pub.outputs || []).map((o) => `<code>${esc(o)}</code>`).join(", ")}</p>
        </div>
      `);
    }

    if (node.formal_pkg === "mathlib_vol2" || node.formal_pkg === "kernel_arena") {
      sections.push(`
        <div>
          <strong>Formal Verification (${esc(node.formal_pkg)})</strong>
          <p class="muted" style="margin:0.25rem 0 0.45rem;">
            <strong>Declarations:</strong> ${(node.decl_names || []).map((d) => `<code>${esc(d)}</code>`).join(", ") || "—"}<br>
            <strong>Kernel Axioms:</strong> <code>${esc(JSON.stringify(node.actual_axioms || []))}</code>
            ${node.cert_path ? `<br><strong>2LTT Cert:</strong> <code>${esc(node.cert_path)}</code> (sha256: <code>${esc(node.cert_sha256 || "")}</code>)` : ""}
          </p>
          <pre class="code-box">${esc(node.lean_signature || "")}</pre>
        </div>
      `);
    }

    if (node.is_core) {
      const pillarsHtml = (node.dual_pillars || [])
        .map(
          (p) =>
            `<li><strong>${esc(p.kind)}</strong>: <code>${esc(p.ref)}</code>${p.locator ? ` (${esc(p.locator)})` : ""} — ${esc(p.purpose)}</li>`
        )
        .join("");
      sections.push(`
        <div class="card">
          <h3>Grounding &amp; Claim Classification</h3>
          <p style="margin:0 0 0.35rem;">
            <strong>Primary Category:</strong> ${esc(node.primary_category || "—")} ·
            <strong>Blueprint Tier:</strong> <code>${esc(node.blueprint_tier)}</code><br>
            <strong>Characterizations:</strong> ${esc((node.characterization_types || []).join(", ") || "—")}
          </p>
          ${node.witness_scope ? `<p style="margin:0 0 0.35rem;"><strong>Witness Scope:</strong> ${esc(node.witness_scope)}</p>` : ""}
          ${pillarsHtml ? `<ul style="margin:0.35rem 0 0 1.2rem;padding:0;">${pillarsHtml}</ul>` : ""}
        </div>
      `);
    }

    if (node.tex) {
      sections.push(`<div><strong>LaTeX Source</strong><div class="tex-box">${esc(node.tex)}</div></div>`);
    }

    const renderEdgeBtns = (list, key) =>
      list.length
        ? list
            .map(
              (e) =>
                `<button type="button" class="edge-btn" data-jump="${esc(e[key])}">[${esc(e.fiber)}] ${esc(e[key])}</button>`
            )
            .join("")
        : '<span class="muted">None</span>';

    sections.push(`
      <div>
        <strong>Incoming Dependencies (${inEdges.length})</strong>
        <div class="pill-list" style="margin-block:0.35rem 0.75rem;">${renderEdgeBtns(inEdges, "src")}</div>
        <strong>Outgoing Dependents (${outEdges.length})</strong>
        <div class="pill-list" style="margin-block:0.35rem 0;">${renderEdgeBtns(outEdges, "dst")}</div>
      </div>
    `);

    bodyEl.innerHTML = sections.join("");
    bodyEl.querySelectorAll("[data-jump]").forEach((btn) => {
      btn.addEventListener("click", () => openNodeInspector(btn.getAttribute("data-jump")));
    });

    if (!dialog.open) {
      dialog.showModal();
    }
  }

  // Render Tab 1: Layered SVG 5-Fiber DAG
  function renderDAG() {
    const svg = document.getElementById("dag-svg");
    const visibleNodes = DATA.nodes.filter((n) => INCLUDE_PLAN_PUB || n.is_core);
    const visIds = new Set(visibleNodes.map((n) => n.id));
    const visibleEdges = DATA.edges.filter(
      (e) => ACTIVE_FIBERS.has(e.fiber) && visIds.has(e.src) && visIds.has(e.dst)
    );

    // Compute longest-path topological layer across active visible edges
    const indeg = new Map();
    const adj = new Map();
    const layer = new Map();
    for (const n of visibleNodes) {
      indeg.set(n.id, 0);
      adj.set(n.id, []);
      layer.set(n.id, 0);
    }
    const uniquePairs = new Set();
    for (const e of visibleEdges) {
      const k = `${e.src}-->${e.dst}`;
      if (!uniquePairs.has(k)) {
        uniquePairs.add(k);
        adj.get(e.src).push(e.dst);
        indeg.set(e.dst, indeg.get(e.dst) + 1);
      }
    }
    const queue = visibleNodes.filter((n) => indeg.get(n.id) === 0).map((n) => n.id);
    while (queue.length > 0) {
      const u = queue.shift();
      const lu = layer.get(u);
      for (const v of adj.get(u)) {
        if (layer.get(v) < lu + 1) layer.set(v, lu + 1);
        indeg.set(v, indeg.get(v) - 1);
        if (indeg.get(v) === 0) queue.push(v);
      }
    }

    const byLayer = new Map();
    for (const n of visibleNodes) {
      const l = layer.get(n.id);
      if (!byLayer.has(l)) byLayer.set(l, []);
      byLayer.get(l).push(n);
    }
    const layerKeys = Array.from(byLayer.keys()).sort((a, b) => a - b);
    const colWidth = 255;
    const rowHeight = 76;
    const boxW = 210;
    const boxH = 54;
    const padX = 28;
    const padY = 26;

    let maxRows = 1;
    for (const lk of layerKeys) {
      byLayer.get(lk).sort((a, b) => (a.seq_order - b.seq_order) || a.id.localeCompare(b.id));
      maxRows = Math.max(maxRows, byLayer.get(lk).length);
    }

    const totalW = Math.max(880, padX * 2 + layerKeys.length * colWidth);
    const totalH = Math.max(460, padY * 2 + maxRows * rowHeight);
    const pos = new Map();

    for (let li = 0; li < layerKeys.length; li++) {
      const list = byLayer.get(layerKeys[li]);
      const offsetY = (totalH - list.length * rowHeight) / 2;
      list.forEach((n, ri) => {
        pos.set(n.id, {
          x: padX + li * colWidth,
          y: Math.max(padY, offsetY + ri * rowHeight),
        });
      });
    }

    const defs = Object.entries(FIBER_COLORS)
      .map(
        ([fiber, col]) =>
          `<marker id="arrow-${fiber}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M 0 1 L 10 5 L 0 9 z" fill="${col}"/></marker>`
      )
      .join("");

    const edgePaths = visibleEdges
      .map((e, i) => {
        const p1 = pos.get(e.src);
        const p2 = pos.get(e.dst);
        if (!p1 || !p2) return "";
        const x1 = p1.x + boxW;
        const y1 = p1.y + boxH / 2;
        const x2 = p2.x;
        const y2 = p2.y + boxH / 2;
        const dx = Math.max(36, (x2 - x1) * 0.45);
        const col = FIBER_COLORS[e.fiber] || "#64748b";
        const dash = e.fiber === "prose_paraphrase" ? 'stroke-dasharray="5 3"' : e.fiber === "notation" ? 'stroke-dasharray="2 3"' : "";
        return `<path d="M ${x1} ${y1} C ${x1 + dx} ${y1}, ${x2 - dx} ${y2}, ${x2} ${y2}" fill="none" stroke="${col}" stroke-width="1.5" stroke-opacity="0.72" ${dash} marker-end="url(#arrow-${e.fiber})"><title>${esc(e.src)} --[${esc(e.fiber)}]--> ${esc(e.dst)}</title></path>`;
      })
      .join("");

    const nodeBoxes = visibleNodes
      .map((n) => {
        const p = pos.get(n.id);
        const st = STRATUM_HEX[n.stratum] || STRATUM_HEX.none;
        const shortId = n.id.length > 29 ? n.id.slice(0, 27) + "…" : n.id;
        const shortTitle = n.title.length > 31 ? n.title.slice(0, 29) + "…" : n.title;
        return `
          <g class="dag-node" tabindex="0" role="button" data-node-id="${esc(n.id)}" aria-label="Inspect ${esc(n.id)}: ${esc(n.title)}" transform="translate(${p.x}, ${p.y})">
            <rect width="${boxW}" height="${boxH}" rx="4" fill="${st.fill}" stroke="${st.stroke}" stroke-width="1.75"/>
            <rect width="6" height="${boxH}" rx="2" fill="${st.stroke}"/>
            <text x="13" y="18" font-family="ui-monospace, monospace" font-size="10.5" font-weight="700" fill="${st.text}">${esc(shortId)}</text>
            <text x="13" y="34" font-family="sans-serif" font-size="10.5" fill="#0f172a">${esc(shortTitle)}</text>
            <text x="13" y="47" font-family="ui-monospace, monospace" font-size="9" fill="#475569">${esc(n.kind)} · ${esc(n.taint_status)} · ${esc(n.spec_hash.slice(0, 8))}</text>
          </g>`;
      })
      .join("");

    svg.setAttribute("viewBox", `0 0 ${totalW} ${totalH}`);
    svg.style.width = `${Math.round(totalW * DAG_ZOOM)}px`;
    svg.style.height = `${Math.round(totalH * DAG_ZOOM)}px`;
    svg.innerHTML = `<defs>${defs}</defs>${edgePaths}${nodeBoxes}`;

    svg.querySelectorAll(".dag-node").forEach((el) => {
      const nid = el.getAttribute("data-node-id");
      el.addEventListener("click", () => openNodeInspector(nid));
      el.addEventListener("keydown", (e) => {
        if (e.key === "Enter" || e.key === " ") {
          e.preventDefault();
          openNodeInspector(nid);
        }
      });
    });

    document.getElementById("dag-summary").textContent =
      `Showing ${visibleNodes.length} nodes and ${visibleEdges.length} edges across ${ACTIVE_FIBERS.size} active fiber(s). Click any node to inspect.`;
  }

  // Render Tab 2: 14-Slice Project Plan & Milestones
  function renderRoadmap() {
    const msMap = new Map();
    for (const w of DATA.work_items) {
      if (!msMap.has(w.milestone_num)) {
        msMap.set(w.milestone_num, { num: w.milestone_num, title: w.milestone, items: [] });
      }
      msMap.get(w.milestone_num).items.push(w);
    }

    const msGrid = document.getElementById("milestone-grid");
    msGrid.innerHTML = Array.from(msMap.values())
      .sort((a, b) => a.num - b.num)
      .map((m) => {
        const done = m.items.filter((x) => x.status === "VERIFIED").length;
        const pct = Math.round((done / m.items.length) * 100);
        return `
          <div class="milestone-card">
            <div class="metric-label">${m.num === 10 ? "TCB Milestone" : `Milestone ${m.num}`}</div>
            <div style="font-weight:700;font-size:0.9rem;margin-block:0.2rem;">${esc(m.title)}</div>
            <div class="progress-track"><div class="progress-fill" style="width:${pct}%"></div></div>
            <div class="metric-sub">${done}/${m.items.length} slices VERIFIED</div>
          </div>`;
      })
      .join("");

    const tbody = document.getElementById("roadmap-tbody");
    tbody.innerHTML = DATA.work_items
      .map((w) => {
        const issueCell = w.issue
          ? `<a href="${esc(w.issue.url)}" target="_blank" rel="noopener">#${esc(w.issue.number)}</a>`
          : w.status === "VERIFIED"
          ? "Done"
          : "—";
        return `
          <tr>
            <th scope="row">${esc(w.seq_order)}. <code>${esc(w.slice_code)}</code><br><button type="button" class="edge-btn" data-inspect="${esc(w.id)}">${esc(w.id)}</button></th>
            <td data-label="Milestone">${esc(w.milestone)}</td>
            <td data-label="Status">${badgeStatus(w.status)}<br><span class="muted">${w.verified_deliverables}/${w.total_deliverables} CLEAN</span></td>
            <td data-label="Target Modules">${(w.target_modules || []).map((m) => `<code>${esc(m)}</code>`).join("<br>") || "—"}</td>
            <td data-label="Guardrails">${(w.guardrails || []).map((g) => `<code>${esc(g)}</code>`).join(", ") || "—"}</td>
            <td data-label="Summary">${esc(w.summary)}</td>
            <td data-label="Issue">${issueCell}</td>
          </tr>`;
      })
      .join("");

    tbody.querySelectorAll("[data-inspect]").forEach((b) => {
      b.addEventListener("click", () => openNodeInspector(b.getAttribute("data-inspect")));
    });
  }

  // Render Tab 3: Claims Ledger & Disjoint Declaration Browser
  function renderLedger() {
    const q = document.getElementById("ledger-search").value.trim().toLowerCase();
    const cohortF = document.getElementById("filter-cohort").value;
    const stratumF = document.getElementById("filter-stratum").value;
    const tierF = document.getElementById("filter-tier").value;

    const rows = DATA.nodes.filter((n) => {
      if (!n.is_core) return false;
      if (cohortF !== "ALL" && n.cohort !== cohortF) return false;
      if (stratumF !== "ALL" && n.stratum !== stratumF) return false;
      if (tierF !== "ALL" && n.blueprint_tier !== tierF) return false;
      if (q) {
        const hay = `${n.id} ${n.title} ${n.primary_category} ${n.statement} ${(n.decl_names || []).join(" ")}`.toLowerCase();
        if (!hay.includes(q)) return false;
      }
      return true;
    });

    document.getElementById("ledger-count").textContent = `${rows.length} of ${DATA.metrics.core_nodes} core nodes`;
    const tbody = document.getElementById("ledger-tbody");
    tbody.innerHTML = rows
      .map(
        (n) => `
        <tr>
          <th scope="row"><button type="button" class="edge-btn" data-inspect="${esc(n.id)}">${esc(n.id)}</button><br><span class="muted">${esc(n.kind)} · ${esc(n.cohort)}</span></th>
          <td data-label="Title">${esc(n.title)}</td>
          <td data-label="Category & Tier">${esc(n.primary_category || "Symbol")}<br><code>${esc(n.blueprint_tier)}</code></td>
          <td data-label="Stratum & Axioms">${badgeStratum(n.stratum)}<br><code>${esc(JSON.stringify(n.actual_axioms))}</code></td>
          <td data-label="Hashes & Status">${badgeStatus(n.taint_status)}<br><code>spec:${esc(n.spec_hash.slice(0, 8))}</code> <code>body:${esc(n.body_hash.slice(0, 8))}</code></td>
        </tr>`
      )
      .join("");

    tbody.querySelectorAll("[data-inspect]").forEach((b) => {
      b.addEventListener("click", () => openNodeInspector(b.getAttribute("data-inspect")));
    });

    // Declaration Ownership Table
    const dq = document.getElementById("decl-search").value.trim().toLowerCase();
    const dRows = DATA.decl_ownership.filter(
      (d) => !dq || d.decl_or_cert.toLowerCase().includes(dq) || d.node_id.toLowerCase().includes(dq)
    );
    document.getElementById("decl-count").textContent = `${dRows.length} of ${DATA.decl_ownership.length} disjoint declarations/certs`;
    const dTbody = document.getElementById("decl-tbody");
    dTbody.innerHTML = dRows
      .map(
        (d) => `
        <tr>
          <th scope="row"><code>${esc(d.decl_or_cert)}</code></th>
          <td data-label="Owning Node"><button type="button" class="edge-btn" data-inspect="${esc(d.node_id)}">${esc(d.node_id)}</button></td>
          <td data-label="Ownership Kind"><code>${esc(d.ownership_kind)}</code></td>
        </tr>`
      )
      .join("");

    dTbody.querySelectorAll("[data-inspect]").forEach((b) => {
      b.addEventListener("click", () => openNodeInspector(b.getAttribute("data-inspect")));
    });
  }

  // Render Tab 4: Process, Guardrails, Pub Targets, & PDFs
  function renderProcessTab() {
    document.getElementById("pdf-cards").innerHTML = DATA.pdfs
      .map(
        (p) => `
        <div class="card">
          <h3>${esc(p.label)}</h3>
          <p class="muted" style="font-size:0.86rem;">${esc(p.description)}</p>
          ${
            p.available
              ? `<a class="btn btn-primary" href="${esc(p.href)}" target="_blank" rel="noopener">Open PDF (${esc(p.size_kb)} KB)</a>`
              : `<span class="badge status-ARTIFACT_DIRTY">PDF not built</span>`
          }
        </div>`
      )
      .join("");

    document.getElementById("drill-cards").innerHTML = `
      <div class="card"><h3>Pass A — Clean Baseline</h3><p>${esc(DATA.drill_summary.pass_a)}</p></div>
      <div class="card"><h3>Pass B — Clause 3 Spec Taint</h3><p>${esc(DATA.drill_summary.pass_b)}</p></div>
      <div class="card"><h3>Pass C — Remediation &amp; Body Isolation</h3><p>${esc(DATA.drill_summary.pass_c)}</p></div>
    `;

    document.getElementById("guardrails-list").innerHTML = DATA.guardrails
      .map(
        (g) => `
        <div class="card">
          <h3><code>${esc(g.id)}</code> — ${esc(g.title)}</h3>
          <p style="margin:0 0 0.3rem;">${esc(g.statement)}</p>
          <div class="muted" style="font-size:0.78rem;">Vol I Anchor: <code>${esc(g.vol1_anchor)}</code></div>
        </div>`
      )
      .join("");

    const pubTbody = document.getElementById("pub-tbody");
    pubTbody.innerHTML = DATA.pub_targets
      .map(
        (p) => `
        <tr>
          <th scope="row"><button type="button" class="edge-btn" data-inspect="${esc(p.id)}">${esc(p.id)}</button></th>
          <td data-label="Channel"><code>${esc(p.channel)}</code></td>
          <td data-label="Sensitivity"><code>${esc(p.sensitivity)}</code></td>
          <td data-label="Outputs">${p.outputs.map((o) => `<code>${esc(o)}</code>`).join("<br>")}</td>
          <td data-label="Cone Hash"><code>${esc(p.cone_hash.slice(0, 12))}</code></td>
          <td data-label="Status">${badgeStatus(p.pub_status)}</td>
        </tr>`
      )
      .join("");
    pubTbody.querySelectorAll("[data-inspect]").forEach((b) => {
      b.addEventListener("click", () => openNodeInspector(b.getAttribute("data-inspect")));
    });
  }

  async function boot() {
    initTabs();
    const resp = await fetch("data/network.json");
    DATA = await resp.json();
    for (const n of DATA.nodes) NODE_BY_ID.set(n.id, n);

    const dialog = document.getElementById("node-inspector");
    dialog.addEventListener("close", () => {
      dialog.returnValue = "";
    });

    // Wire DAG controls
    document.querySelectorAll(".fiber-toggle").forEach((cb) => {
      cb.addEventListener("change", () => {
        if (cb.checked) ACTIVE_FIBERS.add(cb.value);
        else ACTIVE_FIBERS.delete(cb.value);
        renderDAG();
      });
    });
    document.getElementById("toggle-plan-pub").addEventListener("change", (e) => {
      INCLUDE_PLAN_PUB = e.target.checked;
      renderDAG();
    });
    document.getElementById("zoom-in").addEventListener("click", () => {
      DAG_ZOOM = Math.min(2.0, +(DAG_ZOOM + 0.15).toFixed(2));
      renderDAG();
    });
    document.getElementById("zoom-out").addEventListener("click", () => {
      DAG_ZOOM = Math.max(0.55, +(DAG_ZOOM - 0.15).toFixed(2));
      renderDAG();
    });
    document.getElementById("zoom-reset").addEventListener("click", () => {
      DAG_ZOOM = 1.0;
      renderDAG();
    });

    // Wire Ledger filters
    ["ledger-search", "filter-cohort", "filter-stratum", "filter-tier"].forEach((id) => {
      document.getElementById(id).addEventListener("input", renderLedger);
      document.getElementById(id).addEventListener("change", renderLedger);
    });
    document.getElementById("decl-search").addEventListener("input", renderLedger);

    renderDAG();
    renderRoadmap();
    renderLedger();
    renderProcessTab();
  }

  boot().catch((err) => {
    console.error(err);
    document.getElementById("dag-summary").textContent = `Error loading data/network.json: ${err.message}`;
  });
})();
