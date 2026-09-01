(() => {
  "use strict";

  const svg = document.querySelector("[data-chart]");
  const scrubber = document.querySelector("[data-scrubber]");
  const errorMessage = document.querySelector("[data-chart-error]");
  const finalMarker = document.querySelector("[data-final-marker]");
  const decoder = new TextDecoder();
  const NS = "http://www.w3.org/2000/svg";
  const WIDTH = 1200;
  const HEIGHT = 500;
  const MARGIN = {top: 34, right: 24, bottom: 54, left: 80};
  const MODEL_LABELS = {
    constant_train_prevalence: "Constant baseline",
    logistic_all_sensor: "All-sensor logistic",
  };

  const setText = (selector, value) => {
    const node = document.querySelector(selector);
    if (node) node.textContent = value;
  };

  const svgNode = (name, attributes = {}) => {
    const node = document.createElementNS(NS, name);
    for (const [key, value] of Object.entries(attributes)) {
      node.setAttribute(key, String(value));
    }
    return node;
  };

  const sha256 = async (bytes) => {
    const digest = await crypto.subtle.digest("SHA-256", bytes);
    return [...new Uint8Array(digest)]
      .map((byte) => byte.toString(16).padStart(2, "0"))
      .join("");
  };

  const fetchBytes = async (path) => {
    const response = await fetch(path, {cache: "no-store"});
    if (!response.ok) throw new Error(`${path}: HTTP ${response.status}`);
    return new Uint8Array(await response.arrayBuffer());
  };

  const parseJson = (path, bytes) => {
    try {
      return JSON.parse(decoder.decode(bytes));
    } catch (error) {
      throw new Error(`${path}: invalid JSON (${error.message})`);
    }
  };

  const percent = (value) => `${(100 * Number(value)).toFixed(2)}%`;
  const percentRecord = (record, places = 2) => {
    const value = Number(record?.percent_decimal);
    if (!Number.isFinite(value) || value < 0) {
      throw new Error("summary contains an invalid percentage");
    }
    return `${value.toFixed(places)}%`;
  };
  const pointRecord = (record, places = 4) => {
    const value = Number(record?.percent_decimal);
    if (!Number.isFinite(value) || value < 0) {
      throw new Error("summary contains an invalid percentage-point cost");
    }
    return `${value.toFixed(places)} pp`;
  };
  const integer = new Intl.NumberFormat("en-US", {maximumFractionDigits: 0});

  const loadArtifacts = async () => {
    const manifestBytes = await fetchBytes("manifest.json");
    const manifest = parseJson("manifest.json", manifestBytes);
    if (manifest.schema_version !== "formalslt.monitor.uci357-site-manifest.v1") {
      throw new Error("unsupported monitor manifest");
    }
    const declaredHashes = new Map(
      manifest.files.map(({path, sha256: hash}) => [path, hash]),
    );
    const paths = ["certificate.json", "evidence.json", "summary.json", "trace.json"];
    const loaded = await Promise.all(paths.map(async (path) => [path, await fetchBytes(path)]));
    for (const [path, bytes] of loaded) {
      const expected = declaredHashes.get(path);
      if (!expected || await sha256(bytes) !== expected) {
        throw new Error(`${path}: site-manifest digest mismatch`);
      }
    }
    const byPath = new Map(loaded);
    const certificate = parseJson("certificate.json", byPath.get("certificate.json"));
    const evidence = parseJson("evidence.json", byPath.get("evidence.json"));
    const summary = parseJson("summary.json", byPath.get("summary.json"));
    const trace = parseJson("trace.json", byPath.get("trace.json"));
    const certificateHash = await sha256(byPath.get("certificate.json"));
    const evidenceHash = await sha256(byPath.get("evidence.json"));

    if (trace.certificate_sha256 !== certificateHash) {
      throw new Error("display trace is not bound to this certificate");
    }
    if (
      summary.schema_version !== "formalslt.brier-certificate-summary.v1"
      || summary.certificate?.sha256 !== certificateHash
    ) {
      throw new Error("summary is not bound to this certificate");
    }
    if (certificate.data.provenance.evidence_sha256 !== evidenceHash) {
      throw new Error("certificate is not bound to this evidence file");
    }
    if (trace.source_prediction_sha256 !== evidence.data.prediction_stream_sha256) {
      throw new Error("trace and evidence name different prediction streams");
    }
    if (certificate.data.observations !== trace.final.n) {
      throw new Error("certificate and trace horizons disagree");
    }
    if (certificate.kernel.result !== "PASS" || certificate.replay.independent_replay !== "PASS") {
      throw new Error("source receipt is not fully checked");
    }
    if (certificate.data.provenance.tier !== "AUDITED") {
      throw new Error("source receipt is not an audited-data certificate");
    }
    if (evidence.selection.winner !== trace.final.selected_model) {
      throw new Error("selection evidence and final trace disagree");
    }
    if (
      summary.selected_model !== evidence.selection.winner
      || summary.components?.observed_risk?.rational
        !== certificate.statistics.posterior_empirical_brier_risk
      || summary.components?.arithmetic_upper?.rational
        !== certificate.statistics.rational_arithmetic_upper
      || summary.claim?.upper_bound?.rational !== certificate.claim.upper_bound
      || summary.claim?.quantity !== certificate.claim.quantity
      || summary.verification?.lean_kernel !== certificate.kernel.result
      || summary.verification?.independent_replay
        !== certificate.replay.independent_replay
    ) {
      throw new Error("summary and checked certificate disagree");
    }
    return {certificate, evidence, summary, trace};
  };

  const bindReceipt = ({certificate, evidence, summary, trace}) => {
    setText("[data-observed-risk]", percentRecord(summary.components.observed_risk));
    setText("[data-upper-bound]", percentRecord(summary.claim.upper_bound));
    setText("[data-baseline-risk]", percent(trace.final.constant_brier_decimal));
    setText("[data-selected-model]", MODEL_LABELS[evidence.selection.winner]);
    setText(
      "[data-component-observed]",
      percentRecord(summary.components.observed_risk, 4),
    );
    setText(
      "[data-component-variation]",
      pointRecord(summary.components.variation_cost),
    );
    setText(
      "[data-component-selection]",
      pointRecord(summary.components.selection_cost),
    );
    setText(
      "[data-component-confidence]",
      pointRecord(summary.components.confidence_cost),
    );
    setText(
      "[data-component-upper]",
      `≤ ${percentRecord(summary.claim.upper_bound, 4)}`,
    );
    setText(
      "[data-component-rounding]",
      pointRecord(summary.components.rounding_slack, 6),
    );

    const upper = Number(summary.claim.upper_bound.decimal);
    const trackParts = [
      ["[data-track-observed]", summary.components.observed_risk],
      ["[data-track-variation]", summary.components.variation_cost],
      ["[data-track-selection]", summary.components.selection_cost],
      ["[data-track-confidence]", summary.components.confidence_cost],
      ["[data-track-rounding]", summary.components.rounding_slack],
    ];
    if (!Number.isFinite(upper) || upper <= 0) {
      throw new Error("summary contains an invalid checked endpoint");
    }
    for (const [selector, record] of trackParts) {
      const value = Number(record.decimal);
      if (!Number.isFinite(value) || value < 0) {
        throw new Error("summary contains an invalid decomposition term");
      }
      const node = document.querySelector(selector);
      if (node) node.style.width = `${100 * value / upper}%`;
    }
    setText("[data-certificate-status]", "CHECKED");
    setText("[data-replay-status]", certificate.replay.independent_replay);
    setText("[data-kernel-status]", certificate.kernel.result);
    setText("[data-certificate-id]", certificate.schema_version);
    document.querySelector(".checked-status")?.classList.add("is-checked");
  };

  const renderChart = (trace) => {
    const points = trace.points.map((point) => ({
      ...point,
      boundary: Number(point.boundary_upper_decimal),
      constant: Number(point.constant_brier_decimal),
      selected: Number(point.selected_brier_decimal),
    }));
    if (points.length < 2 || points.some((point) =>
      !Number.isFinite(point.boundary)
      || !Number.isFinite(point.constant)
      || !Number.isFinite(point.selected)
      || point.boundary <= 0
      || point.constant <= 0
      || point.selected <= 0
    )) {
      throw new Error("display trace contains invalid chart values");
    }

    const plotWidth = WIDTH - MARGIN.left - MARGIN.right;
    const plotHeight = HEIGHT - MARGIN.top - MARGIN.bottom;
    const minN = points[0].n;
    const maxN = points.at(-1).n;
    const yMin = 0.01;
    const yMax = 1;
    const logXMin = Math.log(minN);
    const logXMax = Math.log(maxN);
    const logYMin = Math.log(yMin);
    const logYMax = Math.log(yMax);
    const x = (n) => MARGIN.left
      + (Math.log(n) - logXMin) / (logXMax - logXMin) * plotWidth;
    const y = (value) => MARGIN.top
      + (logYMax - Math.log(value)) / (logYMax - logYMin) * plotHeight;

    svg.replaceChildren(svg.querySelector("title"), svg.querySelector("desc"));
    const grid = svgNode("g", {"aria-hidden": "true"});
    for (const tick of [0.02, 0.05, 0.1, 0.2, 0.5, 1]) {
      const yPosition = y(tick);
      grid.append(
        svgNode("line", {
          class: "grid-line",
          x1: MARGIN.left,
          x2: WIDTH - MARGIN.right,
          y1: yPosition,
          y2: yPosition,
        }),
      );
      const label = svgNode("text", {
        class: "axis-label",
        x: MARGIN.left - 16,
        y: yPosition + 6,
        "text-anchor": "end",
      });
      label.textContent = `${Math.round(tick * 100)}%`;
      grid.append(label);
    }
    for (const tick of [16, 64, 256, 1024, 4096, maxN]) {
      if (tick < minN || tick > maxN) continue;
      const xPosition = x(tick);
      grid.append(
        svgNode("line", {
          class: "grid-line",
          x1: xPosition,
          x2: xPosition,
          y1: MARGIN.top,
          y2: HEIGHT - MARGIN.bottom,
        }),
      );
      const label = svgNode("text", {
        class: "axis-label",
        x: xPosition,
        y: HEIGHT - MARGIN.bottom + 32,
        "text-anchor": tick === minN ? "start" : tick === maxN ? "end" : "middle",
      });
      label.textContent = integer.format(tick);
      grid.append(label);
    }
    svg.append(grid);

    const pathFor = (key) => points
      .map((point, index) => `${index ? "L" : "M"}${x(point.n).toFixed(2)},${y(point[key]).toFixed(2)}`)
      .join(" ");
    const series = svgNode("g", {class: "series"});
    series.append(
      svgNode("path", {
        class: "constant-path animated-path",
        d: pathFor("constant"),
        pathLength: 1,
        "data-series-path": "constant",
      }),
      svgNode("path", {
        class: "selected-path animated-path",
        d: pathFor("selected"),
        pathLength: 1,
        "data-series-path": "selected",
      }),
      svgNode("path", {
        class: "boundary-path animated-path",
        d: pathFor("boundary"),
        pathLength: 1,
        "data-series-path": "boundary",
      }),
    );
    svg.append(series);

    const cursor = svgNode("g", {class: "chart-cursor", "aria-hidden": "true"});
    const cursorLine = svgNode("line", {
      class: "cursor-line",
      y1: MARGIN.top,
      y2: HEIGHT - MARGIN.bottom,
    });
    const selectedDot = svgNode("circle", {class: "cursor-dot-selected", r: 7});
    const boundaryDot = svgNode("circle", {class: "cursor-dot-boundary", r: 7});
    const constantDot = svgNode("circle", {class: "cursor-dot-constant", r: 6});
    cursor.append(cursorLine, constantDot, selectedDot, boundaryDot);
    svg.append(cursor);

    scrubber.max = String(points.length - 1);
    scrubber.value = String(points.length - 1);
    const update = (index) => {
      const boundedIndex = Math.max(0, Math.min(points.length - 1, Number(index)));
      const point = points[boundedIndex];
      const xPosition = x(point.n);
      cursorLine.setAttribute("x1", xPosition);
      cursorLine.setAttribute("x2", xPosition);
      for (const [dot, value] of [
        [selectedDot, point.selected],
        [boundaryDot, point.boundary],
        [constantDot, point.constant],
      ]) {
        dot.setAttribute("cx", xPosition);
        dot.setAttribute("cy", y(value));
      }
      setText("[data-cursor-time]", integer.format(point.n));
      setText("[data-cursor-risk]", percent(point.selected));
      setText("[data-cursor-bound]", percent(point.boundary));
      finalMarker.hidden = boundedIndex !== points.length - 1;
      scrubber.value = String(boundedIndex);
    };

    scrubber.addEventListener("input", () => update(scrubber.value));
    const chooseFromPointer = (event) => {
      const bounds = svg.getBoundingClientRect();
      const localX = (event.clientX - bounds.left) / bounds.width * WIDTH;
      const fraction = Math.max(0, Math.min(1, (localX - MARGIN.left) / plotWidth));
      const targetN = Math.exp(logXMin + fraction * (logXMax - logXMin));
      let low = 0;
      let high = points.length - 1;
      while (low < high) {
        const middle = Math.floor((low + high) / 2);
        if (points[middle].n < targetN) low = middle + 1;
        else high = middle;
      }
      const before = Math.max(0, low - 1);
      const nearest = Math.abs(points[before].n - targetN) < Math.abs(points[low].n - targetN)
        ? before
        : low;
      update(nearest);
    };
    svg.addEventListener("pointerdown", (event) => {
      svg.setPointerCapture(event.pointerId);
      chooseFromPointer(event);
    });
    svg.addEventListener("pointermove", (event) => {
      if (svg.hasPointerCapture(event.pointerId)) chooseFromPointer(event);
    });

    for (const button of document.querySelectorAll("button[data-series]")) {
      button.addEventListener("click", () => {
        document.querySelectorAll("button[data-series]").forEach((candidate) => {
          candidate.classList.toggle("selected", candidate === button);
          candidate.setAttribute("aria-pressed", String(candidate === button));
        });
        svg.dataset.focus = button.dataset.series;
      });
    }
    update(points.length - 1);
  };

  const fail = (error) => {
    console.error("FormalSLT monitor refused to render", error);
    errorMessage.hidden = false;
    finalMarker.hidden = true;
    setText("[data-certificate-status]", "REFUSED");
    setText("[data-replay-status]", "REFUSED");
    setText("[data-kernel-status]", "REFUSED");
    document.querySelector(".checked-status")?.classList.add("is-error");
  };

  if (!svg || !scrubber || !errorMessage || !finalMarker || !window.crypto?.subtle) {
    fail(new Error("required browser APIs are unavailable"));
    return;
  }

  loadArtifacts()
    .then((artifacts) => {
      bindReceipt(artifacts);
      renderChart(artifacts.trace);
    })
    .catch(fail);
})();
