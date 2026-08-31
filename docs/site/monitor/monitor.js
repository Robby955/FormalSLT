"use strict";

const SVG_NS = "http://www.w3.org/2000/svg";

const select = (selector) => document.querySelector(selector);
const selectAll = (selector) => [...document.querySelectorAll(selector)];

const percent = (decimal) => `${(Number(decimal) * 100).toFixed(2)}%`;

const sha256 = async (text) => {
  const bytes = new TextEncoder().encode(text);
  const digest = await crypto.subtle.digest("SHA-256", bytes);
  return [...new Uint8Array(digest)]
    .map((value) => value.toString(16).padStart(2, "0"))
    .join("");
};

const svgElement = (name, attributes = {}) => {
  const element = document.createElementNS(SVG_NS, name);
  Object.entries(attributes).forEach(([key, value]) => element.setAttribute(key, String(value)));
  return element;
};

const pathFrom = (points) => points
  .map((point, index) => `${index === 0 ? "M" : "L"}${point.x.toFixed(2)},${point.y.toFixed(2)}`)
  .join(" ");

const renderChart = (trace) => {
  const svg = select("[data-chart]");
  const width = 1200;
  const height = 520;
  const margin = { top: 28, right: 34, bottom: 54, left: 88 };
  const innerWidth = width - margin.left - margin.right;
  const innerHeight = height - margin.top - margin.bottom;
  const points = trace.points.map((point) => ({
    ...point,
    risk: Number(point.empirical_risk_decimal),
    bound: Number(point.boundary_upper_decimal),
  }));
  const threshold = Number(trace.replayed_threshold_decimal);
  const values = points.flatMap((point) => [point.risk, point.bound]).concat(threshold);
  const minValue = Math.max(Math.min(...values) * 0.72, 0.01);
  const maxValue = Math.max(...values) * 1.08;
  const logMin = Math.log(minValue);
  const logMax = Math.log(maxValue);
  const x = (n) => margin.left + ((n - 4) / (175 - 4)) * innerWidth;
  const y = (value) => margin.top + ((logMax - Math.log(value)) / (logMax - logMin)) * innerHeight;

  const tickCandidates = [0.025, 0.05, 0.1, 0.2, 0.5, 1, 2, 4];
  tickCandidates
    .filter((tick) => tick >= minValue && tick <= maxValue)
    .forEach((tick) => {
      const line = svgElement("line", {
        class: "grid-line",
        x1: margin.left,
        x2: width - margin.right,
        y1: y(tick),
        y2: y(tick),
      });
      const label = svgElement("text", {
        class: "axis-label",
        x: margin.left - 18,
        y: y(tick) + 6,
        "text-anchor": "end",
      });
      label.textContent = tick < 1 ? tick.toFixed(tick < 0.1 ? 3 : 2) : tick.toFixed(0);
      svg.append(line, label);
    });

  [4, 32, 64, 96, 128, 160, 175].forEach((tick) => {
    const label = svgElement("text", {
      class: "axis-label",
      x: x(tick),
      y: height - 18,
      "text-anchor": tick === 4 ? "start" : tick === 175 ? "end" : "middle",
    });
    label.textContent = String(tick);
    svg.append(label);
  });

  svg.append(svgElement("line", {
    class: "threshold-line",
    x1: margin.left,
    x2: width - margin.right,
    y1: y(threshold),
    y2: y(threshold),
  }));

  const boundPoints = points.map((point) => ({ x: x(point.n), y: y(point.bound) }));
  const riskPoints = points.map((point) => ({ x: x(point.n), y: y(point.risk) }));
  svg.append(
    svgElement("path", {
      class: "bound-line animated-line",
      d: pathFrom(boundPoints),
      pathLength: 1,
    }),
    svgElement("path", {
      class: "risk-line animated-line",
      d: pathFrom(riskPoints),
      pathLength: 1,
    }),
  );

  const cursor = svgElement("g");
  const cursorLine = svgElement("line", {
    class: "cursor-line",
    y1: margin.top,
    y2: height - margin.bottom,
  });
  const cursorBound = svgElement("circle", { class: "cursor-dot-bound", r: 6 });
  const cursorRisk = svgElement("circle", { class: "cursor-dot-risk", r: 5 });
  cursor.append(cursorLine, cursorBound, cursorRisk);
  svg.append(cursor);

  const updateCursor = (index) => {
    const point = points[Math.max(0, Math.min(points.length - 1, index))];
    const cursorX = x(point.n);
    cursorLine.setAttribute("x1", cursorX);
    cursorLine.setAttribute("x2", cursorX);
    cursorBound.setAttribute("cx", cursorX);
    cursorBound.setAttribute("cy", y(point.bound));
    cursorRisk.setAttribute("cx", cursorX);
    cursorRisk.setAttribute("cy", y(point.risk));
    select("[data-cursor-time]").textContent = String(point.n);
    select("[data-cursor-risk]").textContent = percent(point.empirical_risk_decimal);
    select("[data-cursor-bound]").textContent = percent(point.boundary_upper_decimal);
  };

  const interaction = svgElement("rect", {
    fill: "transparent",
    height: innerHeight,
    width: innerWidth,
    x: margin.left,
    y: margin.top,
  });
  interaction.addEventListener("pointermove", (event) => {
    const bounds = svg.getBoundingClientRect();
    const localX = ((event.clientX - bounds.left) / bounds.width) * width;
    const ratio = (localX - margin.left) / innerWidth;
    updateCursor(Math.round(ratio * (points.length - 1)));
  });
  interaction.addEventListener("pointerdown", (event) => interaction.setPointerCapture(event.pointerId));
  svg.append(interaction);
  updateCursor(points.length - 1);
};

const verificationCopy = (certificate) => ({
  data: {
    label: "Data replay",
    status: certificate.verification.data_replay.status,
    title: "Pinned bytes become exact summaries.",
    scope: certificate.verification.data_replay.scope,
  },
  lean: {
    label: "Lean kernel",
    status: certificate.verification.lean_kernel.status,
    title: "Exact summaries become a checked inequality.",
    scope: certificate.verification.lean_kernel.scope,
  },
});

const bindVerificationTabs = (certificate) => {
  const copy = verificationCopy(certificate);
  const activate = (layer) => {
    selectAll("[data-layer-button]").forEach((button) => {
      button.setAttribute("aria-selected", String(button.dataset.layerButton === layer));
    });
    select("[data-layer-label]").textContent = copy[layer].label;
    select("[data-layer-status]").textContent = copy[layer].status;
    select("[data-layer-title]").textContent = copy[layer].title;
    select("[data-layer-scope]").textContent = copy[layer].scope;
  };
  selectAll("[data-layer-button]").forEach((button) => {
    button.addEventListener("click", () => activate(button.dataset.layerButton));
  });
  activate("data");
};

const bindCertificate = (certificate, traceVerified) => {
  select("[data-study-status]").textContent = certificate.study.preregistered_status;
  select("[data-observed-risk]").textContent = percent(certificate.observed.posterior_empirical_brier_risk_decimal);
  select("[data-replayed-bound]").textContent = percent(certificate.observed.replayed_anytime_boundary_upper_decimal);
  select("[data-kernel-bound]").textContent = `< ${percent(certificate.claim.kernel_checked_upper_bound_decimal)}`;
  select("[data-receipt-digest]").textContent = certificate.data.receipt_sha256.slice(0, 16);
  select("[data-trace-status]").textContent = traceVerified ? "SHA-256 PASS" : "FAIL";
  select("[data-confidence]").textContent = percent(certificate.confidence.level_decimal);
  select("[data-certificate-id]").textContent = certificate.certificate_id;
  const list = select("[data-nonclaims]");
  certificate.verification.not_checked_by_lean.forEach((nonclaim) => {
    const item = document.createElement("li");
    item.textContent = nonclaim;
    list.append(item);
  });
  bindVerificationTabs(certificate);
};

const load = async () => {
  const [certificateResponse, traceResponse] = await Promise.all([
    fetch("gjp-certificate-v1.json", { cache: "no-store" }),
    fetch("gjp-monitor-trace-v1.json", { cache: "no-store" }),
  ]);
  if (!certificateResponse.ok || !traceResponse.ok) {
    throw new Error("certificate assets are unavailable");
  }
  const certificateText = await certificateResponse.text();
  const traceText = await traceResponse.text();
  const certificate = JSON.parse(certificateText);
  const trace = JSON.parse(traceText);
  const traceDigest = await sha256(traceText);
  const traceVerified = traceDigest === certificate.trace.sha256;
  if (!traceVerified || trace.source_receipt_sha256 !== certificate.data.receipt_sha256) {
    throw new Error("monitor trace does not match the compact certificate");
  }
  bindCertificate(certificate, traceVerified);
  renderChart(trace);
};

load().catch((error) => {
  console.error(error);
  select("[data-chart-error]").hidden = false;
  select("[data-trace-status]").textContent = "FAIL";
  select("[data-layer-status]").textContent = "UNAVAILABLE";
});
