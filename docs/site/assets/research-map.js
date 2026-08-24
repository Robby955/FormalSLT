(() => {
  const lab = document.querySelector("[data-proof-lab]");
  if (!lab) return;

  const routes = {
    classical: {
      kicker: "Classical learning theory",
      title: "Capacity control becomes a finite-sample learning guarantee.",
      summary:
        "Sauer–Shelah bounds the realized label patterns; Rademacher complexity turns that growth control into uniform deviation and ERM excess risk.",
      assumptions:
        "A finite binary hypothesis class and a trace VC-dimension bound",
      result:
        "A finite-sample uniform-deviation and ERM excess-risk bound",
      href: "theorems/",
      nodes: {
        input: ["Binary class", "finite trace"],
        control: ["Sauer–Shelah", "growth bound"],
        selection: ["Rademacher", "uniform deviation"],
        endpoint: ["ERM risk", "finite sample"],
      },
      description:
        "A binary hypothesis class passes through Sauer–Shelah growth control and Rademacher complexity to reach a finite-sample ERM excess-risk bound.",
    },
    iid: {
      kicker: "PAC-Bayes generalization",
      title: "One event controls every sample size and eligible posterior.",
      summary:
        "The posterior may be selected after seeing the sample. The prior and loss family may not.",
      assumptions: "IID observations and bounded measurable losses",
      result:
        "An empirical-Bernstein PAC-Bayes bound, simultaneous over all n ≥ 2",
      href:
        "FormalSLT/PACBayes/ContinuousInfiniteEmpiricalBernsteinStitch.html#FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch.exists_continuousInfiniteEmpiricalBernstein_event",
      nodes: {
        input: ["IID sample", "bounded loss"],
        control: ["Bessel variance", "Bernstein scale"],
        selection: ["PAC-Bayes", "posterior after data"],
        endpoint: ["All n", "one event"],
      },
      description:
        "An IID sample passes through Bessel empirical variance, PAC-Bayes change of measure, and simultaneous selection to reach one event controlling every sample size and eligible posterior.",
    },
    sequential: {
      kicker: "Anytime-valid inference",
      title: "Evidence remains calibrated while time is chosen adaptively.",
      summary:
        "A nonnegative supermartingale becomes an e-process, then a time-uniform testing statement. The stopping rule does not receive a hidden second budget.",
      assumptions:
        "A filtration, nonnegative supermartingale, and unit initial integral",
      result:
        "Time-uniform Type-I control and optional continuation for the stopped process",
      href:
        "FormalSLT/AnytimeValid/EProcess.html#FormalSLT.AnytimeValid.eProcess_typeI_control",
      nodes: {
        input: ["Data stream", "filtration"],
        control: ["E-process", "supermartingale"],
        selection: ["Stopping rule", "chosen from history"],
        endpoint: ["All times", "Type-I control"],
      },
      description:
        "A filtered data stream passes through an e-process and a stopping rule to reach time-uniform Type-I control.",
    },
    trajectory: {
      kicker: "Adaptive trajectories",
      title: "The policy and posterior may react to the path already observed.",
      summary:
        "Scores and tilt atoms are declared before scoring. Within that catalog, the posterior and tilt may be selected from the realized trajectory.",
      assumptions:
        "Prefix-dependent kernels, predictable bounded scores, and a predeclared catalog",
      result:
        "An all-time trajectory PAC-Bayes event with a selected width tending to zero",
      href:
        "FormalSLT/StochasticDynamics/TrajectoryEmpiricalBernsteinPACBayesCountable.html#FormalSLT.StochasticDynamics.exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event",
      nodes: {
        input: ["Adaptive path", "prefix kernels"],
        control: ["Predictable score", "conditional centering"],
        selection: ["Catalog + posterior", "chosen from path"],
        endpoint: ["All times", "width → 0"],
      },
      description:
        "An adaptive trajectory passes through predictable conditional centering and predeclared catalog selection to reach an all-time PAC-Bayes event with vanishing selected width.",
    },
    stationary: {
      kicker: "Stationary systems",
      title: "A pathwise guarantee is transferred to long-run stationary risk.",
      summary:
        "Finite-depth Poisson correction handles the trajectory-to-stationary gap. A finite candidate catalog can add transition confidence from the same observed path.",
      assumptions:
        "Finite states, row coverage, a predeclared kernel catalog, and selected contraction",
      result:
        "A same-trajectory stationary-risk certificate for the selected candidate",
      href:
        "FormalSLT/StochasticDynamics/EmpiricalStationaryCatalog.html#FormalSLT.StochasticDynamics.exists_selectedCanonicalEmpiricalStationaryCatalog_event",
      nodes: {
        input: ["Markov path", "same trajectory"],
        control: ["Poisson correction", "finite depth"],
        selection: ["Kernel catalog", "transition confidence"],
        endpoint: ["Stationary", "selected risk"],
      },
      description:
        "A finite-state Markov path passes through a finite-depth Poisson correction and empirical kernel selection to reach a stationary-risk certificate for the selected candidate.",
    },
  };

  const tabs = Array.from(lab.querySelectorAll('[role="tab"]'));
  const title = lab.querySelector("[data-route-title]");
  const kicker = lab.querySelector("[data-route-kicker]");
  const summary = lab.querySelector("[data-route-summary]");
  const assumptions = lab.querySelector("[data-route-assumptions]");
  const result = lab.querySelector("[data-route-result]");
  const link = lab.querySelector("[data-route-link]");
  const svgTitle = lab.querySelector("#proof-route-title");
  const svgDescription = lab.querySelector("#proof-route-description");
  const display = lab.querySelector(".proof-lab-display");
  const panel = lab.querySelector("[role=tabpanel]");

  function setRoute(name, focusTab = false) {
    const route = routes[name];
    if (!route) return;

    for (const tab of tabs) {
      const selected = tab.dataset.route === name;
      tab.setAttribute("aria-selected", String(selected));
      tab.tabIndex = selected ? 0 : -1;
      if (selected) panel.setAttribute("aria-labelledby", tab.id);
      if (selected && focusTab) tab.focus();
    }

    kicker.textContent = route.kicker;
    title.textContent = route.title;
    summary.textContent = route.summary;
    assumptions.textContent = route.assumptions;
    result.textContent = route.result;
    link.href = route.href;
    svgTitle.textContent = `${route.kicker} proof route`;
    svgDescription.textContent = route.description;

    for (const [node, values] of Object.entries(route.nodes)) {
      for (const label of lab.querySelectorAll(`[data-node-label="${node}"]`)) {
        label.textContent = values[0];
      }
      for (const detail of lab.querySelectorAll(`[data-node-detail="${node}"]`)) {
        detail.textContent = values[1];
      }
    }

    display.dataset.activeRoute = name;
  }

  for (const [index, tab] of tabs.entries()) {
    tab.addEventListener("click", () => setRoute(tab.dataset.route));
    tab.addEventListener("keydown", (event) => {
      if (!['ArrowLeft', 'ArrowRight', 'Home', 'End'].includes(event.key)) return;
      event.preventDefault();
      let next = index;
      if (event.key === "ArrowLeft") next = (index - 1 + tabs.length) % tabs.length;
      if (event.key === "ArrowRight") next = (index + 1) % tabs.length;
      if (event.key === "Home") next = 0;
      if (event.key === "End") next = tabs.length - 1;
      setRoute(tabs[next].dataset.route, true);
    });
  }

  setRoute("classical");
})();
