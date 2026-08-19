import FormalSLT.StochasticDynamics.EmpiricalStationaryCatalog

/-!
# Informative selected stationary-catalog receipt

This receipt uses a fair two-state true kernel and two small, predeclared
candidate perturbations.  Candidate, risk tilt, and a point posterior branch
on the first observed transition; the reported numerical certificate fixes
the Poisson depth at zero.  The receipt supplies exact row-TV errors rather
than estimating them from the same path.  The existing structural catalog
checker separately exercises the empirical transition-confidence event.

The eventual capstone below does not assert that a named path belongs to an
outer-probability event.  It constructs two high-mass branch families, proves
that each family has mass strictly larger than the common event's failure
budget, and obtains one certified path in each branch by intersection.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayes
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open FormalSLT.PACBayes.StabilityBridge

namespace FormalSLT.Examples.CheckEmpiricalStationaryCatalogInformative

open FormalSLT.StochasticDynamics

noncomputable section

def receiptHorizon : ℕ := 134217728

def receiptFairKernel (_x : Bool) : PMF Bool :=
  PMF.ofFintype (fun _y ↦ ((1 / 2 : NNReal) : ENNReal)) (by
    have hNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
    have h : ((1 / 2 : NNReal) : ENNReal) +
        ((1 / 2 : NNReal) : ENNReal) = 1 := by
      rw [← ENNReal.coe_add, hNN]
      rfl
    simpa [Fintype.sum_bool, two_mul] using h)

def receiptFairStationary : PMF Bool := receiptFairKernel false

def receiptCandidateZero (_x : Bool) : PMF Bool :=
  PMF.ofFintype
    (fun y ↦ if y then
      ((33 / 64 : NNReal) : ENNReal)
    else
      ((31 / 64 : NNReal) : ENNReal))
    (by
      have hNN : (33 / 64 : NNReal) + 31 / 64 = 1 := by norm_num
      have h : ((33 / 64 : NNReal) : ENNReal) +
          ((31 / 64 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hNN]
        rfl
      simpa [Fintype.sum_bool, add_comm] using h)

def receiptCandidateOne (x : Bool) : PMF Bool :=
  PMF.ofFintype
    (fun y ↦ if x = y then
      ((17 / 32 : NNReal) : ENNReal)
    else
      ((15 / 32 : NNReal) : ENNReal))
    (by
      have hNN : (17 / 32 : NNReal) + 15 / 32 = 1 := by norm_num
      have h : ((17 / 32 : NNReal) : ENNReal) +
          ((15 / 32 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hNN]
        rfl
      cases x <;> simpa [Fintype.sum_bool, add_comm] using h)

def receiptCandidate (c : Bool) : Bool → PMF Bool :=
  if c then receiptCandidateOne else receiptCandidateZero

def receiptReference (_c : Bool) : PMF Bool := receiptFairStationary

/-- The two hypotheses swap the values `3/5` and `2/5` across the current
state.  Their fair-stationary risks are both `1/2`. -/
def receiptScore (i : Bool) (current _next : Bool) : ℝ :=
  if current = i then 3 / 5 else 2 / 5

theorem receiptScore_mem_Icc :
    ∀ i x y, receiptScore i x y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i x y
  by_cases h : x = i <;> norm_num [receiptScore, h]

def receiptD (_c : Bool) : ℝ := 1 / 5

def receiptCandidateWeight (_c : Bool) : ℝ := 1 / 2

def receiptPrior (_i : Bool) : ℝ := 1 / 2

def receiptSelectCandidate (x : ℕ → Bool) (_n : ℕ) : Bool := x 1

def receiptSelectDepth (_x : ℕ → Bool) (_n : ℕ) : ℕ := 0

def receiptSelectRiskTilt (x : ℕ → Bool) (_n : ℕ) : ℕ :=
  if x 1 then 12 else 11

def receiptSelectPosterior (x : ℕ → Bool) (_n : ℕ) : Bool → ℝ :=
  diracPosterior (x 1)

def receiptFirstBranch (b : Bool) : Set (ℕ → Bool) :=
  {x | x 1 = b}

/-- A positive-mass two-transition cylinder inside selector branch `b`.
The second transition visits the state opposite to `b`, which both exercises
the selected corrected score and guarantees that both source rows occur. -/
def receiptInformativeBranch (b : Bool) : Set (ℕ → Bool) :=
  {x | x 1 = b ∧ x 2 = !b}

theorem receiptCandidateWeight_isFullSupport :
    IsFullSupportPMF receiptCandidateWeight := by
  constructor
  · constructor
    · intro c
      norm_num [receiptCandidateWeight]
    · norm_num [receiptCandidateWeight, Fintype.sum_bool]
  · intro c
    norm_num [receiptCandidateWeight]

theorem receiptPrior_isFullSupport : IsFullSupportPMF receiptPrior := by
  constructor
  · constructor
    · intro i
      norm_num [receiptPrior]
    · norm_num [receiptPrior, Fintype.sum_bool]
  · intro i
    norm_num [receiptPrior]

theorem receiptSelectPosterior_isPMF :
    ∀ x n, IsPMF (receiptSelectPosterior x n) := by
  intro x n
  exact diracPosterior_isPMF (x 1)

theorem receiptFairStationary_invariant :
    IsInvariantPMF receiptFairKernel receiptFairStationary := by
  unfold IsInvariantPMF receiptFairStationary
  change (receiptFairKernel false).bind (fun _ ↦ receiptFairKernel false) =
    receiptFairKernel false
  exact PMF.bind_const _ _

theorem receiptFair_dobrushin :
    finiteDobrushinCoefficient receiptFairKernel = 0 := by
  apply le_antisymm
  · unfold finiteDobrushinCoefficient
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro x _hx
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro y _hy
    norm_num [finitePMFTotalVariation, receiptFairKernel,
      PMF.ofFintype_apply, Fintype.sum_bool]
  · exact finiteDobrushinCoefficient_nonneg _

theorem receiptCandidateZero_dobrushin :
    finiteDobrushinCoefficient receiptCandidateZero = 0 := by
  apply le_antisymm
  · unfold finiteDobrushinCoefficient
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro x _hx
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro y _hy
    norm_num [finitePMFTotalVariation, receiptCandidateZero,
      PMF.ofFintype_apply, Fintype.sum_bool]
  · exact finiteDobrushinCoefficient_nonneg _

theorem receiptCandidateOne_dobrushin :
    finiteDobrushinCoefficient receiptCandidateOne = 1 / 16 := by
  apply le_antisymm
  · unfold finiteDobrushinCoefficient
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro x _hx
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro y _hy
    fin_cases x <;> fin_cases y <;>
      norm_num [finitePMFTotalVariation, receiptCandidateOne,
        PMF.ofFintype_apply, Fintype.sum_bool]
  · have h := finitePMFTotalVariation_le_finiteDobrushinCoefficient
      receiptCandidateOne false true
    norm_num [finitePMFTotalVariation, receiptCandidateOne,
      PMF.ofFintype_apply, Fintype.sum_bool] at h ⊢
    exact h

theorem receiptCandidate_coefficient_lt_one :
    ∀ c, finiteDobrushinCoefficient (receiptCandidate c) < 1 := by
  intro c
  cases c
  · norm_num [receiptCandidate, receiptCandidateZero_dobrushin]
  · norm_num [receiptCandidate, receiptCandidateOne_dobrushin]

theorem receiptD_nonneg : ∀ c, 0 ≤ receiptD c := by
  intro c
  norm_num [receiptD]

theorem receipt_markovRowRisk (Q : Bool → PMF Bool) (i x : Bool) :
    markovRowRisk Q (receiptScore i) x =
      if x = i then 3 / 5 else 2 / 5 := by
  unfold markovRowRisk receiptScore
  simp only [PMF.integral_eq_sum, smul_eq_mul]
  rw [← Finset.sum_mul, finitePMF_real_mass_sum]
  simp

theorem receipt_stationaryMarkovRisk (Q : Bool → PMF Bool) (i : Bool) :
    stationaryMarkovRisk Q receiptFairStationary (receiptScore i) = 1 / 2 := by
  unfold stationaryMarkovRisk
  simp_rw [receipt_markovRowRisk]
  cases i <;>
    norm_num [receiptFairStationary, receiptFairKernel,
      PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]

theorem receipt_centeredOscillation : ∀ c i,
    finiteOscillation
      (centeredMarkovRowRisk (receiptCandidate c) (receiptReference c)
        (receiptScore i)) = 1 / 5 := by
  intro c i
  apply le_antisymm
  · apply finiteOscillation_le
    intro x y
    rw [centeredMarkovRowRisk, centeredMarkovRowRisk,
      receipt_markovRowRisk, receipt_markovRowRisk]
    fin_cases i <;> fin_cases x <;> fin_cases y <;> norm_num
  · have h := abs_sub_le_finiteOscillation
      (centeredMarkovRowRisk (receiptCandidate c) (receiptReference c)
        (receiptScore i)) false true
    rw [centeredMarkovRowRisk, centeredMarkovRowRisk,
      receipt_markovRowRisk, receipt_markovRowRisk] at h
    fin_cases i <;> norm_num at h ⊢ <;> exact h

theorem receiptD_bounds : ∀ c i,
    finiteOscillation
      (centeredMarkovRowRisk (receiptCandidate c) (receiptReference c)
        (receiptScore i)) ≤ receiptD c := by
  intro c i
  rw [receipt_centeredOscillation]
  rfl

theorem receiptCandidate_rowTV (c z : Bool) :
    finitePMFTotalVariation (receiptFairKernel z) (receiptCandidate c z) =
      if c then 1 / 32 else 1 / 64 := by
  cases c <;> cases z <;>
    norm_num [receiptCandidate, finitePMFTotalVariation,
      receiptFairKernel, receiptCandidateZero, receiptCandidateOne,
      PMF.ofFintype_apply, Fintype.sum_bool]

theorem receiptSelectedKL (x : ℕ → Bool) (n : ℕ) :
    klDiv (receiptSelectPosterior x n) receiptPrior = Real.log 2 := by
  change klDiv (diracPosterior (x 1)) (fun _ : Bool ↦ 1 / 2) = Real.log 2
  have hprior : (fun _ : Bool ↦ (1 / 2 : ℝ)) =
      finiteUniformRealPMF Bool := by
    funext i
    norm_num [finiteUniformRealPMF]
  rw [hprior]
  exact klDiv_dirac_finiteUniformRealPMF (x 1)

theorem receiptSelectedKL_pos (x : ℕ → Bool) (n : ℕ) :
    0 < klDiv (receiptSelectPosterior x n) receiptPrior := by
  rw [receiptSelectedKL]
  exact Real.log_pos (by norm_num)

/-! ## Positive-mass selector branches -/

theorem receiptInformativeBranch_measurable (b : Bool) :
    MeasurableSet (receiptInformativeBranch b) := by
  change MeasurableSet
    ({x : ℕ → Bool | x 1 = b} ∩ {x : ℕ → Bool | x 2 = !b})
  have hnot : MeasurableSet ({(!b)} : Set Bool) :=
    MeasurableSet.singleton (!b)
  have htwo : MeasurableSet {x : ℕ → Bool | x 2 = !b} := by
    change MeasurableSet ((fun x : ℕ → Bool ↦ x 2) ⁻¹' {(!b)})
    exact (measurable_pi_apply 2) hnot
  exact ((measurable_pi_apply 1) (MeasurableSet.singleton b)).inter htwo

theorem receiptInformativeBranch_subset_firstBranch (b : Bool) :
    receiptInformativeBranch b ⊆ receiptFirstBranch b := by
  intro x hx
  exact hx.1

theorem receiptInformativeBranch_allRowsVisited
    {b : Bool} {x : ℕ → Bool} (hx : x ∈ receiptInformativeBranch b)
    {n : ℕ} (hn : 3 ≤ n) :
    ∀ z : Bool, 0 < transitionVisitMass z n x := by
  intro z
  have hone : x 1 = b := hx.1
  have htwo : x 2 = !b := hx.2
  have hvisit_of {k : ℕ} (hk : k < n) (hxk : x k = z) :
      0 < transitionVisitMass z n x := by
    unfold transitionVisitMass
    have hmem : k ∈ Finset.range n := Finset.mem_range.mpr hk
    rw [Finset.sum_pos_iff_of_nonneg]
    · exact ⟨k, hmem, by rw [if_pos hxk]; norm_num⟩
    · intro l _hl
      split_ifs <;> norm_num
  cases b <;> cases z
  · exact hvisit_of (k := 1) (by omega) (by simpa using hone)
  · exact hvisit_of (k := 2) (by omega) (by simpa using htwo)
  · exact hvisit_of (k := 2) (by omega) (by simpa using htwo)
  · exact hvisit_of (k := 1) (by omega) (by simpa using hone)

theorem receiptInformativeBranch_mass (b : Bool) :
    (markovPathMeasure receiptFairKernel false)
        (receiptInformativeBranch b) = 1 / 4 := by
  let κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → Bool) Bool :=
    prefixKernel receiptFairKernel
  let u0 : (i : Finset.Iic 0) → Bool := fun _ ↦ false
  let one : Finset.Iic 1 := ⟨1, Finset.mem_Iic.mpr le_rfl⟩
  let S : Set ((i : Finset.Iic 1) → Bool) :=
    {u | u one = b}
  let T : Set Bool := {(!b)}
  have hS : MeasurableSet S := by
    change MeasurableSet
      ((fun u : (i : Finset.Iic 1) → Bool ↦ u one) ⁻¹' ({b} : Set Bool))
    exact (measurable_pi_apply one)
      (MeasurableSet.singleton b)
  have hT : MeasurableSet T := MeasurableSet.singleton (!b)
  have hprefixMap :
      (ProbabilityTheory.Kernel.partialTraj
        (X := fun _ : ℕ ↦ Bool) κ 0 1 u0).map
          (fun u : (i : Finset.Iic 1) → Bool ↦ u one) =
        κ 0 u0 := by
    have h := congrArg (fun K ↦ K u0)
      (ProbabilityTheory.Kernel.map_partialTraj_succ_self
        (X := fun _ : ℕ ↦ Bool) (κ := κ) 0)
    rw [← ProbabilityTheory.Kernel.map_apply _
      (measurable_pi_apply one) u0]
    exact h
  have hprefix :
      ProbabilityTheory.Kernel.partialTraj
        (X := fun _ : ℕ ↦ Bool) κ 0 1 u0 S = 1 / 2 := by
    have h := congrArg (fun μ : Measure Bool ↦ μ ({b} : Set Bool)) hprefixMap
    rw [Measure.map_apply (measurable_pi_apply one)
      (MeasurableSet.singleton b)] at h
    have hset :
        (fun u : (i : Finset.Iic 1) → Bool ↦ u one) ⁻¹' ({b} : Set Bool) =
          S := by
      ext u
      simp [S]
    rw [hset] at h
    have hrhs : κ 0 u0 ({b} : Set Bool) = 1 / 2 := by
      change (receiptFairKernel false).toMeasure ({b} : Set Bool) = 1 / 2
      rw [(receiptFairKernel false).toMeasure_apply_singleton b
        (MeasurableSet.singleton b)]
      cases b <;> norm_num [receiptFairKernel, PMF.ofFintype_apply]
    exact h.trans hrhs
  have hnext : ∀ u : (i : Finset.Iic 1) → Bool,
      κ 1 u T = 1 / 2 := by
    intro u
    change (receiptFairKernel (u one)).toMeasure ({(!b)} : Set Bool) = 1 / 2
    rw [(receiptFairKernel (u one)).toMeasure_apply_singleton (!b)
      (MeasurableSet.singleton (!b))]
    cases b <;> norm_num [receiptFairKernel, PMF.ofFintype_apply]
  have hjoint := ProbabilityTheory.Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ : ℕ ↦ Bool) (κ := κ) (a := 0) (b := 1)
    (x₀ := u0) (Nat.zero_le 1)
  have h := congrArg
    (fun μ : Measure (((i : Finset.Iic 1) → Bool) × Bool) ↦ μ (S ×ˢ T))
    hjoint
  rw [Measure.compProd_apply_prod hS hT,
    Measure.map_apply (by fun_prop) (hS.prod hT)] at h
  have hleft :
      ∫⁻ u in S, κ 1 u T
          ∂ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ Bool) κ 0 1 u0 = 1 / 4 := by
    simp_rw [hnext]
    rw [setLIntegral_const]
    rw [hprefix]
    apply (ENNReal.toReal_eq_toReal_iff'
      (x := (1 / 2 : ENNReal) * (1 / 2 : ENNReal))
      (y := (1 / 4 : ENNReal))
      (ENNReal.mul_ne_top (by norm_num) (by norm_num))
      (by norm_num)).mp
    norm_num
  rw [hleft] at h
  have hpreimage :
      (fun x : ℕ → Bool ↦
          (Preorder.frestrictLe 1 x, x (1 + 1))) ⁻¹' (S ×ˢ T) =
        receiptInformativeBranch b := by
    ext x
    simp [S, T, one, receiptInformativeBranch,
      Preorder.frestrictLe_apply]
  rw [hpreimage] at h
  simpa [markovPathMeasure, κ, u0] using h.symm

theorem receiptInformativeBranch_real_mass (b : Bool) :
    (markovPathMeasure receiptFairKernel false).real
        (receiptInformativeBranch b) = 1 / 4 := by
  rw [measureReal_def, receiptInformativeBranch_mass]
  norm_num

/-! ## The common catalog event and theorem-produced branch paths -/

def receiptRiskBad : Set (ℕ → Bool) :=
  empiricalStationaryCatalogExceptionalEvent
    receiptFairKernel receiptCandidate receiptReference receiptScore receiptD
    receiptCandidateWeight receiptPrior (1 / 8)

theorem receiptRiskBad_mass_le :
    (markovPathMeasure receiptFairKernel false).real receiptRiskBad ≤ 1 / 8 := by
  exact empiricalStationaryCatalogExceptionalEvent_mass_le
    receiptFairKernel false receiptCandidate receiptReference
    receiptScore_mem_Icc receiptD_nonneg
    receiptCandidate_coefficient_lt_one receiptD_bounds
    receiptCandidateWeight_isFullSupport receiptPrior_isFullSupport
    (by norm_num)

theorem receiptGoodPath_in_each_branch (b : Bool) :
    ∃ x : ℕ → Bool,
      x ∈ receiptInformativeBranch b ∧ x ∉ receiptRiskBad := by
  by_contra h
  push Not at h
  have hsubset : receiptInformativeBranch b ⊆ receiptRiskBad := by
    intro x hx
    exact h x hx
  have hmono := measureReal_mono
    (μ := markovPathMeasure receiptFairKernel false) hsubset
  rw [receiptInformativeBranch_real_mass] at hmono
  have hbad := receiptRiskBad_mass_le
  linarith

/-! ## Selected exact candidate certificate -/

def receiptSelectEta (x : ℕ → Bool) : ℝ :=
  if x 1 then 1 / 32 else 1 / 64

def receiptSelectedBoundary (x : ℕ → Bool) : ℝ :=
  empiricalStationaryCatalogBoundary
    receiptCandidate receiptReference receiptScore receiptD
    receiptCandidateWeight receiptPrior
    (receiptSelectPosterior x receiptHorizon) (1 / 8)
    (receiptSelectEta x) (receiptSelectCandidate x receiptHorizon)
    (receiptSelectDepth x receiptHorizon)
    (receiptSelectRiskTilt x receiptHorizon) receiptHorizon x

theorem receiptSelectEta_nonneg (x : ℕ → Bool) :
    0 ≤ receiptSelectEta x := by
  cases h : x 1 <;> norm_num [receiptSelectEta, h]

theorem receiptSelectedRowTV (x : ℕ → Bool) :
    ∀ z : Bool,
      finitePMFTotalVariation (receiptFairKernel z)
          (receiptCandidate (receiptSelectCandidate x receiptHorizon) z) ≤
        receiptSelectEta x := by
  intro z
  rw [receiptCandidate_rowTV]
  cases h : x 1 <;>
    norm_num [receiptSelectCandidate, receiptSelectEta, h]

theorem receiptSelected_stationaryRisk (x : ℕ → Bool) :
    stationaryPosteriorMarkovRisk receiptFairKernel receiptFairStationary
        receiptScore (receiptSelectPosterior x receiptHorizon) = 1 / 2 := by
  unfold stationaryPosteriorMarkovRisk receiptSelectPosterior
  rw [pacBayesPosteriorAverage_dirac]
  exact receipt_stationaryMarkovRisk receiptFairKernel (x 1)

theorem receiptSelected_empiricalRisk_le (x : ℕ → Bool) :
    empiricalTransitionPosteriorRisk receiptScore
        (receiptSelectPosterior x receiptHorizon) receiptHorizon x ≤ 3 / 5 := by
  unfold empiricalTransitionPosteriorRisk receiptSelectPosterior
  rw [pacBayesPosteriorAverage_dirac]
  unfold empiricalTransitionRisk runningMean runningSum
  apply (div_le_iff₀ (by norm_num [receiptHorizon])).2
  calc
    ∑ k ∈ Finset.range receiptHorizon,
        receiptScore (x 1) (x k) (x (k + 1)) ≤
      ∑ _k ∈ Finset.range receiptHorizon, (3 / 5 : ℝ) := by
        exact Finset.sum_le_sum fun k _hk ↦ by
          by_cases h : x k = x 1 <;> norm_num [receiptScore, h]
    _ = receiptHorizon * (3 / 5 : ℝ) := by simp
    _ = (3 / 5 : ℝ) * receiptHorizon := by ring

theorem receiptSelected_catalog_bound
    {x : ℕ → Bool} (hx : x ∉ receiptRiskBad) :
    stationaryPosteriorMarkovRisk receiptFairKernel receiptFairStationary
        receiptScore (receiptSelectPosterior x receiptHorizon) <
      empiricalTransitionPosteriorRisk receiptScore
          (receiptSelectPosterior x receiptHorizon) receiptHorizon x +
        receiptSelectedBoundary x := by
  exact empiricalStationaryCatalog_allPosteriors_of_not_mem
    receiptFairKernel receiptFairStationary receiptFairStationary_invariant
    receiptCandidate receiptReference receiptScore_mem_Icc
    receiptD_nonneg receiptCandidate_coefficient_lt_one receiptD_bounds
    receiptCandidateWeight_isFullSupport receiptPrior_isFullSupport
    (by norm_num) hx
    (receiptSelectCandidate x receiptHorizon)
    (receiptSelectDepth x receiptHorizon)
    (receiptSelectRiskTilt x receiptHorizon)
    (receiptSelectEta_nonneg x) (receiptSelectedRowTV x)
    (receiptSelectPosterior x receiptHorizon)
    (receiptSelectPosterior_isPMF x receiptHorizon)
    receiptHorizon (by norm_num [receiptHorizon])

/-! ## Uniform numerical width at the reported horizon -/

def receiptSelectedCorrectedScore (x : ℕ → Bool) : Bool → TrajectoryScore Bool :=
  empiricalStationaryCatalogCorrectedScore
    receiptCandidate receiptReference receiptScore receiptD
    (receiptSelectCandidate x receiptHorizon)
    (receiptSelectDepth x receiptHorizon)

theorem receiptSelectedBoundary_eq (x : ℕ → Bool) :
    receiptSelectedBoundary x =
      trajectoryCountableEmpiricalBernsteinPACBayesBoundary
          receiptPrior (receiptSelectedCorrectedScore x)
          (receiptSelectPosterior x receiptHorizon) (1 / 32)
          (receiptSelectRiskTilt x receiptHorizon) receiptHorizon x +
        1 / 5 + 2 * receiptSelectEta x := by
  cases h : x 1 <;>
    norm_num [receiptSelectedBoundary, receiptSelectedCorrectedScore,
      empiricalStationaryCatalogBoundary, empiricalStationaryCatalogSpan,
      finiteDepthPoissonClosedSpanBound, receiptSelectCandidate,
      receiptSelectDepth, receiptSelectRiskTilt, receiptSelectEta,
      receiptCandidateWeight, receiptD, receiptCandidate,
      receiptCandidateZero_dobrushin, receiptCandidateOne_dobrushin,
      polynomialForwardTiltWeight,
      FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch.reverseDyadicEpochWeight,
      h]

theorem receiptSelectedCorrectedScore_mem_Icc (x : ℕ → Bool) :
    ∀ i n u y,
      receiptSelectedCorrectedScore x i n u y ∈ Set.Icc (0 : ℝ) 1 := by
  exact empiricalStationaryCatalogCorrectedScore_mem_Icc
    receiptCandidate receiptReference receiptScore_mem_Icc
    receiptD_nonneg receiptCandidate_coefficient_lt_one receiptD_bounds
    (receiptSelectCandidate x receiptHorizon)
    (receiptSelectDepth x receiptHorizon)

theorem receiptSelectedRate_log_le (x : ℕ → Bool) :
    Real.log
        ((((receiptSelectRiskTilt x receiptHorizon : ℝ) + 1) *
            ((receiptSelectRiskTilt x receiptHorizon : ℝ) + 2)) /
          (1 / 32 : ℝ)) ≤ 13 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  cases h : x 1
  · have hmono : Real.log (4992 : ℝ) ≤ Real.log (8192 : ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hpow : Real.log (8192 : ℝ) = 13 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 13 using 1 <;> norm_num
    norm_num [receiptSelectRiskTilt, h]
    rw [hpow] at hmono
    nlinarith
  · have hmono : Real.log (5824 : ℝ) ≤ Real.log (8192 : ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hpow : Real.log (8192 : ℝ) = 13 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 13 using 1 <;> norm_num
    norm_num [receiptSelectRiskTilt, h]
    rw [hpow] at hmono
    nlinarith

theorem receiptSelectedRate_lt_one_hundredth (x : ℕ → Bool) :
    geometricPolynomialForwardRate
        (fun _ ↦ klDiv (receiptSelectPosterior x receiptHorizon) receiptPrior)
        (1 / 32) (receiptSelectRiskTilt x receiptHorizon) < 1 / 100 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog := receiptSelectedRate_log_le x
  rw [receiptSelectedKL] at *
  cases h : x 1 <;>
    norm_num [geometricPolynomialForwardRate, geometricForwardTilt,
      receiptSelectRiskTilt, h] at hlog ⊢ <;> nlinarith

theorem receiptSelectedTrajectoryBoundary_lt_one_hundredth (x : ℕ → Bool) :
    trajectoryCountableEmpiricalBernsteinPACBayesBoundary
        receiptPrior (receiptSelectedCorrectedScore x)
        (receiptSelectPosterior x receiptHorizon) (1 / 32)
        (receiptSelectRiskTilt x receiptHorizon) receiptHorizon x < 1 / 100 := by
  have hfloor : geometricForwardTiltTime
      (receiptSelectRiskTilt x receiptHorizon) ≤ receiptHorizon := by
    cases h : x 1 <;>
      norm_num [geometricForwardTiltTime, receiptSelectRiskTilt,
        receiptHorizon, h]
  have hle := countableForwardBesselPACBayesBoundary_le_geometricRate
    receiptPrior_isFullSupport
    (receiptSelectPosterior_isPMF x receiptHorizon)
    (show (0 : ℝ) < 1 / 32 by norm_num)
    (show (1 / 32 : ℝ) ≤ 1 by norm_num)
    (fun i k path ↦ observedTrajectoryScore_mem_Icc
      (receiptSelectedCorrectedScore_mem_Icc x i) k path)
    (receiptSelectRiskTilt x receiptHorizon) receiptHorizon
    (by norm_num [receiptHorizon]) hfloor x
  exact hle.trans_lt (receiptSelectedRate_lt_one_hundredth x)

theorem receiptSelectedBoundary_lt_eleven_fortieths (x : ℕ → Bool) :
    receiptSelectedBoundary x < 11 / 40 := by
  rw [receiptSelectedBoundary_eq]
  have htraj := receiptSelectedTrajectoryBoundary_lt_one_hundredth x
  cases h : x 1 <;> norm_num [receiptSelectEta, h] at htraj ⊢ <;> linarith

/-! ## Strictly positive observed Bessel variance on both branches -/

def receiptSelectedObservedScore (x : ℕ → Bool) (k : ℕ) : ℝ :=
  observedTrajectoryScore
    (receiptSelectedCorrectedScore x (x 1)) k x

theorem receiptSelectedCorrectedScore_depthZero (x : ℕ → Bool)
    (i : Bool) (n : ℕ) (u : (k : Finset.Iic n) → Bool) (y : Bool) :
    receiptSelectedCorrectedScore x i n u y =
      receiptScore i (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) y := by
  unfold receiptSelectedCorrectedScore receiptSelectDepth
  unfold empiricalStationaryCatalogCorrectedScore
    empiricalStationaryCatalogSpan empiricalStationaryCatalogPotential
    poissonCorrectedTrajectoryScore poissonCorrectedTransitionScore
    finiteDepthPoissonClosedSpanBound finiteDepthPoissonPotential
    iteratedMarkovPotentialMean
  norm_num
  rfl

theorem receiptSelectedObservedScore_one
    {b : Bool} {x : ℕ → Bool} (hx : x ∈ receiptInformativeBranch b) :
    receiptSelectedObservedScore x 1 = 3 / 5 := by
  unfold receiptSelectedObservedScore observedTrajectoryScore
  rw [receiptSelectedCorrectedScore_depthZero]
  have hone : x 1 = b := hx.1
  simp [receiptScore, Preorder.frestrictLe_apply, hone]

theorem receiptSelectedObservedScore_two
    {b : Bool} {x : ℕ → Bool} (hx : x ∈ receiptInformativeBranch b) :
    receiptSelectedObservedScore x 2 = 2 / 5 := by
  unfold receiptSelectedObservedScore observedTrajectoryScore
  rw [receiptSelectedCorrectedScore_depthZero]
  have hone : x 1 = b := hx.1
  have htwo : x 2 = !b := hx.2
  cases b <;>
    norm_num [receiptScore, Preorder.frestrictLe_apply, hone, htwo]

theorem receiptSelectedBesselQ_pos
    {b : Bool} {x : ℕ → Bool} (hx : x ∈ receiptInformativeBranch b) :
    0 < forwardBesselQ (receiptSelectedObservedScore x) receiptHorizon := by
  let s : ℕ → ℝ := receiptSelectedObservedScore x
  let mean : ℝ := forwardPrefixMean s receiptHorizon
  have hOne : s 1 = 3 / 5 := receiptSelectedObservedScore_one hx
  have hTwo : s 2 = 2 / 5 := receiptSelectedObservedScore_two hx
  have hOneMem : 1 ∈ Finset.range receiptHorizon := by
    norm_num [receiptHorizon]
  have hTwoMem : 2 ∈ Finset.range receiptHorizon := by
    norm_num [receiptHorizon]
  have hOneLe : (s 1 - mean) ^ 2 ≤ forwardBesselQ s receiptHorizon := by
    unfold forwardBesselQ
    exact Finset.single_le_sum
      (fun k _hk ↦ sq_nonneg (s k - forwardPrefixMean s receiptHorizon))
      hOneMem
  have hTwoLe : (s 2 - mean) ^ 2 ≤ forwardBesselQ s receiptHorizon := by
    unfold forwardBesselQ
    exact Finset.single_le_sum
      (fun k _hk ↦ sq_nonneg (s k - forwardPrefixMean s receiptHorizon))
      hTwoMem
  have hQnonneg := forwardBesselQ_nonneg s receiptHorizon
  dsimp [mean] at hOneLe hTwoLe
  change 0 < forwardBesselQ s receiptHorizon
  rw [hOne] at hOneLe
  rw [hTwo] at hTwoLe
  nlinarith [sq_nonneg ((3 / 5 : ℝ) - forwardPrefixMean s receiptHorizon),
    sq_nonneg ((2 / 5 : ℝ) - forwardPrefixMean s receiptHorizon)]

theorem receiptSelectedSampleVariance_pos
    {b : Bool} {x : ℕ → Bool} (hx : x ∈ receiptInformativeBranch b) :
    0 < FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
      (fun i : Fin receiptHorizon ↦ receiptSelectedObservedScore x i) := by
  have hQ := receiptSelectedBesselQ_pos hx
  have heq := forwardBesselQ_eq_card_sub_one_mul_sampleVarianceBessel
    (x := receiptSelectedObservedScore x)
    (n := receiptHorizon) (by norm_num [receiptHorizon])
  rw [heq] at hQ
  have hfactor : (0 : ℝ) < receiptHorizon - 1 := by
    norm_num [receiptHorizon]
  nlinarith

/-! ## End-to-end informative receipts -/

/-- Each selector branch contains a path outside the same exceptional event.
On that theorem-produced path, the selected point posterior has positive KL,
the observed corrected score has positive Bessel variance, and the final
stationary-risk right-hand side is strictly below `7/8`.  The selected row-TV
error is the exact supplied error of the corresponding predeclared candidate. -/
theorem receiptInformative_goodPath_exists (b : Bool) :
    ∃ x : ℕ → Bool,
      x ∈ receiptInformativeBranch b ∧
      x ∉ receiptRiskBad ∧
      receiptSelectCandidate x receiptHorizon = b ∧
      receiptSelectDepth x receiptHorizon = 0 ∧
      receiptSelectRiskTilt x receiptHorizon = (if b then 12 else 11) ∧
      receiptSelectEta x = (if b then 1 / 32 else 1 / 64) ∧
      (∀ z : Bool, 0 < transitionVisitMass z receiptHorizon x) ∧
      klDiv (receiptSelectPosterior x receiptHorizon) receiptPrior =
        Real.log 2 ∧
      0 < klDiv (receiptSelectPosterior x receiptHorizon) receiptPrior ∧
      0 < FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
        (fun i : Fin receiptHorizon ↦ receiptSelectedObservedScore x i) ∧
      stationaryPosteriorMarkovRisk receiptFairKernel receiptFairStationary
          receiptScore (receiptSelectPosterior x receiptHorizon) = 1 / 2 ∧
      empiricalTransitionPosteriorRisk receiptScore
          (receiptSelectPosterior x receiptHorizon) receiptHorizon x ≤ 3 / 5 ∧
      receiptSelectedBoundary x < 11 / 40 ∧
      stationaryPosteriorMarkovRisk receiptFairKernel receiptFairStationary
          receiptScore (receiptSelectPosterior x receiptHorizon) <
        empiricalTransitionPosteriorRisk receiptScore
            (receiptSelectPosterior x receiptHorizon) receiptHorizon x +
          receiptSelectedBoundary x ∧
      empiricalTransitionPosteriorRisk receiptScore
            (receiptSelectPosterior x receiptHorizon) receiptHorizon x +
          receiptSelectedBoundary x < 7 / 8 := by
  obtain ⟨x, hxBranch, hxGood⟩ := receiptGoodPath_in_each_branch b
  have hcandidate : receiptSelectCandidate x receiptHorizon = b := by
    simpa [receiptSelectCandidate] using hxBranch.1
  have hdepth : receiptSelectDepth x receiptHorizon = 0 := rfl
  have hriskTilt :
      receiptSelectRiskTilt x receiptHorizon = (if b then 12 else 11) := by
    simp [receiptSelectRiskTilt, hxBranch.1]
  have heta : receiptSelectEta x = (if b then 1 / 32 else 1 / 64) := by
    simp [receiptSelectEta, hxBranch.1]
  have hvisit := receiptInformativeBranch_allRowsVisited hxBranch
    (show 3 ≤ receiptHorizon by norm_num [receiptHorizon])
  have hKL := receiptSelectedKL x receiptHorizon
  have hKLpos := receiptSelectedKL_pos x receiptHorizon
  have hvar := receiptSelectedSampleVariance_pos hxBranch
  have hstationary := receiptSelected_stationaryRisk x
  have hemp := receiptSelected_empiricalRisk_le x
  have hboundary := receiptSelectedBoundary_lt_eleven_fortieths x
  have hcertificate := receiptSelected_catalog_bound hxGood
  refine ⟨x, hxBranch, hxGood, hcandidate, hdepth, hriskTilt, heta,
    hvisit, hKL, hKLpos, hvar, hstationary, hemp, hboundary,
    hcertificate, ?_⟩
  linarith

/-- Both data-selected candidate branches contain a theorem-certified path.
The paths share one predeclared outer event but need not be the same path. -/
theorem receiptInformative_bothBranches_exist :
    (∃ x : ℕ → Bool,
      x ∈ receiptInformativeBranch false ∧ x ∉ receiptRiskBad ∧
      receiptSelectCandidate x receiptHorizon = false ∧
      0 < FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
        (fun i : Fin receiptHorizon ↦ receiptSelectedObservedScore x i) ∧
      0 < klDiv (receiptSelectPosterior x receiptHorizon) receiptPrior ∧
      empiricalTransitionPosteriorRisk receiptScore
            (receiptSelectPosterior x receiptHorizon) receiptHorizon x +
          receiptSelectedBoundary x < 7 / 8) ∧
    (∃ x : ℕ → Bool,
      x ∈ receiptInformativeBranch true ∧ x ∉ receiptRiskBad ∧
      receiptSelectCandidate x receiptHorizon = true ∧
      0 < FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
        (fun i : Fin receiptHorizon ↦ receiptSelectedObservedScore x i) ∧
      0 < klDiv (receiptSelectPosterior x receiptHorizon) receiptPrior ∧
      empiricalTransitionPosteriorRisk receiptScore
            (receiptSelectPosterior x receiptHorizon) receiptHorizon x +
          receiptSelectedBoundary x < 7 / 8) := by
  constructor
  · obtain ⟨x, hxBranch, hxGood, hcandidate, _hdepth, _htilt, _heta,
      _hvisit, _hKL, hKLpos, hvar, _hstationary, _hemp, _hboundary,
      _hcertificate, hrhs⟩ := receiptInformative_goodPath_exists false
    exact ⟨x, hxBranch, hxGood, hcandidate, hvar, hKLpos, hrhs⟩
  · obtain ⟨x, hxBranch, hxGood, hcandidate, _hdepth, _htilt, _heta,
      _hvisit, _hKL, hKLpos, hvar, _hstationary, _hemp, _hboundary,
      _hcertificate, hrhs⟩ := receiptInformative_goodPath_exists true
    exact ⟨x, hxBranch, hxGood, hcandidate, hvar, hKLpos, hrhs⟩

/-! ## Public receipt and axiom audit -/

#check empiricalStationaryCatalog_allPosteriors_of_not_mem
#check receiptHorizon
#check receiptFairKernel
#check receiptFairStationary
#check receiptCandidateZero
#check receiptCandidateOne
#check receiptCandidate
#check receiptReference
#check receiptScore
#check receiptD
#check receiptCandidateWeight
#check receiptPrior
#check receiptSelectCandidate
#check receiptSelectDepth
#check receiptSelectRiskTilt
#check receiptSelectPosterior
#check receiptFirstBranch
#check receiptInformativeBranch
#check receiptRiskBad
#check receiptSelectEta
#check receiptSelectedBoundary
#check receiptSelectedCorrectedScore
#check receiptSelectedObservedScore

#check receiptScore_mem_Icc
#check receiptCandidateWeight_isFullSupport
#check receiptPrior_isFullSupport
#check receiptSelectPosterior_isPMF
#check receiptFairStationary_invariant
#check receiptFair_dobrushin
#check receiptCandidateZero_dobrushin
#check receiptCandidateOne_dobrushin
#check receiptCandidate_coefficient_lt_one
#check receiptD_nonneg
#check receipt_markovRowRisk
#check receipt_stationaryMarkovRisk
#check receipt_centeredOscillation
#check receiptD_bounds
#check receiptCandidate_rowTV
#check receiptSelectedKL
#check receiptSelectedKL_pos
#check receiptInformativeBranch_measurable
#check receiptInformativeBranch_subset_firstBranch
#check receiptInformativeBranch_allRowsVisited
#check receiptInformativeBranch_mass
#check receiptInformativeBranch_real_mass
#check receiptRiskBad_mass_le
#check receiptGoodPath_in_each_branch
#check receiptSelectEta_nonneg
#check receiptSelectedRowTV
#check receiptSelected_stationaryRisk
#check receiptSelected_empiricalRisk_le
#check receiptSelected_catalog_bound
#check receiptSelectedBoundary_eq
#check receiptSelectedCorrectedScore_mem_Icc
#check receiptSelectedRate_log_le
#check receiptSelectedRate_lt_one_hundredth
#check receiptSelectedTrajectoryBoundary_lt_one_hundredth
#check receiptSelectedBoundary_lt_eleven_fortieths
#check receiptSelectedCorrectedScore_depthZero
#check receiptSelectedObservedScore_one
#check receiptSelectedObservedScore_two
#check receiptSelectedBesselQ_pos
#check receiptSelectedSampleVariance_pos
#check receiptInformative_goodPath_exists
#check receiptInformative_bothBranches_exist

#print axioms receiptScore_mem_Icc
#print axioms receiptCandidateWeight_isFullSupport
#print axioms receiptPrior_isFullSupport
#print axioms receiptSelectPosterior_isPMF
#print axioms receiptFairStationary_invariant
#print axioms receiptFair_dobrushin
#print axioms receiptCandidateZero_dobrushin
#print axioms receiptCandidateOne_dobrushin
#print axioms receiptCandidate_coefficient_lt_one
#print axioms receiptD_nonneg
#print axioms receipt_markovRowRisk
#print axioms receipt_stationaryMarkovRisk
#print axioms receipt_centeredOscillation
#print axioms receiptD_bounds
#print axioms receiptCandidate_rowTV
#print axioms receiptSelectedKL
#print axioms receiptSelectedKL_pos
#print axioms receiptInformativeBranch_measurable
#print axioms receiptInformativeBranch_subset_firstBranch
#print axioms receiptInformativeBranch_allRowsVisited
#print axioms receiptInformativeBranch_mass
#print axioms receiptInformativeBranch_real_mass
#print axioms receiptRiskBad_mass_le
#print axioms receiptGoodPath_in_each_branch
#print axioms receiptSelectEta_nonneg
#print axioms receiptSelectedRowTV
#print axioms receiptSelected_stationaryRisk
#print axioms receiptSelected_empiricalRisk_le
#print axioms receiptSelected_catalog_bound
#print axioms receiptSelectedBoundary_eq
#print axioms receiptSelectedCorrectedScore_mem_Icc
#print axioms receiptSelectedRate_log_le
#print axioms receiptSelectedRate_lt_one_hundredth
#print axioms receiptSelectedTrajectoryBoundary_lt_one_hundredth
#print axioms receiptSelectedBoundary_lt_eleven_fortieths
#print axioms receiptSelectedCorrectedScore_depthZero
#print axioms receiptSelectedObservedScore_one
#print axioms receiptSelectedObservedScore_two
#print axioms receiptSelectedBesselQ_pos
#print axioms receiptSelectedSampleVariance_pos
#print axioms receiptInformative_goodPath_exists
#print axioms receiptInformative_bothBranches_exist

end

end FormalSLT.Examples.CheckEmpiricalStationaryCatalogInformative
