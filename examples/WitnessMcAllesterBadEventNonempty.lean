import FormalSLT.PACBayesBoundedLoss

/-!
# Concrete non-vacuity witness for the finite McAllester bad-event theorem

Adversarial witness for
`finiteMcAllesterBoundedComplexity_badEventMass_le_delta`.

We exhibit a fully concrete finite setup that
1. satisfies every hypothesis of the theorem simultaneously, and
2. has a NON-EMPTY bad-event set (so the bounded sum is not vacuously `0`),
3. on which the conclusion `mass ≤ delta` is a genuine, satisfied constraint.

Setup:
* `ι = Unit` (one hypothesis), prior = point mass (full support, `1 > 0`);
* `Z = Bool`, `p = uniform` (`1/2, 1/2`);
* loss `ℓ * z = if z then 1 else 0`, so population risk `R = 1/2`;
* `n = 1`, sample `S = ![false]`, so empirical risk `Rhat_S = 0`;
* `complexityBound = 2/5`, `delta = 1`.

Then `R - Rhat_S = 1/2 > sqrt(C/(2n)) = sqrt(1/5) ≈ 0.447`, and the only
posterior `ρ` (the point mass) has `KL = 0`, `log(1/δ) = 0 ≤ C`.
So `S = ![false]` lies in the bad set: the set is inhabited.
-/

namespace FormalSLT.PACBayesBoundedLoss.Witness

open FormalSLT.PACBayesKL FormalSLT.PACBayesFiniteProductMGF

noncomputable section

local instance (q : Prop) : Decidable q := Classical.propDecidable q

-- Concrete data
def pW : Bool → ℝ := fun _ => (1 : ℝ) / 2
def priorW : Unit → ℝ := fun _ => (1 : ℝ)
def lossW : Unit → Bool → ℝ := fun _ z => if z then (1 : ℝ) else 0
def SW : Fin 1 → Bool := fun _ => false
def CW : ℝ := 2 / 5
def deltaW : ℝ := 1

-- Hypotheses
theorem pW_isPMF : IsPMF pW := by
  refine ⟨fun z => by simp [pW], ?_⟩
  simp [pW]

theorem priorW_isFullSupport : IsFullSupportPMF priorW := by
  refine ⟨⟨fun i => by simp [priorW], ?_⟩, fun i => by simp [priorW]⟩
  simp [priorW]

theorem lossW_bounded : ∀ i : Unit, ∀ z : Bool, 0 ≤ lossW i z ∧ lossW i z ≤ 1 := by
  intro i z
  cases z <;> simp [lossW]

theorem CW_pos : 0 < CW := by norm_num [CW]
theorem deltaW_pos : 0 < deltaW := by norm_num [deltaW]

/-- Population risk of the single hypothesis is `1/2`. -/
theorem popRisk_eq : finitePopulationRisk pW lossW () = 1 / 2 := by
  simp [finitePopulationRisk, pW, lossW]

/-- Empirical risk on `S = ![false]` is `0`. -/
theorem empRisk_eq : finiteEmpiricalRisk lossW () SW = 0 := by
  simp [finiteEmpiricalRisk, lossW, SW]

/-- `sqrt(C/(2n)) = sqrt(1/5) < 1/2`. -/
theorem sqrt_lt_half : Real.sqrt (CW / (2 * (1 : ℝ))) < 1 / 2 := by
  have h : CW / (2 * (1 : ℝ)) = 1 / 5 := by norm_num [CW]
  rw [h]
  have : Real.sqrt (1 / 5) < Real.sqrt (1 / 4) := by
    apply Real.sqrt_lt_sqrt <;> norm_num
  calc Real.sqrt (1 / 5) < Real.sqrt (1 / 4) := this
    _ = 1 / 2 := by
        rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The point-mass posterior. -/
def rhoW : Unit → ℝ := fun _ => 1

theorem rhoW_isPMF : IsPMF rhoW := by
  refine ⟨fun i => by simp [rhoW], ?_⟩
  simp [rhoW]

/-- `KL(ρ‖prior) = 0` for the point masses. -/
theorem kl_eq_zero : klDiv rhoW priorW = 0 := by
  simp [klDiv, rhoW, priorW]

/-- The complexity constraint holds: `KL + log(1/δ) = 0 ≤ C`. -/
theorem complexity_ok :
    klDiv rhoW priorW + Real.log (1 / deltaW) ≤ CW := by
  rw [kl_eq_zero]
  simp [deltaW]
  norm_num [CW]

/-- Posterior population risk equals `1/2`. -/
theorem postPopRisk_eq : posteriorPopulationRisk pW lossW rhoW = 1 / 2 := by
  unfold posteriorPopulationRisk posteriorAverage
  simp [rhoW, popRisk_eq]

/-- Posterior empirical risk equals `0`. -/
theorem postEmpRisk_eq : posteriorEmpiricalRisk lossW rhoW SW = 0 := by
  unfold posteriorEmpiricalRisk posteriorAverage
  simp [rhoW, empRisk_eq]

/-- The strict overfit condition holds for `ρ = rhoW` at sample `SW`. -/
theorem overfit_ok :
    posteriorPopulationRisk pW lossW rhoW >
      posteriorEmpiricalRisk lossW rhoW SW +
        Real.sqrt (CW / (2 * ((1 : ℕ) : ℝ))) := by
  rw [postPopRisk_eq, postEmpRisk_eq]
  have h := sqrt_lt_half
  push_cast
  linarith

/-- **The bad-event set is NON-EMPTY**: `SW` is a member. -/
theorem SW_mem_badSet :
    SW ∈ (Finset.univ.filter fun S : Fin 1 → Bool =>
      ∃ ρ : Unit → ℝ,
        IsPMF ρ ∧
          klDiv ρ priorW + Real.log (1 / deltaW) ≤ CW ∧
          posteriorPopulationRisk pW lossW ρ >
            posteriorEmpiricalRisk lossW ρ S +
              Real.sqrt (CW / (2 * ((1 : ℕ) : ℝ)))) := by
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, rhoW, rhoW_isPMF, complexity_ok, ?_⟩
  exact overfit_ok

theorem badSet_nonempty :
    (Finset.univ.filter fun S : Fin 1 → Bool =>
      ∃ ρ : Unit → ℝ,
        IsPMF ρ ∧
          klDiv ρ priorW + Real.log (1 / deltaW) ≤ CW ∧
          posteriorPopulationRisk pW lossW ρ >
            posteriorEmpiricalRisk lossW ρ S +
              Real.sqrt (CW / (2 * ((1 : ℕ) : ℝ)))).Nonempty :=
  ⟨SW, SW_mem_badSet⟩

/-- The theorem instantiated on the concrete numbers: bad-event mass `≤ delta`. -/
theorem instantiated_bound :
    (∑ S ∈ (Finset.univ.filter fun S : Fin 1 → Bool =>
        ∃ ρ : Unit → ℝ,
          IsPMF ρ ∧
            klDiv ρ priorW + Real.log (1 / deltaW) ≤ CW ∧
            posteriorPopulationRisk pW lossW ρ >
              posteriorEmpiricalRisk lossW ρ S +
                Real.sqrt (CW / (2 * ((1 : ℕ) : ℝ)))),
        finiteProductSampleWeight pW S) ≤ deltaW :=
  finiteMcAllesterBoundedComplexity_badEventMass_le_delta
    (n := 1) (Z := Bool) (ι := Unit) Nat.one_pos
    pW pW_isPMF priorW priorW_isFullSupport lossW
    CW_pos deltaW_pos lossW_bounded

/-- The mass of the inhabited bad set is exactly `1/2` (the weight of `SW`),
which is genuinely below `delta = 1`. So the bound is a real constraint, not
`0 ≤ delta`. -/
theorem badSet_mass_eq_half :
    (∑ S ∈ (Finset.univ.filter fun S : Fin 1 → Bool =>
        ∃ ρ : Unit → ℝ,
          IsPMF ρ ∧
            klDiv ρ priorW + Real.log (1 / deltaW) ≤ CW ∧
            posteriorPopulationRisk pW lossW ρ >
              posteriorEmpiricalRisk lossW ρ S +
                Real.sqrt (CW / (2 * ((1 : ℕ) : ℝ)))),
        finiteProductSampleWeight pW S) = 1 / 2 := by
  have hset :
      (Finset.univ.filter fun S : Fin 1 → Bool =>
        ∃ ρ : Unit → ℝ,
          IsPMF ρ ∧
            klDiv ρ priorW + Real.log (1 / deltaW) ≤ CW ∧
            posteriorPopulationRisk pW lossW ρ >
              posteriorEmpiricalRisk lossW ρ S +
                Real.sqrt (CW / (2 * ((1 : ℕ) : ℝ)))) = {SW} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨SW_mem_badSet, ?_⟩
    intro S _hS
    rw [Finset.mem_filter] at _hS
    obtain ⟨_, ρ, hρ, _, hover⟩ := _hS
    -- Membership forces S 0 = false (otherwise emp risk = 1 > population risk).
    have hb : S 0 = false := by
      by_contra hne
      have hbtrue : S 0 = true := by
        cases hb' : S 0 with
        | false => exact absurd hb' hne
        | true => rfl
      -- empirical risk on this S equals ρ() = 1, contradicting the overfit gap
      have hsum1 : ρ () = 1 := by
        have := hρ.sum_one; simpa using this
      have hemp : posteriorEmpiricalRisk lossW ρ S = 1 := by
        unfold posteriorEmpiricalRisk posteriorAverage finiteEmpiricalRisk
        have hl : lossW () (S 0) = 1 := by rw [hbtrue]; simp [lossW]
        simp [hl, hsum1]
      have hpop : posteriorPopulationRisk pW lossW ρ ≤ 1 := by
        unfold posteriorPopulationRisk posteriorAverage
        simp [popRisk_eq, hsum1]; norm_num
      rw [hemp] at hover
      have hsqrt_nonneg : 0 ≤ Real.sqrt (CW / (2 * ((1 : ℕ) : ℝ))) := Real.sqrt_nonneg _
      linarith
    funext k
    fin_cases k
    simpa [SW] using hb
  rw [hset, Finset.sum_singleton]
  simp [finiteProductSampleWeight, pW]

end

end FormalSLT.PACBayesBoundedLoss.Witness

#print axioms FormalSLT.PACBayesBoundedLoss.Witness.instantiated_bound
#print axioms FormalSLT.PACBayesBoundedLoss.Witness.badSet_nonempty
#print axioms FormalSLT.PACBayesBoundedLoss.Witness.badSet_mass_eq_half
#print axioms FormalSLT.PACBayesBoundedLoss.Witness.overfit_ok
