import FormalSLT.OnlineToPAC.CesaBianchi

/-!
# Deterministic online-gradient certificate

This file is a reproducible empirical certificate over `T = 1000` rounds on a
finite parameter grid. It is not a probability proof and does not replace the
online-to-PAC theorem.
-/

namespace FormalSLT.Examples.OnlineGradientDescentCertificate

def rounds : Nat := 1000

def gradient (t : Nat) : Int :=
  if t % 2 = 0 then 1 else -1

def clipToGrid (w : Int) : Int :=
  max (-10) (min 10 w)

def ogdParam : Nat → Int
  | 0 => 0
  | t + 1 => clipToGrid (ogdParam t - gradient t)

def boundedLinearLoss (w g : Int) : Int :=
  10 + w * g

def sumRounds (f : Nat → Int) : Int :=
  (List.range rounds).foldl (fun acc t => acc + f t) 0

def ogdCumulativeLoss : Int :=
  sumRounds fun t => boundedLinearLoss (ogdParam t) (gradient t)

def grid : List Int :=
  (List.range 21).map fun i => Int.ofNat i - 10

def comparatorCumulativeLoss (w : Int) : Int :=
  sumRounds fun t => boundedLinearLoss w (gradient t)

def bestComparatorLoss : Int :=
  match grid with
  | [] => 0
  | w :: ws => ws.foldl (fun acc v => min acc (comparatorCumulativeLoss v))
      (comparatorCumulativeLoss w)

def empiricalRegret : Int :=
  ogdCumulativeLoss - bestComparatorLoss

def formalRegretBound : Int := 1000

def pacBoundNumerator : Int := 1500

/-- Exact integer certificate for the finite-grid OGD smoke workload. -/
theorem onlineGradientDescent_regret_certificate :
    empiricalRegret ≤ formalRegretBound := by
  native_decide

/-- Exact integer certificate for the composed PAC-side numerical bound. -/
theorem onlineGradientDescent_pac_certificate :
    empiricalRegret + 500 ≤ pacBoundNumerator := by
  native_decide

#eval ogdCumulativeLoss
#eval bestComparatorLoss
#eval empiricalRegret
#eval pacBoundNumerator

#check @FormalSLT.OnlineToPAC.cesaBianchiConconiGentile2004_boundedLoss_iid_highProbability

end FormalSLT.Examples.OnlineGradientDescentCertificate
