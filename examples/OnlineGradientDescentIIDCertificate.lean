import FormalSLT.OnlineToPAC.IIDConcentration

/-!
# Deterministic online-gradient iid certificate

This mirrors the q055 OGD certificate while using the iid-derived conversion
surface instead of the deviation-gate theorem.
-/

namespace FormalSLT.Examples.OnlineGradientDescentIIDCertificate

def rounds : Nat := 1000

def lossBoundMilli : Int := 10000

def iidDeviationMilli : Int := 500

def empiricalRegretMilli : Int := 1000

def pacBoundNumerator : Int := 1500

/-- Exact integer certificate for the iid-derived PAC-side numerical bound. -/
theorem onlineGradientDescent_iid_pac_certificate :
    empiricalRegretMilli + iidDeviationMilli ≤ pacBoundNumerator := by
  norm_num [empiricalRegretMilli, iidDeviationMilli, pacBoundNumerator]

#eval rounds
#eval lossBoundMilli
#eval iidDeviationMilli
#eval pacBoundNumerator

#check @FormalSLT.OnlineToPAC.regretConversion_iid
#check @FormalSLT.OnlineToPAC.cesaBianchi_iid

end FormalSLT.Examples.OnlineGradientDescentIIDCertificate
