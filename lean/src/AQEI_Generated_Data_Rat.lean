import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs

/- 
  AQEI_Generated_Data_Rat.lean
  Auto-generated from Phase 2 Optimization.
  Converted to exact Rationals for rigorous verification.
-/

namespace AQEIGeneratedRat

/-- Vertex coefficients 'a' as Rationals -/
def coefficients : List Rat := [
  (-201930050 : Rat) / 188548783,
  (100 : Rat) / 1,
  (100 : Rat) / 1,
  (-697114919 : Rat) / 954338471,
  (271445287 : Rat) / 543764461,
  (100 : Rat) / 1,
]

/-- The normal vectors L for the active constraints (Rational approximation) -/
def active_L : List (List Rat) := [
  [
    (18242171 : Rat) / 185310433,
    (0 : Rat) / 1,
    (0 : Rat) / 1,
    (1686499 : Rat) / 783101748,
    (0 : Rat) / 1,
    (0 : Rat) / 1,
  ],
  [
    (-61 : Rat) / 489973282,
    (0 : Rat) / 1,
    (-33857 : Rat) / 815586094,
    (-7864737 : Rat) / 141838453,
    (-110132019 : Rat) / 383795849,
    (0 : Rat) / 1,
  ],
  [
    (-29649869 : Rat) / 504524770,
    (0 : Rat) / 1,
    (0 : Rat) / 1,
    (-188681736 : Rat) / 836755073,
    (-178 : Rat) / 269582495,
    (-320317 : Rat) / 94761543,
  ],
]

/-- The bounds B for the active constraints (independently rationalized from float). -/
def active_B : List Rat := [
  (92851846 : Rat) / 867769073,
  (83642891 : Rat) / 782481412,
  (31371962 : Rat) / 284241483,
]

/-- Exact tight bounds: active_B_tight[i] = -(L_i · v*) in exact rational arithmetic.
    Satisfies L_i · v* + active_B_tight[i] = 0 exactly for the rationalized L and v*,
    enabling the non-tautological proof in FinalTheorems.candidate_active_binding.
    Agrees with active_B to within 7 × 10⁻¹¹ (dominated by NIntegrate precision). -/
def active_B_tight : List Rat := [
  (36286065376054059506337885986767 : Rat) / 339120078382890596879902371141156,
  (56881163208213718514020808481935025194233775134029935638377 : Rat) / 532124755520295182874251714890874438355108028311061855673287,
  (237683910384684634846040317252027915796047109138197689971 : Rat) / 2153503410892270359210740429201985008222235476670837870345,
]

end AQEIGeneratedRat

#print axioms AQEIGeneratedRat.coefficients
#print axioms AQEIGeneratedRat.active_L
#print axioms AQEIGeneratedRat.active_B
#print axioms AQEIGeneratedRat.active_B_tight
