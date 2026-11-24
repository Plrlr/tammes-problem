import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Smoke test for the toolchain: a small fact about the sextic of the lower bound.
It only checks that Lean and Mathlib work here; the real files follow notes/math/lean-16-blueprint.md. -/

namespace Tammes16

def sextic (x : ℝ) : ℝ :=
  23*x^6 + 6*x^5 + 5*x^4 + 4*x^3 - 3*x^2 - 2*x - 1

/-- The sextic changes sign on (61/100, 62/100), so it has a root there (step B1 of the blueprint). -/
theorem sextic_endpoint_signs : sextic (61/100) < 0 ∧ 0 < sextic (62/100) := by
  unfold sextic
  constructor <;> norm_num

end Tammes16
