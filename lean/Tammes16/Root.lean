import Tammes16.Smoke
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Tammes16
noncomputable section

def IsRoot16 (u : ℝ) : Prop :=
  61/100 < u ∧ u < 62/100 ∧ sextic u = 0

-- In the shifted polynomial the nonconstant coefficients are positive.
private lemma shifted_increase (s t : ℝ) (hs : 0 ≤ s) (ht : 0 < t) :
    0 < sextic (3/5 + s + t) - sextic (3/5 + s) := by
  unfold sextic
  ring_nf
  positivity

private lemma sextic_increases {x y : ℝ} (hx : 61/100 < x) (hxy : x < y) :
    sextic x < sextic y := by
  have h := shifted_increase (x - 3/5) (y - x) (by linarith) (by linarith)
  rw [show 3/5 + (x - 3/5) = x by ring, show x + (y - x) = y by ring] at h
  linarith

/-- B1. The open rational interval isolates a unique root of the sextic. -/
theorem root_unique : ∃! u : ℝ, IsRoot16 u := by
  obtain ⟨hlo, hhi⟩ := sextic_endpoint_signs
  have hc : Continuous sextic := by unfold sextic; fun_prop
  obtain ⟨u, hu, hz⟩ := intermediate_value_Icc
    (show (61/100 : ℝ) ≤ 62/100 by norm_num) hc.continuousOn
    (show 0 ∈ Set.Icc (sextic (61/100)) (sextic (62/100)) from ⟨hlo.le, hhi.le⟩)
  have hl : 61/100 < u := lt_of_le_of_ne hu.1 (by
    intro h; rw [← h] at hz; linarith)
  have hr : u < 62/100 := lt_of_le_of_ne hu.2 (by
    intro h; rw [h] at hz; linarith)
  refine ⟨u, ⟨hl, hr, hz⟩, ?_⟩
  rintro y ⟨hyl, _, hy⟩
  rcases lt_trichotomy y u with h | h | h
  · linarith [sextic_increases hyl h]
  · exact h
  · linarith [sextic_increases hl h]

def u0 : ℝ := Classical.choose root_unique.exists
theorem u0_spec : IsRoot16 u0 := Classical.choose_spec root_unique.exists

end
end Tammes16
