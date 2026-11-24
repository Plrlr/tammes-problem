import Tammes16.Root
import Mathlib.Tactic.LinearCombination

namespace Tammes16
noncomputable section

def c : ℝ := Real.sqrt 2 / 2
def a : ℝ := Real.sqrt u0
def b : ℝ := Real.sqrt ((c - u0) / (1 + c))
def v : ℝ := Real.sqrt (1 - u0)
def w : ℝ := Real.sqrt (1 - b^2)

theorem c_sq : 2*c^2 = 1 := by
  unfold c
  nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem c_bounds : 70/100 < c ∧ c < 71/100 := by
  have hc : 0 ≤ c := by unfold c; positivity
  constructor
  · apply (sq_lt_sq₀ (by norm_num : (0:ℝ) ≤ 70/100) hc).mp
    linarith only [c_sq]
  · apply (sq_lt_sq₀ hc (by norm_num : (0:ℝ) ≤ 71/100)).mp
    linarith only [c_sq]

theorem u0_pos : 0 < u0 := by linarith only [u0_spec.1]
theorem c_pos : 0 < c := by linarith only [c_bounds.1]
theorem a_pos : 0 < a := Real.sqrt_pos.2 u0_pos

private theorem b_radicand_pos : 0 < (c - u0) / (1 + c) :=
  div_pos (by linarith only [u0_spec.2.1, c_bounds.1]) (by linarith only [c_pos])

theorem b_pos : 0 < b := Real.sqrt_pos.2 b_radicand_pos
theorem v_pos : 0 < v := Real.sqrt_pos.2 (by linarith only [u0_spec.2.1])
theorem a_sq : a^2 = u0 := Real.sq_sqrt u0_pos.le
theorem v_sq : v^2 = 1 - u0 := Real.sq_sqrt (by linarith only [u0_spec.2.1])

private theorem b_sq_div : b^2 = (c - u0) / (1 + c) :=
  Real.sq_sqrt b_radicand_pos.le

theorem b_sq_scaled : (1+c)*b^2 = c-u0 := by
  exact (mul_comm _ _).trans ((eq_div_iff (by linarith only [c_pos] : 1+c ≠ 0)).mp b_sq_div)

theorem b_sq_bounds : 1/25 < b^2 ∧ b^2 < 1/10 := by
  have hd : 0 < 1+c := by linarith only [c_pos]
  rw [b_sq_div, lt_div_iff₀ hd, div_lt_iff₀ hd]
  constructor <;> linarith only [c_bounds.1, c_bounds.2, u0_spec.1, u0_spec.2.1]

theorem w_pos : 0 < w := Real.sqrt_pos.2 (by linarith only [b_sq_bounds.2])
theorem w_sq : w^2 = 1-b^2 := Real.sq_sqrt (by linarith only [b_sq_bounds.2])

/-- B2. Positive roots and the five polynomial specifications of the coordinates. -/
theorem radical_specs :
    0 < c ∧ 0 < a ∧ 0 < b ∧ 0 < v ∧ 0 < w ∧
    2*c^2 = 1 ∧ a^2 = u0 ∧ (1+c)*b^2 = c-u0 ∧
    v^2 = 1-u0 ∧ w^2 = 1-b^2 :=
  ⟨c_pos, a_pos, b_pos, v_pos, w_pos, c_sq, a_sq, b_sq_scaled, v_sq, w_sq⟩

theorem belt_contact : c*w^2 - b^2 = u0 := by
  rw [w_sq]
  linarith only [b_sq_scaled]

-- These are A, B, U and the squared radical equation from Section 3.
private def X (u : ℝ) := 1-u^2
private def Y (u t : ℝ) := u*(t-2*u)
private def Z (u t : ℝ) := (2+t)*u^2
private def F (u t : ℝ) := (Z u t-X u-Y u t)^2 - 4*X u*Y u t
private def K (u : ℝ) := (5*u^2-1)^2 + 2*(u^2-u)^2 + 8*u^2*(1-u^2)
private def J (u : ℝ) := 2*(5*u^2-1)*(u^2-u) - 4*u*(1-u^2)

private lemma conjugate_form (u t : ℝ) (ht : t^2 = 2) :
    F u t = K u + t*J u := by
  unfold F Z X Y K J
  linear_combination (u^2-u)^2 * ht

private lemma eliminant (u t : ℝ) (ht : t^2 = 2) :
    F u t * F u (-t) = (7*u^2+2*u-1)*sextic u := by
  rw [conjugate_form u t ht, conjugate_form u (-t) (by nlinarith only [ht])]
  calc
    (K u + t*J u)*(K u + -t*J u) = (K u)^2 - 2*(J u)^2 := by
      linear_combination -(J u)^2 * ht
    _ = _ := by unfold K J sextic; ring

/-- B3. The conjugate has the wrong sign to vanish. Undo both squarings on
the positive branch to recover the unsquared mixed-layer contact. -/
theorem mixed_contact : c*v*w + a*b = u0 := by
  let t := 2*c
  let s := 2*(1+c)
  let p := c*v*w
  let q := a*b
  have ht : t^2 = 2 := by dsimp [t]; nlinarith only [c_sq]
  have ht0 : 0 < t := by dsimp [t]; linarith only [c_pos]
  have ht2 : t < 2 := by dsimp [t]; linarith only [c_bounds.2]
  have hs : 0 < s := by dsimp [s]; linarith only [c_pos]
  have hp : 0 < p := mul_pos (mul_pos c_pos v_pos) w_pos
  have hq : 0 < q := mul_pos a_pos b_pos
  have hx : 0 < X u0 := by
    unfold X
    nlinarith only [mul_pos (show 0 < 1-u0 by linarith only [u0_spec.2.1])
      (show 0 < 1+u0 by linarith only [u0_pos])]
  have hy : Y u0 (-t) < 0 := mul_neg_of_pos_of_neg u0_pos (by linarith only [ht0, u0_pos])
  have hneg : 0 < F u0 (-t) := by
    unfold F
    nlinarith only [sq_nonneg (Z u0 (-t)-X u0-Y u0 (-t)), mul_neg_of_pos_of_neg hx hy]
  have hprod := eliminant u0 t ht
  rw [u0_spec.2.2, mul_zero] at hprod
  have hzero := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hneg)
  have hsign : 0 ≤ Z u0 t-X u0-Y u0 t := by
    have hu : (3/5 : ℝ)^2 < u0^2 :=
      (sq_lt_sq₀ (by norm_num) u0_pos.le).mpr (by linarith only [u0_spec.1])
    unfold Z X Y
    nlinarith only [hu, ht2, mul_nonneg ht0.le (sq_nonneg (u0-1/2))]
  have hw : (1+c)*w^2 = 1+u0 := by rw [w_sq]; linarith only [b_sq_scaled]
  have hX : s*p^2 = X u0 := calc
    s*p^2 = (2*c^2)*v^2*((1+c)*w^2) := by dsimp [s, p]; ring
    _ = X u0 := by rw [c_sq, v_sq, hw]; unfold X; ring
  have hY : s*q^2 = Y u0 t := calc
    s*q^2 = 2*a^2*((1+c)*b^2) := by dsimp [s, q]; ring
    _ = Y u0 t := by rw [a_sq, b_sq_scaled]; unfold Y; dsimp [t]; ring
  have hZ : s*u0^2 = Z u0 t := by dsimp [Z, s, t]; ring
  unfold F at hzero
  rw [← hX, ← hY, ← hZ] at hzero hsign
  have he : (s*u0^2-s*p^2-s*q^2)^2 = (s*(2*p*q))^2 := by
    linear_combination hzero
  have he' := (sq_eq_sq₀ hsign (mul_nonneg hs.le (by positivity : 0 ≤ 2*p*q))).mp he
  have hsum : s * (p+q)^2 = s*u0^2 := by linear_combination -he'
  exact (sq_eq_sq₀ (add_pos hp hq).le u0_pos.le).mp (mul_left_cancel₀ hs.ne' hsum)

end
end Tammes16
