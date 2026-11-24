import Tammes16.PairTable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open scoped RealInnerProductSpace

namespace Tammes16
noncomputable section

private lemma product_bounds : 1/10 < a*b ∧ a*b < 1/3 ∧ v*w < 63/100 := by
  have ha : 1/2 < a := (sq_lt_sq₀ (by norm_num : (0:ℝ) ≤ 1/2) a_pos.le).mp
    (by linarith only [a_sq, u0_spec.1])
  have ha' : a < 1 := (sq_lt_sq₀ a_pos.le zero_le_one).mp
    (by linarith only [a_sq, u0_spec.2.1])
  have hb : 1/5 < b := (sq_lt_sq₀ (by norm_num : (0:ℝ) ≤ 1/5) b_pos.le).mp
    (by linarith only [b_sq_bounds.1])
  have hb' : b < 1/3 := (sq_lt_sq₀ b_pos.le (by norm_num : (0:ℝ) ≤ 1/3)).mp
    (by linarith only [b_sq_bounds.2])
  have hv : v < 63/100 := (sq_lt_sq₀ v_pos.le (by norm_num : (0:ℝ) ≤ 63/100)).mp
    (by linarith only [v_sq, u0_spec.1])
  have hw : w < 1 := (sq_lt_sq₀ w_pos.le zero_le_one).mp
    (by linarith only [w_sq, b_sq_bounds.1])
  refine ⟨?_, ?_, ?_⟩
  · linarith only [mul_lt_mul_of_pos_right ha b_pos, hb]
  · linarith only [mul_lt_mul_of_pos_right ha' b_pos, hb']
  · linarith only [mul_lt_mul_of_pos_left hw v_pos, hv]

private lemma contact_value (r : Row) (h : r.isContact = true) : r.value = u0 := by
  cases r <;> simp [Row.isContact, Row.value] at h ⊢ <;>
    first | exact a_sq | exact mixed_contact | exact belt_contact

private lemma row_gap (r : Row) (ho : r ≠ .outerSelf) (hi : r ≠ .innerSelf)
    (hc : r.isContact = false) : r.value < 61/100 := by
  obtain ⟨hab, hab', hvw⟩ := product_bounds
  have hm := mul_pos (mul_pos c_pos v_pos) w_pos
  have hvw' := mul_pos v_pos w_pos
  have hbelt := mul_pos c_pos (pow_pos w_pos 2)
  have hpolar := mul_pos c_pos (pow_pos v_pos 2)
  have hpolar' := mul_pos (show 0 < 1-c by linarith only [c_bounds.2]) (pow_pos v_pos 2)
  cases r <;> simp [Row.isContact, Row.value] at ho hi hc ⊢ <;>
    linarith only [hab, hab', hvw, hm, hvw', hbelt, hpolar, hpolar',
      a_sq, v_sq, b_sq_bounds.1, b_sq_bounds.2, u0_spec.1, u0_spec.2.1]

/-- B5. A single rational cutoff strictly separates all 88 noncontacts. -/
theorem noncontact_lt (i j : I) (hne : i ≠ j) (h : (pairRow i j).isContact = false) :
    ⟪record i, record j⟫ < 61/100 := by
  rw [pair_dot]
  exact row_gap _ (distinct_rows i j hne).1 (distinct_rows i j hne).2 h

theorem contact_iff (i j : I) (hne : i ≠ j) :
    ⟪record i, record j⟫ = u0 ↔ (pairRow i j).isContact = true := by
  cases h : (pairRow i j).isContact with
  | false =>
    have hlt := (noncontact_lt i j hne h).trans u0_spec.1
    simp [hlt.ne]
  | true => simp [pair_dot, contact_value _ h]

theorem record_pair_le : PairLE record u0 := by
  intro i j hij
  cases h : (pairRow i j).isContact with
  | false => exact ((noncontact_lt i j hij h).trans u0_spec.1).le
  | true => exact ((contact_iff i j hij).2 h).le

theorem record_injective : Function.Injective record := by
  intro i j he
  by_contra hn
  have h := record_pair_le i j hn
  rw [he, record_self] at h
  linarith only [h, u0_spec.2.1]

theorem record_zero_one : ⟪record 0, record 1⟫ = u0 := by
  rw [pair_dot]
  exact a_sq

/-- B6. The peak is attained on an outer square side. -/
theorem record_attains : UnitConfig record ∧ HasPeak record u0 :=
  ⟨record_unit, record_pair_le, 0, 1, by norm_num, record_zero_one⟩

theorem lower_bound : ∃ x : Config, UnitConfig x ∧ PairLE x u0 :=
  ⟨record, record_attains.1, record_attains.2.1⟩

/-- The equality set of the witness is precisely the 32 unordered contact pairs. -/
theorem lower_bound_exact :
    ∃ x : Config, UnitConfig x ∧ Function.Injective x ∧ PairLE x u0 ∧
      contactPairs.card = 32 ∧
      ∀ i j : I, i < j → (⟪x i, x j⟫ = u0 ↔ (i,j) ∈ contactPairs) := by
  refine ⟨record, record_unit, record_injective, record_pair_le, pair_counts.1, ?_⟩
  intro i j hij
  simpa [contactPairs, hij] using contact_iff i j hij.ne

/-- Feasible angular separations of 16 distinct points on the unit sphere, in radians. -/
def feasibleAngles : Set ℝ := {d | ∃ x : Config, UnitConfig x ∧ Function.Injective x ∧
  ∀ i j, i ≠ j → d ≤ Real.arccos ⟪x i, x j⟫}

def d16 : ℝ := sSup feasibleAngles

theorem d16_lower_bound : Real.arccos u0 ≤ d16 := by
  apply le_csSup (s := feasibleAngles)
  · refine ⟨Real.pi, ?_⟩
    rintro d ⟨x, _, _, hx⟩
    exact (hx 0 1 (by norm_num)).trans (Real.arccos_le_pi _)
  · exact ⟨record, record_unit, record_injective,
      fun i j h => Real.arccos_le_arccos (record_pair_le i j h)⟩

end
end Tammes16
