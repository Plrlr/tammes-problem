import Tammes16.Radicals
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases

open scoped RealInnerProductSpace

namespace Tammes16
noncomputable section

abbrev V := EuclideanSpace ℝ (Fin 3)
abbrev I := Fin 16
abbrev Config := I → V

def layer (i : I) : Fin 4 := ⟨i.val / 4, by have := i.isLt; omega⟩
def phase (i : I) : Fin 8 :=
  ⟨(2*(i.val % 4) + (layer i).val % 2) % 8, Nat.mod_lt _ (by norm_num)⟩

def cx : Fin 8 → ℝ := ![1, c, 0, -c, -1, -c, 0, c]
def cy : Fin 8 → ℝ := ![0, c, 1, c, 0, -c, -1, -c]
def ht : Fin 4 → ℝ := ![a, b, -b, -a]
def rad : Fin 4 → ℝ := ![v, w, w, v]

def record (i : I) : V :=
  WithLp.toLp 2 ![rad (layer i)*cx (phase i), rad (layer i)*cy (phase i), ht (layer i)]

def UnitConfig (x : Config) : Prop := ∀ i, ‖x i‖ = 1
def PairLE (x : Config) (u : ℝ) : Prop := ∀ i j, i ≠ j → ⟪x i, x j⟫ ≤ u
def HasPeak (x : Config) (u : ℝ) : Prop :=
  PairLE x u ∧ ∃ i j, i ≠ j ∧ ⟪x i, x j⟫ = u

/-- B4. Factor the Euclidean inner product into horizontal and vertical terms. -/
theorem record_dot (i j : I) :
    ⟪record i, record j⟫ = rad (layer i)*rad (layer j)*
      (cx (phase i)*cx (phase j) + cy (phase i)*cy (phase j)) + ht (layer i)*ht (layer j) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [record, star_trivial, dotProduct, Fin.sum_univ_three] <;> ring

theorem phase_unit (q : Fin 8) : cx q * cx q + cy q * cy q = 1 := by
  fin_cases q <;> norm_num [cx, cy] <;> linarith only [c_sq]

theorem layer_unit (l : Fin 4) : rad l * rad l + ht l * ht l = 1 := by
  fin_cases l <;> norm_num [rad, ht] <;> linarith only [a_sq, v_sq, w_sq]

theorem record_self (i : I) : ⟪record i, record i⟫ = 1 := by
  rw [record_dot, phase_unit, mul_one, layer_unit]

theorem record_unit : UnitConfig record := by
  intro i
  apply (sq_eq_sq₀ (norm_nonneg (record i)) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [← real_inner_self_eq_norm_sq, record_self, one_pow]

end
end Tammes16
