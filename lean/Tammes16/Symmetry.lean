import Tammes16.Configuration

open scoped RealInnerProductSpace

namespace Tammes16
noncomputable section

/-- Rotate by π/4 about the polar axis and reverse the height. -/
def rotoreflect (x : V) : V :=
  WithLp.toLp 2 ![c*(x 0-x 1), c*(x 0+x 1), -x 2]

/-- Reflect in the meridian plane through the first vertex. -/
def mirror (x : V) : V := WithLp.toLp 2 ![x 0, -x 1, x 2]

private lemma inner_xyz (x y : V) :
    ⟪x, y⟫ = y 0*x 0 + y 1*x 1 + y 2*x 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [star_trivial, dotProduct, Fin.sum_univ_three] <;> ring

theorem rotoreflect_inner (x y : V) : ⟪rotoreflect x, rotoreflect y⟫ = ⟪x, y⟫ := by
  rw [inner_xyz, inner_xyz]
  simp [rotoreflect] <;> linear_combination (y 0*x 0 + y 1*x 1) * c_sq

theorem mirror_inner (x y : V) : ⟪mirror x, mirror y⟫ = ⟪x, y⟫ := by
  rw [inner_xyz, inner_xyz]
  simp [mirror] <;> ring

def rotLabel : I → I := ![12,13,14,15, 9,10,11,8, 4,5,6,7, 1,2,3,0]
def mirrorLabel : I → I := ![0,3,2,1, 7,6,5,4, 8,11,10,9, 15,14,13,12]

private def flipLayer : Fin 4 → Fin 4 := ![3,2,1,0]

private lemma flip_coords (l : Fin 4) :
    rad (flipLayer l) = rad l ∧ ht (flipLayer l) = -ht l := by
  fin_cases l <;> simp [flipLayer, rad, ht]

private lemma step_coords (q : Fin 8) :
    cx (q+1) = c*(cx q - cy q) ∧ cy (q+1) = c*(cx q + cy q) := by
  fin_cases q <;> constructor <;> norm_num [cx, cy] <;> linarith only [c_sq]

private lemma mirror_coords (q : Fin 8) :
    cx (-q) = cx q ∧ cy (-q) = -cy q := by
  fin_cases q <;> constructor <;> norm_num [cx, cy]

theorem record_rotoreflect (i : I) : record (rotLabel i) = rotoreflect (record i) := by
  have indices : layer (rotLabel i) = flipLayer (layer i) ∧
      phase (rotLabel i) = phase i + 1 := by fin_cases i <;> exact ⟨rfl, rfl⟩
  obtain ⟨hr, hh⟩ := flip_coords (layer i)
  obtain ⟨hx, hy⟩ := step_coords (phase i)
  ext k
  fin_cases k <;> simp [rotoreflect, record, indices.1, indices.2, hr, hh, hx, hy] <;> ring

theorem record_mirror (i : I) : record (mirrorLabel i) = mirror (record i) := by
  have indices : layer (mirrorLabel i) = layer i ∧
      phase (mirrorLabel i) = -(phase i) := by fin_cases i <;> exact ⟨rfl, rfl⟩
  obtain ⟨hx, hy⟩ := mirror_coords (phase i)
  ext k
  fin_cases k <;> simp [mirror, record, indices.1, indices.2, hx, hy]

/-- The two generators satisfy the dihedral relations r⁸ = m² = (mr)² = 1. -/
theorem dihedral_relations (i : I) :
    rotLabel^[8] i = i ∧ mirrorLabel (mirrorLabel i) = i ∧
    mirrorLabel (rotLabel (mirrorLabel (rotLabel i))) = i := by
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

/-- Powers of the rotoreflection, optionally preceded by the meridian reflection. -/
def symmetryLabel (n : Fin 8) (reflected : Bool) (i : I) : I :=
  rotLabel^[n.val] (if reflected then mirrorLabel i else i)

/-- The images of the first two labels distinguish all sixteen normal forms. -/
theorem sixteen_distinct_symmetries :
    Function.Injective (fun g : Fin 8 × Bool =>
      (symmetryLabel g.1 g.2 0, symmetryLabel g.1 g.2 1)) := by
  decide

end
end Tammes16
