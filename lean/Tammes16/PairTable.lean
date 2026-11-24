import Tammes16.Configuration

open scoped RealInnerProductSpace

namespace Tammes16
noncomputable section

/-- Absolute longitude differences of 0, 45, 90, 135 and 180 degrees. -/
inductive Turn | aligned | near | quarter | far | opposite
  deriving DecidableEq

def turn (p q : Fin 8) : Turn :=
  match (8 + q.val - p.val) % 8 with
  | 0 => .aligned
  | 1 | 7 => .near
  | 2 | 6 => .quarter
  | 3 | 5 => .far
  | _ => .opposite

def Turn.factor : Turn → ℝ
  | .aligned => 1
  | .near => c
  | .quarter => 0
  | .far => -c
  | .opposite => -1

set_option maxHeartbeats 600000 in
private theorem horizontal_dot (p q : Fin 8) :
    cx p*cx q + cy p*cy q = (turn p q).factor := by
  fin_cases p <;> fin_cases q <;>
    norm_num [cx, cy, turn, Turn.factor] <;> linarith only [c_sq]

/-- Layer families AA/DD, BB/CC, AB/CD, BC, AC/BD and AD, respectively. -/
inductive Family | outer | inner | lateral | belt | skippedLayer | polar
  deriving DecidableEq

def family : Fin 4 → Fin 4 → Family :=
  ![![.outer, .lateral, .skippedLayer, .polar], ![.lateral, .inner, .belt, .skippedLayer],
    ![.skippedLayer, .belt, .inner, .lateral], ![.polar, .skippedLayer, .lateral, .outer]]

def Family.radial : Family → ℝ
  | .outer | .polar => v^2
  | .inner | .belt => w^2
  | .lateral | .skippedLayer => v*w

def Family.vertical : Family → ℝ
  | .outer => a^2
  | .inner => b^2
  | .lateral => a*b
  | .belt => -b^2
  | .skippedLayer => -(a*b)
  | .polar => -a^2

private theorem layer_products (l m : Fin 4) :
    rad l*rad m = (family l m).radial ∧ ht l*ht m = (family l m).vertical := by
  fin_cases l <;> fin_cases m <;> constructor <;>
    norm_num [rad, ht, family, Family.radial, Family.vertical] <;> ring

/-- The thirteen rows of the mutual-distance table, followed by the two self rows. -/
inductive Row
  | outerSide | outerDiagonal | innerSide | innerDiagonal
  | lateralNear | lateralFar | beltNear | beltFar
  | skipAligned | skipQuarter | skipOpposite | polarNear | polarFar
  | outerSelf | innerSelf
  deriving DecidableEq

def Row.signature : Row → Family × Turn
  | .outerSide => (.outer, .quarter)
  | .outerDiagonal => (.outer, .opposite)
  | .innerSide => (.inner, .quarter)
  | .innerDiagonal => (.inner, .opposite)
  | .lateralNear => (.lateral, .near)
  | .lateralFar => (.lateral, .far)
  | .beltNear => (.belt, .near)
  | .beltFar => (.belt, .far)
  | .skipAligned => (.skippedLayer, .aligned)
  | .skipQuarter => (.skippedLayer, .quarter)
  | .skipOpposite => (.skippedLayer, .opposite)
  | .polarNear => (.polar, .near)
  | .polarFar => (.polar, .far)
  | .outerSelf => (.outer, .aligned)
  | .innerSelf => (.inner, .aligned)

def Row.value : Row → ℝ
  | .outerSide => a^2
  | .outerDiagonal => 2*a^2-1
  | .innerSide => b^2
  | .innerDiagonal => 2*b^2-1
  | .lateralNear => c*v*w+a*b
  | .lateralFar => -(c*v*w)+a*b
  | .beltNear => c*w^2-b^2
  | .beltFar => -(c*w^2)-b^2
  | .skipAligned => v*w-a*b
  | .skipQuarter => -(a*b)
  | .skipOpposite => -(v*w)-a*b
  | .polarNear => c*v^2-a^2
  | .polarFar => -(c*v^2)-a^2
  | .outerSelf | .innerSelf => 1

private lemma row_value (r : Row) :
    r.signature.1.radial * r.signature.2.factor + r.signature.1.vertical = r.value := by
  cases r <;> simp [Row.signature, Row.value, Family.radial, Family.vertical, Turn.factor] <;>
    linarith only [a_sq, v_sq, w_sq]

def pairRow (i j : I) : Row :=
  match family (layer i) (layer j), turn (phase i) (phase j) with
  | .outer, .aligned => .outerSelf
  | .outer, .quarter => .outerSide
  | .outer, _ => .outerDiagonal
  | .inner, .aligned => .innerSelf
  | .inner, .quarter => .innerSide
  | .inner, _ => .innerDiagonal
  | .lateral, .near => .lateralNear
  | .lateral, _ => .lateralFar
  | .belt, .near => .beltNear
  | .belt, _ => .beltFar
  | .skippedLayer, .aligned => .skipAligned
  | .skippedLayer, .quarter => .skipQuarter
  | .skippedLayer, _ => .skipOpposite
  | .polar, .near => .polarNear
  | .polar, _ => .polarFar

-- Check the complete finite domain, including the diagonals and reversed labels.
-- In particular no wildcard in the decoder can assign an incorrect signature.
private theorem pair_signature : ∀ i j : I,
    (pairRow i j).signature = (family (layer i) (layer j), turn (phase i) (phase j)) := by
  decide

theorem distinct_rows : ∀ i j : I, i ≠ j →
    pairRow i j ≠ .outerSelf ∧ pairRow i j ≠ .innerSelf := by decide

/-- The exact entry of the inner-product table for any ordered pair of labels. -/
theorem pair_dot (i j : I) : ⟪record i, record j⟫ = (pairRow i j).value := by
  obtain ⟨hr, hh⟩ := layer_products (layer i) (layer j)
  rw [record_dot, horizontal_dot, hr, hh, ← row_value, pair_signature]

def Row.isContact : Row → Bool
  | .outerSide | .lateralNear | .beltNear => true
  | _ => false

/-- An edge is stored with its smaller label first. The mask uses only integers. -/
def contactPairs : Finset (I × I) :=
  Finset.univ.filter fun e => e.1 < e.2 ∧ (pairRow e.1 e.2).isContact = true

def noncontactPairs : Finset (I × I) :=
  Finset.univ.filter fun e => e.1 < e.2 ∧ (pairRow e.1 e.2).isContact = false

set_option maxRecDepth 4096 in
theorem pair_counts : contactPairs.card = 32 ∧ noncontactPairs.card = 88 := by decide

end
end Tammes16
