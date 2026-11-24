import Tammes16.LowerBound
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The value of `d₁₆`

`d16_eq_of_hypotheses` proves `d₁₆ = ψ* = arccos u₀` from the lower bound proved in
`Tammes16.LowerBound` and five named hypotheses, collected in the structure `Hypotheses`.
Each hypothesis is a result of the paper that is not formalized here:

* `fejesToth`: the area bound of Fejes Tóth (paper, Section 2, equation (2)), rounded up to `dHi` (54.8549°).
* `reduction`: if `d₁₆ > ψ*`, an optimal configuration exists whose contact graph, after removing a
  set of rattlers, is a pattern of the class `InClass` (paper, Sections 4 and 5, Proposition 5.4 and Lemma 5.3: 3-connected, degrees
  3 to 5, faces of 3 to 6 sides, 13 to 16 vertices, no triangle with three corners of degree 3).
* `enumeration`: every pattern of the class is isomorphic to a member of the list `L` (plantri with
  the degree filter; statement (D2) of the paper, Section 8).
* `search`: every realization of a listed pattern with separation in `[ψ*, dHi]` lies within the
  local radius of the record (the certificate trees of the search, replayed; statement (D3) of the paper, Sections 7 and 8).
* `localOpt`: the local theorem (paper, Section 6, Theorem 6.1; its finite checks are in Appendix C):
  every configuration whose squared chord distances to a copy of the record sum to at most `16 r²`,
  `r = 0.036039915`, has a pair at angle at most `ψ*`. Both leaf tests of the search (every chord at
  most `r`, or the squared sum at most `16 r²`) give this neighbourhood.

The contact graph, the realization of a pattern and the neighbourhood of the record are defined
concretely below; the pattern class `InClass` and the list `L` are parameters. Lean checks that these
statements together with the formal lower bound give the exact value; it does not check the
hypotheses themselves.
-/

open scoped RealInnerProductSpace

namespace Tammes16
noncomputable section

/-- The record separation `ψ* = arccos u₀`, in radians (about 52.2443957527°). -/
def psiStar : ℝ := Real.arccos u0

/-- The upper end of the search range, 54.8549° in radians, rounded up from Fejes Tóth's 54.854881°. -/
def dHi : ℝ := 957398615852237622 / 10 ^ 18

/-- The chord radius of the local theorem. -/
def localRadius : ℝ := 36039915 / 10 ^ 9

/-- Every pair of distinct points is at angle at least `d`. -/
def Separated (x : Config) (d : ℝ) : Prop := ∀ i j, i ≠ j → d ≤ Real.arccos ⟪x i, x j⟫

/-- The contact graph at separation `d`: distinct points at angle exactly `d`. -/
def contactGraph (x : Config) (d : ℝ) : SimpleGraph I where
  Adj i j := i ≠ j ∧ Real.arccos ⟪x i, x j⟫ = d
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [real_inner_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A contact pattern: a graph on `n` vertices. -/
structure Pattern where
  n : ℕ
  G : SimpleGraph (Fin n)

/-- `x` realizes `p` at separation `d`: after removing a set `R` of points (the rattlers), the
contact graph of `x` at `d` is isomorphic to `p`. -/
def Realizes (p : Pattern) (x : Config) (d : ℝ) : Prop :=
  ∃ R : Set I, Nonempty ((contactGraph x d).induce Rᶜ ≃g p.G)

/-- One copy of the record, given by one orthogonal map `O` and one relabelling `σ` for all sixteen
points, with squared chord errors summing to at most `16 r²`: the squared-sum form of the local
theorem. The max test (every chord at most `r`) implies it, by `nearRecord_of_max`. -/
def NearRecord (x : Config) : Prop :=
  ∃ (O : V ≃ₗᵢ[ℝ] V) (σ : Equiv.Perm I),
    ∑ i, ‖x i - O (record (σ i))‖ ^ 2 ≤ 16 * localRadius ^ 2

/-- The max test implies the squared-sum test. -/
theorem nearRecord_of_max {x : Config} (O : V ≃ₗᵢ[ℝ] V) (σ : Equiv.Perm I)
    (h : ∀ i, ‖x i - O (record (σ i))‖ ≤ localRadius) : NearRecord x := by
  refine ⟨O, σ, ?_⟩
  calc ∑ i, ‖x i - O (record (σ i))‖ ^ 2 ≤ ∑ _i : I, localRadius ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
    _ = 16 * localRadius ^ 2 := by simp

/-- The results of the paper that enter the formal proof as hypotheses. -/
structure Hypotheses where
  /-- The class of contact patterns of the reduction. -/
  InClass : Pattern → Prop
  /-- The enumerated list of patterns. -/
  L : Set Pattern
  fejesToth : ∀ d ∈ feasibleAngles, d ≤ dHi
  reduction : psiStar < d16 → ∃ x : Config, UnitConfig x ∧ Function.Injective x ∧
    Separated x d16 ∧ ∃ p, InClass p ∧ Realizes p x d16
  enumeration : ∀ p, InClass p → ∃ q ∈ L, Nonempty (p.G ≃g q.G)
  search : ∀ q ∈ L, ∀ (x : Config) (d : ℝ), UnitConfig x → Function.Injective x →
    Separated x d → psiStar ≤ d → d ≤ dHi → Realizes q x d → NearRecord x
  localOpt : ∀ x : Config, UnitConfig x → NearRecord x → ∃ i j, i ≠ j ∧ u0 ≤ ⟪x i, x j⟫

/-- Realization is invariant under isomorphism of patterns. -/
theorem Realizes.of_iso {p q : Pattern} {x : Config} {d : ℝ} (h : Realizes p x d)
    (e : p.G ≃g q.G) : Realizes q x d := by
  obtain ⟨R, ⟨f⟩⟩ := h
  exact ⟨R, ⟨f.trans e⟩⟩

/-- The record lies in its own neighbourhood. -/
theorem record_near : NearRecord record :=
  ⟨LinearIsometryEquiv.refl ℝ V, Equiv.refl I, by norm_num [localRadius]⟩

/-- The record is separated by `ψ*`. -/
theorem record_separated : Separated record psiStar :=
  fun i j h => Real.arccos_le_arccos (record_pair_le i j h)

theorem psiStar_feasible : psiStar ∈ feasibleAngles :=
  ⟨record, record_unit, record_injective, record_separated⟩

theorem d16_le_dHi (H : Hypotheses) : d16 ≤ dHi :=
  csSup_le ⟨psiStar, psiStar_feasible⟩ H.fejesToth

/-- The upper bound: no configuration beats the record. -/
theorem d16_le_psiStar (H : Hypotheses) : d16 ≤ psiStar := by
  rcases le_or_gt d16 psiStar with h | hlt
  · exact h
  exfalso
  obtain ⟨x, hu, hinj, hsep, p, hp, hr⟩ := H.reduction hlt
  obtain ⟨q, hq, ⟨e⟩⟩ := H.enumeration p hp
  have hnear := H.search q hq x d16 hu hinj hsep hlt.le (d16_le_dHi H) (hr.of_iso e)
  obtain ⟨i, j, hij, hge⟩ := H.localOpt x hu hnear
  have h1 := hsep i j hij
  have h2 : Real.arccos ⟪x i, x j⟫ ≤ psiStar := Real.arccos_le_arccos hge
  linarith

/-- **Main theorem.** Under the stated hypotheses, `d₁₆ = arccos u₀`, where `u₀` is the root in
`(0.61, 0.62)` of `23u⁶ + 6u⁵ + 5u⁴ + 4u³ − 3u² − 2u − 1`; the value is attained by the record. -/
theorem d16_eq_of_hypotheses (H : Hypotheses) :
    d16 = psiStar ∧ ∃ x : Config, UnitConfig x ∧ Function.Injective x ∧ Separated x d16 :=
  have hd : d16 = psiStar := le_antisymm (d16_le_psiStar H) d16_lower_bound
  ⟨hd, record, record_unit, record_injective, hd ▸ record_separated⟩

end
end Tammes16
