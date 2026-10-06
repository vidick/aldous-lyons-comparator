/-
# Solution

The proofs live in the [MIPRE-formalization](https://github.com/vidick/MIPRE-formalization)
library, at the commit pinned in `lakefile.toml`.

* **Challenge 1.** `TailoredGameValue.tailored_halting_reduction` is proved in the library under
  that name, in `MIPRE/TailoredMIP.lean`. The `HaltingGameValue` and `TailoredGameValue` parts of
  `Challenge.lean` are the library's own Mathlib-only statement files, so their definitions are
  declared in the library under the same names, and nothing is restated here.
* **Challenge 2.** The library states the conjecture in `MIPRE/SubgroupTestValue.lean`, as
  `SubgroupTestValue.AldousLyons`, and refutes it in `SubgroupTestValue.aldous_lyons_false`.
  `Challenge.lean` states it in its own namespace `AldousLyons`, with a finite action written as
  `N` and `σ` rather than as the library's structure `FiniteAction`. So the `AldousLyons`
  definitions are repeated here verbatim, and the theorem is transported: the two sets of
  finitely described IRSs are equal (`finDescIRS_eq`), and every other definition is the
  library's, unfolded.
-/

module
public import MIPRE.TailoredMIP

@[expose] public section

namespace AldousLyons

open MeasureTheory

/-- The space `Sub(F_s)` of subgroups of the free group `F_s = FreeGroup (Fin s)` on `s`
generators, each subgroup `H` given by its indicator function `A`: `A w = true` iff `w ∈ H`. -/
def SubgroupSpace (s : ℕ) : Type :=
  {A : FreeGroup (Fin s) → Bool //
    A 1 = true ∧ ∀ v w, A v = true → A w = true → A (v * w⁻¹) = true}

/-- The topology of `Sub(F_s)`: the subspace topology of the product topology on
`F_s → Bool`, with `Bool` discrete. -/
instance (s : ℕ) : TopologicalSpace (SubgroupSpace s) := instTopologicalSpaceSubtype

/-- The Borel σ-algebra on `Sub(F_s)`. -/
instance (s : ℕ) : MeasurableSpace (SubgroupSpace s) := borel _

instance (s : ℕ) : BorelSpace (SubgroupSpace s) := ⟨rfl⟩

/-- Conjugation by `w`: `H ↦ w H w⁻¹`, that is, `v ∈ w H w⁻¹ ↔ w⁻¹ v w ∈ H`. -/
def conj {s : ℕ} (w : FreeGroup (Fin s)) (H : SubgroupSpace s) : SubgroupSpace s :=
  ⟨fun v => H.1 (w⁻¹ * v * w), by
    obtain ⟨h1, h2⟩ := H.2
    refine ⟨by simpa using h1, fun v u hv hu => ?_⟩
    simpa [mul_assoc] using h2 _ _ hv hu⟩

/-- The **invariant random subgroups** of `F_s`: the Borel probability measures on `Sub(F_s)`
invariant under conjugation by every `w ∈ F_s`. -/
def IRS (s : ℕ) : Set (ProbabilityMeasure (SubgroupSpace s)) :=
  {μ | ∀ w : FreeGroup (Fin s), (μ : Measure (SubgroupSpace s)).map (conj w) = μ}

/-- The stabilizer `{w ∈ F_s | w · x = x}` of the point `x` under the action of `F_s` on
`Fin N` in which the `i`-th generator acts by the permutation `σ i`. -/
def stab {s N : ℕ} (σ : Fin s → Equiv.Perm (Fin N)) (x : Fin N) : SubgroupSpace s :=
  ⟨fun w => decide (FreeGroup.lift σ w x = x), by
    refine ⟨by simp, fun v w hv hw => ?_⟩
    simp only [decide_eq_true_eq] at hv hw ⊢
    rw [map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq.mpr hw.symm, hv]⟩

/-- The **finitely described** invariant random subgroups of `F_s`: for some `N ≥ 1` and some
action of `F_s` on `Fin N`, the law of the stabilizer of a uniformly random point,
`(1/N) ∑ₓ δ_{stab σ x}`. -/
def finDescIRS (s : ℕ) : Set (ProbabilityMeasure (SubgroupSpace s)) :=
  {μ | ∃ (N : ℕ) (_ : 1 ≤ N) (σ : Fin s → Equiv.Perm (Fin N)),
    (μ : Measure (SubgroupSpace s)) = (N : ENNReal)⁻¹ • ∑ x : Fin N, Measure.dirac (stab σ x)}

/-- **The Aldous–Lyons conjecture**, for free groups: for every `s`, every invariant random
subgroup of `F_s` is a limit, in the weak topology on probability measures, of finitely
described ones. -/
def AldousLyonsConjecture : Prop :=
  ∀ s : ℕ, IRS s ⊆ closure (finDescIRS s)

/-- The library's finitely described IRSs are the Challenge's. -/
theorem finDescIRS_eq (s : ℕ) :
    (SubgroupTestValue.finDescIRS s : Set (ProbabilityMeasure (SubgroupSpace s))) =
      finDescIRS s := by
  ext μ
  constructor
  · rintro ⟨σ, h⟩; exact ⟨σ.N, σ.N_pos, σ.σ, h⟩
  · rintro ⟨N, hN, σ, h⟩; exact ⟨⟨N, hN, σ⟩, h⟩

/-- **Challenge 2**, from `SubgroupTestValue.aldous_lyons_false`. -/
theorem aldousLyonsConjecture_false : ¬ AldousLyonsConjecture := fun h =>
  SubgroupTestValue.aldous_lyons_false fun s => by
    have := h s
    rw [← finDescIRS_eq] at this
    exact this

end AldousLyons

end
