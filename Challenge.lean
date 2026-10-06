/-
# The Aldous–Lyons conjecture is false, and `TMIP* = RE`

This file states, on top of Mathlib alone, the two main results of

* L. Bowen, M. Chapman, T. Vidick, *The Aldous–Lyons Conjecture II: Undecidability*
  (arXiv:2501.00173, "paper II"), and
* L. Bowen, M. Chapman, A. Lubotzky, T. Vidick, *The Aldous–Lyons Conjecture I: Subgroup Tests*
  (arXiv:2408.00110, "paper I"),

each as a theorem left `sorry`:

1. `TailoredGameValue.tailored_halting_reduction` — paper II's main theorem: a computable map
   from Turing machines to *tailored* non-local games sending halting machines to games with a
   perfect Z-aligned permutation strategy commuting along edges, and the other machines to
   games of synchronous value at most `1/2`. In particular the synchronous value of tailored
   games is uncomputable.
2. `AldousLyons.aldousLyonsConjecture_false` — the Aldous–Lyons conjecture, for invariant random
   subgroups of free groups, is false.

The file has three parts.

* `HaltingGameValue`: synchronous games, synchronous strategies and the synchronous value
  `gameValue`, first-order game descriptions `GameData`, and `HaltsOnEmptyInput`. This is the
  statement file `MIPRE/HaltingGameValue.lean` of MIPRE-formalization without its final
  definition (the statement of "MIP* = RE", not used here); it is also the challenge of
  `vidick/mipre-comparator`.
* `TailoredGameValue`: tailored games, ZPC strategies and the statement
  `TailoredHaltingReduction`. This is `MIPRE/TailoredGameValue.lean`, verbatim, with Challenge 1
  appended.
* `AldousLyons`: the space of subgroups of a free group, invariant random subgroups, the
  finitely described ones, and the conjecture; then Challenge 2.

The model of computation is Mathlib's `Nat.Partrec.Code`, "halts on the empty input" is
`(c.eval 0).Dom`, and "computable" is Mathlib's `Computable`. The papers' reductions run in
polynomial time; the statement asks only that they be computable.
-/

module
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Computability.PartrecCode
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Instances.Discrete
-- The tactics the proofs inside the definitions use (MIPRE-formalization's `MIPRE/Tactics.lean`).
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.Measurability
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Peel

@[expose] public section

namespace HaltingGameValue

/- The Loewner order on matrices (`0 ≤ A ↔ A.PosSemidef`) is scoped. -/
open scoped MatrixOrder

/-! ## POVMs -/

/-- A POVM is a (finite) collection of PSD matrices on the same Hilbert space
that sum to the identity. Here `X` indexes the matrices, and `d` is the space
dimension.

This is the QuantumLib (Lean-QuantumInfo) definition of `POVM`, with
`selfAdjoint (Matrix d d ℂ)` spelled out for its definitionally equal
`HermitianMat d ℂ`; `0 ≤ mats x` is the Loewner order, i.e. positive
semidefiniteness. -/
structure POVM (X : Type*) (d : Type*) [Fintype X] [Fintype d] [DecidableEq d] where
  mats : X → selfAdjoint (Matrix d d ℂ)
  nonneg : ∀ x, 0 ≤ mats x
  normalized : ∑ x, mats x = 1

/-! ## Synchronous games -/

/-- A synchronous game: both players receive questions from the same alphabet
and answer from the same alphabet; on equal questions, unequal answers always
lose. -/
structure SynchronousGame (X A : Type*) [Fintype X] [Fintype A] [DecidableEq A] where
  μ : X → X → ℝ
  μ_nonneg : ∀ x y, 0 ≤ μ x y
  μ_sum_one : ∑ x, ∑ y, μ x y = 1
  D : X → X → A → A → Bool
  synchronous : ∀ x a b, a ≠ b → D x x a b = false

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]

/-! ## Synchronous strategies -/

/-- A synchronous strategy for a synchronous game: a finite-dimensional
strategy with a single question-indexed projective measurement family. The
operators act on `ℂ^d` (`d > 0`); each measurement operator is idempotent,
hence (being positive semidefinite) an orthogonal projection. Measurements for
different questions need not commute. There is no state vector: outcome
probabilities are computed with the dimension-normalized trace
`τ(M) = Tr(M)/d` (see `strategyValue`). -/
structure SyncStrategy (G : SynchronousGame X A) where
  d : ℕ
  d_pos : 0 < d
  povm : X → POVM A (Fin d)
  projective : ∀ x a,
    ((povm x).mats a).val * ((povm x).mats a).val = ((povm x).mats a).val

/-! ## Game value -/

/-- The winning probability of a synchronous strategy: the players answer
questions `(x, y)` with `(a, b)` with probability `Tr(M^x_a M^y_b)/d`.
For positive semidefinite matrices this trace is a nonnegative real; we
take the real part so that the definition typechecks with no proof
obligations. -/
noncomputable def strategyValue (G : SynchronousGame X A) (S : SyncStrategy G) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    G.μ x y * (if G.D x y a b then 1 else 0) *
      ((((S.povm x).mats a).val * ((S.povm y).mats b).val).trace.re / (S.d : ℝ))

/-- The synchronous value of a synchronous game: the supremum of winning
probabilities over all synchronous strategies. -/
noncomputable def gameValue (G : SynchronousGame X A) : ℝ :=
  ⨆ S : SyncStrategy G, strategyValue G S

/-! ## Codable game descriptions -/

/-- A first-order description of a synchronous game, suitable for computability
statements. The question alphabet is `Fin (nX + 1)` and the answer alphabet is
`Fin (nA + 1)`. The question
distribution is given by a finite list `w` of unnormalized natural-number
weights `(x, y, weight)`, and the decision predicate by the list `acc` of
accepted tuples `(x, y, a, b)`. -/
structure GameData where
  nX : ℕ
  nA : ℕ
  w : List (ℕ × ℕ × ℕ)
  acc : List (ℕ × ℕ × ℕ × ℕ)

namespace GameData

/-- `GameData` is just a tuple of naturals and lists. -/
def equivTuple : GameData ≃ ℕ × ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ × ℕ) where
  toFun g := (g.nX, g.nA, g.w, g.acc)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩

instance : Primcodable GameData := Primcodable.ofEquiv _ equivTuple

/-- Total weight assigned by the list `w` to the question pair `(x, y)`. -/
def questionWeight (g : GameData) (x y : ℕ) : ℕ :=
  ((g.w.filter fun t => decide (t.1 = x ∧ t.2.1 = y)).map fun t => t.2.2).sum

/-- Total weight assigned by the list `w` to valid question pairs. -/
def totalWeight (g : GameData) : ℕ :=
  ∑ x : Fin (g.nX + 1), ∑ y : Fin (g.nX + 1), g.questionWeight x.val y.val

/-- Interpret a `GameData` as a `SynchronousGame`: normalize the question
weights (falling back to a point mass on `(0, 0)` when the total weight is
zero, so that the interpretation is total), and accept exactly the answer
tuples listed in `acc`, except that unequal answers on equal questions always
lose. -/
noncomputable def toGame (g : GameData) :
    SynchronousGame (Fin (g.nX + 1)) (Fin (g.nA + 1)) where
  μ x y :=
    if g.totalWeight = 0 then (if x = 0 ∧ y = 0 then 1 else 0)
    else (g.questionWeight x.val y.val : ℝ) / (g.totalWeight : ℝ)
  μ_nonneg x y := by
    split_ifs
    · norm_num
    · norm_num
    · positivity
  μ_sum_one := by
    by_cases h : g.totalWeight = 0
    · simp only [if_pos h]
      rw [Finset.sum_eq_single (0 : Fin (g.nX + 1))]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · simp only [if_neg h]
      have hT : (g.totalWeight : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
      have hsum : ∑ x : Fin (g.nX + 1), ∑ y : Fin (g.nX + 1),
          (g.questionWeight x.val y.val : ℝ) = (g.totalWeight : ℝ) := by
        unfold totalWeight
        push_cast
        rfl
      simp_rw [← Finset.sum_div]
      rw [hsum, div_self hT]
  D x y a b := if x = y ∧ a ≠ b then false else decide ((x.val, y.val, a.val, b.val) ∈ g.acc)
  synchronous x a b hne := by
    simp [hne]

end GameData

/-! ## The halting problem -/

/-- The program `c` halts on the empty input. (`Nat.Partrec.Code` is
Mathlib's Gödel numbering of partial recursive functions, an equivalent
model of computation to Turing machines; the empty input is encoded by
`0`.) -/
def HaltsOnEmptyInput (c : Nat.Partrec.Code) : Prop := (c.eval 0).Dom

end HaltingGameValue

namespace TailoredGameValue

open HaltingGameValue

/-! ## Descriptions of tailored games -/

/-- A first-order description of a tailored game (II:1243). The vertices are `Fin (nV + 1)`;
vertex `x` has `lenR.getD x 0` readable and `lenL.getD x 0` linear formal variables; the
question distribution is given, as in `HaltingGameValue.GameData`, by a list `w` of
unnormalized weights `(x, y, weight)`; and the controlled linear constraints by the list
`cons` of entries `(x, y, γ^R, c)`, read as "`c ∈ L_xy(γ^R)`". Here `γ^R` is the readable part
of the answer pair (the readable bits of the answer at `x`, then those at `y`) and `c` is a
vector over `S_x ⊔ S_y ⊔ {J}` (the coefficients on the variables at `x`, readable then linear,
then those at `y`, then the coefficient of `J`). -/
structure TailoredGameData where
  nV : ℕ
  lenR : List ℕ
  lenL : List ℕ
  w : List (ℕ × ℕ × ℕ)
  cons : List (ℕ × ℕ × List Bool × List Bool)

namespace TailoredGameData

/-- `TailoredGameData` is a tuple of naturals and lists. -/
def equivTuple : TailoredGameData ≃
    ℕ × List ℕ × List ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × List Bool × List Bool) where
  toFun g := (g.nV, g.lenR, g.lenL, g.w, g.cons)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩

instance : Primcodable TailoredGameData := Primcodable.ofEquiv _ equivTuple

variable (g : TailoredGameData)

/-- The number `ℓ^R(x)` of readable variables at `x`. -/
def lenRAt (x : ℕ) : ℕ := g.lenR.getD x 0

/-- The number `ℓ^L(x)` of linear variables at `x`. -/
def lenLAt (x : ℕ) : ℕ := g.lenL.getD x 0

/-- The number `ℓ(x) = ℓ^R(x) + ℓ^L(x)` of variables at `x`. -/
def lenAt (x : ℕ) : ℕ := g.lenRAt x + g.lenLAt x

/-- The answer length `Λ = max_x ℓ(x)`. -/
def ansLen : ℕ := Finset.univ.sup fun x : Fin (g.nV + 1) => g.lenAt x.val

/-- Bit `i` of a bit vector, `false` beyond its length. -/
def bit {n : ℕ} (a : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then a ⟨i, h⟩ else false

/-- An answer at `x` is well formatted when it vanishes beyond `ℓ(x)`. -/
def WellFormatted (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) : Prop :=
  ∀ i : Fin g.ansLen, g.lenAt x.val ≤ i.val → a i = false

/-- The readable part `a^R` of an answer at `x`: its first `ℓ^R(x)` bits. -/
def readable (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) : List Bool :=
  (List.range (g.lenRAt x.val)).map (bit a)

/-- The full answer at `x`: its first `ℓ(x)` bits, readable then linear. -/
def full (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) : List Bool :=
  (List.range (g.lenAt x.val)).map (bit a)

/-- A vector `v` satisfies the linear constraint `c` when they have the same length and
`⟨c, v⟩ = 0` over `F₂`. A constraint of the wrong length is never satisfied, as the paper's
canonical decider rejects malformed constraints. -/
def Satisfies (c v : List Bool) : Prop :=
  c.length = v.length ∧ Even ((List.zipWith (· && ·) c v).count true)

instance (c v : List Bool) : Decidable (Satisfies c v) := by
  unfold Satisfies; infer_instance

/-- The canonical decider (II:1757–1787) at the question pair `(x, y)`: unequal answers at a
loop lose; both answers are well formatted; and every constraint `c ∈ L_xy(a^R b^R)` is
satisfied by `a b 1`, the two full answers followed by the coordinate `J = 1`. -/
def Accepts (x y : Fin (g.nV + 1)) (a b : Fin g.ansLen → Bool) : Prop :=
  (x = y → a = b) ∧ g.WellFormatted x a ∧ g.WellFormatted y b ∧
    ∀ e ∈ g.cons, e.1 = x.val → e.2.1 = y.val → e.2.2.1 = g.readable x a ++ g.readable y b →
      Satisfies e.2.2.2 (g.full x a ++ g.full y b ++ [true])

instance (x y : Fin (g.nV + 1)) (a b : Fin g.ansLen → Bool) : Decidable (g.Accepts x y a b) := by
  unfold Accepts WellFormatted; infer_instance

/-- The question distribution: the weights `w` normalized as in `HaltingGameValue.GameData`. -/
noncomputable def weights : GameData := ⟨g.nV, 0, g.w, []⟩

/-- Interpret a `TailoredGameData` as a `SynchronousGame`: questions are vertices, answers are
bit vectors of length `Λ`, the distribution is that of the weights, and acceptance is the
canonical decider's. -/
noncomputable def toGame : SynchronousGame (Fin (g.nV + 1)) (Fin g.ansLen → Bool) where
  μ := g.weights.toGame.μ
  μ_nonneg := g.weights.toGame.μ_nonneg
  μ_sum_one := g.weights.toGame.μ_sum_one
  D x y a b := decide (g.Accepts x y a b)
  synchronous x a b hne := by
    simp [Accepts, hne]

end TailoredGameData

/-! ## Z-aligned permutation strategies commuting along edges -/

/-- The signed permutation matrix `e_j ↦ (-1)^{s j} e_{σ j}` (II:1043–1053): the action of the
signed permutation `(σ, s)` of `Ω_± = {±} × Fin m` on the anti-symmetric functions, in their
standard basis. -/
def signedPermMatrix {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin m → Bool) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if σ j = i then (if s j then -1 else 1) else 0

variable (g : TailoredGameData)

/-- A permutation strategy for a tailored game (II:1056, II:1115): on `ℂ^m`, one observable
`U x i` for each variable `i` at each vertex `x`, a signed permutation matrix and an
involution, the observables at a vertex commuting; the variables beyond `ℓ(x)` act as the
identity (§ "One answer alphabet" of the module docstring). It is *Z-aligned* when the
observables of the readable variables are diagonal and *commutes along edges* when the
observables at the two ends of every edge of positive weight commute (II:1279–1283). -/
structure PermStrategy where
  /-- The dimension. -/
  m : ℕ
  m_pos : 0 < m
  /-- The observables. -/
  U : Fin (g.nV + 1) → Fin g.ansLen → Matrix (Fin m) (Fin m) ℂ
  signedPerm : ∀ x i, ∃ σ s, U x i = signedPermMatrix σ s
  invol : ∀ x i, U x i * U x i = 1
  comm : ∀ x i j, U x i * U x j = U x j * U x i
  pad : ∀ x (i : Fin g.ansLen), g.lenAt x.val ≤ i.val → U x i = 1
  zAligned : ∀ x (i : Fin g.ansLen), i.val < g.lenRAt x.val → (U x i).IsDiag
  commEdges : ∀ x y, 0 < g.toGame.μ x y → ∀ i j, U x i * U y j = U y j * U x i

namespace PermStrategy

variable {g} (S : PermStrategy g)

/-- The measurement at `x`, the Fourier transform of the observables (II:974):
`P^x_a = ∏_i (1 + (-1)^{a_i} U(x, i)) / 2`. -/
noncomputable def proj (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) :
    Matrix (Fin S.m) (Fin S.m) ℂ :=
  ((List.finRange g.ansLen).map fun i =>
    (1 / 2 : ℂ) • (1 + (if a i then (-1 : ℂ) else 1) • S.U x i)).prod

/-- The value of a permutation strategy, defined as `HaltingGameValue.strategyValue` defines
the value of a synchronous strategy: the players answer `(x, y)` with `(a, b)` with probability
`Tr(P^x_a P^y_b) / m`. -/
noncomputable def value : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    g.toGame.μ x y * (if g.toGame.D x y a b then 1 else 0) *
      ((S.proj x a * S.proj y b).trace.re / (S.m : ℝ))

end PermStrategy

/-- The game has a perfect Z-aligned permutation strategy commuting along edges (II:1279). -/
def TailoredGameData.HasPerfectZPC : Prop := ∃ S : PermStrategy g, S.value = 1

/-! ## The halting problem and `TMIP* = RE` -/

/-- **`TMIP* = RE`**, Theorem `thm:tailored_MIP*=RE` of Bowen–Chapman–Vidick, paper II
(arXiv:2501.00173, II:1505), with "polynomial-time" relaxed to "computable" and `< 1/2` read as
`≤ 1/2` (module docstring): there is a computable map from Turing machines to tailored games
such that

1. (completeness) if the machine halts on the empty input then the game has a perfect
   Z-aligned permutation strategy commuting along edges, and
2. (soundness) if it does not then the synchronous value of the game is at most `1/2`.

This is the statement; nothing in this file proves it. -/
def TailoredHaltingReduction : Prop :=
  ∃ g : Nat.Partrec.Code → TailoredGameData, Computable g ∧
    ∀ c : Nat.Partrec.Code,
      (HaltsOnEmptyInput c → (g c).HasPerfectZPC) ∧
      (¬HaltsOnEmptyInput c → gameValue (g c).toGame ≤ 1 / 2)

/-- **Challenge 1: `TMIP* = RE`** (paper II, `thm:tailored_MIP*=RE`, in the form of
`TailoredHaltingReduction` above). -/
theorem tailored_halting_reduction : TailoredHaltingReduction := by
  sorry

end TailoredGameValue

/-! ## The Aldous–Lyons conjecture

The Aldous–Lyons conjecture (D. Aldous and R. Lyons, *Processes on unimodular random
networks*, 2007), in the form for invariant random subgroups of free groups stated in paper I,
says: for every `s`, every invariant random subgroup of the free group on `s` generators is a
weak-* limit of finitely described ones. The definitions, in order:

* `SubgroupSpace s`, the space `Sub(F_s)` of subgroups of the free group `F_s`, each subgroup
  `H` identified with its indicator function `F_s → Bool`. Its topology is the subspace topology
  of the product topology on `{0,1}^{F_s}`; it carries the Borel σ-algebra.
* `conj w`, conjugation `H ↦ w H w⁻¹` on `Sub(F_s)`.
* `IRS s`, the invariant random subgroups: Borel probability measures on `Sub(F_s)` invariant
  under every conjugation.
* `stab σ x`, the stabilizer of a point `x` under an action of `F_s` on `{0, …, N-1}`, given by
  one permutation `σ i` per generator.
* `finDescIRS s`, the finitely described IRSs: the law of the stabilizer of a uniformly random
  point under such an action.
* `AldousLyonsConjecture`: for every `s`, `IRS s` is contained in the closure of
  `finDescIRS s`, in the topology of weak convergence of probability measures (Mathlib's
  topology on `ProbabilityMeasure`).
-/

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

/-- **Challenge 2: the Aldous–Lyons conjecture is false.** -/
theorem aldousLyonsConjecture_false : ¬ AldousLyonsConjecture := by
  sorry

end AldousLyons

end
