/-
# `TMIP* = RE`, and the Aldous–Lyons conjecture is false

This file states, on top of Mathlib alone, the two main results of

* L. Bowen, M. Chapman, T. Vidick, *The Aldous–Lyons Conjecture II: Undecidability*
  (arXiv:2501.00173, "paper II"), and
* L. Bowen, M. Chapman, A. Lubotzky, T. Vidick, *The Aldous–Lyons Conjecture I: Subgroup Tests*
  (arXiv:2408.00110, "paper I"),

each as a theorem left `sorry`:

1. `TailoredGames.tailored_halting_reduction` — paper II's main theorem: a computable map from
   Turing machines to *tailored* non-local games sending halting machines to games with a
   perfect Z-aligned permutation strategy commuting along edges, and the other machines to
   games of synchronous value at most `1/2`. In particular the synchronous value of tailored
   games is uncomputable.
2. `AldousLyons.aldousLyonsConjecture_false` — the Aldous–Lyons conjecture, for invariant random
   subgroups of free groups, is false.

The file has two parts, `TailoredGames` and `AldousLyons`, each with its own introduction.

The model of computation is Mathlib's `Nat.Partrec.Code`, "halts on the empty input" is
`(c.eval 0).Dom`, and "computable" is Mathlib's `Computable`. Paper II's reduction runs in
polynomial time; the statement asks only that it be computable.
-/

module
public import Mathlib.Computability.PartrecCode
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Instances.Discrete
-- The tactics the proofs inside the definitions use.
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! ## Part 1: tailored games and `TMIP* = RE`

Paper II's main theorem, `thm:tailored_MIP*=RE` (II:1505; line numbers `II:n` refer to the arXiv
LaTeX source): there is a computable map from Turing machines to *tailored* non-local games that
sends halting machines to games with a perfect *Z-aligned permutation strategy commuting along
edges* (ZPC) and non-halting machines to games of value at most `1/2`. The definitions:

* `SynchronousGame`, `SyncStrategy`, `strategyValue`, `gameValue`: two-player one-round
  synchronous games (both players draw from the same question and answer alphabets, and unequal
  answers to equal questions lose); synchronous strategies, which are finite-dimensional quantum
  strategies given by one projective measurement per question, with outcome probabilities
  `Tr(P^x_a P^y_b) / d`; and the synchronous value, the supremum of the winning probability over
  all of them. The soundness clause is stated in this value, which bounds every finite-dimensional
  strategy.
* `TailoredGameData` (paper: tailored games, II:1243): a first-order description of a game with
  vertices `Fin (nV + 1)`, at each vertex `x` a set `S_x` of `ℓ^R(x)` *readable* and `ℓ^L(x)`
  *linear* formal variables, edge weights, and *controlled linear constraints*: for an edge `xy`
  and a value `γ^R` of the readable variables, a list `L_xy(γ^R)` of vectors `c` over
  `S_x ⊔ S_y ⊔ {J}`.
* `TailoredGameData.toGame`: its interpretation as a `SynchronousGame`. The answers are bit
  vectors of the maximal length `Λ`; an answer at `x` must vanish beyond `ℓ(x) = ℓ^R(x) + ℓ^L(x)`,
  and the answer pair `(a, b)` at `xy` is accepted by the paper's *canonical decider*
  (II:1757–1787): every `c ∈ L_xy(a^R b^R)` satisfies `⟨c, a b 1⟩ = 0`, where `J` is the affine
  coordinate, set to `1`. The empty list accepts and the list `[J]` rejects.
* `PermStrategy`, `HasPerfectZPC` (paper: II:1043–1057, II:1279–1283): a strategy whose
  observables are signed permutation matrices — one per formal variable, involutions, commuting
  at each vertex — with diagonal observables for the readable variables (*Z-aligned*), commuting
  across every edge of positive weight (*commuting along edges*); its measurements are the
  Fourier transforms `P^x_a = ∏_i (1 + (-1)^{a_i} U(x, i)) / 2`, and it is *perfect* when its
  value is `1`.
* `HaltsOnEmptyInput`, `TailoredHaltingReduction`: the statement.

Two conventions differ from the paper's text and are equivalent to it:

* **Loops.** At a loop `xx` the paper's decision reads one answer, over `S_x`. Here, as in the
  paper's tailored normal form verifiers, whose canonical decider is always given two answers, it
  reads the pair `(a, a)` — unequal answers at a loop lose, which is what makes the game
  synchronous — so a constraint over `S_x ⊔ S_x ⊔ {J}` evaluated at `(a, a)`; a one-copy
  constraint `(c, c_J)` is the two-copy constraint `(c, 0, c_J)`, and a two-copy constraint
  `(c₁, c₂, c_J)` acts as the one-copy constraint `(c₁ + c₂, c_J)`.
* **One answer alphabet.** The paper's answers at `x` are `F₂^{S_x}`; here they are the bit
  vectors of length `Λ = max_x ℓ(x)` that vanish beyond `ℓ(x)`, and the generators beyond `ℓ(x)`
  of a permutation strategy act as the identity. A strategy for the paper's game and one for this
  game determine each other by padding with zeros and truncating, with the same value; a ZPC
  strategy and its padding by identities likewise.

Clause (3) of the paper's theorem reads `val*(G_M) < 1/2`; its proof (II:2046–2065) shows that
every finite-dimensional strategy has value `< 1/2`, which bounds the supremum by `1/2` only, and
paper I uses the theorem with `≤ 1/2` (I:2140). The statement below has `≤ 1/2`.
-/

namespace TailoredGames

/-! ### Synchronous games and the synchronous value -/

/-- A synchronous game: both players receive questions from the same alphabet and answer from the
same alphabet; on equal questions, unequal answers always lose. -/
structure SynchronousGame (X A : Type*) [Fintype X] [Fintype A] [DecidableEq A] where
  μ : X → X → ℝ
  μ_nonneg : ∀ x y, 0 ≤ μ x y
  μ_sum_one : ∑ x, ∑ y, μ x y = 1
  D : X → X → A → A → Bool
  synchronous : ∀ x a b, a ≠ b → D x x a b = false

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]

/-- A synchronous strategy for a synchronous game: a finite-dimensional quantum strategy with a
single question-indexed projective measurement family. The operators act on `ℂ^d` (`d > 0`); for
each question `x` the measurement operators `P x a` are self-adjoint idempotent matrices (so
orthogonal projections) summing to the identity. Measurements for different questions need not
commute. There is no state vector: outcome probabilities are computed with the normalized trace
`τ(M) = Tr(M)/d` (see `strategyValue`). -/
structure SyncStrategy (G : SynchronousGame X A) where
  d : ℕ
  d_pos : 0 < d
  P : X → A → Matrix (Fin d) (Fin d) ℂ
  selfAdjoint : ∀ x a, star (P x a) = P x a
  projective : ∀ x a, P x a * P x a = P x a
  normalized : ∀ x, ∑ a, P x a = 1

/-- The winning probability of a synchronous strategy: the players answer questions `(x, y)` with
`(a, b)` with probability `Tr(P^x_a P^y_b)/d`. This trace is a nonnegative real; the real part is
taken so that the definition typechecks with no proof obligation. -/
noncomputable def strategyValue (G : SynchronousGame X A) (S : SyncStrategy G) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    G.μ x y * (if G.D x y a b then 1 else 0) * ((S.P x a * S.P y b).trace.re / (S.d : ℝ))

/-- The synchronous value of a synchronous game: the supremum of the winning probability over all
synchronous strategies. -/
noncomputable def gameValue (G : SynchronousGame X A) : ℝ :=
  ⨆ S : SyncStrategy G, strategyValue G S

/-! ### Descriptions of tailored games -/

/-- A first-order description of a tailored game (II:1243). The vertices are `Fin (nV + 1)`;
vertex `x` has `lenR.getD x 0` readable and `lenL.getD x 0` linear formal variables; the question
distribution is given by a list `w` of unnormalized natural-number weights `(x, y, weight)`; and
the controlled linear constraints by the list `cons` of entries `(x, y, γ^R, c)`, read as
"`c ∈ L_xy(γ^R)`". Here `γ^R` is the readable part of the answer pair (the readable bits of the
answer at `x`, then those at `y`) and `c` is a vector over `S_x ⊔ S_y ⊔ {J}` (the coefficients on
the variables at `x`, readable then linear, then those at `y`, then the coefficient of `J`). -/
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

instance (c v : List Bool) : Decidable (Satisfies c v) := instDecidableAnd

/-- The canonical decider (II:1757–1787) at the question pair `(x, y)`: unequal answers at a loop
lose; both answers are well formatted; and every constraint `c ∈ L_xy(a^R b^R)` is satisfied by
`a b 1`, the two full answers followed by the coordinate `J = 1`. -/
def Accepts (x y : Fin (g.nV + 1)) (a b : Fin g.ansLen → Bool) : Prop :=
  (x = y → a = b) ∧ g.WellFormatted x a ∧ g.WellFormatted y b ∧
    ∀ e ∈ g.cons, e.1 = x.val → e.2.1 = y.val → e.2.2.1 = g.readable x a ++ g.readable y b →
      Satisfies e.2.2.2 (g.full x a ++ g.full y b ++ [true])

instance (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) : Decidable (g.WellFormatted x a) :=
  Nat.decidableForallFin _

instance (x y : Fin (g.nV + 1)) (a b : Fin g.ansLen → Bool) : Decidable (g.Accepts x y a b) :=
  instDecidableAnd

/-- The total weight the list `w` assigns to the question pair `(x, y)`. -/
def questionWeight (x y : ℕ) : ℕ :=
  ((g.w.filter fun t => decide (t.1 = x ∧ t.2.1 = y)).map fun t => t.2.2).sum

/-- The total weight the list `w` assigns to valid question pairs. -/
def totalWeight : ℕ :=
  ∑ x : Fin (g.nV + 1), ∑ y : Fin (g.nV + 1), g.questionWeight x.val y.val

/-- Interpret a `TailoredGameData` as a `SynchronousGame`: questions are vertices, answers are bit
vectors of length `Λ`, the distribution normalizes the weights (falling back to a point mass on
`(0, 0)` when the total weight is zero, so that the interpretation is total), and acceptance is
the canonical decider's. -/
noncomputable def toGame : SynchronousGame (Fin (g.nV + 1)) (Fin g.ansLen → Bool) where
  μ x y :=
    if g.totalWeight = 0 then (if x = 0 ∧ y = 0 then 1 else 0)
    else (g.questionWeight x.val y.val : ℝ) / (g.totalWeight : ℝ)
  -- The proofs inside this definition use `rw`/`exact` with named lemmas only (no `simp`,
  -- `norm_num` or `positivity`): the comparator requires them to elaborate to the same terms
  -- in this file's environment and in the Solution's, where the whole library is imported.
  μ_nonneg x y := by
    by_cases h : g.totalWeight = 0
    · rw [ite_eq_left h]
      by_cases hxy : x = 0 ∧ y = 0
      · rw [ite_eq_left hxy]
        exact zero_le_one
      · rw [ite_eq_right hxy]
    · rw [ite_eq_right h]
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  μ_sum_one := by
    by_cases h : g.totalWeight = 0
    · have hrw : ∀ x y : Fin (g.nV + 1),
          (if g.totalWeight = 0 then (if x = 0 ∧ y = 0 then (1 : ℝ) else 0)
            else (g.questionWeight x.val y.val : ℝ) / (g.totalWeight : ℝ)) =
          if x = 0 ∧ y = 0 then 1 else 0 := fun x y => ite_eq_left h
      rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hrw x y))]
      rw [Finset.sum_eq_single (0 : Fin (g.nV + 1))]
      · rw [Finset.sum_eq_single (0 : Fin (g.nV + 1))]
        · exact ite_eq_left ⟨rfl, rfl⟩
        · intro b _ hb
          exact ite_eq_right (fun hc => hb hc.2)
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
      · intro b _ hb
        exact Finset.sum_eq_zero (fun y _ => ite_eq_right (fun hc => hb hc.1))
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · have hT : (g.totalWeight : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
      have hrw : ∀ x y : Fin (g.nV + 1),
          (if g.totalWeight = 0 then (if x = 0 ∧ y = 0 then (1 : ℝ) else 0)
            else (g.questionWeight x.val y.val : ℝ) / (g.totalWeight : ℝ)) =
          (g.questionWeight x.val y.val : ℝ) / (g.totalWeight : ℝ) := fun x y => ite_eq_right h
      rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hrw x y))]
      have hin : ∀ x : Fin (g.nV + 1),
          (∑ y : Fin (g.nV + 1), (g.questionWeight x.val y.val : ℝ) / (g.totalWeight : ℝ)) =
            (∑ y : Fin (g.nV + 1), (g.questionWeight x.val y.val : ℝ)) / (g.totalWeight : ℝ) :=
        fun x => (Finset.sum_div _ _ _).symm
      have hsum : ∑ x : Fin (g.nV + 1), ∑ y : Fin (g.nV + 1),
          (g.questionWeight x.val y.val : ℝ) = (g.totalWeight : ℝ) := by
        change _ = ((∑ x : Fin (g.nV + 1), ∑ y : Fin (g.nV + 1),
          g.questionWeight x.val y.val : ℕ) : ℝ)
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl (fun x _ => (Nat.cast_sum _ _).symm)
      rw [Finset.sum_congr rfl (fun x _ => hin x), ← Finset.sum_div, hsum, div_self hT]
  D x y a b := decide (g.Accepts x y a b)
  synchronous x a b hne := decide_eq_false fun h => hne (h.1 rfl)

end TailoredGameData

/-! ### Z-aligned permutation strategies commuting along edges -/

/-- The signed permutation matrix `e_j ↦ (-1)^{s j} e_{σ j}` (II:1043–1053): the action of the
signed permutation `(σ, s)` of `Ω_± = {±} × Fin m` on the anti-symmetric functions, in their
standard basis. -/
def signedPermMatrix {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin m → Bool) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if σ j = i then (if s j then -1 else 1) else 0

variable (g : TailoredGameData)

/-- A permutation strategy for a tailored game (II:1056, II:1115): on `ℂ^m`, one observable
`U x i` for each variable `i` at each vertex `x`, a signed permutation matrix and an involution,
the observables at a vertex commuting; the variables beyond `ℓ(x)` act as the identity ("One
answer alphabet" above). It is *Z-aligned* when the observables of the readable variables are
diagonal and *commutes along edges* when the observables at the two ends of every edge of
positive weight commute (II:1279–1283). -/
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

/-- The value of a permutation strategy, defined as `strategyValue` defines the value of a
synchronous strategy: the players answer `(x, y)` with `(a, b)` with probability
`Tr(P^x_a P^y_b) / m`. -/
noncomputable def value : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    g.toGame.μ x y * (if g.toGame.D x y a b then 1 else 0) *
      ((S.proj x a * S.proj y b).trace.re / (S.m : ℝ))

end PermStrategy

/-- The game has a perfect Z-aligned permutation strategy commuting along edges (II:1279). -/
def TailoredGameData.HasPerfectZPC : Prop := ∃ S : PermStrategy g, S.value = 1

/-! ### The halting problem and `TMIP* = RE` -/

/-- The program `c` halts on the empty input. (`Nat.Partrec.Code` is Mathlib's Gödel numbering of
partial recursive functions, an equivalent model of computation to Turing machines; the empty
input is encoded by `0`.) -/
def HaltsOnEmptyInput (c : Nat.Partrec.Code) : Prop := (c.eval 0).Dom

/-- **`TMIP* = RE`**, Theorem `thm:tailored_MIP*=RE` of Bowen–Chapman–Vidick, paper II
(arXiv:2501.00173, II:1505), with "polynomial-time" relaxed to "computable" and `< 1/2` read as
`≤ 1/2` (see above): there is a computable map from Turing machines to tailored games such that

1. (completeness) if the machine halts on the empty input then the game has a perfect Z-aligned
   permutation strategy commuting along edges, and
2. (soundness) if it does not then the synchronous value of the game is at most `1/2`. -/
def TailoredHaltingReduction : Prop :=
  ∃ g : Nat.Partrec.Code → TailoredGameData, Computable g ∧
    ∀ c : Nat.Partrec.Code,
      (HaltsOnEmptyInput c → (g c).HasPerfectZPC) ∧
      (¬HaltsOnEmptyInput c → gameValue (g c).toGame ≤ 1 / 2)

/-- **Challenge 1: `TMIP* = RE`** (paper II, `thm:tailored_MIP*=RE`, in the form of
`TailoredHaltingReduction` above). -/
theorem tailored_halting_reduction : TailoredHaltingReduction := by
  sorry

end TailoredGames

/-! ## Part 2: the Aldous–Lyons conjecture

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
    refine ⟨?_, fun v u hv hu => ?_⟩
    · show H.1 (w⁻¹ * 1 * w) = true
      rw [mul_one, inv_mul_cancel]
      exact h1
    · have h := h2 _ _ hv hu
      show H.1 (w⁻¹ * (v * u⁻¹) * w) = true
      rwa [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc (w⁻¹ * v) w, mul_inv_cancel_left,
        mul_assoc w⁻¹ v (u⁻¹ * w), ← mul_assoc v u⁻¹ w, ← mul_assoc w⁻¹ (v * u⁻¹) w] at h⟩

/-- The **invariant random subgroups** of `F_s`: the Borel probability measures on `Sub(F_s)`
invariant under conjugation by every `w ∈ F_s`. -/
def IRS (s : ℕ) : Set (ProbabilityMeasure (SubgroupSpace s)) :=
  {μ | ∀ w : FreeGroup (Fin s), (μ : Measure (SubgroupSpace s)).map (conj w) = μ}

/-- The stabilizer `{w ∈ F_s | w · x = x}` of the point `x` under the action of `F_s` on
`Fin N` in which the `i`-th generator acts by the permutation `σ i`. -/
def stab {s N : ℕ} (σ : Fin s → Equiv.Perm (Fin N)) (x : Fin N) : SubgroupSpace s :=
  ⟨fun w => decide (FreeGroup.lift σ w x = x), by
    refine ⟨decide_eq_true (by rw [map_one, Equiv.Perm.one_apply]), fun v w hv hw => ?_⟩
    have hv' := of_decide_eq_true hv
    have hw' := of_decide_eq_true hw
    exact decide_eq_true (by
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq.mpr hw'.symm, hv'])⟩

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
