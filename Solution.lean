/-
# Solution

The proofs live in the [MIPRE-formalization](https://github.com/vidick/MIPRE-formalization)
library, at the commit pinned in `lakefile.toml`, as `TailoredGameValue.tailored_halting_reduction`
and `SubgroupTestValue.aldous_lyons_false` (`MIPRE/TailoredMIP.lean`). The library states them in
its own Mathlib-only statement files, `MIPRE/TailoredGameValue.lean` (with
`MIPRE/HaltingGameValue.lean`) and `MIPRE/SubgroupTestValue.lean`, whose definitions differ from
`Challenge.lean`'s in packaging only:

* the library's synchronous strategies carry their measurement operators as a POVM of
  self-adjoint matrices, with positivity as a field; the Challenge's carry plain matrices and ask
  for self-adjointness, idempotence and normalization (positivity follows);
* the library's tailored game description reads its question weights through the first-order
  game descriptions `HaltingGameValue.GameData`; the Challenge normalizes the weights directly;
* the library packages a finite action of a free group as a structure `FiniteAction`; the
  Challenge writes it as `N` and `σ`.

So every definition of `Challenge.lean` is repeated here verbatim, and the two theorems are
transported. The transport is structural: the two synchronous values agree
(`gameValue_eq_syncValue`), a library game description and its Challenge reading have the same
game and the same permutation strategies (`toGame_toMIPRE`, `PermStrategy.of`), and the two sets of
finitely described IRSs are equal (`finDescIRS_eq`).
-/

module
public import MIPRE.TailoredMIP
public import MIPRE.Tailored.Data.Bridge

@[expose] public section

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

/-! ### Transport from the library -/

/-- The same game, as a `MIPRE.SynchronousGame`. -/
noncomputable def SynchronousGame.toMIPRE (G : SynchronousGame X A) : MIPRE.SynchronousGame X A where
  μ := G.μ
  μ_nonneg := G.μ_nonneg
  μ_sum_one := G.μ_sum_one
  D := G.D
  synchronous := G.synchronous

variable {G : SynchronousGame X A}

/-- A synchronous strategy, as one of the library: the same dimension and operators. -/
noncomputable def SyncStrategy.toMIPRE (S : SyncStrategy G) : MIPRE.SyncStrategy G.toMIPRE :=
  ⟨S.d, S.d_pos, ⟨S.P, S.selfAdjoint, S.projective, S.normalized⟩⟩

/-- A synchronous strategy of the library, as one of the Challenge. -/
noncomputable def SyncStrategy.ofMIPRE (S : MIPRE.SyncStrategy G.toMIPRE) : SyncStrategy G :=
  ⟨S.d, S.d_pos, S.P.M, S.P.selfAdjoint, S.P.projective, S.P.normalized⟩

theorem SyncStrategy.value_toMIPRE (S : SyncStrategy G) : S.toMIPRE.value = strategyValue G S := by
  rw [MIPRE.SyncStrategy.value_eq]; rfl

theorem SyncStrategy.strategyValue_ofMIPRE (S : MIPRE.SyncStrategy G.toMIPRE) :
    strategyValue G (SyncStrategy.ofMIPRE S) = S.value := by
  rw [MIPRE.SyncStrategy.value_eq]; rfl

/-- **The Challenge's synchronous value is the library's.** -/
theorem gameValue_eq_syncValue (G : SynchronousGame X A) :
    gameValue G = MIPRE.syncValue G.toMIPRE := by
  apply le_antisymm
  · refine Real.iSup_le (fun S => ?_) (MIPRE.syncValue_nonneg _)
    rw [← S.value_toMIPRE]
    exact le_ciSup (MIPRE.SyncStrategy.bddAbove_range_value _) S.toMIPRE
  · refine Real.iSup_le (fun S => ?_) (Real.iSup_nonneg fun S => ?_)
    · rw [← SyncStrategy.strategyValue_ofMIPRE S]
      refine le_ciSup ⟨1, ?_⟩ (SyncStrategy.ofMIPRE S)
      rintro r ⟨S, rfl⟩
      rw [← S.value_toMIPRE]
      exact S.toMIPRE.value_le_one
    · rw [← S.value_toMIPRE]
      exact S.toMIPRE.value_nonneg

/-- A game description of the library, read as one of the Challenge: the same data. -/
def TailoredGameData.of (g : TailoredGameValue.TailoredGameData) : TailoredGameData :=
  ⟨g.nV, g.lenR, g.lenL, g.w, g.cons⟩

theorem TailoredGameData.computable_of : Computable TailoredGameData.of :=
  ((Primrec.of_equiv_symm (e := TailoredGameData.equivTuple)).comp
    (Primrec.of_equiv (e := TailoredGameValue.TailoredGameData.equivTuple))).to_comp.of_eq
    fun _ => rfl

/-- **The two readings of a description are the same game.** -/
theorem TailoredGameData.toGame_toMIPRE (g : TailoredGameValue.TailoredGameData) :
    (TailoredGameData.of g).toGame.toMIPRE = g.toGame.toMIPRE := rfl

/-- A permutation strategy of the library, as one of the Challenge: the same observables. -/
noncomputable def PermStrategy.of {g : TailoredGameValue.TailoredGameData}
    (S : TailoredGameValue.PermStrategy g) : PermStrategy (TailoredGameData.of g) :=
  ⟨S.m, S.m_pos, S.U, S.signedPerm, S.invol, S.comm, S.pad, S.zAligned, S.commEdges⟩

theorem PermStrategy.value_of {g : TailoredGameValue.TailoredGameData}
    (S : TailoredGameValue.PermStrategy g) : (PermStrategy.of S).value = S.value := rfl

/-- **Challenge 1**, from `TailoredGameValue.tailored_halting_reduction`. -/
theorem tailored_halting_reduction : TailoredHaltingReduction := by
  obtain ⟨g, hg, h⟩ := TailoredGameValue.tailored_halting_reduction
  refine ⟨fun c => TailoredGameData.of (g c), TailoredGameData.computable_of.comp hg, fun c => ?_⟩
  obtain ⟨hc, hs⟩ := h c
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨S, hS⟩ := hc hh
    exact ⟨PermStrategy.of S, (PermStrategy.value_of S).trans hS⟩
  · have := hs hh
    rw [HaltingGameValue.SynchronousGame.gameValue_eq_syncValue] at this
    rw [gameValue_eq_syncValue]
    exact this

end TailoredGames

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
