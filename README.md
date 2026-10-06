# aldous-lyons-comparator

Independent verification, via `lake comparator` (the
[comparator](https://github.com/leanprover/comparator) that ships in the Lean toolchain), that the
[MIPRE-formalization](https://github.com/vidick/MIPRE-formalization) library proves the main
results of

* L. Bowen, M. Chapman, T. Vidick, *The Aldous–Lyons Conjecture II: Undecidability*,
  [arXiv:2501.00173](https://arxiv.org/abs/2501.00173) ("paper II"), and
* L. Bowen, M. Chapman, A. Lubotzky, T. Vidick, *The Aldous–Lyons Conjecture I: Subgroup Tests*,
  [arXiv:2408.00110](https://arxiv.org/abs/2408.00110) ("paper I").

There are two challenges.

> **1. `TMIP* = RE`** (paper II, `thm:tailored_MIP*=RE`). There is a computable map $g$ from
> Turing machines to (descriptions of) finite *tailored* non-local games such that, for every
> machine $c$,
>
> * if $c$ halts on the empty input, $g(c)$ has a perfect Z-aligned permutation strategy commuting
>   along edges;
> * if $c$ does not halt on the empty input, the synchronous value of $g(c)$ is at most $1/2$.
>
> In particular the synchronous value of tailored games is uncomputable.

> **2. The Aldous–Lyons conjecture is false.** For some $s$, some invariant random subgroup of the
> free group on $s$ generators is not a weak-* limit of finitely described invariant random
> subgroups.

Machines are Mathlib's `Nat.Partrec.Code`, "halts on the empty input" is `(c.eval 0).Dom`, and
"computable" is Mathlib's `Computable`. Paper II's reduction is polynomial-time; this statement
asks only that it be computable. Paper II's soundness clause reads `< 1/2`, but its proof bounds
every strategy's value by `1/2`, which bounds the supremum only by `≤ 1/2`; paper I uses the
theorem with `≤ 1/2`, as stated here.

## What to audit

Only [`Challenge.lean`](Challenge.lean), which imports **only Mathlib**. It is about 400 lines,
half of them docstrings, in two parts.

* **`TailoredGames`**: synchronous games and strategies and the synchronous value; tailored game
  descriptions and the game they describe; Z-aligned permutation strategies commuting along
  edges; the statement `TailoredHaltingReduction`; Challenge 1.
* **`AldousLyons`**: the space of subgroups of a free group with the product topology, invariant
  random subgroups, the finitely described ones, the conjecture; Challenge 2.

The definitions are the library's own, from its Mathlib-only statement files
`MIPRE/TailoredGameValue.lean`, `MIPRE/HaltingGameValue.lean` and `MIPRE/SubgroupTestValue.lean`,
repackaged for a reader: a synchronous strategy is given by its measurement operators directly
(self-adjoint idempotent matrices summing to the identity, so positivity is not a separate
axiom), the question weights of a tailored game are normalized in place, and a finite action of
a free group is a tuple of permutations rather than a structure. The tailored game and the
permutation strategies are the library's text verbatim.

If you believe `Challenge.lean` says the intended theorems, then a successful comparator run
certifies that the library proves them using only the standard axioms:

```text
propext, Quot.sound, Classical.choice
```

[`Solution.lean`](Solution.lean) imports the library and repeats every definition of
`Challenge.lean` verbatim (the comparator checks that they are identical in the two environments).
It then proves the two theorems from the library's `TailoredGameValue.tailored_halting_reduction`
and `SubgroupTestValue.aldous_lyons_false` by transport: the Challenge's synchronous value is the
library's (`gameValue_eq_syncValue`), a library game description and its Challenge reading are the
same game with the same permutation strategies (both by `rfl`), and the two sets of finitely
described IRSs are equal. The transport proofs are about 60 lines and are themselves checked by
the comparator, so they need not be trusted.

The comparator builds both modules in a `bwrap` sandbox. For `Solution`, that means compiling the
library from source at the commit pinned in [`lakefile.toml`](lakefile.toml). It then:

1. exports both modules with `leanexport`;
2. checks that each theorem's statement, and every declaration it uses, is identical in the two
   environments;
3. checks the axioms;
4. replays the proof through Lean's kernel and the toolchain's two independent kernels,
   [nanoda](https://github.com/ammkrn/nanoda_lib) and con-ron.

## Run it

```bash
./verify.sh
```

This needs Linux with `bwrap` (bubblewrap) and unprivileged user namespaces, `python3`, and
[elan](https://github.com/leanprover/elan). The comparator and the kernels come with the Lean
toolchain pinned in [`lean-toolchain`](lean-toolchain), so nothing else is downloaded except
Mathlib's build cache. MIPRE-formalization itself is compiled from source, which takes the better
part of an hour on a four-core machine. The GitHub workflow
[`comparator.yml`](.github/workflows/comparator.yml) runs the same script.

The run succeeds, with exit code `0`, only if both theorems pass every check.
