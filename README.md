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

Only [`Challenge.lean`](Challenge.lean), which imports **only Mathlib**. It has three parts.

* **`HaltingGameValue`**: synchronous games, synchronous strategies and the synchronous value,
  first-order game descriptions, `HaltsOnEmptyInput`. This is the library's statement file
  `MIPRE/HaltingGameValue.lean` without its final definition, the statement of
  "MIP\* = RE", which is not used here. The same definitions make up the challenge of
  [`vidick/mipre-comparator`](https://github.com/vidick/mipre-comparator).
* **`TailoredGameValue`**: tailored games, Z-aligned permutation strategies commuting along edges,
  and the statement `TailoredHaltingReduction`. This is the library's statement file
  `MIPRE/TailoredGameValue.lean`, verbatim, with Challenge 1 appended.
* **`AldousLyons`**: the space of subgroups of a free group with the product topology, invariant
  random subgroups, the finitely described ones, the conjecture, and Challenge 2. Read it in full:
  it is about 75 lines.

The first two parts can be checked against the library mechanically, at the commit pinned in
[`lakefile.toml`](lakefile.toml):

```bash
SRC=https://raw.githubusercontent.com/vidick/MIPRE-formalization/6d1962e2a70b85461912c684526fafb71e177b2d/MIPRE
part() { sed -n "/^namespace $1/,/^end $1/p"; }
diff <(curl -sL $SRC/HaltingGameValue.lean | part HaltingGameValue) <(part HaltingGameValue < Challenge.lean)
diff <(curl -sL $SRC/TailoredGameValue.lean | part TailoredGameValue) <(part TailoredGameValue < Challenge.lean)
```

The first diff shows only the removed final definition and its section title; the second, only
the appended theorem.

If you believe `Challenge.lean` says the intended theorems, then a successful comparator run
certifies that the library proves them using only the standard axioms:

```text
propext, Quot.sound, Classical.choice
```

[`Solution.lean`](Solution.lean) imports `MIPRE.TailoredMIP` from the library.

* Challenge 1 is proved there under its own name, so the Solution restates nothing.
* For Challenge 2, the Solution repeats the `AldousLyons` definitions verbatim. It transports
  the library's `SubgroupTestValue.aldous_lyons_false` to them: the library packages a finite
  action as a structure, and the two sets of finitely described IRSs are equal.

The comparator builds both modules in a `bwrap` sandbox. For `Solution`, that means compiling the
library from source at the pinned commit. It then:

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
