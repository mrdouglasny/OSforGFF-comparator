# OSforGFF-comparator

Independent Comparator verification of the headline theorem of
[**mrdouglasny/OSforGFF**](https://github.com/mrdouglasny/OSforGFF): the massive Gaussian Free
Field in Euclidean spacetime of any dimension `d ≥ 2` satisfies all of the
Osterwalder–Schrader axioms.

This repository contains **no mathematics of its own**. It is a thin wrapper, in the sense of
the [Palomar Registry](https://palomar-registry.org) policy: it exposes the library's theorem
to [Comparator](https://github.com/leanprover/comparator) and names the substantive
development, pinned to an exact commit, in `formalization.yaml`.

## The two files that matter

| file | what it is |
|---|---|
| `Challenge.lean` | the statement a mathematician audits — **imports Mathlib and nothing else** |
| `Solution.lean` | the same declaration, proved from OSforGFF |

The Challenge may not import OSforGFF, or anything else project-specific, anywhere in its
transitive import closure. So it restates from scratch, in Mathlib's vocabulary, everything the
theorem needs: spacetime and Schwartz test functions, field configurations as tempered
distributions, the generating functional, the free covariance in its proper-time form, the
Euclidean group and its action, time reflection and the OS star operation, positive-time test
functions, and the five OS predicates. Comparator then checks that the Solution really does
discharge that statement, and that the proof rests on nothing beyond Lean's three core axioms.

That constraint is the point. The audit surface is written in a vocabulary the reader already
trusts, and none of it is taken on the library's word.

The design choices behind the restatement — why existential + characterization, why the
proper-time covariance — and the full dictionary between the Challenge's self-contained
definitions and the library's originals are laid out in
[docs/challenge.md](docs/challenge.md).

## Verifying

```bash
lake build                 # builds Challenge and Solution — both are default targets
./scripts/verify-comparator.sh
bash scripts/check-pair.sh # source-level gate: no axioms/escape hatches; Challenge has
                           # exactly the challenge-hole sorry, Solution none
```

`verify-comparator.sh` fetches and pins Comparator, `lean4export`, NanoDa and Landrun, then
runs the comparison under a real sandbox with the independent NanoDa kernel replay enabled.
The `lean4export` pin tracks `lean-toolchain` (`v4.33.0-rc1`); revisit it, and NanoDa
compatibility, whenever the toolchain moves. Landrun is Linux-only, so the scripted run wants
Linux — CI does it on every push.

## The pin, and the canary

`lakefile.toml` requires OSforGFF at a fixed commit. That is deliberate: a registry entry
names an exact commit, and re-pinning should be a decision rather than a drift.

The cost of pinning is that the library can move underneath a statement that no longer builds
against it, silently. So CI carries a scheduled **canary** job that builds the same pair
against OSforGFF `main` instead of the pin. The canary is `continue-on-error`: main moving
ahead of the pin is expected and is not a failure of this repository. A red canary means the
registered statement no longer builds against the library, which is the signal to re-pin and
re-verify.

Re-pinning is triggered by any of:

- a **meaningful library milestone**, verified here before it enters any registry version;
- a **metadata change** in the library — not only its mathematics — since Palomar inspects
  the substantive repository at the declared commit;
- a **red canary**, the drift signal.

## Why the pair lives here rather than in OSforGFF

Keeping the registry artifacts out of the library leaves OSforGFF free to be a physics project
— its lakefile, CI and file tree carry no registry requirements, and Palomar's policy, which is
pre-launch and still changing, churns here instead of in the library's history.

The trade is the sync burden the canary is there to manage. Note also that the choice is
effectively one-way: Palomar's automated updates must retain the same source repository and
Comparator configuration path, and a repository transfer requires operator review.

## Provenance

The library is by Michael R. Douglas, Sergey A. Cherkis, Sarah Hoback, Anna Mei and Ron
Nissim; the Challenge/Solution pair is by Sergey A. Cherkis. Apache-2.0, matching OSforGFF.
