# Prior-art review: finite greedy submodular maximization

**Review date:** 2026-09-05 (America/Chicago)  
**Scope:** bounded inspection of current Mathlib, StatLean, and selected public Lean repositories for a machine-checked theorem implementing the Nemhauser–Wolsey–Fisher (NWF) greedy guarantee. Repository snapshots and commit IDs are recorded below. This is a scoped search record, not a proof of global absence.

## Candidate theorem

Let `E` be finite and let `f : Finset E → ℝ` satisfy

* `f ∅ = 0` (normalization);
* `A ⊆ B → f A ≤ f B` (monotonicity); and
* diminishing returns, `A ⊆ B` and `x ∉ B` imply
  `f (A ∪ {x}) - f A ≥ f (B ∪ {x}) - f B`.

For an integer `k ≥ 1`, define `G₀ = ∅` and let `Gᵢ₊₁` add an element outside `Gᵢ` having maximum marginal gain. If `O` maximizes `f` over all sets of cardinality at most `k`, then the classical finite guarantee is

```
f Gₖ ≥ (1 - (1 - 1/k)^k) f O.
```

Since `(1 - 1/k)^k ≤ exp (-1)`, this implies `f Gₖ ≥ (1 - 1/e) f O`. The finite-k inequality is the better first formal target: it avoids an asymptotic statement and isolates the greedy residual recurrence. A weighted maximum-coverage application takes `f S` to be the nonnegative weight of the union of the sets indexed by `S`.

The statement needs an explicit tie-breaking convention for a *function* `G`; an existential version can instead quantify a maximizer at every step. The `k = 0` case should be stated separately or excluded.

## Primary mathematical sources

* [Nemhauser, Wolsey, Fisher, “An analysis of approximations for maximizing submodular set functions—I,” DOI 10.1007/BF01588971](https://doi.org/10.1007/BF01588971), *Mathematical Programming* 14 (1978), 265–294. The paper defines submodularity on a finite ground set, studies `max {z(S) : |S| ≤ K}`, and gives the greedy factor `1 - ((K-1)/K)^K`, with limit `(e-1)/e`.
* [INFORMS record, “Best Algorithms for Approximating the Maximum of a Submodular Set Function”](https://pubsonline.informs.org/doi/abs/10.1287/moor.3.3.177), Nemhauser–Wolsey (1978). The abstract records the normalized, nondecreasing submodular setting and the greedy-algorithm result.
* [Open copy of the 1978 NWF-I paper](https://thibaut.horel.org/submodularity/papers/nemhauser1978.pdf). This was used to check the exact finite factor against the bibliographic records; the publisher DOI remains the authoritative citation.

## Lean-library search

### Mathlib

Snapshot: [mathlib4 commit 7974e751bece493b6ff508039423ca9fa2452fa8](https://github.com/leanprover-community/mathlib4/tree/7974e751bece493b6ff508039423ca9fa2452fa8), inspected 2026-09-05. Targeted searches covered `submodular`, `submodularity`, `diminishing returns`, `greedy`, `maximum coverage`, and cardinality-constraint terms.

The relevant hits are matroid-rank submodularity, not a generic set-function API or greedy approximation theorem:

* [`cRk_inter_add_cRk_union_le`](https://github.com/leanprover-community/mathlib4/blob/7974e751bece493b6ff508039423ca9fa2452fa8/Mathlib/Combinatorics/Matroid/Rank/Cardinal.lean#L297) proves submodularity of cardinal matroid rank.
* [`eRk_inter_add_eRk_union_le` and alias `eRk_submod`](https://github.com/leanprover-community/mathlib4/blob/7974e751bece493b6ff508039423ca9fa2452fa8/Mathlib/Combinatorics/Matroid/Rank/ENat.lean#L271-L283) do the analogous rank result for extended naturals.
* [`Finset.exists_max_image`](https://github.com/leanprover-community/mathlib4/blob/7974e751bece493b6ff508039423ca9fa2452fa8/Mathlib/Data/Finset/Max.lean#L387) supplies a useful finite maximum-existence lemma for constructing greedy steps.

No generic `f : Finset E → ℝ` submodular/diminishing-returns definition, greedy sequence, NWF factor, or maximum-coverage approximation declaration was found in this snapshot. This is an inspection result for the named source areas, not a global theorem-name claim.

### StatLean

Snapshot: [StatLean commit 855b6afb69fead1bef066111732ed44df181040e](https://github.com/StatLean/StatLean/tree/855b6afb69fead1bef066111732ed44df181040e), inspected 2026-09-05. Searches over `StatLean/` found no submodular, diminishing-returns, maximum-coverage, or greedy-cardinality framework. Its optimization and statistical files are unrelated to this finite combinatorial theorem.

## Public-repository checks and near misses

* [apnelson1/Matroid, `WIP/Submodular.lean`, commit 09177e2bfdaed1199b81221f9f88064fd4309f5b](https://github.com/apnelson1/Matroid/blob/09177e2bfdaed1199b81221f9f88064fd4309f5b/WIP/Submodular.lean) defines generic lattice submodularity and develops matroid constructions from integer-valued submodular functions, polymatroid rank, and transversal results. Direct inspection of this source found no greedy approximation algorithm or NWF guarantee. This is prior art for the submodular-function vocabulary and related combinatorics; those definitions are not claimed as new.
* [derivon-ai/omnibias, commit 60624870ca9dce2d261dd1b242858c5c063150eb](https://github.com/derivon-ai/omnibias/tree/60624870ca9dce2d261dd1b242858c5c063150eb) contains a substantial **Python** `omnibias-submodular` package. Its [README](https://github.com/derivon-ai/omnibias/blob/60624870ca9dce2d261dd1b242858c5c063150eb/packages/omnibias-submodular/README.md) describes continuous greedy, rounding, weighted coverage, and a `(1 - 1/e)` guarantee; [`greedy_maximize`](https://github.com/derivon-ai/omnibias/blob/60624870ca9dce2d261dd1b242858c5c063150eb/packages/omnibias-submodular/src/omnibias/submodular/_core/greedy.py) is executable Python. The repository’s `.lean` files are in separate kernel/analytic projects and do not formalize the submodular API or its guarantee. This is implementation/documentation prior art, not a Lean theorem match.
* [Olangu/pairwise-correlation-gap-lean, commit 6c6b61a3c7ed0bab880b68f646ac039b6c41901e](https://github.com/Olangu/pairwise-correlation-gap-lean/tree/6c6b61a3c7ed0bab880b68f646ac039b6c41901e) is a completed finite Lean counterexample. [`CorrelationGap.lean`](https://github.com/Olangu/pairwise-correlation-gap-lean/blob/6c6b61a3c7ed0bab880b68f646ac039b6c41901e/CorrelationGap.lean#L37-L124) defines a specialized coverage function on `Finset (Fin 5)` and proves specialized monotonicity and submodularity by finite decision. It has no generic submodular-function interface, greedy construction, or approximation factor. This is useful finite coverage precedent but not an NWF match.
* [bf24-note, commit 8ada1a7b6ad248a01cb046e86a9727796ea2fed5](https://github.com/daizisheng/bf24-note/tree/8ada1a7b6ad248a01cb046e86a9727796ea2fed5) and [arXiv:2604.27362](https://arxiv.org/abs/2604.27362) machine-check scalar inequalities used in Buchbinder–Feldman-style approximation analysis. The paper explicitly says the algorithm and its correctness analysis are not formalized; the Lean file contains no submodular objective or greedy algorithm. This is algebraic support at most, not prior art for the target theorem.

GitHub code/repository searches were also run for `submodular`, `submodularity`, `Nemhauser`, `maximum coverage`, `diminishing returns`, and `greedy approximation`. The code-search API became rate-limited (HTTP 403) during the bounded pass; therefore those searches are supplementary and cannot support an exhaustive public-repository claim.

## Proof-shape and infrastructure boundary

The expected finite proof is algebraic once the finite data are exposed:

1. choose a marginal maximizer from a nonempty finite candidate set (Mathlib’s `Finset.exists_max_image` is a direct building block);
2. telescope the marginal gains along `O \ Gᵢ`, using diminishing returns and monotonicity to obtain the one-step residual bound;
3. iterate `Rᵢ₊₁ ≤ (1 - 1/k) Rᵢ` for `Rᵢ = f O - f Gᵢ`;
4. conclude the exact finite factor by finite induction.

The scalar exponential estimate is already in the pinned mathlib as `Real.one_sub_div_pow_le_exp_neg`; the release reuses it to derive the `1 - 1/e` corollary. The weighted maximum-coverage layer requires a union-of-indexed-sets definition and a proof that weighted union cardinality/sum is monotone and submodular. No complete generic maximum-coverage approximation theorem was found already packaged in the inspected sources.

## Excluded Markov flagship

The proposed finite Doeblin–Dobrushin flagship is not a clean novelty target. [RL Theory in Lean](https://github.com/ShangtongZhang/rl-theory-in-lean/tree/fec0b5d1a03e90479945286532f89e4f22cfcd1e) already exposes irreducibility/aperiodicity, Doeblin minorization, contraction, stationary existence/uniqueness, and geometric mixing; the [arXiv paper](https://arxiv.org/abs/2511.03618) describes those formal results. Independently, [Econlib’s Doeblin file](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Math/Probability/Doeblin.lean) proves finite total-variation contraction, and its [ergodic file](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Probability/Markov/Ergodic.lean) includes stationary existence/uniqueness and geometric convergence. Those are genuine theorem matches for the full route, unlike the NWF near misses above.

## Scoped conclusion

As of 2026-09-05, the bounded inspection located no generic, machine-checked Lean formalization of the finite NWF greedy guarantee in the current Mathlib snapshot, StatLean snapshot, or the selected public repositories. The strongest overlap is specialized finite coverage (Olangu), executable Python submodular optimization (omnibias), and scalar approximation inequalities (bf24-note). A formalization should be described narrowly as a finite NWF theorem with an explicit greedy sequence and exact finite-k factor; any claim of global absence would exceed this evidence.
