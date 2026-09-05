# Prior-art report: finite algebraic inequality candidates

**Research date:** 2026-09-05 (America/Chicago)

This is a bounded, reproducible prior-art check for three candidate theorems with
finite/discrete algebraic formulations in Lean. It is evidence about the snapshots
and queries listed below. It is not a global novelty or non-formalization claim.

## Scope and snapshots

| Target | Snapshot | Exact revision |
| --- | --- | --- |
| mathlib4 | shallow clone of leanprover-community/mathlib4 (master) | [7974e751bece493b6ff508039423ca9fa2452fa8](https://github.com/leanprover-community/mathlib4/commit/7974e751bece493b6ff508039423ca9fa2452fa8), fetched 2026-09-05 |
| StatLean | shallow clone of [StatLean/Stat-Lean](https://github.com/StatLean/Stat-Lean), main | [855b6afb69fead1bef066111732ed44df181040e](https://github.com/StatLean/Stat-Lean/commit/855b6afb69fead1bef066111732ed44df181040e), 2026-08-31 |
| Kraft | shallow clone of [elazarg/kraft](https://github.com/elazarg/kraft), default branch | [f742ff92fed86732fbca8b8ff7df2860c6b9a11b](https://github.com/elazarg/kraft/commit/f742ff92fed86732fbca8b8ff7df2860c6b9a11b), 2026-08-15 |
| local comparison baseline | mathlib package in erdos906_lean | [5450b53e5ddc75d46418fabb605edbf36bd0beb6](https://github.com/leanprover-community/mathlib4/commit/5450b53e5ddc75d46418fabb605edbf36bd0beb6), 2026-04-18 |

The generated online mathlib documentation is a moving target and may correspond to a
different release than either source checkout; source conclusions below use the exact
commits in the table.

## Search procedure

The following read-only checks were run against the two shallow clones.

* rg -n -i --glob '*.lean' 'samuelson|hammersley|chapman-robbins|pearson.*kurt|kurtosis|skewness' /tmp/mathlib4-prior-art/Mathlib
* rg -n -i --glob '*.lean' 'samuelson|hammersley|kurtosis|skewness|chapman-robbins' /tmp/statlean-prior-art/StatLean
* rg searches for centralMoment, centralMoment 3, centralMoment 4, third/fourth
  moment, mu3, mu4, and Pearson/skewness/kurtosis combinations.
* Authenticated GitHub CLI code searches (gh search code, account tcmartin) for:
  samuelson language:Lean, hammersley language:Lean, chapman-robbins language:Lean,
  chapman robbins language:Lean, pearson kurtosis language:Lean,
  skewness kurtosis language:Lean, centralMoment 3 language:Lean, and
  centralMoment 4 language:Lean, with a 20-result limit. The first six returned no
  relevant hits. The central-moment queries returned generic Gaussian-moment files in
  RemyDegenne/brownian-motion, formal-applied-math/formal-mathfin, and test code,
  not any of the three target inequalities. A later repository-restricted query was
  rate-limited after returning only docs/1000.yaml entries.
  Additional authenticated queries for chiSqDiv, chi-squared divergence, f-divergence,
  and chiSquared variance found no HCR declaration; they surfaced Kraft's finite-KL
  chi-squared upper bounds and unrelated chi-squared distribution files.

The mathlib docs/1000.yaml hits are unrelated theorem-index entries: Stolper–Samuelson
and Hammersley–Clifford. They are not formalizations of Samuelson's finite variance bound
or Hammersley–Chapman–Robbins estimation bound.

The official generated docs expose the relevant baseline interfaces:
[Moments.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Basic.html)
defines generic moments and centralMoment (with the explicit bridge only for order two),
while [Moments.Variance](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Variance.html)
documents variance bounds and the Bhatia–Davis theorem. These generated pages can lag or
lead the checked source revision, so they are supporting links rather than the absence
criterion.

## Candidate findings

| Candidate | Exact finite statement | Source scan finding | Formalization shape / scoped evidence |
| --- | --- | --- | --- |
| Samuelson (Laguerre–Samuelson) inequality | For \(x_1,\ldots,x_n\), \(\bar x=n^{-1}\sum_i x_i\), \(s^2=n^{-1}\sum_i(x_i-\bar x)^2\), every \(j\) satisfies \(|x_j-\bar x|\le\sqrt{n-1}\,s\). | No Samuelson/Laguerre name or matching theorem in the inspected mathlib or StatLean Lean sources. | Squared finite-sum form follows by Cauchy–Schwarz and rearrangement of the centered sum; scoped absence confidence: **medium-high**. |
| Hammersley–Chapman–Robbins (HCR) bound | For finite \(\Omega\), pmfs \(p,q\) with \(q\ll p\), and \(T:\Omega\to\mathbb R\), first state \((\mathbb E_qT-\mathbb E_pT)^2\le\operatorname{Var}_p(T)\chi^2(q\|p)\). If \(\chi^2(q\|p)>0\), divide to obtain \(\operatorname{Var}_p(T)\ge(\mathbb E_qT-\mathbb E_pT)^2/\chi^2(q\|p)\). For an unbiased estimator of \(g(\theta)\), apply this with \(p=p_\theta,q=p_{\theta'}\) and take the supremum over admissible \(\theta'\ne\theta\). | No HCR/Chapman–Robbins name or matching theorem in the inspected mathlib, StatLean, or Kraft sources. Hammersley hits in StatLean are Hammersley–Clifford graphical-model results; Robbins hits are empirical-Bayes material. Kraft has finite-KL chi-squared upper bounds, not a variance/expectation-difference lower bound. | Finite proof is a weighted Cauchy–Schwarz argument after writing \(q-p=p(q/p-1)\); scoped absence confidence: **medium** after the additional Kraft adjacency check. |
| Pearson skewness–kurtosis inequality | With central moments \(\mu_r=\mathbb E[(X-\mathbb EX)^r]\), \(\mu_2>0\): \(\mu_3^2+\mu_2^3\le\mu_2\mu_4\). Equivalently, standardized skewness \(\tau=\mu_3/\mu_2^{3/2}\) and kurtosis \(\kappa=\mu_4/\mu_2^2\) satisfy \(\kappa\ge\tau^2+1\). | No Pearson inequality or matching \(\mu_3,\mu_4\) theorem found in mathlib. StatLean does define StatLean.HypothesisTesting.skewness and proves third/fourth-moment lemmas for Edgeworth analysis, but no Pearson skewness–kurtosis inequality was found. | Unnormalized Cauchy–Schwarz form uses \(Y\) and \(Y^2-\mu_2\), avoiding square roots; scoped absence confidence: **medium** because StatLean has adjacent skewness infrastructure. |

## Mathematical sources and proof shapes

### Samuelson

Samuelson's paper states the finite-universe result in terms of \(N\) items and says that
no item can lie more than \(\sqrt{N-1}\) standard deviations from the mean, improving the
finite-universe use of Chebyshev. See Paul A. Samuelson, “How Deviant Can You Be?”,
Journal of the American Statistical Association 63 (1968), DOI
[10.1080/01621459.1968.10480944](https://www.tandfonline.com/doi/abs/10.1080/01621459.1968.10480944).

For a list \(x\), fix \(j\), write \(d=x_j-\bar x\), and use
\(\sum_{i\ne j}(x_i-\bar x)=-d\). Cauchy–Schwarz gives
\(d^2\le(n-1)\sum_{i\ne j}(x_i-\bar x)^2\). Since the total square sum is
\(d^2+\sum_{i\ne j}(x_i-\bar x)^2\), rearrangement gives
\(d^2\le(n-1)\sum_i(x_i-\bar x)^2/n\). The resulting Lean theorem can use
the squared form \(n(x_j-\bar x)^2\le(n-1)\sum_i(x_i-\bar x)^2\), which avoids a
Real.sqrt interface.

An accessible reference with the population-divisor convention and the two-sided form
\(\bar x-s\sqrt{n-1}\le x_j\le\bar x+s\sqrt{n-1}\) is Jensen and Styan,
“Some Comments on Samuelson's Inequality,” PDF:
[2001JensenStyan.pdf](https://web.tecnico.ulisboa.pt/~mcasquilho/compute/qc/%2Cstandarddev/2001JensenStyan.pdf).

### Hammersley–Chapman–Robbins

The original references are Hammersley, “On Estimating Restricted Parameters,” JRSS B
12 (1950), 192–229, DOI
[10.1111/j.2517-6161.1950.tb00056.x](https://doi.org/10.1111/j.2517-6161.1950.tb00056.x),
and Chapman–Robbins, “Minimum Variance Estimation Without Regularity Assumptions,”
Annals of Mathematical Statistics 22 (1951), 581–586, DOI
[10.1214/aoms/1177729548](https://doi.org/10.1214/aoms/1177729548).

For the finite algebraic version, define
\[
  \chi^2(q\|p)=\sum_{\omega:p(\omega)>0}
       p(\omega)\left(\frac{q(\omega)}{p(\omega)}-1\right)^2.
\]
Writing \(q-p=p(r-1)\), the expectation difference is
\(\sum_\omega p(\omega)(T(\omega)-\mathbb E_pT)(r(\omega)-1)\). Cauchy–Schwarz
gives the raw inequality
\[
  (\mathbb E_qT-\mathbb E_pT)^2
  \le \operatorname{Var}_p(T)\chi^2(q\|p).
\]
The displayed quotient form is a corollary under the explicit assumption
\(\chi^2(q\|p)>0\). This finite proof avoids differentiability or
dominated-convergence assumptions.

Theorem 6.1 in the public lecture notes Information-Theoretic Methods in High-Dimensional
Statistics gives the standard estimator form, with the quotient understood only when
\(\chi^2(P_{\theta'}\|P_\theta)>0\):
\[
R_\theta(\hat\theta)\ge\operatorname{Var}_\theta(\hat\theta)
\ge\sup_{\theta'\ne\theta}
\frac{(\mathbb E_\theta\hat\theta-\mathbb E_{\theta'}\hat\theta)^2}
     {\chi^2(P_{\theta'}\|P_\theta)}.
\]
See [it-stats.pdf](https://2prime.github.io/files/it-stats.pdf), §6.2, Theorem 6.1.

### Pearson

Pearson's original source is “Mathematical Contributions to the Theory of Evolution. XIX.
Second Supplement to a Memoir on Skew Variation,” Philosophical Transactions of the Royal
Society A 216 (1916), 429–457, DOI
[10.1098/rsta.1916.0009](https://doi.org/10.1098/rsta.1916.0009).

The modern statement \(\kappa\ge\tau^2+1\), with
\(\tau=E[(X-\mu)^3]/\sigma^3\) and
\(\kappa=E[(X-\mu)^4]/\sigma^4\), is explicitly attributed to Pearson (1916) and
stated for all distributions in Klaassen, “Inference via the Skewness-Kurtosis Set,”
International Statistical Review (2025),
[10.1111/insr.70007](https://onlinelibrary.wiley.com/doi/full/10.1111/insr.70007).

For a finite uniform list, \(\mu_r=n^{-1}\sum_i(x_i-\bar x)^r\). Put
\(Y=X-\mathbb EX\). Cauchy–Schwarz applied to \(Y\) and \(Y^2-\mu_2\) gives
\[
  \mu_3^2
  =\bigl(E[Y(Y^2-\mu_2)]\bigr)^2
  \le E[Y^2]E[(Y^2-\mu_2)^2]
  =\mu_2(\mu_4-\mu_2^2).
\]
Rearrangement gives the unnormalized theorem above. This form also has a clean degenerate
case \(\mu_2=0\), where both sides reduce to zero, and is preferable for a first Lean
statement.

StatLean's adjacent source is
[StatLean/HypothesisTesting/Bootstrap/Edgeworth.lean](https://github.com/StatLean/Stat-Lean/blob/855b6afb69fead1bef066111732ed44df181040e/StatLean/HypothesisTesting/Bootstrap/Edgeworth.lean):
it defines skewness as the third central moment divided by the cube of the standard
deviation and proves identities/absolute-moment bounds for Edgeworth expansions. The scan
found no central-moment kurtosis theorem, Pearson skewness–kurtosis theorem, or declaration equivalent to
\(\mu_3^2+\mu_2^3\le\mu_2\mu_4\). Pearson hits in StatLean instead concern Pearson
chi-square statistics and Neyman–Pearson testing; unrelated kurtosis declarations occur
in the GARCH files; Hammersley hits concern the Hammersley–Clifford theorem.

## Adjacency review for HCR

The inspected mathlib snapshot has an InformationTheory/KullbackLeibler API, including
klDiv, klFun, klDiv_map_le, Gibbs-type nonnegativity, and likelihood-ratio integral
identities. It has no chi-square divergence, generic f-divergence API, or HCR variational
representation in the searched source tree. The relevant source files are
[KullbackLeibler/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/7974e751bece493b6ff508039423ca9fa2452fa8/Mathlib/InformationTheory/KullbackLeibler/Basic.lean),
[KullbackLeibler/KLFun.lean](https://github.com/leanprover-community/mathlib4/blob/7974e751bece493b6ff508039423ca9fa2452fa8/Mathlib/InformationTheory/KullbackLeibler/KLFun.lean),
and [Probability/Moments/Covariance.lean](https://github.com/leanprover-community/mathlib4/blob/7974e751bece493b6ff508039423ca9fa2452fa8/Mathlib/Probability/Moments/Covariance.lean).
The last file supplies generic covariance algebra, including covariance_eq_sub; it does
not compare expectations under two different probability measures.

The inspected StatLean snapshot has adjacent but mathematically different results:

* [PointEstimation/InformationInequality/CramerRao.lean](https://github.com/StatLean/Stat-Lean/blob/855b6afb69fead1bef066111732ed44df181040e/StatLean/PointEstimation/InformationInequality/CramerRao.lean)
  contains the private
  square-integral Cauchy–Schwarz lemma sq_integral_mul_le and the public
  cramer_rao and cramer_rao_of_deriv theorems. These compare an estimator with a
  derivative-derived score under one model measure and a positive Fisher information.
* [PointEstimation/InformationInequality/Multiparameter.lean](https://github.com/StatLean/Stat-Lean/blob/855b6afb69fead1bef066111732ed44df181040e/StatLean/PointEstimation/InformationInequality/Multiparameter.lean)
  contains the private
  sq_covariance_le lemma and public covariance_matrix_inequality and
  multiparameter_cramer_rao. These compare covariance and variance of functions under
  one fixed probability measure.
* [Minimaxity/ForMathlib/KLDivergence.lean](https://github.com/StatLean/Stat-Lean/blob/855b6afb69fead1bef066111732ed44df181040e/StatLean/Minimaxity/ForMathlib/KLDivergence.lean)
  and [KLDataProcessing.lean](https://github.com/StatLean/Stat-Lean/blob/855b6afb69fead1bef066111732ed44df181040e/StatLean/Minimaxity/ForMathlib/KLDataProcessing.lean) formalize KL
  identities, mixture minimization, and data processing. They do not define chi-square
  divergence or an expectation-difference variational formula.
* [MultipleTesting/ForMathlib/ChiSquared.lean](https://github.com/StatLean/Stat-Lean/blob/855b6afb69fead1bef066111732ed44df181040e/StatLean/MultipleTesting/ForMathlib/ChiSquared.lean)
  and the goodness-of-fit files define the
  chi-squared probability distribution/statistics. Those declarations are unrelated to
  \(\chi^2(q\|p)\) between two pmfs.
* [Kraft InformationTheory/Divergence/Basic.lean](https://github.com/elazarg/kraft/blob/f742ff92fed86732fbca8b8ff7df2860c6b9a11b/InformationTheory/Divergence/Basic.lean)
  defines the finite KL sum klFin and proves Gibbs/relabeling facts.
  [Divergence/Tensorization.lean](https://github.com/elazarg/kraft/blob/f742ff92fed86732fbca8b8ff7df2860c6b9a11b/InformationTheory/Divergence/Tensorization.lean)
  proves klFin_mix_le_chiSq, an upper bound of KL of a mixture by a
  chi-squared-like finite sum. [Divergence/Binary.lean](https://github.com/elazarg/kraft/blob/f742ff92fed86732fbca8b8ff7df2860c6b9a11b/InformationTheory/Divergence/Binary.lean)
  proves the binary specialization klBin_le_sq_div. Neither file defines
  \(\chi^2(q\|p)\) as a divergence with a variance variational representation, and neither
  states an HCR estimator bound.

Thus these nearby declarations provide reusable Cauchy–Schwarz/covariance infrastructure
but are not equivalent prior formalizations of the finite HCR statement.

## Adjacency review for Pearson

The mathlib source scan found centralMoment and the bridge
centralMoment_two_eq_variance in Probability/Moments/Basic.lean, plus generic variance
and covariance identities. It found no matching order-three/order-four central-moment
inequality.

StatLean/HypothesisTesting/Bootstrap/Edgeworth.lean defines skewness, proves
integral_cube_centredLaw, and includes moment bounds such as
abs_integral_pow_three_le and the private skewness_window/skewness_ledger arithmetic.
These are used for Edgeworth expansions and do not state
\(\mu_3^2+\mu_2^3\le\mu_2\mu_4\). StatLean also has unrelated kurtosis declarations
for ARCH/GARCH models; those do not establish Pearson's general inequality.

The additional Kraft source scan found no centralMoment, skewness, kurtosis, third/fourth
moment, or raw finite-sum equivalent of this inequality.

## Explicit rejection: Bhatia–Davis

Bhatia–Davis is not a viable “absent theorem” candidate for this task. The local mathlib
baseline already contains
ProbabilityTheory.variance_le_sub_mul_sub in
Mathlib/Probability/Moments/Variance.lean (at the comparison-baseline commit
5450b53e5ddc75d46418fabb605edbf36bd0beb6), documented as the Bhatia–Davis inequality.
The current shallow mathlib snapshot contains the same theorem at source line 466.
Popoviciu's variance upper bound is also present nearby. See the official source file at
[Mathlib/Probability/Moments/Variance.lean](https://github.com/leanprover-community/mathlib4/blob/7974e751bece493b6ff508039423ca9fa2452fa8/Mathlib/Probability/Moments/Variance.lean#L460-L480).

These findings support only the bounded searches and exact revisions recorded here; they
do not establish that no formalization exists elsewhere.
