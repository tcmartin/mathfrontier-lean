# Classical statistical inequalities in Lean 4

Kernel-checked proofs of three established statistical inequalities:

| Result | Formal scope | File |
| --- | --- | --- |
| Samuelson's inequality | Every observation in an arbitrary nonempty finite real sample; population variance | [Samuelson.lean](FrontierTheorems/Samuelson.lean) |
| Hammersley–Chapman–Robbins | Arbitrary finite statistical models, including zero-probability outcomes under absolute continuity | [HammersleyChapmanRobbins.lean](FrontierTheorems/HammersleyChapmanRobbins.lean) |
| Pearson's skewness–kurtosis inequality | Arbitrary finite probability distributions; polynomial and standardized forms | [Pearson.lean](FrontierTheorems/Pearson.lean) |

These are formalizations of classical mathematics, not new mathematical discoveries.
The finite probability results do not claim the unrestricted measure-theoretic versions.
See [PRIOR_ART.md](PRIOR_ART.md) for the dated, scoped search for existing Lean formalizations.
Absence from the checked sources is not a guarantee of worldwide priority.

## Reproduce

Install [elan](https://github.com/leanprover/elan), then:

```sh
git clone https://github.com/tcmartin/mathfrontier-lean.git
cd mathfrontier-lean
lake exe cache get
./scripts/verify.sh
```

`lean-toolchain` pins Lean **4.30.0-rc2**. `lakefile.toml` and the committed
`lake-manifest.json` pin mathlib at **5450b53e5ddc75d46418fabb605edbf36bd0beb6**
and its transitive dependencies. The public theorem files rely on mathlib's
finite-sum and Cauchy–Schwarz infrastructure.

The verification script rebuilds the library, checks concrete edge cases, and
prints the axioms of every theorem in these modules. The allowed foundational
axioms are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
It rejects additional axioms, admitted proofs, and native computation as proof evidence.
Compiler verification establishes the formal statements; the explanations below
identify the mathematical interpretation and scope.

## Statements and sources

### Samuelson

For any nonempty sample of size n, let m be its arithmetic mean and
v = sum((x_i − m)²)/n its **population** variance. For every observation j,

```text
(x_j − m)² ≤ (n − 1) v.
```

It gives a sharp limit on an individual observation's distance from the mean,
with no distributional assumption. It also holds for n = 1, when both sides vanish.
The division is by n, not the n − 1 used for an unbiased sample variance estimator.

Source: Paul A. Samuelson, [How Deviant Can You Be?](https://doi.org/10.1080/01621459.1968.10480944),
*Journal of the American Statistical Association* 63 (1968), 1522–1525.
Historical and mathematical context: Jensen and Styan,
[Jensen–Styan survey](https://web.tecnico.ulisboa.pt/~mcasquilho/compute/qc/%2Cstandarddev/2001JensenStyan.pdf) (2001).

### Hammersley–Chapman–Robbins

For probability masses p and q on any finite sample space, assume q_i = 0 whenever
p_i = 0. Write E_p(T) = sum(p_i T_i), Var_p(T) = sum(p_i(T_i − E_p(T))²), and
χ²(q ‖ p) = sum((q_i − p_i)²/p_i). At p_i = q_i = 0, the summand is zero.

```text
(E_q(T) − E_p(T))² ≤ Var_p(T) χ²(q ‖ p).
```

When χ² is positive and T is unbiased at parameter values θ and η,

```text
(η − θ)² / χ²(q ‖ p) ≤ Var_p(T).
```

This bounds an estimator's variance without differentiating a likelihood or
assuming the regularity conditions of the Cramér–Rao bound. The polynomial
expectation-shift theorem also covers zero divergence. The published lower-bound
corollary is the two-point bound, not a separate formalization of a supremum over
an entire parameter family.

Sources: J. M. Hammersley, [On Estimating Restricted Parameters](https://doi.org/10.1111/j.2517-6161.1950.tb00056.x) (1950);
D. G. Chapman and H. Robbins, [Minimum Variance Estimation Without Regularity Assumptions](https://doi.org/10.1214/aoms/1177729548) (1951).
Accessible presentation: Yihong Wu, [Information-theoretic methods for high-dimensional statistics, Lecture 6](https://www.stat.yale.edu/~yw562/teaching/598/lec06.pdf).

### Pearson

For nonnegative weights p summing to one and real observations x, define central
moments m_k = sum(p_i (x_i − sum(p_j x_j))^k). Then

```text
m₃² + m₂³ ≤ m₂ m₄.
```

The polynomial form includes zero variance. When m₂ > 0,

```text
m₃²/m₂³ + 1 ≤ m₄/m₂².
```

The left fraction is squared standardized skewness; the right fraction is
kurtosis, not excess kurtosis. This constrains possible moment combinations and
provides a consistency check for distribution models and descriptive statistics.

Sources: Karl Pearson, [Mathematical Contributions to the Theory of Evolution XIX](https://doi.org/10.1098/rsta.1916.0009) (1916);
Klaassen and van Es, [Inference via the Skewness–Kurtosis Set](https://doi.org/10.1111/insr.70007) (2025), equation (1.1),
with [author-deposited full text](https://pure.uva.nl/ws/files/270239230/Int_Statistical_Rev_-_2025_-_Klaassen_-_Inference_via_the_Skewness_Kurtosis_Set.pdf).

## License

Original proof code and documentation: MIT, see [LICENSE](LICENSE).
Mathlib retains its Apache 2.0 license. Cited papers retain their own rights.
