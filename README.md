# A Lean proof of the Janisch–Lehéricy conjecture

Start with [the theorem in Lean](JanischLehericy/Published.lean) and [Theorem 3 of the manuscript](paper/janisch-lehericy-proof.pdf). Both give the published form of Conjecture 1.4. The manuscript writes $\sigma$ for the standard deviation and $q=D+1$ for the largest closed neighborhood size. The Lean statement uses $v=\sigma^2$ and $m=q$. The formal proof uses Lean 4.24.0 and mathlib v4.24.0. [Original conjecture and Definition 1.1](https://doi.org/10.1007/s10959-024-01363-z)

To compile the [manuscript](paper/janisch-lehericy-proof.tex) and its [introduction](paper/introduction.tex), run `latexmk -cd -pdf paper/janisch-lehericy-proof.tex` from this directory.

The [arXiv submission ZIP](paper/arxiv-submission.zip) contains both TeX sources and the Lean project. Rebuild the ZIP with `python3 paper/package_arxiv.py`.

## The statement

Let $G$ be a dependency graph of maximum degree $D$ for a finite family of real random variables $Y_i$. Fix $2 < \delta \le 3$ and assume each variable has a finite absolute moment of order $\delta$.

Let $S=\sum_i Y_i$ have positive standard deviation $\sigma$. Write $W=(S-\mathbb{E}S)/\sigma$ and $q=D+1$. The Kolmogorov distance from $W$ to a standard normal is at most the smaller of 1 and

```math
2{,}000{,}000\,q^{\delta-1}\sum_i \mathbb{E}\left|\frac{Y_i}{\sigma}\right|^\delta.
```

This bounds the error in the normal approximation at every real threshold, including atoms of the sum. [Theorem 3 in the manuscript](paper/janisch-lehericy-proof.pdf) gives the equivalent expression in the notation of the original conjecture.

In the [Lean statement](JanischLehericy/Published.lean), the hypothesis `hG` spells out independence of the joint random vectors on disjoint vertex sets with no connecting edge. The last line applies the [raw-moment proof](JanischLehericy/RawMoments.lean).

The stronger normalized theorem applies to centered square-integrable $X_i$ whose sum has variance one. For any positive integer $m$ bounding every closed neighborhood size, put $\ell(t)=t^2\min(1,t)$ and $\beta=m^{-1}\sum_i\mathbb E\ell(m|X_i|)$. The bound is $\min(1,250{,}000\,\beta)$. Centering and rescaling the paper's variables costs a factor of at most eight in the raw moment estimate. [Normalized theorems](JanischLehericy/Theorem.lean) · [Conversion to raw moments](JanischLehericy/RawMoments.lean)

## Verify the proof

The [verification instructions](VERIFY.md) cover the build, the axiom audit, and the kernel replay of all three theorems.

## Proof map

| Step | Lean source |
| --- | --- |
| Deterministic inequality for adjacent pairs with constant 8 | [Pair](JanischLehericy/Pair.lean) |
| Truncation, envelope moments and deletion estimates | [Budget](JanischLehericy/Budget.lean), [Moments](JanischLehericy/Moments.lean) |
| Independence after deletion, random intervals and normalization | [Dependence](JanischLehericy/Dependence.lean), [Interval](JanischLehericy/Interval.lean), [Restriction](JanischLehericy/Restriction.lean), [Comparison](JanischLehericy/Comparison.lean) |
| Covariance cancellation and graph bound for a smooth test | [SteinIdentity](JanischLehericy/SteinIdentity.lean), [SteinResidual](JanischLehericy/SteinResidual.lean) |
| Normal Stein solution, Mills inequalities and smoothing at the CDF jump | [Gaussian](JanischLehericy/Gaussian.lean), [Average](JanischLehericy/Average.lean), [NormalTest](JanischLehericy/NormalTest.lean) |
| Induction on vertex count and assembly of the end theorems | [Induction](JanischLehericy/Induction.lean), [Theorem](JanischLehericy/Theorem.lean), [RawMoments](JanischLehericy/RawMoments.lean) |

The manuscript and the formalization use the secant form of Stein's identity and the estimate $1/16+16\beta$ for the second moment of the deleted sum.
