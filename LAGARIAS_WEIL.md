# Lagarias Li/Weil normalization map

This note records the next formalization target from Jeffrey C. Lagarias,
*Li coefficients for automorphic L-functions*, Ann. Inst. Fourier 57 (2007),
1689--1740, Section 3, DOI 10.5802/aif.2311. Nothing here is currently a Lean theorem.

## Hypotheses and ambient test space

Lagarias fixes an irreducible cuspidal unitary automorphic representation
`pi` of `GL(N)`, its associated `xi(s,pi)`, and the multiset `Z(pi)` of its
zeros counted with multiplicity. The ambient space `A` consists of functions
holomorphic on `0 < Re(s) < 1` satisfying, uniformly in that strip outside
`|Im(s)| <= 1`, the bound `F(s) = O(1/|s|)`.

For `F,G in A`, equation (3.1) defines

```text
<F,G>_W(pi) = sum_{rho in Z(pi)} F(rho) * conjugate(G(1-conjugate(rho))).
```

The sum is absolute under the stated growth condition, is linear in `F` and
conjugate-linear in `G`, and uses zero multiplicities. The printed PDF's
overbar on the second factor is easy to lose in text extraction.

## Li test functions and exact normalization

The Li class `L` comprises rational functions in `C(s)` which vanish at
infinity and whose polar divisor is supported on `{0,1}`. Equation (3.2) is

```text
G_n(s) = 1 - (1 - 1/s)^n,   n in Z.
```

All `G_n` except `G_0=0` form a basis of `L`, and
`lambda_n(pi)=sum'_{rho in Z(pi)} G_n(rho)` uses star convergence.
Theorem 3.1 gives (3.3)

```text
<G_n,G_m>_W(pi)
  = lambda_n(pi) + lambda_{-m}(pi) - lambda_{n-m}(pi),
```

and its diagonal specialization (3.4)

```text
||G_n||_W(pi)^2
  = lambda_n(pi) + lambda_{-n}(pi)
  = 2 * Re(lambda_n(pi)).
```

The proof uses `G_{-m}(s)=G_m(1-s)` (3.5) and
`G_n(s)G_{-m}(s)=G_n(s)+G_{-m}(s)-G_{n-m}(s)` (3.6).
Thus the diagonal normalization is `2*Re(lambda_n)`, not `lambda_n` in
general. For Riemann zeta the coefficients are real, so it is `2*lambda_n`.
RHGarden is zero-based: `classicalLiRealCoefficient k` represents
`lambda_(k+1)`, corresponding to `G_(k+1)`.

The next formal boundary is to define this test family and the zero-sum/Weil
form with its convergence convention, then specialize (3.4). Until then all
edges through `WeilLiTestFunctions` and `WeilQuadraticValues` remain
`LiteratureCertified`.
