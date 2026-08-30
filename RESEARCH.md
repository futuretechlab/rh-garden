# Research corridor: xi to the Li sequence

**Status: this project does not currently prove the Riemann Hypothesis.** The
implemented corridor organizes known identities and exposes missing proof
obligations; most analytic bridges are literature-certified metadata, not
kernel proof terms.

## Common source and target

The source is Riemann's completed function

```text
xi(s) = 1/2 s(s-1) pi^(-s/2) Gamma(s/2) zeta(s).
```

Both active routes terminate at the identical typed node `LiSequence`, with
index convention `n>=1`.

### Route A: zeros / Hadamard viewpoint

```text
XiFunction -> XiZeros -> LiSequence
```

Taking the zero multiset is classified as information loss. Reconstruction
requires normalization, order/growth facts, exponential factors, and analytic
hypotheses for Hadamard factorization; none is silently assumed.

The zero formula is registered as

```text
lambda_n = sum_rho [1 - (1 - 1/rho)^n],    n >= 1,
```

with the standard limiting interpretation. Its summation prescription and
analytic justification are `LiteratureCertified`; the code does not derive
them or assume RH to make the identity valid.

### Route B: Mobius / logarithmic derivative viewpoint

```text
XiFunction -> XiAfterMobius -> LogXiMobius
           -> LiGeneratingSeries -> LiSequence
```

The registered convention is

```text
m(z)   = -z/(1-z)
phi(z) = xi(m(z))
d/dz log phi(z) = sum_{n>=1} lambda_n z^(n-1).
```

Exact rational algebra checks `m'(z)=-1/(1-z)^2`. Forming the symbolic syntax
`xi(m(z))` is finite and exact. Logarithmic differentiation of the analytic
object, domain/nonvanishing requirements, the generating identity, convergence,
and coefficient interpretation remain `LiteratureCertified`.

## Property transport and RH

Li's theorem transports

```text
all nontrivial xi zeros lie on Re(s)=1/2
```

to

```text
forall n>=1, lambda_n >= 0.
```

Both directions are literature-certified, not kernel checked. Finite positivity
computations cannot satisfy the universal quantifier.

The graph also records a literature relationship between the Li sequence and a
specified family of Weil quadratic-functional values. It does **not** assume
that the Weil form is positive. The desired forms
`lambda_n=<v_n,A v_n>` with `A>=0`, or `lambda_n=||T v_n||^2`, are research
targets. Their candidate bridge remains `Conjectural` until constructed and
proved without assuming RH.

## Status ledger

Implemented and locally kernel checked:

- normalized exact `Rational` polynomials;
- polynomial arithmetic and formal differentiation;
- rational-function quotient differentiation;
- exact cross-multiplication verification of the Mobius derivative identity.

Literature certified only:

- xi/nontrivial-zero correspondence and RH/Xi-real-zero equivalence;
- analytic logarithmic-derivative Li generating identity;
- zero-sum formula for Li coefficients and Li positivity criterion;
- Nyman–Beurling and Lagarias equivalences;
- registered Li/Weil correspondence;
- hypotheses needed for zero products and Taylor reconstruction.

Conjectural or unconstructed:

- a positive Gram/norm-square factorization proving all Li coefficients
  nonnegative;
- a self-adjoint Hilbert–Pólya operator with exactly the required spectrum;
- a bridge unifying Li/Weil positivity with Nyman–Beurling geometry.

## Next mathematical bottleneck

The immediate bottleneck is a certified, non-circular universal positivity
theorem for the entire `LiSequence` (or corresponding Weil test-function
family). It must validate every analytic interchange and infinite sum without
importing RH. Only kernel-checked proofs of that theorem and Li's equivalence
could make this corridor part of a submission-grade RH proof.
