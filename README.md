# RH Garden

`rh-garden` is a typed graph and proof-search scaffold for research on the
Riemann Hypothesis (RH). **This project does not prove RH.** A proof may be
claimed only when the repository contains a finite, auditable, kernel-checkable
proof term whose dependencies are also kernel checked. No such term exists.

## Architecture

The program keeps four domains separate:

1. `RHGarden.Core` models propositions/proof obligations such as RH, Li
   positivity, Nyman–Beurling density, the Lagarias inequality, and a
   self-adjoint Xi realization. `Reduction a b` means “replace obligation `a`
   by obligation `b`.” Thus `XiZerosReal -> SelfAdjointXiRealization` is a
   sufficient goal reduction; it does **not** assert that real Xi zeros
   construct an operator.
2. `RHGarden.Representation` models data/description forms independently:
   `XiFunction`, `XiZeros`, `MobiusVariable`, `XiAfterMobius`, `LogXiMobius`,
   `LiGeneratingSeries`, `LiSequence`, `WeilLiQuadraticValues`, and the
   zero-side Suzuki screw-function representations.
3. `RHGarden.Algebra` and `RHGarden.Mobius` implement a small exact algebra
   checker over `Rational`. It does not evaluate xi or zeta.
4. `RHGarden.Evidence` contains finite floating-point experiments. It exports
   no conversion to the opaque `Proof` type.

Representation edges classify their semantics as `ExactRepresentation`,
`EquivalentTheorem`, `SufficientReduction`, `InformationLoss`, or
`ConjecturalBridge`. Each edge also records trust, cost, provenance, transform,
reconstruction information, and optional property transport. Li's criterion is
recorded as transport between “all nontrivial zeros lie on the critical line”
and `forall n>=1, lambda_n>=0`, rather than unexplained graph text.

Trust is independent of edge kind:

- `LeanChecked`: a named theorem is implemented under `formal/` and accepted
  by Lean's kernel with mathlib dependencies.
- `ExactExecutable`: a finite exact Haskell calculation checks an identity,
  but Haskell is not the submission proof kernel.
- `LiteratureCertified`: cited mathematics not yet formalized here.
- `Conjectural`: a research hypothesis or proposed bridge.

`KernelMode` admits only `LeanChecked` edges. `LiteratureMode` additionally
admits `ExactExecutable` and `LiteratureCertified`; `ExplorationMode` also
admits `Conjectural`. A Haskell trust label or theorem-name string is navigation
metadata only: the Lean source and a successful `lake build` are authoritative.
Cost-minimizing search exists separately for proof obligations and
representations.

## Exact algebra currently checked

Polynomials have normalized ascending rational coefficients and exact addition,
multiplication, scalar multiplication, and differentiation. Rational functions
have quotient-rule differentiation and equality by cross multiplication.
`check-mobius` constructs `m(z)=-z/(1-z)` and checks exactly that
`m'(z)=-1/(1-z)^2`.

Only this finite rational-function identity is `ExactExecutable`. No analytic
statement about xi, zeta, zeros, Taylor convergence, or Li coefficients follows
from that certificate. The checked analytic and representation theorems are
listed in `formal/README.md`.

## Build and commands

```bash
cabal build
cabal test
cabal run rh-garden -- routes
cabal run rh-garden -- explore
cabal run rh-garden -- kernel
cabal run rh-garden -- garden
cabal run rh-garden -- path XiFunction LiSequence
cabal run rh-garden -- check-mobius
cabal run rh-garden -- check-lagarias 10000
cabal run rh-garden -- submission
cabal run rh-garden -- formal-status
cabal run rh-garden -- ui-export

cd formal
lake build

cd ../ui
npm install
npm run dev
```

`garden` prints both registered routes to the same `LiSequence` node.
`formal-status` reports static theorem-name metadata and explicitly does not
perform proof validation.

## RH Garden Navigator

The Navigator under `ui/` is a React/TypeScript/Vite research instrument fed
by the real Haskell registry and bounded Suzuki Explorer scans. Refresh its
four versioned JSON inputs with `cabal run rh-garden -- ui-export`, then run
`npm run dev` from `ui/` (or use `scripts/start-ui.ps1` on Windows). It offers
the theorem Garden Map and route finder, active-frontier cards, Suzuki field
and Mangoldt-block views, linked root-discrepancy/busy-period plots, phase
portraits, and a certificate workbench.

Proof Mode hides or desaturates numerical layers; Exploration Mode exposes
them with textual `NumericalEvidence` labels. The UI and its JSON are tooling,
not mathematical evidence, and never promote Explorer output to
`LeanChecked`. See `UI.md` for architecture and the trust boundary.

The Navigator's Arithmetic Frontier view uses a ten-million-range busy-period
summary. It shows effective interval exponents, the external Guth--Maynard
`17/30` reference scale, the LeanChecked local-width bound, and the exact
profile-valued formal target. Literature shading and finite scans remain
visibly separate from kernel-checked implications.

The formal graph now includes Lean-checked equivalences between mathlib's RH,
the entire-xi zero formulation, and the `XiT` real-coordinate formulation.
These are equivalences between open propositions, not proofs of either endpoint;
route discovery never marks a terminal obligation as discharged.

The Li district now has a Lean-checked local analytic realization of the
derivative-defined xi Taylor data, kept explicitly separate from the bare
`PowerSeries` algebra object. The correspondence between analytic FMS
composition and `PowerSeries.subst` remains an open interoperability lemma, but
no longer blocks the certified route: Lean composes the analytic FMS germs,
uses uniqueness, and adapts their coefficients to the authoritative
`PowerSeries`. Identification with independently defined classical Li
coefficients remains unformalized. Li's positivity
criterion remains literature-certified.
`check-lagarias` is finite floating-point evidence and can neither construct
`Proof RH` nor discharge the universal theorem. `submission` stays negative
unless a genuine kernel proof term is registered.

## Current proof obligations

The known RH equivalences (Xi real zeros, Li positivity, Nyman–Beurling, and
Lagarias) are `LiteratureCertified`, not kernel checked. The Hilbert–Pólya
realization is an unfulfilled stronger obligation. A candidate positive
Gram/norm-square factorization of Li/Weil values is explicitly `Conjectural`.

The Suzuki district now kernel-checks the occurrence-indexed zero-side series,
the screw-kernel identity, the critical-line Gram factorization, the exact xi
Nevanlinna criterion, screw continuity, and the high-strip Fourier--Laplace
transform.  Its specialized xi screw/Nevanlinna and shifted zero-free
criteria are checked without claiming the general Krein--Langer theorem.
The prime-side representation and universal strict convexity on prime cells
are also checked; `suzukiPsi_pos_cell_two` is the first exact certificate for
the actual unshifted function on a complete cell `[log 2,log 3]`.  This finite
result does not prove global positivity or RH. An Euler--Maclaurin remainder estimate proves
`riemannXi (1/2) != 0`, so every spectral denominator in the zero-side formula
is unconditionally nonzero; see `SUZUKI_SCREW.md`.

The non-negotiable invariant is that a numerical pattern, citation, symbolic
experiment, or conjectural reduction never becomes proof merely because it
would close a route.
