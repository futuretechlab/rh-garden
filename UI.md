# RH Garden Navigator

The Navigator is a local research instrument for seeing the theorem graph and
the current Suzuki configuration space. It is not a proof checker and is not
mathematical evidence.

## Architecture and data flow

The frontend is React 18 with TypeScript and Vite. Its plots and graph are
small native SVG components, keeping the v1 dependency surface limited. The
Haskell command

```text
cabal run rh-garden -- ui-export
```

serializes live project state into:

```text
ui/public/data/garden.json
ui/public/data/frontiers.json
ui/public/data/status.json
ui/public/data/explorer-summary.json
```

`garden.json` is generated from the typed criterion and representation
registries; the frontend never scrapes terminal text. `frontiers.json`
identifies the exact open proposition, blocker, source modules, and candidate
approaches. `explorer-summary.json` contains bounded, reproducible numerical
field/block/root/busy-period scans. `status.json` carries the Git snapshot and
the explicit negative-submission state. Build and test results remain marked
`not_checked_by_export`: the exporter does not infer successful validation.

## Trust model

Every node and edge has a textual badge and icon as well as a color. Proof
Mode retains `LeanChecked` and exact tooling layers while suppressing or
desaturating numerical exploration. Exploration Mode shows all layers.
`NumericalEvidence` never becomes `LeanChecked` through export, display, or a
candidate certificate. The only promotion route is an independent Lean proof
accepted by the kernel.

## Views

- Garden Map: pan/zoom graph, district and trust filters, node inspector, and
  directed route finder with Lean-only, literature, and exploration modes.
- Frontier Cockpit: exact blockers, known theorem chains, source modules, and
  the measured mismatch between local arrivals and global-prefix bounds.
- Suzuki Field: sampled `Psi_omega(t)` with numerical trust warning.
- Mangoldt Blocks: event intervals, arithmetic state, optimizer type, and
  margins.
- Root Discrepancy: linked `D(u)` sawtooth and `Psi(2 log u)`, negative-area
  shading, event impulses, and clickable busy-period diagnostics.
- State Space: phase portraits for margin, discrepancy, reserve, backlog, and
  arrival/service behavior.
- Certificates: candidate, failed, and formal certificate lanes; only actual
  registry entries are labelled checked.

- Arithmetic Frontier: a clickable `thetaEff` versus prefix-envelope-slack
  scatter, reference regimes at `1/2`, `17/30`, `3/5`, and `2/3`, and a
  synchronized busy-period inspector. The `17/30` background is explicitly
  `LiteratureCertified` context; it is not a formal or effective theorem in
  this project.

The arrival gauge compares exact terminal arrival, the largest terminal
proxy compatible with the scalar verifier, and the LeanChecked local-width
upper bound. It also reports the much coarser pinned global-prefix expression.
The selected period exposes the observed maximum prefix excess and whether
the constant envelope itself fails. Terminal `epsilonRequired` and the
stronger prefix-relative slack are displayed separately. In the failure case
the cockpit points to
`SuzukiWeightedShortIntervalProfileBound` and
`busyPeriod_safe_of_weightedMangoldt_profile`.

The busy-period inspector now plots the exact arrival/service excess beside
the transformed Chebyshev remainder, the explicit archimedean defect, and the
resulting backlog.  It also displays the regression residual and the
anchored `U_m(x)=R(m)+epsilon*(x-m)` required/budget comparison.  The formal cockpit anchor is
`arrivalServiceExcess_eq_chebyshevError` followed by
`busyPeriod_safe_of_chebyshev_error_profile`; all plotted values and envelope
budgets remain visibly `NumericalEvidence`.

The inspector also exposes the finite-event verifier. Every displayed event
cell reports its exact-service cutoff cost, conservative `5/3` linear-service
cost, cumulative cost, and remaining reserve. Explorer event samples are
rounded upward by `0.001`; this is a numerical candidate coarsening, not a
Lean proof of the corresponding arithmetic bound. The checked interface is
`SuzukiFiniteEventProfileCertificate.psiRoot_nonnegative`: it consumes a
complete finite prime-power chain, finitely many proved event inequalities,
a proved starting reserve, and one finite total-cost inequality.

Proof Mode marks `[0,log 3]` as finite LeanChecked coverage, combining the
nine-term initial-interval certificate with the certified second prime cell.
The interval beyond `log 3` and every universal tail claim remain open.

The exported UI data deliberately uses two scan sizes: a smaller full event
trace for responsive sawtooth inspection and a ten-million-period summary for
the arithmetic scatter and frontier rankings. Both remain
`NumericalEvidence`.

## Development

From the repository root on Windows:

```powershell
./scripts/start-ui.ps1
```

Or run the steps separately:

```text
cabal run rh-garden -- ui-export
cd ui
npm install
npm run typecheck
npm run dev
npm run build
```

The generated snapshot is deliberately explicit about its source commit.
Refresh it before relying on the displayed project state.
