import { useEffect, useMemo, useRef, useState } from 'react'
import type {
  BusyPeriod, DualRow, ExplorerData, FrontierData, GardenData, GardenEdge,
  GardenNode, MangoldtBlock, StatusData, Trust,
} from './types'

type View = 'map' | 'frontier' | 'field' | 'blocks' | 'discrepancy' | 'phase' | 'certificates'
type RouteMode = 'lean' | 'literature' | 'all'

const trustMeta: Record<Trust, {label: string; icon: string}> = {
  LeanChecked: {label: 'LeanChecked', icon: '◆'},
  LiteratureCertified: {label: 'Literature', icon: '◈'},
  NumericalEvidence: {label: 'Numerical', icon: '△'},
  Conjectural: {label: 'Conjectural', icon: '◇'},
  Open: {label: 'Open', icon: '○'},
  ExactExecutable: {label: 'Executable', icon: '⬡'},
}

const views: Array<[View, string, string]> = [
  ['map', 'Garden map', '01'],
  ['frontier', 'Frontier cockpit', '02'],
  ['field', 'Suzuki field', '03'],
  ['blocks', 'Mangoldt blocks', '04'],
  ['discrepancy', 'Root discrepancy', '05'],
  ['phase', 'State space', '06'],
  ['certificates', 'Certificates', '07'],
]

export default function App() {
  const [garden, setGarden] = useState<GardenData | null>(null)
  const [frontiers, setFrontiers] = useState<FrontierData | null>(null)
  const [status, setStatus] = useState<StatusData | null>(null)
  const [explorer, setExplorer] = useState<ExplorerData | null>(null)
  const [view, setView] = useState<View>(() => {
    const requested = window.location.hash.slice(1) as View
    return views.some(([id]) => id === requested) ? requested : 'map'
  })
  const [proofMode, setProofMode] = useState(false)
  const [error, setError] = useState('')

  useEffect(() => {
    Promise.all([
      fetch('./data/garden.json').then(r => checkedJson<GardenData>(r)),
      fetch('./data/frontiers.json').then(r => checkedJson<FrontierData>(r)),
      fetch('./data/status.json').then(r => checkedJson<StatusData>(r)),
      fetch('./data/explorer-summary.json').then(r => checkedJson<ExplorerData>(r)),
    ]).then(([g, f, s, e]) => {
      setGarden(g); setFrontiers(f); setStatus(s); setExplorer(e)
    }).catch(reason => setError(String(reason)))
  }, [])

  if (error) return <div className="load-state error"><span>Export unavailable</span>{error}<code>cabal run rh-garden -- ui-export</code></div>
  if (!garden || !frontiers || !status || !explorer) return <div className="load-state"><div className="orbit" /><span>Opening the garden…</span></div>

  return <div className={`app ${proofMode ? 'proof-mode' : 'exploration-mode'}`}>
    <header className="topbar">
      <div className="brand-mark"><span>RH</span><i /></div>
      <div className="brand-copy">
        <p>RESEARCH INSTRUMENT / v0.1</p>
        <h1>Garden Navigator</h1>
      </div>
      <div className="mode-switch" role="group" aria-label="Trust overlay">
        <button className={proofMode ? 'active' : ''} onClick={() => setProofMode(true)}>Proof mode</button>
        <button className={!proofMode ? 'active' : ''} onClick={() => setProofMode(false)}>Exploration</button>
      </div>
      <div className="snapshot">
        <span className="pulse" />
        <div><small>EXPORTED SNAPSHOT</small><code>{status.snapshot_commit.slice(0, 9)}</code></div>
      </div>
    </header>

    <aside className="sidebar">
      <nav>{views.map(([id, label, number]) => <button key={id} className={view === id ? 'active' : ''} onClick={() => {setView(id); window.location.hash = id}}><span>{number}</span>{label}</button>)}</nav>
      <div className="trust-legend">
        <p>EPISTEMIC LAYERS</p>
        {(Object.keys(trustMeta) as Trust[]).map(trust => <div key={trust} className={`trust ${trust}`}><i>{trustMeta[trust].icon}</i>{trustMeta[trust].label}</div>)}
      </div>
      <div className="submission-seal"><span>SUBMISSION</span><strong>NEGATIVE</strong><small>No proof of RH is claimed</small></div>
    </aside>

    <main>
      {view === 'map' && <GardenMap data={garden} proofMode={proofMode} />}
      {view === 'frontier' && <FrontierCockpit data={frontiers} explorer={explorer} />}
      {view === 'field' && <SuzukiField explorer={explorer} proofMode={proofMode} />}
      {view === 'blocks' && <BlockMap blocks={explorer.busy.mangoldt_blocks} proofMode={proofMode} />}
      {view === 'discrepancy' && <DiscrepancyView explorer={explorer} proofMode={proofMode} />}
      {view === 'phase' && <PhaseView rows={explorer.busy.dual_dynamics} proofMode={proofMode} />}
      {view === 'certificates' && <CertificateWorkbench busy={explorer.busy.busy_periods} />}
    </main>

    <StatusRail status={status} />
  </div>
}

async function checkedJson<T>(response: Response): Promise<T> {
  if (!response.ok) throw new Error(`${response.url}: ${response.status}`)
  return response.json() as Promise<T>
}

function GardenMap({data, proofMode}: {data: GardenData; proofMode: boolean}) {
  const [selected, setSelected] = useState<GardenNode | null>(null)
  const [query, setQuery] = useState('')
  const [district, setDistrict] = useState('All districts')
  const [routeFrom, setRouteFrom] = useState('representation:XiFunction')
  const [routeTo, setRouteTo] = useState('representation:SuzukiBusyPeriodLoss')
  const [routeMode, setRouteMode] = useState<RouteMode>('lean')
  const [camera, setCamera] = useState({x: 0, y: 0, zoom: .68})
  const drag = useRef<{x: number; y: number; cx: number; cy: number} | null>(null)
  const districts = useMemo(() => ['All districts', ...Array.from(new Set(data.nodes.map(n => n.district)))], [data])
  const positions = useMemo(() => layoutNodes(data.nodes), [data.nodes])
  const route = useMemo(() => findRoute(data.edges, routeFrom, routeTo, routeMode), [data.edges, routeFrom, routeTo, routeMode])
  const routeEdgeIds = new Set(route.map(e => e.id))
  const routeNodeIds = new Set([routeFrom, routeTo, ...route.flatMap(e => [e.source, e.target])])
  const q = query.toLowerCase()
  const visibleNodes = data.nodes.filter(node =>
    (district === 'All districts' || node.district === district) &&
    (!q || `${node.display_name} ${node.theorem_names.join(' ')}`.toLowerCase().includes(q)) &&
    (!proofMode || node.trust === 'LeanChecked' || node.trust === 'ExactExecutable'))
  const visibleIds = new Set(visibleNodes.map(n => n.id))
  const visibleEdges = data.edges.filter(edge => visibleIds.has(edge.source) && visibleIds.has(edge.target) &&
    (!proofMode || edge.trust === 'LeanChecked' || edge.trust === 'ExactExecutable'))

  return <section className="screen graph-screen">
    <ScreenHeading eyebrow="LIVE REPRESENTATION GRAPH" title="The garden, as routes rather than a list" blurb="Every bridge carries its own trust class. Search, route, and inspect without collapsing equivalence into proof." />
    <div className="graph-toolbar">
      <label><span>Search</span><input value={query} onChange={e => setQuery(e.target.value)} placeholder="theorem or representation" /></label>
      <label><span>District</span><select value={district} onChange={e => setDistrict(e.target.value)}>{districts.map(x => <option key={x}>{x}</option>)}</select></label>
      <button onClick={() => setCamera({x: 0, y: 0, zoom: .68})}>Reset view</button>
      <div className="graph-count">{visibleNodes.length} nodes · {visibleEdges.length} bridges</div>
    </div>
    <div className="graph-workspace">
      <div className="graph-canvas"
        onWheel={event => {event.preventDefault(); setCamera(c => ({...c, zoom: clamp(c.zoom * (event.deltaY > 0 ? .9 : 1.1), .28, 1.8)}))}}
        onPointerDown={event => {drag.current = {x: event.clientX, y: event.clientY, cx: camera.x, cy: camera.y}; (event.currentTarget as HTMLElement).setPointerCapture(event.pointerId)}}
        onPointerMove={event => {if (drag.current) setCamera(c => ({...c, x: drag.current!.cx + event.clientX - drag.current!.x, y: drag.current!.cy + event.clientY - drag.current!.y}))}}
        onPointerUp={() => {drag.current = null}}>
        <svg viewBox="0 0 1900 1300" style={{transform: `translate(${camera.x}px, ${camera.y}px) scale(${camera.zoom})`}}>
          <defs><filter id="glow"><feGaussianBlur stdDeviation="3" result="b"/><feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge></filter></defs>
          {visibleEdges.map(edge => {
            const a = positions.get(edge.source), b = positions.get(edge.target); if (!a || !b) return null
            const hot = routeEdgeIds.has(edge.id) || selected?.id === edge.source || selected?.id === edge.target
            return <g key={edge.id} className={`edge ${edge.trust} ${hot ? 'hot' : ''}`}><line x1={a.x} y1={a.y} x2={b.x} y2={b.y}/><circle cx={b.x} cy={b.y} r={hot ? 4 : 2}/></g>
          })}
          {visibleNodes.map(node => {
            const p = positions.get(node.id)!; const hot = routeNodeIds.has(node.id) || selected?.id === node.id
            return <g key={node.id} transform={`translate(${p.x - 74} ${p.y - 27})`} className={`map-node ${node.trust} ${hot ? 'hot' : ''}`} onClick={event => {event.stopPropagation(); setSelected(node)}}>
              <rect width="148" height="54" rx="4"/><text className="node-icon" x="10" y="18">{trustMeta[node.trust].icon}</text><text x="27" y="18">{truncate(node.display_name, 22)}</text><text className="node-district" x="10" y="39">{node.district.toUpperCase()}</text>{node.rh_equivalent && <text className="rh-mark" x="137" y="42">RH↔</text>}
            </g>
          })}
        </svg>
        <div className="canvas-caption">DRAG TO PAN · WHEEL TO ZOOM · CLICK TO INSPECT</div>
      </div>
      <NodeInspector node={selected} edges={data.edges} nodes={data.nodes} />
    </div>
    <div className="route-finder panel">
      <div><small>ROUTE FINDER</small><h3>{route.length ? `${route.length} bridges` : 'No admissible directed route'}</h3></div>
      <select value={routeFrom} onChange={e => setRouteFrom(e.target.value)}>{data.nodes.map(n => <option value={n.id} key={n.id}>{n.display_name}</option>)}</select>
      <span className="route-arrow">→</span>
      <select value={routeTo} onChange={e => setRouteTo(e.target.value)}>{data.nodes.map(n => <option value={n.id} key={n.id}>{n.display_name}</option>)}</select>
      <select value={routeMode} onChange={e => setRouteMode(e.target.value as RouteMode)}><option value="lean">LeanChecked only</option><option value="literature">Literature allowed</option><option value="all">Include exploration</option></select>
      <div className="route-steps">{route.map((edge, i) => <span key={edge.id} className={edge.trust}><b>{i + 1}</b>{edge.theorem_name || edge.relation_type}</span>)}</div>
    </div>
  </section>
}

function NodeInspector({node, edges, nodes}: {node: GardenNode | null; edges: GardenEdge[]; nodes: GardenNode[]}) {
  if (!node) return <aside className="inspector empty"><div className="sigil">✦</div><h3>Select a node</h3><p>The formal object, provenance, incoming and outgoing transformations will appear here.</p></aside>
  const inbound = edges.filter(e => e.target === node.id), outbound = edges.filter(e => e.source === node.id)
  const name = (id: string) => nodes.find(n => n.id === id)?.display_name ?? id
  return <aside className="inspector">
    <TrustBadge trust={node.trust}/><p className="mono-id">{node.id}</p><h2>{node.display_name}</h2>
    {node.rh_equivalent && <div className="rh-equivalent">RH-EQUIVALENT REPRESENTATION <b>≠ PROVED</b></div>}
    <p>{node.description}</p>
    <h4>Formal anchors</h4>{node.theorem_names.length ? node.theorem_names.map(t => <code key={t}>{t}</code>) : <span className="muted">No theorem attached to this node.</span>}
    <h4>Source</h4>{node.source_files.map(file => <span className="source" key={file}>{file}</span>)}
    <h4>Inbound / outbound</h4>
    <div className="edge-list">{[...inbound, ...outbound].slice(0, 10).map(edge => <div key={edge.id}><TrustBadge trust={edge.trust}/><span>{edge.source === node.id ? '→' : '←'} {truncate(name(edge.source === node.id ? edge.target : edge.source), 32)}</span><small>{edge.relation_type}</small></div>)}</div>
  </aside>
}

function FrontierCockpit({data, explorer}: {data: FrontierData; explorer: ExplorerData}) {
  const periods = explorer.busy.busy_periods
  const comparable = periods.filter((period): period is BusyPeriod & {pinned_bound_over_arrival: number} =>
    period.arrival_mass > 1e-12 && period.pinned_bound_over_arrival !== null &&
      Number.isFinite(period.pinned_bound_over_arrival))
  const tightest = comparable.length ? [...comparable].sort((a,b) =>
    a.pinned_bound_over_arrival - b.pinned_bound_over_arrival)[0] : null
  return <section className="screen">
    <ScreenHeading eyebrow="OPEN MATHEMATICS / EXACTLY LOCATED" title="Frontier cockpit" blurb="The first missing inequality is displayed as a mathematical interface, not hidden behind a project-status label." />
    <div className="frontier-grid">{data.frontiers.map((frontier, index) => <article className={`frontier-card ${index === 0 ? 'headline' : ''}`} key={frontier.id}>
      <div className="card-index">F{String(index + 1).padStart(2, '0')}</div><TrustBadge trust={frontier.trust}/><h2>{frontier.title}</h2><span className="category">{frontier.category}</span>
      <div className="chain"><small>CHECKED APPROACH</small><p>{frontier.known_chain}</p></div>
      <div className="blocker"><small>FIRST OPEN BRIDGE</small><p>{frontier.exact_blocker}</p></div>
      <div className="bound"><small>CURRENT BOUND</small><p>{frontier.current_bound}</p></div>
      <div className="tags">{frontier.candidate_approaches.map(x => <span key={x}>{x}</span>)}</div>
    </article>)}</div>
    {tightest && <div className="metric-band panel"><div><small>PINNED PREFIX BOUND / ACTUAL ARRIVAL</small><strong>{format(tightest.pinned_bound_over_arrival)}×</strong></div><p>Even the tightest interval in this exported scan inherits a global-prefix bound this much larger than its actual local arrival. The issue is structural: the theorem discards the starting prefix.</p><div><small>AT BUSY PERIOD</small><strong>{tightest.start_event} → {tightest.recovery_before_event}</strong></div></div>}
    <MilestoneStrip />
  </section>
}

function SuzukiField({explorer, proofMode}: {explorer: ExplorerData; proofMode: boolean}) {
  const omegas = Array.from(new Set(explorer.field_samples.map(x => x.omega)))
  const [omega, setOmega] = useState(omegas[0] ?? 0)
  const points = explorer.field_samples.filter(x => x.omega === omega).map(x => ({x: x.t, y: x.psi}))
  const minima = explorer.scan.cell_minima.filter(x => x.omega === omega).sort((a,b) => a.minimum_candidate - b.minimum_candidate).slice(0, 8)
  return <section className="screen">
    <ScreenHeading eyebrow="SUZUKI FIELD / (ω,t)" title="Watch the arithmetic landscape move" blurb="The plotted samples are generated by the Haskell evaluator and remain NumericalEvidence. Certified regions are annotated separately." />
    <NumericalBanner hidden={proofMode}/>
    <div className="control-ribbon"><label>ω<select value={omega} onChange={e => setOmega(Number(e.target.value))}>{omegas.map(x => <option value={x} key={x}>{x}</option>)}</select></label><span>Prime-side + Volterra evaluator</span><span>t ∈ [0, 7]</span></div>
    {proofMode ? <ProofModeVeil title="Numerical field hidden"><p>Proof Mode preserves the exact representation and certified intervals, while hiding sampled values.</p><div className="certified-range"><b>[log 2, log 3]</b><span>strictly positive · LeanChecked</span></div></ProofModeVeil> : <>
      <div className="chart-panel panel"><Chart series={[{name: `Ψ_${omega}(t)`, color: '#f2bc57', points}]} zeroLine certified={[Math.log(2), Math.log(3)]}/><div className="chart-label left">Ψω(t)</div><div className="chart-label bottom">t →</div></div>
      <div className="minima-grid">{minima.map(row => <div key={row.prime_cell}><small>CELL {row.prime_cell}</small><strong>{format(row.minimum_candidate)}</strong><span>t* {format(row.minimizing_t_candidate)}</span><i>κ {format(row.second_derivative)}</i></div>)}</div>
    </>}
  </section>
}

function BlockMap({blocks, proofMode}: {blocks: MangoldtBlock[]; proofMode: boolean}) {
  const rows = [...blocks].sort((a,b) => a.block_margin - b.block_margin).slice(0, 80)
  const [selected, setSelected] = useState<MangoldtBlock | null>(rows[0] ?? null)
  return <section className="screen">
    <ScreenHeading eyebrow="CONSTANT ARITHMETIC STATE" title="Mangoldt block map" blurb="Between consecutive prime-power events, the complete arithmetic state is only (S,C); the archimedean curve supplies the unique minimum." />
    <NumericalBanner hidden={proofMode}/>
    {proofMode ? <ProofModeVeil title="Block geometry remains"><p>State constancy, strict convexity, and scalar margin equivalence are LeanChecked. Candidate margins are hidden.</p></ProofModeVeil> : <div className="block-layout">
      <div className="block-river panel">{rows.map(block => <button key={block.event_q} className={`${block.slope_deficit_left < 0 && block.slope_deficit_right > 0 ? 'active-block' : ''} ${selected?.event_q === block.event_q ? 'selected' : ''}`} style={{flexGrow: Math.max(1, Math.sqrt(block.gap))}} onClick={() => setSelected(block)}><span>{block.event_q}</span><i /><span>{block.next_event_r}</span><small>{format(block.block_margin)}</small></button>)}</div>
      {selected && <div className="block-inspector panel"><small>BLOCK {selected.event_q} → {selected.next_event_r}</small><h2>{selected.minimizer_type} optimizer</h2><Metric label="margin" value={format(selected.block_margin)}/><Metric label="state slope S" value={format(selected.slope_S_q)}/><Metric label="state intercept C" value={format(selected.intercept_C_q)}/><Metric label="exp(t*)" value={format(selected.exp_minimizing_t_candidate)}/><Metric label="integer cell" value={String(selected.winning_integer_cell)}/><p>Λ is zero in the interior. The same strictly convex function spans all {selected.gap - 1} intervening integers.</p></div>}
      <div className="data-table panel"><div className="table-head"><span>q → r</span><span>gap</span><span>margin</span><span>optimizer</span><span>cell</span></div>{rows.slice(0, 24).map(row => <button key={row.event_q} onClick={() => setSelected(row)}><span>{row.event_q} → {row.next_event_r}</span><span>{row.gap}</span><span>{format(row.block_margin)}</span><span>{row.minimizer_type}</span><span>{row.winning_integer_cell}</span></button>)}</div>
    </div>}
  </section>
}

function DiscrepancyView({explorer, proofMode}: {explorer: ExplorerData; proofMode: boolean}) {
  const periods = [...explorer.busy.busy_periods].sort((a,b) => b.loss_over_reserve - a.loss_over_reserve)
  const [period, setPeriod] = useState<BusyPeriod | null>(periods[0] ?? null)
  const allRows = explorer.busy.dual_dynamics
  const rows = period ? allRows.filter(row => row.sqrt_next_event >= period.root_start - .2 && row.sqrt_event <= period.root_end + .2) : allRows.slice(0, 120)
  const dPoints = rows.flatMap(row => [{x: row.sqrt_event, y: row.event_slope_deficit}, {x: row.sqrt_next_event, y: row.event_slope_deficit + row.archimedean_drift}])
  const psiPoints = rows.flatMap(row => [{x: row.sqrt_event, y: row.event_value}, {x: row.root_optimizer_before, y: row.block_margin}]).sort((a,b) => a.x - b.x)
  return <section className="screen">
    <ScreenHeading eyebrow="D(u) = SMOOTH SERVICE − ARITHMETIC ARRIVAL" title="Root discrepancy sawtooth" blurb="Rising service curves are interrupted by Mangoldt impulses. The aligned lower trace shows exactly how a negative excursion consumes Ψ reserve." />
    <NumericalBanner hidden={proofMode}/>
    {proofMode ? <ProofModeVeil title="Exact identities remain visible"><div className="formula-stack"><code>D′(u) = 2 F(u),  5/3 ≤ D′(u) &lt; 2</code><code>H′(u) = 2 D(u)/u</code><code>Loss[a,b] = ∫ 2 max(−D(u),0)/u du</code></div></ProofModeVeil> : <div className="discrepancy-layout">
      <div className="linked-charts">
        <div className="panel chart-panel saw"><Chart series={[{name: 'D(u)', color: '#52e0bb', points: dPoints}]} zeroLine highlight={period ? [period.root_start, period.root_end] : undefined}/><span className="plot-title">ROOT SLOPE DISCREPANCY D(u)</span></div>
        <div className="panel chart-panel psi"><Chart series={[{name: 'Ψ(2 log u)', color: '#f2bc57', points: psiPoints}]} zeroLine highlight={period ? [period.root_start, period.root_end] : undefined}/><span className="plot-title">RESERVE Ψ(2 LOG u)</span></div>
      </div>
      <BusyInspector period={period}/>
      <div className="busy-list panel"><div className="table-head"><span>start → recovery</span><span>events</span><span>loss / reserve</span><span>arrival / service</span></div>{periods.slice(0, 18).map(row => <button className={period?.start_event === row.start_event ? 'selected' : ''} key={row.start_event} onClick={() => setPeriod(row)}><span>{row.start_event} → {row.recovery_before_event}</span><span>{row.event_count}</span><span>{format(row.loss_over_reserve)}</span><span>{format(row.arrival_over_service)}</span></button>)}</div>
    </div>}
  </section>
}

function BusyInspector({period}: {period: BusyPeriod | null}) {
  if (!period) return null
  return <aside className="busy-inspector panel"><small>NEGATIVE EXCURSION</small><h2>{period.start_event} → {period.recovery_before_event}</h2><div className="reserve-gauge"><i style={{width: `${Math.min(100, period.loss_over_reserve * 100)}%`}}/><span>{format(period.loss_over_reserve * 100)}% reserve consumed</span></div><Metric label="event states" value={String(period.event_count)}/><Metric label="root width" value={format(period.root_width)}/><Metric label="start reserve" value={format(period.psi_start)}/><Metric label="weighted loss" value={format(period.weighted_loss)}/><Metric label="minimum Ψ" value={format(period.minimum_psi)}/><Metric label="maximum backlog" value={format(-period.most_negative_discrepancy)}/><Metric label="arrival / service" value={format(period.arrival_over_service)}/><div className="bound-warning"><small>PINNED GLOBAL PREFIX BOUND</small><strong>{format(period.pinned_prefix_arrival_upper)} arrival units</strong><p>{period.arrival_mass > 1e-12 ? `${format(period.pinned_bound_over_arrival)}× actual interval arrival.` : 'No internal impulse: a prefix estimate still ignores the interval geometry.'}</p></div></aside>
}

function PhaseView({rows, proofMode}: {rows: DualRow[]; proofMode: boolean}) {
  const data = rows.slice(0, 10000)
  const portraits = [
    {title: 'Margin vs discrepancy', x: (r: DualRow) => r.event_slope_deficit, y: (r: DualRow) => r.global_dual_margin, xl: 'd_q', yl: 'M_q'},
    {title: 'Root ratio vs event scale', x: (r: DualRow) => Math.log(r.event_q), y: (r: DualRow) => r.root_ratio, xl: 'log q', yl: 'ρ_q'},
    {title: 'Reserve vs backlog', x: (r: DualRow) => Math.max(-r.event_slope_deficit, 0), y: (r: DualRow) => r.event_value, xl: 'backlog', yl: 'B_q'},
  ]
  const [portrait, setPortrait] = useState(0)
  const p = portraits[portrait]
  const points = data.map(r => ({x: p.x(r), y: p.y(r)}))
  return <section className="screen">
    <ScreenHeading eyebrow="NUMERICAL STATE SPACE" title="Phase portraits without a fitted story" blurb="Low-complexity coordinates only. These plots are for discovering candidate invariants, never for certifying them." />
    <NumericalBanner hidden={proofMode}/>
    {proofMode ? <ProofModeVeil title="Exploratory phase portraits hidden"><p>No sampled state-space cloud is mathematical evidence. Switch to Exploration Mode to inspect it.</p></ProofModeVeil> : <><div className="portrait-tabs">{portraits.map((x,i) => <button key={x.title} className={portrait === i ? 'active' : ''} onClick={() => setPortrait(i)}>{x.title}</button>)}</div><div className="panel chart-panel phase-chart"><Scatter points={points}/><span className="axis-label y">{p.yl}</span><span className="axis-label x">{p.xl}</span></div><div className="phase-note"><b>{data.length.toLocaleString()}</b> event states in this view <span>•</span> color-free trust badge: <TrustBadge trust="NumericalEvidence"/></div></>}
  </section>
}

function CertificateWorkbench({busy}: {busy: BusyPeriod[]}) {
  const candidates = [...busy].sort((a,b) => b.loss_over_reserve - a.loss_over_reserve).slice(0, 8)
  return <section className="screen">
    <ScreenHeading eyebrow="DISCOVERY → RATIONALIZATION → KERNEL" title="Certificate workbench" blurb="A candidate becomes evidence only after every bound field is inhabited by an independent Lean proof." />
    <div className="pipeline"><div><span>01</span><b>Explorer</b><small>floating candidate</small></div><i>→</i><div><span>02</span><b>Exact bounds</b><small>rational / algebraic</small></div><i>→</i><div><span>03</span><b>Lean verifier</b><small>kernel checked</small></div></div>
    <div className="certificate-grid">
      <article className="certificate formal"><TrustBadge trust="LeanChecked"/><h2>Prime cell 2</h2><code>suzukiPsi_pos_cell_two</code><p>Ψ(t) &gt; 0 on [log 2, log 3]. This is finite certified coverage, not a tail theorem.</p><div className="certificate-margin">COMPLETE CELL <strong>✓</strong></div></article>
      <article className="certificate formal"><TrustBadge trust="LeanChecked"/><h2>Busy-period verifier</h2><code>SuzukiBusyPeriodCertificate.psiRoot_nonnegative</code><p>Reserve lower bound + excursion loss upper bound + exact ordering imply ΨRoot ≥ 0 throughout the interval.</p><div className="certificate-margin">INTERFACE <strong>READY</strong></div></article>
      {candidates.map(candidate => <article className="certificate candidate" key={candidate.start_event}><TrustBadge trust="NumericalEvidence"/><h2>{candidate.start_event} → {candidate.recovery_before_event}</h2><p>{candidate.event_count} event states · proposed exact loss envelope still missing.</p><Metric label="reserve" value={format(candidate.psi_start)}/><Metric label="loss" value={format(candidate.weighted_loss)}/><Metric label="candidate slack" value={format(candidate.psi_start - candidate.weighted_loss)}/><div className="certificate-margin">STATUS <strong>CANDIDATE</strong></div></article>)}
    </div>
    <div className="tail-strip"><span>FINITE CERTIFIED COVERAGE</span><b>[log 2, log 3]</b><i /><span>UNCERTIFIED TAIL</span><b>[log 3, ∞)</b></div>
  </section>
}

function StatusRail({status}: {status: StatusData}) {
  return <footer className="status-rail"><div><span>HEAD SNAPSHOT</span><code>{status.snapshot_commit.slice(0, 12)}</code></div><div><span>LEAN EXPORT FLAG</span><b>{status.formal_build}</b></div><div><span>CABAL EXPORT FLAG</span><b>{status.cabal_test}</b></div><div><span>CHECKED EDGES</span><b>{status.counts.lean_checked_edges ?? 0}</b></div><div className="submission"><span>TRUST BOUNDARY</span><b>{status.submission}</b></div></footer>
}

function ScreenHeading({eyebrow, title, blurb}: {eyebrow: string; title: string; blurb: string}) {
  return <div className="screen-heading"><div><p>{eyebrow}</p><h2>{title}</h2></div><span>{blurb}</span></div>
}

function NumericalBanner({hidden}: {hidden: boolean}) { return hidden ? null : <div className="numerical-banner"><b>△ NUMERICAL EVIDENCE</b><span>Finite sampled output. Not a proof and not sufficient evidence for RH.</span></div> }
function TrustBadge({trust}: {trust: Trust}) { return <span className={`trust-badge ${trust}`}>{trustMeta[trust].icon} {trustMeta[trust].label}</span> }
function Metric({label, value}: {label: string; value: string}) { return <div className="metric"><span>{label}</span><b>{value}</b></div> }
function ProofModeVeil({title, children}: {title: string; children: React.ReactNode}) { return <div className="proof-veil panel"><div className="shield">◆</div><small>PROOF MODE</small><h2>{title}</h2>{children}</div> }

function MilestoneStrip() { return <div className="milestones"><div><span>01</span><b>Shift semigroup</b><small>LeanChecked</small></div><div><span>02</span><b>Shifted criterion</b><small>LeanChecked</small></div><div><span>03</span><b>Prime-cell convexity</b><small>LeanChecked</small></div><div><span>04</span><b>Root discrepancy</b><small>LeanChecked</small></div><div className="open"><span>05</span><b>Busy-period bound</b><small>OPEN</small></div></div> }

interface Point {x: number; y: number}
function Chart({series, zeroLine, highlight, certified}: {series: Array<{name: string; color: string; points: Point[]}>; zeroLine?: boolean; highlight?: [number, number]; certified?: [number, number]}) {
  const all = series.flatMap(s => s.points).filter(p => Number.isFinite(p.x) && Number.isFinite(p.y))
  if (!all.length) return <div className="empty-chart">No exported points in range.</div>
  const xs = all.map(p => p.x), ys = all.map(p => p.y), xmin = Math.min(...xs), xmax = Math.max(...xs), ymin0 = Math.min(...ys), ymax0 = Math.max(...ys)
  const padY = Math.max((ymax0 - ymin0) * .12, .001), ymin = ymin0 - padY, ymax = ymax0 + padY
  const sx = (x: number) => 50 + (x - xmin) / Math.max(xmax - xmin, 1e-9) * 840
  const sy = (y: number) => 300 - (y - ymin) / Math.max(ymax - ymin, 1e-9) * 260
  const path = (points: Point[]) => points.filter(p => Number.isFinite(p.x) && Number.isFinite(p.y)).map((p,i) => `${i ? 'L' : 'M'}${sx(p.x).toFixed(2)},${sy(p.y).toFixed(2)}`).join(' ')
  return <svg className="chart" viewBox="0 0 920 335" preserveAspectRatio="none">
    <defs><linearGradient id="cert" x1="0" x2="1"><stop stopColor="#3de9b0" stopOpacity=".03"/><stop offset=".5" stopColor="#3de9b0" stopOpacity=".16"/><stop offset="1" stopColor="#3de9b0" stopOpacity=".03"/></linearGradient></defs>
    {[0,.25,.5,.75,1].map(k => <line className="gridline" key={k} x1="50" x2="890" y1={40 + k*260} y2={40 + k*260}/>)}
    {highlight && <rect className="busy-highlight" x={sx(highlight[0])} width={Math.max(2,sx(highlight[1])-sx(highlight[0]))} y="40" height="260"/>}
    {certified && <rect fill="url(#cert)" x={sx(certified[0])} width={Math.max(2,sx(certified[1])-sx(certified[0]))} y="40" height="260"/>}
    {zeroLine && ymin <= 0 && ymax >= 0 && <line className="zero-line" x1="50" x2="890" y1={sy(0)} y2={sy(0)}/>}
    {series.map(s => <path key={s.name} d={path(s.points)} fill="none" stroke={s.color} strokeWidth="2" vectorEffect="non-scaling-stroke"/>)}
    <text x="50" y="324">{format(xmin)}</text><text textAnchor="end" x="890" y="324">{format(xmax)}</text><text x="8" y="48">{format(ymax0)}</text><text x="8" y="298">{format(ymin0)}</text>
  </svg>
}

function Scatter({points}: {points: Point[]}) {
  const clean = points.filter(p => Number.isFinite(p.x) && Number.isFinite(p.y)); if (!clean.length) return null
  const xs = clean.map(p=>p.x), ys=clean.map(p=>p.y), xmin=Math.min(...xs), xmax=Math.max(...xs), ymin=Math.min(...ys), ymax=Math.max(...ys)
  const sx=(x:number)=>45+(x-xmin)/Math.max(xmax-xmin,1e-9)*840, sy=(y:number)=>295-(y-ymin)/Math.max(ymax-ymin,1e-9)*250
  const stride = Math.max(1, Math.floor(clean.length / 2200))
  return <svg className="chart" viewBox="0 0 920 330" preserveAspectRatio="none">{[0,.25,.5,.75,1].map(k=><line className="gridline" key={k} x1="45" x2="885" y1={45+k*250} y2={45+k*250}/>)}{clean.filter((_,i)=>i%stride===0).map((p,i)=><circle key={i} cx={sx(p.x)} cy={sy(p.y)} r="1.7" fill={p.y < 0 ? '#ff4d86' : '#52e0bb'} opacity=".55"/>)}<text x="45" y="322">{format(xmin)}</text><text textAnchor="end" x="885" y="322">{format(xmax)}</text></svg>
}

function findRoute(edges: GardenEdge[], start: string, target: string, mode: RouteMode): GardenEdge[] {
  if (start === target) return []
  const allowed = edges.filter(edge => mode === 'all' || edge.trust === 'LeanChecked' || (mode === 'literature' && edge.trust === 'LiteratureCertified'))
  const queue: Array<{node: string; route: GardenEdge[]}> = [{node: start, route: []}], seen = new Set([start])
  while (queue.length) { const current = queue.shift()!; for (const edge of allowed.filter(x => x.source === current.node)) { if (seen.has(edge.target)) continue; const route=[...current.route,edge]; if(edge.target===target)return route; seen.add(edge.target); queue.push({node:edge.target,route}) } }
  return []
}

function layoutNodes(nodes: GardenNode[]): Map<string, {x: number; y: number}> {
  const districtOrder = ['Xi','Hadamard','Li','Weil','Nevanlinna','Suzuki','Prime arithmetic','Explorer','Open frontiers']
  const result = new Map<string,{x:number;y:number}>()
  districtOrder.forEach((district, di) => {
    const members=nodes.filter(n=>n.district===district), col=di%3, row=Math.floor(di/3), baseX=300+col*610, baseY=190+row*395
    members.forEach((node,i)=>{const cols=4; result.set(node.id,{x:baseX+(i%cols-1.5)*142,y:baseY+(Math.floor(i/cols)-Math.floor(members.length/cols)/2)*68})})
  })
  return result
}

function clamp(x: number, lo: number, hi: number) { return Math.max(lo, Math.min(hi, x)) }
function truncate(text: string, length: number) { return text.length > length ? `${text.slice(0,length-1)}…` : text }
function format(value: number | null) { if (value === null || !Number.isFinite(value)) return '—'; const a=Math.abs(value); return a !== 0 && (a < .001 || a >= 10000) ? value.toExponential(3) : value.toFixed(a < 1 ? 6 : a < 100 ? 4 : 2) }
