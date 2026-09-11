export type Trust = 'LeanChecked' | 'LiteratureCertified' | 'NumericalEvidence' | 'Conjectural' | 'ExactExecutable' | 'Open'

export interface GardenNode {
  id: string
  display_name: string
  district: string
  description: string
  trust: Trust
  kind: 'proposition' | 'representation'
  status: 'open' | 'defined'
  rh_equivalent: boolean
  theorem_names: string[]
  source_files: string[]
}

export interface GardenEdge {
  id: string
  source: string
  target: string
  relation_type: string
  trust: Trust
  theorem_name: string
  provenance: string
  information_loss: string
  description: string
}

export interface GardenData {
  schema_version: number
  generated_by: string
  nodes: GardenNode[]
  edges: GardenEdge[]
}

export interface Frontier {
  id: string
  title: string
  category: string
  status: string
  trust: Trust
  known_chain: string
  exact_blocker: string
  current_bound: string
  source_modules: string[]
  candidate_approaches: string[]
  literature_reference?: string
  literature_url?: string
  literature_scope?: string
}

export interface FrontierData { frontiers: Frontier[] }

export interface StatusData {
  snapshot_commit: string
  snapshot_note: string
  formal_build: string
  cabal_test: string
  submission: string
  submission_ready: boolean
  counts: Record<string, number>
}

export interface FieldSample { omega: number; t: number; psi: number; trust: Trust }

export interface CellMinimum {
  omega: number
  prime_cell: number
  t_left: number
  t_right: number
  minimizing_t_candidate: number
  minimum_candidate: number
  second_derivative: number
}

export interface MangoldtBlock {
  event_q: number
  next_event_r: number
  gap: number
  slope_S_q: number
  intercept_C_q: number
  slope_deficit_left: number
  slope_deficit_right: number
  block_margin: number
  minimizing_t_candidate: number
  exp_minimizing_t_candidate: number
  minimizer_type: string
  winning_integer_cell: number
}

export interface DualRow {
  event_q: number
  next_event_r: number
  lambda_q: number
  slope_S_q: number
  global_dual_margin: number
  event_slope_deficit: number
  archimedean_drift: number
  next_mangoldt_impulse: number
  active_block: boolean
  block_margin: number
  event_value: number
  sqrt_event: number
  sqrt_next_event: number
  root_optimizer_before: number
  root_optimizer_after: number
  root_displacement: number
  root_ratio: number
}

export interface BusyPeriod {
  start_event: number
  recovery_before_event: number
  event_count: number
  interval_start: number
  interval_end: number
  interval_width: number
  theta_eff: number | null
  width_over_sqrt_x: number | null
  width_over_sqrt_x_log_x: number | null
  h_over_x_17_30: number | null
  root_start: number
  root_end: number
  root_width: number
  starting_discrepancy: number
  most_negative_discrepancy: number
  weighted_loss: number
  psi_start: number
  psi_end: number
  minimum_psi: number
  loss_over_reserve: number
  arrival_mass: number
  service_drift: number
  arrival_over_service: number | null
  arrival_excess_budget: number
  actual_max_arrival_service_excess: number
  prefix_envelope_slack: number
  required_arrival_upper: number
  arrival_slack: number
  epsilon_required: number | null
  prefix_epsilon_required: number | null
  checked_elementary_arrival_upper: number
  arithmetic_bound_factor: number | null
  arithmetic_bound_excess: number
  pinned_prefix_arrival_upper: number
  pinned_bound_over_arrival: number | null
  pinned_bound_excess_over_service: number
  pinned_bound_over_required: number | null
  pinned_bound_excess_over_required: number
}

export interface ExplorerSlice {
  summaries: Array<{omega: number; minimum: number; minimizing_t: number; prime_cell: number}>
  cell_minima: CellMinimum[]
  mangoldt_blocks: MangoldtBlock[]
  dual_dynamics: DualRow[]
  busy_periods: BusyPeriod[]
}

export interface ExplorerData {
  trust: Trust
  warning: string
  field_samples: FieldSample[]
  scan: ExplorerSlice
  busy: ExplorerSlice
  arithmetic_frontier_periods: BusyPeriod[]
}
