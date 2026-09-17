// Future Technologies Laboratory LLC. Numerical diagnostics only.
// Usage: node scripts/suzuki-event-report.mjs REGRESSION.json
import { readFileSync } from 'node:fs';
import assert from 'node:assert/strict';

const data = JSON.parse(readFileSync(process.argv[2], 'utf8'));
assert.equal(data.summary.trust, 'NumericalEvidence');
assert.equal(data.summary.regressions_pass, true);
console.log(JSON.stringify(data.summary, null, 2));
for (const p of new Map([...data.regressions, ...data.event_log_failures]
  .map(p => [p.start_event, p])).values()) {
  let localCost = 0;
  let pinnedCost = 0;
  let firstPinnedFailure = null;
  let firstLocalFailure = null;
  for (const row of p.chebyshev_profile) {
    assert.ok(row.event_excess_upper + 1e-8 >= row.exact_excess);
    assert.ok(row.outgoing_envelope_cost + 1e-8 >= row.outgoing_exact_cost);
    localCost += row.outgoing_local_width_cost;
    pinnedCost += row.outgoing_pinned_cost;
    if (pinnedCost > p.psi_start + 1e-10 && firstPinnedFailure === null) {
      firstPinnedFailure = { event: row.x, exact_excess: row.exact_excess,
        pinned_excess_upper: row.pinned_excess_upper, cumulative_cost: pinnedCost,
        reserve: p.psi_start, gap: pinnedCost - p.psi_start };
    }
    if (localCost > p.psi_start + 1e-10 && firstLocalFailure === null) {
      firstLocalFailure = {
        event: row.x,
        exact_excess: row.exact_excess,
        arithmetic_upper: row.local_width_excess_upper,
        cell_cost: row.outgoing_local_width_cost,
        cumulative_cost: localCost,
        reserve: p.psi_start,
        gap: localCost - p.psi_start,
        cause: 'local-width arithmetic envelope exceeds the total-cost budget',
      };
    }
  }
  assert.equal(firstLocalFailure?.event ?? null, p.local_width_first_failing_cell);
  assert.ok(Math.abs(localCost - p.local_width_cost) < 1e-6);
  assert.ok(Math.abs(p.event_log_cost - p.weighted_loss - p.prime_power_surcharge) < 1e-7);
  assert.equal(firstPinnedFailure?.event ?? null, p.pinned_anchored_first_failing_cell);
  console.log(JSON.stringify({
    start: p.start_event, recovery_before: p.recovery_before_event,
    recovery_root: p.root_end, recovery_square: p.recovery_square,
    recovery_reserve: p.psi_end, surcharge: p.prime_power_surcharge,
    surcharge_identity_residual: p.surcharge_identity_residual,
    pinned_anchored_cost: p.pinned_anchored_cost, first_pinned_failure: firstPinnedFailure,
    events: p.event_count, exported_rows: p.chebyshev_profile.length,
    terminal_slack: p.arrival_slack, prefix_slack: p.prefix_envelope_slack,
    old_affine_slack: p.anchored_linear_envelope_slack,
    reserve: p.psi_start, exact_cost: p.finite_event_exact_cost,
    sample_envelope_cost: p.envelope_cost, sample_cost_gap: p.envelope_cost_gap,
    sample_linear_cost: p.envelope_linear_cost,
    sample_reserve_remaining: p.envelope_reserve_remaining,
    sample_max_excess_gap: p.envelope_max_excess_gap,
    sample_first_failure: p.envelope_first_failing_cell,
    local_width_cost: p.local_width_cost, first_local_failure: firstLocalFailure,
    event_log_cost: p.event_log_cost,
    event_log_cost_gap: p.event_log_cost - p.finite_event_exact_cost,
    event_log_reserve_remaining: p.event_log_reserve_remaining,
    event_log_first_failure: p.event_log_first_failing_cell,
    event_log_failing_row: p.chebyshev_profile.find(row =>
      row.x === p.event_log_first_failing_cell),
  }, null, 2));
}
