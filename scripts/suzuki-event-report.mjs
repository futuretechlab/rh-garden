// Future Technologies Laboratory LLC. Numerical diagnostics only.
// Usage: node scripts/suzuki-event-report.mjs REGRESSION.json
import { readFileSync } from 'node:fs';
import assert from 'node:assert/strict';

const data = JSON.parse(readFileSync(process.argv[2], 'utf8'));
assert.equal(data.summary.trust, 'NumericalEvidence');
assert.equal(data.summary.regressions_pass, true);
console.log(JSON.stringify(data.summary, null, 2));
for (const p of [...data.regressions, ...data.event_log_failures]) {
  let localCost = 0;
  let firstLocalFailure = null;
  for (const row of p.chebyshev_profile) {
    assert.ok(row.event_excess_upper + 1e-8 >= row.exact_excess);
    assert.ok(row.outgoing_envelope_cost + 1e-8 >= row.outgoing_exact_cost);
    localCost += row.outgoing_local_width_cost;
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
  console.log(JSON.stringify({
    start: p.start_event, recovery_before: p.recovery_before_event,
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
