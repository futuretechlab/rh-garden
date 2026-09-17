// Copyright (c) 2026 Future Technologies Laboratory LLC.
// Floating-point regressions only: not outward-rounded or proof evidence.
// Usage: node scripts/suzuki-surcharge-profile.mjs .cabal-work/event-diagnostics.json
import { readFileSync } from 'node:fs';
import assert from 'node:assert/strict';

const data = JSON.parse(readFileSync(process.argv[2], 'utf8'));
assert.equal(data.summary.trust, 'NumericalEvidence');
const periods = [31, 324431, 8573249].map(m => {
  const p = data.regressions.find(p => p.start_event === m);
  assert.ok(p, `missing required regression ${m}`);
  return p;
});
const windows = [
  ...periods.map(p => ({ m: p.start_event, x: p.recovery_square, period: p })),
  { m: 2, x: 64 }, { m: 4, x: 4 }, { m: 4, x: 81 }, { m: 31, x: 32 },
  { m: 32, x: 37 }, { m: 37, x: 148 }, { m: 1000, x: 1000 * Math.exp(1) },
];
const cutoff = Math.max(...windows.map(w => w.x));
const baseLimit = Math.floor(Math.sqrt(cutoff));
const composite = new Uint8Array(baseLimit + 1);
const primes = [];
for (let p = 2; p <= baseLimit; p++) {
  if (composite[p]) continue;
  primes.push(p);
  for (let q = p * p; q <= baseLimit; q += p) composite[q] = 1;
}
const powers = [];
for (const p of primes) {
  for (let k = 2, q = p * p; q <= cutoff; k++, q *= p) {
    powers.push({ p, k, q, gamma: (k - 1) * Math.log(p) / Math.sqrt(q) });
  }
}
powers.sort((a, b) => a.q - b.q);
assert.equal(new Set(powers.map(e => e.q)).size, powers.length);
const sum = values => values.reduce((a, b) => a + b, 0);
const tolerance = 1e-9;
let maxRampResidual = 0;
let maxIntegralResidual = 0;
let maxRecoveryResidual = 0;
const reports = [];
for (const { m, x, period } of windows) {
  const S = Math.log(x / m);
  // Anchor excluded, even when it is itself a proper prime power.
  const events = powers.filter(e => m < e.q && e.q <= x)
    .map(e => ({ ...e, t: Math.log(e.q / m) }));
  const points = [...new Set([0, S / 7, S / 2, S, ...events.map(e => e.t)])]
    .filter(s => s <= S).sort((a, b) => a - b);
  for (const s of points) {
    const endpoint = m * Math.exp(s);
    const direct = sum(events.filter(e => e.q <= endpoint)
      .map(e => e.gamma * Math.log(endpoint / e.q)));
    const ramp = sum(events.map(e => e.gamma * Math.max(s - e.t, 0)));
    const cuts = [...new Set([0, s, ...events.filter(e => e.t < s).map(e => e.t)])]
      .sort((a, b) => a - b);
    const integrated = sum(cuts.slice(1).map((right, i) => {
      const left = cuts[i];
      const midpoint = (left + right) / 2;
      return (right - left) * sum(events.filter(e => e.t <= midpoint).map(e => e.gamma));
    }));
    maxRampResidual = Math.max(maxRampResidual, Math.abs(direct - ramp));
    maxIntegralResidual = Math.max(maxIntegralResidual, Math.abs(direct - integrated));
    assert.ok(Math.abs(direct - ramp) < tolerance, `ramp m=${m}, s=${s}`);
    assert.ok(Math.abs(direct - integrated) < tolerance, `integral m=${m}, s=${s}`);
  }
  const J = sum(events.map(e => e.gamma * Math.log(x / e.q)));
  const deltaSquare = sum(events.filter(e => e.k === 2).map(e => e.gamma));
  const deltaHigher = sum(events.filter(e => e.k >= 3).map(e => e.gamma));
  if (period) {
    const residual = Math.abs(J - period.prime_power_surcharge);
    maxRecoveryResidual = Math.max(maxRecoveryResidual, residual);
    assert.ok(residual < tolerance, `recovery surcharge m=${m}`);
  }
  reports.push({ m, terminal_square: x, S, proper_power_events: events.length,
    profile_test_points: points.length, delta_square: deltaSquare, delta_higher: deltaHigher,
    J, limiting_profile: S * S / 4,
    recovery_before_event: period?.recovery_before_event,
    recovery_root: period?.root_end, true_loss: period?.weighted_loss,
    integrated_event_log_cost: period?.event_log_cost,
    rounded_sample_cost: period?.envelope_cost,
    conservative_sample_linear_cost: period?.envelope_linear_cost });
}
const event32 = powers.find(e => e.q === 32);
assert.equal(event32.k, 5);
assert.equal(event32.gamma * Math.max(Math.log(32 / 31) - Math.log(32 / 31), 0), 0);
assert.ok(sum(powers.filter(e => 31 < e.q && e.q <= 32).map(e => e.gamma)) > 0);
assert.equal(powers.filter(e => 32 < e.q && e.q <= 37).length, 0);
console.log(JSON.stringify({ trust: 'NumericalEvidence', arithmetic: 'IEEE-754, not outward-rounded',
  cutoff, proper_power_table_size: powers.length, max_ramp_residual: maxRampResidual,
  max_integral_residual: maxIntegralResidual, max_recovery_surcharge_residual: maxRecoveryResidual,
  endpoint_tests_pass: true, windows: reports }, null, 2));
