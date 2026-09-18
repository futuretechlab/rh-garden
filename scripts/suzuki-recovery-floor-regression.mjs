// Copyright (c) 2026 Future Technologies Laboratory LLC.
// NumericalEvidence ONLY. Reads retained diagnostics; performs no prime scan.
// Measured recovery endpoints and state samples are validation data, never
// hypotheses of a universal floor. IEEE-754 values are not outward enclosures.
import {readFileSync, writeFileSync} from 'node:fs';
import assert from 'node:assert/strict';

const events = JSON.parse(readFileSync(process.argv[2], 'utf8'));
const sieve = JSON.parse(readFileSync(process.argv[3], 'utf8'));
const log2 = Math.log(2), kappa = 151 / 20000;
const c = (-0.5772156649015329 - Math.PI / 2 - 3 * log2 - Math.log(Math.PI)) / 2;
function arch(x) {
  const u = Math.sqrt(x), t = Math.log(x);
  let tail = 0;
  for (let n = 0; n < 40; n++) tail += 4 / (4 * n + 1) ** 2 * u ** (-(4 * n + 1));
  return 4 * (u + 1 / u - 2) + c * t + Math.PI ** 2 / 4 + 2 * 0.915965594177219 - tail;
}
function slope(x) {
  const u = Math.sqrt(x);
  return 2 * (u - 1 / u) + c + Math.PI / 2 - Math.atan(u)
    + 0.5 * Math.log((1 + 1 / u) / (1 - 1 / u));
}
function explicitFloor(t) {
  return kappa * Math.expm1(t / 2)
    - (t - log2) * (2 * Math.log(4) * Math.exp(t / 2) + 2 * t + t * t / 2);
}
const cases = [31, 324431, 8573249].map(m => {
  const period = events.regressions.find(p => p.start_event === m);
  const reference = sieve.cases.find(p => p.m === m && p.label === 'measured recovery (validation only)');
  assert(period && reference);
  const x = period.recovery_square, b = Math.sqrt(x), t = Math.log(x);
  assert.equal(x, reference.x);
  const lastEvent = period.chebyshev_profile.at(-2);
  assert(Number.isInteger(lastEvent.x) && lastEvent.x < x);
  const reserve = reference.actual_endpoint_reserve;
  const support = arch(x) - (t - log2) * slope(x);
  const explicit = explicitFloor(t);
  const curvature = lastEvent.remaining_reserve
    - 3 / (5 * Math.sqrt(lastEvent.x)) * lastEvent.backlog ** 2;
  assert(Math.abs(reference.terminal_signed_D) < 1e-8);
  assert(explicit <= support + 1e-8 && support <= reserve + 1e-8);
  assert(explicit <= -b);
  assert(curvature <= reserve + 1e-7);
  return {m, recovery_square: x, recovery_root: b, last_event: lastEvent.x,
    next_event: period.recovery_before_event, actual_reserve: reserve,
    correlated_support_floor: support, explicit_floor: explicit,
    explicit_floor_gap: reserve - explicit, state_local_curvature_floor: curvature,
    curvature_gap: reserve - curvature};
});
for (const t of [2, 4, 10, 20, 40]) assert(explicitFloor(t) <= -Math.exp(t / 2));
const unfinished = sieve.cases.find(p => p.m === 19999981 && p.x === 19999999);
assert(unfinished && unfinished.terminal_signed_D < 0);
for (const [m, x, gap] of [[324431, 339360, 0.0053], [8573249, 8620438, 0.00017]]) {
  const witness = sieve.cases.find(p => p.m === m && p.x === x);
  assert(witness && witness.arithmetic_target_gap > gap);
}
const result = {trust: 'NumericalEvidence', rounding: 'IEEE-754; no outward enclosure',
  new_prime_scan: false, uniform_floor_proved: false, cases,
  unfinished_terminal: {m: unfinished.m, x: unfinished.x,
    discrepancy: unfinished.terminal_signed_D, completed: false}, tests_passed: true};
const json = JSON.stringify(result, null, 2) + '\n';
if (process.argv[4]) writeFileSync(process.argv[4], json);
console.log(json);
