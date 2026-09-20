// Copyright (c) 2026 Future Technologies Laboratory LLC.
// Validation only. Actual intermediate samples NEVER enter momentCandidates.
import {readFileSync,writeFileSync} from 'node:fs';
import assert from 'node:assert/strict';
import {momentCandidates} from './suzuki-moment-candidate.mjs';
const events=JSON.parse(readFileSync(process.argv[2],'utf8'));
const sieve=JSON.parse(readFileSync(process.argv[3],'utf8'));
const c=(-0.5772156649015329-Math.PI/2-3*Math.log(2)-Math.log(Math.PI))/2;
function arch(x) {
  const u=Math.sqrt(x),t=Math.log(x);let tail=0;
  for(let n=0;n<40;n++)tail+=4/(4*n+1)**2*u**(-(4*n+1));
  return 4*(u+1/u-2)+c*t+Math.PI**2/4+2*0.915965594177219-tail;
}
function oldFloor(t) {
  return 151/20000*Math.expm1(t/2)-(t-Math.log(2))*(2*Math.log(4)*Math.exp(t/2)+2*t+t*t/2);
}
const cases=[31,324431,8573249].map((m,i)=>{
  const p=events.regressions.find(p=>p.start_event===m);
  const v=sieve.cases.find(p=>p.m===m && p.label==='measured recovery (validation only)');
  assert(p&&v);
  const q=p.chebyshev_profile.at(-2).x,s=v.actual_terminal_weighted_mass,T=v.actual_terminal_log_moment;
  assert(Number.isFinite(s)&&Number.isFinite(T));
  const x=p.recovery_square,t=Math.log(x),dual=s*t-arch(x),bounds=momentCandidates(q,s);
  const actual=T-dual,base=bounds.baseline-dual,cumulative=bounds.cumulative-dual;
  const parity=bounds.cumulative_parity-dual;
  assert(Math.abs(actual-v.actual_endpoint_reserve)<1e-8);
  assert(Math.abs(cumulative-[-13.67417,-1248.78328,-4768.25121][i])<0.002);
  assert(bounds.greedy_terminal_mass===s);
  assert(bounds.parity_feasible);
  assert(Math.abs(bounds.greedy_identity_residual)<1e-7);
  assert(base<cumulative && cumulative<parity && parity<0 && parity<actual);
  return {m,q,recovery_square:x,s,T,arch_dual:dual,actual_margin:actual,
    baseline_margin:base,cumulative_margin:cumulative,parity_margin:parity,
    old_F:oldFloor(t),moment_improvement:cumulative-base,
    parity_improvement:parity-cumulative,parity_deficit:actual-parity,
    same_archimedean_dual:true,terminal_discrepancy_residual:v.terminal_signed_D,...bounds};
});
const zero=momentCandidates(2,0), single=momentCandidates(2,Math.log(2)/Math.sqrt(2));
assert.equal(zero.cumulative,0);assert.equal(zero.cumulative_parity,0);
assert.equal(single.baseline,single.cumulative);
assert.equal(single.cumulative,single.cumulative_parity);
assert.equal(single.greedy_terminal_mass,Math.log(2)/Math.sqrt(2));
assert.equal(momentCandidates(2,1).parity_feasible,false);
// Synthetic scalar states probe the relaxation, not the location of any prime.
const scales=[100,300,1000,3000,10000].map(s=>{
  const q=Math.ceil((s/2)**2),v=momentCandidates(q,s),leadingDual=2*s*Math.log(s/2)-2*s;
  return {s,q,cumulative_normalized:(v.cumulative-leadingDual)/s,
    parity_normalized:(v.cumulative_parity-leadingDual)/s,
    parity_improvement:v.cumulative_parity-v.cumulative,...v};
});
const unfinished=sieve.cases.find(v=>v.m===19999981&&v.x===19999999);
assert(unfinished.terminal_signed_D<0);
const result={trust:'NumericalEvidence',rounding:'IEEE-754; no proved outward enclosure',
  asymptotic_limit_written_only:-2*Math.log(Math.log(4)),new_prime_scan:false,
  optimality_scope:'arbitrary nonnegative real weights with specified caps, not Mangoldt weights',
  uniform_floor_proved:false,cases,scales,endpoint_tests:true,
  unfinished_terminal_preserved:true,tests_passed:true};
const json=JSON.stringify(result,null,2)+'\n';
if(process.argv[4])writeFileSync(process.argv[4],json);
console.log(json);
