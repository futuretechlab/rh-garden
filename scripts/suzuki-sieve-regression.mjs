// Copyright (c) 2026 Future Technologies Laboratory LLC.
// Validation path ONLY: exact future samples never enter candidate().
import {readFileSync,writeFileSync} from 'node:fs';
import assert from 'node:assert/strict';
import {candidate,weight,referenceCost} from './suzuki-sieve-candidate.mjs';
const data=JSON.parse(readFileSync(process.argv[2], 'utf8'));
const periods=[31,324431,8573249].map(m=>data.regressions.find(p=>p.start_event===m));
assert.ok(periods.every(Boolean));
const cases=[...periods.map(p=>({m:p.start_event,x:p.recovery_square,label:'measured recovery (validation only)'})),
  {m:324432,x:361197.6403415228,label:'cutoff inside pre-existing excursion'},
  {m:19999981,x:19999999,label:'unfinished cutoff window'},
  {m:30,x:31,label:'one-integer prime endpoint'},
  {m:31,x:32,label:'one-integer proper-power endpoint'},
  {m:31,x:32.25,label:'very short after power jump'},
  {m:10,x:15,label:'small nontrivial interval'}, {m:31,x:31,label:'zero width'},
  {m:37,x:37.5,label:'sub-integer width'}];
const cutoff=Math.ceil(Math.max(...cases.map(c=>c.x)));
// Independent full-origin validation sieve; this object is not passed to candidate().
const composite=new Uint8Array(cutoff+1),lambda=new Float64Array(cutoff+1),isPrime=new Uint8Array(cutoff+1);
for(let p=2;p<=cutoff;p++) if(!composite[p]) {
  isPrime[p]=1;
  for(let n=p*p;n<=cutoff;n+=p) composite[n]=1;
  for(let q=p;q<=cutoff;q*=p) lambda[q]=Math.log(p);
}
const c=(-0.5772156649015329-Math.PI/2-3*Math.log(2)-Math.log(Math.PI))/2;
const catalan=0.915965594177219;
function arch(x) { const u=Math.sqrt(x),t=Math.log(x); let tail=0;
  for(let n=0;n<40;n++) tail+=4/(4*n+1)**2*u**(-(4*n+1));
  return 4*(u+1/u-2)+c*t+Math.PI**2/4+2*catalan-tail;
}
function slope(x) {const u=Math.sqrt(x); return 2*(u-1/u)+c+Math.PI/2-Math.atan(u)+0.5*Math.log((1+1/u)/(1-1/u));}
function simpson(f,a,b,N=512) {let total=f(a)+f(b); for(let i=1;i<N;i++) total+=(i%2?4:2)*f(a+(b-a)*i/N);return total*(b-a)/(3*N);}
function defectCharge(m,x) { if(x===m) return 0; return simpson(u=>2/(u*u*(u**4-1))*Math.log(x/(u*u)),Math.sqrt(m),Math.sqrt(x)); }
const anchors=new Set(cases.flatMap(p=>[p.m,Math.floor(p.x)])),states=new Map();
let T=0,L=0,tcor=0,lcor=0;
for(let n=2;n<=cutoff;n++) {
  let y=lambda[n]/Math.sqrt(n)-tcor,t=T+y;tcor=(t-T)-y;T=t;
  y=lambda[n]*Math.log(n)/Math.sqrt(n)-lcor;t=L+y;lcor=(t-L)-y;L=t;
  if(anchors.has(n)) states.set(n,{V:arch(n)-T*Math.log(n)+L,D:slope(n)-T,T,L});
}
function integrateAnchoredError(m,x) {
  let total=0,increment=0;
  for(let k=m;k<x;k++) {
    if(k>m) increment+=lambda[k];
    const right=Math.min(k+1,x);
    const f=y=>(increment-(y-m))*(1+0.5*Math.log(x/y))/(y*Math.sqrt(y));
    // The fixed arithmetic increment is that of [k,k+1), including k, excluding k+1.
    total+=simpson(f,k,right,m<100?32:2);
  }
  return total;
}
const reports=[];
for(const spec of cases) {
 const {m,x}=spec,bound=candidate(m,x),st=states.get(m),Adef=defectCharge(m,x),signed=st.D*Math.log(x/m);
 let prime=0,pp=0; for(let n=m+1;n<=x;n++) if(lambda[n]) {
   const v=lambda[n]/Math.sqrt(n)*Math.log(x/n); if(isPrime[n]) prime+=v;else pp+=v;
 }
 const I=prime+pp-referenceCost(m,x),budget=st.V+signed-Adef;
 const integratedI=integrateAnchoredError(m,x),end=states.get(Math.floor(x));
 const endpointV=arch(x)-end.T*Math.log(x)+end.L;
 assert.ok(Math.abs(integratedI-I)<1e-8,`anchored integral residual m=${m}: ${integratedI-I}`);
 assert.ok(Math.abs(endpointV-(budget-I))<1e-8);
 if(spec.label==='measured recovery (validation only)') assert.ok(Math.abs(slope(x)-end.T)<1e-8);
 if(spec.label==='unfinished cutoff window') {
   assert.ok(st.D<0 && states.get(Math.floor(x)).D<0);
   // Even uninterrupted service at its upper speed 2 cannot recover in this window.
   assert.ok(st.D+2*(Math.sqrt(x)-Math.sqrt(m))<0);
 }
 if(m===30 && x===31) assert.ok(Math.abs(lambda[31]-1-(Math.log(31)-1))<1e-14);
 assert.ok(bound.I_upper+1e-8>=I); assert.ok(bound.parity_I_upper+1e-8>=I);
 assert.ok(bound.parity_I_upper<=bound.all_integer_I_upper+1e-10);
 assert.ok(Math.abs(bound.quadratic_residual)<1e-8);
 const count=candidate(m,x,{mode:'count'});
 // Predetermined prefixes: do not select coefficients/level from observed events.
 let firstFail=null;
 const prefixes=[...new Set([m,Math.min(x,m+0.5),Math.min(x,m+1),...Array.from({length:32},(_,i)=>m+(x-m)*(i+1)/32)])].sort((a,b)=>a-b);
 for(const y of prefixes) {
   const v=candidate(m,y),B=st.V+st.D*Math.log(y/m)-defectCharge(m,y);
   if(v.I_upper>B+1e-10 && firstFail===null) firstFail={x:y,I_upper:v.I_upper,budget:B};
 }
 reports.push({...spec,z:bound.z,support_size:bound.support.length,
   starting_reserve:st.V,starting_signed_D:st.D,terminal_signed_D:slope(x)-end.T,
   signed_log_contribution:signed,arch_defect_charge:Adef,
   available_budget:budget,true_I:I,actual_endpoint_reserve:budget-I,
   anchored_integral_residual:integratedI-I,signed_identity_residual:endpointV-(budget-I),
   continuous_main_term_C:bound.C,actual_prime_part:prime,actual_proper_power_part:pp,
   sieve_prime_part:bound.prime_bound,all_base_proper_power_part:bound.proper_power_bound,
   pure_density_budget_limit:bound.C>0?budget/bound.C:null,
   pure_burst_budget_limit:x>m?budget*Math.sqrt(m)/Math.log(x/m):null,
   weighted_sieve_I_upper:bound.I_upper,favorable_exact_PP_I_upper:bound.prime_bound+pp-bound.C,
   prime_overcharge:bound.prime_bound-prime,proper_power_overcharge:bound.proper_power_bound-pp,
   parity_I_upper:bound.parity_I_upper,all_integer_I_upper:bound.all_integer_I_upper,
   count_optimized_I_upper:count.I_upper,count_first_log_x_I_upper:count.count_first_log_x_I_upper,
   reserve_deficit:bound.I_upper-budget,parity_reserve_deficit:bound.parity_I_upper-budget,
   first_failing_tested_prefix:firstFail,coefficient_rounding:'exact rational proposal, denominator 1000000',
   divisor_support:bound.support,coefficient_numerators:bound.coefficient_numerators,
   quadratic_residual:bound.quadratic_residual,numerical_enclosure_error:null});
}
const report={trust:'NumericalEvidence',candidate_inputs:'m,x; z=max(1,min(600,m-1,floor(sqrt(floor(x)-m)))); squarefree divisors <=z; divisibility and elementary weights only',
 validation_cutoff:cutoff,rounding:'IEEE-754, no proved outward bounds or optimizer minimum',
 prefix_coverage:'finite predetermined test grid only, not every real prefix',cases:reports};
if(process.argv[3]) writeFileSync(process.argv[3],JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({...report,cases:reports.map(({divisor_support,coefficient_numerators,...r})=>r)},null,2));
