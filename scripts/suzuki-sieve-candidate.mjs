// Copyright (c) 2026 Future Technologies Laboratory LLC.
// Sample-independent candidate path. No prime/event/Chebyshev samples are accepted.
// All real evaluations are exploratory IEEE-754, not outward-certified enclosures.
export const weight = (n, x) => Math.log(n) / Math.sqrt(n) * Math.log(x / n);
export function referenceCost(m, x) {
  const t = Math.log1p((x - m) / m) / 2;
  let rem = 0, term = t * t / 2;
  for (let k = 2; k < 50; k++) { rem += term; term *= t / (k + 1); }
  return 4 * Math.sqrt(m) * rem;
}
const gcd = (a,b) => { while(b) [a,b]=[b,a%b]; return a; };
const lcm = (a,b) => a / gcd(a,b) * b;
function squarefreeSupport(z) {
  const bad = new Uint8Array(z + 1);
  for (let d = 2; d*d <= z; d++) for (let n = d*d; n <= z; n += d*d) bad[n] = 1;
  return Array.from({length:z},(_,i)=>i+1).filter(d=>!bad[d]);
}
// Exact integer residue counts; weighted entries are explicitly NOT enclosures.
export function matrix(m,x,ds,mode='weighted') {
  const N=Math.floor(x), cache=new Map();
  const entry = L => {
    if(cache.has(L)) return cache.get(L);
    let value=0;
    if(mode==='count') value=Math.floor(N/L)-Math.floor(m/L);
    else for(let n=(Math.floor(m/L)+1)*L;n<=N;n+=L) value+=weight(n,x);
    cache.set(L,value); return value;
  };
  return ds.map(d=>Float64Array.from(ds,e=>entry(lcm(d,e))));
}
function proposedCoefficients(Q) {
  // Solve Q_minor*a=-Q_minor,1. Cholesky suggests coefficients; no optimality claim.
  const n=Q.length-1,L=Array.from({length:n},()=>new Float64Array(n));
  for(let i=0;i<n;i++) for(let j=0;j<=i;j++) {
    let v=Q[i+1][j+1]; for(let k=0;k<j;k++) v-=L[i][k]*L[j][k];
    if(i===j) { if(!(v>1e-14)) return [1,...Array(n).fill(0)]; L[i][j]=Math.sqrt(v); }
    else L[i][j]=v/L[j][j];
  }
  const y=new Float64Array(n),a=new Float64Array(n);
  for(let i=0;i<n;i++) { let v=-Q[i+1][0]; for(let k=0;k<i;k++) v-=L[i][k]*y[k]; y[i]=v/L[i][i]; }
  for(let i=n-1;i>=0;i--) { let v=y[i]; for(let k=i+1;k<n;k++) v-=L[k][i]*a[k]; a[i]=v/L[i][i]; }
  // The proposed mathematical coefficients are exactly these integers / 10^6.
  return [1,...a].map(v=>Math.round(v*1e6)/1e6);
}
export function allBasePowers(m,x) {
  let value=0, terms=0;
  for(let a=2;a*a<=x;a++) for(let q=a*a;q<=x;q*=a) if(q>m) {
    value+=Math.log(a)/Math.sqrt(q)*Math.log(x/q); terms++;
  }
  return {value,terms};
}
export function evaluateCoefficients(m,x,ds,a) {
  let direct=0,weak=0,parity=0,baseline=0,count=0;
  const nu=new Float64Array(Math.floor(x)-m+1);
  for(let j=0;j<ds.length;j++) for(let n=(Math.floor(m/ds[j])+1)*ds[j];n<=x;n+=ds[j]) nu[n-m]+=a[j];
  for(let n=m+1;n<=x;n++) {
    const w=weight(n,x), v=nu[n-m]**2;
    direct+=w*v; weak+=Math.log(x)/Math.sqrt(n)*Math.log(x/n)*v; count+=v;
    baseline+=w;
    parity+=(n%2 ? Math.log(n):Math.log(2))/Math.sqrt(n)*Math.log(x/n);
  }
  return {direct,weak,parity,baseline,count};
}
export function candidate(m,x,{cap=600,mode='weighted'}={}) {
  if(!Number.isInteger(m)||m<2||x<m) throw Error('requires natural m>=2, real x>=m');
  const z=Math.max(1,Math.min(m-1,cap,Math.floor(Math.sqrt(Math.floor(x)-m))));
  const ds=squarefreeSupport(z),Q=matrix(m,x,ds,mode),a=proposedCoefficients(Q);
  const ev=evaluateCoefficients(m,x,ds,a),pp=allBasePowers(m,x),C=referenceCost(m,x);
  let quadratic=0;
  for(let i=0;i<ds.length;i++) for(let j=0;j<ds.length;j++) quadratic+=a[i]*a[j]*Q[i][j];
  return {m,x,z,support:ds,coefficient_numerators:a.map(v=>Math.round(v*1e6)),denominator:1000000,
    mode,prime_bound:ev.direct,proper_power_bound:pp.value,proper_power_terms:pp.terms,C,
    I_upper:ev.direct+pp.value-C,parity_I_upper:ev.parity-C,
    all_integer_I_upper:ev.baseline-C,count_first_log_x_I_upper:ev.weak+pp.value-C,
    quadratic_residual:quadratic-(mode==='weighted'?ev.direct:ev.count),
    enclosure_error:null,trust:'NumericalEvidence'};
}
