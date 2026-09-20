// Copyright (c) 2026 Future Technologies Laboratory LLC.
// Sample-independent RELAXATIONS. Inputs: q and the explicitly retained scalar s.
// No prime/Mangoldt table or measured recovery coordinate is read here.
// IEEE-754 exploratory evaluation, NOT an outward-rounded certificate.
export function prefixCap(n) {
  const l = Math.log(n);
  return 2 * Math.log(4) * Math.sqrt(n) + 2 * l + l * l / 2;
}
export function parityCap(n) {
  return Math.log(n % 2 === 0 ? 2 : n) / Math.sqrt(n);
}
export function momentCandidates(q, s) {
  if (!Number.isSafeInteger(q) || q < 2 || !(s >= 0) || s > prefixCap(q))
    throw new Error('Requires q>=2, nonnegative s, and s<=P(q)');
  let pLayer = s * Math.log(2), parityLayer = pLayer, C = 0;
  let directGreedy = 0, last = 0, pSaturation = null, paritySaturation = null;
  let pcor = 0, gcor = 0, dcor = 0;
  const add = (total, correction, term) => {
    const y = term - correction, t = total + y;
    return [t, (t - total) - y];
  };
  for (let n = 2; n <= q; n++) {
    const U = prefixCap(n), previous = C;
    C = Math.min(s, U, C + parityCap(n));
    [directGreedy, dcor] = add(directGreedy, dcor, (C - previous) * Math.log(n));
    if (pSaturation === null && U >= s) pSaturation = n;
    if (paritySaturation === null && C === s) paritySaturation = n;
    if (n < q) {
      const dlog = Math.log1p(1 / n);
      [pLayer, pcor] = add(pLayer, pcor, Math.max(s - U, 0) * dlog);
      [parityLayer, gcor] = add(parityLayer, gcor, (s - C) * dlog);
    }
    last = n;
    if (C === s && U >= s) break;
  }
  return {baseline:s * Math.log(2), cumulative:pLayer, cumulative_parity:parityLayer,
    greedy_direct_moment:directGreedy, greedy_terminal_mass:C, parity_feasible:C===s,
    greedy_identity_residual:parityLayer-directGreedy, p_saturation:pSaturation,
    parity_saturation:paritySaturation, evaluated_integers:last-1,
    inputs:['q','terminal scalar s','proved P(n)','proved parity pointwise cap'],
    numerical_enclosure_error:null};
}
