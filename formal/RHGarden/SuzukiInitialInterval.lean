import RHGarden.SuzukiMangoldtBlocks

noncomputable section

open Set
open scoped BigOperators

namespace RHGarden

/-! ## A finite polynomial certificate for the initial Suzuki interval -/

/-- The rational polynomial obtained by retaining the first nine positive
quarter-lattice terms and applying the elementary logarithm minorant in the
initial-interval argument. -/
def suzukiInitialPolynomial (w : ℝ) : ℝ :=
  11 / 5 - 9 / 2 * w + 9 / 10 * w ^ 2 +
    ∑ n ∈ Finset.Icc 1 8,
      4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2 *
        ∑ k ∈ Finset.Icc 1 (4 * n + 1), w ^ k

private theorem differentiable_suzukiInitialPolynomial :
    Differentiable ℝ suzukiInitialPolynomial := by
  unfold suzukiInitialPolynomial
  fun_prop

private def suzukiInitialPolynomialDeriv (w : ℝ) : ℝ :=
      -9 / 2 + 9 / 5 * w +
        ∑ n ∈ Finset.Icc 1 8,
          4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2 *
            ∑ k ∈ Finset.Icc 1 (4 * n + 1), k * w ^ (k - 1)

private def suzukiInitialPolynomialSecond (w : ℝ) : ℝ :=
  9 / 5 +
    ∑ n ∈ Finset.Icc 1 8,
      4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2 *
        ∑ k ∈ Finset.Icc 1 (4 * n + 1),
          k * (k - 1) * w ^ (k - 2)

private theorem hasDerivAt_suzukiInitialPolynomial (w : ℝ) :
    HasDerivAt suzukiInitialPolynomial (suzukiInitialPolynomialDeriv w) w := by
  have hbase : HasDerivAt
      (fun x : ℝ => 11 / 5 - 9 / 2 * x + 9 / 10 * x ^ 2)
      (-9 / 2 + 9 / 5 * w) w := by
    have h := ((hasDerivAt_const w (11 / 5 : ℝ)).sub
      ((hasDerivAt_id w).const_mul (9 / 2))).add
        (((hasDerivAt_id w).pow 2).const_mul (9 / 10))
    have hfun :
        (fun x : ℝ => 11 / 5 - 9 / 2 * x + 9 / 10 * x ^ 2) =
          ((fun _ : ℝ => (11 / 5 : ℝ)) - fun x => 9 / 2 * id x) +
            fun x => 9 / 10 * (id ^ 2) x := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, id_eq, Pi.pow_apply]
    rw [hfun]
    exact h.congr_deriv (by norm_num; ring)
  have hinner : ∀ n : ℕ, HasDerivAt
      (fun x : ℝ => ∑ k ∈ Finset.Icc 1 (4 * n + 1), x ^ k)
      (∑ k ∈ Finset.Icc 1 (4 * n + 1), k * w ^ (k - 1)) w := by
    intro n
    exact HasDerivAt.fun_sum fun k _ => hasDerivAt_pow k w
  have hsum : HasDerivAt
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 8,
        4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2 *
          ∑ k ∈ Finset.Icc 1 (4 * n + 1), x ^ k)
      (∑ n ∈ Finset.Icc 1 8,
        4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2 *
          ∑ k ∈ Finset.Icc 1 (4 * n + 1), k * w ^ (k - 1)) w := by
    exact HasDerivAt.fun_sum fun n _ =>
      (hinner n).const_mul (4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2)
  unfold suzukiInitialPolynomial suzukiInitialPolynomialDeriv
  change HasDerivAt
    (fun x : ℝ =>
      (11 / 5 - 9 / 2 * x + 9 / 10 * x ^ 2) +
        ∑ n ∈ Finset.Icc 1 8,
          4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2 *
            ∑ k ∈ Finset.Icc 1 (4 * n + 1), x ^ k) _ w
  exact hbase.add hsum

private theorem hasDerivAt_suzukiInitialPolynomialDeriv (w : ℝ) :
    HasDerivAt suzukiInitialPolynomialDeriv
      (suzukiInitialPolynomialSecond w) w := by
  have hbase : HasDerivAt (fun x : ℝ => -9 / 2 + 9 / 5 * x) (9 / 5) w := by
    have h := (hasDerivAt_const w (-9 / 2 : ℝ)).add
      ((hasDerivAt_id w).const_mul (9 / 5))
    have hfun : (fun x : ℝ => -9 / 2 + 9 / 5 * x) =
        (fun _ : ℝ => (-9 / 2 : ℝ)) + fun x => 9 / 5 * id x := by
      funext x
      simp only [Pi.add_apply, id_eq]
    rw [hfun]
    exact h.congr_deriv (by norm_num)
  have hinner : ∀ n : ℕ, HasDerivAt
      (fun x : ℝ => ∑ k ∈ Finset.Icc 1 (4 * n + 1),
        (k : ℝ) * x ^ (k - 1))
      (∑ k ∈ Finset.Icc 1 (4 * n + 1),
        k * (k - 1) * w ^ (k - 2)) w := by
    intro n
    exact HasDerivAt.fun_sum fun k hk => by
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hd := (hasDerivAt_pow (k - 1) w).const_mul (k : ℝ)
      have hfun : (fun x : ℝ => (k : ℝ) * x ^ (k - 1)) =
          fun x => (k : ℝ) * (id ^ (k - 1)) x := by
        funext x
        rfl
      rw [hfun]
      apply hd.congr_deriv
      rw [Nat.cast_sub hk1]
      simp only [Nat.sub_sub]
      ring
  have hsum : HasDerivAt
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 8,
        4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2 *
          ∑ k ∈ Finset.Icc 1 (4 * n + 1), k * x ^ (k - 1))
      (∑ n ∈ Finset.Icc 1 8,
        4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2 *
          ∑ k ∈ Finset.Icc 1 (4 * n + 1),
            k * (k - 1) * w ^ (k - 2)) w := by
    exact HasDerivAt.fun_sum fun n _ =>
      (hinner n).const_mul (4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2)
  unfold suzukiInitialPolynomialDeriv suzukiInitialPolynomialSecond
  change HasDerivAt
    (fun x : ℝ => (-9 / 2 + 9 / 5 * x) +
      ∑ n ∈ Finset.Icc 1 8,
        4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2 *
          ∑ k ∈ Finset.Icc 1 (4 * n + 1), k * x ^ (k - 1)) _ w
  exact hbase.add hsum

private theorem deriv_suzukiInitialPolynomial (w : ℝ) :
    deriv suzukiInitialPolynomial w = suzukiInitialPolynomialDeriv w :=
  (hasDerivAt_suzukiInitialPolynomial w).deriv

private theorem differentiable_deriv_suzukiInitialPolynomial :
    Differentiable ℝ (deriv suzukiInitialPolynomial) := by
  intro w
  rw [show deriv suzukiInitialPolynomial = suzukiInitialPolynomialDeriv by
    funext x
    exact deriv_suzukiInitialPolynomial x]
  exact (hasDerivAt_suzukiInitialPolynomialDeriv w).differentiableAt

private theorem one_le_secondDeriv_suzukiInitialPolynomial {w : ℝ}
    (hw : 0 ≤ w) : 1 ≤ deriv (deriv suzukiInitialPolynomial) w := by
  rw [show deriv suzukiInitialPolynomial = suzukiInitialPolynomialDeriv by
    funext x
    exact deriv_suzukiInitialPolynomial x,
    (hasDerivAt_suzukiInitialPolynomialDeriv w).deriv]
  unfold suzukiInitialPolynomialSecond
  have hsum : 0 ≤
      ∑ n ∈ Finset.Icc 1 8,
        4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2 *
          ∑ k ∈ Finset.Icc 1 (4 * n + 1),
            k * (k - 1) * w ^ (k - 2) := by
    apply Finset.sum_nonneg
    intro n hn
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    positivity
  linarith

theorem suzukiInitialPolynomial_at_sample_gt :
    (1 : ℝ) / 100 < suzukiInitialPolynomial (39 / 50) := by
  norm_num [suzukiInitialPolynomial, Finset.sum_Icc_succ_top]

theorem deriv_suzukiInitialPolynomial_at_sample_mem_Ico :
    deriv suzukiInitialPolynomial (39 / 50) ∈ Ico 0 (7 / 100) := by
  rw [deriv_suzukiInitialPolynomial]
  norm_num [suzukiInitialPolynomialDeriv, Finset.sum_Icc_succ_top]

/-- The finite polynomial certificate is uniformly separated from zero on
`[0,1]`.  All numerical claims in this proof are rational normalization. -/
theorem suzukiInitialPolynomial_gt {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    (151 : ℝ) / 20000 < suzukiInitialPolynomial w := by
  have hbound := lower_bound_of_secondDeriv_ge
    (f := suzukiInitialPolynomial) (a := 0) (b := 1)
    (x := 39 / 50) (m := 1) (by norm_num) (by norm_num)
    (by norm_num) differentiable_suzukiInitialPolynomial.continuous.continuousOn
    differentiable_suzukiInitialPolynomial.differentiableOn
    differentiable_deriv_suzukiInitialPolynomial.differentiableOn
    (fun y hy => one_le_secondDeriv_suzukiInitialPolynomial hy.1.le)
    w ⟨hw0, hw1⟩
  have hv := suzukiInitialPolynomial_at_sample_gt
  have hd := deriv_suzukiInitialPolynomial_at_sample_mem_Ico
  norm_num at hbound hv hd ⊢
  nlinarith [sq_nonneg (deriv suzukiInitialPolynomial (39 / 50))]

private def suzukiInitialLogAux (w : ℝ) : ℝ :=
  Real.log w + (1 - w) + (1 - w) ^ 2 / 2 + (1 - w) ^ 3 / (3 * w)

private theorem hasDerivAt_suzukiInitialLogAux {w : ℝ} (hw : 0 < w) :
    HasDerivAt suzukiInitialLogAux ((w - 1) ^ 3 / (3 * w ^ 2)) w := by
  have hw0 : w ≠ 0 := ne_of_gt hw
  unfold suzukiInitialLogAux
  let g : ℝ → ℝ := fun x => 1 - x
  have hg : HasDerivAt g (-1) w := by
    change HasDerivAt ((fun _ : ℝ => (1 : ℝ)) - id) (-1) w
    exact ((hasDerivAt_const w 1).sub (hasDerivAt_id w)).congr_deriv (by norm_num)
  have h1 := (Real.hasDerivAt_log hw0).add hg
  have h2 := (hg.pow 2).div_const 2
  have h3 := (hg.pow 3).div
    ((hasDerivAt_id w).const_mul 3) (by positivity)
  have h := (h1.add h2).add h3
  have h' : HasDerivAt
      ((Real.log + g + fun x => (g x) ^ 2 / 2) +
          fun x => (g x) ^ 3 / (3 * x))
      ((w - 1) ^ 3 / (3 * w ^ 2)) w := by
    apply h.congr_deriv
    simp only [id_eq]
    dsimp [g]
    field_simp
    ring
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with x
  dsimp [g]

/-- A third-order one-sided logarithm minorant tailored to the initial
Suzuki interval. -/
theorem log_ge_initial_cubic {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    -((1 - w) + (1 - w) ^ 2 / 2 + (1 - w) ^ 3 / (3 * w)) ≤
      Real.log w := by
  have hcont : ContinuousOn suzukiInitialLogAux (Icc w 1) := by
    intro x hx
    have hx0 : 0 < x := hw.trans_le hx.1
    exact (hasDerivAt_suzukiInitialLogAux hx0).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ suzukiInitialLogAux (interior (Icc w 1)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_suzukiInitialLogAux (hw.trans hx.1)).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn suzukiInitialLogAux (Icc w 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc w 1) hcont hdiff
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_suzukiInitialLogAux (hw.trans hx.1)).deriv]
    have hcube : (x - 1) ^ 3 ≤ 0 := by
      have hxneg : x - 1 ≤ 0 := by linarith [hx.2]
      rw [pow_succ]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hxneg
    exact div_nonpos_of_nonpos_of_nonneg
      hcube (by positivity)
  have hH := hanti ⟨le_rfl, hw1⟩ ⟨hw1, le_rfl⟩ hw1
  unfold suzukiInitialLogAux at hH
  norm_num at hH
  linarith

private theorem quarter_tsum_ge_first_nine {t : ℝ} (ht : 0 ≤ t) :
    (∑ n ∈ Finset.range 9,
      (1 / ((n : ℝ) + 1 / 4) ^ 2) *
        (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t))) ≤
      ∑' n : ℕ,
        (1 / ((n : ℝ) + 1 / 4) ^ 2) *
          (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t)) := by
  let f : ℕ → ℝ := fun n =>
    (1 / ((n : ℝ) + 1 / 4) ^ 2) *
      (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t))
  have hsbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1 / 4) ^ 2) := by
    rw [show (fun n : ℕ => 1 / ((n : ℝ) + 1 / 4) ^ 2) =
        fun n : ℕ => 1 / |(n : ℝ) + 1 / 4| ^ (2 : ℝ) by
      funext n
      simp [sq_abs]]
    exact (Real.summable_one_div_nat_add_rpow (1 / 4) 2).mpr (by norm_num)
  have hs : Summable f := by
    exact Summable.of_nonneg_of_le
      (fun n => by
        dsimp [f]
        have he : Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
        positivity)
      (fun n => by
        dsimp [f]
        have hc : 0 ≤ 1 / ((n : ℝ) + 1 / 4) ^ 2 := by positivity
        have he0 : 0 ≤ Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) :=
          Real.exp_nonneg _
        nlinarith)
      hsbase
  exact hs.sum_le_tsum (Finset.range 9) fun n _ => by
    have he : Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    exact mul_nonneg (by positivity) (sub_nonneg.mpr he)

/-- The supplied nine-term quarter-lattice certificate reduces the entire
archimedean side to the finite rational polynomial above. -/
theorem suzukiPsiArchimedean_ge_initialPolynomialFactor {t : ℝ} (ht : 0 < t) :
    (Real.exp (t / 2) - 1) *
        suzukiInitialPolynomial (Real.exp (-t / 2)) ≤
      suzukiPsiArchimedean t := by
  let w : ℝ := Real.exp (-t / 2)
  have hw : 0 < w := by dsimp [w]; positivity
  have hw1 : w < 1 := by
    dsimp [w]
    rw [Real.exp_lt_one_iff]
    linarith
  have hwexp : Real.exp (t / 2) = 1 / w := by
    dsimp [w]
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have htlog : t = -2 * Real.log w := by
    have hlog : Real.log w = -t / 2 := by
      dsimp [w]
      rw [Real.log_exp]
    linarith
  have hexp : ∀ n : ℕ,
      Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) = w ^ (4 * n + 1) := by
    intro n
    dsimp [w]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  let finitePart : ℝ := ∑ n ∈ Finset.range 9,
    4 / ((4 * n + 1 : ℕ) : ℝ) ^ 2 * (1 - w ^ (4 * n + 1))
  have hfinite : finitePart ≤
      1 / 4 * (∑' n : ℕ,
        (1 / ((n : ℝ) + 1 / 4) ^ 2) *
          (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t))) := by
    have hpartial := quarter_tsum_ge_first_nine ht.le
    have hscaled := mul_le_mul_of_nonneg_left hpartial (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [Finset.mul_sum] at hscaled
    have hfiniteEq : finitePart =
        ∑ n ∈ Finset.range 9,
          1 / 4 * ((1 / ((n : ℝ) + 1 / 4) ^ 2) *
            (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t))) := by
      unfold finitePart
      apply Finset.sum_congr rfl
      intro n hn
      rw [hexp n]
      field_simp
      push_cast
      ring
    rw [hfiniteEq]
    exact hscaled
  have hD : (-27 / 5 : ℝ) <
      (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi := by
    linarith [digammaLogPi_mem_Ioo_rational.1]
  have hDmul : (-27 / 5 : ℝ) * (t / 2) ≤
      t / 2 * ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) := by
    have ht2 : 0 ≤ t / 2 := by positivity
    nlinarith
  have hlog := log_ge_initial_cubic hw hw1.le
  have hscaledLog :
      (27 / 5 : ℝ) *
          (-((1 - w) + (1 - w) ^ 2 / 2 + (1 - w) ^ 3 / (3 * w))) ≤
        (27 / 5) * Real.log w :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  have halgebra :
      (1 / w - 1) * suzukiInitialPolynomial w =
        4 * (1 / w + w - 2) +
          (27 / 5) *
            (-((1 - w) + (1 - w) ^ 2 / 2 + (1 - w) ^ 3 / (3 * w))) +
          finitePart := by
    unfold suzukiInitialPolynomial finitePart
    norm_num [Finset.sum_Icc_succ_top, Finset.sum_range_succ]
    field_simp
    ring
  rw [hwexp]
  rw [halgebra]
  rw [suzukiPsiArchimedean_eq_quarter_tsum ht.le]
  have hmiddle :
      4 * (1 / w + w - 2) +
          (27 / 5) *
            (-((1 - w) + (1 - w) ^ 2 / 2 + (1 - w) ^ 3 / (3 * w))) +
          finitePart ≤
        4 * (1 / w + w - 2) +
          t / 2 * ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) +
          1 / 4 * (∑' n : ℕ,
            (1 / ((n : ℝ) + 1 / 4) ^ 2) *
              (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t))) := by
    calc
      _ ≤ 4 * (1 / w + w - 2) +
          (27 / 5) * Real.log w + finitePart := by linarith
      _ = 4 * (1 / w + w - 2) +
          (-27 / 5) * (t / 2) + finitePart := by rw [htlog]; ring
      _ ≤ _ := by linarith
  rw [hwexp]
  exact hmiddle

/-- Uniform explicit lower bound for the archimedean Suzuki term on the
whole nonnegative half-line. -/
theorem suzukiPsiArchimedean_ge_exp_sub_one {t : ℝ} (ht : 0 ≤ t) :
    (151 / 20000 : ℝ) * (Real.exp (t / 2) - 1) ≤
      suzukiPsiArchimedean t := by
  rcases ht.eq_or_lt with rfl | htpos
  · rw [suzukiPsiArchimedean_eq_quarter_tsum (by norm_num)]
    norm_num
  · have hw0 : 0 ≤ Real.exp (-t / 2) := Real.exp_nonneg _
    have hw1 : Real.exp (-t / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have hP := suzukiInitialPolynomial_gt hw0 hw1
    have hfactor : 0 ≤ Real.exp (t / 2) - 1 := by
      rw [sub_nonneg, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    calc
      (151 / 20000 : ℝ) * (Real.exp (t / 2) - 1) ≤
          suzukiInitialPolynomial (Real.exp (-t / 2)) *
            (Real.exp (t / 2) - 1) :=
        mul_le_mul_of_nonneg_right hP.le hfactor
      _ = (Real.exp (t / 2) - 1) *
          suzukiInitialPolynomial (Real.exp (-t / 2)) := by ring
      _ ≤ suzukiPsiArchimedean t :=
        suzukiPsiArchimedean_ge_initialPolynomialFactor htpos

theorem suzukiPsi_pos_of_pos_le_log_two {t : ℝ}
    (ht0 : 0 < t) (ht2 : t ≤ Real.log 2) : 0 < suzukiPsi t := by
  have hlowerPos : 0 < (151 / 20000 : ℝ) * (Real.exp (t / 2) - 1) := by
    apply mul_pos (by norm_num)
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by positivity)
  have harch : 0 < suzukiPsiArchimedean t :=
    hlowerPos.trans_le (suzukiPsiArchimedean_ge_exp_sub_one ht0.le)
  rcases ht2.eq_or_lt with rfl | htlt
  · rw [suzukiPsi_eq_archimedean_sub_twoRamp le_rfl
      (Real.log_lt_log (by norm_num) (by norm_num))]
    ring_nf
    exact harch
  · rw [suzukiPsi_eq_archimedean_of_lt_log_two ht0.le htlt]
    exact harch

/-- The previously open compact initial condition is discharged by the
nine-term archimedean certificate. -/
theorem suzukiInitialNonnegative_proved : SuzukiInitialNonnegative := by
  intro t ht0 ht2
  rcases ht0.eq_or_lt with rfl | htpos
  · simp
  · exact (suzukiPsi_pos_of_pos_le_log_two htpos ht2).le

theorem suzukiPsi_pos_zero_to_log_three {t : ℝ}
    (ht0 : 0 < t) (ht3 : t ≤ Real.log 3) : 0 < suzukiPsi t := by
  by_cases ht2 : t ≤ Real.log 2
  · exact suzukiPsi_pos_of_pos_le_log_two ht0 ht2
  · exact suzukiPsi_pos_cell_two t (le_of_not_ge ht2) ht3

/-- With the compact initial interval now checked, the cell-margin
representation has no separate initial hypothesis.  This remains an
equivalence to an open infinite family, not a proof of RH. -/
theorem riemannHypothesis_iff_all_cellMargins :
    RiemannHypothesis ↔
      ∀ n : ℕ, 2 ≤ n → 0 ≤ suzukiCellMargin n := by
  rw [riemannHypothesis_iff_initial_and_all_cellMargins]
  simp only [suzukiInitialNonnegative_proved, true_and]

/-- Sparse Mangoldt-block version of the preceding equivalence. -/
theorem riemannHypothesis_iff_all_mangoldtBlockMargins :
    RiemannHypothesis ↔
      ∀ q r : ℕ, IsMangoldtBlock q r → 0 ≤ suzukiMangoldtBlockMargin q r := by
  rw [riemannHypothesis_iff_initial_and_all_mangoldtBlockMargins]
  simp only [suzukiInitialNonnegative_proved, true_and]

end RHGarden
