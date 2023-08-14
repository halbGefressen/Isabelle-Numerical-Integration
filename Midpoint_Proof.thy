theory Midpoint_Proof
  imports "Analysis_Helper"
begin

definition midpoint_rule :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  \<open>midpoint_rule f a b = (b - a) * f ((a + b)/2)\<close>

definition midpoint_rule_comp :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  \<open>midpoint_rule_comp f a b n = (let h = (b - a)/n
  in h * (\<Sum>k\<leftarrow>[0..<n]. f (a + (2 * k + 1) * h / 2)))\<close>

lemma [cong]:"midpoint_rule_comp f a b 1 = midpoint_rule f a b"
proof -
    have [cong]:"a + (b-a)/2 = (a + b)/2" by argo
    then show ?thesis unfolding midpoint_rule_def midpoint_rule_comp_def by simp
qed


lemma midpoint_IH:
  assumes "n > 0" shows
  "midpoint_rule_comp f a b (Suc n) = midpoint_rule_comp f a (b - (b - a)/Suc n) n
    + (b - a)/(Suc n) * f (a + (2 * n + 1) * (b-a)/(Suc n)/2)"
proof -
  let ?rest = "(b - a)/(Suc n) * f (a + (2 * real n + 1) * (b - a)/(Suc n)/2)"
  have "((b-a) / Suc n) = (n * (b-a) / Suc n) / n" using \<open>n>0\<close> by simp
  also have "... = (Suc n * (b-a) - (b-a)) / Suc n / n" by (simp add: algebra_simps)
  also have "... = (b - ((b-a) / Suc n) - a) / n" by (simp add: diff_divide_distrib)
  finally have *: "(b - ((b-a) / Suc n) - a) / n = ((b-a) / Suc n) " ..
  have "midpoint_rule_comp f a b (Suc n) = (let h = (b - a)/(Suc n)
    in h * (\<Sum>k\<leftarrow>[0..<n]. f (a + (2 * k + 1) * h/2)) + h * f (a + (2 * real n + 1) * h/2))"
    unfolding midpoint_rule_comp_def by (simp add: algebra_simps)
  also have "... = (let h = (b - ((b-a) / Suc n) - a) / n
    in h * (\<Sum>k\<leftarrow>[0..<n]. f (a + (2 * k + 1) * h/2))) + ?rest" by (simp cong: *)
  finally show ?thesis unfolding midpoint_rule_comp_def by (simp add: algebra_simps)
qed



lemma double_integration_by_parts:
  fixes f::"real \<Rightarrow> real"
  assumes deriv1: "\<And>x. (f has_real_derivative f' x) (at x within {a..b})"
      and deriv2: "\<And>x. (f' has_real_derivative f'' x) (at x within {a..b})"
      and cont_f'': "continuous_on {a..b} f''"
      and f''_bound: "\<And>x. x \<in> {a..b} \<Longrightarrow> (k::real) \<ge> abs(f'' x)"
      and a_le_b[arith]: "a \<le> b"
    shows "\<And>c. (\<integral>x\<in>{a..b}. f x \<partial>lborel)
        = (b - c) * f b - (a - c) * f a
          - ((b - c) * (b - c) / 2 * f' b - (a - c) * (a - c) / 2 * f' a)
          + (\<integral> x\<in>{a..b}. ((x - c) * (x - c) / 2 *f'' x) \<partial>lborel)"
proof - (*front part*)
      fix c::real
      have [cong]:"\<And>x. (4 * x - 4 * c) / 4 = (x-c)" by simp
      have deriv'_F:"(\<And>x. ((λx. (x - c) * (x-c) / 2) has_real_derivative (λx. x - c) x) (at x within {a..b}))"
        using DERIV_divide[OF DERIV_mult[OF DERIV_diff[OF DERIV_ident DERIV_const[of c]]
                                            DERIV_diff[OF DERIV_ident DERIV_const[of c]]]
                              DERIV_const[of "2"]] by simp
      have part1: "(\<integral>x\<in>{a..b}. f x \<partial>lborel) = (b - c) * f b - (a - c) * f a - (\<integral>x\<in>{a..b}. ((x - c) * f' x) \<partial>lborel)"
        using set_integral_by_parts[OF a_le_b continuous_on_const DERIV_continuous_on[OF deriv2]
          DERIV_diff[OF DERIV_ident DERIV_const[of c]] deriv1] by simp
      with set_integral_by_parts[OF a_le_b continuous_on_diff[OF continuous_on_id continuous_on_const] cont_f'' deriv'_F deriv2]
      show "(\<integral>x\<in>{a..b}. f x \<partial>lborel) = (b - c) * f b - (a - c) * f a
          - ((b - c) * (b - c) / 2 * f' b - (a - c) * (a - c) / 2 * f' a)
          + (\<integral> x\<in>{a..b}. ((x - c) * (x - c) / 2 *f'' x) \<partial>lborel)" apply (subst part1) by argo
qed


theorem midpoint_approx_error:
  fixes f::"real \<Rightarrow> real"
  assumes deriv1: "\<And>x. (f has_real_derivative f' x) (at x within {a..b})"
      and deriv2: "\<And>x. (f' has_real_derivative f'' x) (at x within {a..b})"
      and cont_f'': "continuous_on {a..b} f''"
      and f''_bound: "\<And>x. x \<in> {a..b} \<Longrightarrow> (k::real) \<ge> ¦f'' x¦"
      and a_le_b[arith]: "a \<le> b"
    shows "\<bar>(\<integral>x\<in>{a..b}. f x \<partial>lborel) - midpoint_rule f a b \<bar> \<le> k * ((b - a) ^ 3) / 24"
proof -
    let ?mid = "a + (b-a)/2"
    have [arith]: "a \<le> ?mid" and [arith]: "?mid \<le> b" using a_le_b field_sum_of_halves by simp (smt (z3) a_le_b field_sum_of_halves)
    have lower: "(\<integral>x\<in>{a..?mid}. f x \<partial>lborel)
        = (b-a)/2 * f ?mid - ((b-a)/2) * ((b-a)/2) / 2 * f' ?mid + (\<integral> x\<in>{a..?mid}. ((x - a) * (x - a) / 2 *f'' x) \<partial>lborel)"
        by (subst double_integration_by_parts[of f f' a ?mid f'' k a],
          auto simp: f''_bound intro: continuous_on_subset[OF cont_f'']
          DERIV_subset[OF deriv2] DERIV_subset[OF deriv1])

    have upper: "(\<integral>x\<in>{?mid..b}. f x \<partial>lborel)
        = (b-a)/2 * f ?mid + ((b-a)/2) * ((b-a)/2) / 2 * f' ?mid + (\<integral>x\<in>{?mid..b}. ((x - b) * (x - b) / 2 * f'' x)\<partial>lborel)"
        by (subst double_integration_by_parts[of f f' ?mid b f'' k b],
        auto simp: algebra_simps f''_bound intro!: continuous_on_subset[OF cont_f'']
          DERIV_subset[OF deriv2] DERIV_subset[OF deriv1])
    {
        have "\<bar> \<integral>x\<in>{a..?mid}. ((x - a) * (x - a) / 2 * f'' x) \<partial>lborel\<bar> \<le> \<integral>x\<in>{a..?mid}. \<bar>(x - a) * (x - a) / 2 * f'' x\<bar> \<partial>lborel"
          by presburger
        also have "... \<le> \<integral>x\<in>{a..?mid}. ((x - a) * (x - a) / 2 * k) \<partial>lborel"
          apply (intro set_integral_mono) using continuous_on_subset[OF cont_f'']
          by (auto 1 0 intro!: continuous_intros borel_integrable_atLeastAtMost' cong: abs_mult
            simp: f''_bound mult_left_mono)
        also have "... = k/2 * (\<integral>x\<in>{a..?mid}. ((x - a)^2) \<partial>lborel)" by (simp add: power2_eq_square)
        also have "... = k * ((b-a)/2)^3 / 6" unfolding set_lebesgue_integral_def apply (subst integral_FTC_Icc)
          using DERIV_mult[OF DERIV_const [of "1/3"] DERIV_power[OF DERIV_diff[OF DERIV_ident DERIV_const[of a]], of 3]]
            by (auto intro!: continuous_intros  borel_integrable_atLeastAtMost'
              cong: has_real_derivative_iff_has_vector_derivative[symmetric])
        finally have "\<bar>\<integral>x\<in>{a..?mid}. ((x - a) * (x - a) / 2 * f'' x) \<partial>lborel\<bar> \<le> k * ((b-a))^3/48" by (simp add: power_divide)
    }
          note e1 = this
    {
        have [cong]:"-((a + (b - a) / 2 - b) ^ 3) = (b - (a + (b - a) / 2)) ^ 3" and *: "b - ?mid = (b-a)/2"
          by (auto simp: power3_eq_cube power2_eq_square right_diff_distrib') argo+
        have "\<bar>\<integral>x\<in>{?mid..b}. ((x - b) * (x - b) / 2 * f'' x) \<partial>lborel\<bar> \<le> \<integral> x\<in>{?mid..b}. \<bar>(x - b) * (x - b) / 2 * f'' x\<bar> \<partial>lborel"
          by presburger
        also have "... = \<integral> x\<in>{?mid..b}. ((x - b) * (x - b) / 2 * \<bar>f'' x\<bar>) \<partial>lborel"
          by (auto cong: abs_mult)
        also have "... \<le> \<integral> x\<in>{?mid..b}. ((x - b) * (x - b) / 2 * k) \<partial>lborel"
          apply (intro set_integral_mono) using continuous_on_subset[OF cont_f'']
          by (auto 1 0 intro!: continuous_intros borel_integrable_atLeastAtMost' cong: abs_mult
            simp: f''_bound mult_left_mono)
        also have "... = k/2 * (\<integral>x\<in>{?mid..b}. ((x - b)^2) \<partial>lborel)" by (simp add: mult.commute power2_eq_square)
        also have "... = k/6 * (b-?mid)^3" unfolding set_lebesgue_integral_def apply (subst integral_FTC_Icc)
          using DERIV_mult[OF DERIV_const [of "1/3"] DERIV_power[OF DERIV_diff[OF DERIV_ident DERIV_const[of b]], of 3]]
            by (auto intro!: continuous_intros  borel_integrable_atLeastAtMost'
              cong: has_real_derivative_iff_has_vector_derivative[symmetric])
        finally have "\<bar>\<integral>x\<in>{?mid..b}. ((x - b) * (x - b) / 2 * f'' x)\<partial>lborel\<bar> \<le> k * (b-a)^3/48" unfolding * by (simp add: power_divide)
    }
    with e1 show ?thesis unfolding midpoint_rule_def lower upper
      real_set_integral_combine(1)[OF borel_integrable_atLeastAtMost'[OF DERIV_continuous_on[OF deriv1]] \<open>a \<le> ?mid\<close> \<open>?mid \<le> b\<close>, symmetric]
      by argo
qed

corollary midpoint_comp_approx_error:
  fixes f::"real \<Rightarrow> real"
  assumes deriv1: "\<And>x. (f has_real_derivative f' x) (at x within {a..b})"
      and deriv2: "\<And>x. (f' has_real_derivative f'' x) (at x within {a..b})"
      and cont_f'': "continuous_on {a..b} f''"
      and f''_bound: "\<And>x. x \<in> {a..b} \<Longrightarrow> (k::real) \<ge> abs(f'' x)"
      and a_le_b[arith]: "a \<le> b"
      and n_nonzero[arith]: "N > 0"
    shows "\<bar>(\<integral>x\<in>{a..b}. f x \<partial>lborel) - midpoint_rule_comp f a b N\<bar> \<le> k * ((b - a) ^ 3) / (24*N\<^sup>2)"
proof (insert n_nonzero, insert assms, induction N arbitrary: a b rule: nat_induct_non_zero)
  case (Suc n)
  have integr: "set_integrable lborel {a..b} f"
    by (rule borel_integrable_atLeastAtMost'[OF DERIV_continuous_on[OF Suc.prems(1)]])
  let ?Mn = "midpoint_rule_comp f a (b - (b - a) / real (Suc n)) n"
  let ?En = "k * (b - (b - a) / real (Suc n) - a) ^ 3 / real (24 * n\<^sup>2)"
  let ?h = "(b - a)/Suc n"
  let ?b = "(b - (b - a)/Suc n)"
  have \<open>n \<noteq> 0\<close> using \<open>n > 0\<close> by simp
  have [arith]: "(1 + real n) \<ge> 1" using Suc by auto
  have subset: "{a..?b} \<subseteq> {a..b}" using Suc by simp
  have *: "(\<integral>x\<in>{a..b}. f x \<partial>lborel) =
    (\<integral>x\<in>{a..(b - (b - a)/Suc n)}. f x \<partial>lborel) + (\<integral>x\<in>{(b - (b - a)/Suc n)..b}. f x \<partial>lborel)"
  by (subst real_set_integral_combine[OF integr], auto simp: algebra_simps Suc.prems(5),
      metis Suc.prems(5) scaling_mono \<open>1 \<le> 1 + real n\<close>  mult_cancel_right1 zero_less_one_class.zero_le_one)

  note ih1 = DERIV_subset[OF Suc.prems(1) subset]
  note ih2 = DERIV_subset[OF Suc.prems(2) subset]
  note ih3 = continuous_on_subset[OF Suc.prems(3) subset]
  have ih4: "(\<And>x. x \<in> {a..?b} \<Longrightarrow> \<bar>f'' x\<bar> \<le> k)" using Suc.prems(4) subset by blast
  have ih5: "a \<le> ?b" by (auto simp: algebra_simps Suc.prems, metis Suc.prems(5)
    scaling_mono \<open>1 \<le> 1 + real n\<close>  mult_cancel_right1 zero_less_one_class.zero_le_one)
  have rest1: "(\<And>x. (f has_real_derivative f' x) (at x within {?b..b}))" and
       rest2: "(\<And>x. (f' has_real_derivative f'' x) (at x within {?b..b}))" and
       rest3: "continuous_on {?b..b} f''" and
       rest4: "(\<And>x. x \<in> {?b..b} \<Longrightarrow> \<bar>f'' x\<bar> \<le> k)" and
       rest5: "?b \<le> b"
    using Suc.prems
    by ((meson DERIV_subset atLeastatMost_subset_iff dual_order.refl ih5)+,
         meson atLeastatMost_subset_iff continuous_on_subset ih5 verit_comp_simplify1(2),
         meson atLeastAtMost_iff ih5 order.trans, simp) (*yeah it's not beautiful. nobody asked though*)
  let ?mn = "?h * f (?b + ?h / 2)"
  let ?e = "k * (?h ^ 3) / 24"
  have 1:"?mn = midpoint_rule f ?b b" unfolding midpoint_rule_def by argo
  have err1: "\<bar>(\<integral>x\<in>{a..?b}. f x \<partial>lborel) - ?Mn\<bar> \<le> ?En"
    using Suc.IH[OF ih1 ih2 ih3 ih4 ih5 \<open>n > 0\<close>] by auto
  have err2: "\<bar>(\<integral>x\<in>{?b..b}. f x \<partial>lborel) - midpoint_rule f ?b b\<bar> \<le> ?e"
     using midpoint_approx_error[OF rest1 rest2 rest3 rest4 rest5] by simp
  from err1 err2 *
  have **: "\<bar>(\<integral>x\<in>{a..b}. f x \<partial>lborel) - (?Mn + midpoint_rule f ?b b)\<bar> \<le> ?En + ?e" by argo
  have "b = a + (Suc n) * ?h" by simp
  then have "b - ?h = a + n * ?h" by (auto simp: algebra_simps, argo)
  then have "(a + (2 * real n + 1) * ?h / 2) = (b - ?h + ?h / 2)" by argo
  then have "?Mn + midpoint_rule f ?b b = midpoint_rule_comp f a b (Suc n)" using midpoint_IH[OF \<open>0 < n\<close>, of f a b] 1 by simp
  moreover have "?En + ?e = k * (b-a)^3 / (24 * (Suc n)^2)" proof -
    have "(b - (b - a) / (1 + real n) - a)
      = ((b - a) * (1 + real n) / (1 + real n) - (b - a) / (1 + real n))" by simp
    then have "(b - (b - a) / (1 + real n) - a) = ((b - a) * (real n)) / (1 + real n)" by argo
    then have "(b - (b - a) / real (Suc n) - a) ^ 3 / real (24 * n\<^sup>2)
      = ((b - a) ^3 * (real n)^3) / ((1 + real n) ^ 3 * 24 * (real n)\<^sup>2)" by (simp add: power_divide power_mult_distrib)
    also have "... = ((b - a) ^3 * (real n)^2 * real n) / ((1 + real n) ^ 3 * 24 * (real n)\<^sup>2)" by algebra
    finally have "(b - (b - a) / real (Suc n) - a) ^ 3 / real (24 * n\<^sup>2)
      = ((b - a) ^3 *  real n) / ((1 + real n) ^ 3 * 24)" by simp
    then have "(b - (b - a) / real (Suc n) - a) ^ 3 / real (24 * n\<^sup>2) + ((b - a) / real (Suc n)) ^ 3 / 24
      = ((b - a) ^3 *  real n) / ((1 + real n) ^ 3 * 24) + (b - a)^3 / (24 * (1 + (real n)) ^ 3)"
      by (simp add: power_divide)
    also have "... = (((b - a) ^3 *  real n) + (b-a)^3)/(24 * (1 + real n) ^ 3)" by (simp add: add_divide_distrib)
    also have "... = ((b - a) ^3 * (1 +  real n))/(24 * (1 + real n) ^ 3)" by argo
    also have "... = ((b - a) ^3 * (1 +  real n))/(24 * ((1 + real n) * (1 + real n) ^ 2))"
      by (metis (mono_tags, opaque_lifting) eval_nat_numeral(3) power_Suc)
    also have "... = ((b - a) ^3)/(24 * ((Suc n) ^ 2))" by simp
    finally show ?thesis by algebra
  qed
  ultimately show ?case using ** by simp
qed (insert midpoint_approx_error, fastforce)


corollary midpoint_exact_linear:
  fixes f :: "real \<Rightarrow> real"
  fixes a b m t :: "real"
  assumes [simp, symmetric]:"f = (λx. m * x + t)"
    and [arith]:"a \<le> b"
    and [arith]:"n > 0"
    shows "(\<integral>x\<in>{a..b}. f x \<partial>lborel) = midpoint_rule_comp f a b n"
proof -
  have *: "⋀x. (f has_real_derivative m) (at x within {a..b})" unfolding assms(1) using
   DERIV_add[OF DERIV_mult[OF DERIV_const[of m] DERIV_ident] DERIV_const[of t]] by simp
  have **: "⋀x. ((λx. m) has_real_derivative 0) (at x within {a..b})" using DERIV_const by blast
  have "\<bar>(\<integral>x\<in>{a..b}. f x \<partial>lborel) - midpoint_rule_comp f a b n\<bar> \<le> 0 * ((b - a) ^ 3) / (24*n\<^sup>2)"
     by (intro midpoint_comp_approx_error[OF * ** _ _ assms(2) assms(3)], auto)
  then show ?thesis by simp
qed


end
