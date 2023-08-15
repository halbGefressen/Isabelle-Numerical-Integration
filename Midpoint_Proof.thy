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
  "midpoint_rule_comp f a b (Suc n) =
    midpoint_rule_comp f a (b - (b - a)/Suc n) n + midpoint_rule f (b - (b - a)/Suc n) b"
proof -
  have *: "midpoint_rule f (b - (b - a)/Suc n) b = (b - a)/(Suc n) * f (a + (2 * n + 1) * (b-a)/(Suc n)/2)"
    unfolding midpoint_rule_def by (auto simp: algebra_simps divide_simps)

  let ?rest = "(b - a)/(Suc n) * f (a + (2 * real n + 1) * (b - a)/(Suc n)/2)"
  have "((b-a) / Suc n) = (n * (b-a) / Suc n) / n" using \<open>n>0\<close> by simp
  also have "... = (Suc n * (b-a) - (b-a)) / Suc n / n" by (simp add: algebra_simps)
  also have "... = (b - ((b-a) / Suc n) - a) / n" by (simp add: diff_divide_distrib)
  finally have **: "(b - ((b-a) / Suc n) - a) / n = ((b-a) / Suc n) " ..
  have "midpoint_rule_comp f a b (Suc n) = (let h = (b - a)/(Suc n)
    in h * (\<Sum>k\<leftarrow>[0..<n]. f (a + (2 * k + 1) * h/2)) + h * f (a + (2 * real n + 1) * h/2))"
    unfolding midpoint_rule_comp_def by (simp add: algebra_simps)
  also have "... = (let h = (b - ((b-a) / Suc n) - a) / n
    in h * (\<Sum>k\<leftarrow>[0..<n]. f (a + (2 * k + 1) * h/2))) + ?rest" by (simp cong: **)
  finally show ?thesis unfolding midpoint_rule_comp_def * by (simp add: algebra_simps)
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
    have [arith]: "a \<le> ?mid" and [arith]: "?mid \<le> b"
      by simp (smt (z3) a_le_b field_sum_of_halves)
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
  define h where "h = (b-a)/Suc n"
  define b' where "b' = (b - h)"
  have [simp]:"a \<le> b'" and [simp]:"b' \<le> b" and cong0: "n * h = b' - a" unfolding h_def b'_def
    using \<open>a \<le> b\<close> \<open>n > 0\<close> by (auto simp: divide_simps algebra_simps)
  have [simp]: "h \<ge> 0" unfolding h_def
    using \<open>a \<le> b\<close> \<open>n > 0\<close> by (auto simp: divide_simps)
  let ?Mn = "midpoint_rule_comp f a b' n" and ?En = "k * (n*h) ^ 3 / real (24 * n\<^sup>2)"
  have subset1: "{a..b'} \<subseteq> {a..b}"
   and subset2: "{b'..b} \<subseteq> {a..b}" using \<open>a \<le> b\<close> by auto

  have cong1: "h = b - b'" unfolding b'_def by argo
  let ?M = "midpoint_rule f b' b" and ?e = "k * (h ^ 3) / 24"
  have err1: "\<bar>(\<integral>x\<in>{a..b'}. f x \<partial>lborel) - ?Mn\<bar> \<le> ?En" unfolding cong0 using \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> \<bar>f'' x\<bar> \<le> k\<close> subset1
    by (subst Suc.IH[OF DERIV_subset[OF Suc.prems(1)] DERIV_subset[OF Suc.prems(2)]
          continuous_on_subset[OF Suc.prems(3)] _ \<open>a \<le> b'\<close> \<open>0 < n\<close>], blast+)
  moreover have err2: "\<bar>(\<integral>x\<in>{b'..b}. f x \<partial>lborel) - ?M\<bar> \<le> ?e" using Suc.prems(4) subset2 unfolding cong1
    by (subst midpoint_approx_error[OF DERIV_subset[OF Suc.prems(1) subset2] DERIV_subset[OF Suc.prems(2) subset2]
          continuous_on_subset[OF Suc.prems(3) subset2] _ \<open>b' \<le> b\<close>], blast+)
  ultimately have **: "\<bar>(\<integral>x\<in>{a..b}. f x \<partial>lborel) - (?Mn + ?M)\<bar> \<le> ?En + ?e"
    by (subst real_set_integral_combine(1)[of a b f b',
          OF borel_integrable_atLeastAtMost'[OF DERIV_continuous_on[OF Suc.prems(1)]]
          \<open>a \<le> b'\<close> \<open>b' \<le> b\<close>, symmetric], argo)
  have combined_approx: "midpoint_rule_comp f a b' n + midpoint_rule f b' b = midpoint_rule_comp f a b (Suc n)"
    unfolding b'_def h_def using midpoint_IH[OF \<open>0 < n\<close>, of f a b] by (simp add: b'_def h_def)
  {
        have "?En + ?e = (k / 24) * ((n * h) ^ 3 / (n ^ (3-1)) + (h ^ 3))"
          by (auto simp: algebra_simps)
        also have "... = (k / 24) * (b-a)^3 / ((Suc n)^(3-1))"
          using error_cong[of "b-a" n 3, OF _ _ _ \<open>0 < n\<close>] h_def \<open>0 \<le> h\<close> \<open>a \<le> b\<close> by auto
        finally have "?En + ?e = k * (b-a)^3 / (24 * (Suc n)^2)" unfolding h_def by simp
    }
  with combined_approx show ?case using ** by simp
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
