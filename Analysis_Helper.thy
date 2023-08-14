theory Analysis_Helper
  imports "HOL-Analysis.Analysis"
begin

lemma real_set_integral_combine:
  assumes \<open>set_integrable lborel {a..b} (f::real\<Rightarrow>real)\<close>
      and \<open>(a::real) \<le> c\<close>
      and \<open>c \<le> b\<close>
  shows \<open>(\<integral>x\<in>{a..c}. f x \<partial>lborel) + (\<integral>x\<in>{c..b}. f x \<partial>lborel) = \<integral>x\<in>{a..b}. f x \<partial>lborel\<close>
    and \<open>set_integrable lborel {a..c} f\<close>
    and \<open>set_integrable lborel {c..b} f\<close>
proof goal_cases
  show setintegr1: \<open>set_integrable lborel {a..c} f\<close>
   and setintegr2: \<open>set_integrable lborel {c..b} f\<close> using assms set_integrable_subset by fastforce+
  then show \<open>(\<integral>x\<in>{a..c}. f x \<partial>lborel) + (\<integral>x\<in>{c..b}. f x \<partial>lborel) = \<integral>x\<in>{a..b}. f x \<partial>lborel\<close>
    using assms AE_lborel_singleton[of c] by (auto intro!: set_integral_Un_AE[symmetric]
      cong: ivl_disj_un_two_touch(4)[OF assms(2) assms(3), symmetric])
qed


lemma set_integral_by_parts:
  fixes f g F G::"real \<Rightarrow> real"
  assumes [arith]: "a \<le> b"
  assumes cont_f[intro]: "continuous_on {a..b} f"
  assumes cont_g[intro]: "continuous_on {a..b} g'"
  assumes [intro]: "\<And>x. (F has_real_derivative f x) (at x within {a..b})"
  assumes [intro]: "\<And>x. (g has_real_derivative g' x) (at x within {a..b})"
  shows "(\<integral>x\<in>{a..b}. (f x * g x) \<partial>lborel)
            =  F b * g b - F a * g a - (\<integral>x\<in>{a..b}. (F x * g' x) \<partial>lborel)"
proof-
  have int: "\<integral>x\<in>{a..b}. (f x * g x + F x * g' x) \<partial>lborel = F b * g b - F a * g a"
    unfolding set_lebesgue_integral_def apply (intro integral_FTC_Icc[OF assms(1)])
        using DERIV_mult[OF assms(4) assms(5)] DERIV_continuous_on assms
          by (auto 5 0 intro!: continuous_intros integral_FTC_Icc[OF assms(1)]
            cong: has_real_derivative_iff_has_vector_derivative simp: mult.commute)
  have integr_left:  "set_integrable lborel {a..b} (λx. f x * g x)"
   and integr_right: "set_integrable lborel {a..b} (λx. F x * g' x)"
    using cont_f cont_g DERIV_continuous_on
    by (auto intro!: borel_integrable_atLeastAtMost' continuous_intros)
  with set_integral_add(2)[OF this] int show ?thesis by linarith
qed

lemma set_integral_abs_bound[arith]:
  fixes f::"real\<Rightarrow>real"
    and a b :: real
    shows "\<bar>\<integral>x\<in>{a..b}. f x \<partial>lborel\<bar> \<le> \<integral>x\<in>{a..b}. \<bar>f x\<bar> \<partial>lborel"
unfolding set_lebesgue_integral_def by (simp cong: abs_mult_pos')

end
