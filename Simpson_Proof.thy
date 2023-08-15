theory Simpson_Proof
  imports Analysis_Helper
begin


definition simpson_rule :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  \<open>simpson_rule f a b = (b - a) / 6 * (f a + 4 * f ((b + a)/2) + f b)\<close>


(*Alternate definition: For input n, there are 2n subintervals. This makes more sense because
 *the simpson rule is not defined for an uneven amount of subintervals.*)
definition simpson_rule_comp :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  \<open>simpson_rule_comp f a b n = (let H = (b - a)/n
  in H/6 * (f a + f b + 2 * (\<Sum>k\<leftarrow>[1..<n]. f (a + k * H)) + 4 * (\<Sum>k\<leftarrow>[0..<n]. f (a + H/2 + k * H))))\<close>


lemma simpson_rule_sum_eq_simpson_rule_comp:
  assumes "n > 0"
      shows "simpson_rule_comp f a b n
        = (let H = (b-a)/n in (\<Sum>k\<leftarrow>[0..<n]. simpson_rule f (a + k * H) (a + (Suc k) * H)))"
proof (insert assms, induction n arbitrary: a b rule: nat_induct_non_zero)
  case 1 have [simp]:"a + (b-a) / 2 = (a+b)/2" by argo
  then show ?case unfolding simpson_rule_comp_def simpson_rule_def by simp
next
  case (Suc n)
  let ?Hs = "(b-a)/(Suc n)"
  {
    have "((b-a) / Suc n) = 1 * ((b-a) / Suc n)" by argo
    also have "... =  (n * (b-a) / Suc n) / n" using \<open>n > 0\<close> by simp
    also have "... =  (Suc n * (b-a) - (b-a)) / Suc n / n" by (simp add: algebra_simps)
    also have "... =  (b - ((b-a) / Suc n) - a) / n" by (simp add: diff_divide_distrib)
    finally have "(b - ?Hs - a) / n = ?Hs" by simp
  }
  note cong0 = this
  have cong1: "a + (Suc n * ?Hs) = b" by simp
  then have cong2: "a + n * ?Hs = b - ?Hs" by (auto simp: algebra_simps divide_simps)
  have "\<And>x::real. Suc n * x = n * x + x" by (simp add: distrib_left mult.commute)
  note cong3 = this[of ?Hs]

  (*the transitive reasoner (also, finally) is somehow broken on step d. this is a fix*)
  have a: "(let H = (b-a)/(Suc n) in (\<Sum>k\<leftarrow>[0..<Suc n]. simpson_rule f (a + k * H) (a + (Suc k) * H)))
    = (\<Sum>k\<leftarrow>[0..<n]. simpson_rule f (a + k * ((b - ?Hs - a) / n)) (a + (Suc k) * ((b - ?Hs - a) / n)))
    + simpson_rule f (a + n * ?Hs) (a + (Suc n) * ?Hs)" by (simp cong: cong0)
  have b: "... = (\<Sum>k\<leftarrow>[0..<n]. simpson_rule f (a + k * ((b - ?Hs - a) / n)) (a + (Suc k) * ((b - ?Hs - a) / n)))
    + simpson_rule f (a + n * ?Hs) (a + (Suc n) * ?Hs)" by (simp cong: times_divide_eq_right cong0)
  have c: "... = simpson_rule_comp f a (b - ?Hs) n + simpson_rule f (a + real n * ?Hs) (a + (Suc n) * ?Hs)" by (simp cong: Suc.IH)
  have "... = ?Hs / 6 * (f a + f (b - ?Hs) + 2 * (\<Sum>k\<leftarrow>map real [1..<n]. f (a + k * ?Hs))
    + 4 * (\<Sum>k\<leftarrow>map real[0..<n]. f (a + ?Hs / 2 + k * ?Hs))) + ?Hs/6 * (f (a + n * ?Hs) + 4 * f ((2 * b - ?Hs) / 2) + f b)"
    unfolding simpson_rule_comp_def simpson_rule_def by (simp cong: cong0 cong2)
  also have "... = ?Hs / 6 *
    (f a + f (b - ?Hs)
    + 2 * (\<Sum>k\<leftarrow>map real [1..<n]. f (a + k * ?Hs))
    + 4 * (\<Sum>k\<leftarrow>map real [0..<n]. f (a + ?Hs / 2 + k * ?Hs))
    + f (a + n * ?Hs) + 4 * f (b - ?Hs / 2) + f b)" by argo
  also have "... = ?Hs / 6 *
    (f a + f (b - ?Hs)
    + 2 * (\<Sum>k\<leftarrow>map real [1..<n]. f (a + k * ?Hs))
    + 4 * (\<Sum>k\<leftarrow>map real [0..<n]. f (a + ?Hs / 2 + k * ?Hs))
    + f (a + n * ?Hs) + 4 * f (a + (Suc n * ?Hs) - ?Hs / 2) + f b)" by (simp add: cong1)
  also have "... = ?Hs / 6 *
    (f a + f (b - ?Hs)
    + 2 * (\<Sum>k\<leftarrow>map real [1..<n]. f (a + k * ?Hs))
    + 4 * (\<Sum>k\<leftarrow>map real [0..<n]. f (a + ?Hs / 2 + k * ?Hs))
    + f (a + n * ?Hs) + 4 * f (a + (n * ?Hs) + ?Hs / 2) + f b)"
    unfolding cong3 by argo
  also have "... = ?Hs / 6 *
    (f a + 2 * f (a + n * ?Hs)
    + 2 * (\<Sum>k\<leftarrow>map real [1..<n]. f (a + k * ?Hs))
    + 4 * (\<Sum>k\<leftarrow>map real [0..<n]. f (a + ?Hs / 2 + k * ?Hs))
    + 4 * f (a + (n * ?Hs) + ?Hs / 2) + f b)" by (simp cong: cong2)
  also have "... = ?Hs / 6 *
    (f a
    + 2 * ((\<Sum>k\<leftarrow>map real [1..<n]. f (a + k * ?Hs))
          + f (a + real n * ?Hs))
    + 4 * ((\<Sum>k\<leftarrow>map real [0..<n]. f (a + ?Hs / 2 + k * ?Hs))
           + f (a + ?Hs / 2 + (n * ?Hs))) + f b)" by argo
  finally have "simpson_rule_comp f a (b - ?Hs) n + simpson_rule f (a + real n * ?Hs) (a + (Suc n) * ?Hs)
    = simpson_rule_comp f a b (Suc n)" unfolding simpson_rule_comp_def using \<open>n > 0\<close> by simp
  then show ?case by ((subst a c)+) simp
qed


lemma [cong]:"simpson_rule_comp f a b 1 = simpson_rule f a b"
  using simpson_rule_sum_eq_simpson_rule_comp[OF zero_less_Suc[of 0]] by simp



lemma poly1_derivs:
  fixes a b :: real
  assumes [arith]:"a \<le> b"
  shows "\<And>x. ((λx. (x-a)^3 * (x - (a + 2*b)/3)) has_real_derivative (λx. (x-a)^2 * (4*x -2*a -2*b)) x) (at x within {a..b})"
  and "\<And>x. ((λx. (x-a)^2 * (4*x -2*a -2*b)) has_real_derivative (λx. 4*(x-a)*(3*x-2*a-b)) x) (at x within {a..b})"
  and "\<And>x. ((λx. 4*(x-a)*(3*x-2*a-b)) has_real_derivative (λx. 4*(6*x - 5*a - b)) x) (at x within {a..b})"
  and "\<And>x. ((λx. 4*(6*x - 5*a - b)) has_real_derivative 24) (at x within {a..b})"
proof goal_cases
  case (1 x)
  have "((\<lambda>x. (x - a) ^ 3 * (x - (a + 2 * b) / 3)) has_real_derivative
   3 * ((x - a) ^ (2)) * (x - (a + 2 * b) / 3) + (x - a) ^ 3)
   (at x within {a..b})"
  using DERIV_mult[OF DERIV_power[OF DERIV_diff[OF DERIV_ident DERIV_const[of a]], of 3]
                      DERIV_diff[OF DERIV_ident DERIV_const[of "(a + 2*b)/3"]]] by simp
  moreover have "3 * ((x - a) ^ (2)) * (x - (a + 2 * b) / 3) + (x - a) ^ 3 = (x-a)^2 * (4*x - 2*a - 2*b)" by algebra
  ultimately show ?case by simp
next
  case (2 x)
    have "((λx. (x-a)^2 * (4*x -2*a -2*b)) has_real_derivative 2 * (x-a) * (4*x - 2*a - 2*b) + 4*(x-a)^2) (at x within {a..b})"
    using DERIV_mult[OF DERIV_power[OF DERIV_diff[OF DERIV_ident DERIV_const[of a]], of 2]
                      DERIV_diff[OF DERIV_diff[OF DERIV_mult[OF DERIV_const[of 4] DERIV_ident]
         DERIV_const[of "2*a"]] DERIV_const[of "2*b"]]] by simp
    moreover have "4*(x-a)*(3*x-2*a-b) = 2 * (x-a) * (4*x - 2*a - 2*b) + 4*(x-a)^2" by algebra
  ultimately show ?case by simp
next
  case (3 x)
  then show ?case using DERIV_mult[OF DERIV_mult[OF DERIV_const[of 4] DERIV_diff[OF DERIV_ident DERIV_const[of a]]]
            DERIV_diff[OF DERIV_diff[OF DERIV_mult[OF DERIV_const[of 3] DERIV_ident]
         DERIV_const[of "2*a"]] DERIV_const[of "b"]]] by (simp add: algebra_simps)
next
  case (4 x) then show ?case using DERIV_mult[OF DERIV_const[of 4] DERIV_diff
    [OF DERIV_diff[OF DERIV_mult[OF DERIV_const[of 6] DERIV_ident] DERIV_const[of "5*a"]] DERIV_const[of "b"]]] by auto
qed

lemma poly2_derivs:
  fixes a b :: real
  assumes [arith]:"a \<le> b"
  shows "\<And>x. ((λx. (x-b)^3 * (x - (2*a + b)/3)) has_real_derivative (λx. (x-b)^2 * (4*x -2*a -2*b)) x) (at x within {a..b})"
  and "\<And>x. ((λx. (x-b)^2 * (4*x -2*a -2*b)) has_real_derivative (λx. 4*(x-b)*(3*x-a-2*b)) x) (at x within {a..b})"
  and "\<And>x. ((λx. 4*(x-b)*(3*x-a-2*b)) has_real_derivative (λx. 4*(6*x - a - 5*b)) x) (at x within {a..b})"
  and "⋀x. ((λx. 4*(6*x - a - 5*b)) has_real_derivative 24) (at x within {a..b})"
proof goal_cases
  case (1 x)
  have "((\<lambda>x. (x - b) ^ 3 * (x - (2 * a + b) / 3)) has_real_derivative
   3 * ((x - b) ^ (2)) * (x - (2*a + b) / 3) + (x - b) ^ 3)
   (at x within {a..b})"
  using DERIV_mult[OF DERIV_power[OF DERIV_diff[OF DERIV_ident DERIV_const[of b]], of 3]
                      DERIV_diff[OF DERIV_ident DERIV_const[of "(2*a + b)/3"]]] by simp
  moreover have "3 * ((x - b) ^ (2)) * (x - (2*a + b) / 3) + (x - b) ^ 3 = (x-b)^2 * (4*x - 2*a - 2*b)" by algebra
  ultimately show ?case by simp
next
  case (2 x)
    have "((λx. (x-b)^2 * (4*x -2*a -2*b)) has_real_derivative 2 * (x-b) * (4*x - 2*a - 2*b) + 4*(x-b)^2) (at x within {a..b})"
    using DERIV_mult[OF DERIV_power[OF DERIV_diff[OF DERIV_ident DERIV_const[of b]], of 2]
                      DERIV_diff[OF DERIV_diff[OF DERIV_mult[OF DERIV_const[of 4] DERIV_ident]
         DERIV_const[of "2*a"]] DERIV_const[of "2*b"]]] by simp
    moreover have "4*(x-b)*(3*x-a-2*b) = 2 * (x-b) * (4*x - 2*a - 2*b) + 4*(x-b)^2" by algebra
  ultimately show ?case by simp
next
  case (3 x)
  then show ?case using DERIV_mult[OF DERIV_mult[OF DERIV_const[of 4] DERIV_diff[OF DERIV_ident DERIV_const[of b]]]
            DERIV_diff[OF DERIV_diff[OF DERIV_mult[OF DERIV_const[of 3] DERIV_ident]
         DERIV_const[of "a"]] DERIV_const[of "2*b"]]] by (simp add: algebra_simps)
next
  case (4 x) then show ?case using DERIV_mult[OF DERIV_const[of 4] DERIV_diff
    [OF DERIV_diff[OF DERIV_mult[OF DERIV_const[of 6] DERIV_ident] DERIV_const[of a]] DERIV_const[of "5*b"]]] by auto
qed


lemma simpson_partial:
  fixes f f\<^sub>1 f\<^sub>2 f\<^sub>3 f\<^sub>4 :: "real \<Rightarrow> real" (*alternative notation because too lazy for long superscripts*)
  assumes deriv1: "\<And>x. (f has_real_derivative f\<^sub>1 x) (at x within {a..b})"
      and deriv2: "\<And>x. (f\<^sub>1 has_real_derivative f\<^sub>2 x) (at x within {a..b})"
      and deriv3: "\<And>x. (f\<^sub>2 has_real_derivative f\<^sub>3 x) (at x within {a..b})"
      and deriv4: "\<And>x. (f\<^sub>3 has_real_derivative f\<^sub>4 x) (at x within {a..b})"
      and cont_f\<^sub>4: "continuous_on {a..b} f\<^sub>4"
      and a_le_b[arith]: "a \<le> b"
      and pderiv1: "\<And>x. (p has_real_derivative p\<^sub>1 x) (at x within {a..b})"
      and pderiv2: "\<And>x. (p\<^sub>1 has_real_derivative p\<^sub>2 x) (at x within {a..b})"
      and pderiv3: "\<And>x. (p\<^sub>2 has_real_derivative p\<^sub>3 x) (at x within {a..b})"
      and pderiv4: "\<And>x. (p\<^sub>3 has_real_derivative p\<^sub>4 x) (at x within {a..b})"
      and cont_p\<^sub>4: "continuous_on {a..b} p\<^sub>4"
      shows "(\<integral>x\<in>{a..b}. (f\<^sub>4 x * p x) \<partial>lborel) =
      (p b * f\<^sub>3 b - p a * f\<^sub>3 a)
    - (p\<^sub>1 b * f\<^sub>2 b - p\<^sub>1 a * f\<^sub>2 a)
    + (p\<^sub>2 b * f\<^sub>1 b - p\<^sub>2 a * f\<^sub>1 a)
    - (p\<^sub>3 b * f b - p\<^sub>3 a * f a)
    + (\<integral>x\<in>{a..b}. (f x * p\<^sub>4 x) \<partial>lborel)"
proof -
  have "(\<integral>x\<in>{a..b}. (f\<^sub>4 x * p x) \<partial>lborel)
    = (p b * f\<^sub>3 b - p a * f\<^sub>3 a) - (\<integral>x\<in>{a..b}. (f\<^sub>3 x * p\<^sub>1 x) \<partial>lborel)"
    apply (subst set_integral_by_parts[OF a_le_b _ _, where ?F = f\<^sub>3 and ?g' = p\<^sub>1])
    using assms DERIV_continuous_on[OF pderiv2] by auto
  also have "... = (p b * f\<^sub>3 b - p a * f\<^sub>3 a)
    - (p\<^sub>1 b * f\<^sub>2 b - p\<^sub>1 a * f\<^sub>2 a) + (\<integral>x\<in>{a..b}. (f\<^sub>2 x * p\<^sub>2 x) \<partial>lborel)"
    apply (subst set_integral_by_parts[OF a_le_b _ _, where ?F = f\<^sub>2 and ?g' = p\<^sub>2])
    using assms DERIV_continuous_on[OF deriv4] DERIV_continuous_on[OF pderiv3] by auto
  also have "... = (p b * f\<^sub>3 b - p a * f\<^sub>3 a)
    - (p\<^sub>1 b * f\<^sub>2 b - p\<^sub>1 a * f\<^sub>2 a)
    + (p\<^sub>2 b * f\<^sub>1 b - p\<^sub>2 a * f\<^sub>1 a)
    - (\<integral>x\<in>{a..b}. (f\<^sub>1 x * p\<^sub>3 x) \<partial>lborel)"
    apply (subst set_integral_by_parts[OF a_le_b _ _, where ?F = f\<^sub>1 and ?g' = p\<^sub>3])
    using assms DERIV_continuous_on[OF deriv3] DERIV_continuous_on[OF pderiv4] by auto
  also have "... = (p b * f\<^sub>3 b - p a * f\<^sub>3 a)
    - (p\<^sub>1 b * f\<^sub>2 b - p\<^sub>1 a * f\<^sub>2 a)
    + (p\<^sub>2 b * f\<^sub>1 b - p\<^sub>2 a * f\<^sub>1 a)
    - (p\<^sub>3 b * f b - p\<^sub>3 a * f a)
    + (\<integral>x\<in>{a..b}. (f x * p\<^sub>4 x) \<partial>lborel)"
    apply (subst set_integral_by_parts[OF a_le_b _ _, where ?F = f and ?g' = p\<^sub>4])
    using assms DERIV_continuous_on[OF deriv2] by auto
  finally show ?thesis .
qed



theorem simpson_approx_error:
  fixes f f\<^sub>1 f\<^sub>2 f\<^sub>3 f\<^sub>4 :: "real \<Rightarrow> real" (*alternative notation because too lazy for long superscripts*)
  assumes deriv1: "\<And>x. (f has_real_derivative f\<^sub>1 x) (at x within {a..b})"
      and deriv2: "\<And>x. (f\<^sub>1 has_real_derivative f\<^sub>2 x) (at x within {a..b})"
      and deriv3: "\<And>x. (f\<^sub>2 has_real_derivative f\<^sub>3 x) (at x within {a..b})"
      and deriv4: "\<And>x. (f\<^sub>3 has_real_derivative f\<^sub>4 x) (at x within {a..b})"
      and cont_f\<^sub>4: "continuous_on {a..b} f\<^sub>4"
      and f\<^sub>4_bound: "\<And>x. x \<in> {a..b} \<Longrightarrow> (k::real) \<ge> abs(f\<^sub>4 x)"
      and a_le_b[arith]: "a \<le> b"
    shows "\<bar>(\<integral>x\<in>{a..b}. f x \<partial>lborel) - simpson_rule f a b\<bar>
      \<le> k * (b-a)^5 / (90*2^5)"
proof -
  define mid where "mid = (a + b)/2"
  have a_le_mid[arith]:"a \<le> mid" and mid_le_b[arith]:"mid \<le> b" unfolding mid_def by auto
  have "mid - a = (b-a)/2" unfolding mid_def by simp
  have middle_diff: "mid - a = b - mid" unfolding mid_def by argo
  then have subset1: "{a..mid} \<subseteq> {a..b}" and subset2: "{mid..b} \<subseteq> {a..b}" by auto
  have f\<^sub>4_bound1: "\<And>x. x \<in> {a..mid} \<Longrightarrow> (k::real) \<ge> abs(f\<^sub>4 x)" using f\<^sub>4_bound by simp
  have f\<^sub>4_bound2: "\<And>x. x \<in> {mid..b} \<Longrightarrow> (k::real) \<ge> abs(f\<^sub>4 x)" using f\<^sub>4_bound by simp
  {
    note partial = simpson_partial[of f f\<^sub>1 _ _ f\<^sub>2 f\<^sub>3 f\<^sub>4]
    note partial1 = partial[of a mid
      "(λx. (x-a)^3 * (x - (a + 2*b)/3))"
      "(λx. (x-a)^2 * (4*x -2*a -2*b))"
      "(λx. 4*(x-a)*(3*x-2*a-b))"
      "(λx. 4*(6*x - 5*a - b))"
      "(λx. 24)"]
    note partial2 = partial[of mid b
      "(λx. (x-b)^3 * (x - (2*a + b)/3))"
      "(λx. (x-b)^2 * (4*x -2*a -2*b))"
      "(λx. 4*(x-b)*(3*x-a-2*b))"
      "(λx. 4*(6*x - a - 5*b))"
      "(λx. 24)"]

    have front: "LBINT x:{a..mid}. f\<^sub>4 x * ((x - a) ^ 3 * (x - (a + 2 * b) / 3)) =
  (mid - a) ^ 3 * (mid - (a + 2 * b) / 3) * f\<^sub>3 mid
    - ((mid - a)\<^sup>2 * (4 * mid - 2 * a - 2 * b) * f\<^sub>2 mid)
    + 4 * (mid - a) * (3 * mid - 2 * a - b) * f\<^sub>1 mid
    - 4 * (6 * mid - 5 * a - b) * f mid
    + 4 * (a - b) * f a +
  (LBINT x:{a..mid}. f x * 24)" using assms poly1_derivs
  by (subst partial1, auto 0 2 intro: continuous_on_subset[OF _ subset1] DERIV_subset[OF _ subset1])
    have rear: "LBINT x:{mid..b}. f\<^sub>4 x * ((x - b) ^ 3 * (x - (2 * a + b) / 3)) =
   - ((mid - b) ^ 3 * (mid - (2 * a + b) / 3) * f\<^sub>3 mid)
    + ((mid - b)\<^sup>2 * (4 * mid - 2 * a - 2 * b) * f\<^sub>2 mid)
    - 4 * (mid - b) * (3 * mid - a - 2 * b) * f\<^sub>1 mid
    - 4 * (b - a) * f b
    + 4 * (6 * mid - a - 5 * b) * f mid
    + (LBINT x:{mid..b}. f x * 24)" using assms poly2_derivs
  by (subst partial2, auto 0 2 intro: continuous_on_subset[OF _ subset2] DERIV_subset[OF _ subset2])
    have "(LBINT x:{a..mid}. f\<^sub>4 x * ((x - a) ^ 3 * (x - (a + 2 * b) / 3)))
      + (LBINT x:{mid..b}. f\<^sub>4 x * ((x - b) ^ 3 * (x - (2 * a + b) / 3)))
    = (((b-a)/2) ^ 3 + ((a-b)/2)^3) * ((a-b) / 6 * f\<^sub>3 mid)
    - 8 * (2*b - 2*a) * f mid
    - 4 * (b - a) * f a - 4 * (b - a) * f b
    + (LBINT x:{a..mid}. f x * 24)
    + (LBINT x:{mid..b}. f x * 24)" by (subst front, subst rear, unfold mid_def, argo)
    also have "... = (((b-a)/2) ^ 3 + ((a-b)/2)^3) * ((a-b) / 6 * f\<^sub>3 mid)
    - 16 * (b - a) * f mid
    - 4 * (b - a) * f a - 4 * (b - a) * f b
    + 24 * (LBINT x:{a..b}. f x)" using
      real_set_integral_combine(1)[OF borel_integrable_atLeastAtMost'
        [OF DERIV_continuous_on[OF deriv1]] \<open>a \<le> mid\<close> \<open>mid \<le> b\<close>] by simp
    also have "... =
    - 16 * (b - a) * f mid
    - 4 * (b - a) * f a - 4 * (b - a) * f b
    + 24 * (LBINT x:{a..b}. f x)" by (auto simp: divide_simps, algebra)
    finally have "(LBINT x:{a..b}. f x)
      = (4 * (b - a) * f mid + (b - a) * f a + (b - a) * f b)/6
      + ((LBINT x:{a..mid}. f\<^sub>4 x * ((x - a) ^ 3 * (x - (a + 2 * b) / 3)))
      + (LBINT x:{mid..b}. f\<^sub>4 x * ((x - b) ^ 3 * (x - (2 * a + b) / 3))))/24" by algebra
    then have "\<bar>(LBINT x:{a..b}. f x) - simpson_rule f a b\<bar> \<le>
      (\<bar>(LBINT x:{a..mid}. f\<^sub>4 x * ((x - a) ^ 3 * (x - (a + 2 * b) / 3)))\<bar>
      + \<bar>(LBINT x:{mid..b}. f\<^sub>4 x * ((x - b) ^ 3 * (x - (2 * a + b) / 3)))\<bar>)/24" unfolding simpson_rule_def mid_def by argo
  }

  note partial_result = this

  { (*first error term*)
      let ?minor = "(λx.  \<bar>f\<^sub>4 x\<bar> * \<bar>(x - a) ^ 3 * (x - (a + 2 * b) / 3)\<bar>)"
      let ?between = "(λx. k * \<bar>(x - a) ^ 3 * (x - (a + 2 * b) / 3)\<bar>)"
      let ?major = "(λx. k * ((x - a) ^ 3) * (((a + 2 * b) / 3) - x))"
      have integr_minor: "set_integrable lborel {a..mid} ?minor"
        using cont_f\<^sub>4 by (auto intro!: continuous_intros borel_integrable_atLeastAtMost'
          continuous_on_subset[OF _ subset1] cong: abs_mult)
      have integr_major: "set_integrable lborel {a..mid} ?major"
        by (auto intro!: borel_integrable_atLeastAtMost' continuous_intros)
      have "\<And>x. x\<in>{a..mid} \<Longrightarrow> ?minor x \<le> ?between x"
          using f\<^sub>4_bound by (auto simp: mult_right_mono)
      moreover have "\<And>x. x\<in>{a..mid} \<Longrightarrow> ?between x = ?major x"
        unfolding mid_def by (auto simp: abs_mult)
      ultimately have *: "\<And>x. x\<in>{a..mid} \<Longrightarrow> ?minor x \<le> ?major x" by auto
      have "\<bar>LBINT x:{a..mid}. f\<^sub>4 x * ((x - a) ^ 3 * (x - (a + 2 * b) / 3))\<bar>
        \<le> (LBINT x:{a..mid}. \<bar>f\<^sub>4 x * ((x - a) ^ 3 * (x - (a + 2 * b) / 3))\<bar>)" by presburger
      also have "... = LBINT x:{a..mid}. \<bar>f\<^sub>4 x\<bar> * \<bar>((x - a) ^ 3 * (x - (a + 2 * b) / 3))\<bar>" by (simp add: abs_mult)
      also have "... \<le> LBINT x:{a..mid}. k * ((x-a) ^ 3) * (((a + 2 * b) / 3) - x)"
        by (rule set_integral_mono[OF integr_minor integr_major *]) 
      also have "... = k * (LBINT x:{a..mid}. ((x-a) ^ 3) * (((a + 2 * b) / 3) - x))" by (simp add: mult.assoc)
      finally have 1: "\<bar>LBINT x:{a..mid}. f\<^sub>4 x * ((x - a) ^ 3 * (x - (a + 2 * b) / 3))\<bar> \<le> ..." .

      have [simp]: "(LBINT x:{a..mid}. (x - a) ^ 3) = 1/4 * ((b-a)/2)^4"
        unfolding set_lebesgue_integral_def mid_def
        apply (subst integral_FTC_Icc)
        using DERIV_mult[OF DERIV_const [of "1/4"] DERIV_power[OF DERIV_diff[OF DERIV_ident DERIV_const[of a]], of 4]]
        by (auto intro!: continuous_intros  borel_integrable_atLeastAtMost'
          cong: has_real_derivative_iff_has_vector_derivative[symmetric])

      have [simp]: "(LBINT x:{a..mid}. (x - a) ^ 4) = 1/5 * ((b-a)/2)^5"
        unfolding set_lebesgue_integral_def mid_def
        apply (subst integral_FTC_Icc)
        using DERIV_mult[OF DERIV_const [of "1/5"] DERIV_power[OF DERIV_diff[OF DERIV_ident DERIV_const[of a]], of 5]]
        by (auto intro!: continuous_intros borel_integrable_atLeastAtMost'
          cong: has_real_derivative_iff_has_vector_derivative[symmetric])


      have "\<And>x. (((a + 2 * b) / 3) - x) = (2 * (b-a) / 3) - (x-a)" by argo
      then have "(LBINT x:{a..mid}. ((x-a) ^ 3) * (((a + 2 * b) / 3) - x))
        = (LBINT x:{a..mid}. ((x-a) ^ 3) * ((2 * (b-a) / 3) - (x-a)))" by presburger
      also have "... = (LBINT x:{a..mid}. (x-a) ^ 3 * (2 * (b - a) / 3) - (x-a)^4)"
        by (auto simp: power3_eq_cube power4_eq_xxxx right_diff_distrib')

      also have "... = (LBINT x:{a..mid}. (x - a) ^ 3 * (2 * (b - a) / 3)) - (LBINT x:{a..mid}. (x - a)^4)"
        by (intro set_integral_diff(2), auto intro!: continuous_intros borel_integrable_atLeastAtMost')
      also have "... = ((b - a) / 6) * ((b-a)/2)^4 - 1/5 * ((b-a)/2)^5" by simp
      also have "... = (b-a)^5/240" by (simp add: power_divide no_atp(126))
      finally have 2: "(LBINT x:{a..mid}. ((x-a) ^ 3) * (((a + 2 * b) / 3) - x)) = ..." .

      have "\<bar>LBINT x:{a..mid}. f\<^sub>4 x * ((x - a) ^ 3 * (x - (a + 2 * b) / 3))\<bar> \<le> k * (b-a)^5/240"
        using 1 2 by simp
  }

  note error1 = this

  { (*second error term*)
      let ?minor = "(λx.  \<bar>f\<^sub>4 x\<bar> * \<bar>(x - b) ^ 3 * (x - (2 * a + b) / 3)\<bar>)"
      let ?between = "(λx. k * \<bar>(x - b) ^ 3 * (x - (2 * a + b) / 3)\<bar>)"
      let ?major = "(λx. k * ((b-x) ^ 3) * (x - (2 * a + b) / 3))"
      have integr_minor: "set_integrable lborel {mid..b} ?minor"
        using cont_f\<^sub>4 by (auto intro!: continuous_intros borel_integrable_atLeastAtMost'
          continuous_on_subset[OF _ subset2] cong: abs_mult)
      have integr_major: "set_integrable lborel {mid..b} ?major"
        by (auto intro!: borel_integrable_atLeastAtMost' continuous_intros)
      have "\<And>x. x\<in>{mid..b} \<Longrightarrow> ?minor x \<le> ?between x"
          using f\<^sub>4_bound by (auto simp: mult_right_mono)
      moreover have "\<And>x. x\<in>{mid..b} \<Longrightarrow> ?between x = ?major x"
        unfolding mid_def by (auto simp: abs_mult minus_diff_eq[of _ b], algebra)
      ultimately have *: "\<And>x. x\<in>{mid..b} \<Longrightarrow> ?minor x \<le> ?major x" by auto

      have "\<bar>LBINT x:{mid..b}. f\<^sub>4 x * ((x - b) ^ 3 * (x - (2 * a + b) / 3))\<bar>
        \<le> LBINT x:{mid..b}. \<bar>f\<^sub>4 x * ((x - b) ^ 3 * (x - (2 * a + b) / 3))\<bar>"
        by presburger
      also have "... = LBINT x:{mid..b}. \<bar>f\<^sub>4 x\<bar> * \<bar>((x - b) ^ 3 * (x - (2 * a + b) / 3))\<bar>" by (simp add: abs_mult)
      also have "... \<le> LBINT x:{mid..b}. k * ((b-x) ^ 3) * (x - (2 * a + b) / 3)"
        by (rule set_integral_mono[OF integr_minor integr_major *])
      also have "... = k * (LBINT x:{mid..b}. ((b-x) ^ 3) * (x - (2 * a + b) / 3))" by (simp add: mult.assoc)
      finally have 1: "\<bar>LBINT x:{mid..b}. f\<^sub>4 x * ((x - b) ^ 3 * (x - (2 * a + b) / 3))\<bar> \<le> ..." .

      have [simp]: "(LBINT x:{mid..b}. (b - x) ^ 3) = 1/4 * ((b-a)/2)^4"
        unfolding set_lebesgue_integral_def mid_def apply (subst integral_FTC_Icc)
        using DERIV_mult[OF DERIV_const [of "-1/4"] DERIV_power[OF DERIV_diff[OF DERIV_const[of b] DERIV_ident], of 4]]
        by (auto intro!: continuous_intros  borel_integrable_atLeastAtMost'
          cong: has_real_derivative_iff_has_vector_derivative[symmetric], argo)

      have [simp]: "(LBINT x:{mid..b}. (b - x) ^ 4) = 1/5 * ((b-a)/2)^5"
        unfolding set_lebesgue_integral_def mid_def apply (subst integral_FTC_Icc)
        using DERIV_mult[OF DERIV_const [of "-1/5"] DERIV_power[OF DERIV_diff[OF DERIV_const[of b] DERIV_ident], of 5]]
        by (auto intro!: continuous_intros  borel_integrable_atLeastAtMost'
          cong: has_real_derivative_iff_has_vector_derivative[symmetric], argo)

      have "\<And>x. (x - ((2 * a + b) / 3)) = (2 * (b - a) / 3) - (b-x)" by argo
      then have "(LBINT x:{mid..b}. ((b-x) ^ 3) * (x - (2 * a + b) / 3))
        = (LBINT x:{mid..b}. ((b-x) ^ 3) * ((2 * (b - a) / 3) - (b-x)))" by presburger
      also have "... = (LBINT x:{mid..b}. (b - x) ^ 3 * (2 * (b - a) / 3) - (b-x)^4)"
        by (auto simp: power3_eq_cube power4_eq_xxxx right_diff_distrib')
      also have "... = (LBINT x:{mid..b}. (b - x) ^ 3 * (2 * (b - a) / 3)) - (LBINT x:{mid..b}. (b - x)^4)"
        by (intro set_integral_diff(2), auto intro!: continuous_intros borel_integrable_atLeastAtMost')
      also have "... = ((b - a) / 6) * ((b-a)/2)^4 - 1/5 * ((b-a)/2)^5" by simp
      finally have 2: "(LBINT x:{mid..b}. ((b-x) ^ 3) * (x - (2 * a + b) / 3)) = (b-a)^5/240" by (simp add: power_divide no_atp(126))

      have "\<bar>LBINT x:{mid..b}. f\<^sub>4 x * ((x - b) ^ 3 * (x - (2 * a + b) / 3))\<bar> \<le> k * (b-a)^5/240"
        using 1 2 by simp
  }
  note error2 = this
  show ?thesis
    using partial_result error1 error2 by (auto cong: power_divide)
qed




corollary simpson_comp_approx_error:
  fixes f f\<^sub>1 f\<^sub>2 f\<^sub>3 f\<^sub>4 :: "real \<Rightarrow> real" (*alternative notation because too lazy for long superscripts*)
  assumes n_nonzero[arith] :"N > 0"
      and deriv1: "\<And>x. (f has_real_derivative f\<^sub>1 x) (at x within {a..b})"
      and deriv2: "\<And>x. (f\<^sub>1 has_real_derivative f\<^sub>2 x) (at x within {a..b})"
      and deriv3: "\<And>x. (f\<^sub>2 has_real_derivative f\<^sub>3 x) (at x within {a..b})"
      and deriv4: "\<And>x. (f\<^sub>3 has_real_derivative f\<^sub>4 x) (at x within {a..b})"
      and cont_f\<^sub>4: "continuous_on {a..b} f\<^sub>4"
      and f\<^sub>4_bound: "\<And>x. x \<in> {a..b} \<Longrightarrow> (k::real) \<ge> abs(f\<^sub>4 x)"
      and a_le_b[arith]: "a \<le> b"
    shows "\<bar>(\<integral>x\<in>{a..b}. f x \<partial>lborel) - simpson_rule_comp f a b N\<bar> \<le> k * (b-a)^5 / (90*2^5*N^4)"
proof (insert assms, induction N arbitrary: a b rule: nat_induct_non_zero)
    case (Suc n)
    define H where "H = (b-a)/Suc n"
    have cong1: "a + Suc n * H = b" unfolding H_def by simp
    then have cong2: "a + n * H = b - H" by (auto simp: algebra_simps)
    have [arith]:"H \<ge> 0" unfolding H_def using a_le_b by (simp add: Suc.prems(7))
    then have a_le_mid[arith]:"a \<le> b - H" using cong2 by (auto simp: algebra_simps)
    have mid_le_b[arith]: "b - H \<le> b" by linarith
    have subset1: "{a..b - H} \<subseteq> {a..b}" using mid_le_b by simp
    have subset2: "{b-H..b} \<subseteq> {a..b}" using a_le_mid by simp

    have simpson_add: "simpson_rule_comp f a b (Suc n) = simpson_rule_comp f a (b-H) n + simpson_rule f (b-H) b"
      proof -
        have "simpson_rule_comp f a b (Suc n)
          = (\<Sum>k\<leftarrow>[0..<Suc n]. simpson_rule f (a + real k * H) (a + real (Suc k) * H))"
          unfolding simpson_rule_sum_eq_simpson_rule_comp[OF zero_less_Suc] H_def by simp
        also have "... = simpson_rule_comp f a (a + n * H) n + simpson_rule f (a + n * H) (a + (Suc n) * H)"
          unfolding simpson_rule_sum_eq_simpson_rule_comp[OF \<open>n > 0\<close>] by simp
        finally show ?thesis using cong1 cong2 by simp
      qed

    let ?e1 = "k * (n * H) ^ 5 / (90 * 2^5 * n ^ 4)"
    let ?e2 = "k * H ^ 5 / (90*2^5)"

    {
      have *: "b - H - a = n * H" using cong2 by linarith
      have "\<bar>(LBINT x:{a..b - H}. f x) - simpson_rule_comp f a (b - H) n\<bar> \<le> k * (b - H - a)^5 /(90*2^5*n ^4)"
        using subset1 Suc.prems(6) by (subst Suc.IH[
          OF DERIV_subset[OF Suc.prems(1)] DERIV_subset[OF Suc.prems(2)]
             DERIV_subset[OF Suc.prems(3)] DERIV_subset[OF Suc.prems(4)]
             continuous_on_subset[OF Suc.prems(5)] _ a_le_mid], auto)
      then have "\<bar>(LBINT x:{a..b - H}. f x) - simpson_rule_comp f a (b - H) n\<bar> \<le> ?e1" using * by simp
    }
        note e1 = this
    {
      have "\<bar>(LBINT x:{b - H..b}. f x) - simpson_rule f (b-H) b \<bar> \<le> k * (b - (b - H)) ^ 5 / (90*2^5)"
        using subset2 Suc.prems(6) by (subst simpson_approx_error[
             OF DERIV_subset[OF Suc.prems(1)] DERIV_subset[OF Suc.prems(2)]
                DERIV_subset[OF Suc.prems(3)] DERIV_subset[OF Suc.prems(4)]
                continuous_on_subset[OF Suc.prems(5)] _ mid_le_b], auto)
      then have "\<bar>(LBINT x:{b - H..b}. f x) - simpson_rule f (b-H) b \<bar> \<le> ?e2" by argo
    }
        note e2 = this
    {
        have "?e1 + ?e2 = (k / (90*2^5)) * ((n * H) ^ 5 / (n ^ (5-1)) + (H ^ 5))"
          by (auto simp: algebra_simps)
        also have "... = (k / (90 * 2^5)) * (b-a)^5 / ((Suc n)^(5-1))"
          using error_cong[of "b-a" n 5, OF _ _ _ \<open>0 < n\<close>] H_def \<open>0 \<le> H\<close> \<open>a \<le> b\<close> by auto
        finally have "?e1 + ?e2 = k * (b-a)^5 / (90 * 2^5 * (Suc n)^4)" unfolding H_def by simp
    }
      note combined_error = this
    from real_set_integral_combine[OF borel_integrable_atLeastAtMost'[OF DERIV_continuous_on[OF Suc.prems(1)]]]
    have "(LBINT x:{a..b}. f x) = (LBINT x:{a..b - H}. f x) + (LBINT x:{b - H..b}. f x)"
      by simp
    then show ?case using e1 e2 simpson_add combined_error by argo
qed (insert simpson_approx_error, fastforce)

end
