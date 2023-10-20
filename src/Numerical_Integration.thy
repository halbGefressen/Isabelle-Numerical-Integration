theory Numerical_Integration
  imports "HOL-Decision_Procs.Approximation"
begin

unbundle floatarith_notation
bundle floatarith_short_notation begin
notation (floatarith_notation) Approximation.Add (infixl "+\<^sub>f" 65)
notation (floatarith_notation) Approximation.Mult (infixl "*\<^sub>f" 70)
notation (floatarith_notation) Approximation.Minus ("-\<^sub>f _" [82] 81)
notation (floatarith_notation) Approximation.Inverse ("_\<^sup>-\<^sub>f" [81] 80)
end
(* Example usage: value "Add (Minus (Num 1)) (Inverse (Num 2)) = -\<^sub>fNum 1 +\<^sub>f Num 2\<^sup>-\<^sub>f" *)

bundle no_floatarith_short_notation begin
no_notation (floatarith_notation) Approximation.Add (infixl "+\<^sub>f" 65)
no_notation (floatarith_notation) Approximation.Mult (infixl "*\<^sub>f" 70)
no_notation (floatarith_notation) Approximation.Minus ("-\<^sub>f _" [82] 81)
no_notation (floatarith_notation) Approximation.Inverse ("_\<^sup>-\<^sub>f" [81] 80)
end
unbundle floatarith_short_notation

(*    function to approximate
 * \<Rightarrow> arithmetic precision
 * \<Rightarrow> integral precision (e.g. intermediate points)
 * \<Rightarrow> variable to integrate over
 * \<Rightarrow> bounds
 * \<Rightarrow> variable values
 * \<Rightarrow> result: interval*)
type_synonym prec = nat
type_synonym ivl_count = nat
type_synonym integr_var = nat
type_synonym val = "(float interval) option"
type_synonym int_approx = "prec \<Rightarrow> ivl_count \<Rightarrow> floatarith \<Rightarrow> integr_var \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val list \<Rightarrow> val"

abbreviation "ivl_coerce \<equiv> Some \<circ> interval_of"
abbreviation "sum_expr low high \<equiv> fold (Add \<circ> Var \<circ> nat) [low..high] (Num 0)"

definition int_approx_midpoint :: int_approx where
  "int_approx_midpoint prec N f x a b vals = (let apprx = approx prec;
      H = apprx ((Var 2 +\<^sub>f -\<^sub>fVar 1) *\<^sub>f Var 0\<^sup>-\<^sub>f) [ivl_coerce (of_nat N), a, b];
      x_ex = Var 1 +\<^sub>f (Num 2 *\<^sub>f Var 0 +\<^sub>f Num 1) *\<^sub>f Var 2 *\<^sub>f Num 2\<^sup>-\<^sub>f;
      xs = map (\<lambda>i. apprx x_ex [(ivl_coerce \<circ> of_int) i, a, H]) [0..<N];
      fs = map (\<lambda>x\<^sub>i. apprx f (vals[x := x\<^sub>i])) xs
    in apprx (Var 0 *\<^sub>f sum_expr 1 N) (H # fs))"

definition int_approx_simpson :: int_approx where
  "int_approx_simpson prec N f x a b vals = (let apprx = approx prec;
      H2 = apprx ((Var 2 +\<^sub>f -\<^sub>fVar 1) *\<^sub>f (Var 0 *\<^sub>f Num 2)\<^sup>-\<^sub>f) [ivl_coerce (of_nat N), a, b];
      x_evn_expr = Var 2 +\<^sub>f (Num 2 *\<^sub>f Var 0) *\<^sub>f Var 1;
      x_odd_expr = x_evn_expr +\<^sub>f Var 1;
      xs_evn = map (\<lambda>i. apprx x_evn_expr [(ivl_coerce \<circ> of_int) i, H2, a]) [0..N];
      xs_odd = map (\<lambda>i. apprx x_odd_expr [(ivl_coerce \<circ> of_int) i, H2, a]) [0..<N];
      fs = map (\<lambda>v. apprx f (vals[x := v])) (xs_evn @ xs_odd);
      simpson = Var 0 *\<^sub>f Num 3\<^sup>-\<^sub>f *\<^sub>f (Var 1 +\<^sub>f Var (N+1) +\<^sub>f (Num 2) *\<^sub>f sum_expr 2 N
                                              +\<^sub>f (Num 4) *\<^sub>f sum_expr (N+2) (2*N+1))
    in apprx simpson (H2 # fs))"


(* Since the function exp(x) derives to itself, the nth derivative between 0 and 1 is always bounded by exp(1).
 * This allows the precise calculation of an interval in which the exact value must lie by adding the analytical
 * and numerical error.
 *
 * (approx 0 (Cos (Num 1)) []) is an expression that returns the interval (-1, 1).
 * The interval cannot be constructed directly because Isabelle considers this an "abstraction violation". *)
definition
  "int_approx_exp1_midpoint prec N \<equiv> (
    let approximation = int_approx_midpoint prec N (Exp (Var 0)) 0 (ivl_coerce 0) (ivl_coerce 1) [ivl_coerce 0];
        err = approx prec (Abs ((Power (Var 1 +\<^sub>f -\<^sub>fVar 0) 3) *\<^sub>f (Exp (Num 1)) *\<^sub>f (Power (Var 3) 2 *\<^sub>f Num 24)\<^sup>-\<^sub>f) *\<^sub>f Var 2)
                     [(ivl_coerce 0), (ivl_coerce 1), approx 0 (Cos (Num 1)) [], ivl_coerce (of_int N)]
    in approx prec (Var 0 +\<^sub>f Var 1) [err, approximation])"

definition
  "int_approx_exp1_simpson prec N \<equiv> (
    let approximation = int_approx_simpson prec N (Exp (Var 0)) 0 (ivl_coerce 0) (ivl_coerce 1) [ivl_coerce 0];
        err = approx prec (Abs ((Power (Var 1 +\<^sub>f -\<^sub>fVar 0) 5) *\<^sub>f (Exp (Num 1)) *\<^sub>f (Power (Var 3) 4 *\<^sub>f Num 2880)\<^sup>-\<^sub>f) *\<^sub>f Var 2)
                     [(ivl_coerce 0), (ivl_coerce 1), approx 0 (Cos (Num 1)) [], ivl_coerce (of_int N)]
    in approx prec (Var 0 +\<^sub>f Var 1) [err, approximation])"


(* Generates a list of lists. The top level is the interval count, the bottom level is the precision.
 * For data extraction. *)
definition extract_data :: "int_approx \<Rightarrow> floatarith \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> float interval) list list" where
  "extract_data ia f a b P I \<equiv> (let
    apprx = \<lambda>p i. ia p i f 0 (ivl_coerce (of_int a)) (ivl_coerce (of_int b)) [ivl_coerce 0];
    precision_fns = map (\<lambda>p i. (p, i, the (apprx p i))) (map (times 5) [1..<P]);
    int_count = map (\<lambda>i. map (\<lambda>f. f i) precision_fns) (map (times 5) [1..<I])
  in int_count)"


definition extract_data_exp1 :: "(nat \<Rightarrow> nat \<Rightarrow> (float interval) option) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> float interval) list list" where
  "extract_data_exp1 ia P I \<equiv> (let
    apprx = \<lambda>p i. ia p i;
    precision_fns = map (\<lambda>p i. (p, i, the (apprx p i))) (map (times 5) [1..<10]);
    res = map (\<lambda>i. map (\<lambda>f. f i) precision_fns) (map (times 5) [1..<10])
  in res)"

abbreviation "\<phi> \<equiv> Sqrt(Num 2 *\<^sub>f Pi)\<^sup>-\<^sub>f *\<^sub>f Exp (-\<^sub>f(Power (Var 0) 2) *\<^sub>f (Num 2)\<^sup>-\<^sub>f)"
abbreviation "ill_conditioned \<equiv> Cos (Inverse ((Var 0) +\<^sub>f (Num (Float 1 (-10)))))"


unbundle no_floatarith_short_notation
unbundle no_floatarith_notation
end
