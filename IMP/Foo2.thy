theory Foo2 imports "Complex_Main" "HOL-Eisbach.Eisbach" begin

lemma
  "(0 :: nat) \<in> {0..<4}"
  "(1 :: nat) \<in> {0..<4}"
  "(2 :: int) \<in> {0..<4}"
  "(3 :: int) \<in> {0..<4}"
  "finite ({0..<4} :: nat set)"
  by simp_all

lemma "\<not> finite ({0..<4} :: real set)" by simp

datatype rev_nat = Rev (unrev: nat)

instantiation rev_nat :: zero begin
definition "0 = Rev 0"
instance ..
end

instantiation rev_nat :: one begin
definition "1 = Rev 1"
instance ..
end

instantiation rev_nat :: plus begin
definition "(x + y) = Rev (unrev x + unrev y)"
instance ..
end

instantiation rev_nat :: times begin
definition "(x * y) = Rev (unrev x * unrev y)"
instance ..
end

instantiation rev_nat :: ord begin
definition "(x \<le> y) \<equiv> unrev y \<le> unrev x"
definition "(x < y) \<equiv> unrev y < unrev x"
instance ..
end

instantiation rev_nat :: linorder
begin
instance
  apply standard
  unfolding less_eq_rev_nat_def less_rev_nat_def using rev_nat.expand by auto
end

instantiation rev_nat :: semiring_1
begin
instance
  apply standard
  unfolding
    zero_rev_nat_def one_rev_nat_def plus_rev_nat_def times_rev_nat_def
      less_eq_rev_nat_def less_rev_nat_def using rev_nat.expand
  by (simp_all add: algebra_simps)
end

lemma
  "\<not> (0 :: rev_nat) \<in> {0..<4}"
  "\<not> (1 :: rev_nat) \<in> {0..<4}"
  "\<not> (2 :: rev_nat) \<in> {0..<4}"
  "\<not> (3 :: rev_nat) \<in> {0..<4}"
  by (simp_all add: numeral_Bit0 numeral_Bit1 zero_rev_nat_def one_rev_nat_def plus_rev_nat_def less_rev_nat_def)

(* 

datatype pointD = Hd | Ad | Bd | Cd| Dd| Ed| Fd| Pd | Qd |Rd

definition LinesD::"pointD set set"  where
  "LinesD ={{Ad,Bd, Pd}, {Bd, Cd,Rd}, {Cd, Ad, Qd}, {Dd, Ed, Pd}, {Ed, Fd, Rd}, {Fd, Dd, Qd},
            {Hd, Ad, Dd}, {Hd, Bd, Ed}, {Hd, Cd, Fd}, {Pd, Qd, Rd}}"
(* 
method repeat0 methods m = (m; repeat0 \<open>m\<close>)?
method repeat methods m = m; repeat0 \<open>m\<close>

lemma set_literal_to_list:
  assumes "A = set xs"
  shows "insert x A = set (x # xs)"
  using assms by simp

schematic_goal "LinesD = set ?xs" unfolding LinesD_def by (rule set_literal_to_list)+ simp *)

(* 

lemma split_ex_insert:
  assumes "P y \<or> (\<exists>x \<in> A. P x)"
  shows "\<not> (\<exists>x \<in> insert y A. P x)"
  using assms by blast
 *)

(* lemma assumes "\<not>P \<Longrightarrow> False" shows P *)

lemma split_ex_insert:
  assumes "(\<exists>x \<in> A. P x) \<or> (P y \<or> Q)"
  shows "(\<exists>x \<in> insert y A. P x) \<or> Q"
  using assms by blast

lemma split_ex_start:
  assumes "(\<exists>x \<in> insert y A. P x) \<or> False"
  shows "\<exists>x \<in> insert y A. P x"
  using assms by blast

lemma split_ex_stop:
  assumes Q
  shows "(\<exists>x \<in> {}. P x) \<or> Q"
  using assms by blast

(* 
lemma split_ex_insert:
  assumes "\<not> (\<exists>x \<in> insert y A. P x)"
  shows "\<not>P y" "\<not> (\<exists>x \<in>A. P x)"
  using assms by blast+
 *)

lemma desargues_three_lines1: (* every pt lies on 3 lines *)
  fixes X::"pointD"
  assumes "X = Ad" (* an extreme case...can we prove this even with X known *)
  shows
    "\<exists>l \<in> LinesD. \<exists>m \<in> LinesD. \<exists>n \<in> LinesD.
      distinct[l, m, n] \<and> X \<in> l \<and>  X \<in> m \<and> X \<in> n"
  unfolding LinesD_def
  apply (rule split_ex_start)

  apply (rule split_ex_insert)+
  apply (rule split_ex_stop)
  apply (rule split_ex_insert)+
  apply (rule split_ex_stop)
  apply (rule split_ex_insert)+
  apply (rule split_ex_stop)

  apply (drule split_ex_insert)
  apply (drule split_ex_insert)

  unfolding LinesD_def apply (rule split_ex_insert)
  apply rule
  proof (repeat \<open>rule exI conjI\<close>)
    show "distinct [{Ad, Bd, Pd}, {Cd, Ad, Qd}, {Hd, Ad, Dd}]" by fastforce
  qed (simp_all add: assms LinesD_def)

lemma desargues_three_lines: (* every pt lies on 3 lines *)
  fixes X::"pointD"
  shows "\<exists> l m n . distinct[l, m, n] \<and>
   X \<in> l \<and>  X \<in> m \<and>  X \<in> n \<and>
   l \<in> LinesD \<and> m \<in> LinesD \<and> n \<in> LinesD"
  apply (cases rule: pointD.induct) 
  apply (rule exI)+

  proof (repeat \<open>rule exI conjI\<close>)
    show "distinct [{Ad, Bd, Pd}, {Cd, Ad, Qd}, {Hd, Ad, Dd}]" by fastforce
    qed (simp_all add: assms LinesD_def) *)
end