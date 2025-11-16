theory Foo1 imports Main begin

lemma
  "(0 :: nat) \<in> {0..<4}"
  "(1 :: nat) \<in> {0..<4}"
  "(2 :: int) \<in> {0..<4}"
  "(3 :: int) \<in> {0..<4}"
  "finite ({0..<4} :: nat set)"
  by simp_all

typedef reversed_nat = "UNIV :: nat set"
  by auto
print_theorems

setup_lifting type_definition_reversed_nat

lift_definition rev_zero :: reversed_nat is "(0 :: nat)" .
lift_definition rev_one :: reversed_nat is "(1 :: nat)" .
lift_definition rev_le   :: "reversed_nat \<Rightarrow> reversed_nat \<Rightarrow> bool" is "\<lambda>m n. n \<le> m" .
lift_definition rev_less :: "reversed_nat \<Rightarrow> reversed_nat \<Rightarrow> bool" is "\<lambda>m n. n < m" .
lift_definition rev_plus :: "reversed_nat \<Rightarrow> reversed_nat \<Rightarrow> reversed_nat" is "(+) :: nat \<Rightarrow> nat \<Rightarrow> nat" .
lift_definition rev_times :: "reversed_nat \<Rightarrow> reversed_nat \<Rightarrow> reversed_nat" is "(*) :: nat \<Rightarrow> nat \<Rightarrow> nat" .

instantiation reversed_nat :: zero begin
definition "zero = rev_zero"
instance ..
end

instantiation reversed_nat :: one begin
definition "one = rev_one"
instance ..
end

instantiation reversed_nat :: plus begin
definition "(x + y) = rev_plus x y"
instance ..
end

instantiation reversed_nat :: times begin
definition "(x * y) = rev_times x y"
instance ..
end

instantiation reversed_nat :: ord begin
definition "(x \<le> y) \<equiv> rev_le x y"
definition "(x < y) \<equiv> rev_less x y"
instance ..
end


instantiation reversed_nat :: linorder
begin
instance
proof
  fix x y z :: reversed_nat
  obtain x' :: nat where 1: "x = Abs_reversed_nat x'" using Abs_reversed_nat_cases by blast
  obtain y' :: nat where 2: "y = Abs_reversed_nat y'" using Abs_reversed_nat_cases by blast
  obtain z' :: nat where 3: "z = Abs_reversed_nat z'" using Abs_reversed_nat_cases by blast
  note k = 1 2 3

  find_theorems Abs_reversed_nat

  show "x \<le> x" unfolding less_eq_reversed_nat_def rev_le.rep_eq by simp
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding k thm rev_le.abs_eq
    unfolding less_eq_reversed_nat_def rev_le.rep_eq
    using Rep_reversed_nat_inject by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_reversed_nat_def rev_le.rep_eq by simp
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    unfolding less_reversed_nat_def less_eq_reversed_nat_def rev_less.rep_eq rev_le.rep_eq by linarith
  show "x \<le> y \<or> y \<le> x"
    unfolding less_reversed_nat_def less_eq_reversed_nat_def rev_le.rep_eq by force
qed
end

instantiation reversed_nat :: semiring_1
begin

instance
proof
  fix x y z :: reversed_nat
  show "0 + x = x"
    apply (subst Rep_reversed_nat_inject[symmetric])
    unfolding plus_reversed_nat_def rev_plus.rep_eq apply simp
    find_theorems rev_plus

    
    apply (cases x rule: Rep_reversed_nat_cases)
    unfolding plus_reversed_nat_def using type_definition_reversed_nat 
  show "x + 0 = x"
    unfolding plus_reversed_nat_def zero_reversed_nat_def by simp
  show "(x + y) + z = x + (y + z)"
    unfolding plus_reversed_nat_def by simp
  show "x + y = y + x"
    unfolding plus_reversed_nat_def by simp
  show "0 * x = 0"
    unfolding times_reversed_nat_def zero_reversed_nat_def by simp
  show "x * 0 = 0"
    unfolding times_reversed_nat_def zero_reversed_nat_def by simp
  show "1 * x = x"
    unfolding times_reversed_nat_def one_reversed_nat_def by simp
  show "x * 1 = x"
    unfolding times_reversed_nat_def one_reversed_nat_def by simp
  show "(x * y) * z = x * (y * z)"
    unfolding times_reversed_nat_def by simp
  show "x * (y + z) = x * y + x * z"
    unfolding times_reversed_nat_def plus_reversed_nat_def by simp
  show "(x + y) * z = x * z + y * z"
    unfolding times_reversed_nat_def plus_reversed_nat_def by simp
  show "0 \<noteq> 1"
    unfolding zero_reversed_nat_def one_reversed_nat_def by simp
qed

end

instantiation reversed_nat :: numeral
begin
lift_definition numeral_reversed_nat :: "num \<Rightarrow> reversed_nat"
  is "\<lambda>n. numeral n :: nat" .
instance ..
end





(* instantiate zero: give the definition an explicit unique name *)
instantiation reversed_nat :: zero
begin
definition zero_reversed_nat_inst_def: "0 = rev_zero"
instance ..
end

(* instantiate ord: give each definition a unique name *)
instantiation reversed_nat :: ord
begin
definition le_reversed_nat_inst_def: "(x \<le> y) \<equiv> rev_le x y"
definition less_reversed_nat_inst_def: "(x < y) \<equiv> rev_less x y"
instance ..
end

(* make it a linorder (proof by transfer) *)
instantiation reversed_nat :: linorder
begin
instance
  apply standard
  apply (meson le_reversed_nat_inst_def less_reversed_nat_inst_def nle_le rev_le.rep_eq rev_less.rep_eq verit_comp_simplify1(3))
  apply (simp add: le_reversed_nat_inst_def rev_le.rep_eq)
  using le_reversed_nat_inst_def rev_le.rep_eq apply force
  apply (simp add: Rep_reversed_nat_inject le_reversed_nat_inst_def rev_le.rep_eq)
  using le_reversed_nat_inst_def rev_le.rep_eq apply force
  done
end

lemma upto_empty: "{0::reversed_nat..<n} = {}"
  by (simp add: le_reversed_nat_inst_def rev_le.rep_eq rev_zero.rep_eq zero_reversed_nat_inst_def)
lemma
  "(0 :: reversed_nat) \<in> {0..<4}"
  "(1 :: nat) \<in> {0..<4}"
  "(2 :: int) \<in> {0..<4}"
  "(3 :: real) \<in> {0..<4}"
  "finite ({0..<4} :: nat set)"
  by simp_all

end