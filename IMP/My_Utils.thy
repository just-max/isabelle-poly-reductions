theory My_Utils
  imports Main
begin

(* TODO: move these utils into some better place *)


definition "null = (\<lambda>_. undefined)"

abbreviation "concat_map f xs \<equiv> concat (map f xs)"


(* generate *)

definition "generate f n \<equiv> map f [0..<n]"
(* abbreviation "generate_len f xs \<equiv> generate f (length xs)" (* ? *) *)

lemma generate_cong[fundef_cong]:
  assumes "n = m" "\<And>i. i < m \<Longrightarrow> f i = g i"
  shows "generate f n = generate g m"
  using assms unfolding generate_def by simp

lemma map_generate_comp: "map g (generate f n) = generate (g o f) n"
  unfolding generate_def by simp

lemma generate_snoc: "generate f (Suc n) = generate f n @ [f n]"
  unfolding generate_def by auto

lemma generate_length[simp]: "length (generate f n) = n"
  unfolding generate_def by simp

lemma generate_0_conv[iff]: "generate f n = [] \<longleftrightarrow> n = 0"
  unfolding generate_def by simp

(* like turning a classic for loop into a for-each loop *)
lemma generate_nth_is_map[simp]: "generate (\<lambda>i. f (xs ! i)) (length xs) = map f xs"
  unfolding generate_def by (simp add: map_equality_iff)


(* sum_map *)

abbreviation "sum_map f xs \<equiv> sum_list (map f xs)"

lemma sum_map_concat: "sum_map f (concat xss) = sum_list (concat (map (map f) xss))"
  using map_concat by metis

lemma sum_map_mono:
  fixes f g :: "'a \<Rightarrow> 'b :: {ordered_ab_semigroup_add, monoid_add}"
  assumes "\<forall>x \<in> set xs. f x \<le> g x"
  shows "sum_map f xs \<le> sum_map g xs"
  using assms add_mono by (induction xs) auto


(* max_list0 *)

(* maximum of a list, but defined (as 0) for empty lists *)
(* defined only on nat to keep things simple *)
definition max_list0 :: "nat list \<Rightarrow> nat" where
  "max_list0 xs \<equiv> fold max xs 0"

lemma max_list0_cons:
  shows "max_list0 (x # xs) = max x (max_list0 xs)"
proof-
  have "fold max (x # xs) z = max x (fold max xs z)" for xs :: "nat list" and x z
    by (induction xs arbitrary: x z) simp_all
  then show ?thesis unfolding max_list0_def by blast
qed

lemma max_list0_append: "max (max_list0 xs) (max_list0 ys) = max_list0 (xs @ ys)"
proof (induction xs)
  case Nil then show ?case using max_list0_def by simp
  case (Cons a xs) then show ?case using max_list0_cons by simp
qed


(* max1 *)

definition max1 :: "nat \<Rightarrow> nat" (\<open>(\<open>notation=\<open>postfix +\<close>\<close>_\<^sub>+)\<close> [1000] 999) where
  "max1 \<equiv> max 1"

lemma max1_idem[simp]: shows "(x\<^sub>+)\<^sub>+ = x\<^sub>+" unfolding max1_def by simp
lemma max1_pos[simp]: "x\<^sub>+ \<noteq> 0" unfolding max1_def by simp
lemma max1_pos_id[simp]: "x \<noteq> 0 \<Longrightarrow> x\<^sub>+ = x" unfolding max1_def by simp
lemma max1_id_positive[iff]: "x\<^sub>+ = x \<longleftrightarrow> x \<noteq> 0" unfolding max1_def by linarith

lemma max1_plus1[simp]: "x \<noteq> 0 \<Longrightarrow> (x + y)\<^sub>+ = x + y" by simp
lemma max1_plus2[simp]: "y \<noteq> 0 \<Longrightarrow> (x + y)\<^sub>+ = x + y" by simp

lemma max1_inc: "x\<^sub>+ \<ge> x" unfolding max1_def by simp


end
