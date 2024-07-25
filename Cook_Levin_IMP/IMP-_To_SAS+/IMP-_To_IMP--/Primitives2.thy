theory Primitives2
  imports
    "HOL-Library.Nat_Bijection"
    HOL_To_IMP_Minus.HOL_To_IMP_Tactics
    HOL_To_IMP_Minus.HOL_To_IMP_Minus_Primitives
    HOL_To_IMP_Minus.HOL_To_IMP_Minus_Arithmetics
begin

context HOL_To_IMP_Minus
begin



fun prod_decode_aux1 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "prod_decode_aux1 k m =
    (if m \<le> k then m else prod_decode_aux1 (Suc k) (m - Suc k))"
declare prod_decode_aux1.simps[simp del]  (* NOTE: prevents simplifier loop *)

fun prod_decode_aux2 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "prod_decode_aux2 k m =
    (if m \<le> k then k - m else prod_decode_aux2 (Suc k) (m - Suc k))"
declare prod_decode_aux2.simps[simp del]

definition prod_decode1 :: "nat \<Rightarrow> nat"
  where "prod_decode1 = prod_decode_aux1 0" (* TODO: currying? *)
lemma prod_decode1_simps: "prod_decode1 m = prod_decode_aux1 0 m" unfolding prod_decode1_def by simp

definition prod_decode2 :: "nat \<Rightarrow> nat"
  where "prod_decode2 = prod_decode_aux2 0"
lemma prod_decode2_simps: "prod_decode2 m = prod_decode_aux2 0 m" unfolding prod_decode2_def by simp


thm prod_decode_aux1.induct (* NOTE: induction hyp. may have paramaters *)


compile_nat prod_decode_aux1.simps
compile_nat prod_decode_aux2.simps

HOL_To_IMP_Minus_func_correct prod_decode_aux1 by (cook mode = tailcall)
HOL_To_IMP_Minus_func_correct prod_decode_aux2 by (cook mode = tailcall)

compile_nat prod_decode1_simps
compile_nat prod_decode2_simps

HOL_To_IMP_Minus_func_correct prod_decode1 by cook
HOL_To_IMP_Minus_func_correct prod_decode2 by cook


lemmas prod_decode_simps =
  prod_decode_aux.simps prod_decode_def
  prod_decode_aux1.simps prod_decode_aux2.simps
  prod_decode1_def prod_decode2_def

(* declare prod_decode_simps[simp] *)

lemma prod_decode_aux1: "prod_decode_aux1 k m = fst (prod_decode_aux k m)"
  apply (induction k m rule: prod_decode_aux.induct)
  using prod_decode_simps by auto

lemma prod_decode_aux2: "prod_decode_aux2 k m = snd (prod_decode_aux k m)"
  apply (induction k m rule: prod_decode_aux.induct)
  using prod_decode_simps by auto

lemma prod_decode: "prod_decode x = (prod_decode1 x, prod_decode2 x)"
  using prod_decode_simps prod_decode_aux1[of 0] prod_decode_aux2[of 0] by simp


lemma prod_decode_aux1_le[simp]: "prod_decode_aux1 k m \<le> m"
proof (induction k m rule: prod_decode_aux1.induct)
  case (1 k m)
  then show ?case using prod_decode_aux1.simps by (cases "m \<le> k") simp_all
qed

lemma prod_decode_aux2_le[simp]: "prod_decode_aux2 k m \<le> k + m"
proof (induction k m rule: prod_decode_aux2.induct)
  case (1 k m)
  then show ?case using prod_decode_aux2.simps by (cases "m \<le> k") simp_all
qed

lemma prod_decode1_le[simp]: "prod_decode1 x \<le> x"
  unfolding prod_decode1_def using prod_decode_aux1_le[of 0] by simp
lemma prod_decode2_le[simp]: "prod_decode2 x \<le> x"
  unfolding prod_decode2_def using prod_decode_aux2_le[of 0] by simp


definition prod_encode :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "prod_encode m n = (m + n) * (Suc (m + n)) div 2 + m"

compile_nat prod_encode_def
HOL_To_IMP_Minus_func_correct prod_encode by cook

lemma prod_encode: "prod_encode m n = Nat_Bijection.prod_encode (m, n)"
  unfolding prod_encode_def Nat_Bijection.prod_encode_def triangle_def by simp

lemma prod_encode_inverse1[simp]: "prod_decode1 (prod_encode m n) = m"
  using prod_encode prod_decode prod_encode_inverse by force

lemma prod_encode_inverse2[simp]: "prod_decode2 (prod_encode m n) = n"
  using prod_encode prod_decode prod_encode_inverse by force

lemma prod_decode_inverse[simp]: "prod_encode (prod_decode1 x) (prod_decode2 x) = x"
  using prod_decode prod_encode prod_decode_inverse by force

(*

fun prod_encode' :: "(nat * nat) \<Rightarrow> nat" where
  "prod_encode' (m, n) = (m + n) * (Suc (m + n)) div 2 + m"


declare_compiled_const Product_Type.Pair
  return_register "prod_encode.ret"
  argument_registers "prod_encode.args.m" "prod_encode.args.k"
  compiled "tailcall_to_IMP_Minus prod_encode_IMP_tailcall"


definition pairup :: "nat \<Rightarrow> (nat * nat)" where "pairup n = (n, 3)"

compile_nat pairup_def
theorem "terminates_with_res_IMP_Minus (tailcall_to_IMP_Minus pairup_IMP_tailcall) s ''pairup.ret'' (prod_encode' (pairup (s ''pairup.args.n'')))"
  sorry

*)

subsection \<open>Options\<close>

(* encode/decode *)

fun encode_option where "encode_option None = 0" | "encode_option (Some x) = Suc x"
fun decode_option where "decode_option 0 = None" | "decode_option (Suc x) = Some x"

lemma "decode_option (encode_option x) = x" by (cases x) simp_all
lemma "encode_option (decode_option x) = x" by (cases x) simp_all

(* some *)

definition "some_nat x = Suc x"

compile_nat some_nat_def basename some
HOL_To_IMP_Minus_func_correct some_nat by cook

declare some_nat_def[simp]

lemma "encode_option (Some x) = some_nat x" unfolding some_nat_def by simp

(* none *)

definition none_nat :: nat where "none_nat = 0"
declare none_nat_def[simp]

lemma "encode_option None = none_nat" unfolding none_nat_def by simp

(* is_none *)

definition is_none_nat :: "nat \<Rightarrow> nat" where "is_none_nat m = nat_of_bool (m = 0)"

compile_nat is_none_nat_def
HOL_To_IMP_Minus_func_correct is_none_nat by cook

declare is_none_nat_def[simp]

lemma "nat_of_bool (x = None) = is_none_nat (encode_option x)" by (cases x) simp_all

(* the *)

fun the :: "nat option \<Rightarrow> nat" where "the None = 0" | "the (Some x) = x"

fun the_nat :: "nat \<Rightarrow> nat" where "the_nat 0 = 0" | "the_nat (Suc x) = x"
declare the_nat.simps[simp del]

case_of_simps the_nat_eq[simplified Nitpick.case_nat_unfold] : the_nat.simps
compile_nat the_nat_eq basename the
HOL_To_IMP_Minus_func_correct the_nat by cook

lemma "the x = the_nat (encode_option x)" using the_nat_eq by (cases x) simp_all

subsection \<open>Lists\<close>

fun encode_list where
  "encode_list [] = 0" |
  "encode_list (x # xs) = Suc (prod_encode x (encode_list xs))"
fun decode_list where
  "decode_list 0 = []" |
  "decode_list (Suc x) = prod_decode1 x # decode_list (prod_decode2 x)"

lemma "decode_list (encode_list xs) = xs" by (induction rule: encode_list.induct) simp_all
lemma "encode_list (decode_list xs) = xs" by (induction rule: decode_list.induct) simp_all


definition "cons_nat x xs = some_nat (prod_encode x xs)"

compile_nat cons_nat_def basename cons
HOL_To_IMP_Minus_func_correct cons_nat by cook

definition nil_nat :: nat where "nil_nat = 0"

fun head where "head 0 = 0" | "head (Suc x) = prod_decode1 x"
fun tail where "tail 0 = 0" | "tail (Suc x) = prod_decode2 x"
declare head.simps[simp del] tail.simps[simp del]

case_of_simps head_eq[simplified Nitpick.case_nat_unfold] : head.simps
case_of_simps tail_eq[simplified Nitpick.case_nat_unfold] : tail.simps

compile_nat head_eq
compile_nat tail_eq
HOL_To_IMP_Minus_func_correct head by (cook mode = tailcall)
HOL_To_IMP_Minus_func_correct tail by (cook mode = tailcall)


fun length_list_acc where
  "length_list_acc a 0 = a" |
  "length_list_acc a xs = length_list_acc (a + 1) (tail xs)"



end


end



