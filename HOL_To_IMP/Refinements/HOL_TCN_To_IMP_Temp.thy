theory HOL_TCN_To_IMP_Temp
  imports HOL_To_IMP_Primitives "IMP.HOL_TCN_Timing"
begin


  (* assumes inf: "\<exists>zh v. (f,reg) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup>zh\<^esup> v" *)

(* definition "interp_time1 reg g vs_arg_g = T_f_from_reg reg g vs_arg_g" *)
(* definition "interp_time reg = sum_map (\<lambda>(g, vs_arg_g). interp_time1 reg g vs_arg_g)" *)
  (* assumes "f_imp = to_imp_tc_1 f_args ctxt r0 f" *)
  (* assumes "set (special_regs f_args ctxt r t) \<subseteq> set stale" *)

lemma lookups_eq_on: assumes "s = t on set xs" shows "lookups xs s = lookups xs t"
  using assms by (simp add: eq_on_def)

abbreviation "lookup_args ctxt g \<equiv> lookups (args_from_ctxt ctxt g)"

definition "tinterp_time reg ctxt =
  sum_map
    (\<lambda>(g, vs_arg_g).
      HOL_Nat_To_IMP.least_constant_IMP (com_from_ctxt ctxt g) (T_f_from_reg reg g o lookup_args ctxt g)
      * interp_time1 reg g vs_arg_g)"

definition "well_formed_comp f_args ctxt bs stale t \<longleftrightarrow>
  tailrec t
  \<and> set (reserved_regs f_args ctxt bs t) \<subseteq> set stale
  \<and> distinct f_args
  \<and> (\<forall>g \<in> set (h_calls t). distinct (args_from_ctxt ctxt g))"

definition "well_encoded_comp f_args bs vs_arg vs_b s \<longleftrightarrow> lookups f_args s = vs_arg \<and> lookups bs s = vs_b"

definition "called_correctness ctxt reg t \<longleftrightarrow> (\<forall>g \<in> set (h_calls t).
    HOL_Nat_To_IMP.terminates_with_res_time_order_IMP
      (com_from_ctxt ctxt g) (ret_from_ctxt ctxt g)
      (f_from_reg reg g o lookup_args ctxt g) (T_f_from_reg reg g o lookup_args ctxt g))" (* can we replace f with existential ? *)


lemma ttime_non_tail:
  fixes c :: tcom
  assumes "invar c"
  assumes "f \<turnstile> (c,s1) \<Rightarrow>\<^bsup>z\<^esup> s2"
  assumes "teval_to_tail s1 c None"
  shows "ttime_to_tail s1 c z"
  sorry (* TODO *)

lemma non_tail_tailrec: "non_tail t \<Longrightarrow> tailrec t"
  by (induction t) auto

(* TODO: need assumption relating registry and context *)
lemma compiler_correct_nt:
  assumes "non_tail t"
  assumes "well_formed_comp f_args ctxt bs stale t"
  assumes "well_encoded_comp f_args bs vs_arg vs_b s"
  obtains f z s' where
    "f \<turnstile> (to_imp_tc f_args ctxt bs r stale t,s) \<Rightarrow>\<^bsup>z\<^esup> s'"
    "s' r = eval_non_tail reg vs_b vs_arg t"
    "s = s' on (Set.remove r (set stale))"
  nitpick
  sorry




(* TODO: this should (just?) use the small step semantics instead !!!! *)
(* state, term, constants, calls, new state, tail call *)
inductive tto_end :: "state \<Rightarrow> tcom \<Rightarrow> nat \<Rightarrow> (com \<times> state) list \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool" where
  "tto_end s tSKIP (Suc 0) [] s False" |
  "tto_end s (tAssign x a) (Suc (Suc 0)) [] (s(x := aval a s)) False" |
  "\<lbrakk>tto_end s1 c1 k1 gs1 s2 False; tto_end s2 c2 k2 gs2 s3 l2; k = k1 + k2; gs = gs1 @ gs2\<rbrakk>
    \<Longrightarrow> tto_end s1 (tSeq c1 c2) k gs s3 l2" | (* l1 = False ? *)
  "\<lbrakk>s b \<noteq> 0; tto_end s c1 x gs t l; y = x + 1\<rbrakk> \<Longrightarrow> tto_end s (tIf b c1 c2) y gs t l" |
  "\<lbrakk>s b = 0; tto_end s c2 x gs t l; y = x + 1\<rbrakk> \<Longrightarrow> tto_end s (tIf b c1 c2) y gs t l" |
  "\<lbrakk>(C,s) \<Rightarrow>\<^bsup>z \<^esup> t\<rbrakk> \<Longrightarrow> tto_end s (tCall C r) 0 [(C,s)] (s(r := t r)) False" |
  "tto_end s tTAIL 5 [] s True"


(*
lemma tto_end_tseqs:
  assumes "\<forall>i \<le> length cs. tto_end s (cs ! i) (ks ! i) (gss ! i)"
  shows True *)

fun tcalls where
  "tcalls (tSeq c1 c2) = tcalls c1 @ tcalls c2" |
  "tcalls (tIf x c1 c2) = tcalls c1 @ tcalls c2" |
  "tcalls (tCall C r) = [C]" |
  "tcalls _ = []"

definition "truntime_reg gs T_g = (\<forall>C \<in> gs. \<forall>s. \<exists>t. (C,s) \<Rightarrow>\<^bsup> T_g C s \<^esup> t)"
definition "tinterp_time2 T_g k gs = k + sum_map (\<lambda>(C,s). T_g C s) gs"

lemma tinterp_time2_nil: "tinterp_time2 T_g k [] = k" unfolding tinterp_time2_def by simp

theorem tto_end_non_tail:
  fixes p :: tcom
  assumes "truntime_reg (set (tcalls p)) T_g"
  assumes "tto_end s p k gs t l"
  assumes "l = False"
  shows "tp \<turnstile> (p,s) \<Rightarrow>\<^bsup>tinterp_time2 T_g k gs\<^esup> t"
using assms(2,1,3) proof (induction rule: tto_end.induct)
  case (1 s)
  then show ?case using tinterp_time2_nil tSkip by metis
next
  case (2 s x a) show ?case using tinterp_time2_nil tAssign by metis
next
  case (3 s1 c1 k1 gs1 s2 c2 k2 gs2 s3 l2 k gs)

  have *: "tinterp_time2 T_g k gs = tinterp_time2 T_g k1 gs1 + tinterp_time2 T_g k2 gs2"
    unfolding tinterp_time2_def using \<open>k = k1 + k2\<close> \<open>gs = gs1 @ gs2\<close> by simp

  have **: "truntime_reg (set (tcalls c1)) T_g" "truntime_reg (set (tcalls c2)) T_g"
    using "3.prems" unfolding truntime_reg_def by auto
  
  from 3 * ** show ?case by blast
next
  case (4 s b c1 x gs t l y c2)
  then have "truntime_reg (set (tcalls c1)) T_g" unfolding truntime_reg_def by auto
  with 4 show ?case unfolding tinterp_time2_def by auto
next
  case (5 s b c2 x gs t l y c1)
  then have "truntime_reg (set (tcalls c2)) T_g" unfolding truntime_reg_def by auto
  with 5 show ?case unfolding tinterp_time2_def by auto
next
  case (6 C s z t r)
  show ?case
    apply (rule tCall) unfolding tinterp_time2_def apply simp
    using 6 unfolding truntime_reg_def using bigstep_det by force (* TODO: cleanup *)
next
  case (7 s)
  then show ?case by blast
qed

theorem tto_end_tail:
  fixes p1 p2 :: tcom
  assumes "truntime_reg (set (tcalls p1)) T_g"
  assumes "p2 \<turnstile> (p1,s1) \<Rightarrow>\<^bsup>z\<^esup> t"
  assumes "tto_end s1 p1 k gs s2 l"
  assumes "l = True"
  shows "\<exists>z2. z = tinterp_time2 T_g k gs + z2 \<and> p2 \<turnstile> (p2,s2) \<Rightarrow>\<^bsup>z2\<^esup> t"
using assms(3,1,2,4) proof (induction arbitrary: z rule: tto_end.induct)
  case (1 s) then show ?case by blast
next
  case (2 s x a) then show ?case by blast
next
  case (3 s1 c1 k1 gs1 s2 c2 k2 gs2 s3 l2 k gs)

  have *: "tinterp_time2 T_g k gs = tinterp_time2 T_g k1 gs1 + tinterp_time2 T_g k2 gs2"
    unfolding tinterp_time2_def using \<open>k = k1 + k2\<close> \<open>gs = gs1 @ gs2\<close> by simp
  have **: "truntime_reg (set (tcalls c1)) T_g" "truntime_reg (set (tcalls c2)) T_g"
    using "3.prems" unfolding truntime_reg_def by auto

  have "p2 \<turnstile> (c1,s1) \<Rightarrow>\<^bsup>tinterp_time2 T_g k1 gs1\<^esup>  s2" using tto_end_non_tail ** 3 by blast
  then obtain y where tSeq_inv:
    "z = tinterp_time2 T_g k1 gs1 + y"
    "p2 \<turnstile> (c1, s1) \<Rightarrow>\<^bsup>tinterp_time2 T_g k1 gs1\<^esup> s2"
    "p2 \<turnstile> (c2, s2) \<Rightarrow>\<^bsup>y\<^esup> t"
    using tSeq_tE "3.prems" tdeterm by metis
  then obtain z2 where "y = tinterp_time2 T_g k2 gs2 + z2" "p2 \<turnstile> (p2, s3) \<Rightarrow>\<^bsup>z2\<^esup> t"
    using "3.IH" \<open>l2 = True\<close> ** by blast
  then show ?case using tSeq_inv * by simp
next
  case (4 s b c1 x gs t l y c2)
  then have "truntime_reg (set (tcalls c1)) T_g" unfolding truntime_reg_def apply simp by blast
  with 4 show ?case unfolding tinterp_time2_def by auto
next
  case (5 s b c2 x gs t l y c1)
  then have "truntime_reg (set (tcalls c2)) T_g" unfolding truntime_reg_def apply simp by blast
  with 5 show ?case unfolding tinterp_time2_def by auto
next
  case (6 C s z t r)
  then show ?case by blast
next
  case (7 s)
  then show ?case using tinterp_time2_nil by force
qed

lemma tto_end_struct_k:
  assumes "tto_end s c k gs t l"
  shows "k \<le> tstruct_k c"
  using assms by (induction rule: tto_end.induct) simp_all

thm tto_end_non_tail tto_end_tail

find_theorems "map fst"
lemma
  assumes compiler_correct_nt_: True
  assumes "t_imp = to_imp_tc f_args ctxt bs r stale t"
  assumes "t_time = time_to_tail reg vs_b vs_arg t"
  assumes "well_formed_comp f_args ctxt bs stale t"
  assumes "well_encoded_comp f_args bs vs_arg vs_b s"
  (* assumes "called_correctness ctxt reg t" *)
  shows "\<exists>k Cs.
    (\<exists>t l. tto_end s t_imp k Cs t l)
    \<and> length Cs = length t_time
    \<and> (\<forall>((C,s), (g,vs_arg_g)) \<in> set (zip Cs t_time).
          C = com_from_ctxt ctxt g \<and> vs_arg_g = lookup_args ctxt g s)"
using assms(2-4) proof (induction t arbitrary: t_imp t_time bs r stale vs_b s)
  case (hLet t1 t2)
  then show ?case sorry
next
  case (hLetBound x)
  then show ?case sorry
next
  case (hArg x)
  then show ?case sorry
next
  case (hNumber x)
  then show ?case sorry
next
  case (hIf t1 t2 t3)
  then show ?case sorry
next
  case (hCall g ts)
  let ?xs = "make_n_fresh (length ts) stale ''Call.x.''"
  let ?cs1 = "mapi (\<lambda>i t. to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t) ts"
  let ?cs2 = "mapi (\<lambda>i t. tAssign (args_from_ctxt ctxt g ! i) (A (V (?xs ! i)))) ts"
  let ?call = "tSeq (tCall (com_from_ctxt ctxt g) (ret_from_ctxt ctxt g)) (tAssign r (A (V (ret_from_ctxt ctxt g))))"

  have "t_imp = t_seqs (?cs1 @ ?cs2) ?call" using hCall by (simp add: Let_def split_beta)

  let ?x = "\<lambda>s. f_from_reg reg g (lookup_args ctxt g s)"
  have "tto_end s ?call 2 [(com_from_ctxt ctxt g,s)] (s(ret_from_ctxt ctxt g := ?x s, r := ?x s)) False" for s
    sorry

  then show ?case sorry
next
  case (hTAIL x)
  then show ?case sorry
qed




    (* \<and> (\<forall>((C,s), (g,vs_arg_g)) \<in> set (zip gs (time_to_tail reg vs_b vs_arg t)). *)
          (* C = com_from_ctxt ctxt g \<and> vs_arg_g = lookup_args ctxt g s)" *)



lemma
  assumes compiler_correct_nt_: True
  assumes "t_imp = to_imp_tc f_args ctxt bs r stale t"
  assumes "well_formed_comp f_args ctxt bs stale t"
  assumes "well_encoded_comp f_args bs vs_arg vs_b s"
  assumes "called_correctness ctxt reg t"
  shows "\<exists>k z.
    ttime_to_tail s t_imp (k + z)
    \<and> k \<le> tstruct_k t_imp
    \<and> z \<le> tinterp_time reg ctxt (time_to_tail reg vs_b vs_arg t)"
using assms(2-5) proof (induction t arbitrary: t_imp bs r stale vs_b s)
  case (hLet t1 t2)
  thm hLet.prems(1)[simplified]
  thm hLet.IH(1) hLet.IH(2)

  thm hLet.prems

  let ?x_var = "fresh' stale ''Let.x''"
  let ?t_imp1 = "to_imp_tc f_args ctxt bs ?x_var stale t1"

  have wf1: "well_formed_comp f_args ctxt bs stale t1" using hLet.prems(2)
    unfolding well_formed_comp_def using non_tail_tailrec apply auto apply (simp only: reserved_regs_def h_calls.simps map_append)
    by auto
  then obtain k1 z1 where k1z1:
      "ttime_to_tail s ?t_imp1 (k1 + z1)"
      "k1 \<le> tstruct_k ?t_imp1"
      "z1 \<le> tinterp_time reg ctxt (time_to_tail reg vs_b vs_arg t1)"
    using hLet.IH(1)[where t_imp = ?t_imp1 and s = s and bs = bs and vs_b = vs_b and r = ?x_var and stale = stale] hLet.prems
    unfolding called_correctness_def by auto

  have ob1: "non_tail t1" using hLet unfolding well_formed_comp_def by simp
  have ob2: "well_encoded_comp f_args bs vs_arg vs_b s" using hLet by simp
  obtain f y1 s1
      where t1s1: "f \<turnstile> (?t_imp1,s) \<Rightarrow>\<^bsup>y1\<^esup> s1"
      and s1_xvar: "s1 ?x_var = eval_non_tail reg vs_b vs_arg t1"
      and s1: "s = s1 on (Set.remove ?x_var (set stale))"
    using compiler_correct_nt[OF ob1 wf1 ob2, simplified] by blast

  have "tailrec t1" using well_formed_comp_def wf1 by blast
  then have inv: "invar ?t_imp1" using to_imp_invar by blast
  have y1: "y1 = k1 + z1" using ttime_non_tail[OF inv t1s1] sorry (* ttime_to_tail for non-tail MUST INVESTIGATE AND WRITE LEMMA *)

  let ?t_imp2 = "to_imp_tc f_args ctxt (?x_var # bs) r (?x_var # stale) t2"
  have "tailrec t2" using hLet unfolding well_formed_comp_def by simp

  have t2_1: "well_formed_comp f_args ctxt (?x_var # bs) (?x_var # stale) t2"
    using hLet.prems(2) unfolding well_formed_comp_def apply auto sorry (* almost sub-term *)
  have "set f_args \<subseteq> Set.remove ?x_var (set stale)" using fresh_not_in_stale
    unfolding remove_def apply simp using hLet.prems(2) unfolding well_formed_comp_def reserved_regs_def by simp
  then have t2_2_1: "lookups f_args s1 = vs_arg"
    apply (subst lookups_eq_on[where s = s, symmetric])
    using s1 apply blast using hLet.prems(3) unfolding well_encoded_comp_def by blast
  have "set bs \<subseteq> Set.remove ?x_var (set stale)" using fresh_not_in_stale
    unfolding remove_def apply simp using hLet.prems(2) unfolding well_formed_comp_def reserved_regs_def by simp
  then have t2_2_2: "lookups (?x_var # bs) s1 = eval_non_tail reg vs_b vs_arg t1 # vs_b" apply auto
    using s1_xvar apply blast
    apply (subst lookups_eq_on[where s = s, symmetric])
    using s1 apply blast using hLet.prems(3) unfolding well_encoded_comp_def by blast
  from t2_2_1 t2_2_2 have t2_2: "well_encoded_comp f_args (?x_var # bs) vs_arg (eval_non_tail reg vs_b vs_arg t1 # vs_b) s1"
    unfolding well_encoded_comp_def by simp
  have t2_3: "called_correctness ctxt reg t2" using hLet.prems(4) unfolding called_correctness_def by auto
  obtain k2 z2 where k2z2:
      "ttime_to_tail s1 ?t_imp2 (k2 + z2)"
      "k2 \<le> tstruct_k ?t_imp2"
      "z2 \<le> tinterp_time reg ctxt (time_to_tail reg (eval_non_tail reg vs_b vs_arg t1 # vs_b) vs_arg t2)"
    using hLet.IH(2)[where t_imp = ?t_imp2 and r = r and s = s1 and bs = "?x_var # bs"
      and vs_b = "eval_non_tail reg vs_b vs_arg t1 # vs_b" and stale = "?x_var # stale", OF _ t2_1 t2_2 t2_3, simplified]
    by blast

  from t1s1 k2z2
  have "ttime_to_tail s t_imp (y1 + (k2 + z2))" using hLet.prems(1) apply simp unfolding Let_def apply (rule ttime_to_tail.intros(3)) by auto
  moreover have "y1 + (k2 + z2) = (k1 + k2) + (z1 + z2)" using y1 by linarith
  moreover have "k1 + k2 \<le> tstruct_k t_imp" using hLet.prems(1) apply simp unfolding Let_def using k1z1 k2z2 by simp
  moreover have "z1 + z2 \<le> tinterp_time reg ctxt (time_to_tail reg vs_b vs_arg (hLet t1 t2))"
    apply simp using k1z1 k2z2 unfolding tinterp_time_def by simp

  ultimately show ?case by auto

    (* idea: - solve premises of IH for t1, get k1 and z1 as structural/functional times for compiled t1
               AND use compiler correctness to obtain y1 and s1 as run time and updated state of compiled t1
             - show y1 = k1 + z1 using ttime_to_tail non_tail lemma for compiled t1
             - ... *)
next
  case (hLetBound n)
  then have t_imp: "t_imp = tAssign r (A (V (bs ! n)))" by simp

  from t_imp have k: "ttime_to_tail s t_imp (2 + 0)" using ttime_to_tail.intros by simp
  from t_imp have z: "2 \<le> tstruct_k t_imp" by simp

  from k z show ?case by blast
next
  case (hArg n)
  then have t_imp: "t_imp = tAssign r (A (V (f_args ! n)))" by simp

  from t_imp have k: "ttime_to_tail s t_imp (2 + 0)" using ttime_to_tail.intros by simp
  from t_imp have z: "2 \<le> tstruct_k t_imp" by simp

  from k z show ?case by blast
next
  case (hNumber n) (* then show ?case using ttime_to_tail.intros by fastforce *)
  then have t_imp: "t_imp = tAssign r (A (N n))" by simp

  from t_imp have k: "ttime_to_tail s t_imp (2 + 0)" using ttime_to_tail.intros by simp
  from t_imp have z: "2 \<le> tstruct_k t_imp" by simp

  from k z show ?case by blast
next
  case (hIf t1 t2 t3)
  then show ?case sorry
next
  case (hCall g ts)
  then show ?case sorry
next
  case (hTAIL ts)
  then show ?case sorry
qed

lemma "\<exists>c. \<forall>s. tstruct_k t_imp + something \<le> c * interp_time reg (time_to_tail reg vs_b vs_arg t)" oops
(* in fact, we can calculate c as the max of the structural-constant-factor and all T_f_const-ants or so *)

end
