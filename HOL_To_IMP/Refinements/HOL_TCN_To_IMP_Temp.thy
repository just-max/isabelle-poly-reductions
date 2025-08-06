theory HOL_TCN_To_IMP_Temp
  imports HOL_Nat_To_IMP.IMP_Terminates_With "IMP.HOL_TCN_To_IMP" (* HOL_Nat_To_IMP.Compile_HOL_Nat_To_IMP *)
(* TODO: rearrange import of stuff from Compile *)
begin

method repeat methods m = (m; repeat \<open>m\<close>)?

abbreviation "lookups names (s :: state) \<equiv> map s names"
abbreviation "lookup_args crgt g \<equiv> lookups (args_from_crgt crgt g)"

(* note: lookups xs s = map s xs *)
lemma map_eq_on_subset_eq: fixes A assumes "set xs \<subseteq> A" "f = g on A" shows "map f xs = map g xs"
  using assms unfolding eq_on_def by (induction xs) auto

abbreviation disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"  (infix \<open>\<inter>\<^sub>\<emptyset>\<close> 60)
  where "A \<inter>\<^sub>\<emptyset> B \<equiv> A \<inter> B = {}" for A B

lemma disjoint_subset2:
  fixes A B
  assumes "B \<subseteq> B'"
  assumes "A \<inter>\<^sub>\<emptyset> B'"
  shows "A \<inter>\<^sub>\<emptyset> B"
  using assms by blast

definition "compiler_args_invar crgt f_args bs keep t \<longleftrightarrow>
  HOL_TCN_Timing.invar t
  \<and> distinct f_args
  \<and> set f_args \<inter>\<^sub>\<emptyset> set (call_registers crgt t)
  \<and> set bs \<inter>\<^sub>\<emptyset> set (call_registers crgt t)
  \<and> set bs \<inter>\<^sub>\<emptyset> set f_args
  \<and> set keep \<inter>\<^sub>\<emptyset> set f_args
  \<and> set keep \<inter>\<^sub>\<emptyset> set (call_registers crgt t)
  \<and> (\<forall>g\<in>fst ` set (calls t). distinct (args_from_crgt crgt g))
  \<and> (\<forall>(g,ts)\<in>set (calls t). length ts = length (args_from_crgt crgt g))"
(*
- The term must be tail-recursive, i.e. satisfy the invariant.

- Register lists that are written to must be distinct, otherwise writing a later register will
  overwrite a register earlier in the list. Thus, f_args and g_args for each called g must be
  distinct: f_args is written before a tail call, g_args on a call to g.

- If a value is stored to a register (list) R, then later the register (list) W is written to, and
  then later that value should be read back from R, R and W must be disjoint.
  Otherwise, the write to W could overwrite the value in R. We consider "f_args" and "bs" to be
  stored at the beginning of execution, and "keep" and "r" to be read after execution. We have:

  - f_args: stored at the beginning of execution, written while preparing for a tail call, read at argument variable read
  - bs: stored at the beginning of execution, read at bound variable read
  - g_args for each call of a function g: written and then immediately read by the called function.
  - g_ret for each call of a function g: written after the call and the immediately read for copying.
  - r: written immediately before the end of execution, read after execution
  - keep: stored before execution, read after execution.

  Conflict matrix:

         W: f_args bs g_args g_ret r
    R:     +------------------------
    f_args |        -      X     X -
    bs     |     X         X     X -
    g_args |     -  -      -     - -
    g_ret  |     -  -      -     - -
    r      |     -  -      -     - -
    keep   |     X  -      X     X X

  We special-case the keep/r conflict: instead of requiring keep and r to be disjoint, the
  correctness theorems show that "keep" except "r" is preserved.

- At each call site, the correct number of arguments must be provided to the called function.
*)

lemma compiler_args_invar_subset:
  assumes "invar t"
  assumes "set (calls t) \<subseteq> set (calls t')"
  assumes "compiler_args_invar crgt f_args bs keep t'"
  shows "compiler_args_invar crgt f_args bs keep t"
  using disjoint_subset2[where B = "set (call_registers crgt t)" and B' = "set (call_registers crgt t')"]
  using assms call_registers_set unfolding compiler_args_invar_def split_beta by auto

(* the "state" of the HOL-TCN execution (args, bounds) is related
   to the state of the IMP-TC execution *)
definition "relate_exec_state f_args bs vs_arg vs_b s \<longleftrightarrow>
  lookups f_args s = vs_arg \<and> lookups bs s = vs_b"

(*
definition "called_correctness crgt frgt fs \<longleftrightarrow> (\<forall>f \<in> fs.
    HOL_Nat_To_IMP.terminates_with_res_time_order_IMP
      (com_from_crgt crgt f) (ret_from_crgt crgt f)
      (f_from_frgt frgt f o lookup_args crgt f) (T_f_from_frgt frgt f o lookup_args crgt f))" (* can we replace ...  with existential ? *)
*)

definition "relate_rgt_correctness frgt crgt fs \<longleftrightarrow> (\<forall>f \<in> fs.
  \<forall>s. terminates_with_res_IMP (com_from_crgt crgt f) s (ret_from_crgt crgt f) (f_from_frgt frgt f (lookup_args crgt f s)))"


lemma snoc_obtain:
  assumes "xs \<noteq> []"
  obtains x xs' where "xs = xs' @ [x]"
  using assms by (meson rev_exhaust)

lemma snoc_list_induct2 [case_names len Nil snoc]:
  assumes len: "length xs = length ys"
  assumes nil: "P [] []"
  assumes snoc: "\<And>xs x ys y. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs @ [x]) (ys @ [y])"
  shows "P xs ys"
proof-
  let ?P = "\<lambda>xs ys. P (rev xs) (rev ys)"
  have "length (rev xs) = length (rev ys)" using len by simp
  then have "?P (rev xs) (rev ys)"
  proof (induction rule: list_induct2)
  qed (simp_all add: nil snoc)
  then show "P xs ys" by simp
qed

lemma snoc_list_induct3 [case_names len1 len2 Nil snoc]:
  assumes len: "length xs = length ys" "length ys = length zs"
  assumes nil: "P [] [] []"
  assumes snoc: "\<And>xs x ys y zs z. length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow> P xs ys zs \<Longrightarrow> P (xs @ [x]) (ys @ [y]) (zs @ [z])"
  shows "P xs ys zs"
proof-
  let ?P = "\<lambda>xs ys zs. P (rev xs) (rev ys) (rev zs)"
  have "length (rev xs) = length (rev ys)" "length (rev ys) = length (rev zs)" using len by simp_all
  then have "?P (rev xs) (rev ys) (rev zs)"
  proof (induction rule: list_induct3)
  qed (simp_all add: nil snoc)
  then show "P xs ys zs" by simp
qed

lemma nth_append_length_eq:
  assumes "length xs = n"
  shows "(xs @ y # zs) ! n = y"
  apply (subst nth_append) using assms by simp

(* executing a list of terms (as in the call and tail-call cases) *)
lemma compiled_list_bigstep:
  assumes lengths: "length vs = length ts" "length xs = length ts"
  assumes rel: "relate_exec_state f_args bs vs_arg vs_b s"
  assumes dist: "distinct xs"
  assumes keep_xs: "set xs \<subseteq> set keep"
  assumes disj: "set f_args \<inter>\<^sub>\<emptyset> set xs" "set bs \<inter>\<^sub>\<emptyset> set xs"
  assumes sem: "\<And>i s.
    \<lbrakk> i < length ts; relate_exec_state f_args bs vs_arg vs_b s \<rbrakk> \<Longrightarrow>
    \<exists>z s'. f \<turnstile> (to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i), s) \<Rightarrow>\<^bsup>z\<^esup> s' \<and>
             s' (xs ! i) = (vs ! i) \<and> s' = s on set f_args \<union> set bs \<union> set keep - {xs ! i}"
  shows "\<exists>z s'. f \<turnstile> (t_seqs' (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts)), s) \<Rightarrow>\<^bsup>z\<^esup> s' \<and>
                lookups xs s' = vs \<and> s' = s on set f_args \<union> set bs \<union> set keep - set xs"
using dist keep_xs disj sem proof (induction ts xs vs rule: snoc_list_induct3)
  case Nil
  then show ?case unfolding generate_def by auto
next
  case (snoc ts t xs x vs v)

  (* obtain the IH *)

  from snoc have *: "distinct xs" "set xs \<subseteq> set keep" "set f_args \<inter>\<^sub>\<emptyset> set xs" "set bs \<inter>\<^sub>\<emptyset> set xs" by simp_all

  have "i < length (ts @ [t])" if "i < length ts" for i using that by simp
  with snoc.prems(5) have **: "\<exists>z s'.
      f \<turnstile> (to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i), s) \<Rightarrow>\<^bsup>z\<^esup>  s' \<and>
      s' (xs ! i) = vs ! i \<and> s' = s on set f_args \<union> set bs \<union> set keep - {xs ! i}"
    if "i < length ts" "relate_exec_state f_args bs vs_arg vs_b s" for i s
    using that nth_append_left snoc.hyps by metis

  with snoc.IH[OF * **] obtain z1 s2 where exec1:
    "f \<turnstile> (t_seqs' (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts)), s) \<Rightarrow>\<^bsup>z1\<^esup> s2"
    "lookups xs s2 = vs" "s2 = s on set f_args \<union> set bs \<union> set keep - set xs"
    by blast

  (* obtain the step *)

  have *: "length ts < length (ts @ [t])" by simp

  from rel exec1(3) snoc.prems(3,4) have **: "relate_exec_state f_args bs vs_arg vs_b s2"
    unfolding relate_exec_state_def by fastforce

  from snoc.prems(5)[OF * **]
  obtain z2 s3 where exec2:
      "f \<turnstile> (to_imp_tc f_args crgt bs ((xs @ [x]) ! length ts) keep ((ts @ [t]) ! length ts), s2) \<Rightarrow>\<^bsup>z2\<^esup> s3"
      "s3 ((xs @ [x]) ! length ts) = (vs @ [v]) ! length ts"
      "s3 = s2 on set f_args \<union> set bs \<union> set keep - {(xs @ [x]) ! length ts}"
    by blast

  (* put it together *)

  have "(xs @ [x]) ! i = xs ! i" "(ts @ [t]) ! i = ts ! i" if "i < length ts" for i
    using nth_append_left snoc.hyps that by metis+
  then have "generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts) =
      generate (\<lambda>i. to_imp_tc f_args crgt bs ((xs @ [x]) ! i) keep ((ts @ [t]) ! i)) (length ts)"
    unfolding generate_def by simp
  then have append_cs: "generate (\<lambda>i. to_imp_tc f_args crgt bs ((xs @ [x]) ! i) keep ((ts @ [t]) ! i)) (length (ts @ [t])) =
    generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts) @
    [to_imp_tc f_args crgt bs ((xs @ [x]) ! length ts) keep ((ts @ [t]) ! length ts)]"
    by (simp add: generate_snoc)

  have "f \<turnstile> (t_seqs' (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts));;
              to_imp_tc f_args crgt bs ((xs @ [x]) ! length ts) keep ((ts @ [t]) ! length ts), s) \<Rightarrow>\<^bsup>z1 + z2\<^esup> s3"
    using exec1 exec2 by blast
  then have *: "f \<turnstile> (t_seqs' (generate (\<lambda>i. to_imp_tc f_args crgt bs ((xs @ [x]) ! i) keep ((ts @ [t]) ! i)) (length (ts @ [t]))), s) \<Rightarrow>\<^bsup>z1 + z2\<^esup> s3"
    using append_cs t_seqs'_t_seqs by fastforce

  have nth: "(xs @ [x]) ! length ts = x" "(vs @ [v]) ! length ts = v"
    using nth_append_length_eq snoc.hyps by metis+

  from exec2(2) have "s3 x = v" using snoc.hyps nth_append_length by metis
  moreover from exec2(3) nth(1) snoc.prems(1,2) have "s3 = s2 on set xs" by auto
  ultimately have **: "lookups (xs @ [x]) s3 = vs @ [v]" using exec1(2) by auto

  have ***: "s3 = s on set f_args \<union> set bs \<union> set keep - set (xs @ [x])"
    using DiffE DiffI UnCI empty_set eq_on_def exec1(3) exec2(3) nth(1) by auto

  from * ** *** show ?case by blast
qed (simp_all add: lengths)

(* copying a list of registers *)
lemma copy_list_bigstep:
  assumes "length xs = length ys"
  assumes "distinct ys"
  assumes "set xs \<inter> set ys = {}"
    (* technically, these assumptions could be weakened *)
  obtains s' where
    "f \<turnstile> (t_seqs' (generate (\<lambda>i. (ys ! i) ::= A (V (xs ! i))) (length xs)),s) \<Rightarrow>\<^bsup>Suc (2 * length xs)\<^esup> s'"
    "lookups ys s' = lookups xs s" "s' = s on (- set ys)"
using assms proof (induction xs ys arbitrary: thesis rule: snoc_list_induct2)
  case Nil
  then show ?case unfolding generate_def using tSkip_tE by auto
next
  case (snoc xs x ys y)

  let ?cs = "\<lambda>xs ys. generate (\<lambda>i. (ys ! i) ::= A (V (xs ! i)) :: tcom) (length xs)"

  let ?cs1 = "?cs xs ys"
  let ?c2 = "y ::= A (V x) :: tcom"
  let ?cs' = "?cs (xs @ [x]) (ys @ [y])"

  have cs': "?cs' = ?cs1 @ [?c2]"
    apply (simp add: generate_snoc)
    unfolding generate_def using nth_append_left snoc by fastforce

  from snoc obtain s2 where ih:
      "f \<turnstile> (t_seqs' ?cs1, s) \<Rightarrow>\<^bsup>Suc (2 * length xs)\<^esup> s2"
      "lookups ys s2 = lookups xs s" "s2 = s on (- set ys)"
    by auto
  moreover obtain s3 where step:
      "f \<turnstile> (?c2, s2) \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> s3"
      "s3 y = s2 x" "s3 = s2 on (- {y})"
    by fastforce
  ultimately have "f \<turnstile> (t_seqs' ?cs1;; ?c2, s) \<Rightarrow>\<^bsup>Suc (2 * length (xs @ [x]))\<^esup> s3" by auto
  then have "f \<turnstile> (t_seqs' (?cs1 @ [?c2]), s) \<Rightarrow>\<^bsup>Suc (2 * length (xs @ [x]))\<^esup> s3" 
    using t_seqs'_snoc t_seqs'_t_seqs by simp
  then have 1: "f \<turnstile> (t_seqs' ?cs', s) \<Rightarrow>\<^bsup>Suc (2 * length (xs @ [x]))\<^esup> s3"
    by (subst cs') assumption

  have 2: "lookups (ys @ [y]) s3 = lookups (xs @ [x]) s"
    using ih step snoc by auto

  have 3: "s3 = s on (- set (ys @ [y]))"
    using ih step by auto

  from 1 2 3 snoc show ?case by blast
qed (simp add: assms)

lemma compiled_list_bigstep':
  assumes "length vs = length ts" "length xs = length ts"
  assumes "relate_exec_state f_args bs vs_arg vs_b s"
  assumes "distinct xs"
  assumes "set xs \<subseteq> set keep"
  assumes "set f_args \<inter>\<^sub>\<emptyset> set xs" "set bs \<inter>\<^sub>\<emptyset> set xs"
  assumes "\<And>i s.
    \<lbrakk> i < length ts; relate_exec_state f_args bs vs_arg vs_b s \<rbrakk> \<Longrightarrow>
    \<exists>z s'. f \<turnstile> (to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i), s) \<Rightarrow>\<^bsup>z\<^esup> s' \<and>
             s' (xs ! i) = (vs ! i) \<and> s' = s on set f_args \<union> set bs \<union> set keep - {xs ! i}"
  obtains z s' where
    "f \<turnstile> (t_seqs' (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts)), s) \<Rightarrow>\<^bsup>z\<^esup> s'"
    "lookups xs s' = vs" "s' = s on set f_args \<union> set bs \<union> set keep - set xs"
  using compiled_list_bigstep[OF assms] by blast

lemma copy_list_bigstep':
  assumes "length xs = n"
  assumes "length ys = n"
  assumes "distinct ys"
  assumes "set xs \<inter> set ys = {}"
  obtains s' where
    "f \<turnstile> (t_seqs' (generate (\<lambda>i. (ys ! i) ::= A (V (xs ! i))) n),s) \<Rightarrow>\<^bsup>Suc (2 * n)\<^esup> s'"
    "lookups ys s' = lookups xs s" "s' = s on (- set ys)"
  using copy_list_bigstep[where xs = xs and ys = ys] assms by auto


abbreviation "calls_r t \<equiv> set (map fst (calls t))"

lemma Un_Diff_cancel1: "A \<union> B - A = B - A" for A B :: "'a set"
  by blast

theorem compiler_correct_no_tails:
  assumes "\<not> tails t"
  assumes "(f,frgt) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup>z\<^esup> v"
  assumes "compiler_args_invar crgt f_args bs keep t"
  assumes "relate_rgt_correctness frgt crgt (calls_r t)"
  assumes "relate_exec_state f_args bs vs_arg vs_b s"
  shows "\<exists>z_c s'.
    f_c \<turnstile> (to_imp_tc f_args crgt bs r keep t,s) \<Rightarrow>\<^bsup>z_c\<^esup> s'
    \<and> s' r = v
    \<and> s' = s on set f_args \<union> set bs \<union> set keep - {r}"
using assms proof (induction t arbitrary: vs_b z v bs keep s r crgt)
  case (hLet t1 t2)

  let ?r1 = "fresh' (stale_registers f_args crgt bs keep LET t1 IN t2) ''Let.x''"
  let ?t1_c = "to_imp_tc f_args crgt bs ?r1 keep t1"
  let ?t2_c = "to_imp_tc f_args crgt (?r1 # bs) r (?r1 # keep) t2"

  (* solve assumptions and obtain IH for t1 (and solve some assumptions for t2 at the same time, where convenient) *)

  have no_tails: "\<not> HOL_TCN_Timing.tails t1" "\<not> HOL_TCN_Timing.tails t2" using hLet by simp_all

  obtain z1 v1 z2 where
      "z = z1 + z2" and inv: "(f, frgt) \<turnstile> (t1, vs_b, vs_arg) \<Rightarrow>\<^bsup>z1\<^esup> v1" "(f, frgt) \<turnstile> (t2, v1 # vs_b, vs_arg) \<Rightarrow>\<^bsup>z2\<^esup> v"
    using hLet_case hLet.prems by blast

  have args_invar1: "compiler_args_invar crgt f_args bs keep t1"
    using hLet.prems compiler_args_invar_subset[where t' = "LET t1 IN t2"] by simp

  have rel_rgt: "relate_rgt_correctness frgt crgt (calls_r t1)" "relate_rgt_correctness frgt crgt (calls_r t2)"
    using hLet unfolding relate_rgt_correctness_def by simp_all

  have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" using hLet by blast

  obtain z1_c s2 where ih1:
      "f_c \<turnstile> (?t1_c, s) \<Rightarrow>\<^bsup>z1_c\<^esup> s2" "s2 ?r1 = v1" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
    using hLet.IH(1) no_tails(1) inv(1) args_invar1 rel_rgt(1) rel_state1 by blast

  (* solve assumptions and obtain IH for t2 *)

  have "?r1 \<notin> set f_args"
    apply (rule contra_subsetD[OF _ fresh_not_in_stale])
    unfolding stale_registers_def by simp
  moreover have "?r1 \<notin> set (call_registers crgt t2)"
    apply (rule contra_subsetD[OF _ fresh_not_in_stale])
    using call_registers_set unfolding stale_registers_def by auto
  moreover have "compiler_args_invar crgt f_args bs keep t2"
    using hLet.prems compiler_args_invar_subset[where t' = "LET t1 IN t2"] by simp
  ultimately have args_invar2: "compiler_args_invar crgt f_args (?r1 # bs) (?r1 # keep) t2"
    using hLet.prems(3) unfolding compiler_args_invar_def by auto

  have s_like_s2: "s2 = s on set f_args \<union> set bs \<union> set keep" (* TODO *)
    by (smt (verit) DiffI Un_iff eq_on_def fresh_not_in_stale ih1(3) set_append singletonD stale_registers_def)
  then have rel_state2: "relate_exec_state f_args (?r1 # bs) vs_arg (v1 # vs_b) s2"
    using hLet.prems(5) unfolding relate_exec_state_def using ih1 by fastforce

  obtain z2_c s3 where ih2:
      "f_c \<turnstile> (?t2_c, s2) \<Rightarrow>\<^bsup>z2_c\<^esup>  s3" "s3 r = v"
      "s3 = s2 on set f_args \<union> set (?r1 # bs) \<union> set (?r1 # keep) - {r}"
    using hLet.IH(2) no_tails(2) inv(2) args_invar2 rel_rgt(2) rel_state2 by blast

  (* put it together *)

  have s2_like_s3: "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
    using Un_Diff ih2(3) by auto
  with s_like_s2 have s_like_s3: "s3 = s on set f_args \<union> set bs \<union> set keep - {r}"
    by (simp add: eq_on_def)

  show ?case
    unfolding to_imp_tc.simps Let_def
    using ih1 ih2 s_like_s3 by blast
next
  case (hLetBound n)
  show ?case
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    from hLetBound_case hLetBound have "v = vs_b ! n" "n < length vs_b" by auto
    then have "aval (A (V (bs ! n))) s = v" using hLetBound unfolding relate_exec_state_def by auto
    then show "f_c \<turnstile> (to_imp_tc f_args crgt bs r keep (hLetBound n), s) \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> s(r := v)"
      by (metis tbig_step_t.tAssign to_imp_tc.simps(3))
  qed (simp_all add: eq_on_def)
next
  case (hArg n)
  show ?case
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    from hArg_case hArg have "v = vs_arg ! n" "n < length vs_arg" by auto
    then have "aval (A (V (f_args ! n))) s = v" using hArg unfolding relate_exec_state_def by auto
    then show "f_c \<turnstile> (to_imp_tc f_args crgt bs r keep (hArg n), s) \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> s(r := v)"
      by (metis tbig_step_t.tAssign to_imp_tc.simps(4))
  qed (simp_all add: eq_on_def)
next
  case (hNumber n)
  show ?case
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    have "aval (A (N n)) s = v" using hNumber unfolding relate_exec_state_def by auto
    then show "f_c \<turnstile> (to_imp_tc f_args crgt bs r keep (hNumber n), s) \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> s(r := v)"
      by (metis tbig_step_t.tAssign to_imp_tc.simps(5))
  qed (simp_all add: eq_on_def)
next
  case (hIf t1 t2 t3)

  let ?r1 = "fresh' (stale_registers f_args crgt bs keep (IF t1\<noteq>0 THEN t2 ELSE t3)) ''If.x''"

  have no_tails: "\<not> HOL_TCN_Timing.tails t1" "\<not> HOL_TCN_Timing.tails t2" "\<not> HOL_TCN_Timing.tails t3" using hIf by simp_all
  then have "invar t1" "invar t2" "invar t3" by simp_all
  then have args_invar:
      "compiler_args_invar crgt f_args bs keep t1"
      "compiler_args_invar crgt f_args bs keep t2"
      "compiler_args_invar crgt f_args bs keep t3"
    using hIf.prems compiler_args_invar_subset[where t = t1 and t' = "IF t1\<noteq>0 THEN t2 ELSE t3"] apply simp
    using hIf.prems compiler_args_invar_subset[where t = t2 and t' = "IF t1\<noteq>0 THEN t2 ELSE t3"] apply fastforce
    using hIf.prems compiler_args_invar_subset[where t = t3 and t' = "IF t1\<noteq>0 THEN t2 ELSE t3"] apply fastforce (* TODO ? *)
    done

  have rel_rgt: "relate_rgt_correctness frgt crgt (calls_r t1)" "relate_rgt_correctness frgt crgt (calls_r t2)" "relate_rgt_correctness frgt crgt (calls_r t3)"
    using hIf unfolding relate_rgt_correctness_def by simp_all

  have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" using hIf by blast

  show ?case
  proof (cases rule: hIf_case[OF hIf.prems(2)])
    case (1 z1 v1 z2)

    obtain z1_c s2 where ih1:
        "f_c \<turnstile> (to_imp_tc f_args crgt bs ?r1 keep t1, s) \<Rightarrow>\<^bsup>z1_c\<^esup> s2"
        "s2 ?r1 = v1" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
      using hIf.IH(1) no_tails(1) 1 args_invar(1) rel_rgt(1) rel_state1 by blast

    have s_like_s2: "s2 = s on set f_args \<union> set bs \<union> set keep" (* TODO *)
      by (smt (verit) DiffI Un_iff eq_on_def fresh_not_in_stale ih1(3) set_append singletonD stale_registers_def)
    then have rel_state2: "relate_exec_state f_args bs vs_arg vs_b s2"
      using hIf.prems(5) unfolding relate_exec_state_def using ih1 by fastforce

    obtain z2_c s3 where ih2:
        "f_c \<turnstile> (to_imp_tc f_args crgt bs r keep t2, s2) \<Rightarrow>\<^bsup>z2_c\<^esup>  s3" "s3 r = v"
        "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
      using hIf.IH(2) no_tails(2) 1 args_invar(2) rel_rgt(2) rel_state2 by blast
  
    have s2_like_s3: "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
      using Un_Diff ih2(3) by auto
    with s_like_s2 have s_like_s3: "s3 = s on set f_args \<union> set bs \<union> set keep - {r}"
      by (simp add: eq_on_def)
  
    show ?thesis
      unfolding to_imp_tc.simps Let_def
      using ih1 ih2 s_like_s3 1 by blast
  next
    case (2 z1 z2)

    obtain z1_c s2 where ih1:
        "f_c \<turnstile> (to_imp_tc f_args crgt bs ?r1 keep t1, s) \<Rightarrow>\<^bsup>z1_c\<^esup> s2"
        "s2 ?r1 = 0" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
      using hIf.IH(1) no_tails(1) 2(2) args_invar(1) rel_rgt(1) rel_state1 by metis

    have s_like_s2: "s2 = s on set f_args \<union> set bs \<union> set keep" (* TODO *)
      by (smt (verit) DiffI Un_iff eq_on_def fresh_not_in_stale ih1(3) set_append singletonD stale_registers_def)
    then have rel_state3: "relate_exec_state f_args bs vs_arg vs_b s2"
      using hIf.prems(5) unfolding relate_exec_state_def using ih1 by fastforce

    obtain z2_c s3 where ih3:
        "f_c \<turnstile> (to_imp_tc f_args crgt bs r keep t3, s2) \<Rightarrow>\<^bsup>z2_c\<^esup>  s3" "s3 r = v"
        "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
      using hIf.IH(3) no_tails(3) 2 args_invar(3) rel_rgt(3) rel_state3 by blast
  
    have s2_like_s3: "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
      using Un_Diff ih3(3) by auto
    with s_like_s2 have s_like_s3: "s3 = s on set f_args \<union> set bs \<union> set keep - {r}"
      by (simp add: eq_on_def)
  
    show ?thesis
      unfolding to_imp_tc.simps Let_def
      using ih1 ih3 s_like_s3 2 by blast
  qed
next
  case (hCall gr ts)

  let ?g = "f_from_frgt frgt gr"
  let ?T_g = "T_f_from_frgt frgt gr"

  obtain zs vs where
          z: "z = sum_list zs + ?T_g vs"
      and lengths: "length zs = length ts" "length vs = length ts"
      and args_bigstep: "\<forall>i<length ts. (f, frgt) \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>zs ! i\<^esup> vs ! i"
      and gvs: "?g vs = v"
    using hCall_case hCall split_from_frgt by auto


  (* part 1: computing the arguments *)

  let ?xs = "make_n_fresh (stale_registers f_args crgt bs keep (hCall gr ts)) ''Call.x.'' (length ts)"
  let ?c1 = "t_seqs' (generate (\<lambda>i. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ keep) (ts ! i)) (length ts))"


  have "length vs = length ts" "length ?xs = length ts"
    using lengths unfolding make_n_fresh_def generate_def by simp_all
  moreover have "relate_exec_state f_args bs vs_arg vs_b s" using hCall by blast
  moreover have "distinct ?xs" using distinct_make_n_fresh by blast
  moreover have "set ?xs \<subseteq> set (?xs @ keep)" by simp
  moreover have "set f_args \<inter>\<^sub>\<emptyset> set ?xs" "set bs \<inter>\<^sub>\<emptyset> set ?xs"
    unfolding stale_registers_def using make_n_fresh_not_in_stale by fastforce+
  moreover have "\<exists>z_c s'. f_c \<turnstile> (to_imp_tc f_args crgt bs (?xs ! i) (?xs @ keep) (ts ! i), s) \<Rightarrow>\<^bsup>z_c\<^esup>  s' \<and>
       s' (?xs ! i) = (vs ! i) \<and> s' = s on set f_args \<union> set bs \<union> set (?xs @ keep) - {?xs ! i}"
    if "i < length ts" "relate_exec_state f_args bs vs_arg vs_b s" for i s
  proof (rule hCall.IH)
    from that show "ts ! i \<in> set ts" by simp
  next
    from that hCall.prems(1) show "\<not> HOL_TCN_Timing.tails (ts ! i)" by simp
  next
    from that args_bigstep show "(f, frgt) \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>zs ! i\<^esup>  vs ! i" by simp
  next
    have "set (call_registers crgt (ts ! i)) \<subseteq> set (call_registers crgt (hCall gr ts))"
      using call_registers_set that by fastforce
    then have "set ?xs \<inter>\<^sub>\<emptyset> set (call_registers crgt (ts ! i))"
      unfolding stale_registers_def using lengths make_n_fresh_not_in_stale by fastforce
    moreover have "set ?xs \<inter>\<^sub>\<emptyset> set f_args"
      unfolding stale_registers_def using make_n_fresh_not_in_stale by fastforce
    moreover from that have "compiler_args_invar crgt f_args bs keep (ts ! i)"
      using hCall.prems(1,3) compiler_args_invar_subset[where t = "ts ! i" and t' = "hCall gr ts"] by fastforce
    ultimately show "compiler_args_invar crgt f_args bs (?xs @ keep) (ts ! i)"
      unfolding compiler_args_invar_def by auto
  next
    from that show "relate_rgt_correctness frgt crgt (calls_r (ts ! i))"
      using hCall.prems(4) unfolding relate_rgt_correctness_def by fastforce
  next
    from that show "relate_exec_state f_args bs vs_arg vs_b s" by blast
  qed

  ultimately obtain z1 s2 where exec_c1: "f_c \<turnstile> (?c1, s) \<Rightarrow>\<^bsup>z1\<^esup>  s2"
      "lookups ?xs s2 = vs" "s2 = s on set f_args \<union> set bs \<union> set (?xs @ keep) - set ?xs"
    using compiled_list_bigstep' by blast


  (* part 2: copying from temporaries to argument registers *)

  let ?c2 = "t_seqs' (generate (\<lambda>i. (args_from_crgt crgt gr ! i) ::= A (V (?xs ! i))) (length ts))"
  let ?z2 = "Suc (2 * length ts)"

  have "set (args_from_crgt crgt gr) \<subseteq> set (stale_registers f_args crgt bs keep (hCall gr ts))"
    unfolding stale_registers_def call_registers_def by fastforce
  then have dj: "set ?xs \<inter> set (args_from_crgt crgt gr) = {}"
    using make_n_fresh_not_in_stale by blast
  moreover have "distinct (args_from_crgt crgt gr)"
    using hCall.prems unfolding compiler_args_invar_def by simp
  moreover have "length ?xs = length ts"
    unfolding make_n_fresh_def generate_def by simp
  moreover have "length (args_from_crgt crgt gr) = length ts"
    using hCall.prems unfolding compiler_args_invar_def by simp

  ultimately obtain s3 where exec_c2: "f_c \<turnstile> (?c2, s2) \<Rightarrow>\<^bsup>?z2\<^esup> s3"
       "lookup_args crgt gr s3 = lookups ?xs s2" "s3 = s2 on - set (args_from_crgt crgt gr)"
    using copy_list_bigstep' by blast
                       

  (* part 3: calling g *)
  
  let ?gcom = "com_from_crgt crgt gr" and ?gret = "ret_from_crgt crgt gr" and ?gv = "f_from_frgt frgt gr (lookup_args crgt gr s3)"
  let ?c3 = "CALL ?gcom RETURN ?gret :: tcom"
  let ?s4 = "s3(?gret := ?gv)"

  have "terminates_with_res_IMP ?gcom s3 ?gret ?gv" using hCall.prems unfolding relate_rgt_correctness_def by simp
  then obtain z3 s4' where "(?gcom, s3) \<Rightarrow>\<^bsup>z3\<^esup> s4'" "s4' ?gret = ?gv"
    unfolding terminates_with_res_IMP_def terminates_with_res_pred_time_IMP_def terminates_with_pred_time_IMP_def by blast
  then have exec_c3: "f_c \<turnstile> (?c3, s3) \<Rightarrow>\<^bsup>z3\<^esup> ?s4" using tbig_step_t.tCall by metis

  have "f_from_frgt frgt gr = ?g" using split_from_frgt by simp
  then have vfrom: "?gv = v" using exec_c1(2) exec_c2(2) gvs by simp


  (* part 4: copying to r *)

  let ?c4 = "r ::= A (V (ret_from_crgt crgt gr)) :: tcom"

  let ?s5 = "?s4(r := aval (A (V ?gret)) ?s4)"
  obtain z4 where exec_c4: "f_c \<turnstile> (?c4, ?s4) \<Rightarrow>\<^bsup>z4\<^esup> ?s5" by blast
  then have s5: "?s5 = ?s4(r := v)" using vfrom exec_c3 by simp


  (* putting it together *)

  show ?case unfolding to_imp_tc.simps Let_def split_beta
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    show "f_c \<turnstile> (?c1;; ?c2;; ?c3;; ?c4, s) \<Rightarrow>\<^bsup>z1 + ?z2 + z3 + z4\<^esup> ?s5"
    apply (repeat \<open>rule tbig_step_t.tSeq\<close>)
      using exec_c1 exec_c2 exec_c3 exec_c4 using tbig_step_t.tSeq by auto
  next
    show "?s5 r = v" using s5 by simp
  next
    have "set f_args \<union> set bs \<union> set (?xs @ keep) - set ?xs = set f_args \<union> set bs \<union> set keep"
      using make_n_fresh_not_in_stale unfolding stale_registers_def by fastforce
    then have *: "s2 = s on set f_args \<union> set bs \<union> set keep - {r}"
      using exec_c1 by blast

    have "set f_args \<union> set bs \<union> set keep \<inter>\<^sub>\<emptyset> set (args_from_crgt crgt gr)"
      using hCall.prems(3) unfolding compiler_args_invar_def call_registers_def by auto
    then have **: "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
      using hCall.prems(3) exec_c2 unfolding compiler_args_invar_def by auto

    have "ret_from_crgt crgt gr \<notin> set f_args \<union> set bs \<union> set keep"
      using hCall.prems(3) unfolding compiler_args_invar_def call_registers_def by auto
    then have ***: "?s5 = s3 on set f_args \<union> set bs \<union> set keep - {r}" by auto

    show "?s5 = s on set f_args \<union> set bs \<union> set keep - {r}"
      using * ** *** by fastforce
  qed

next
  case (hTAIL x)
  then show ?case by simp
qed



definition rel_trace_call :: "com_registry \<Rightarrow> fun_ref \<Rightarrow> nat list \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "rel_trace_call crgt gr gargs gcom gs \<longleftrightarrow> com_from_crgt crgt gr = gcom \<and> lookup_args crgt gr gs = gargs"
definition rel_trace_calls :: "com_registry \<Rightarrow> HOL_TCN_Timing.trace \<Rightarrow> IMP_Tailcall_Traces.call_trace \<Rightarrow> bool" where
  "rel_trace_calls crgt hT cT \<longleftrightarrow>
    length hT = length cT \<and>
    list_all (\<lambda>((gr,gargs),(gcom,gs)). rel_trace_call crgt gr gargs gcom gs) (zip hT cT)"
(* "rel_trace_calls crgt hT cT \<longleftrightarrow>
    length hT = length cT \<and>
    (\<forall>i < length hT. let (gr, gargs) = hT ! i; (gcom, gs) = cT ! i in
                     rel_trace_call crgt gr gargs gcom gs)" *)
fun rel_leaf_state :: "com_registry \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow> leaf_state \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool" where
  "rel_leaf_state crgt _      r (Value v) s l \<longleftrightarrow> \<not> l \<and> s       r        = v " |
  "rel_leaf_state crgt f_args _ (Tail vs) s l \<longleftrightarrow>   l \<and> lookups f_args s = vs"

definition rel_trace_to_leaf ::
    "com_registry \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow>
      HOL_TCN_Timing.trace \<Rightarrow> leaf_state \<Rightarrow>
        IMP_Tailcall_Traces.call_trace \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool" where
  "rel_trace_to_leaf crgt f_args r hT hl cT s cl \<longleftrightarrow>
    rel_trace_calls crgt hT cT \<and> rel_leaf_state crgt f_args r hl s cl"

(* lemma
  assumes "length xs = length ys"
  shows "(\<forall>i<length xs. P (xs ! i) (ys ! i)) = list_all (\<lambda>(x, y). P x y) (zip xs ys)"
   apply (induction rule: snoc_list_induct2[OF assms])  *)

lemma rel_trace_append:
  assumes "rel_trace_calls crgt hT1 cT1"
  assumes "rel_trace_to_leaf crgt f_args r hT2 hl cT2 s cl"
  shows "rel_trace_to_leaf crgt f_args r (hT1 @ hT2) hl (cT1 @ cT2) s cl"
  using assms unfolding rel_trace_to_leaf_def rel_trace_calls_def by auto


term "undefined :: HOL_TCN_Timing.trace"
term "undefined :: IMP_Tailcall_Traces.trace"
term htrace_to_leaf
term ttrace_to_leaf


thm compiler_correct_no_tails
thm trace_val_to_semantics

theorem compiler_rel_trace:
  fixes hT :: HOL_TCN_Timing.trace
  assumes "invar t"
  assumes "frgt \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup>hT \<^esup> hl"
  assumes "compiler_args_invar crgt f_args bs keep t"
  assumes "relate_rgt_correctness frgt crgt (calls_r t)"
  assumes "relate_exec_state f_args bs vs_arg vs_b s"
  shows "\<exists>k cT cl s'.
    (to_imp_tc f_args crgt bs r keep t,s)\<Rightarrow>\<^bsup>(k, cT)\<^esup> (s',cl)
    \<and> rel_trace_to_leaf crgt f_args r hT hl cT s' cl"
using assms(2) assms(1,3-) proof (induction arbitrary: bs keep s r crgt rule: htrace_to_leaf_induct)
  case (hLet frgt t1 vs_b vs_arg T1 v1 t2 T2 l2 T)

  let ?r1 = "fresh' (stale_registers f_args crgt bs keep LET t1 IN t2) ''Let.x''"
  let ?c1 = "to_imp_tc f_args crgt bs ?r1 keep t1"
  let ?c2 = "to_imp_tc f_args crgt (?r1 # bs) r (?r1 # keep) t2"

  (* assumptions and IH for t1 (and some stuff for t2) *)

  have no_tails1: "\<not> HOL_TCN_Timing.tails t1" using hLet by simp
  have invar: "HOL_TCN_Timing.invar t1" "HOL_TCN_Timing.invar t2" using hLet by simp_all

  have args_invar1: "compiler_args_invar crgt f_args bs keep t1"
    using hLet.prems compiler_args_invar_subset[where t' = "LET t1 IN t2"] by simp

  have rel_rgt: "relate_rgt_correctness frgt crgt (calls_r t1)" "relate_rgt_correctness frgt crgt (calls_r t2)"
    using hLet unfolding relate_rgt_correctness_def by simp_all

  have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" using hLet by blast

  from hLet.hyps obtain f z1 where "(f,frgt) \<turnstile> (t1,vs_b,vs_arg) \<Rightarrow>\<^bsup>z1\<^esup> v1"
    using trace_val_to_semantics by blast
  then obtain f_c z1_c s2 where corr1:
      "f_c \<turnstile> (?c1,s) \<Rightarrow>\<^bsup>z1_c\<^esup> s2" "s2 ?r1 = v1"
      "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
    using compiler_correct_no_tails[where t = t1] no_tails1 args_invar1 rel_rgt(1) rel_state1 by blast

  obtain k1 cT1 s2' cl1 where ih1:
      "(?c1,s)\<Rightarrow>\<^bsup>(k1,cT1)\<^esup> (s2',cl1)" "rel_trace_to_leaf crgt f_args ?r1 T1 (Value v1) cT1 s2' cl1"
    using hLet.IH(1) invar(1) args_invar1 rel_rgt(1) rel_state1 by blast
  then have [simp]: "\<not> cl1" unfolding rel_trace_to_leaf_def by simp

  have [simp]: "s2' = s2"
    using corr1(1) trace_nontail_has_bigstep[OF ih1(1) \<open>\<not> cl1\<close>] determ(2) by blast

  (* assumptions and IH for t2 *)

  have "?r1 \<notin> set f_args"
    apply (rule contra_subsetD[OF _ fresh_not_in_stale])
    unfolding stale_registers_def by simp
  moreover have "?r1 \<notin> set (call_registers crgt t2)"
    apply (rule contra_subsetD[OF _ fresh_not_in_stale])
    using call_registers_set unfolding stale_registers_def by auto
  moreover have "compiler_args_invar crgt f_args bs keep t2"
    using hLet.prems compiler_args_invar_subset[where t' = "LET t1 IN t2"] by simp
  ultimately have args_invar2: "compiler_args_invar crgt f_args (?r1 # bs) (?r1 # keep) t2"
    using hLet.prems(3) unfolding compiler_args_invar_def by auto

  have s_like_s2: "s2 = s on set f_args \<union> set bs \<union> set keep" (* TODO *)
    by (smt (verit) DiffI Un_iff eq_on_def fresh_not_in_stale corr1(3) set_append singletonD stale_registers_def)
  then have rel_state2: "relate_exec_state f_args (?r1 # bs) vs_arg (v1 # vs_b) s2"
    using hLet.prems(4) unfolding relate_exec_state_def using corr1 by fastforce

  obtain k2 cT2 s3' cl2 where ih2:
      "(?c2,s2)\<Rightarrow>\<^bsup>(k2,cT2)\<^esup> (s3',cl2)" "rel_trace_to_leaf crgt f_args r T2 l2 cT2 s3' cl2"
    using hLet.IH(2) invar(2) args_invar2 rel_rgt(2) rel_state2 by blast

  (* putting it together *)

  show ?case unfolding to_imp_tc.simps Let_def
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    show "(?c1;; ?c2,s) \<Rightarrow>\<^bsup>(k1 + k2, cT1 @ cT2)\<^esup> (s3', cl2)"
      using ttrace_to_leaf.tSeq ih1(1)[simplified \<open>\<not> cl1\<close> \<open>s2' = s2\<close>] ih2(1) by blast
  next
    show "rel_trace_to_leaf crgt f_args r T l2 (cT1 @ cT2) s3' cl2"
      using hLet.hyps(3) rel_trace_append ih1(2) ih2(2)
      unfolding rel_trace_to_leaf_def by blast
  qed
next
  case (hLetBound n vs_b _ _)
  show ?case
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    have "aval (A (V (bs ! n))) s = vs_b ! n" using hLetBound unfolding relate_exec_state_def by auto
    then show "(to_imp_tc f_args crgt bs r keep (hLetBound n), s) \<Rightarrow>\<^bsup>(Suc (Suc 0), [])\<^esup> (s(r := vs_b ! n), False)"
      unfolding to_imp_tc.simps using ttrace_to_leaf.tAssign by metis
  next
    show "rel_trace_to_leaf crgt f_args r [] (Value (vs_b ! n)) [] (s(r := vs_b ! n)) False"
      unfolding rel_trace_to_leaf_def rel_trace_calls_def rel_trace_call_def by simp
  qed
next
  case (hArg n vs_arg _ _)
  show ?case
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    have "aval (A (V (f_args ! n))) s = vs_arg ! n" using hArg unfolding relate_exec_state_def by auto
    then show "(to_imp_tc f_args crgt bs r keep (hArg n), s) \<Rightarrow>\<^bsup>(Suc (Suc 0), [])\<^esup> (s(r := vs_arg ! n), False)"
      unfolding to_imp_tc.simps using ttrace_to_leaf.tAssign by metis
  next
    show "rel_trace_to_leaf crgt f_args r [] (Value (vs_arg ! n)) [] (s(r := vs_arg ! n)) False"
      unfolding rel_trace_to_leaf_def rel_trace_calls_def rel_trace_call_def by simp
  qed
next
  case (hNumber frgt n _ _)
  show ?case
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    have "aval (A (N n)) s = n" by auto
    then show "(to_imp_tc f_args crgt bs r keep (hNumber n), s) \<Rightarrow>\<^bsup>(Suc (Suc 0), [])\<^esup> (s(r := n), False)"
      unfolding to_imp_tc.simps using ttrace_to_leaf.tAssign by metis
  next
    show "rel_trace_to_leaf crgt f_args r [] (Value n) [] (s(r := n)) False"
      unfolding rel_trace_to_leaf_def rel_trace_calls_def rel_trace_call_def by simp
  qed
next
  case (hIfTrue frgt t1 bs xs T1 v1 t2 T2 l2 T t3)
  then show ?case sorry
next
  case (hIfFalse frgt t1 bs xs T1 v1 t3 T3 l3 T t2)
  then show ?case sorry
next
  case (hCall g T_g frgt gr vs ts Ts bs xs T v)
  then show ?case sorry
next
  case (hTail vs ts Ts frgt bs xs T)
  then show ?case sorry
qed

(* lemma "\<exists>c. \<forall>s. tstruct_k t_imp + something \<le> c * interp_time frgt (time_to_tail frgt vs_b vs_arg t)" oops *)
(* in fact, we can calculate c as the max of the structural-constant-factor and all T_f_const-ants or so *)

end
