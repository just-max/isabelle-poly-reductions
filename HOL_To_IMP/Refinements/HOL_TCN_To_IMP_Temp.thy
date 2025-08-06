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

theorem compiler_correct_nt:
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

  have no_tails: "\<not> HOL_TCN_Timing.tails t1" "\<not> HOL_TCN_Timing.tails t2" using hLet by simp_all

  obtain z1 v1 z2 where
      "z = z1 + z2" and inv: "(f, frgt) \<turnstile> (t1, vs_b, vs_arg) \<Rightarrow>\<^bsup>z1\<^esup> v1" "(f, frgt) \<turnstile> (t2, v1 # vs_b, vs_arg) \<Rightarrow>\<^bsup>z2\<^esup> v"
    using hLet_case hLet.prems by blast

  have args_invar1: "compiler_args_invar crgt f_args bs keep t1"
    using hLet.prems compiler_args_invar_subset[where t' = "LET t1 IN t2"] by simp

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

  have rel_rgt: "relate_rgt_correctness frgt crgt (calls_r t1)" "relate_rgt_correctness frgt crgt (calls_r t2)"
    using hLet unfolding relate_rgt_correctness_def by simp_all

  have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" using hLet by blast

  obtain z1_c s2 where ih1:
      "f_c \<turnstile> (?t1_c, s) \<Rightarrow>\<^bsup>z1_c\<^esup> s2" "s2 ?r1 = v1" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
    using hLet.IH(1) no_tails(1) inv(1) args_invar1 rel_rgt(1) rel_state1 by blast

  have s_like_s2: "s2 = s on set f_args \<union> set bs \<union> set keep" (* TODO *)
    by (smt (verit) DiffI Un_iff eq_on_def fresh_not_in_stale ih1(3) set_append singletonD stale_registers_def)
  then have rel_state2: "relate_exec_state f_args (?r1 # bs) vs_arg (v1 # vs_b) s2"
    using hLet.prems(5) unfolding relate_exec_state_def using ih1 by fastforce

  obtain z2_c s3 where ih2:
      "f_c \<turnstile> (?t2_c, s2) \<Rightarrow>\<^bsup>z2_c\<^esup>  s3" "s3 r = v"
      "s3 = s2 on set f_args \<union> set (?r1 # bs) \<union> set (?r1 # keep) - {r}"
    using hLet.IH(2) no_tails(2) inv(2) args_invar2 rel_rgt(2) rel_state2 by blast

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


  have 1: "length vs = length ts" "length ?xs = length ts"
    using lengths unfolding make_n_fresh_def generate_def by simp_all
  moreover have 2: "relate_exec_state f_args bs vs_arg vs_b s" using hCall by blast
  moreover have 3: "distinct ?xs" using distinct_make_n_fresh by blast
  moreover have 4: "set ?xs \<subseteq> set (?xs @ keep)" by simp
  moreover have 5: "set f_args \<inter>\<^sub>\<emptyset> set ?xs" "set bs \<inter>\<^sub>\<emptyset> set ?xs"
    unfolding stale_registers_def using make_n_fresh_not_in_stale by fastforce+
  moreover have 6: "\<exists>z_c s'. f_c \<turnstile> (to_imp_tc f_args crgt bs (?xs ! i) (?xs @ keep) (ts ! i), s) \<Rightarrow>\<^bsup>z_c\<^esup>  s' \<and>
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
      unfolding stale_registers_def using 1 make_n_fresh_not_in_stale by fastforce
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
  thm compiled_list_bigstep

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












(*

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

*)


(*
lemma tto_end_tseqs:
  assumes "\<forall>i \<le> length cs. tto_end s (cs ! i) (ks ! i) (gss ! i)"
  shows True *)

fun tcalls where
  "tcalls (tSeq c1 c2) = tcalls c1 @ tcalls c2" |
  "tcalls (tIf x c1 c2) = tcalls c1 @ tcalls c2" |
  "tcalls (tCall C r) = [C]" |
  "tcalls _ = []"

(*
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

thm tto_end_non_tail tto_end_tail *)

find_theorems "map fst"
lemma
  assumes compiler_correct_nt_: True
  fixes t_imp f_args crgt frgt bs r keep t vs_b vs_arg
  defines "t_imp \<equiv> to_imp_tc f_args crgt bs r keep t"
  assumes "t_time \<equiv> time_to_tail frgt vs_b vs_arg t"
  assumes "well_formed_comp f_args crgt bs keep t"
  assumes "well_encoded_comp f_args bs vs_arg vs_b s"
  (* assumes "called_correctness crgt frgt t" *)
  shows "\<exists>k Cs.
    (\<exists>t l. tto_end s t_imp k Cs t l)
    \<and> length Cs = length t_time
    \<and> (\<forall>((C,s), (g,vs_arg_g)) \<in> set (zip Cs t_time).
          C = com_from_crgt crgt g \<and> vs_arg_g = lookup_args crgt g s)"
using assms(2-4) proof (induction t arbitrary: t_imp t_time bs r keep vs_b s)
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
  let ?xs = "make_n_fresh (length ts) keep ''Call.x.''"
  let ?cs1 = "mapi (\<lambda>i t. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ keep) t) ts"
  let ?cs2 = "mapi (\<lambda>i t. tAssign (args_from_crgt crgt g ! i) (A (V (?xs ! i)))) ts"
  let ?call = "tSeq (tCall (com_from_crgt crgt g) (ret_from_crgt crgt g)) (tAssign r (A (V (ret_from_crgt crgt g))))"

  have "t_imp = t_seqs (?cs1 @ ?cs2) ?call" using hCall by (simp add: Let_def split_beta)

  let ?x = "\<lambda>s. f_from_reg frgt g (lookup_args crgt g s)"
  have "tto_end s ?call 2 [(com_from_crgt crgt g,s)] (s(ret_from_crgt crgt g := ?x s, r := ?x s)) False" for s
    sorry

  then show ?case sorry
next
  case (hTAIL x)
  then show ?case sorry
qed




    (* \<and> (\<forall>((C,s), (g,vs_arg_g)) \<in> set (zip gs (time_to_tail frgt vs_b vs_arg t)). *)
          (* C = com_from_crgt crgt g \<and> vs_arg_g = lookup_args crgt g s)" *)

*)

lemma
  assumes "t_imp = to_imp_tc f_args crgt bs r keep t"
  assumes "well_formed_comp f_args crgt bs keep t"
  assumes "well_encoded_comp f_args bs vs_arg vs_b s"
  assumes "called_correctness crgt frgt t"
  shows "\<exists>k z.
    ttime_to_tail s t_imp (k + z)
    \<and> k \<le> tstruct_k t_imp
    \<and> z \<le> tinterp_time frgt crgt (time_to_tail frgt vs_b vs_arg t)"
using assms(2-5) proof (induction t arbitrary: t_imp bs r keep vs_b s)
  case (hLet t1 t2)
  thm hLet.prems(1)[simplified]
  thm hLet.IH(1) hLet.IH(2)

  thm hLet.prems

  let ?x_var = "fresh' keep ''Let.x''"
  let ?t_imp1 = "to_imp_tc f_args crgt bs ?x_var keep t1"

  have wf1: "well_formed_comp f_args crgt bs keep t1" using hLet.prems(2)
    unfolding well_formed_comp_def using non_tail_tailrec apply auto apply (simp only: reserved_regs_def h_calls.simps map_append)
    by auto
  then obtain k1 z1 where k1z1:
      "ttime_to_tail s ?t_imp1 (k1 + z1)"
      "k1 \<le> tstruct_k ?t_imp1"
      "z1 \<le> tinterp_time frgt crgt (time_to_tail frgt vs_b vs_arg t1)"
    using hLet.IH(1)[where t_imp = ?t_imp1 and s = s and bs = bs and vs_b = vs_b and r = ?x_var and keep = keep] hLet.prems
    unfolding called_correctness_def by auto

  have ob1: "non_tail t1" using hLet unfolding well_formed_comp_def by simp
  have ob2: "well_encoded_comp f_args bs vs_arg vs_b s" using hLet by simp
  obtain f y1 s1
      where t1s1: "f \<turnstile> (?t_imp1,s) \<Rightarrow>\<^bsup>y1\<^esup> s1"
      and s1_xvar: "s1 ?x_var = eval_non_tail frgt vs_b vs_arg t1"
      and s1: "s = s1 on (Set.remove ?x_var (set keep))"
    using compiler_correct_nt[OF ob1 wf1 ob2, simplified] by blast

  have "tailrec t1" using well_formed_comp_def wf1 by blast
  then have inv: "invar ?t_imp1" using to_imp_invar by blast
  have y1: "y1 = k1 + z1" using ttime_non_tail[OF inv t1s1] sorry (* ttime_to_tail for non-tail MUST INVESTIGATE AND WRITE LEMMA *)

  let ?t_imp2 = "to_imp_tc f_args crgt (?x_var # bs) r (?x_var # keep) t2"
  have "tailrec t2" using hLet unfolding well_formed_comp_def by simp

  have t2_1: "well_formed_comp f_args crgt (?x_var # bs) (?x_var # keep) t2"
    using hLet.prems(2) unfolding well_formed_comp_def apply auto sorry (* almost sub-term *)
  have "set f_args \<subseteq> Set.remove ?x_var (set keep)" using fresh_not_in_keep
    unfolding remove_def apply simp using hLet.prems(2) unfolding well_formed_comp_def reserved_regs_def by simp
  then have t2_2_1: "lookups f_args s1 = vs_arg"
    apply (subst lookups_eq_on[where s = s, symmetric])
    using s1 apply blast using hLet.prems(3) unfolding well_encoded_comp_def by blast
  have "set bs \<subseteq> Set.remove ?x_var (set keep)" using fresh_not_in_keep
    unfolding remove_def apply simp using hLet.prems(2) unfolding well_formed_comp_def reserved_regs_def by simp
  then have t2_2_2: "lookups (?x_var # bs) s1 = eval_non_tail frgt vs_b vs_arg t1 # vs_b" apply auto
    using s1_xvar apply blast
    apply (subst lookups_eq_on[where s = s, symmetric])
    using s1 apply blast using hLet.prems(3) unfolding well_encoded_comp_def by blast
  from t2_2_1 t2_2_2 have t2_2: "well_encoded_comp f_args (?x_var # bs) vs_arg (eval_non_tail frgt vs_b vs_arg t1 # vs_b) s1"
    unfolding well_encoded_comp_def by simp
  have t2_3: "called_correctness crgt frgt t2" using hLet.prems(4) unfolding called_correctness_def by auto
  obtain k2 z2 where k2z2:
      "ttime_to_tail s1 ?t_imp2 (k2 + z2)"
      "k2 \<le> tstruct_k ?t_imp2"
      "z2 \<le> tinterp_time frgt crgt (time_to_tail frgt (eval_non_tail frgt vs_b vs_arg t1 # vs_b) vs_arg t2)"
    using hLet.IH(2)[where t_imp = ?t_imp2 and r = r and s = s1 and bs = "?x_var # bs"
      and vs_b = "eval_non_tail frgt vs_b vs_arg t1 # vs_b" and keep = "?x_var # keep", OF _ t2_1 t2_2 t2_3, simplified]
    by blast

  from t1s1 k2z2
  have "ttime_to_tail s t_imp (y1 + (k2 + z2))" using hLet.prems(1) apply simp unfolding Let_def apply (rule ttime_to_tail.intros(3)) by auto
  moreover have "y1 + (k2 + z2) = (k1 + k2) + (z1 + z2)" using y1 by linarith
  moreover have "k1 + k2 \<le> tstruct_k t_imp" using hLet.prems(1) apply simp unfolding Let_def using k1z1 k2z2 by simp
  moreover have "z1 + z2 \<le> tinterp_time frgt crgt (time_to_tail frgt vs_b vs_arg (hLet t1 t2))"
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

lemma "\<exists>c. \<forall>s. tstruct_k t_imp + something \<le> c * interp_time frgt (time_to_tail frgt vs_b vs_arg t)" oops
(* in fact, we can calculate c as the max of the structural-constant-factor and all T_f_const-ants or so *)

end
