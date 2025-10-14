theory HOL_TCN_To_IMP_Temp
  imports HOL_Nat_To_IMP.IMP_Terminates_With "IMP.HOL_TCN_To_IMP" (* HOL_Nat_To_IMP.Compile_HOL_Nat_To_IMP *)
(* TODO: rearrange import of stuff from Compile *)

  HOL_To_IMP_Primitives (* only for stuff that should be in IMP_Terminates_With, TODO: fix here once that's done *)
begin

method repeat methods m = (m; repeat \<open>m\<close>)?

type_synonym state = IMP_Base.state (* TODO *)

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

lemma fresh_not_in_stale_subset: assumes "set stale' \<subseteq> set stale" shows "fresh stale name \<notin> set stale'"
  using fresh_not_in_stale assms by blast


definition "compiler_invar crgt f_args bs keep t \<longleftrightarrow>
  HOL_TCN_Timing.invar t
  \<and> distinct f_args
  \<and> set f_args \<inter>\<^sub>\<emptyset> set (call_registers crgt t)
  \<and> set bs \<inter>\<^sub>\<emptyset> set (call_registers crgt t)
  \<and> set bs \<inter>\<^sub>\<emptyset> set f_args
  \<and> set keep \<inter>\<^sub>\<emptyset> set f_args
  \<and> set keep \<inter>\<^sub>\<emptyset> set (call_registers crgt t)
  \<and> (\<forall>g\<in>set (calls' t). distinct (args_from_crgt crgt g))
  \<and> (\<forall>(g,n)\<in>set (calls_n t). n = length (args_from_crgt crgt g))"
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

- At each (TODO: tail: len ... = len f_args, needs new function to collect tail calls) call site, the correct number of arguments must be provided to the called function.

Note that this is not the *weakest* possible invariant, but that would
significantly complicate the invariant with no obvious benefit.
*)

lemma compiler_invarE[elim]:
  assumes "compiler_invar crgt f_args bs keep t"
  shows
    "HOL_TCN_Timing.invar t"
    "distinct f_args"
    "set f_args \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
    "set bs \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
    "set bs \<inter>\<^sub>\<emptyset> set f_args"
    "set keep \<inter>\<^sub>\<emptyset> set f_args"
    "set keep \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
    "\<And>g. g \<in> set (calls' t) \<Longrightarrow> distinct (args_from_crgt crgt g)" (* what's the canonical way to write this? *)
    "\<And>g n. (g,n)\<in>set (calls_n t) \<Longrightarrow> n = length (args_from_crgt crgt g)"
  using assms unfolding compiler_invar_def by auto

lemma compiler_invarI[intro]:
  assumes
    "HOL_TCN_Timing.invar t"
    "distinct f_args"
    "set f_args \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
    "set bs \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
    "set bs \<inter>\<^sub>\<emptyset> set f_args"
    "set keep \<inter>\<^sub>\<emptyset> set f_args"
    "set keep \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
    "\<And>g. g \<in> set (calls' t) \<Longrightarrow> distinct (args_from_crgt crgt g)"
    "\<And>g n. (g,n)\<in>set (calls_n t) \<Longrightarrow> n = length (args_from_crgt crgt g)"
  shows "compiler_invar crgt f_args bs keep t"
  using assms unfolding compiler_invar_def by blast

lemma compiler_invar_subset:
  assumes invar: "invar t"
  assumes calls: "set (calls t) \<subseteq> set (calls t')" (* subset on calls_n would be enough... *)
  assumes comp_invar: "compiler_invar crgt f_args bs keep t'"
  shows "compiler_invar crgt f_args bs keep t"
proof
  have "set (call_registers crgt t) \<subseteq> set (call_registers crgt t')"
    using calls calls'_set unfolding call_registers_def by auto
  then show
      "set f_args \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
      "set bs \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
      "set keep \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
    using compiler_invarE[OF comp_invar] by blast+
next
  fix g assume "g \<in> set (calls' t)"
  then have "g \<in> set (calls' t')" using calls calls'_set by auto
  then show "distinct (args_from_crgt crgt g)" using comp_invar by auto
next
  fix g n assume "(g,n) \<in> set (calls_n t)"
  then have "(g,n) \<in> set (calls_n t')" using calls calls_n_set by auto
  then show "n = length (args_from_crgt crgt g)" using comp_invar by auto
qed (auto simp add: invar compiler_invarE[OF comp_invar])

lemma compiler_invar_let:
  fixes crgt f_args bs keep t1 t2
  assumes comp_invar: "compiler_invar crgt f_args bs keep (LET t1 IN t2)"
  defines "r \<equiv> fresh' (stale_registers f_args crgt bs keep LET t1 IN t2) ''Let.x''"
  shows
    "compiler_invar crgt f_args bs keep t1"
    "compiler_invar crgt f_args (r # bs) (r # keep) t2"
proof -
  have "invar t1" using comp_invar unfolding compiler_invar_def by simp
  then show "compiler_invar crgt f_args bs keep t1"
    using comp_invar compiler_invar_subset[where t' = "LET t1 IN t2"] by simp
next
  have "invar t2" using comp_invar unfolding compiler_invar_def by simp
  then have "compiler_invar crgt f_args bs keep t2"
    using comp_invar compiler_invar_subset[where t' = "LET t1 IN t2"] by simp

  moreover have "r \<notin> set f_args"
    unfolding r_def stale_registers_def
    using fresh_not_in_stale set_append by fastforce
  moreover have "r \<notin> set (call_registers crgt t2)"
  unfolding r_def proof (rule fresh_not_in_stale_subset)
    show "set (call_registers crgt t2) \<subseteq> set (stale_registers f_args crgt bs keep LET t1 IN t2)"
      unfolding stale_registers_def call_registers_def using calls'_set by auto
  qed

  ultimately show "compiler_invar crgt f_args (r # bs) (r # keep) t2"
    unfolding compiler_invar_def by auto
qed

lemma compiler_invar_if:
  assumes "compiler_invar crgt f_args bs keep (IF t1\<noteq>0 THEN t2 ELSE t3)"
  shows
    "compiler_invar crgt f_args bs keep t1"
    "compiler_invar crgt f_args bs keep t2"
    "compiler_invar crgt f_args bs keep t3"
proof -
  have "HOL_TCN_Timing.invar t1" using assms unfolding compiler_invar_def by simp
  moreover have "set (calls t1) \<subseteq> set (calls (IF t1\<noteq>0 THEN t2 ELSE t3))" by fastforce
  ultimately show "compiler_invar crgt f_args bs keep t1"
    using assms compiler_invar_subset by metis
next
  have "HOL_TCN_Timing.invar t2" using assms unfolding compiler_invar_def by simp
  moreover have "set (calls t2) \<subseteq> set (calls (IF t1\<noteq>0 THEN t2 ELSE t3))" by fastforce
  ultimately show "compiler_invar crgt f_args bs keep t2"
    using assms compiler_invar_subset by metis
next
  have "HOL_TCN_Timing.invar t3" using assms unfolding compiler_invar_def by simp
  moreover have "set (calls t3) \<subseteq> set (calls (IF t1\<noteq>0 THEN t2 ELSE t3))" by fastforce
  ultimately show "compiler_invar crgt f_args bs keep t3"
    using assms compiler_invar_subset by metis
qed

lemma compiler_invar_call:
  fixes f_args crgt bs keep gr ts
  assumes compiler_invar: "compiler_invar crgt f_args bs keep (hCall gr ts)"
  defines "xs \<equiv> make_n_fresh (stale_registers f_args crgt bs keep (hCall gr ts)) ''Call.x.'' (length ts)"
  assumes t: "t \<in> set ts"
  shows "compiler_invar crgt f_args bs (xs @ keep) t"
proof -
  have "HOL_TCN_Timing.invar t" using compiler_invar t unfolding compiler_invar_def by simp
  with t compiler_invar compiler_invar_subset[where t = t and t' = "hCall gr ts"]
  have inv: "compiler_invar crgt f_args bs keep t" by fastforce

  show "compiler_invar crgt f_args bs (xs @ keep) t"
  proof
    have "set (call_registers crgt t) \<subseteq> set (call_registers crgt (hCall gr ts))"
      using t calls'_set unfolding call_registers_def by auto
    then have "set xs \<inter>\<^sub>\<emptyset> set f_args" "set xs \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
      unfolding xs_def stale_registers_def using make_n_fresh_not_in_stale by fastforce+
    then show "set (xs @ keep) \<inter>\<^sub>\<emptyset> set f_args" "set (xs @ keep) \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
      using inv unfolding compiler_invar_def by fastforce+
  qed (simp_all add: compiler_invarE[OF inv])
qed

lemma compiler_invar_tail:
  fixes f_args crgt bs keep gr ts
  assumes compiler_invar: "compiler_invar crgt f_args bs keep (hTAIL ts)"
  defines "xs \<equiv> make_n_fresh (stale_registers f_args crgt bs keep (hTAIL ts)) ''TAIL.x.'' (length ts)"
  assumes t: "t \<in> set ts"
  shows "compiler_invar crgt f_args bs (xs @ keep) t"
proof -
  have "HOL_TCN_Timing.invar t" using compiler_invar t unfolding compiler_invar_def by simp
  with t compiler_invar compiler_invar_subset[where t = t and t' = "hTAIL ts"]
  have inv: "compiler_invar crgt f_args bs keep t" by fastforce

  show "compiler_invar crgt f_args bs (xs @ keep) t"
  proof
    have "set (call_registers crgt t) \<subseteq> set (call_registers crgt (hTAIL ts))"
      using t calls'_set unfolding call_registers_def by auto
    then have "set xs \<inter>\<^sub>\<emptyset> set f_args" "set xs \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
      unfolding xs_def stale_registers_def using make_n_fresh_not_in_stale by fastforce+
    then show "set (xs @ keep) \<inter>\<^sub>\<emptyset> set f_args" "set (xs @ keep) \<inter>\<^sub>\<emptyset> set (call_registers crgt t)"
      using inv unfolding compiler_invar_def by fastforce+
  qed (simp_all add: compiler_invarE[OF inv])
qed


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


definition rel_trace_call :: "com_registry \<Rightarrow> fun_ref \<Rightarrow> nat list \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "rel_trace_call crgt gr gargs gcom gs \<longleftrightarrow> com_from_crgt crgt gr = gcom \<and> lookup_args crgt gr gs = gargs"

definition rel_trace_calls :: "com_registry \<Rightarrow> HOL_TCN_Timing.call_trace \<Rightarrow> IMP_Tailcall_Traces.call_trace \<Rightarrow> bool" where
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
      HOL_TCN_Timing.call_trace \<Rightarrow> leaf_state \<Rightarrow>
        IMP_Tailcall_Traces.call_trace \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool" where
  "rel_trace_to_leaf crgt f_args r hT hl cT s cl \<longleftrightarrow>
    rel_trace_calls crgt hT cT \<and> rel_leaf_state crgt f_args r hl s cl"

definition rel_trace_to_end where
  "rel_trace_to_end crgt r hT v cT s \<longleftrightarrow>
    rel_trace_calls crgt hT cT \<and> s r = v"

(* lemma
  assumes "length xs = length ys"
  shows "(\<forall>i<length xs. P (xs ! i) (ys ! i)) = list_all (\<lambda>(x, y). P x y) (zip xs ys)"
   apply (induction rule: snoc_list_induct2[OF assms])  *)

lemma rel_trace_to_leaf_cl:
  shows "rel_trace_to_leaf crgt f_args r hT (Value v) cT s cl \<Longrightarrow> \<not> cl"
    and "rel_trace_to_leaf crgt f_args r hT (Tail vs) cT s cl \<Longrightarrow> cl"
  unfolding rel_trace_to_leaf_def by simp_all

(* concatenating traces *)

lemma rel_trace_calls_append:
  assumes "rel_trace_calls crgt hT1 cT1"
  assumes "rel_trace_calls crgt hT2 cT2"
  shows "rel_trace_calls crgt (hT1 @ hT2) (cT1 @ cT2)" using assms unfolding rel_trace_calls_def by simp

lemma rel_trace_to_leaf_append:
  assumes "rel_trace_calls crgt hT1 cT1"
  assumes "rel_trace_to_leaf crgt f_args r hT2 hl cT2 s cl"
  shows "rel_trace_to_leaf crgt f_args r (hT1 @ hT2) hl (cT1 @ cT2) s cl"
  using assms rel_trace_calls_append unfolding rel_trace_to_leaf_def by auto

lemma rel_trace_to_end_append:
  assumes "rel_trace_calls crgt hT1 cT1"
  assumes "rel_trace_to_end crgt r hT2 v cT2 s"
  shows "rel_trace_to_end crgt r (hT1 @ hT2) v (cT1 @ cT2) s"
  using assms rel_trace_calls_append unfolding rel_trace_to_end_def by auto

(* relating partial and full traces *)

lemma rel_trace_to_leaf_value_rel_trace_to_end:
  "rel_trace_to_leaf crgt f_args r hT (Value v) cT s False \<longleftrightarrow> rel_trace_to_end crgt r hT v cT s"
  unfolding rel_trace_to_leaf_def rel_trace_to_end_def by simp



lemma snoc_obtain:
  assumes "xs \<noteq> []"
  obtains x xs' where "xs = xs' @ [x]"
  using assms by (meson rev_exhaust)

lemma snoc_list_induct2 [case_names len Nil snoc]:
  assumes len: "length xs = length ys"
  assumes nil: "P [] []"
  assumes snoc: "\<And>xs x ys y. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs @ [x]) (ys @ [y])"
  shows "P xs ys"
proof -
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
proof -
  let ?P = "\<lambda>xs ys zs. P (rev xs) (rev ys) (rev zs)"
  have "length (rev xs) = length (rev ys)" "length (rev ys) = length (rev zs)" using len by simp_all
  then have "?P (rev xs) (rev ys) (rev zs)"
  proof (induction rule: list_induct3)
  qed (simp_all add: nil snoc)
  then show "P xs ys zs" by simp
qed

lemma snoc_list_induct4 [case_names len1 len2 len3 Nil snoc]:
  assumes len: "length xs1 = length xs2" "length xs2 = length xs3" "length xs3 = length xs4"
  assumes nil: "P [] [] [] []"
  assumes snoc: "\<And>xs1 x1 xs2 x2 xs3 x3 xs4 x4.
    length xs1 = length xs2 \<Longrightarrow> length xs2 = length xs3 \<Longrightarrow> length xs3 = length xs4 \<Longrightarrow>
    P xs1 xs2 xs3 xs4 \<Longrightarrow> P (xs1 @ [x1]) (xs2 @ [x2]) (xs3 @ [x3]) (xs4 @ [x4])"
  shows "P xs1 xs2 xs3 xs4"
proof -
  let ?P = "\<lambda>xs1 xs2 xs3 xs4. P (rev xs1) (rev xs2) (rev xs3) (rev xs4)"
  have
    "length (rev xs1) = length (rev xs2)"
    "length (rev xs2) = length (rev xs3)"
    "length (rev xs3) = length (rev xs4)" using len by simp_all
  then have "?P (rev xs1) (rev xs2) (rev xs3) (rev xs4)"
  proof (induction rule: list_induct4)
  qed (simp_all add: nil snoc)
  then show "P xs1 xs2 xs3 xs4" by simp
qed


lemma nth_append_length_eq:
  assumes "length xs = n"
  shows "(xs @ y # zs) ! n = y"
  apply (subst nth_append) using assms by simp

(* executing a list of terms (as in the call and tail-call cases) *)
lemma compiled_arguments_bigstep:
  assumes lengths: "length vs = length ts" "length xs = length ts"
  assumes rel: "relate_exec_state f_args bs vs_arg vs_b s"
  assumes dist: "distinct xs"
  assumes keep_xs: "set xs \<subseteq> set keep"
  assumes disj: "set f_args \<inter>\<^sub>\<emptyset> set xs" "set bs \<inter>\<^sub>\<emptyset> set xs"
  assumes sem: "\<And>i s.
    \<lbrakk> i < length ts; relate_exec_state f_args bs vs_arg vs_b s \<rbrakk> \<Longrightarrow>
    \<exists>z s'. f \<turnstile> (to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i), s) \<Rightarrow>\<^bsup>z :: nat\<^esup> s' \<and>
           s' (xs ! i) = (vs ! i) \<and> s' = s on set f_args \<union> set bs \<union> set keep - {xs ! i}"
  shows "\<exists>z s'. f \<turnstile> (mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts)), s) \<Rightarrow>\<^bsup>z :: nat\<^esup> s' \<and>
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
      f \<turnstile> (to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i), s) \<Rightarrow>\<^bsup>z :: nat\<^esup>  s' \<and>
      s' (xs ! i) = vs ! i \<and> s' = s on set f_args \<union> set bs \<union> set keep - {xs ! i}"
    if "i < length ts" "relate_exec_state f_args bs vs_arg vs_b s" for i s
    using that nth_append_left snoc.hyps by metis

  with snoc.IH[OF * **] obtain z1 s2 where exec1:
    "f \<turnstile> (mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts)), s) \<Rightarrow>\<^bsup>z1 :: nat\<^esup> s2"
    "lookups xs s2 = vs" "s2 = s on set f_args \<union> set bs \<union> set keep - set xs"
    by blast

  (* obtain the step *)

  have *: "length ts < length (ts @ [t])" by simp

  from rel exec1(3) snoc.prems(3,4) have **: "relate_exec_state f_args bs vs_arg vs_b s2"
    unfolding relate_exec_state_def by fastforce

  from snoc.prems(5)[OF * **]
  obtain z2 s3 where exec2:
      "f \<turnstile> (to_imp_tc f_args crgt bs ((xs @ [x]) ! length ts) keep ((ts @ [t]) ! length ts), s2) \<Rightarrow>\<^bsup>z2 :: nat\<^esup> s3"
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

  have "f \<turnstile> (mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts));;
              to_imp_tc f_args crgt bs ((xs @ [x]) ! length ts) keep ((ts @ [t]) ! length ts), s) \<Rightarrow>\<^bsup>z1 + z2\<^esup> s3"
    using exec1 exec2 by blast
  then have *: "f \<turnstile> (mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs ((xs @ [x]) ! i) keep ((ts @ [t]) ! i)) (length (ts @ [t]))), s) \<Rightarrow>\<^bsup>z1 + z2\<^esup> s3"
    apply (subst append_cs ) using mk_seqs_append_bigstep sorry (* need case distinction on xs! *)

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
  assumes "set xs \<inter>\<^sub>\<emptyset> set ys"
  obtains s' where
    "f \<turnstile> (mk_seqs (generate (\<lambda>i. (ys ! i) ::= A (V (xs ! i))) (length xs)),s) \<Rightarrow>\<^bsup>Suc (2 * length xs)\<^esup> s'"
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
      "f \<turnstile> (mk_seqs ?cs1, s) \<Rightarrow>\<^bsup>Suc (2 * length xs)\<^esup> s2"
      "lookups ys s2 = lookups xs s" "s2 = s on (- set ys)"
    by auto
  moreover obtain s3 where step:
      "f \<turnstile> (?c2, s2) \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> s3"
      "s3 y = s2 x" "s3 = s2 on (- {y})"
    by fastforce
  ultimately have "f \<turnstile> (mk_seqs ?cs1;; ?c2, s) \<Rightarrow>\<^bsup>Suc (2 * length (xs @ [x]))\<^esup> s3" by auto
  then have "f \<turnstile> (mk_seqs (?cs1 @ [?c2]), s) \<Rightarrow>\<^bsup>Suc (2 * length (xs @ [x]))\<^esup> s3" 
    (* using *) (* t_seqs'_snoc *) (* t_seqs'_t_seqs *) sorry (* need case distinction on cs1 *)
  then have 1: "f \<turnstile> (mk_seqs ?cs', s) \<Rightarrow>\<^bsup>Suc (2 * length (xs @ [x]))\<^esup> s3"
    by (subst cs') assumption

  have 2: "lookups (ys @ [y]) s3 = lookups (xs @ [x]) s"
    using ih step snoc by auto

  have 3: "s3 = s on (- set (ys @ [y]))"
    using ih step by auto

  from 1 2 3 snoc show ?case by blast
qed (simp add: assms)

lemma compiled_arguments_bigstep':
  assumes "length vs = length ts" "length xs = length ts"
  assumes "relate_exec_state f_args bs vs_arg vs_b s"
  assumes "distinct xs"
  assumes "set xs \<subseteq> set keep"
  assumes "set f_args \<inter>\<^sub>\<emptyset> set xs" "set bs \<inter>\<^sub>\<emptyset> set xs"
  assumes "\<And>i s.
    \<lbrakk> i < length ts; relate_exec_state f_args bs vs_arg vs_b s \<rbrakk> \<Longrightarrow>
    \<exists>z s'. f \<turnstile> (to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i), s) \<Rightarrow>\<^bsup>z :: nat\<^esup> s' \<and>
             s' (xs ! i) = (vs ! i) \<and> s' = s on set f_args \<union> set bs \<union> set keep - {xs ! i}"
  obtains z s' where
    "f \<turnstile> (mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts)), s) \<Rightarrow>\<^bsup>z :: nat\<^esup> s'"
    "lookups xs s' = vs" "s' = s on set f_args \<union> set bs \<union> set keep - set xs"
  using compiled_arguments_bigstep[OF assms] by blast

lemma copy_list_bigstep':
  assumes "length xs = n"
  assumes "length ys = n"
  assumes "distinct ys"
  assumes "set xs \<inter>\<^sub>\<emptyset> set ys"
  obtains s' where
    "f \<turnstile> (mk_seqs (generate (\<lambda>i. (ys ! i) ::= A (V (xs ! i))) n),s) \<Rightarrow>\<^bsup>Suc (2 * n)\<^esup> s'"
    "lookups ys s' = lookups xs s" "s' = s on (- set ys)"
  using copy_list_bigstep[where xs = xs and ys = ys] assms by auto


abbreviation "calls_r t \<equiv> set (map fst (calls t))"

theorem compiler_correct_no_tails:
  assumes "\<not> tails t"
  assumes "(f,frgt) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup>z :: nat\<^esup> v"
  assumes "compiler_invar crgt f_args bs keep t"
  assumes "relate_rgt_correctness frgt crgt (calls_r t)"
  assumes "relate_exec_state f_args bs vs_arg vs_b s"
  shows "\<exists>z_c s'.
    f_c \<turnstile> (to_imp_tc f_args crgt bs r keep t,s) \<Rightarrow>\<^bsup>z_c :: nat\<^esup> s'
    \<and> s' r = v
    \<and> s' = s on set f_args \<union> set bs \<union> set keep - {r}"
using assms proof (induction t arbitrary: vs_b z v bs keep s r crgt)
  case (hLet t1 t2)

  let ?r1 = "fresh' (stale_registers f_args crgt bs keep LET t1 IN t2) ''Let.x''"
  let ?c1 = "to_imp_tc f_args crgt bs ?r1 keep t1"
  let ?c2 = "to_imp_tc f_args crgt (?r1 # bs) r (?r1 # keep) t2"

  from hLet.prems hLet_case
  obtain z1 v1 z2 :: nat where inv:
      "(f, frgt) \<turnstile> (t1, vs_b, vs_arg) \<Rightarrow>\<^bsup>z1\<^esup> v1"
      "(f, frgt) \<turnstile> (t2, v1 # vs_b, vs_arg) \<Rightarrow>\<^bsup>z2\<^esup> v"
    by blast

  (* solve assumptions and obtain IH for t1 *)

  from hLet.prems
  have no_tails: "\<not> HOL_TCN_Timing.tails t1" "\<not> HOL_TCN_Timing.tails t2" by simp_all

  from hLet.prems compiler_invar_let
  have comp_invar:
      "compiler_invar crgt f_args bs keep t1"
      "compiler_invar crgt f_args (?r1 # bs) (?r1 # keep) t2" by auto

  from hLet.prems
  have rel_rgt:
      "relate_rgt_correctness frgt crgt (calls_r t1)"
      "relate_rgt_correctness frgt crgt (calls_r t2)"
    unfolding relate_rgt_correctness_def by simp_all

  from hLet.prems have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" by blast

  obtain z1_c :: nat and s2 where ih1:
      "f_c \<turnstile> (?c1, s) \<Rightarrow>\<^bsup>z1_c\<^esup> s2" "s2 ?r1 = v1" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
    using hLet.IH(1) no_tails(1) inv(1) comp_invar(1) rel_rgt(1) rel_state1 by blast

  (* solve assumptions and obtain IH for t2 *)

  have s2_like_s: "s2 = s on set f_args \<union> set bs \<union> set keep" (* TODO *)
    by (metis Diff_empty Diff_insert0 Un_iff fresh_not_in_stale ih1(3) set_append stale_registers_def)
  then have rel_state2: "relate_exec_state f_args (?r1 # bs) vs_arg (v1 # vs_b) s2"
    using hLet.prems unfolding relate_exec_state_def using ih1 by fastforce

  obtain z2_c :: nat and s3 where ih2:
      "f_c \<turnstile> (?c2, s2) \<Rightarrow>\<^bsup>z2_c\<^esup>  s3" "s3 r = v"
      "s3 = s2 on set f_args \<union> set (?r1 # bs) \<union> set (?r1 # keep) - {r}"
    using hLet.IH(2) no_tails(2) inv(2) comp_invar(2) rel_rgt(2) rel_state2 by blast

  (* put it together *)

  have "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
    using Un_Diff ih2(3) by auto
  with s2_like_s have "s3 = s on set f_args \<union> set bs \<union> set keep - {r}"
    by (simp add: eq_on_def)

  then show ?case
    unfolding to_imp_tc.simps Let_def
    using ih1 ih2 by blast
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
  let ?c1 = "to_imp_tc f_args crgt bs ?r1 keep t1"
  let ?c2 = "to_imp_tc f_args crgt bs r keep t2"
  let ?c3 = "to_imp_tc f_args crgt bs r keep t3"

  from hIf.prems
  have no_tails:
    "\<not> HOL_TCN_Timing.tails t1"
    "\<not> HOL_TCN_Timing.tails t2"
    "\<not> HOL_TCN_Timing.tails t3" by simp_all

  from compiler_invar_if[OF hIf.prems(3)]
  have comp_invar:
      "compiler_invar crgt f_args bs keep t1"
      "compiler_invar crgt f_args bs keep t2"
      "compiler_invar crgt f_args bs keep t3" by auto

  from hIf.prems
  have rel_rgt:
      "relate_rgt_correctness frgt crgt (calls_r t1)"
      "relate_rgt_correctness frgt crgt (calls_r t2)"
      "relate_rgt_correctness frgt crgt (calls_r t3)"
    unfolding relate_rgt_correctness_def by simp_all

  from hIf.prems have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" by blast

  show ?case
  proof (cases rule: hIf_case[OF hIf.prems(2)])
    case ifTrue: (1 z1 v1 z2)

    obtain z1_c :: nat and s2 where ih1:
        "f_c \<turnstile> (?c1, s) \<Rightarrow>\<^bsup>z1_c\<^esup> s2"
        "s2 ?r1 = v1" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
      using hIf.IH(1) no_tails(1) ifTrue comp_invar(1) rel_rgt(1) rel_state1 by blast

    have s2_like_s: "s2 = s on set f_args \<union> set bs \<union> set keep" (* TODO *)
      by (metis Diff_empty Diff_insert0 Un_iff fresh_not_in_stale ih1(3) set_append stale_registers_def)
    then have rel_state2: "relate_exec_state f_args bs vs_arg vs_b s2"
      using hIf.prems unfolding relate_exec_state_def using ih1 by fastforce

    obtain z2_c :: nat and s3 where ih2:
        "f_c \<turnstile> (?c2, s2) \<Rightarrow>\<^bsup>z2_c\<^esup>  s3" "s3 r = v"
        "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
      using hIf.IH(2) no_tails(2) ifTrue comp_invar(2) rel_rgt(2) rel_state2 by blast
  
    have "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
      using Un_Diff ih2(3) by auto
    with s2_like_s have "s3 = s on set f_args \<union> set bs \<union> set keep - {r}"
      by (simp add: eq_on_def)
  
    then show ?thesis
      unfolding to_imp_tc.simps Let_def
      using ih1 ih2 ifTrue by blast
  next
    case ifFalse: (2 z1 z2)

    obtain z1_c :: nat and s2 where ih1:
        "f_c \<turnstile> (?c1, s) \<Rightarrow>\<^bsup>z1_c\<^esup> s2"
        "s2 ?r1 = 0" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
      using hIf.IH(1) no_tails(1) ifFalse comp_invar(1) rel_rgt(1) rel_state1 by metis

    have s2_like_s: "s2 = s on set f_args \<union> set bs \<union> set keep" (* TODO *)
      by (metis Diff_empty Diff_insert0 Un_iff fresh_not_in_stale ih1(3) set_append stale_registers_def)
    then have rel_state3: "relate_exec_state f_args bs vs_arg vs_b s2"
      using hIf.prems(5) unfolding relate_exec_state_def using ih1 by fastforce

    obtain z2_c :: nat and s3 where ih3:
        "f_c \<turnstile> (?c3, s2) \<Rightarrow>\<^bsup>z2_c\<^esup>  s3" "s3 r = v"
        "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
      using hIf.IH(3) no_tails(3) ifFalse comp_invar(3) rel_rgt(3) rel_state3 by blast
  
    have "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
      using Un_Diff ih3(3) by auto
    with s2_like_s have "s3 = s on set f_args \<union> set bs \<union> set keep - {r}"
      by (simp add: eq_on_def)
  
    then show ?thesis
      unfolding to_imp_tc.simps Let_def
      using ih1 ih3 ifFalse by blast
  qed
next
  case (hCall gr ts)

  let ?g = "f_from_frgt frgt gr"
  let ?T_g = "T_f_from_frgt frgt gr"

  from hCall.prems hCall_case
  obtain zs vs :: "nat list" where
          z: "z = sum_list zs + ?T_g vs"
      and lengths: "length zs = length ts" "length vs = length ts"
      and args_bigstep: "\<forall>i<length ts. (f, frgt) \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>zs ! i\<^esup> vs ! i"
      and gvs: "?g vs = v"
    using split_from_frgt by auto

  (* part 1: computing the arguments *)

  let ?xs = "make_n_fresh (stale_registers f_args crgt bs keep (hCall gr ts)) ''Call.x.'' (length ts)"
  let ?c1 = "mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ keep) (ts ! i)) (length ts))"

  have "length vs = length ts" "length ?xs = length ts"
    using lengths unfolding make_n_fresh_def generate_def by simp_all
  moreover have "relate_exec_state f_args bs vs_arg vs_b s" using hCall by blast
  moreover have "distinct ?xs" using distinct_make_n_fresh by blast
  moreover have "set ?xs \<subseteq> set (?xs @ keep)" by simp
  moreover have "set f_args \<inter>\<^sub>\<emptyset> set ?xs" "set bs \<inter>\<^sub>\<emptyset> set ?xs"
    unfolding stale_registers_def using make_n_fresh_not_in_stale by fastforce+
  moreover have
      "\<exists>z_c s'. f_c \<turnstile> (to_imp_tc f_args crgt bs (?xs ! i) (?xs @ keep) (ts ! i), s) \<Rightarrow>\<^bsup>z_c :: nat\<^esup>  s' \<and>
                s' (?xs ! i) = (vs ! i) \<and> s' = s on set f_args \<union> set bs \<union> set (?xs @ keep) - {?xs ! i}"
    if "i < length ts" "relate_exec_state f_args bs vs_arg vs_b s" for i s
  proof (rule hCall.IH)
    from that show "ts ! i \<in> set ts" by simp
  next
    from that hCall.prems
    show "\<not> HOL_TCN_Timing.tails (ts ! i)" by simp
  next
    from that args_bigstep
    show "(f, frgt) \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>zs ! i\<^esup>  vs ! i" by simp
  next
    from that hCall.prems compiler_invar_call
    show "compiler_invar crgt f_args bs (?xs @ keep) (ts ! i)" by simp
  next
    from that show "relate_rgt_correctness frgt crgt (calls_r (ts ! i))"
      using hCall.prems(4) unfolding relate_rgt_correctness_def by fastforce
  next
    from that show "relate_exec_state f_args bs vs_arg vs_b s" by blast
  qed

  ultimately obtain z1 :: nat and s2 where exec_c1: "f_c \<turnstile> (?c1, s) \<Rightarrow>\<^bsup>z1\<^esup>  s2"
      "lookups ?xs s2 = vs" "s2 = s on set f_args \<union> set bs \<union> set (?xs @ keep) - set ?xs"
    using compiled_arguments_bigstep' by blast

  (* part 2: copying from temporaries to argument registers *)

  let ?c2 = "mk_seqs (generate (\<lambda>i. (args_from_crgt crgt gr ! i) ::= A (V (?xs ! i))) (length ts))"
  let ?z2 = "Suc (2 * length ts)"

  have "set (args_from_crgt crgt gr) \<subseteq> set (stale_registers f_args crgt bs keep (hCall gr ts))"
    unfolding stale_registers_def call_registers_def using calls'_set by auto
  then have "set ?xs \<inter>\<^sub>\<emptyset> set (args_from_crgt crgt gr)"
    using make_n_fresh_not_in_stale by blast
  moreover have "distinct (args_from_crgt crgt gr)"
    using hCall.prems unfolding compiler_invar_def calls'_set by simp
  moreover have "length ?xs = length ts"
    unfolding make_n_fresh_def generate_def by simp
  moreover have "length (args_from_crgt crgt gr) = length ts"
    using hCall.prems unfolding compiler_invar_def calls_n_set by simp

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
  obtain z4 :: nat where exec_c4: "f_c \<turnstile> (?c4, ?s4) \<Rightarrow>\<^bsup>z4\<^esup> ?s5" by blast
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
      using hCall.prems(3) unfolding compiler_invar_def call_registers_def using calls'_set by auto
    then have **: "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
      using hCall.prems(3) exec_c2 unfolding compiler_invar_def by auto

    have "ret_from_crgt crgt gr \<notin> set f_args \<union> set bs \<union> set keep"
      using hCall.prems(3) unfolding compiler_invar_def call_registers_def using calls'_set by auto
    then have ***: "?s5 = s3 on set f_args \<union> set bs \<union> set keep - {r}" by auto

    show "?s5 = s on set f_args \<union> set bs \<union> set keep - {r}"
      using * ** *** by fastforce
  qed

next
  case (hTAIL x)
  then show ?case by simp
qed

(* In the compiled trace relatedness proof, we frequently apply the IH to obtain relatedness
   theorems for subterms (assumption comp_rel). By using the theorems relating traces and bigstep
   semantics, we can add the compiler correctness results for the execution of those subterms.
   Those we need to continue applying the IH to further subterms, e.g. the IH for the second
   LET subterm requires a well-formed starting state. *)
lemma compiler_augment_rel_trace:
  assumes no_tails: "\<not> HOL_TCN_Timing.tails t"
  assumes htrace: "frgt \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup> hT :: HOL_TCN_Timing.call_trace \<^esup> Value v"
  assumes comp_assms:
    "compiler_invar crgt f_args bs keep t"
    and "relate_rgt_correctness frgt crgt (calls_r t)"
    and "relate_exec_state f_args bs vs_arg vs_b s"
  assumes comp_rel:
    "(to_imp_tc f_args crgt bs r keep t,s) \<Rightarrow>\<^bsup>(k, cT)\<^esup> (s', False)"
    and "rel_trace_to_leaf crgt f_args r hT (Value v) cT s' False"
  shows "s' r = v" "s' = s on set f_args \<union> set bs \<union> set keep - {r}"
proof -
  from assms trace_leaf_nontail_bigstep
  obtain f z where "(f,frgt) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup>z :: nat\<^esup> v" by blast

  then obtain f_c z_c s2 where correct:
      "f_c \<turnstile> (to_imp_tc f_args crgt bs r keep t,s) \<Rightarrow>\<^bsup>z_c :: nat\<^esup> s2" "s2 r = v"
      "s2 = s on set f_args \<union> set bs \<union> set keep - {r}"
    using compiler_correct_no_tails[where t = t] assms by blast

  have "s2 = s'" using correct(1) IMP_Tailcall_Traces.trace_leaf_nontail_bigstep[OF comp_rel(1)] determ(2) by blast

  then show "s' r = v" "s' = s on set f_args \<union> set bs \<union> set keep - {r}" using correct by simp_all
qed

(* executing a list of terms (as in the call and tail-call cases) *)
lemma compiled_arguments_trace:
  assumes lengths: "length vs = length ts" "length xs = length ts" "length hTs = length ts"
  assumes rel: "relate_exec_state f_args bs vs_arg vs_b s"
  assumes args: "distinct xs" "set xs \<subseteq> set keep" "set f_args \<inter>\<^sub>\<emptyset> set xs" "set bs \<inter>\<^sub>\<emptyset> set xs"
  assumes trace: "\<And>i. i < length ts \<Longrightarrow> frgt \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>hTs ! i\<^esup>  Value (vs ! i)"
  assumes sem: "\<And>i s.
    \<lbrakk> i < length ts; relate_exec_state f_args bs vs_arg vs_b s \<rbrakk> \<Longrightarrow>
    \<exists>k cT s'. (to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i), s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False) \<and>
              rel_trace_to_leaf crgt f_args (xs ! i) (hTs ! i) (Value (vs ! i)) cT s' False \<and>
              s' (xs ! i) = (vs ! i) \<and> s' = s on set f_args \<union> set bs \<union> set keep - {xs ! i}"
  shows "\<exists>k cT s'. (mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts)), s) \<Rightarrow>\<^bsup>(k, cT)\<^esup> (s', False) \<and>
                   rel_trace_calls crgt (concat hTs) cT \<and>
                   lookups xs s' = vs \<and> s' = s on set f_args \<union> set bs \<union> set keep - set xs"
using args trace sem proof (induction ts xs vs hTs rule: snoc_list_induct4)
  case Nil
  then show ?case unfolding generate_def rel_trace_calls_def using ttrace_to_leaf.tSkip by auto
next
  case (snoc ts t xs x vs v hTs hT)

  (* obtain the IH *)
  have *: "i < length (ts @ [t])" if "i < length ts" for i using that by simp

  from snoc have "distinct xs" "set xs \<subseteq> set keep" "set f_args \<inter>\<^sub>\<emptyset> set xs" "set bs \<inter>\<^sub>\<emptyset> set xs" by simp_all
  moreover from * snoc.prems have "frgt \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>hTs ! i\<^esup>  Value (vs ! i)" if "i < length ts" for i
    using that nth_append_left snoc.hyps by metis
  moreover from * snoc.prems have "\<exists>k cT s'.
        (to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i), s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False) \<and>
        rel_trace_to_leaf crgt f_args (xs ! i) (hTs ! i) (Value (vs ! i)) cT s' False \<and>
        s' (xs ! i) = (vs ! i) \<and> s' = s on set f_args \<union> set bs \<union> set keep - {xs ! i}"
      if "i < length ts" "relate_exec_state f_args bs vs_arg vs_b s" for i s
    using that nth_append_left snoc.hyps by metis

  ultimately obtain k1 cT1 s2 where trace1:
      "(mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts)), s) \<Rightarrow>\<^bsup>(k1, cT1)\<^esup>  (s2, False)"
      "rel_trace_calls crgt (concat hTs) cT1"
      "lookups xs s2 = vs" "s2 = s on set f_args \<union> set bs \<union> set keep - set xs"
    using snoc.IH by blast

  (* obtain the step *)

  have *: "length ts < length (ts @ [t])" by simp

  from rel trace1(4) snoc.prems(3,4) have **: "relate_exec_state f_args bs vs_arg vs_b s2"
    unfolding relate_exec_state_def by fastforce

  from * ** snoc.prems(6)
  obtain k2 cT2 s3 where trace2:
      "(to_imp_tc f_args crgt bs ((xs @ [x]) ! length ts) keep ((ts @ [t]) ! length ts), s2) \<Rightarrow>\<^bsup>(k2, cT2)\<^esup>  (s3, False)"
      "rel_trace_to_leaf crgt f_args ((xs @ [x]) ! length ts) ((hTs @ [hT]) ! length ts) (Value ((vs @ [v]) ! length ts)) cT2 s3 False"
      "s3 ((xs @ [x]) ! length ts) = (vs @ [v]) ! length ts"
      "s3 = s2 on set f_args \<union> set bs \<union> set keep - {(xs @ [x]) ! length ts}"
    by blast

  (* put it together *)

  have nth: "(xs @ [x]) ! length ts = x" "(vs @ [v]) ! length ts = v" "(hTs @ [hT]) ! length ts = hT"
    using nth_append_length_eq snoc.hyps by metis+

  show ?case
  proof (repeat \<open>rule exI\<close>, repeat \<open>rule conjI\<close>)

    have "(xs @ [x]) ! i = xs ! i" "(ts @ [t]) ! i = ts ! i" if "i < length ts" for i
      using nth_append_left snoc.hyps that by metis+
    then have "generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts) =
        generate (\<lambda>i. to_imp_tc f_args crgt bs ((xs @ [x]) ! i) keep ((ts @ [t]) ! i)) (length ts)"
      unfolding generate_def by simp
    then have append_cs:
        "generate (\<lambda>i. to_imp_tc f_args crgt bs ((xs @ [x]) ! i) keep ((ts @ [t]) ! i)) (length (ts @ [t])) =
         generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts) @
         [to_imp_tc f_args crgt bs ((xs @ [x]) ! length ts) keep ((ts @ [t]) ! length ts)]"
      by (simp add: generate_snoc)
  
    have "(mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts));;
                to_imp_tc f_args crgt bs ((xs @ [x]) ! length ts) keep ((ts @ [t]) ! length ts), s) \<Rightarrow>\<^bsup>(k1 + k2, cT1 @ cT2)\<^esup> (s3,False)"
      using trace1 trace2 ttrace_to_leaf.tSeq by blast
    then show "(mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs ((xs @ [x]) ! i) keep ((ts @ [t]) ! i)) (length (ts @ [t]))), s) \<Rightarrow>\<^bsup>(k1 + k2, cT1 @ cT2)\<^esup> (s3,False)"
      using append_cs (* t_seqs'_t_seqs *) sorry
  next
    show "rel_trace_calls crgt (concat (hTs @ [hT])) (cT1 @ cT2)"
      using rel_trace_calls_append trace1(2) trace2(2)[simplified rel_trace_to_leaf_def nth] by simp
  next
    from trace2(3) have "s3 x = v" using snoc.hyps nth_append_length by metis
    moreover from trace2(4) nth(1) snoc.prems(1,2) have "s3 = s2 on set xs" by auto
    ultimately show "lookups (xs @ [x]) s3 = vs @ [v]" using trace1(3) by auto
  next
    show "s3 = s on set f_args \<union> set bs \<union> set keep - set (xs @ [x])"
      using nth trace1(4) trace2(4) by auto
  qed

qed (simp_all add: lengths)

(* copying a list of registers *)
lemma copy_list_trace:
  assumes "length xs = length ys"
  assumes "distinct ys"
  assumes "set xs \<inter>\<^sub>\<emptyset> set ys"
  obtains s' where
    "(mk_seqs (generate (\<lambda>i. (ys ! i) ::= A (V (xs ! i))) (length xs)),s) \<Rightarrow>\<^bsup>(Suc (2 * length xs), [])\<^esup> (s', False)"
    "lookups ys s' = lookups xs s" "s' = s on (- set ys)"
using assms proof (induction xs ys arbitrary: thesis rule: snoc_list_induct2)
  case Nil
  then show ?case unfolding generate_def using ttrace_to_leaf.tSkip by auto
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
      "(mk_seqs ?cs1, s) \<Rightarrow>\<^bsup>(Suc (2 * length xs), [])\<^esup> (s2,False)"
      "lookups ys s2 = lookups xs s" "s2 = s on (- set ys)"
    by auto
  moreover obtain s3 where step:
      "(?c2, s2) \<Rightarrow>\<^bsup>(Suc (Suc 0), [])\<^esup> (s3, False)"
      "s3 y = s2 x" "s3 = s2 on (- {y})"
    using ttrace_to_leaf.tAssign by fastforce
  ultimately have "(mk_seqs ?cs1;; ?c2, s) \<Rightarrow>\<^bsup>(Suc (2 * length (xs @ [x])), [])\<^esup> (s3,False)"
    using ttrace_to_leaf.tSeq by auto
  then have "(mk_seqs (?cs1 @ [?c2]), s) \<Rightarrow>\<^bsup>(Suc (2 * length (xs @ [x])), [])\<^esup> (s3,False)" 
    (* using (* t_seqs'_snoc *) t_seqs'_t_seqs *) sorry
  then have 1: "(mk_seqs ?cs', s) \<Rightarrow>\<^bsup>(Suc (2 * length (xs @ [x])), [])\<^esup> (s3,False)"
    by (subst cs') assumption

  have "s3 = s2 on set ys" using snoc step by auto
  then have "lookups ys s3 = lookups ys s2" by auto
  then have 2: "lookups (ys @ [y]) s3 = lookups (xs @ [x]) s"
    using ih step snoc by auto

  have 3: "s3 = s on (- set (ys @ [y]))"
    using ih step by auto

  from 1 2 3 snoc show ?case by blast
qed (simp add: assms)

lemma compiled_arguments_trace':
  assumes lengths: "length vs = length ts" "length xs = length ts" "length hTs = length ts"
  assumes rel: "relate_exec_state f_args bs vs_arg vs_b s"
  assumes dist: "distinct xs"
  assumes keep_xs: "set xs \<subseteq> set keep"
  assumes disj: "set f_args \<inter>\<^sub>\<emptyset> set xs" "set bs \<inter>\<^sub>\<emptyset> set xs"
  assumes trace: "\<And>i. i < length ts \<Longrightarrow> frgt \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>hTs ! i\<^esup>  Value (vs ! i)"
  assumes sem: "\<And>i s.
    \<lbrakk> i < length ts; relate_exec_state f_args bs vs_arg vs_b s \<rbrakk> \<Longrightarrow>
    \<exists>k cT s'. (to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i), s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False) \<and>
              rel_trace_to_leaf crgt f_args (xs ! i) (hTs ! i) (Value (vs ! i)) cT s' False \<and>
              s' (xs ! i) = (vs ! i) \<and> s' = s on set f_args \<union> set bs \<union> set keep - {xs ! i}"
  obtains k cT s' where
    "(mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts)), s) \<Rightarrow>\<^bsup>(k, cT)\<^esup> (s', False)"
    "rel_trace_calls crgt (concat hTs) cT"
    "lookups xs s' = vs \<and> s' = s on set f_args \<union> set bs \<union> set keep - set xs"
  using compiled_arguments_trace[OF assms] by blast

lemma copy_list_trace':
  assumes "length xs = n"
  assumes "length ys = n"
  assumes "distinct ys"
  assumes "set xs \<inter>\<^sub>\<emptyset> set ys"
  obtains s' where
    "(mk_seqs (generate (\<lambda>i. (ys ! i) ::= A (V (xs ! i))) (length xs)),s) \<Rightarrow>\<^bsup>(Suc (2 * length xs), [])\<^esup> (s', False)"
    "lookups ys s' = lookups xs s" "s' = s on (- set ys)"
  using copy_list_trace[where xs = xs and ys = ys] assms by auto


theorem compiler_rel_trace:
  assumes "invar t"
  assumes "frgt \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup> hT :: HOL_TCN_Timing.call_trace \<^esup> hl"
  assumes "compiler_invar crgt f_args bs keep t"
  assumes "relate_rgt_correctness frgt crgt (calls_r t)"
  assumes "relate_exec_state f_args bs vs_arg vs_b s"
  shows "\<exists>k cT s' cl.
    (to_imp_tc f_args crgt bs r keep t,s)\<Rightarrow>\<^bsup>(k, cT)\<^esup> (s', cl)
    \<and> rel_trace_to_leaf crgt f_args r hT hl cT s' cl"
using assms(2) assms(1,3-) proof (induction arbitrary: bs keep s r crgt rule: htrace_to_leaf_induct)
  case (hLet frgt t1 vs_b vs_arg T1 v1 t2 T2 l2 T)

  let ?r1 = "fresh' (stale_registers f_args crgt bs keep LET t1 IN t2) ''Let.x''"
  let ?c1 = "to_imp_tc f_args crgt bs ?r1 keep t1"
  let ?c2 = "to_imp_tc f_args crgt (?r1 # bs) r (?r1 # keep) t2"

  (* solve assumptions, and obtain IH for t1 *)

  from hLet.prems have
      no_tails1: "\<not> HOL_TCN_Timing.tails t1"
      and invar: "HOL_TCN_Timing.invar t1" "HOL_TCN_Timing.invar t2"
    by simp_all

  from hLet.prems compiler_invar_let
  have comp_invar:
      "compiler_invar crgt f_args bs keep t1"
      "compiler_invar crgt f_args (?r1 # bs) (?r1 # keep) t2" by auto

  from hLet.prems
  have rel_rgt:
      "relate_rgt_correctness frgt crgt (calls_r t1)"
      "relate_rgt_correctness frgt crgt (calls_r t2)"
    unfolding relate_rgt_correctness_def by simp_all

  from hLet.prems have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" by blast

  from
    hLet.IH(1)[OF invar(1) comp_invar(1) rel_rgt(1) rel_state1] rel_trace_to_leaf_cl  (* why does this need to be instantiated??? clean up *)
    compiler_augment_rel_trace[where t = t1, OF no_tails1 hLet.hyps(1) comp_invar(1) rel_rgt(1) rel_state1]
  obtain k1 cT1 s2 where
      ih1:
        "(to_imp_tc f_args crgt bs ?r1 keep t1, s) \<Rightarrow>\<^bsup>(k1, cT1)\<^esup>  (s2, False)"
        "rel_trace_to_leaf crgt f_args ?r1 T1 (Value v1) cT1 s2 False"
      and corr1: "s2 ?r1 = v1" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
    by (metis (full_types))

  (* solve assumptions and obtain IH for t2 *)

  have "s2 = s on set f_args \<union> set bs \<union> set keep" (* TODO *)
    by (smt (verit) DiffI Un_iff eq_on_def fresh_not_in_stale corr1(2) set_append singletonD stale_registers_def)
  then have rel_state2: "relate_exec_state f_args (?r1 # bs) vs_arg (v1 # vs_b) s2"
    using hLet.prems(4) unfolding relate_exec_state_def using corr1(1) by fastforce

  obtain k2 cT2 s3' cl2 where ih2:
      "(?c2,s2)\<Rightarrow>\<^bsup>(k2,cT2)\<^esup> (s3',cl2)" "rel_trace_to_leaf crgt f_args r T2 l2 cT2 s3' cl2"
    using hLet.IH(2) invar(2) comp_invar(2) rel_rgt(2) rel_state2 by blast

  (* putting it together *)

  show ?case unfolding to_imp_tc.simps Let_def
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    show "(?c1;; ?c2,s) \<Rightarrow>\<^bsup>(k1 + k2, cT1 @ cT2)\<^esup> (s3', cl2)"
      using ttrace_to_leaf.tSeq ih1(1) ih2(1) by blast
  next
    show "rel_trace_to_leaf crgt f_args r T l2 (cT1 @ cT2) s3' cl2"
      using hLet.hyps(3) rel_trace_to_leaf_append ih1(2) ih2(2)
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
  case (hIfTrue frgt t1 vs_b vs_arg T1 v1 t2 T2 l2 T t3)

  let ?r1 = "fresh' (stale_registers f_args crgt bs keep (IF t1\<noteq>0 THEN t2 ELSE t3)) ''If.x''"
  let ?c1 = "to_imp_tc f_args crgt bs ?r1 keep t1"
  let ?c2 = "to_imp_tc f_args crgt bs r keep t2"
  let ?c3 = "to_imp_tc f_args crgt bs r keep t3"

  from hIfTrue.prems
  have no_tails: "\<not> HOL_TCN_Timing.tails t1"
      and invar: "HOL_TCN_Timing.invar t1" "HOL_TCN_Timing.invar t2" by simp_all

  from compiler_invar_if[OF hIfTrue.prems(2)]
  have comp_invar:
      "compiler_invar crgt f_args bs keep t1"
      "compiler_invar crgt f_args bs keep t2" by auto

  from hIfTrue.prems
  have rel_rgt:
      "relate_rgt_correctness frgt crgt (calls_r t1)"
      "relate_rgt_correctness frgt crgt (calls_r t2)"
    unfolding relate_rgt_correctness_def by simp_all

  from hIfTrue.prems have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" by blast

  (* t1 *)

  from
    hIfTrue.IH(1)[OF invar(1) comp_invar(1) rel_rgt(1) rel_state1] rel_trace_to_leaf_cl  (* why does this need to be instantiated??? clean up *)
    compiler_augment_rel_trace[where t = t1, OF no_tails hIfTrue.hyps(1) comp_invar(1) rel_rgt(1) rel_state1]
  obtain k1 cT1 s2 where
      ih1:
        "(to_imp_tc f_args crgt bs ?r1 keep t1, s) \<Rightarrow>\<^bsup>(k1, cT1)\<^esup>  (s2, False)"
        "rel_trace_to_leaf crgt f_args ?r1 T1 (Value v1) cT1 s2 False"
      and corr1: "s2 ?r1 = v1" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
    by (metis (full_types))

  (* t2 *)

  have "s2 = s on set f_args \<union> set bs \<union> set keep" (* TODO *)
    by (smt (verit) DiffI Un_iff eq_on_def fresh_not_in_stale corr1(2) set_append singletonD stale_registers_def)
  then have rel_state2: "relate_exec_state f_args bs vs_arg vs_b s2"
    using hIfTrue.prems unfolding relate_exec_state_def by fastforce

  from hIfTrue.IH(2) invar(2) comp_invar(2) rel_rgt(2) rel_state2
  obtain k2 cT2 s3' cl2 where ih2:
      "(?c2,s2)\<Rightarrow>\<^bsup>(k2,cT2)\<^esup> (s3',cl2)" "rel_trace_to_leaf crgt f_args r T2 l2 cT2 s3' cl2"
    by blast

  (* putting it together *)

  show ?case unfolding to_imp_tc.simps Let_def
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    show "(?c1;; IF ?r1\<noteq>0 THEN ?c2 ELSE ?c3,s) \<Rightarrow>\<^bsup>(Suc (k1 + k2), cT1 @ cT2)\<^esup> (s3', cl2)"
    proof
      show "(?c1,s) \<Rightarrow>\<^bsup>(k1, cT1)\<^esup> (s2, False)" using ih1(1) by simp
      show "(IF ?r1\<noteq>0 THEN ?c2 ELSE ?c3,s2)\<Rightarrow>\<^bsup>(Suc k2, cT2)\<^esup> (s3', cl2)"
      proof (rule ttrace_to_leaf.tIfTrue)
        show "s2 ?r1 \<noteq> 0" using hIfTrue.hyps corr1(1) by simp
        show "(?c2, s2) \<Rightarrow>\<^bsup>(k2, cT2)\<^esup>  (s3', cl2)" using ih2(1) by blast
      qed simp
    qed simp_all
    show "rel_trace_to_leaf crgt f_args r T l2 (cT1 @ cT2) s3' cl2"
      using hIfTrue.hyps(4) rel_trace_to_leaf_append ih1(2) ih2(2)
      unfolding rel_trace_to_leaf_def by blast
  qed
next
  case (hIfFalse frgt t1 vs_b vs_arg T1 v1 t3 T3 l3 T t2)

  let ?r1 = "fresh' (stale_registers f_args crgt bs keep (IF t1\<noteq>0 THEN t2 ELSE t3)) ''If.x''"
  let ?c1 = "to_imp_tc f_args crgt bs ?r1 keep t1"
  let ?c2 = "to_imp_tc f_args crgt bs r keep t2"
  let ?c3 = "to_imp_tc f_args crgt bs r keep t3"

  from hIfFalse.prems
  have no_tails: "\<not> HOL_TCN_Timing.tails t1"
      and invar: "HOL_TCN_Timing.invar t1" "HOL_TCN_Timing.invar t3" by simp_all

  from compiler_invar_if[OF hIfFalse.prems(2)]
  have comp_invar:
      "compiler_invar crgt f_args bs keep t1"
      "compiler_invar crgt f_args bs keep t3" by auto

  from hIfFalse.prems
  have rel_rgt:
      "relate_rgt_correctness frgt crgt (calls_r t1)"
      "relate_rgt_correctness frgt crgt (calls_r t3)"
    unfolding relate_rgt_correctness_def by simp_all

  from hIfFalse.prems have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" by blast

  (* t1 *)

  from
    hIfFalse.IH(1)[OF invar(1) comp_invar(1) rel_rgt(1) rel_state1] rel_trace_to_leaf_cl  (* why does this need to be instantiated??? clean up *)
    compiler_augment_rel_trace[where t = t1, OF no_tails hIfFalse.hyps(1) comp_invar(1) rel_rgt(1) rel_state1]
  obtain k1 cT1 s2 where
      ih1:
        "(to_imp_tc f_args crgt bs ?r1 keep t1, s) \<Rightarrow>\<^bsup>(k1, cT1)\<^esup>  (s2, False)"
        "rel_trace_to_leaf crgt f_args ?r1 T1 (Value v1) cT1 s2 False"
      and corr1: "s2 ?r1 = v1" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
    by (metis (full_types))

  (* t2 *)

  have "s2 = s on set f_args \<union> set bs \<union> set keep" (* TODO *)
    by (smt (verit) DiffI Un_iff eq_on_def fresh_not_in_stale corr1(2) set_append singletonD stale_registers_def)
  then have rel_state2: "relate_exec_state f_args bs vs_arg vs_b s2"
    using hIfFalse.prems unfolding relate_exec_state_def by fastforce

  from hIfFalse.IH(2) invar(2) comp_invar(2) rel_rgt(2) rel_state2
  obtain k2 cT2 s3' cl2 where ih2:
      "(?c3,s2)\<Rightarrow>\<^bsup>(k2,cT2)\<^esup> (s3',cl2)" "rel_trace_to_leaf crgt f_args r T3 l3 cT2 s3' cl2"
    by blast

  (* putting it together *)

  show ?case unfolding to_imp_tc.simps Let_def
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    show "(?c1;; IF ?r1\<noteq>0 THEN ?c2 ELSE ?c3,s) \<Rightarrow>\<^bsup>(Suc (k1 + k2), cT1 @ cT2)\<^esup> (s3', cl2)"
    proof
      show "(?c1,s) \<Rightarrow>\<^bsup>(k1, cT1)\<^esup> (s2, False)" using ih1(1) by simp
      show "(IF ?r1\<noteq>0 THEN ?c2 ELSE ?c3,s2)\<Rightarrow>\<^bsup>(Suc k2, cT2)\<^esup> (s3', cl2)"
      proof (rule ttrace_to_leaf.tIfFalse)
        show "s2 ?r1 = 0" using hIfFalse.hyps corr1(1) by simp
        show "(?c3, s2) \<Rightarrow>\<^bsup>(k2, cT2)\<^esup>  (s3', cl2)" using ih2(1) by blast
      qed simp
    qed simp_all
    show "rel_trace_to_leaf crgt f_args r T l3 (cT1 @ cT2) s3' cl2"
      using hIfFalse.hyps(4) rel_trace_to_leaf_append ih1(2) ih2(2)
      unfolding rel_trace_to_leaf_def by blast
  qed
next
  case (hCall vs ts hTs frgt vs_b vs_arg T gr v)
  let ?g = "f_from_frgt frgt gr"
  let ?T_g = "T_f_from_frgt frgt gr"

  let ?xs = "make_n_fresh (stale_registers f_args crgt bs keep (hCall gr ts)) ''Call.x.'' (length ts)"
  let ?c_arg = "\<lambda>i. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ keep) (ts ! i)"
  let ?c1 = "mk_seqs (generate ?c_arg (length ts))"

  (* part 1: computing the arguments *)

  from hCall.prems
  have no_tails: "\<not> HOL_TCN_Timing.tails (ts ! i)" and invar: "HOL_TCN_Timing.invar (ts ! i)"
    if "i < length ts" for i using that by simp_all

  from compiler_invar_call[OF hCall.prems(2)]
  have comp_invar: "compiler_invar crgt f_args bs (?xs @ keep) (ts ! i)"
    if "i < length ts" for i using that by simp

  have "calls_r (ts ! i) \<subseteq> calls_r (hCall gr ts)" if "i < length ts" for i using that by fastforce
  with hCall.prems have rel_rgt:
      "relate_rgt_correctness frgt crgt (calls_r (ts ! i))"
    if "i < length ts" for i using that unfolding relate_rgt_correctness_def by blast

  from hCall.IH
  have htrace: "frgt \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>hTs ! i\<^esup>  Value (vs ! i)"
    if "i < length ts" for i using that by blast

  have aug_ih: "\<exists>k cT s'. (?c_arg i, s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False) \<and>
                      rel_trace_to_leaf crgt f_args (?xs ! i) (hTs ! i) (Value (vs ! i)) cT s' False \<and>
                      s' (?xs ! i) = vs ! i \<and> s' = s on set f_args \<union> set bs \<union> set (?xs @ keep) - {?xs ! i}"
    if "relate_exec_state f_args bs vs_arg vs_b s" "i < length ts" for i s
  proof goal_cases case 1

    from hCall.IH invar comp_invar rel_rgt that
    obtain k cT s' where trace:
      "(?c_arg i, s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False)"
      "rel_trace_to_leaf crgt f_args (?xs ! i) (hTs ! i) (Value (vs ! i)) cT s' False"
      using rel_trace_to_leaf_cl by (metis (full_types))

    moreover with compiler_augment_rel_trace no_tails htrace comp_invar rel_rgt that
    have "s' (?xs ! i) = vs ! i \<and> s' = s on set f_args \<union> set bs \<union> set (?xs @ keep) - {?xs ! i}"
      by metis

    ultimately show ?case by blast
  qed

  have lengths: "length vs = length ts" "length ?xs = length ts" "length hTs = length ts"
    using hCall.hyps unfolding make_n_fresh_def generate_def by simp_all
  have *: "distinct ?xs" using distinct_make_n_fresh by blast
  have **: "set ?xs \<subseteq> set (?xs @ keep)" by simp
  have ***: "set f_args \<inter>\<^sub>\<emptyset> set ?xs" "set bs \<inter>\<^sub>\<emptyset> set ?xs"
    unfolding stale_registers_def using make_n_fresh_not_in_stale by fastforce+

  from compiled_arguments_trace[OF lengths hCall.prems(4) * ** *** htrace aug_ih] (* TODO *)
  obtain k1 cTs s2 where
      trace1: "(?c1,s) \<Rightarrow>\<^bsup>(k1, cTs)\<^esup> (s2, False)" "rel_trace_calls crgt (concat hTs) cTs"
      and corr1: "lookups ?xs s2 = vs" "s2 = s on set f_args \<union> set bs \<union> set (?xs @ keep) - set ?xs"
    by blast

  (* part 2: copying from temporaries to argument registers *)

  let ?c2 = "mk_seqs (generate (\<lambda>i. (args_from_crgt crgt gr ! i) ::= A (V (?xs ! i))) (length ts))"
  let ?k2 = "Suc (2 * length ts)"

  have "set (args_from_crgt crgt gr) \<subseteq> set (stale_registers f_args crgt bs keep (hCall gr ts))"
    unfolding stale_registers_def call_registers_def using calls'_set by auto
  then have 1: "set ?xs \<inter>\<^sub>\<emptyset> set (args_from_crgt crgt gr)"
    using make_n_fresh_not_in_stale by blast
  moreover have 2: "distinct (args_from_crgt crgt gr)"
    using hCall.prems unfolding compiler_invar_def calls'_set by simp
  moreover have 3: "length ?xs = length ts"
    unfolding make_n_fresh_def generate_def by simp
  moreover have 4: "length (args_from_crgt crgt gr) = length ts"
    using hCall.prems unfolding compiler_invar_def calls_n_set by simp

  ultimately obtain s3 where trace2: "(?c2, s2) \<Rightarrow>\<^bsup>(?k2, [])\<^esup> (s3,False)"
       "lookup_args crgt gr s3 = lookups ?xs s2" "s3 = s2 on - set (args_from_crgt crgt gr)"
    using copy_list_trace'[OF 3 4 2 1] by auto (* ? *)

  (* part 3: calling g *)

  let ?gcom = "com_from_crgt crgt gr" and ?gret = "ret_from_crgt crgt gr" and ?gv = "f_from_frgt frgt gr (lookup_args crgt gr s3)"
  let ?c3 = "CALL ?gcom RETURN ?gret :: tcom"
  let ?k3 = "0 :: nat"
  let ?s4 = "s3(?gret := ?gv)"

  have "terminates_with_res_IMP ?gcom s3 ?gret ?gv" using hCall.prems unfolding relate_rgt_correctness_def by simp
  then obtain z3 s4' where "(?gcom, s3) \<Rightarrow>\<^bsup>z3\<^esup> s4'" "s4' ?gret = ?gv"
    unfolding terminates_with_res_IMP_def terminates_with_res_pred_time_IMP_def terminates_with_pred_time_IMP_def by blast
  then have trace3: "(?c3, s3) \<Rightarrow>\<^bsup>(?k3, [(?gcom, s3)])\<^esup> (?s4, False)" using ttrace_to_leaf.tCall by metis

  have g_args: "lookup_args crgt gr s3 = vs" using trace2 corr1 by simp
  then have g_call: "?gv = v" using trace1 hCall split_from_frgt by auto

  (* part 4: copying to r *)

  let ?c4 = "r ::= A (V (ret_from_crgt crgt gr)) :: tcom"

  let ?k4 = "Suc (Suc 0)"
  let ?s5 = "?s4(r := aval (A (V ?gret)) ?s4)"
  have trace4: "(?c4, ?s4) \<Rightarrow>\<^bsup>(?k4, [])\<^esup> (?s5, False)" using ttrace_to_leaf.tAssign by blast
  then have s5: "?s5 = ?s4(r := v)" using g_call trace3 by simp

  (* putting it together *)

  show ?case unfolding to_imp_tc.simps Let_def split_beta
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    show "(?c1;; ?c2;; ?c3;; ?c4, s) \<Rightarrow>\<^bsup>(k1 + ?k2 + ?k3 + ?k4, cTs @ [(?gcom, s3)])\<^esup> (?s5,False)"
      apply (repeat \<open>rule ttrace_to_leaf.tSeq\<close>)
      using trace1 trace2 trace3 trace4 by blast+ auto
  next
    have "rel_trace_call crgt gr vs ?gcom s3"
      unfolding rel_trace_call_def using g_args by blast
    then have *: "rel_trace_calls crgt [(gr, vs)] [(?gcom, s3)]"
      unfolding rel_trace_calls_def by simp

    have **: "rel_leaf_state crgt f_args r (Value v) ?s5 False"
      using g_call by simp
    
    from * ** trace1(2)
    show "rel_trace_to_leaf crgt f_args r T (Value v) (cTs @ [(?gcom, s3)]) ?s5 False"
      unfolding rel_trace_to_leaf_def \<open>T = concat hTs @ [(gr, vs)]\<close>
      using rel_trace_calls_append by blast
  qed
next
  case (hTail vs ts hTs frgt vs_b vs_arg T)

  let ?xs = "make_n_fresh (stale_registers f_args crgt bs keep (hTAIL ts)) ''TAIL.x.'' (length ts)"
  let ?c_arg = "\<lambda>i. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ keep) (ts ! i)"
  let ?c1 = "mk_seqs (generate ?c_arg (length ts))"

  (* part 1: computing the arguments *)

  from hTail.prems
  have no_tails: "\<not> HOL_TCN_Timing.tails (ts ! i)" and invar: "HOL_TCN_Timing.invar (ts ! i)"
    if "i < length ts" for i using that by simp_all

  from compiler_invar_tail[OF hTail.prems(2)]
  have comp_invar: "compiler_invar crgt f_args bs (?xs @ keep) (ts ! i)"
    if "i < length ts" for i using that by simp

  have "calls_r (ts ! i) \<subseteq> calls_r (hTAIL ts)" if "i < length ts" for i using that by fastforce
  with hTail.prems have rel_rgt:
      "relate_rgt_correctness frgt crgt (calls_r (ts ! i))"
    if "i < length ts" for i using that unfolding relate_rgt_correctness_def by blast

  from hTail.IH
  have htrace: "frgt \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>hTs ! i\<^esup>  Value (vs ! i)"
    if "i < length ts" for i using that by blast

  have aug_ih: "\<exists>k cT s'. (?c_arg i, s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False) \<and>
                      rel_trace_to_leaf crgt f_args (?xs ! i) (hTs ! i) (Value (vs ! i)) cT s' False \<and>
                      s' (?xs ! i) = vs ! i \<and> s' = s on set f_args \<union> set bs \<union> set (?xs @ keep) - {?xs ! i}"
    if "relate_exec_state f_args bs vs_arg vs_b s" "i < length ts" for i s
  proof goal_cases case 1

    from hTail.IH invar comp_invar rel_rgt that
    obtain k cT s' where trace:
      "(?c_arg i, s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False)"
      "rel_trace_to_leaf crgt f_args (?xs ! i) (hTs ! i) (Value (vs ! i)) cT s' False"
      using rel_trace_to_leaf_cl by (metis (full_types))

    moreover with compiler_augment_rel_trace no_tails htrace comp_invar rel_rgt that
    have "s' (?xs ! i) = vs ! i \<and> s' = s on set f_args \<union> set bs \<union> set (?xs @ keep) - {?xs ! i}"
      by metis

    ultimately show ?case by blast
  qed

  have lengths: "length vs = length ts" "length ?xs = length ts" "length hTs = length ts"
    using hTail.hyps unfolding make_n_fresh_def generate_def by simp_all
  have *: "distinct ?xs" using distinct_make_n_fresh by blast
  have **: "set ?xs \<subseteq> set (?xs @ keep)" by simp
  have ***: "set f_args \<inter>\<^sub>\<emptyset> set ?xs" "set bs \<inter>\<^sub>\<emptyset> set ?xs"
    unfolding stale_registers_def using make_n_fresh_not_in_stale by fastforce+

  from compiled_arguments_trace[OF lengths hTail.prems(4) * ** *** htrace aug_ih] (* TODO *)
  obtain k1 cTs s2 where
      trace1: "(?c1,s) \<Rightarrow>\<^bsup>(k1, cTs)\<^esup> (s2, False)" "rel_trace_calls crgt (concat hTs) cTs"
      and corr1: "lookups ?xs s2 = vs" "s2 = s on set f_args \<union> set bs \<union> set (?xs @ keep) - set ?xs"
    by blast

  (* part 2: copying from temporaries to argument registers *)

  let ?c2 = "mk_seqs (generate (\<lambda>i. (f_args ! i) ::= A (V (?xs ! i))) (length ts))"
  let ?k2 = "Suc (2 * length ts)"

  have "set f_args \<subseteq> set (stale_registers f_args crgt bs keep (hTAIL ts))"
    unfolding stale_registers_def call_registers_def using calls'_set by auto
  then have 1: "set ?xs \<inter>\<^sub>\<emptyset> set f_args"
    using make_n_fresh_not_in_stale by blast
  moreover have 2: "distinct f_args"
    using hTail.prems unfolding compiler_invar_def calls'_set by simp
  moreover have 3: "length ?xs = length ts"
    unfolding make_n_fresh_def generate_def by simp
  moreover have 4: "length f_args = length ts"
    using hTail.prems unfolding compiler_invar_def calls_n_set sorry (* need to change invariant *)

  ultimately obtain s3 where trace2: "(?c2, s2) \<Rightarrow>\<^bsup>(?k2, [])\<^esup> (s3,False)"
       "lookups f_args s3 = lookups ?xs s2" "s3 = s2 on - set f_args"
    using copy_list_trace'[OF 3 4 2 1] by auto (* ? *)

  have g_args: "lookups f_args s3 = vs" using trace2 corr1 by simp

  (* putting it together *)

  show ?case unfolding to_imp_tc.simps Let_def split_beta
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    show "(?c1;; ?c2;; tTAIL, s) \<Rightarrow>\<^bsup>(k1 + ?k2 + 5, cTs)\<^esup> (s3, True)"
      apply (repeat \<open>rule ttrace_to_leaf.tSeq ttrace_to_leaf.tTail\<close>)
      using trace1 trace2 by blast+ simp
  next
    have **: "rel_leaf_state crgt f_args r (Tail vs) s3 True"
      using g_args by simp

    from * ** trace1(2)
    show "rel_trace_to_leaf crgt f_args r T (Tail vs) cTs s3 True"
      unfolding rel_trace_to_leaf_def \<open>T = concat hTs\<close>
      using rel_trace_calls_append by blast
  qed
qed


lemma ind_tail:
  fixes P :: "thol \<Rightarrow> fun_registry \<Rightarrow> thol \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> HOL_TCN_Timing.call_trace \<Rightarrow> nat \<Rightarrow> bool"
  assumes invar: "invar t" "invar f"
  assumes trace: "(f,frgt) \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup> (k, T) :: HOL_TCN_Timing.trace \<^esup> v"
  assumes val:
    "\<And>f frgt t vs_b vs_arg T v.
      frgt \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup> T :: HOL_TCN_Timing.call_trace \<^esup> Value v \<Longrightarrow>
      P f frgt t vs_b vs_arg 0 T v"
  assumes tail:
    "\<And>f frgt t vs_b vs_arg k T1 T2 vs v.
      frgt \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup> T1 :: HOL_TCN_Timing.call_trace \<^esup> Tail vs \<Longrightarrow>
      (f, frgt) \<turnstile> (f, [], vs) \<Rightarrow>\<^bsup> (k, T2) :: HOL_TCN_Timing.trace \<^esup> v \<Longrightarrow>
      P f frgt f [] vs k T2 v \<Longrightarrow>
      P f frgt t vs_b vs_arg (k + 1) (T1 @ T2) v"
  shows "P f frgt t vs_b vs_arg k T v"
using assms(3,1) proof (induction k arbitrary: t vs_b vs_arg T v)
  case 0
  then have "frgt \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup>T\<^esup> Value v"
    using HOL_TCN_Timing.trace_end_nontail_trace_leaf by force
  then show ?case
    using val by blast
next
  case (Suc k)

  from trace_end_trace_leaf[OF Suc.prems(1,2)] obtain T1 l where
      "frgt \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup>T1\<^esup> l"
      "case l of Value v1 \<Rightarrow> Suc k = 0 \<and> T1 = T \<and> v1 = v
               | Tail ts \<Rightarrow> \<exists>T2. (f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(Suc k - 1, T2)\<^esup>  v \<and> T = T1 @ T2"
    by blast
  then obtain ts T2 where
      "frgt \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup>T1\<^esup> Tail ts"
      "(f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(k, T2)\<^esup> v" "T = T1 @ T2"
    by (cases l) auto

  with Suc tail invar(2) show ?case by simp
qed


(* due to `c_struct` and lemma `to_imp_num_commands` *)
definition "rel_trace_times t hk k \<equiv>
  k \<le> 35 * HOL_TCN_Timing.num_commands t * (hk + 1)"

lemma compiler_rel_trace_times_to_tail:
  assumes "(to_imp_tc f_args crgt bs r keep t,s)\<Rightarrow>\<^bsup>(k, cT)\<^esup> (s', l)"
  shows "rel_trace_times t hk k"
proof-
  have "k \<le> c_struct (to_imp_tc f_args crgt bs r keep t)"
    using assms trace_nontail_static_bound by blast
  also have "... \<le> 35 * HOL_TCN_Timing.num_commands t"
    using to_imp_num_commands by simp
  also have "... \<le> 35 * HOL_TCN_Timing.num_commands t * (hk + 1)" by simp
  finally show ?thesis unfolding rel_trace_times_def .
qed

lemma rel_trace_times_join:
  assumes "rel_trace_times t hk1 k1" "rel_trace_times t hk2 k2"
  shows "rel_trace_times t (hk1 + hk2 + 1) (k1 + k2)"
  using assms unfolding rel_trace_times_def by (simp add: algebra_simps)

lemma rel_trace_times_num_commands_mono:
  assumes "HOL_TCN_Timing.num_commands t \<le> HOL_TCN_Timing.num_commands f"
  assumes "rel_trace_times t hk k"
  shows "rel_trace_times f hk k"
  using assms unfolding rel_trace_times_def
  by (meson dual_order.refl mult_le_mono order_trans)

theorem compiler_rel_trace_end:
  assumes "invar t" "invar f"
  assumes "HOL_TCN_Timing.num_commands t \<le> HOL_TCN_Timing.num_commands f"
  assumes "(f,frgt) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup> (hk, hT) :: HOL_TCN_Timing.trace \<^esup> hv"
  assumes "compiler_invar crgt f_args bs keep t"
  assumes "compiler_invar crgt f_args [] [] f"
  assumes "relate_rgt_correctness frgt crgt (calls_r t)"
  assumes "relate_rgt_correctness frgt crgt (calls_r f)"
  assumes "relate_exec_state f_args bs vs_arg vs_b s"
  shows "\<exists>k cT s'.
    to_imp_tc f_args crgt [] r [] f \<turnstile> (to_imp_tc f_args crgt bs r keep t,s)\<Rightarrow>\<^bsup>(k, cT)\<^esup> s'
    \<and> rel_trace_to_end crgt r hT hv cT s'
    \<and> rel_trace_times f hk k"
using assms(1-3,5-) proof (induction arbitrary: s bs keep rule: ind_tail[OF assms(1,2,4)])
  (* base case: t executes to a value without a tail call *)
  case (1 f frgt t vs_b vs_arg T v)

  (* using the partial trace relatedness theorem, obtain a related trace *)
  with compiler_rel_trace obtain k cT s'
    where imp: "(to_imp_tc f_args crgt bs r keep t, s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False)"
      and rel: "rel_trace_to_leaf crgt f_args r T (Value v) cT s' False"
    using rel_trace_to_leaf_cl by (metis (full_types))

  (* turn the information about partial traces (ending in a value) to full traces *)
  from rel have "rel_trace_to_end crgt r T v cT s'"
    using rel_trace_to_leaf_value_rel_trace_to_end by simp
  moreover from imp have "f \<turnstile> (to_imp_tc f_args crgt bs r keep t, s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  s'" for f
    using IMP_Tailcall_Traces.trace_leaf_no_tail_trace_end by blast

  (* the running time until the tail call is bounded *)
  moreover from imp have "rel_trace_times f 0 k"
    using compiler_rel_trace_times_to_tail "1.prems" rel_trace_times_num_commands_mono by blast

  ultimately show ?case by blast
next
  (* inductive step: t executes to a tail call *)
  case (2 f frgt t vs_b vs_arg hk hT1 hT2 vs v)

  (* again using the partial trace relatedness theorem, obtain a related trace up to the tail call *)
  with compiler_rel_trace obtain ck1 cT1 s2
    where imp1: "(to_imp_tc f_args crgt bs r keep t, s) \<Rightarrow>\<^bsup>(ck1, cT1)\<^esup>  (s2, True)"
      and rel1: "rel_trace_to_leaf crgt f_args r hT1 (Tail vs) cT1 s2 True"
    using rel_trace_to_leaf_cl by (metis (full_types))
  then have rel_time1: "rel_trace_times f 0 ck1"
    using compiler_rel_trace_times_to_tail "2.prems" rel_trace_times_num_commands_mono by blast

  (* show that the intermediate state s2 encodes the initial context for the remaining trace *)
  from rel1 have "lookups f_args s2 = vs" unfolding rel_trace_to_leaf_def by simp
  then have rel_state2: "relate_exec_state f_args [] vs [] s2"
    unfolding relate_exec_state_def by simp

  (* from there, apply the IH to get the remaining trace *)
  with "2.IH" "2.prems" obtain ck2 cT2 s3
    where imp2: "to_imp_tc f_args crgt [] r [] f \<turnstile>(to_imp_tc f_args crgt [] r [] f, s2) \<Rightarrow>\<^bsup>(ck2, cT2)\<^esup>  s3"
      and rel2: "rel_trace_to_end crgt r hT2 v cT2 s3"
      and rel_time2: "rel_trace_times f hk ck2"
    by blast

  (* combine the first and second parts of the execution *)
  moreover from imp1 imp2 have
    "to_imp_tc f_args crgt [] r [] f \<turnstile>(to_imp_tc f_args crgt bs r keep t, s) \<Rightarrow>\<^bsup>(ck1 + ck2, cT1 @ cT2)\<^esup>  s3"
    using IMP_Tailcall_Traces.trace_leaf_tail_trace_end by auto
  moreover from rel1 rel2 have "rel_trace_to_end crgt r (hT1 @ hT2) v (cT1 @ cT2) s3"
    using rel_trace_to_end_append unfolding rel_trace_to_leaf_def by metis
  moreover from rel_time1 rel_time2 have "rel_trace_times f (hk + 1) (ck1 + ck2)"
    using rel_trace_times_join by fastforce

  ultimately show ?case by blast
qed



definition "terminates_time_order_IMP p T_f =
  (\<exists>f. HOL_Nat_To_IMP.terminates_with_time_order_IMP p f T_f)"

(* TODO "fs" or "set fs" *)
definition "relate_rgt_time frgt crgt fs \<longleftrightarrow> (\<forall>f \<in> set fs.
  terminates_time_order_IMP (com_from_crgt crgt f) (T_f_from_frgt frgt f o lookup_args crgt f))"
(* note that terminates_time_order_IMP imposes only an upper bound on the running time, even though it could really by exact *)

definition "least_constant frgt crgt f =
  HOL_Nat_To_IMP.least_constant_IMP (com_from_crgt crgt f) (T_f_from_frgt frgt f o lookup_args crgt f)"

definition "list_least_constant frgt crgt gs = max_list0 (map (least_constant frgt crgt) gs)"

(* lemma "list_least_constant frgt crgt (map fst hT) \<le> ... max of all constants occuring in term " *)

lemma rel_trace_times:
  assumes "rel_trace_calls crgt hT cT"
  assumes "relate_rgt_time frgt crgt (map fst hT)"
  shows "\<exists>z. IMP_Tailcall_Traces.interp_trace 0 cT z \<and>
             z \<le> list_least_constant frgt crgt (map fst hT) * HOL_TCN_Timing.interp_trace frgt 0 hT"
proof-
  from assms(1) have "length hT = length cT" unfolding rel_trace_calls_def by simp
  then show ?thesis
  using assms proof (induction rule: list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons hg hT cg cT)
    let ?gr = "fst hg" and ?gargs = "snd hg"
    let ?gcom = "fst cg" and ?gs = "snd cg"

    from Cons have rel1: "rel_trace_call crgt ?gr ?gargs ?gcom ?gs"
      unfolding rel_trace_calls_def by auto

    let ?T_f = "T_f_from_frgt frgt ?gr o lookup_args crgt ?gr"
    let ?c1 = "HOL_Nat_To_IMP.least_constant_IMP ?gcom ?T_f"

    have "?gr \<in> set (map fst (hg # hT))" by simp
    with Cons.prems(2) rel1 have
      "terminates_time_order_IMP (com_from_crgt crgt ?gr) ?T_f"
      unfolding relate_rgt_time_def by blast
    then have
      "\<exists>t. HOL_Nat_To_IMP.terminates_with_time_IMP (com_from_crgt crgt ?gr) ?gs t
            (HOL_Nat_To_IMP.least_constant_IMP (com_from_crgt crgt ?gr) ?T_f * ?T_f ?gs)"
      using HOL_Nat_To_IMP.obtain_least_bound unfolding terminates_time_order_IMP_def by blast
    then obtain t where
      "HOL_Nat_To_IMP.terminates_with_time_IMP ?gcom ?gs t (?c1 * T_f_from_frgt frgt ?gr ?gargs)"
      using rel1 unfolding rel_trace_call_def by auto
    then obtain z1 where z1:
        "(?gcom, ?gs) \<Rightarrow>\<^bsup> z1 \<^esup> t" "z1 \<le> ?c1 * T_f_from_frgt frgt ?gr ?gargs"
      by (meson HOL_Nat_To_IMP.terminates_with_time_IMPE)

    then have interp1: "IMP_Tailcall_Traces.interp_trace 0 [(?gcom, ?gs)] z1"
      using IMP_Tailcall_Traces.interp_trace_singleton' by blast

    let ?c2 = "list_least_constant frgt crgt (map fst hT)"

    from Cons obtain z2
      where interp2: "IMP_Tailcall_Traces.interp_trace 0 cT z2"
        and z2: "z2 \<le> ?c2 * HOL_TCN_Timing.interp_trace frgt 0 hT"
      unfolding rel_trace_calls_def relate_rgt_time_def by auto

    let ?c = "list_least_constant frgt crgt (map fst (hg # hT))"
    have "?c = max (least_constant frgt crgt ?gr) ?c2"
      unfolding list_least_constant_def
      using max_list0_cons by simp
    also have "... = max ?c1 ?c2"
      using rel1 unfolding rel_trace_call_def least_constant_def by simp
    finally have c_as_max: "?c = max ?c1 ?c2" .

    show ?case
    proof (rule exI, rule conjI)
      from interp1 interp2 show "IMP_Tailcall_Traces.interp_trace 0 (cg # cT) (z1 + z2)"
        using IMP_Tailcall_Traces.interp_trace_append by fastforce
    next
      (* have "?c1 \<le> list_least_constant frgt crgt (map fst (hg # hT)) *)
      have "z1 + z2 \<le> ?c1 * T_f_from_frgt frgt ?gr ?gargs + ?c2 * HOL_TCN_Timing.interp_trace frgt 0 hT" using z1 z2 by simp
      also have "... \<le> ?c1 * T_f_from_frgt frgt ?gr ?gargs + ?c * HOL_TCN_Timing.interp_trace frgt 0 hT" using c_as_max by simp
      also have "... \<le> ?c * T_f_from_frgt frgt ?gr ?gargs + ?c * HOL_TCN_Timing.interp_trace frgt 0 hT" using c_as_max by simp
      also have "... = ?c * (T_f_from_frgt frgt ?gr ?gargs + HOL_TCN_Timing.interp_trace frgt 0 hT)" by algebra
      also have "... = ?c * (HOL_TCN_Timing.interp_trace frgt 0 [hg] + HOL_TCN_Timing.interp_trace frgt 0 hT)"
        using HOL_TCN_Timing.interp_trace_singleton[where n = 0, simplified add_0_left] by (metis split_pairs)
      also have "... = ?c * HOL_TCN_Timing.interp_trace frgt 0 ([hg] @ hT)"
        using HOL_TCN_Timing.interp_trace_append[of _ 0 0, simplified add_0_right] by presburger
      finally show "z1 + z2 \<le> list_least_constant frgt crgt (map fst (hg # hT)) * HOL_TCN_Timing.interp_trace frgt 0 (hg # hT)" by simp
    qed
  qed
qed



term HOL_TCN_Timing.interp_trace
term IMP_Tailcall_Traces.interp_trace

(* lemma "\<exists>c. \<forall>s. tstruct_k t_imp + something \<le> c * interp_time frgt (time_to_tail frgt vs_b vs_arg t)" oops *)
(* in fact, we can calculate c as the max of the structural-constant-factor and all T_f_const-ants or so *)

end
