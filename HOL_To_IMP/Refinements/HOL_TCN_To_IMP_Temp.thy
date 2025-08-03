theory HOL_TCN_To_IMP_Temp
  imports HOL_To_IMP_Primitives "IMP.HOL_TCN_To_IMP" (* HOL_Nat_To_IMP.Compile_HOL_Nat_To_IMP *)
(* TODO: rearrange import of stuff from Compile *)
begin

method repeat methods m = (m; repeat \<open>m\<close>)?

(*
  (* assumes inf: "\<exists>zh v. (f,frgt) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup>zh\<^esup> v" *)

(* definition "interp_time1 frgt g vs_arg_g = T_f_from_reg frgt g vs_arg_g" *)
(* definition "interp_time frgt = sum_map (\<lambda>(g, vs_arg_g). interp_time1 frgt g vs_arg_g)" *)
  (* assumes "f_imp = to_imp_tc_1 f_args crgt r0 f" *)
  (* assumes "set (special_regs f_args crgt r t) \<subseteq> set stale" *)

abbreviation "lookups names (s :: state) \<equiv> map s names"

definition "is_call_in t f = (f \<in> set (calls t))"

lemma lookups_eq_on: assumes "s = t on set xs" shows "lookups xs s = lookups xs t"
  using assms by (simp add: eq_on_def)

abbreviation "lookup_args crgt g \<equiv> lookups (args_from_crgt crgt g)"

definition "tinterp_time frgt crgt =
  sum_map
    (\<lambda>(g, vs_arg_g).
      HOL_Nat_To_IMP.least_constant_IMP (com_from_crgt crgt g) (T_f_from_reg frgt g o lookup_args crgt g)
      * interp_time1 frgt g vs_arg_g)"

*)

abbreviation "lookups names (s :: state) \<equiv> map s names"
abbreviation "lookup_args crgt g \<equiv> lookups (args_from_crgt crgt g)"

(* definition "is_call_in t f = (f \<in> set (calls t))" *)

(* the term is tail-recursive, "special" registers are marked stale,
   and the argument list of f and of any called functions is distinct *)
definition "compiler_args_invar f_args crgt bs stale t \<longleftrightarrow>
  HOL_TCN_Timing.invar t
  \<and> set (reserved_regs f_args crgt bs t) \<subseteq> set stale
  \<and> distinct f_args
  \<and> (\<forall>(g,_) \<in> set (calls t). distinct (args_from_crgt crgt g))
  \<and> (\<forall>(g,ts) \<in> set (calls t). length ts = length (args_from_crgt crgt g))"

(* the "state" of the HOL-TCN execution (args, bounds) is related
   to the state of the IMP-TC execution *)
definition "relate_exec_state f_args bs vs_arg vs_b s \<longleftrightarrow>
  lookups f_args s = vs_arg \<and> lookups bs s = vs_b"

definition "called_correctness crgt frgt fs \<longleftrightarrow> (\<forall>f \<in> fs.
    HOL_Nat_To_IMP.terminates_with_res_time_order_IMP
      (com_from_crgt crgt f) (ret_from_crgt crgt f)
      (f_from_frgt frgt f o lookup_args crgt f) (T_f_from_frgt frgt f o lookup_args crgt f))" (* can we replace ...  with existential ? *)

definition "relate_rgt_correctness frgt crgt fs \<longleftrightarrow> (\<forall>f \<in> fs.
  \<forall>s. terminates_with_res_IMP (com_from_crgt crgt f) s (ret_from_crgt crgt f)
        (f_from_frgt frgt f (lookup_args crgt f s)))"


(* note: lookups xs s = map s xs *)
lemma map_eq_on_subset_eq: fixes A assumes "set xs \<subseteq> A" "f = g on A" shows "map f xs = map g xs"
  using assms unfolding eq_on_def by (induction xs) auto

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

  
(* 
lemma snoc_list_induct3 [case_names len1 len2 Nil snoc]:
  assumes "length ys = length xs"
  assumes "length zs = length xs"
  assumes nil: "P [] [] []"
  assumes cons: "\<And>xs x ys y zs z. length ys = length xs \<Longrightarrow> length zs = length xs \<Longrightarrow> P xs ys zs \<Longrightarrow> P (xs @ [x]) (ys @ [y]) (zs @ [z])"
  shows "P xs ys zs"
using assms(1,2) proof (induction "rev xs" arbitrary: xs ys zs)
  case (Cons a as')
  then have "xs \<noteq> []" "ys \<noteq> []" "zs \<noteq> []" by auto
  then obtain x xs' y ys' z zs' where "xs = xs' @ [x]" "ys = ys' @ [y]" "zs = zs' @ [z]" using snoc_obtain by metis
  then moreover have "length ys' = length xs'" "length zs' = length xs'" using Cons by simp_all
  ultimately show ?case using Cons cons by simp
qed (simp add: nil) *)

(*
lemma mapi_ix1:
  assumes "length ys = length xs"
  shows "map (\<lambda>i. f ((ys @ zs) ! i) i) [0..<length xs] = map (\<lambda>i. f (ys ! i) i) [0..<length xs]"
  apply simp apply (subst nth_append) using assms apply simp done

lemma mapi_ix2:
  assumes "length ys = length xs"
  assumes "zs \<noteq> []"
  shows "(\<lambda>i. f ((ys @ zs) ! i) i) (length xs) = f (hd zs) (length xs)"
  apply (subst nth_append) using assms hd_conv_nth by fastforce *)

(* lemma nth_append1:
  assumes "n < length xs"
  shows "(xs @ ys) ! n = xs ! n"
  using assms nth_append by metis *)

lemma nth_append_length_eq:
  assumes "length xs = length ys"
  shows "(xs @ y # zs) ! (length ys) = y"
  apply (subst nth_append) using assms by simp

lemma copy_list_sem:
  assumes "length xs = length ys"
  assumes "distinct (xs @ ys)" (* technically, this assumption could be weakened *)
  obtains s' where
    "f \<turnstile> (t_seqs' (map (\<lambda>i. (ys ! i) ::= A (V (xs ! i))) [0..<length xs]),s) \<Rightarrow>\<^bsup>Suc (2 * length xs)\<^esup> s'"
    "lookups xs s = lookups ys s'" "s = s' on (- set ys)"
using assms proof (induction xs ys arbitrary: thesis rule: snoc_list_induct2)
  case Nil
  then show ?case using tSkip_tE by auto
next
  case (snoc xs x ys y)

  let ?cs = "\<lambda>xs ys. map (\<lambda>i. (ys ! i) ::= A (V (xs ! i)) :: tcom) [0..<length xs]"

  let ?cs1 = "?cs xs ys"
  let ?c2 = "y ::= A (V x) :: tcom"
  let ?cs' = "?cs (xs @ [x]) (ys @ [y])"

  have cs': "?cs' = ?cs1 @ [?c2]" by (simp add: snoc nth_append_left nth_append_length_eq)

  from snoc obtain s2 where ih:
      "f \<turnstile> (t_seqs' ?cs1, s) \<Rightarrow>\<^bsup>Suc (2 * length xs)\<^esup> s2"
      "lookups xs s = lookups ys s2" "s = s2 on (- set ys)"
    by auto
  moreover obtain s3 where step:
      "f \<turnstile> (?c2, s2) \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> s3"
      "s3 y = s2 x" "s2 = s3 on (- {y})"
    by fastforce
  ultimately have "f \<turnstile> (t_seqs' ?cs1;; ?c2, s) \<Rightarrow>\<^bsup>Suc (2 * length (xs @ [x]))\<^esup> s3" by auto
  then have "f \<turnstile> (t_seqs' (?cs1 @ [?c2]), s) \<Rightarrow>\<^bsup>Suc (2 * length (xs @ [x]))\<^esup> s3" 
    using t_seqs'_snoc t_seqs'_t_seqs by simp
  then have 1: "f \<turnstile> (t_seqs' ?cs', s) \<Rightarrow>\<^bsup>Suc (2 * length (xs @ [x]))\<^esup> s3"
    by (subst cs') assumption

  have 2: "lookups (xs @ [x]) s = lookups (ys @ [y]) s3"
    using ih step snoc by auto

  have 3: "s = s3 on (- set (ys @ [y]))"
    using ih step by auto

  from 1 2 3 snoc show ?case by blast
qed (simp add: assms)



lemma cc_call_helper:
  "f \<turnstile> (t_seqs' cs1;; t_seqs' cs2;; c, s) \<Rightarrow>\<^bsup>Suc (Suc z)\<^esup> t \<longleftrightarrow> f \<turnstile> (t_seqs (cs1 @ cs2) c, s) \<Rightarrow>\<^bsup>z\<^esup> t"
  using tbig_step_t_t_seqs_rewrite by simp

abbreviation "calls_r t \<equiv> set (map fst (calls t))"

lemma compiler_correct_nt:
  assumes "\<not> tails t"
  assumes "(f,frgt) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup>z\<^esup> v"
  assumes "compiler_args_invar f_args crgt bs stale t"
  assumes "relate_rgt_correctness frgt crgt (calls_r t)"
  assumes "relate_exec_state f_args bs vs_arg vs_b s"
  shows "\<exists>z_c s'.
    f_c \<turnstile> (to_imp_tc f_args crgt bs r stale t,s) \<Rightarrow>\<^bsup>z_c\<^esup> s'
    \<and> s' r = v
    \<and> s = s' on set stale - {r}"
using assms proof (induction t arbitrary: vs_b z v bs stale s r crgt)
  case (hLet t1 t2)

  let ?r1 = "fresh' stale ''Let.x''"

  have no_tails: "\<not> HOL_TCN_Timing.tails t1" "\<not> HOL_TCN_Timing.tails t2" using hLet by simp_all

  obtain z1 v1 z2 where inv: "z = z1 + z2" "(f, frgt) \<turnstile> (t1, vs_b, vs_arg) \<Rightarrow>\<^bsup>z1\<^esup>  v1" "(f, frgt) \<turnstile> (t2, v1 # vs_b, vs_arg) \<Rightarrow>\<^bsup>z2\<^esup>  v"
    using hLet_case hLet.prems by blast

  have args_invar: "compiler_args_invar f_args crgt bs stale t1" "compiler_args_invar f_args crgt (?r1 # bs) (?r1 # stale) t2"
    using hLet unfolding compiler_args_invar_def reserved_regs_def split_beta by auto

  have rel_rgt: "relate_rgt_correctness frgt crgt (calls_r t1)" "relate_rgt_correctness frgt crgt (calls_r t2)"
    using hLet unfolding relate_rgt_correctness_def by auto

  have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" using hLet by blast

  obtain z1_c s2 where
    ih1: "f_c \<turnstile> (to_imp_tc f_args crgt bs ?r1 stale t1, s) \<Rightarrow>\<^bsup>z1_c\<^esup>  s2" "s2 ?r1 = v1" "s = s2 on set stale - {?r1}"
    using no_tails inv args_invar rel_rgt rel_state1 hLet by metis

  have res_reg_subset: "set f_args \<subseteq> set stale - {?r1}" "set bs \<subseteq> set stale - {?r1}"
    using hLet.prems(3) fresh_not_in_stale unfolding compiler_args_invar_def reserved_regs_def by simp_all

  have rel_state2: "relate_exec_state f_args (?r1 # bs) vs_arg (v1 # vs_b) s2"
    using hLet ih1 unfolding relate_exec_state_def apply simp
    unfolding map_eq_on_subset_eq[OF res_reg_subset(1)] map_eq_on_subset_eq[OF res_reg_subset(2)] by blast

  obtain z2_c s3 where
    ih2: "f_c \<turnstile> (to_imp_tc f_args crgt (?r1 # bs) r (?r1 # stale) t2, s2) \<Rightarrow>\<^bsup>z2_c\<^esup>  s3" "s3 r = v" "s2 = s3 on set (?r1 # stale) - {r}"
    using hLet.IH(2)[OF no_tails(2) inv(3) args_invar(2) rel_rgt(2) rel_state2] by blast

  have "s = s2 on set stale - {r}" using ih1 fresh_not_in_stale eq_on_subset by blast
  moreover have "s2 = s3 on set stale - {r}" using ih2 fresh_not_in_stale by auto
  ultimately have s3_like_s: "s = s3 on set stale - {r}" by blast

  show ?case
    apply (simp add: Let_def)
    apply (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    apply (rule tbig_step_t.tSeq)
    using ih1 ih2 s3_like_s by auto
next
  case (hLetBound n)
  show ?case
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    from hLetBound_case hLetBound have "v = vs_b ! n" "n < length vs_b" by auto
    then have "aval (A (V (bs ! n))) s = v" using hLetBound unfolding relate_exec_state_def by auto
    then show "f_c \<turnstile> (to_imp_tc f_args crgt bs r stale (hLetBound n), s) \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> s(r := v)"
      by (metis tbig_step_t.tAssign to_imp_tc.simps(3))
  qed (simp_all add: eq_on_def)
next
  case (hArg n)
  show ?case
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    from hArg_case hArg have "v = vs_arg ! n" "n < length vs_arg" by auto
    then have "aval (A (V (f_args ! n))) s = v" using hArg unfolding relate_exec_state_def by auto
    then show "f_c \<turnstile> (to_imp_tc f_args crgt bs r stale (hArg n), s) \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> s(r := v)"
      by (metis tbig_step_t.tAssign to_imp_tc.simps(4))
  qed (simp_all add: eq_on_def)
next
  case (hNumber n)
  show ?case
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    have "aval (A (N n)) s = v" using hNumber unfolding relate_exec_state_def by auto
    then show "f_c \<turnstile> (to_imp_tc f_args crgt bs r stale (hNumber n), s) \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> s(r := v)"
      by (metis tbig_step_t.tAssign to_imp_tc.simps(5))
  qed (simp_all add: eq_on_def)
next
  case (hIf t1 t2 t3)

  let ?r1 = "fresh' stale ''If.x''"

  have no_tails: "\<not> HOL_TCN_Timing.tails t1" "\<not> HOL_TCN_Timing.tails t2" "\<not> HOL_TCN_Timing.tails t3" using hIf by simp_all

  have args_invar: "compiler_args_invar f_args crgt bs stale t1" "compiler_args_invar f_args crgt bs stale t2" "compiler_args_invar f_args crgt bs stale t3"
    using hIf unfolding compiler_args_invar_def reserved_regs_def split_beta by auto

  have rel_rgt: "relate_rgt_correctness frgt crgt (calls_r t1)" "relate_rgt_correctness frgt crgt (calls_r t2)" "relate_rgt_correctness frgt crgt (calls_r t3)"
    using hIf unfolding relate_rgt_correctness_def by auto

  have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" using hIf by blast

  have res_reg_subset: "set f_args \<subseteq> set stale - {?r1}" "set bs \<subseteq> set stale - {?r1}"
    using hIf.prems(3) fresh_not_in_stale unfolding compiler_args_invar_def reserved_regs_def by simp_all

  show ?case
  proof (cases rule: hIf_case[OF hIf.prems(2)])
    case (1 z1 v1 z2)

    obtain z1_c s2 where
      ih1: "f_c \<turnstile> (to_imp_tc f_args crgt bs ?r1 stale t1, s) \<Rightarrow>\<^bsup>z1_c\<^esup>  s2" "s2 ?r1 = v1" "s = s2 on set stale - {?r1}"
      using no_tails 1 args_invar rel_rgt rel_state1 hIf by metis

    have rel_state2: "relate_exec_state f_args bs vs_arg vs_b s2"
      using hIf ih1 unfolding relate_exec_state_def apply simp
      unfolding map_eq_on_subset_eq[OF res_reg_subset(1)] map_eq_on_subset_eq[OF res_reg_subset(2)] by blast

    obtain z2_c s3 where
      ih2: "f_c \<turnstile> (to_imp_tc f_args crgt bs r stale t2, s2) \<Rightarrow>\<^bsup>z2_c\<^esup>  s3" "s3 r = v" "s2 = s3 on set stale - {r}"
      using no_tails 1 args_invar rel_rgt rel_state2 hIf by metis

    have "s = s2 on set stale - {r}" using ih1 fresh_not_in_stale eq_on_subset by blast
    moreover have "s2 = s3 on set stale - {r}" using ih2 fresh_not_in_stale by auto
    ultimately have s3_like_s: "s = s3 on set stale - {r}" by blast

    show ?thesis apply (simp add: Let_def) apply (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
        apply (rule tbig_step_t.tSeq) using ih1 apply blast apply (rule tbig_step_t.tIfTrue) using ih1 1 apply simp using ih2 apply simp apply simp apply simp
        using ih2 apply simp using s3_like_s by auto
  next
    case (2 z1 z2)

    obtain z1_c s2 where
      ih1: "f_c \<turnstile> (to_imp_tc f_args crgt bs ?r1 stale t1, s) \<Rightarrow>\<^bsup>z1_c\<^esup>  s2" "s2 ?r1 = 0" "s = s2 on set stale - {?r1}"
      using no_tails 2 args_invar rel_rgt rel_state1 hIf by metis

    have rel_state2: "relate_exec_state f_args bs vs_arg vs_b s2"
      using hIf ih1 unfolding relate_exec_state_def apply simp
      unfolding map_eq_on_subset_eq[OF res_reg_subset(1)] map_eq_on_subset_eq[OF res_reg_subset(2)] by blast

    obtain z2_c s3 where
      ih2: "f_c \<turnstile> (to_imp_tc f_args crgt bs r stale t3, s2) \<Rightarrow>\<^bsup>z2_c\<^esup>  s3" "s3 r = v" "s2 = s3 on set stale - {r}"
      using no_tails 2 args_invar rel_rgt rel_state2 hIf by metis

    have "s = s2 on set stale - {r}" using ih1 fresh_not_in_stale eq_on_subset by blast
    moreover have "s2 = s3 on set stale - {r}" using ih2 fresh_not_in_stale by auto
    ultimately have s3_like_s: "s = s3 on set stale - {r}" by blast

    show ?thesis apply (simp add: Let_def) apply (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
        apply (rule tbig_step_t.tSeq) using ih1 apply blast apply (rule tbig_step_t.tIfFalse) using ih1 2 apply simp using ih2 apply simp apply simp apply simp
        using ih2 apply simp using s3_like_s by auto
  qed
next
  case (hCall gr ts)

  obtain g T_g zs vs where
          z: "z = sum_list zs + T_g vs"
      and gr: "(g, T_g) = frgt gr"
      and lengths: "length zs = length ts" "length vs = length ts"
      and args_bigstep: "\<forall>i<length ts. (f, frgt) \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>zs ! i\<^esup> vs ! i"
      and gvs: "g vs = v"
    using hCall_case hCall by blast


  let ?xs = "make_n_fresh stale ''Call.x.'' (length ts)"
  let ?c1_gen = "\<lambda>crgt st. t_seqs' (map (\<lambda>i. to_imp_tc f_args crgt bs (?xs ! i) st (ts ! i)) [0..<length ts])"
  let ?crgt_gen = "crgt(gr := (take (length ts) (args_from_crgt crgt gr), com_from_crgt crgt gr, ret_from_crgt crgt gr))"
  let ?c1 = "?c1_gen crgt (?xs @ stale)"
  let ?c2 = "t_seqs' (map (\<lambda>i. (args_from_crgt crgt gr ! i) ::= A (V (?xs ! i))) [0..<length ts])"
  let ?c3 = "CALL com_from_crgt crgt gr RETURN ret_from_crgt crgt gr :: tcom"
  let ?c4 = "r ::= A (V (ret_from_crgt crgt gr)) :: tcom"

  (* let ?compiler_args_invar_weak = "\<lambda>f_args crgt bs stale t. *)
        (* HOL_TCN_Timing.invar t *)
        (* \<and> set (reserved_regs f_args crgt bs t) \<subseteq> set stale *)
        (* \<and> distinct f_args *)
        (* \<and> (\<forall>(g,_) \<in> set (calls t). distinct (args_from_crgt crgt g))" *)
  (* from hCall(4) *)
  (* have args_invar': "?compiler_args_invar_weak f_args crgt bs stale (hCall gr ts)" *)
    (* unfolding compiler_args_invar_def by simp *)
  have "\<exists>z1 s2. f_c \<turnstile> (?c1_gen crgt st,s) \<Rightarrow>\<^bsup>z1\<^esup> s2 \<and> lookups ?xs s2 = vs \<and> s = s2 on set stale"
    if "set (?xs @ stale) \<subseteq> set st" "length ts = length (args_from_crgt crgt gr)" for st
  using hCall(1,2,4,5,6) that args_bigstep proof (induction ts zs vs arbitrary: z v st crgt gr rule: snoc_list_induct3)
    case Nil then show ?case unfolding make_n_fresh_def by auto
  next
    case (snoc ts_arg t_arg zs0 z0 vs0 v0)

    let ?xs = "make_n_fresh stale ''Call.x.'' (length ts_arg)"
    let ?xs' = "make_n_fresh stale ''Call.x.'' (length (ts_arg @ [t_arg]))"
    let ?x = "make_nth_fresh stale ''Call.x.'' (length ts_arg)"
    have xs': "?xs' = ?xs @ [?x]" unfolding make_n_fresh_def using nth_map_upt by simp
    have x: "?xs' ! length ts_arg = ?x" unfolding xs' unfolding make_n_fresh_def by (subst nth_append) simp

    let ?gr' = "fresh' (map fst (calls (hCall gr ts_arg))) ''g''"
    (* let ?crgt = "crgt(?gr' := (take (length ts_arg) (args_from_crgt crgt gr), com_from_crgt crgt gr, ret_from_crgt crgt gr))" *)
    let ?c1 = "t_seqs' (map (\<lambda>i. to_imp_tc f_args crgt bs (?xs ! i) st (ts_arg ! i)) [0..<length ts_arg])"
    let ?c2 = "to_imp_tc f_args crgt bs ?x st t_arg"
    term ?c1
    (* have "set (calls (hCall gr ts_arg)) \<subseteq> set (calls (hCall gr (ts_arg @ [t_arg])))" *)
      (* apply (induction ts_arg) apply auto *)
    thm snoc
    thm snoc.IH
    have "\<exists>z1 s2. f_c \<turnstile> (?c1, s) \<Rightarrow>\<^bsup>z1\<^esup>  s2 \<and> lookups ?xs s2 = vs0 \<and> s = s2 on set stale"
      apply (rule snoc.IH[where gr = gr]) (* ?gr' *)
      subgoal using snoc.prems(1) by simp
      subgoal using snoc.prems(2) by simp
      subgoal
        unfolding compiler_args_invar_def apply (repeat \<open>rule conjI\<close>)
        subgoal using snoc.prems(3) unfolding compiler_args_invar_def by simp
        subgoal using snoc.prems(3) unfolding compiler_args_invar_def reserved_regs_def thm set_take_subset apply simp done
        subgoal using snoc.prems(3) unfolding compiler_args_invar_def by simp
        subgoal using snoc.prems(3) unfolding compiler_args_invar_def by fastforce
        subgoal using snoc.prems(3,7) unfolding compiler_args_invar_def apply (simp add: split_beta) sorry
        done
(* set (calls (hCall gr ts_arg) *)
      subgoal using snoc.prems(4) unfolding relate_rgt_correctness_def by auto
      subgoal using snoc.prems(5) by blast
      subgoal using snoc.prems(6) unfolding make_n_fresh_def by fastforce
      subgoal using snoc.prems(7) (* by (metis le_eq_less_or_eq le_imp_less_Suc length_append_singleton nth_append_left snoc.hyps(1,2)) *)
        sorry
      subgoal sorry
      done
    then obtain z1 s2 where ih1: "f_c \<turnstile> (?c1, s) \<Rightarrow>\<^bsup>z1\<^esup> s2" "lookups ?xs s2 = vs0" "s = s2 on set stale"
      by blast


    have t_arg_in_args: "t_arg \<in> set (ts_arg @ [t_arg])" by simp

    have no_tails: "\<not> HOL_TCN_Timing.tails t_arg"
      using that snoc.prems by auto

    have calls_subset: "set (calls t_arg) \<subseteq> set (calls (hCall gr (ts_arg @ [t_arg])))"
      using snoc.prems by auto

    have args_invar: "compiler_args_invar f_args crgt bs st t_arg"
    unfolding compiler_args_invar_def proof (repeat \<open>rule conjI\<close>)
      show "HOL_TCN_Timing.invar t_arg" using no_tails_invar no_tails that by blast
    next
      have "set (reserved_regs f_args crgt bs t_arg) \<subseteq> set (reserved_regs f_args crgt bs (hCall gr (ts_arg @ [t_arg])))"
        unfolding reserved_regs_def using calls_subset that by fastforce
      then show "set (reserved_regs f_args crgt bs t_arg) \<subseteq> set st"
        using snoc.prems unfolding compiler_args_invar_def by auto
    next
      show "distinct f_args" using hCall compiler_args_invar_def by simp
    next
      show "\<forall>(g,_)\<in>set (calls t_arg). distinct (args_from_crgt crgt g)"
        using snoc.prems calls_subset that unfolding compiler_args_invar_def split_beta by blast
    next
      show "\<forall>(g, ts)\<in>set (calls t_arg). length ts = length (args_from_crgt crgt g)"
        using snoc.prems calls_subset that unfolding compiler_args_invar_def split_beta by blast
    qed

    have rel_rgt: "relate_rgt_correctness frgt crgt (calls_r t_arg)"
      using snoc.prems unfolding relate_rgt_correctness_def by auto

    have exec_t_arg: "(f, frgt) \<turnstile> (t_arg, vs_b, vs_arg) \<Rightarrow>\<^bsup>z0\<^esup> v0" using snoc.prems
      by (metis length_append_singleton lessI nth_append_length
          snoc.hyps(1,2))

    have "set f_args \<subseteq> set stale" "set bs \<subseteq> set stale"
      using snoc.prems unfolding compiler_args_invar_def reserved_regs_def by simp_all
    then have rel_state: "relate_exec_state f_args bs vs_arg vs_b s2" using snoc.prems(5) ih1
      unfolding relate_exec_state_def using eq_on_subset by fastforce

    obtain z2 s3 where texec_t_arg:
        "f_c \<turnstile> (to_imp_tc f_args crgt bs ?x st t_arg, s2) \<Rightarrow>\<^bsup>z2\<^esup>  s3"
        "s3 ?x = v0"
        "s2 = s3 on set st - {?x}"
      using snoc.prems t_arg_in_args no_tails exec_t_arg args_invar rel_rgt rel_state by metis
    
    show ?case proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
      have "?x \<notin> set ?xs"
        apply (subst sym[OF none_equal_not_in])
        using make_n_fresh_def inj_on_contraD[OF inj_make_nth_fresh] by simp (* this should not be so hard... *)
      then have "set ?xs \<subseteq> set (?xs' @ stale) - {?x}" using xs' fresh_not_in_stale unfolding make_nth_fresh_def by simp
      also have "... \<subseteq> set st - {?x}" using snoc.prems by blast
      finally show "lookups ?xs' s3 = vs0 @ [v0]"
        using xs' ih1 texec_t_arg by fastforce
    next
      show "s = s3 on set stale"
        using ih1 texec_t_arg fresh_not_in_stale make_nth_fresh_def snoc.prems(6) by fastforce
    next
      have 1: "map (\<lambda>i. to_imp_tc f_args crgt bs (?xs' ! i) st ((ts_arg @ [t_arg]) ! i)) [0..<length (ts_arg @ [t_arg])]
        = map (\<lambda>i. to_imp_tc f_args crgt bs (?xs ! i) st (ts_arg ! i)) [0..<length ts_arg] @ [?c2]"
        using xs' x unfolding make_n_fresh_def apply simp apply (subst nth_append)+ by simp

      thm t_seqs'_append
      have "f_c \<turnstile> (?c1;; ?c2,s) \<Rightarrow>\<^bsup>z1 + z2\<^esup> s3" using ih1 texec_t_arg tbig_step_t.tSeq by blast
      then have "f_c \<turnstile> (t_seqs' (map (\<lambda>i. to_imp_tc f_args crgt bs (?xs ! i) st (ts_arg ! i)) [0..<length ts_arg] @ [?c2]),s) \<Rightarrow>\<^bsup>z1 + z2\<^esup>  s3"
        apply (subst t_seqs'_append[symmetric]) apply (subst (2) t_seqs_def) apply simp apply (subst tbig_step_t_tSeq_assoc) using tbig_step_t.tSeq by fastforce
      with 1 show "f_c \<turnstile> (t_seqs' (map (\<lambda>i. to_imp_tc f_args crgt bs (?xs' ! i) st ((ts_arg @ [t_arg]) ! i)) [0..<length (ts_arg @ [t_arg])]),s) \<Rightarrow>\<^bsup>z1 + z2\<^esup>  s3"
        by metis
    qed
  qed (simp_all add: lengths)

  moreover have lll: "length ts = length (args_from_crgt crgt gr)"
    using hCall.prems unfolding compiler_args_invar_def by simp
  ultimately obtain z1 s2 where exec_c1: "f_c \<turnstile> (?c1,s) \<Rightarrow>\<^bsup>z1\<^esup> s2" and "lookups ?xs s2 = vs" and s2: "s = s2 on set stale"
    using hCall.prems unfolding compiler_args_invar_def by blast


  (* part 2: copying from temporaries to argument registers *)

  have lll2: "length ?xs = length (args_from_crgt crgt gr)"
    using lll unfolding make_n_fresh_def by simp

  have "set (args_from_crgt crgt gr) \<subseteq> set stale"
    using hCall.prems unfolding compiler_args_invar_def reserved_regs_def by simp
  then have ddd: "distinct (?xs @ args_from_crgt crgt gr)"
    apply simp using hCall.prems make_n_fresh_not_in_stale unfolding compiler_args_invar_def apply simp
    apply (rule Int_emptyI) by blast

  thm copy_list_sem
  thm copy_list_sem[where s = s2 and f = f_c and xs = ?xs and ys = "args_from_crgt crgt gr", OF lll2 ddd]

  obtain s3 where "f_c \<turnstile> (t_seqs'
               (map (\<lambda>i. (args_from_crgt crgt gr ! i) ::= A (V (make_n_fresh stale ''Call.x.'' (length ts) ! i)))
                 [0..<length (make_n_fresh stale ''Call.x.'' (length ts))]),
              s2) \<Rightarrow>\<^bsup>Suc (2 * length (make_n_fresh stale ''Call.x.'' (length ts)))\<^esup>  s3"
      "lookups ?xs s2 = lookup_args crgt gr s3 " and s3: "s2 = s3 on - set (args_from_crgt crgt gr)"
    using copy_list_sem[OF lll2 ddd] by blast
  then obtain z2 where exec_c2: "f_c \<turnstile> (?c2, s2) \<Rightarrow>\<^bsup>z2\<^esup> s3"
    unfolding make_n_fresh_def by simp


  (* part 3: calling g *)

  let ?gcom = "com_from_crgt crgt gr" and ?gret = "ret_from_crgt crgt gr" and ?gv = "f_from_frgt frgt gr (lookup_args crgt gr s3)"
  have "terminates_with_res_IMP ?gcom s3 ?gret ?gv" using hCall.prems unfolding relate_rgt_correctness_def by simp
  then obtain z3 s4c where "(?gcom, s3) \<Rightarrow>\<^bsup>z3\<^esup> s4c" "s4c ?gret = ?gv"
    unfolding terminates_with_res_IMP_def terminates_with_res_pred_time_IMP_def terminates_with_pred_time_IMP_def by blast
  then obtain s4 where exec_c3: "f_c \<turnstile> (?c3, s3) \<Rightarrow>\<^bsup>z3\<^esup> s4" and s4: "s4 = s3(?gret := ?gv)" using tbig_step_t.tCall by fastforce

  have vfrom: "v = f_from_frgt frgt gr (lookup_args crgt gr s3)"
    by (metis \<open>(g, T_g) = frgt gr\<close> \<open>g vs = v\<close> \<open>lookups ?xs s2 = lookup_args crgt gr s3\<close>
        \<open>lookups ?xs s2 = vs\<close> fst_conv) (* TODO clean *)


  (* part 4: copying to r *)

  term ?c4
  let ?s5 = "s4(r := aval (A (V ?gret)) s4)"
  obtain z4 where exec_c4: "f_c \<turnstile> (?c4, s4) \<Rightarrow>\<^bsup>z4\<^esup> ?s5" by blast
  then have s5: "?s5 = s4(r := v)" using vfrom s4 by simp


  (* putting it together *)

  have "f_c \<turnstile> (?c1;; ?c2;; ?c3;; ?c4, s) \<Rightarrow>\<^bsup>z1 + z2 + z3 + z4\<^esup> ?s5"
    using exec_c1 exec_c2 exec_c3 exec_c4 by blast

  have "?s5 r = v" using s5 by simp

  have "s = s2 on set stale" using s2 .
  have "set stale \<subseteq> - set (args_from_crgt crgt gr)"
    using hCall.prems unfolding compiler_args_invar_def reserved_regs_def 
(* not equal on all of stale! have to fix lemma *) sorry
  have "s2 = s3 on set stale" using s3 using hCall.prems unfolding compiler_args_invar_def reserved_regs_def 
  have "s = ?s5 on set stale - {r}" using s2 s3 s4 s5 apply simp
  

  thm hCall_case[OF hCall.prems(2)]
  have ?case
  apply (simp only: to_imp_tc.simps Let_def split_beta mapi_map cc_call_helper[symmetric])
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    apply (subst sym[OF cc_call_helper]) sorry



  have tsi_in_ts: "ts ! i \<in> set ts" if "i < length ts" for i using that by simp
  (* have 8: "P (ts ! i)" if "i < length ts" "\<forall>t\<in>set ts. P t" for P i using that by auto *)

  have no_tails: "\<not> HOL_TCN_Timing.tails (ts ! i)" if "i < length ts" for i using hCall that by auto

  have calls_subset: "set (calls (ts ! i)) \<subseteq> set (calls (hCall gr ts))" if "i < length ts" for i using hCall tsi_in_ts that by fastforce

  have args_invar: "compiler_args_invar f_args crgt bs stale (ts ! i)" if "i < length ts" for i
  unfolding compiler_args_invar_def proof (repeat \<open>rule conjI\<close>)
    show "HOL_TCN_Timing.invar (ts ! i)" using no_tails_invar no_tails that by blast
  next
    have "set (reserved_regs f_args crgt bs (ts ! i)) \<subseteq> set (reserved_regs f_args crgt bs (hCall gr ts))"
      unfolding reserved_regs_def using calls_subset that by fastforce
    then show "set (reserved_regs f_args crgt bs (ts ! i)) \<subseteq> set stale"
      using hCall unfolding compiler_args_invar_def by auto
  next
    show "distinct f_args" using hCall compiler_args_invar_def by simp
  next
    show "\<forall>g\<in>set (calls (ts ! i)). distinct (args_from_crgt crgt g)"
      using hCall calls_subset that unfolding compiler_args_invar_def by blast
  qed

  
(* 
  have no_tails: "\<not> HOL_TCN_Timing.tails (ts ! i)"
    and args_invar: "compiler_args_invar f_args crgt bs stale (ts ! i)"
    (* and "set (calls (ts ! i)) \<subseteq> set (calls (hCall gr ts))" *)
    if "i < length ts" for i
    (* using hCall tsi_in_ts that by auto *)
  proof (goal_cases)
    case 1 then show ?case using hCall tsi_in_ts that by auto
  next
    case 2
    then show ?case sorry
  qed
    show "\<not> HOL_TCN_Timing.tails (ts ! i)"
    (* have tsi_in_ts: "ts ! i \<in> set ts" using that by simp *)
    

  have "set (calls (ts ! i)) \<subseteq> set (calls (hCall gr ts))" if "i < length ts" for i using hCall tsi_in_ts that by fastforce
  then have args_invar: "compiler_args_invar f_args crgt bs stale (ts ! i)" if "i < length ts" for i
    using hCall tsi_in_ts that unfolding compiler_args_invar_def reserved_regs_def apply simp

  show ?case
    apply (simp add: Let_def split_beta mapi_map del: One_nat_def) *)
    
    sorry (* TODO :< *)
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
  fixes t_imp f_args crgt frgt bs r stale t vs_b vs_arg
  defines "t_imp \<equiv> to_imp_tc f_args crgt bs r stale t"
  assumes "t_time \<equiv> time_to_tail frgt vs_b vs_arg t"
  assumes "well_formed_comp f_args crgt bs stale t"
  assumes "well_encoded_comp f_args bs vs_arg vs_b s"
  (* assumes "called_correctness crgt frgt t" *)
  shows "\<exists>k Cs.
    (\<exists>t l. tto_end s t_imp k Cs t l)
    \<and> length Cs = length t_time
    \<and> (\<forall>((C,s), (g,vs_arg_g)) \<in> set (zip Cs t_time).
          C = com_from_crgt crgt g \<and> vs_arg_g = lookup_args crgt g s)"
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
  let ?cs1 = "mapi (\<lambda>i t. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ stale) t) ts"
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
  assumes compiler_correct_nt_: True
  assumes "t_imp = to_imp_tc f_args crgt bs r stale t"
  assumes "well_formed_comp f_args crgt bs stale t"
  assumes "well_encoded_comp f_args bs vs_arg vs_b s"
  assumes "called_correctness crgt frgt t"
  shows "\<exists>k z.
    ttime_to_tail s t_imp (k + z)
    \<and> k \<le> tstruct_k t_imp
    \<and> z \<le> tinterp_time frgt crgt (time_to_tail frgt vs_b vs_arg t)"
using assms(2-5) proof (induction t arbitrary: t_imp bs r stale vs_b s)
  case (hLet t1 t2)
  thm hLet.prems(1)[simplified]
  thm hLet.IH(1) hLet.IH(2)

  thm hLet.prems

  let ?x_var = "fresh' stale ''Let.x''"
  let ?t_imp1 = "to_imp_tc f_args crgt bs ?x_var stale t1"

  have wf1: "well_formed_comp f_args crgt bs stale t1" using hLet.prems(2)
    unfolding well_formed_comp_def using non_tail_tailrec apply auto apply (simp only: reserved_regs_def h_calls.simps map_append)
    by auto
  then obtain k1 z1 where k1z1:
      "ttime_to_tail s ?t_imp1 (k1 + z1)"
      "k1 \<le> tstruct_k ?t_imp1"
      "z1 \<le> tinterp_time frgt crgt (time_to_tail frgt vs_b vs_arg t1)"
    using hLet.IH(1)[where t_imp = ?t_imp1 and s = s and bs = bs and vs_b = vs_b and r = ?x_var and stale = stale] hLet.prems
    unfolding called_correctness_def by auto

  have ob1: "non_tail t1" using hLet unfolding well_formed_comp_def by simp
  have ob2: "well_encoded_comp f_args bs vs_arg vs_b s" using hLet by simp
  obtain f y1 s1
      where t1s1: "f \<turnstile> (?t_imp1,s) \<Rightarrow>\<^bsup>y1\<^esup> s1"
      and s1_xvar: "s1 ?x_var = eval_non_tail frgt vs_b vs_arg t1"
      and s1: "s = s1 on (Set.remove ?x_var (set stale))"
    using compiler_correct_nt[OF ob1 wf1 ob2, simplified] by blast

  have "tailrec t1" using well_formed_comp_def wf1 by blast
  then have inv: "invar ?t_imp1" using to_imp_invar by blast
  have y1: "y1 = k1 + z1" using ttime_non_tail[OF inv t1s1] sorry (* ttime_to_tail for non-tail MUST INVESTIGATE AND WRITE LEMMA *)

  let ?t_imp2 = "to_imp_tc f_args crgt (?x_var # bs) r (?x_var # stale) t2"
  have "tailrec t2" using hLet unfolding well_formed_comp_def by simp

  have t2_1: "well_formed_comp f_args crgt (?x_var # bs) (?x_var # stale) t2"
    using hLet.prems(2) unfolding well_formed_comp_def apply auto sorry (* almost sub-term *)
  have "set f_args \<subseteq> Set.remove ?x_var (set stale)" using fresh_not_in_stale
    unfolding remove_def apply simp using hLet.prems(2) unfolding well_formed_comp_def reserved_regs_def by simp
  then have t2_2_1: "lookups f_args s1 = vs_arg"
    apply (subst lookups_eq_on[where s = s, symmetric])
    using s1 apply blast using hLet.prems(3) unfolding well_encoded_comp_def by blast
  have "set bs \<subseteq> Set.remove ?x_var (set stale)" using fresh_not_in_stale
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
      and vs_b = "eval_non_tail frgt vs_b vs_arg t1 # vs_b" and stale = "?x_var # stale", OF _ t2_1 t2_2 t2_3, simplified]
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
