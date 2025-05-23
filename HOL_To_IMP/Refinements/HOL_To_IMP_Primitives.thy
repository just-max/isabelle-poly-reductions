\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Primitives
  imports
    "HOL_Nat_To_IMP.HOL_Nat_To_IMP_Tactics"
    "HOL-Data_Structures.Define_Time_Function"
    "ML_Unification.Unify_Assumption_Tactic"
begin

context HOL_To_HOL_Nat
begin

declare transport_eq_id.partial_equivalence_rel_equivalenceI[per_intro del]
and transport_eq_restrict_id.partial_equivalence_rel_equivalence[per_intro del]

paragraph \<open>Numerals\<close>

text \<open>Natural number numerals are directly mapped to IMP constans and hence must not be compiled.\<close>
lemma Rel_nat_numeral [Rel_nat]: "((=) ===> Rel_nat) (numeral :: _ \<Rightarrow> nat) (numeral :: _ \<Rightarrow> nat)"
  unfolding Rel_nat_nat_eq_eq by auto

paragraph \<open>Equality\<close>

definition "eq_nat (n :: nat) m \<equiv> if (n - m) + (m - n) = 0 then True_nat else False_nat"

lemma eq_nat_eq_False_nat_iff [HOL_To_IMP_finish_simps]: "eq_nat x y = False_nat \<longleftrightarrow> x \<noteq> y"
 unfolding eq_nat_def by (auto simp: True_nat_ne_False_nat)

lemma Rel_nat_eq_nat [Rel_nat]: "(Rel_nat ===> Rel_nat ===> Rel_nat) eq_nat (=)"
proof (intro rel_funI)
  fix x x' and y y' :: 'a
  assume "Rel_nat x y" "Rel_nat x' y'"
  then show "Rel_nat (eq_nat x x') (y = y')"
  by (cases "y = y'") (auto simp: Rel_nat_iff_eq_natify compile_nat_type_def.Rep_inject eq_nat_def
    natify_True_eq natify_False_eq)
qed

end

context HOL_Nat_To_IMP
begin

(*remove simplification rules interfering with refinement proofs*)
declare neq0_conv[iff del, symmetric, iff] Nat.One_nat_def[simp del]
and de_Morgan_disj[simp del] de_Morgan_conj[simp del] not_imp[simp del] disj_not1[simp del]

unbundle tcom_syntax

context includes com_syntax and no com'_syntax and no tcom_syntax
begin

definition [compiled_IMP_const_def]:
  "eq_IMP \<equiv>
    ''eq.x_Sub_y'' ::= (V ''eq.arg.x'' \<ominus> V ''eq.arg.y'');;
    ''eq.y_Sub_x'' ::= (V ''eq.arg.y'' \<ominus> V ''eq.arg.x'');;
    ''eq.neq'' ::= (V ''eq.x_Sub_y'' \<oplus> V ''eq.y_Sub_x'');;
    IF ''eq.neq'' \<noteq>0
    THEN ''eq.ret'' ::= A (N False_nat)
    ELSE ''eq.ret'' ::= A (N True_nat)"

end

declare_compiled_const HTHN.eq_nat
  return_register "eq.ret"
  argument_registers "eq.arg.x" "eq.arg.y"
  compiled eq_IMP

declare_compiled_const HOL.eq
  return_register "eq.ret"
  argument_registers "eq.arg.x" "eq.arg.y"
  compiled eq_IMP

HOL_To_IMP_correct HTHN.eq_nat
  unfolding eq_IMP_def HTHN.eq_nat_def
  by (fastforce intro: terminates_with_res_IMPI terminates_with_IMPI)

end

paragraph \<open>Addition and Subtraction\<close>

context HOL_To_HOL_Nat
begin

lemma Rel_nat_add [Rel_nat]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) (+) ((+) :: nat \<Rightarrow> _)"
  by (auto simp: Rel_nat_nat_eq_eq)

lemma Rel_nat_sub [Rel_nat]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) (-) ((-) :: nat \<Rightarrow> _)"
  by (auto simp: Rel_nat_nat_eq_eq)

end

context HOL_Nat_To_IMP
begin

context includes com_syntax and no com'_syntax and no tcom_syntax
begin

definition [compiled_IMP_const_def]:
  "add_IMP \<equiv> ''add.ret'' ::= (V ''add.arg.x'' \<oplus> V ''add.arg.y'')"
definition [compiled_IMP_const_def]:
  "sub_IMP \<equiv> ''sub.ret'' ::= (V ''sub.arg.x'' \<ominus> V ''sub.arg.y'')"

end

declare_compiled_const "Groups.plus"
  return_register "add.ret"
  argument_registers "add.arg.x" "add.arg.y"
  compiled "add_IMP"

declare_compiled_const "Groups.minus"
  return_register "sub.ret"
  argument_registers "sub.arg.x" "sub.arg.y"
  compiled "sub_IMP"

HOL_To_IMP_correct Groups.plus
  unfolding add_IMP_def
  by (fastforce intro: terminates_with_res_IMPI terminates_with_IMPI)
HOL_To_IMP_correct Groups.minus
  unfolding sub_IMP_def
  by (fastforce intro: terminates_with_res_IMPI terminates_with_IMPI)

end





context HOL_Nat_To_IMP
begin

definition bounded_by :: "nat \<Rightarrow> nat \<Rightarrow> bool" where "bounded_by u \<equiv> (\<lambda>t. t \<le> u)"
lemma bounded_byI[intro]: assumes "t \<le> u" shows "bounded_by u t" using assms unfolding bounded_by_def .
lemma bounded_byE[elim]: assumes "bounded_by u t" shows "t \<le> u" using assms unfolding bounded_by_def .

definition constant_time :: "state \<Rightarrow> nat" where "constant_time \<equiv> (\<lambda>_. 1)"
lemma constant_time1: "constant_time s = 1" unfolding constant_time_def by simp

definition linear_time_in :: "vname \<Rightarrow> state \<Rightarrow> nat" where "linear_time_in x \<equiv> (\<lambda>s. s x)"

(* TODO: tcom \<rightarrow> com step as in correctness proof *)

definition "terminates_with_time_IMP_Tailcall tp p s s' t \<equiv>
  terminates_with_pred_time_IMP_Tailcall tp p s s' (bounded_by t)"

definition "terminates_with_time_IMP p s s' t \<equiv>
  terminates_with_pred_time_IMP p s s' (bounded_by t)"

definition "terminates_with_res_time_IMP_Tailcall tp p s r val t \<equiv>
  terminates_with_res_pred_time_IMP_Tailcall tp p s r val (bounded_by t)"

definition "terminates_with_res_time_IMP p s r val t \<equiv>
  terminates_with_res_pred_time_IMP p s r val (bounded_by t)"

(* _time: ((=) t); _bound_time: \exists c. \forall s. \exists t. ... (t) \and t \<le> c * T_f *)

(* TODO: probably only care about IMP, not IMP_Tailcall ? *)
definition "terminates_with_res_bound_time_IMP_Tailcall tp p r f T_f \<equiv>
  \<exists>c. \<forall>s. terminates_with_res_time_IMP_Tailcall tp p s r (f s) (c * T_f s)"

definition "terminates_with_res_bound_time_IMP p r f T_f \<equiv>
  \<exists>c. \<forall>s. terminates_with_res_time_IMP p s r (f s) (c * T_f s)"

definition "terminates_with_bound_time_IMP p s_p T_f \<equiv>
  \<exists>c. \<forall>s. terminates_with_time_IMP p s (s_p s) (c * T_f s)"

definition "least_bound_time_IMP p T_f \<equiv>
  (LEAST c. \<forall>s. \<exists>s'. terminates_with_time_IMP p s s' (c * T_f s))"

definition "least_bound_time_IMP_res p r f T_f \<equiv>
  (LEAST c. \<forall>s. terminates_with_res_time_IMP p s r (f s) (c * T_f s))"

(* TODO: we may need to add a predicate on states where they are hidden inside a definition *)

(* it might be "nicer" to write these in terms of terminates_with_pred_time_IMP_TailcallI/E,
    but the resulting higher-order unification seems to trip up the automation *)
lemma terminates_with_time_IMP_TailcallI:
  assumes "tp \<turnstile> (p, s) \<Rightarrow>\<^bsup>t'\<^esup> s'"
  assumes "t' \<le> t"
  shows "terminates_with_time_IMP_Tailcall tp p s s' t"
  using assms terminates_with_pred_time_IMP_TailcallI bounded_byI
  unfolding terminates_with_time_IMP_Tailcall_def
  by fastforce

lemma terminates_with_time_IMP_TailcallE:
  assumes "terminates_with_time_IMP_Tailcall tp p s s' t"
  obtains t' where "tp \<turnstile> (p, s) \<Rightarrow>\<^bsup>t'\<^esup> s'" "t' \<le> t"
  using assms terminates_with_pred_time_IMP_TailcallE bounded_byE
  unfolding terminates_with_time_IMP_Tailcall_def
  by metis

lemma terminates_with_time_IMPI:
  assumes "(p, s) \<Rightarrow>\<^bsup>t'\<^esup> s'"
  assumes "t' \<le> t"
  shows "terminates_with_time_IMP p s s' t"
  using assms terminates_with_pred_time_IMPI bounded_byI
  unfolding terminates_with_time_IMP_def
  by fastforce

lemma terminates_with_time_IMPE:
  assumes "terminates_with_time_IMP p s s' t"
  obtains t' where "(p, s) \<Rightarrow>\<^bsup>t'\<^esup> s'" "t' \<le> t"
  using assms terminates_with_pred_time_IMPE bounded_byE
  unfolding terminates_with_time_IMP_def
  by metis

lemma terminates_with_res_time_IMP_TailcallI:
  assumes "tp \<turnstile> (p, s) \<Rightarrow>\<^bsup>t'\<^esup> s'"
  assumes "s' r = val"
  assumes "t' \<le> t"
  shows "terminates_with_res_time_IMP_Tailcall tp p s r val t"
  using assms terminates_with_res_pred_time_IMP_TailcallI terminates_with_pred_time_IMP_TailcallI
  unfolding terminates_with_res_time_IMP_Tailcall_def
  by (meson bounded_by_def) (* TODO *)

lemma terminates_with_res_time_IMP_TailcallE:
  assumes "terminates_with_res_time_IMP_Tailcall tp p s r val t"
  obtains s' t' where "tp \<turnstile> (p, s) \<Rightarrow>\<^bsup>t'\<^esup> s'" "s' r = val" "t' \<le> t"
  using assms terminates_with_res_pred_time_IMP_TailcallE terminates_with_pred_time_IMP_TailcallE
  unfolding terminates_with_res_time_IMP_Tailcall_def
  by (metis bounded_by_def)

lemma terminates_with_res_time_IMPI:
  assumes "(p, s) \<Rightarrow>\<^bsup>t'\<^esup> s'"
  assumes "s' r = val"
  assumes "t' \<le> t"
  shows "terminates_with_res_time_IMP p s r val t"
  using assms terminates_with_res_pred_time_IMPI terminates_with_pred_time_IMPI bounded_byI
  unfolding terminates_with_res_time_IMP_def
  by fastforce

lemma terminates_with_res_time_IMPE:
  assumes "terminates_with_res_time_IMP p s r val t"
  obtains s' t' where "(p, s) \<Rightarrow>\<^bsup>t'\<^esup> s'" "s' r = val" "t' \<le> t"
  using assms terminates_with_res_pred_time_IMPE terminates_with_pred_time_IMPE bounded_byE
  unfolding terminates_with_res_time_IMP_def
  by metis

lemma terminates_with_res_bound_time_IMP_TailcallI:
  assumes "\<exists>c. \<forall>s. terminates_with_res_time_IMP_Tailcall tp p s r (val s) (c * t s)"
  shows "terminates_with_res_bound_time_IMP_Tailcall tp p r val t"
  unfolding terminates_with_res_bound_time_IMP_Tailcall_def using assms by blast

lemma terminates_with_res_bound_time_IMP_TailcallE:
  assumes "terminates_with_res_bound_time_IMP_Tailcall tp p r val t"
  obtains c where "\<And>s. terminates_with_res_time_IMP_Tailcall tp p s r (val s) (c * t s)"
  using assms unfolding terminates_with_res_bound_time_IMP_Tailcall_def by blast

lemma terminates_with_res_bound_time_IMPI:
  assumes "\<exists>c. \<forall>s. terminates_with_res_time_IMP p s r (val s) (c * t s)"
  shows "terminates_with_res_bound_time_IMP p r val t"
  unfolding terminates_with_res_bound_time_IMP_def using assms by blast

lemma terminates_with_res_bound_time_IMPE:
  assumes "terminates_with_res_bound_time_IMP p r val t"
  obtains c where "\<And>s. terminates_with_res_time_IMP p s r (val s) (c * t s)"
  using assms unfolding terminates_with_res_bound_time_IMP_def by blast

lemma terminates_with_bound_time_IMPI:
  assumes "\<exists>c. \<forall>s. terminates_with_time_IMP p s (s_p s) (c * t s)"
  shows "terminates_with_bound_time_IMP p s_p t"
  unfolding terminates_with_bound_time_IMP_def using assms by blast

lemma terminates_with_bound_time_IMPE:
  assumes "terminates_with_bound_time_IMP p s_p t"
  obtains c where "\<And>s. terminates_with_time_IMP p s (s_p s) (c * t s)"
  using assms unfolding terminates_with_bound_time_IMP_def by blast


lemmas terminates_with_intros =
  terminates_with_pred_time_IMP_TailcallI
  terminates_with_res_pred_time_IMP_TailcallI
  terminates_with_time_IMP_TailcallI
  terminates_with_res_time_IMP_TailcallI
  terminates_with_res_bound_time_IMP_TailcallI

  terminates_with_pred_time_IMPI
  terminates_with_res_pred_time_IMPI
  terminates_with_time_IMPI
  terminates_with_res_time_IMPI
  terminates_with_bound_time_IMPI
  terminates_with_res_bound_time_IMPI

lemmas terminates_with_elims =
  terminates_with_pred_time_IMP_TailcallE
  terminates_with_res_pred_time_IMP_TailcallE
  terminates_with_time_IMP_TailcallE
  terminates_with_res_time_IMP_TailcallE
  terminates_with_res_bound_time_IMP_TailcallE

  terminates_with_pred_time_IMPE
  terminates_with_res_pred_time_IMPE
  terminates_with_time_IMPE
  terminates_with_res_time_IMPE
  terminates_with_bound_time_IMPE
  terminates_with_res_bound_time_IMPE

context
  notes terminates_with_intros[intro] terminates_with_elims[elim]
begin

lemma terminates_with_res_time_IMP_Tailcall_bound: (* monotonicity *)
  assumes "t \<le> u"
  assumes "terminates_with_res_time_IMP_Tailcall tp p s r val t"
  shows "terminates_with_res_time_IMP_Tailcall tp p s r val u"
  using assms by fastforce

lemma terminates_with_res_time_IMP_bound:
  assumes "t \<le> u"
  assumes "terminates_with_res_time_IMP p s r val t"
  shows "terminates_with_res_time_IMP p s r val u"
  using assms by fastforce


lemma bound_fix_state:
  assumes "terminates_with_res_bound_time_IMP p r f T_f"
  shows "\<And>s. \<exists>c. terminates_with_res_time_IMP p s r (f s) (c * T_f s)"
  using assms by blast

lemma terminates_with_time_res_equiv:
  "terminates_with_res_time_IMP p s r val t \<equiv>
    \<exists>s'. terminates_with_time_IMP p s s' t \<and> s' r = val"
  by (rule eq_reflection, rule iffI; blast)

lemma terminates_with_res_to_terminates_with_bound_time:
  assumes "terminates_with_res_bound_time_IMP p r f T_f"
  shows "\<exists>s_p. terminates_with_bound_time_IMP p s_p T_f \<and> (\<forall>s. s_p s r = f s)"
proof-
  from assms have "\<exists>c. \<forall>s. \<exists>s'. terminates_with_time_IMP p s s' (c * T_f s) \<and> s' r = f s" by fastforce
  then have "\<exists>s_p. \<exists>c. \<forall>s. terminates_with_time_IMP p s (s_p s) (c * T_f s) \<and> s_p s r = f s" using choice by fast
  then show "\<exists>s_p. terminates_with_bound_time_IMP p s_p T_f \<and> (\<forall>s. s_p s r = f s)" by blast
  (* note these last two are equivalent, and the former could perhaps be useful, but the latter is "cleaner" *)
qed

(* not used *)
lemma terminates_with_to_terminates_with_res_bound_time:
  assumes "terminates_with_bound_time_IMP p s_p T_f"
  shows "terminates_with_res_bound_time_IMP p r (\<lambda>s. s_p s r) T_f"
  using assms by fastforce


lemma obtain_least_bound:
  assumes has_res_bound: "terminates_with_bound_time_IMP p s' t"
  shows "terminates_with_time_IMP p s (s' s) (least_bound_time_IMP p t * t s)"
  using assms
  by (smt (verit, ccfv_threshold) LeastI_ex big_step_t_determ2 least_bound_time_IMP_def
      terminates_with_bound_time_IMP_def terminates_with_time_IMPE) (* tidy *)

lemma obtain_least_bound_res_1:
  assumes has_res_bound: "terminates_with_res_bound_time_IMP p r f T_f"
  shows "terminates_with_res_time_IMP p s r (f s) (least_bound_time_IMP_res p r f T_f * T_f s)"
  using assms
  by (smt (verit) least_bound_time_IMP_res_def terminates_with_res_bound_time_IMP_def
      wellorder_Least_lemma(1)) (* tidy *)

lemma obtain_least_bound_res_2:
  assumes "terminates_with_res_bound_time_IMP p r f T_f"
  shows "terminates_with_res_time_IMP p s r (f s) (least_bound_time_IMP p T_f * T_f s)"
proof-
  from assms have "\<exists>s_p. terminates_with_bound_time_IMP p s_p T_f \<and> (\<forall>s. s_p s r = f s)"
    using terminates_with_res_to_terminates_with_bound_time by blast
  then have "\<exists>s_p. terminates_with_time_IMP p s (s_p s) (least_bound_time_IMP p T_f * T_f s) \<and> s_p s r = f s"
    using obtain_least_bound by blast
  then show "terminates_with_res_time_IMP p s r (f s) (least_bound_time_IMP p T_f * T_f s)"
    using terminates_with_time_res_equiv by blast
qed


lemma terminates_with_time_tSeqI:
  assumes "terminates_with_time_IMP_Tailcall tp p1 s s' t1"
  assumes "terminates_with_time_IMP_Tailcall tp p2 s' s'' t2"
  shows "terminates_with_time_IMP_Tailcall tp (tSeq p1 p2) s s'' (t1 + t2)"
  using assms by fastforce

lemma terminates_with_time_tAssignI:
  assumes "s' = s(k := aval aexp s)"
  shows "terminates_with_time_IMP_Tailcall p (tAssign k aexp) s s' 2"
  using assms by fastforce

(* TODO: do we need a non-res version?? \<rightarrow> if so, fix *)
lemma terminates_with_time_tIfI:
  assumes "cond \<Longrightarrow> terminates_with_time_IMP_Tailcall p p1 s1 s1' t1"
  assumes "cond \<Longrightarrow> s1 = s"
  assumes "\<not>cond \<Longrightarrow> terminates_with_time_IMP_Tailcall p p2 s2 s2' t2"
  assumes "\<not>cond \<Longrightarrow> s2 = s"
  assumes "s' = (if cond then s1' else s2')"
  assumes "t \<ge> (if cond then t1 else t2) + 1"
  assumes "cond = (s vb \<noteq> 0)"
  shows "terminates_with_time_IMP_Tailcall p (tIf vb p1 p2) s s' t"
  using assms by fastforce

lemma terminates_with_res_time_IMPI_bound:
  assumes "terminates_with_res_bound_time_IMP p r f T_f"
  shows "terminates_with_res_time_IMP p s r (f s) (least_bound_time_IMP p T_f * T_f s)"
  using obtain_least_bound_res_2[OF assms(1), where s = s] using assms by fastforce
  (* note this is just obtain_least_bound_res_2, but we abstract it here *)

lemma terminates_with_time_tCallI:
  assumes "s' = s(r := val)"
  assumes "terminates_with_res_time_IMP p s r val t"
  shows "terminates_with_time_IMP_Tailcall tp (tCall p r) s s' t"
  using assms by fastforce

lemma terminates_with_time_tTailI:
  assumes "terminates_with_time_IMP_Tailcall tp tp s s' t"
  shows "terminates_with_time_IMP_Tailcall tp tTAIL s s' (t + 5)"
  using assms by fastforce

lemma terminates_with_res_time_tSeqI:
  assumes "terminates_with_time_IMP_Tailcall tp p1 s s' t1"
  assumes "terminates_with_res_time_IMP_Tailcall tp p2 s' r val t2"
  shows "terminates_with_res_time_IMP_Tailcall tp (tSeq p1 p2) s r val (t1 + t2)"
  using assms by fastforce

lemma terminates_with_res_time_tIfI:
  assumes "cond \<Longrightarrow> s1 = s" (* do we really need these s_i = s assumptions ? *)
  assumes "cond \<Longrightarrow> terminates_with_res_time_IMP_Tailcall p p1 s1 r val t1"
  assumes "\<not>cond \<Longrightarrow> s2 = s"
  assumes "\<not>cond \<Longrightarrow> terminates_with_res_time_IMP_Tailcall p p2 s2 r val t2"
  assumes "cond \<Longrightarrow> t \<ge> t1 + 1"
  assumes "\<not>cond \<Longrightarrow> t \<ge> t2 + 1"
  assumes "cond = (s vb \<noteq> 0)"
  shows "terminates_with_res_time_IMP_Tailcall p (tIf vb p1 p2) s r val t"
  using assms by fastforce

lemma terminates_with_res_time_treturnI:
  assumes "aval a s = val"
  shows "terminates_with_res_time_IMP_Tailcall p (tAssign r a) s r val 2"
  using assms by fastforce

lemma terminates_with_res_time_tTailI:
  assumes "terminates_with_res_time_IMP_Tailcall tp tp s r val t"
  shows "terminates_with_res_time_IMP_Tailcall tp tTAIL s r val (t + 5)"
  using assms by fastforce

end

(* this stuff is just here for now for proving correctness/timing for IMP primitives *)

lemma big_step_ifI:
  assumes "s b \<noteq> 0 \<Longrightarrow> (c1,s) \<Rightarrow>\<^bsup> x1 \<^esup> t1"
  assumes "s b = 0 \<Longrightarrow> (c2,s) \<Rightarrow>\<^bsup> x2 \<^esup> t2"
  assumes "t = (if s b \<noteq> 0 then t1 else t2)"
  assumes "y = (if s b \<noteq> 0 then x1 else x2) + 1"
  shows "(com.If b c1 c2,s) \<Rightarrow>\<^bsup> y \<^esup> t"
  using assms big_step_t.intros(4,5) by simp

method repeat methods m = (m; repeat \<open>m\<close>)?
lemmas big_stepI = big_step_t.Skip big_step_t.Assign big_step_t.Seq big_step_ifI
method big_step_time = rule big_stepI
method big_step_unfold_time = repeat \<open>big_step_time\<close>

(* example: schematic goal to materialize the constant *)
schematic_goal add_IMP_twrt: "terminates_with_res_time_IMP add_IMP s ''add.ret'' (s ''add.arg.x'' + s ''add.arg.y'') ?t"
  apply (rule terminates_with_res_time_IMPI)
    apply (subst add_IMP_def)
    apply (rule big_step_t.Assign)
   apply auto
  done

lemma add_IMP_twrbt:
  "terminates_with_res_bound_time_IMP add_IMP ''add.ret''
    (\<lambda>s. s ''add.arg.x'' + s ''add.arg.y'') constant_time"
  (* apply (rule terminates_with_res_bound_time_IMPI, rule exI, rule allI, rule terminates_with_res_time_IMP_bound) *)
  apply (rule terminates_with_res_bound_time_IMPI)
  apply (rule exI, rule allI)
  apply (rule terminates_with_res_time_IMP_bound[OF _ add_IMP_twrt])
  unfolding constant_time_def apply auto
  done

lemma sub_IMP_twrbt:
  "terminates_with_res_bound_time_IMP sub_IMP ''sub.ret''
    (\<lambda>s. s ''sub.arg.x'' - s ''sub.arg.y'') constant_time"
  apply (rule terminates_with_res_bound_time_IMPI, rule exI, rule allI)
  apply (rule terminates_with_res_time_IMPI)
    apply (subst sub_IMP_def)
    apply (big_step_unfold_time; simp)
  apply simp
  apply (auto simp add: constant_time_def)
  done

(* TODO: remove *)
schematic_goal eq_IMP_twrt:
  "terminates_with_res_time_IMP eq_IMP s ''eq.ret''
  (HTHN.eq_nat (s ''eq.arg.x'') (s ''eq.arg.y'')) ?t"
  apply (rule terminates_with_res_time_IMPI)
    apply (subst eq_IMP_def)
    apply (big_step_unfold_time; simp)
  apply (simp add: HTHN.eq_nat_def)
  apply (auto simp add: constant_time_def)
  done

lemma eq_IMP_twrbt:
  "terminates_with_res_bound_time_IMP eq_IMP ''eq.ret''
    (\<lambda>s. HTHN.eq_nat (s ''eq.arg.x'') (s ''eq.arg.y'')) constant_time"
  apply (rule terminates_with_res_bound_time_IMPI, rule exI, rule allI)
  apply (rule terminates_with_res_time_IMPI)
    apply (subst eq_IMP_def)
    apply (big_step_unfold_time; simp)
  apply (simp add: HTHN.eq_nat_def)
  apply (auto simp add: constant_time_def)
  done


lemma start_time:
  assumes "s0 = s"
  assumes "terminates_with_time_IMP_Tailcall tp p s0 s' t"
  shows "terminates_with_time_IMP_Tailcall tp p s s' t"
  using assms by blast

method start_time uses f_def =
  subst (2) f_def, subst start_time

method cond_false = rule not_TrueE FalseE, assumption

lemma simps_to_eq_r: assumes "PROP SIMPS_TO y y'" "x = y'" shows "x = y"
  using SIMPS_TOD[OF assms(1)] assms(2) by simp

lemma flip_xsrD: assumes "x = s r" shows "s r = x" using assms by blast

lemma start_case:
  assumes "p \<equiv> e"
  assumes "terminates_with_res_time_IMP_Tailcall p e s r val t'"
  assumes "t' \<le> t"
  shows "terminates_with_res_time_IMP_Tailcall p p s r val t"
  using assms terminates_with_res_time_IMP_Tailcall_bound by blast

method start_case uses IMP_def =
   drule flip_xsrD, (* flip "x = s r" assumptions *)
   rule start_case[OF IMP_def] (* avoid flex-flex pair with explicit rule instead of subst *)

method terminates_with_res_time_seq_assign =
  rule terminates_with_res_time_tSeqI, rule terminates_with_time_tAssignI[OF refl]

method terminates_with_res_time_seq_call uses f_thm =
  rule terminates_with_res_time_tSeqI,
  rule terminates_with_time_tCallI[OF refl],
  rule terminates_with_res_time_IMPI_bound,
  rule f_thm

method terminates_with_res_time_if = rule terminates_with_res_time_tIfI[OF refl _ refl _]

lemma simps_to_case_end:
  assumes "PROP SIMPS_TO s s'"
  assumes "PROP SIMPS_TO v v'"
  assumes "terminates_with_res_time_IMP_Tailcall tp p s' r v' t"
  shows "terminates_with_res_time_IMP_Tailcall tp p s r v t"
  using SIMPS_TOD[OF assms(1)] SIMPS_TOD[OF assms(2)] assms(3) by simp

lemma pick:
  assumes "t \<le> u"
  shows "t \<le> u"
  using assms .


fun bar :: "nat \<Rightarrow> nat" where
  "bar 0 = 0" |
  "bar (Suc n) = bar n"
declare bar.simps[simp del]
time_fun bar

case_of_simps bar_eq_case : bar.simps
lemmas bar_eq = bar_eq_case[unfolded case_nat_eq_if]
compile_nat bar_eq

lemma bar_IMP_Tailcall_ih:
  assumes "(\<And>s. y = s ''bar.arg.xa'' \<Longrightarrow>
                terminates_with_res_time_IMP_Tailcall bar_IMP_tailcall bar_IMP_tailcall s ''bar.ret'' (bar (s ''bar.arg.xa''))
                 (c * T_bar (s ''bar.arg.xa'')))"
  shows "y = (v(''eq.arg.x'' := Suc y, ''eq.arg.y'' := 0, ''eq.ret'' := 0, ''sub.arg.x'' := Suc y, ''sub.arg.y'' := 1, ''sub.ret'' := y, ''bar.arg.xa'' := y)) ''bar.arg.xa'' \<Longrightarrow>
                terminates_with_res_time_IMP_Tailcall bar_IMP_tailcall bar_IMP_tailcall (v(''eq.arg.x'' := Suc y, ''eq.arg.y'' := 0, ''eq.ret'' := 0, ''sub.arg.x'' := Suc y, ''sub.arg.y'' := 1, ''sub.ret'' := y, ''bar.arg.xa'' := y)) ''bar.ret'' (bar ((v(''eq.arg.x'' := Suc y, ''eq.arg.y'' := 0, ''eq.ret'' := 0, ''sub.arg.x'' := Suc y, ''sub.arg.y'' := 1, ''sub.ret'' := y, ''bar.arg.xa'' := y)) ''bar.arg.xa''))
                 (c * T_bar ((v(''eq.arg.x'' := Suc y, ''eq.arg.y'' := 0, ''eq.ret'' := 0, ''sub.arg.x'' := Suc y, ''sub.arg.y'' := 1, ''sub.ret'' := y, ''bar.arg.xa'' := y)) ''bar.arg.xa''))"
  using assms by blast

schematic_goal bar_IMP_Tailcall_twrt: "
    terminates_with_res_time_IMP_Tailcall bar_IMP_tailcall bar_IMP_tailcall s
      ''bar.ret'' (bar (s ''bar.arg.xa'')) (?c * T_bar (s ''bar.arg.xa''))"

  apply (induction "s ''bar.arg.xa''" arbitrary: s rule: bar.induct) (* what is the induction rule??? *)

  (* base case *)

  apply (start_case IMP_def: bar_IMP_tailcall_def)

    apply terminates_with_res_time_seq_assign
    apply terminates_with_res_time_seq_assign
    apply (terminates_with_res_time_seq_call f_thm: eq_IMP_twrbt)

    apply terminates_with_res_time_if
        apply (rule terminates_with_res_time_treturnI) defer

        apply terminates_with_res_time_seq_assign
        apply terminates_with_res_time_seq_assign
        apply (terminates_with_res_time_seq_call f_thm: sub_IMP_twrbt)
        apply terminates_with_res_time_seq_assign

        apply (rule terminates_with_res_time_tTailI)

        (* simplify condition *)
        prefer 4 apply (rule simps_to_eq_r) apply (simp (no_asm_simp) add: HTHN.eq_nat_def True_nat_def) apply (urule SIMPS_TOI) apply (urule refl)
       (* dismiss opposite conditional branch, this only works when condition is case analysis of function definition *)
       prefer 3 apply cond_false
      prefer 1 apply cond_false

     prefer 4
     apply (simp (no_asm_simp) only:) (* substitute "s r = x" assumptions *)
     apply (simp (no_asm_simp) add: bar.simps) (* solve the equality outright (hopefully) *)

(* induction step *)

    prefer 3
    apply (start_case IMP_def: bar_IMP_tailcall_def)

     apply terminates_with_res_time_seq_assign
     apply terminates_with_res_time_seq_assign
     apply (terminates_with_res_time_seq_call f_thm: eq_IMP_twrbt)

     apply terminates_with_res_time_if
         apply (rule terminates_with_res_time_treturnI) defer

         apply terminates_with_res_time_seq_assign
         apply terminates_with_res_time_seq_assign
         apply (terminates_with_res_time_seq_call f_thm: sub_IMP_twrbt)
         apply terminates_with_res_time_seq_assign

         apply (rule terminates_with_res_time_tTailI)

         (* simplify condition *)
         prefer 4 apply (rule simps_to_eq_r) apply (simp (no_asm_simp) add: HTHN.eq_nat_def False_nat_def) apply (urule SIMPS_TOI) apply (urule refl)
        (* dismiss opposite conditional branch, this only works when condition is case analysis of function definition *)
        prefer 7 apply cond_false
       prefer 2 apply cond_false

      apply (rule simps_to_case_end)

        (* simplify state *)
        apply (simp add: HTHN.eq_nat_def False_nat_def)
        apply (urule SIMPS_TOI)

        (* "run" function *)
        apply (simp (no_asm_simp) only:) (* substitute "s r = x" assumptions *)
       apply (simp (no_asm_simp) add: bar.simps)
       apply (urule SIMPS_TOI)

      apply (drule bar_IMP_Tailcall_ih) (* instantiate IH *)
       apply simp (* solve IH assumption *)
      apply simp (* apply IH *)

  (* now we have two timing constraints per case: one each "up to" the condition, and each "inside" the condition *)

     prefer 3 apply (urule le_refl)
    prefer 1 apply (urule le_refl)
   apply (simp_all add: constant_time1)

  (* what we have here is really just the constraint system:
      16 + C_eq + C_sub + c * T_bar x \<le> c * (T_bar x + 1)
      7  + C_eq \<le> c
     which has a solution c := max (7 + C_eq) (16 + C_eq + C_sub) *)
   prefer 2 apply (rule pick[where u =
        "max
          (7 + least_bound_time_IMP eq_IMP constant_time)
          (16
            + least_bound_time_IMP eq_IMP constant_time
            + least_bound_time_IMP sub_IMP constant_time)"
        ])
(* can isabelle solve this automatically? *)
   apply (auto simp add: algebra_simps)
  done

lemma bar_IMP_Tailcall_twrbt:
  "terminates_with_res_bound_time_IMP_Tailcall bar_IMP_tailcall bar_IMP_tailcall
      ''bar.ret'' (\<lambda>s. bar (s ''bar.arg.xa'')) (\<lambda>s. T_bar (s ''bar.arg.xa''))"
  apply (rule terminates_with_res_bound_time_IMP_TailcallI)
  apply (rule exI)
  apply (rule allI)
  apply (rule bar_IMP_Tailcall_twrt)
  done


HOL_To_IMP_correct bar by cook

end


paragraph \<open>Multiplication\<close>

context HOL_To_HOL_Nat
begin

fun mul_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"mul_acc_nat 0 _ z = z" |
"mul_acc_nat (Suc x) y z = mul_acc_nat x y (y + z)"
declare mul_acc_nat.simps[simp del]

time_fun mul_acc_nat

lemma mul_acc_nat_eq_mul_add: "mul_acc_nat x y z = x * y + z"
  by (induction x y z arbitrary: z rule: mul_acc_nat.induct)
  (auto simp: mul_acc_nat.simps mult_eq_if)

case_of_simps mul_acc_nat_eq : mul_acc_nat.simps
function_compile_nat mul_acc_nat_eq

lemma mul_eq_mul_acc_nat_zero: "x * y = mul_acc_nat x y 0"
  using mul_acc_nat_eq_mul_add by simp

(* TODO: time_fun mul_eq_mul_acc_nat_zero *)

function_compile_nat mul_eq_mul_acc_nat_zero

end

context HOL_Nat_To_IMP
begin

declare case_nat_eq_if[simp]
and case_bool_nat_def[simp]
and Rel_nat_selector_Suc[Rel_nat]

lemmas mul_acc_nat_nat_eq = HTHN.mul_acc_nat_nat_eq_unfolded[unfolded case_nat_eq_if]
compile_nat mul_acc_nat_nat_eq
HOL_To_IMP_correct HTHN.mul_acc_nat_nat by cook






compile_nat HTHN.times_nat_eq_unfolded
HOL_To_IMP_correct HTHN.times_nat by cook

end

paragraph \<open>Boolean Operators\<close>

context HOL_Nat_To_IMP
begin

compile_nat True_nat_def
HOL_To_IMP_correct True_nat by cook

compile_nat False_nat_def
HOL_To_IMP_correct False_nat by cook

end

context HOL_To_HOL_Nat
begin

lemma not_iff_eq_False: "\<not>b \<longleftrightarrow> b = False" by simp

function_compile_nat not_iff_eq_False

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.Not_nat_eq_unfolded
HOL_To_IMP_correct HTHN.Not_nat by cook

end

paragraph \<open>Orders\<close>

context HOL_To_HOL_Nat
begin

lemma max_nat_eq_if: "max (x :: nat) y = (if x - y \<noteq> 0 then x else y)"
  by simp

function_compile_nat max_nat_eq_if

lemma min_nat_eq_if: "min (x :: nat) y = (if x - y \<noteq> 0 then y else x)"
  by simp

function_compile_nat min_nat_eq_if

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.max_nat_eq_unfolded
HOL_To_IMP_correct HTHN.max_nat by cook

compile_nat HTHN.min_nat_eq_unfolded basename min
HOL_To_IMP_correct HTHN.min_nat by cook

end

paragraph \<open>More Boolean Operators\<close>

context HOL_To_HOL_Nat
begin

lemma conj_eq_if_then_else: "b1 \<and> b2 \<longleftrightarrow> (if b1 then if b2 then True else False else False)"
  by auto

function_compile_nat conj_eq_if_then_else

lemma disj_eq_if_then_else: "b1 \<or> b2 \<longleftrightarrow> (if b1 then True else if b2 then True else False)"
  by auto

function_compile_nat disj_eq_if_then_else

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.conj_nat_eq_unfolded
HOL_To_IMP_correct HTHN.conj_nat by cook

compile_nat HTHN.disj_nat_eq_unfolded
HOL_To_IMP_correct HTHN.disj_nat by cook

end

paragraph \<open>More Orders\<close>

context HOL_To_HOL_Nat
begin

lemma le_nat_iff_sub_eq_zero: "(x :: nat) \<le> y \<longleftrightarrow> x - y = 0" by auto

function_compile_nat le_nat_iff_sub_eq_zero

lemma lt_nat_iff_le_and_ne: "(x :: nat) < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y" by auto

function_compile_nat lt_nat_iff_le_and_ne

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.less_eq_nat_eq_unfolded
HOL_To_IMP_correct HTHN.less_eq_nat by cook

compile_nat HTHN.less_nat_eq_unfolded
HOL_To_IMP_correct HTHN.less_nat by cook

end

paragraph \<open>Division\<close>

context HOL_To_HOL_Nat
begin

fun div_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_acc_nat x y z = (if y = 0 then z else if x < y then z else div_acc_nat (x - y) y (z + 1))"
declare div_acc_nat.simps[simp del]

lemma div_acc_nat_eq_div_add: "div_acc_nat x y z = x div y + z"
  by (induction x y z rule: div_acc_nat.induct) (auto simp: div_acc_nat.simps div_if)

function_compile_nat div_acc_nat.simps

lemma div_eq_div_acc_nat_zero: "x div y = div_acc_nat x y 0"
  using div_acc_nat_eq_div_add by simp

function_compile_nat div_eq_div_acc_nat_zero

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.div_acc_nat_nat_eq_unfolded
HOL_To_IMP_correct HTHN.div_acc_nat_nat by cook

compile_nat HTHN.divide_nat_eq_unfolded
HOL_To_IMP_correct HTHN.divide_nat by cook

end

paragraph \<open>Datatype Encoding Functions\<close>

context HOL_Nat_To_IMP
begin

definition [compiled_IMP_const_def]:
  "suc_IMP \<equiv> Com.Assign ''suc.ret'' (V ''suc.arg.x'' \<oplus> N 1)"

declare_compiled_const Suc
  return_register "suc.ret"
  argument_registers "suc.arg.x"
  compiled suc_IMP

HOL_To_IMP_correct Suc unfolding suc_IMP_def
  by (fastforce intro: terminates_with_res_IMPI terminates_with_IMPI)

end

context HOL_To_HOL_Nat
begin

function_compile_nat triangle_def

lemma pair_nat_eq_triangle_add: "pair_nat a b = triangle (a + b) + a"
  unfolding pair_nat_eq prod_encode_def by simp

text \<open>We generate unconditional equations for all functions used in the construction of natural
number datatypes. This way, one can directly compile native nat-datatype functions without
an intermediate transfer step.\<close>

function_compile_nat pair_nat_eq_triangle_add
declare pair_nat_related_transfer[Rel_nat del]

lemma pair_nat_eq_triangle_nat: "pair_nat a b = triangle_nat (a + b) + a"
proof -
  from pair_nat_related_transfer have "pair_nat_nat = pair_nat"
    unfolding Rel_nat_nat_eq_eq by (simp add: rel_fun_eq)
  with Rel_nat_nat_eq_eq pair_nat_nat_eq_unfolded show ?thesis by auto
qed

lemma Rel_nat_pair_nat [Rel_nat]: "(Rel_nat ===> Rel_nat ===> Rel_nat) pair_nat pair_nat"
  unfolding Rel_nat_nat_eq_eq by (simp add: rel_fun_eq)

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.triangle_nat_eq_unfolded
HOL_To_IMP_correct HTHN.triangle_nat by cook

compile_nat HTHN.pair_nat_eq_triangle_nat
HOL_To_IMP_correct pair_nat by cook

end

context HOL_To_HOL_Nat
begin

fun fst_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fst_acc_nat k m = (if m \<le> k then m else fst_acc_nat (Suc k) (m - Suc k))"
fun snd_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "snd_acc_nat k m = (if m \<le> k then k - m else snd_acc_nat (Suc k) (m - Suc k))"
declare fst_acc_nat.simps[simp del] and snd_acc_nat.simps[simp del]

function_compile_nat fst_acc_nat.simps
function_compile_nat snd_acc_nat.simps

lemma app_eq_app_prod_decode_acc_if_eq_if:
  assumes "\<And>k m. f k m = (if m \<le> k then g (m, k - m) else f (Suc k) (m - Suc k))"
  shows "f k m = g (prod_decode_aux k m)"
proof (induction k m rule: prod_decode_aux.induct)
  case (1 k m)
  then show ?case by (cases "m \<le> k") (simp_all add: assms prod_decode_aux.simps)
qed

lemma fst_acc_nat_eq_fst_prod_decode_aux: "fst_acc_nat k m = fst (prod_decode_aux k m)"
  by (fact
    app_eq_app_prod_decode_acc_if_eq_if[where g = fst, unfolded fst_conv, OF fst_acc_nat.simps])

lemma snd_acc_nat_eq_snd_prod_decode_aux: "snd_acc_nat k m = snd (prod_decode_aux k m)"
  by (fact
    app_eq_app_prod_decode_acc_if_eq_if[where g = snd, unfolded snd_conv, OF snd_acc_nat.simps])

lemma fst_nat_eq_fst_acc_nat: "fst_nat m = fst_acc_nat 0 m"
  unfolding fst_nat_eq unpair_nat_eq prod_decode_def
  by (subst fst_acc_nat_eq_fst_prod_decode_aux) simp

lemma snd_nat_eq_snd_acc_nat: "snd_nat m = snd_acc_nat 0 m"
  unfolding snd_nat_eq unpair_nat_eq prod_decode_def
  by (subst snd_acc_nat_eq_snd_prod_decode_aux) simp

function_compile_nat fst_nat_eq_fst_acc_nat
declare fst_nat_related_transfer[Rel_nat del]

lemma fst_nat_eq_fst_acc_nat_nat: "fst_nat n = fst_acc_nat_nat 0 n"
proof -
  from fst_nat_related_transfer have "fst_nat_nat = fst_nat"
    unfolding Rel_nat_nat_eq_eq by (simp add: rel_fun_eq)
  with Rel_nat_nat_eq_eq fst_nat_nat_eq_unfolded show ?thesis by auto
qed

lemma Rel_nat_fst_nat [Rel_nat]: "(Rel_nat ===> Rel_nat) fst_nat fst_nat"
  unfolding Rel_nat_nat_eq_eq by (simp add: rel_fun_eq)

function_compile_nat snd_nat_eq_snd_acc_nat

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.fst_acc_nat_nat_eq_unfolded
HOL_To_IMP_correct HTHN.fst_acc_nat_nat by cook

compile_nat HTHN.snd_acc_nat_nat_eq_unfolded
HOL_To_IMP_correct HTHN.snd_acc_nat_nat by cook

compile_nat HTHN.fst_nat_eq_fst_acc_nat_nat
HOL_To_IMP_correct fst_nat by cook

compile_nat HTHN.snd_nat_nat_eq_unfolded
HOL_To_IMP_correct HTHN.snd_nat_nat by cook

end

context HOL_To_HOL_Nat
begin

lemma fun_pow_eq: "(f^^n) x = (case n of 0 => x | Suc n => (f^^n) (f x))"
  by (simp add: case_nat_eq_if)

lemma nat_selector_eq: "nat_selector nargs arg n =
  (let x = (snd_nat ^^ (arg + 1)) n in if arg + 1 < nargs then fst_nat x else x)"
  unfolding nat_selector_eq by simp

definition "fun_pow_snd_nat n \<equiv> snd_nat^^n"
lemmas fun_pow_snd_nat_eq = fun_pow_eq[of _ "snd_nat", folded fun_pow_snd_nat_def]

function_compile_nat fun_pow_snd_nat_eq

lemmas nat_selector_eq_fun_pow_snd_nat = nat_selector_eq[folded fun_pow_snd_nat_def]
function_compile_nat nat_selector_eq_fun_pow_snd_nat
declare nat_selector_related_transfer[Rel_nat del]

lemma nat_selector_eq_nat: "nat_selector nargs arg n =
  (let x = fun_pow_snd_nat_nat (arg + 1) n in If_nat (less_nat (arg + 1) nargs) (fst_nat x) x)"
proof -
  from nat_selector_related_transfer have "nat_selector_nat = nat_selector"
    unfolding Rel_nat_nat_eq_eq by (simp add: rel_fun_eq)
  with Rel_nat_nat_eq_eq nat_selector_nat_eq_unfolded show ?thesis by auto
qed

lemma Rel_nat_nat_selector [Rel_nat]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat ===> Rel_nat) nat_selector nat_selector"
  unfolding Rel_nat_nat_eq_eq by (simp add: rel_fun_eq)

end

context HOL_Nat_To_IMP
begin

lemmas fun_pow_snd_nat_eq = HTHN.fun_pow_snd_nat_nat_eq_unfolded[unfolded case_nat_eq_if]
compile_nat fun_pow_snd_nat_eq

HOL_To_IMP_correct HTHN.fun_pow_snd_nat_nat
  supply Rel_nat_selector_Suc[Rel_nat]
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction y arbitrary: ya s rule: nat.induct) (cook mode = run_finish)

compile_nat HTHN.nat_selector_eq_nat
HOL_To_IMP_correct nat_selector by cook

end

end
