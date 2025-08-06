theory IMP_Tailcall_Traces
  imports IMP_Tailcall
begin

unbundle tcom_syntax
unbundle no com'_syntax

type_synonym call_trace = "(com \<times> state) list"
type_synonym trace = "nat \<times> call_trace"

(* interp_trace k T z \<longrightarrow> z is the running time of the trace T, plus k *)
definition "interp_trace k T z \<equiv>
  (\<exists>zgs. length zgs = length T
         \<and> (\<forall>i < length T. \<exists>s'. T ! i \<Rightarrow>\<^bsup>zgs ! i\<^esup> s')
         \<and> z = sum_list zgs + k)"

lemma interp_trace_append[simp]:
  assumes "interp_trace k1 T1 z1" "interp_trace k2 T2 z2"
  shows "interp_trace (k1 + k2) (T1 @ T2) (z1 + z2)"
  using assms unfolding interp_trace_def oops (* TODO *)

type_synonym leaf_state = "state \<times> bool"

inductive
  (* (term, state), (constants, calls), (new state, is tail call) *)
  ttrace_to_leaf :: "tcom \<times> state \<Rightarrow> trace \<Rightarrow> leaf_state \<Rightarrow> bool"  ("_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
tSkip: "(tSKIP,s) \<Rightarrow>\<^bsup>(Suc 0, [])\<^esup> (s, False)" |
tAssign: "(tAssign x a,s) \<Rightarrow>\<^bsup>(Suc (Suc 0), [])\<^esup> (s(x := aval a s), False)" |
tSeq:
  "\<lbrakk>(c1,s1) \<Rightarrow>\<^bsup>(k1, T1)\<^esup> (s2, False); (c2,s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup> (s3, l); k = k1 + k2; T = T1 @ T2\<rbrakk>
   \<Longrightarrow> (tSeq c1 c2,s1) \<Rightarrow>\<^bsup>(k, T)\<^esup> (s3, l)" |
tIfTrue:
  "\<lbrakk>s b \<noteq> 0; (c1,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l); k' = k + 1\<rbrakk>
   \<Longrightarrow> (IF b\<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>(k', T)\<^esup> (t, l)" |
tIfFalse:
  "\<lbrakk>s b = 0; (c2,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l); k' = k + 1\<rbrakk>
   \<Longrightarrow> (IF b\<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>(k', T)\<^esup> (t, l)" |
tCall: "\<lbrakk>(C,s) \<Rightarrow>\<^bsup>z \<^esup> t\<rbrakk> \<Longrightarrow> (tCall C r,s) \<Rightarrow>\<^bsup>(0, [(C,s)])\<^esup> (s(r := t r), False)" |
tTail: "(tTAIL,s) \<Rightarrow>\<^bsup>(5, [])\<^esup> (s, True)"

lemmas ttrace_to_leaf_induct = ttrace_to_leaf.induct[split_format(complete)]

lemma trace_nontail_has_bigstep:
  assumes "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)" "\<not> l"
  shows "\<exists>z. f \<turnstile> (c,s) \<Rightarrow>\<^bsup> z \<^esup> t"
  using assms by (induction rule: ttrace_to_leaf_induct) auto

lemma bigstep_has_trace_nontail:
  assumes "\<not> tails c"
  assumes "f \<turnstile> (c,s) \<Rightarrow>\<^bsup> z \<^esup> t"
  assumes "\<not> l"
  shows "\<exists>k T. (c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)" 
  using assms(2,1,3) apply (induction rule: tbig_step_t_induct)
  using ttrace_to_leaf.intros apply auto oops
  




lemma trace_nontail_to_semantics0:
  assumes "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)" "\<not> l"
  shows "\<exists>z. interp_trace k T z \<and> f \<turnstile> (c,s) \<Rightarrow>\<^bsup> z \<^esup> t"
  using assms apply (induction arbitrary: rule: ttrace_to_leaf_induct)
  subgoal unfolding interp_trace_def by force
  subgoal unfolding interp_trace_def by force
  using tbig_step_t.intros apply simp
  oops

theorem trace_nontail_to_semantics:
  assumes "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, False)"
  obtains z where "interp_trace k T z" "f \<turnstile> (c,s) \<Rightarrow>\<^bsup> z \<^esup> t"
  (* using assms trace_nontail_to_semantics0 by blast *)
  oops

lemma trace_tail_to_semantics0:
  assumes "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)" "l"
  assumes "invar c"
  assumes "f \<turnstile> (f,t) \<Rightarrow>\<^bsup>y\<^esup> u"
  shows "\<exists>x. interp_trace k T x \<and> f \<turnstile> (c,s) \<Rightarrow>\<^bsup> x+y \<^esup> u"
  oops

theorem trace_tail_to_semantics:
  assumes "invar c"
  assumes "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, True)"
  assumes "f \<turnstile> (f,t) \<Rightarrow>\<^bsup>y\<^esup> u"
  obtains x where "interp_trace k T x" "f \<turnstile> (c,s) \<Rightarrow>\<^bsup> x+y \<^esup> u"
  (* using assms trace_tail_to_semantics0 by blast *)
  oops

(* TODO: prove more things about traces, see HOL-TCN for inspiration *)



(* assumptions:
    - variable names of function arguments and return values of
      called functions and f itself do not conflict
    - correct number of arguments to call/recurse constructors *)


end
