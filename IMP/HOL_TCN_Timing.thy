theory HOL_TCN_Timing
  imports Com
begin

unbundle no com_syntax
declare [[syntax_ambiguity_warning=false]]

(* general stuff *)

abbreviation "sum_map f xs \<equiv> sum_list (map f xs)"

lemma sum_map_concat: "sum_map f (concat xss) = sum_list (concat (map (map f) xss))"
  using map_concat by metis

(* hol-tcn definition+semantics*)

type_synonym fun_ref = string

(* HOL-TCN *)
datatype
  thol = hLet thol thol
  | hLetBound nat
  | hArg nat
  | hNumber nat
  | hIf thol thol thol
  | hCall fun_ref "thol list"
  | hTAIL "thol list"

open_bundle thol_syntax begin
notation hLet ("LET _ IN _") and
         hIf ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61)
end

(* find_consts "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" *)

(* TODO: could maybe return a set *)
fun calls where
  "calls (LET t1 IN t2) = calls t1 @ calls t2" |
  "calls (hLetBound _) = []" |
  "calls (hArg _) = []" |
  "calls (hNumber _) = []" |
  "calls (IF t1\<noteq>0 THEN t2 ELSE t3) = calls t1 @ calls t2 @ calls t3" |
  "calls (hCall f ts) = (f, ts) # concat (map calls ts)" |
  "calls (hTAIL ts) = concat (map calls ts)"

(* function name \<Rightarrow> (function \<times> timing function) *)
type_synonym fun_registry = "fun_ref \<Rightarrow> ((nat list \<Rightarrow> nat) \<times> (nat list \<Rightarrow> nat))"
abbreviation "f_from_frgt (frgt :: fun_registry) name \<equiv> fst (frgt name)"
abbreviation "T_f_from_frgt (frgt :: fun_registry) name \<equiv> snd (frgt name)"

lemma split_from_frgt:
  "(f, T_f) = frgt fr \<longleftrightarrow> f_from_frgt frgt fr = f \<and> T_f_from_frgt frgt fr = T_f"
  using split_pairs .


inductive
  hbig_step_t :: "thol \<times> fun_registry \<Rightarrow> thol \<times> nat list \<times> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
  where
hLet: "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1; env \<turnstile> (t2,v1#bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v; z = z1+z2\<rbrakk>
       \<Longrightarrow> env \<turnstile> (LET t1 IN t2,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v" |
hLetBound: "n < length bs \<Longrightarrow> env \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>0\<^esup> bs!n" |
hArg: "n < length xs \<Longrightarrow> env \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>0\<^esup> xs!n" |
hNumber: "env \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>0\<^esup> n" |
hIfTrue: "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1; v1 \<noteq> 0; env \<turnstile> (t2,bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v2; z = z1+z2\<rbrakk>
          \<Longrightarrow> env \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v2" |
hIfFalse: "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1; v1 = 0; env \<turnstile> (t3,bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v2; z = z1+z2\<rbrakk>
          \<Longrightarrow> env \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v2" |
hCall: "\<lbrakk>(g, T_g) = frgt gr; length zs = length ts; length vs = length ts;
          \<forall>i < length ts. (f,frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>zs ! i\<^esup> vs ! i;
          g vs = v'; z' = sum_list zs + T_g vs\<rbrakk>
          \<Longrightarrow> (f,frgt) \<turnstile> (hCall gr ts,bs,xs) \<Rightarrow>\<^bsup>z'\<^esup> v'" |
hTAIL: "\<lbrakk>length zs = length ts; length vs = length ts;
          \<forall>i < length ts. (f,frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>zs ! i\<^esup> vs ! i;
          (f,frgt) \<turnstile> (f,[],vs) \<Rightarrow>\<^bsup>z'\<^esup> v';
          z'' = sum_list zs + z' + 1\<rbrakk>
          \<Longrightarrow> (f,frgt) \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>z''\<^esup> v'"

print_theorems

(* code_pred [show_modes] hbig_step_t . (* can't handle the universal quantifier *) *)

lemmas hbig_step_t_induct = hbig_step_t.induct[split_format(complete)]

inductive_cases hLet_case [elim!]: "env \<turnstile> (hLet t1 t2,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hLetBound_case [elim!]: "env \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hArg_case [elim!]: "env \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hNumber_case [elim!]: "env \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hIf_case [elim!]: "env \<turnstile> (hIf t1 t2 t3,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hCall_case [elim!]: "(f,frgt) \<turnstile> (hCall g ts,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hTAIL_case [elim!]: "(f,frgt) \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
lemmas hbig_step_t_cases = hLet_case hLetBound_case hArg_case hNumber_case hIf_case hCall_case hTAIL_case


lemma determ:
  fixes t :: thol
  assumes "ctxt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1"
  assumes "ctxt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v2"
  shows "z1 = z2" "v1 = v2"
  oops (* TODO *)
(* using assms proof (induction arbitrary: z2 v2 rule: hbig_step_t.induct)
  case (hCall g T_g frgt gr zs ts vs f bs xs v' z')
  {
    case 1
    then show ?case sorry (* TODO *)
  next
    case 2
    then show ?case sorry
  }
next
  case (hTAIL zs ts vs f frgt bs xs z' v' z'')
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
qed blast+ *)


fun tails where
  "tails (hTAIL _) \<longleftrightarrow> True" |
  "tails (hLet t1 t2) \<longleftrightarrow> tails t1 \<or> tails t2" |
  "tails (hIf t1 t2 t3) \<longleftrightarrow> tails t1 \<or> tails t2 \<or> tails t3" |
  "tails (hCall g ts) \<longleftrightarrow> (\<exists>t \<in> set ts. tails t)" |
  "tails _ = False"

fun invar where
  "invar (hLet t1 t2) \<longleftrightarrow> \<not> tails t1 \<and> invar t2" |
  "invar (hIf t1 t2 t3) \<longleftrightarrow> \<not> tails t1 \<and> invar t2 \<and> invar t3" |
  "invar (hCall g ts) = (\<forall>t \<in> set ts. \<not> tails t)" |
  "invar (hTAIL ts) = (\<forall>t \<in> set ts. \<not> tails t)" |
  "invar _ = True"

lemma no_tails_invar[simp]: "\<not> tails t \<Longrightarrow> invar t" by (induction t) auto


(* traces *)

type_synonym trace = "(fun_ref \<times> nat list) list"

definition "interp_trace_item frgt g vs_arg_g = T_f_from_frgt frgt g vs_arg_g"
definition "interp_trace frgt = sum_map (\<lambda>(g, vs_arg_g). interp_trace_item frgt g vs_arg_g)"

lemma interp_trace_append[simp]:
  "interp_trace frgt (xs @ ys) = interp_trace frgt xs + interp_trace frgt ys"
  unfolding interp_trace_def by simp
lemma interp_trace_concat_is_sum_map:
  "interp_trace frgt (concat xss) = sum_map (interp_trace frgt) xss"
  unfolding interp_trace_def by (induction xss) auto

datatype leaf_state = Value nat | Tail "nat list"

inductive
  htrace_to_leaf :: "fun_registry \<Rightarrow> thol \<times> nat list \<times> nat list \<Rightarrow> trace \<Rightarrow> leaf_state \<Rightarrow> bool"  ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
hLet:
  "\<lbrakk>frgt \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1; frgt \<turnstile> (t2,v1#bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> l2; T = T1@T2\<rbrakk>
   \<Longrightarrow> frgt \<turnstile> (LET t1 IN t2,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> l2" |
hLetBound: "n < length bs \<Longrightarrow> frgt \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>[]\<^esup> Value (bs ! n)" |
hArg: "n < length xs \<Longrightarrow> frgt \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>[]\<^esup> Value (xs ! n)" |
hNumber: "frgt \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>[]\<^esup> Value n" |
hIfTrue:
  "\<lbrakk>frgt \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1; v1 \<noteq> 0; frgt \<turnstile> (t2,bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> l2; T = T1@T2\<rbrakk>
   \<Longrightarrow> frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> l2" |
hIfFalse:
  "\<lbrakk>frgt \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1; v1 = 0; frgt \<turnstile> (t3,bs,xs) \<Rightarrow>\<^bsup>T3\<^esup> l3; T = T1@T3\<rbrakk>
   \<Longrightarrow> frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> l3" |
hCall:
  "\<lbrakk>(g, T_g) = frgt gr; length vs = length ts; length Ts = length ts;
    \<forall>i < length ts. frgt \<turnstile> (ts ! i,bs,xs) \<Rightarrow>\<^bsup>Ts ! i\<^esup> Value (vs ! i);
    T = concat Ts @ [(gr,vs)]; v = g vs\<rbrakk>
   \<Longrightarrow> frgt \<turnstile> (hCall gr ts,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Value v" |
hTail:
  "\<lbrakk>length vs = length ts; length Ts = length ts;
    \<forall>i < length ts. frgt \<turnstile> (ts ! i,bs,xs) \<Rightarrow>\<^bsup>Ts ! i\<^esup> Value (vs ! i);
    T = concat Ts\<rbrakk>
   \<Longrightarrow> frgt \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Tail vs"

lemmas htrace_to_leaf_induct = htrace_to_leaf.induct[split_format(complete)]


(* relating traces to the semantics

For any t/bs/xs, there are two cases depending on whether t runs to Value or to Tail:

Case 1:
  |----- Value v|  (trace)
  |----------- v|  (sem.)

Case 2:
  |---- Tail xs'||----------- v|  (trace, sem.)
  |-------------------------- v|  (sem.)

In the direction trace \<longrightarrow> semantics:
- For case 1, we show: if there is a trace, there is a corresponding inference in the semantics.
- For case 2, we show: if there is a trace to Tail xs' and an inference in the semantics from f/[]/xs',
  there is a corresponding inference in the semantics for the "whole execution" from t/bs/xs.

In the direction semantics \<longrightarrow> trace:
We show: if there is a semantics, either:
- there exists a corresponding trace to a value (i.e. no tail call occurs), or
- there exists a trace to Tail xs', and from f/[]/xs' a semantics to a value.

*)

lemma trace_val_to_semantics0:
  assumes "frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>(T :: trace)\<^esup> l" "l = Value v"
  shows "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> interp_trace frgt T \<^esup> v"
using assms proof (induction arbitrary: v rule: htrace_to_leaf_induct)
  case (hCall g T_g frgt gr vs ts Ts bs xs T v)
  let ?zs = "map (interp_trace frgt) Ts"
  show ?case
  proof
    have "interp_trace frgt [(gr,vs)] = T_g vs"
      unfolding interp_trace_def interp_trace_item_def using hCall split_from_frgt by simp
    then show "interp_trace frgt T = sum_list ?zs + T_g vs"
      using hCall interp_trace_concat_is_sum_map interp_trace_append by simp
  next
    show "g vs = v" using hCall by simp
  qed (simp_all add: hCall)
qed (auto simp add: interp_trace_def hbig_step_t.intros)

theorem trace_val_to_semantics:
  assumes "frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Value v"
  shows "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> interp_trace frgt T \<^esup> v"
  using assms trace_val_to_semantics0 by blast


lemma trace_tail_to_semantics0:
  assumes "frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>(T :: trace)\<^esup> l" "l = Tail xs'"
  assumes "invar t"
  assumes "(f,frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z\<^esup> v"
  shows "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> interp_trace frgt T + z + 1 \<^esup> v"
  (* TODO: could probably get this proof a bit shorter/cleaner, OK for now *)
using assms proof (induction arbitrary: rule: htrace_to_leaf_induct)
  case (hLet frgt t1 bs xs T1 v1 t2 T2 l2 T)
  show ?case
  proof
    show "interp_trace frgt T + z + 1 = (interp_trace frgt T1) + (interp_trace frgt T2 + z + 1)"
      using hLet interp_trace_append by simp
  next
    show "(f, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>interp_trace frgt T1\<^esup> v1"
      using hLet trace_val_to_semantics by simp
  next
    show "(f, frgt) \<turnstile> (t2, v1 # bs, xs) \<Rightarrow>\<^bsup>interp_trace frgt T2 + z + 1\<^esup>  v"
      using hLet by simp
  qed
next
  case (hIfTrue frgt t1 bs xs T1 v1 t2 T2 l2 T t3)
  show ?case
  proof (rule hbig_step_t.hIfTrue)
    show "(f, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>interp_trace frgt T1\<^esup> v1"
      using hIfTrue trace_val_to_semantics by simp
  next
    show "v1 \<noteq> 0" using hIfTrue by simp
  next
    show "(f, frgt) \<turnstile> (t2, bs, xs) \<Rightarrow>\<^bsup>interp_trace frgt T2 + z + 1\<^esup> v" using hIfTrue by simp
  next
    show "interp_trace frgt T + z + 1 = (interp_trace frgt T1) + (interp_trace frgt T2 + z + 1)"
      using hIfTrue by simp
  qed
next
  case (hIfFalse frgt t1 bs xs T1 v1 t3 T3 l3 T t2)
  show ?case
  proof (rule hbig_step_t.hIfFalse)
    show "(f, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>interp_trace frgt T1\<^esup> v1"
      using hIfFalse trace_val_to_semantics by simp
  next
    show "v1 = 0" using hIfFalse by simp
  next
    show "(f, frgt) \<turnstile> (t3, bs, xs) \<Rightarrow>\<^bsup>interp_trace frgt T3 + z + 1\<^esup> v" using hIfFalse by simp
  next
    show "interp_trace frgt T + z + 1 = (interp_trace frgt T1) + (interp_trace frgt T3 + z + 1)"
      using hIfFalse by simp
  qed
next
  case (hTail vs ts Ts frgt bs xs T)
  let ?zs = "map (interp_trace frgt) Ts"
  show ?case
  proof
    show "interp_trace frgt T + z + 1 = sum_list ?zs + z + 1"
      using hTail interp_trace_concat_is_sum_map interp_trace_append by simp
  next show "\<forall>i<length ts. (f, frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>?zs ! i\<^esup> vs ! i"
      using hTail[simplified] nth_map trace_val_to_semantics by simp
  next show "length vs = length ts" using hTail by simp
  next show "(f, frgt) \<turnstile> (f, [], vs) \<Rightarrow>\<^bsup>z\<^esup> v" using hTail by simp
  next show "length (map (interp_trace frgt) Ts) = length ts" using hTail by simp
  qed
qed simp_all

theorem trace_tail_to_semantics:
  assumes "invar t"
  assumes "frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Tail xs'"
  assumes "(f,frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z\<^esup> v"
  shows "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> interp_trace frgt T + z + 1 \<^esup> v"
  using assms trace_tail_to_semantics0 by blast


(* semantics \<longrightarrow> trace *)


lemma sem_to_trace_non_tailE:
  assumes "\<not> tails t"
  assumes "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> z \<^esup> v"
  obtains T :: trace where "frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Value v" "interp_trace frgt T = z"
  using assms(2,1) apply (induction rule: hbig_step_t_induct)
  apply (metis HOL_TCN_Timing.tails.simps(2) htrace_to_leaf.hLet interp_trace_append)
  apply (metis htrace_to_leaf.hLetBound interp_trace_def list.map(1) sum_list.Nil)
  apply (metis htrace_to_leaf.hArg interp_trace_def list.map(1) sum_list.Nil)
  apply (metis htrace_to_leaf.hNumber interp_trace_def list.map(1) sum_list.Nil)
  apply (metis HOL_TCN_Timing.tails.simps(3) htrace_to_leaf.hIfTrue interp_trace_append)
  apply (metis HOL_TCN_Timing.tails.simps(3) htrace_to_leaf.hIfFalse interp_trace_append)
  oops (* TODO *)

lemma sem_to_trace_inductionI:
  assumes "P' \<or> (\<exists>xs'. Q1' xs' \<and> Q2' xs')"
  assumes "P' \<Longrightarrow> P T"
  assumes "\<And>xs'. Q1' xs' \<Longrightarrow> Q1 T xs'"
  assumes "\<And>xs'. Q2' xs' \<Longrightarrow> Q2 T xs'"
  shows "\<exists>T. P T \<or> (\<exists>xs'. Q1 T xs' \<and> Q2 T xs')"
  using assms by blast

(* oops
lemma sem_to_traceE:
  assumes "invar t"
  assumes "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
  shows "\<exists>T.
    (frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Value v) \<or>
    (\<exists>xs'. frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Tail xs'
           \<and> (f,frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z - interp_trace frgt T - 1\<^esup> v)"
using assms(2,1) proof (induction rule: hbig_step_t_induct)
  case (hLet f frgt t1 bs xs z1 v1 t2 z2 v z)

  from sem_to_trace_non_tailE hLet.hyps(1) obtain T1 where
    T1: "frgt \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1" "interp_trace frgt T1 = z1"
    using hLet.prems invar.simps by blast
  from hLet.IH(2) obtain T2 where
      "(frgt \<turnstile> (t2,v1#bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> Value v) \<or>
       (\<exists>xs'. frgt \<turnstile> (t2,v1#bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> Tail xs' \<and>
              (f, frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z2 - interp_trace frgt T2 - 1\<^esup> v)"
    using hLet.prems by auto
  then show ?case proof (rule sem_to_trace_inductionI)
    assume "frgt \<turnstile> (t2,v1#bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> Value v"
    then show "frgt \<turnstile> (LET t1 IN t2,bs,xs) \<Rightarrow>\<^bsup>T1@T2\<^esup> Value v"
      using T1 htrace_to_leaf.intros by simp
  next
    fix xs'
    assume "frgt \<turnstile> (t2, v1 # bs, xs) \<Rightarrow>\<^bsup>T2\<^esup>  Tail xs'"
    then show "frgt \<turnstile> (LET t1 IN t2, bs, xs) \<Rightarrow>\<^bsup>T1@T2\<^esup>  Tail xs'"
      using T1 htrace_to_leaf.intros by simp
  next
    fix xs'
    assume "(f, frgt) \<turnstile> (f, [], xs') \<Rightarrow>\<^bsup>z2 - interp_trace frgt T2 - 1\<^esup>  v"
    then show "(f, frgt) \<turnstile> (f, [], xs') \<Rightarrow>\<^bsup>z - interp_trace frgt (T1 @ T2) - 1\<^esup>  v"
      using hLet T1 htrace_to_leaf.intros interp_trace_append by simp
  qed
next
  case (hLetBound n bs a b xs)
  then have "b \<turnstile> (hLetBound n, bs, xs) \<Rightarrow>\<^bsup> [] \<^esup> Value (bs ! n)" using htrace_to_leaf.intros by simp
  then show ?case by blast
next
  case (hArg n xs a b bs)
  then have "b \<turnstile> (hArg n, bs, xs) \<Rightarrow>\<^bsup> [] \<^esup> Value (xs ! n)" using htrace_to_leaf.intros by simp
  then show ?case by blast
next
  case (hNumber a b n bs xs)
  then have "b \<turnstile> (hNumber n, bs, xs) \<Rightarrow>\<^bsup> [] \<^esup> Value n" using htrace_to_leaf.intros by simp
  then show ?case by blast
next
  case (hIfTrue f frgt t1 bs xs z1 v1 t2 z2 v2 z t3)
  from sem_to_trace_non_tailE hIfTrue.hyps(1) obtain T1 where
    T1: "frgt \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1" "interp_trace frgt T1 = z1"
    using hIfTrue.prems invar.simps by blast
  from hIfTrue.IH(2) obtain T2 where
      "(frgt \<turnstile> (t2,bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> Value v2) \<or>
       (\<exists>xs'. frgt \<turnstile> (t2,bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> Tail xs' \<and>
              (f, frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z2 - interp_trace frgt T2 - 1\<^esup> v2)"
    using hIfTrue.prems by auto
  then show ?case proof (rule sem_to_trace_inductionI)
    assume "frgt \<turnstile> (t2,bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> Value v2"
    then show "frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>T1@T2\<^esup> Value v2"
      using hIfTrue T1 htrace_to_leaf.intros by simp
  next
    fix xs'
    assume "frgt \<turnstile> (t2,bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> Tail xs'"
    then show "frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>T1@T2\<^esup> Tail xs'"
      using hIfTrue T1 htrace_to_leaf.intros by simp
  next
    fix xs'
    assume "(f,frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z2 - interp_trace frgt T2 - 1\<^esup>  v2"
    then show "(f,frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z - interp_trace frgt (T1@T2) - 1\<^esup> v2"
      using hIfTrue T1 htrace_to_leaf.intros interp_trace_append by simp
  qed
next
  case (hIfFalse f frgt t1 bs xs z1 v1 t3 z2 v2 z t2)
  from sem_to_trace_non_tailE hIfFalse.hyps(1) obtain T1 where
    T1: "frgt \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1" "interp_trace frgt T1 = z1"
    using hIfFalse.prems invar.simps by blast
  from hIfFalse.IH(2) obtain T2 where
      "(frgt \<turnstile> (t3,bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> Value v2) \<or>
       (\<exists>xs'. frgt \<turnstile> (t3,bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> Tail xs' \<and>
              (f,frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z2 - interp_trace frgt T2 - 1\<^esup> v2)"
    using hIfFalse.prems by auto
  then show ?case proof (rule sem_to_trace_inductionI)
    assume "frgt \<turnstile> (t3,bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> Value v2"
    then show "frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>T1@T2\<^esup> Value v2"
      using hIfFalse T1 htrace_to_leaf.intros by simp
  next
    fix xs'
    assume "frgt \<turnstile> (t3,bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> Tail xs'"
    then show "frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>T1@T2\<^esup> Tail xs'"
      using hIfFalse T1 htrace_to_leaf.intros by simp
  next
    fix xs'
    assume "(f,frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z2 - interp_trace frgt T2 - 1\<^esup>  v2"
    then show "(f,frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z - interp_trace frgt (T1@T2) - 1\<^esup> v2"
      using hIfFalse T1 htrace_to_leaf.intros interp_trace_append by simp
  qed
next
  case (hCall g T_g frgt gr zs ts vs f bs xs v' z')
  then show ?case sorry (* TODO *)
next
  case (hTAIL zs ts vs f frgt bs xs z' v' z'')
  then show ?case sorry
qed

(* TODO is this better *)
lemma sem_to_traceE':
  assumes "invar t"
  assumes "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
  obtains T where "
    (frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Value v) \<or>
    (\<exists>xs'. frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Tail xs'
           \<and> (f,frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z - interp_trace frgt T - 1\<^esup> v)"
  using assms sem_to_traceE by blast *)

lemma sem_to_trace_existsE:
  assumes "invar t"
  assumes "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> z \<^esup> v"
  obtains T :: trace and l where "frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> l"
  (* using sem_to_traceE assms by blast *)
  oops

(*
lemma trace_val_from_semantics:
  assumes "invar t" (* ? *)
  assumes "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> z \<^esup> v1"
  assumes "frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Value v2"
  shows "v1 = v2 \<and> interp_trace frgt T = z"
  sorry

lemma non_tails_trace: (* useful/meaningful? *)
  assumes "\<not> tails t"
  assumes "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> z \<^esup> v"
  obtains T where "frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> T \<^esup> Value v" "interp_trace frgt T = z"
  using trace_exists_non_tail trace_val_from_semantics assms no_tails_invar by blast

lemma trace_tail_from_semantics:
  assumes "invar t" (* ? *)
  assumes "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> z \<^esup> v"
  assumes "frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Tail xs'"
  shows "(f,frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z - interp_trace frgt T - 1\<^esup> v"
  sorry

lemma trace_from_semantics:
  assumes "invar t"
  assumes "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> z \<^esup> v1"
  assumes "frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> T :: trace \<^esup> l"
  shows "(case l of
      Value v2 \<Rightarrow> v2 = v1
    | Tail xs' \<Rightarrow> (f,frgt) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z - interp_trace frgt T - 1\<^esup> v)"
  using trace_val_from_semantics[OF assms(1) assms(2)] trace_tail_from_semantics assms sorry

*)

end
