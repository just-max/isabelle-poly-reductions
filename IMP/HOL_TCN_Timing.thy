theory HOL_TCN_Timing
  imports "HOL-Library.Log_Nat" IMP_Tailcall Fresh
begin

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

(* function name \<Rightarrow> (function \<times> timing function) *)
type_synonym thol_reg = "fun_ref \<Rightarrow> ((nat list \<Rightarrow> nat) \<times> (nat list \<Rightarrow> nat))"
abbreviation "f_from_reg (reg :: thol_reg) name \<equiv> fst (reg name)"
abbreviation "T_f_from_reg (reg :: thol_reg) name \<equiv> snd (reg name)"

lemma split_from_reg:
  "(f, T_f) = reg fr \<longleftrightarrow> f_from_reg reg fr = f \<and> T_f_from_reg reg fr = T_f"
  using split_pairs .

(* function name \<Rightarrow> (argument registers' names \<times> IMP command \<times> return register's name *)
type_synonym thol_ctxt = "fun_ref \<Rightarrow> (vname list \<times> com \<times> vname)"
abbreviation "args_from_ctxt (ctxt :: thol_ctxt) name \<equiv> fst (ctxt name)"
abbreviation "com_from_ctxt (ctxt :: thol_ctxt) name \<equiv> fst (snd (ctxt name))"
abbreviation "ret_from_ctxt (ctxt :: thol_ctxt) name \<equiv> snd (snd (ctxt name))"
(* TODO: use these abbrev. *)
(* TODO: use better names than reg/ctxt *)

definition "null = (\<lambda>_. undefined)"



inductive
  hbig_step_t :: "thol \<times> thol_reg \<Rightarrow> thol \<times> nat list \<times> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
  where
hLet: "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1; env \<turnstile> (t2,v1#bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v; z = z1+z2\<rbrakk>
       \<Longrightarrow> env \<turnstile> (LET t1 IN t2,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v" |
hLetBound: "v = bs!n \<Longrightarrow> env \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>0\<^esup> v" |
hArg: "v = xs!n \<Longrightarrow> env \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>0\<^esup> v" |
hNumber: "env \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>0\<^esup> n" |
hIfTrue: "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1; v1 \<noteq> 0; env \<turnstile> (t2,bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v2; z = z1+z2\<rbrakk>
          \<Longrightarrow> env \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v2" |
hIfFalse: "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1; v1 = 0; env \<turnstile> (t3,bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v2; z = z1+z2\<rbrakk>
          \<Longrightarrow> env \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v2" |
hCall: "\<lbrakk>(g, T_g) = reg gr; length zs = length ts; length vs = length ts;
          \<forall>i < length ts. (f,reg) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>zs ! i\<^esup> vs ! i;
          g vs = v'; z' = sum_list zs + T_g vs\<rbrakk>
          \<Longrightarrow> (f,reg) \<turnstile> (hCall gr ts,bs,xs) \<Rightarrow>\<^bsup>z'\<^esup> v'" |
hTAIL: "\<lbrakk>length zs = length ts; length vs = length ts;
          \<forall>i < length ts. (f,reg) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>zs ! i\<^esup> vs ! i;
          (f,reg) \<turnstile> (f,[],vs) \<Rightarrow>\<^bsup>z'\<^esup> v';
          z'' = sum_list zs + z' + 1\<rbrakk>
          \<Longrightarrow> (f,reg) \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>z''\<^esup> v'"




(* 
(* TODO: use list_all instead of quantifiers?:
    list_all (\<lambda>(ti, zi, vi). (f,reg) \<turnstile> (ti,bs,xs) \<Rightarrow>\<^bsup>zi\<^esup> vi) (zip ts (zip zs vs)) *)
inductive
  hbig_step_t :: "thol \<times> thol_reg \<Rightarrow> thol \<times> nat list \<times> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
  where
hLet: "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1; env \<turnstile> (t2,v1#bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v; z = z1+z2\<rbrakk>
       \<Longrightarrow> env \<turnstile> (hLet t1 t2,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v" |
hLetBound: "v = bs!n \<Longrightarrow> env \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>0\<^esup> v" |
hArg: "v = xs!n \<Longrightarrow> env \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>0\<^esup> v" |
hNumber: "env \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>0\<^esup> n" |
hIfTrue: "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1; v1 \<noteq> 0; env \<turnstile> (t2,bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v2; z = z1+z2\<rbrakk>
          \<Longrightarrow> env \<turnstile> (hIf t1 t2 t3,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v2" |
hIfFalse: "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1; v1 = 0; env \<turnstile> (t3,bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v2; z = z1+z2\<rbrakk>
          \<Longrightarrow> env \<turnstile> (hIf t1 t2 t3,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v2" |
hCall: "\<lbrakk>reg vg = (g, T_g); length zs = length ts; length vs = length ts;
          \<And>ti vi zi. (ti, zi, vi) \<in> set (zip ts (zip zs vs)) \<longrightarrow> (f,reg) \<turnstile> (ti,bs,xs) \<Rightarrow>\<^bsup>zi\<^esup> vi;
          g vs = v'; z' = sum_list zs + T_g vs\<rbrakk>
          \<Longrightarrow> (f,reg) \<turnstile> (hCall vg ts,bs,xs) \<Rightarrow>\<^bsup>z'\<^esup> v'" |
hTAIL: "\<lbrakk>length zs = length ts; length vs = length ts;
          \<And>ti vi zi. (ti, zi, vi) \<in> set (zip ts (zip zs vs)) \<longrightarrow> (f,reg) \<turnstile> (ti,bs,xs) \<Rightarrow>\<^bsup>zi\<^esup> vi;
          (f,reg) \<turnstile> (f,[],vs) \<Rightarrow>\<^bsup>z'\<^esup> v';
          z'' = sum_list zs + z' + 1\<rbrakk>
          \<Longrightarrow> (f,reg) \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>z''\<^esup> v'" *)

print_theorems

(* code_pred [show_modes] hbig_step_t . (* can't handle the universal quantifier *) *)

lemmas hbig_step_t_induct = hbig_step_t.induct[split_format(complete)]

inductive_cases hLet_case [elim!]: "env \<turnstile> (hLet t1 t2,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hLetBound_case [elim!]: "env \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hArg_case [elim!]: "env \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hNumber_case [elim!]: "env \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hIf_case [elim!]: "env \<turnstile> (hIf t1 t2 t3,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hCall_case [elim!]: "(f,reg) \<turnstile> (hCall g ts,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hTAIL_case [elim!]: "(f,reg) \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
lemmas hbig_step_t_cases = hLet_case hLetBound_case hArg_case hNumber_case hIf_case hCall_case hTAIL_case


lemma determ:
  fixes t :: thol
  assumes "ctxt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1"
  assumes "ctxt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v2"
  shows "z1 = z2" "v1 = v2"
  oops
(* using assms proof (induction arbitrary: z2 v2 rule: hbig_step_t.induct)
  case (hCall g T_g reg gr zs ts vs f bs xs v' z')
  {
    case 1
    then show ?case sorry (* TODO *)
  next
    case 2
    then show ?case sorry
  }
next
  case (hTAIL zs ts vs f reg bs xs z' v' z'')
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

lemma non_tail_invar[simp]: "\<not> tails t \<Longrightarrow> invar t" by (induction t) auto


(* traces *)

type_synonym trace = "(fun_ref \<times> nat list) list"

definition "interp_trace_item reg g vs_arg_g = T_f_from_reg reg g vs_arg_g"
definition "interp_trace reg = sum_map (\<lambda>(g, vs_arg_g). interp_trace_item reg g vs_arg_g)"

lemma interp_trace_append[simp]:
  "interp_trace reg (xs @ ys) = interp_trace reg xs + interp_trace reg ys"
  unfolding interp_trace_def by simp
lemma interp_trace_concat_is_sum_map:
  "interp_trace reg (concat xss) = sum_map (interp_trace reg) xss"
  unfolding interp_trace_def by (induction xss) auto



datatype leaf_state = Value nat | Tail "nat list"

inductive
  htrace_to_leaf :: "thol_reg \<Rightarrow> thol \<times> nat list \<times> nat list \<Rightarrow> trace \<Rightarrow> leaf_state \<Rightarrow> bool"  ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
hLet:
  "\<lbrakk>reg \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1; reg \<turnstile> (t2,v1#bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> l2; T = T1@T2\<rbrakk>
   \<Longrightarrow> reg \<turnstile> (LET t1 IN t2,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> l2" |
hLetBound: "reg \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>[]\<^esup> Value (bs ! n)" |
hArg: "reg \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>[]\<^esup> Value (xs ! n)" |
hNumber: "reg \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>[]\<^esup> Value n" |
hIfTrue:
  "\<lbrakk>reg \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1; v1 \<noteq> 0; reg \<turnstile> (t2,bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> l2; T = T1@T2\<rbrakk>
   \<Longrightarrow> reg \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> l2" |
hIfFalse:
  "\<lbrakk>reg \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1; v1 = 0; reg \<turnstile> (t3,bs,xs) \<Rightarrow>\<^bsup>T3\<^esup> l3; T = T1@T3\<rbrakk>
   \<Longrightarrow> reg \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> l3" |
hCall:
  "\<lbrakk>(g, T_g) = reg gr; length vs = length ts; length Ts = length ts;
    \<forall>i < length ts. reg \<turnstile> (ts ! i,bs,xs) \<Rightarrow>\<^bsup>Ts ! i\<^esup> Value (vs ! i);
    T = concat Ts @ [(gr,vs)]; v = g vs\<rbrakk>
   \<Longrightarrow> reg \<turnstile> (hCall gr ts,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Value v" |
hTail:
  "\<lbrakk>length vs = length ts; length Ts = length ts;
    \<forall>i < length ts. reg \<turnstile> (ts ! i,bs,xs) \<Rightarrow>\<^bsup>Ts ! i\<^esup> Value (vs ! i);
    T = concat Ts\<rbrakk>
   \<Longrightarrow> reg \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Tail vs"

lemmas htrace_to_leaf_induct = htrace_to_leaf.induct[split_format(complete)]


(* relating traces to the semantics *)

lemma trace_non_tail0:
  assumes "reg \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>(T :: trace)\<^esup> l" "l = Value v"
  shows "(f,reg) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> interp_trace reg T \<^esup> v"
using assms proof (induction arbitrary: v rule: htrace_to_leaf_induct)
  case (hCall g T_g reg gr vs ts Ts bs xs T v)
  let ?zs = "map (interp_trace reg) Ts"
  show ?case
  proof
    have "interp_trace reg [(gr,vs)] = T_g vs"
      unfolding interp_trace_def interp_trace_item_def using hCall split_from_reg by simp
    then show "interp_trace reg T = sum_list ?zs + T_g vs"
      using hCall interp_trace_concat_is_sum_map interp_trace_append by simp
  next
    show "g vs = v" using hCall by simp
  qed (simp_all add: hCall)
qed (simp_all add: interp_trace_def hbig_step_t.intros)

theorem trace_non_tail:
  assumes "reg \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Value v"
  shows "(f,reg) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> interp_trace reg T \<^esup> v"
  using assms trace_non_tail0 by blast


lemma trace_tail0:
  assumes "reg \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>(T :: trace)\<^esup> l" "l = Tail xs'"
  assumes "invar t"
  assumes "(f,reg) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z\<^esup> v"
  shows "(f,reg) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> interp_trace reg T + z + 1 \<^esup> v"
  (* TODO: could probably get this proof a bit shorter/cleaner, OK for now *)
using assms proof (induction arbitrary: rule: htrace_to_leaf_induct)
  case (hLet reg t1 bs xs T1 v1 t2 T2 l2 T)
  show ?case
  proof
    show "interp_trace reg T + z + 1 = (interp_trace reg T1) + (interp_trace reg T2 + z + 1)"
      using hLet interp_trace_append by simp
  next
    show "(f, reg) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>interp_trace reg T1\<^esup> v1"
      using hLet trace_non_tail by simp
  next
    show "(f, reg) \<turnstile> (t2, v1 # bs, xs) \<Rightarrow>\<^bsup>interp_trace reg T2 + z + 1\<^esup>  v"
      using hLet by simp
  qed
next
  case (hIfTrue reg t1 bs xs T1 v1 t2 T2 l2 T t3)
  show ?case
  proof (rule hbig_step_t.hIfTrue)
    show "(f, reg) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>interp_trace reg T1\<^esup> v1"
      using hIfTrue trace_non_tail by simp
  next
    show "v1 \<noteq> 0" using hIfTrue by simp
  next
    show "(f, reg) \<turnstile> (t2, bs, xs) \<Rightarrow>\<^bsup>interp_trace reg T2 + z + 1\<^esup> v" using hIfTrue by simp
  next
    show "interp_trace reg T + z + 1 = (interp_trace reg T1) + (interp_trace reg T2 + z + 1)"
      using hIfTrue by simp
  qed
next
  case (hIfFalse reg t1 bs xs T1 v1 t3 T3 l3 T t2)
  show ?case
  proof (rule hbig_step_t.hIfFalse)
    show "(f, reg) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>interp_trace reg T1\<^esup> v1"
      using hIfFalse trace_non_tail by simp
  next
    show "v1 = 0" using hIfFalse by simp
  next
    show "(f, reg) \<turnstile> (t3, bs, xs) \<Rightarrow>\<^bsup>interp_trace reg T3 + z + 1\<^esup> v" using hIfFalse by simp
  next
    show "interp_trace reg T + z + 1 = (interp_trace reg T1) + (interp_trace reg T3 + z + 1)"
      using hIfFalse by simp
  qed
next
  case (hTail vs ts Ts reg bs xs T)
  let ?zs = "map (interp_trace reg) Ts"
  show ?case
  proof
    show "interp_trace reg T + z + 1 = sum_list ?zs + z + 1"
      using hTail interp_trace_concat_is_sum_map interp_trace_append by simp
  next show "\<forall>i<length ts. (f, reg) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>?zs ! i\<^esup> vs ! i"
      using hTail[simplified] nth_map trace_non_tail by simp
  next show "length vs = length ts" using hTail by simp
  next show "(f, reg) \<turnstile> (f, [], vs) \<Rightarrow>\<^bsup>z\<^esup> v" using hTail by simp
  next show "length (map (interp_trace reg) Ts) = length ts" using hTail by simp
  qed
qed simp_all

theorem trace_tail:
  assumes "invar t"
  assumes "reg \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Tail xs'"
  assumes "(f,reg) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z\<^esup> v"
  shows "(f,reg) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> interp_trace reg T + z + 1 \<^esup> v"
  using assms trace_tail0 by blast


(* lemma trace_exists:
  assumes "(f,reg) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> z \<^esup> v"
  assumes "invar t"
  shows "\<exists>(T :: trace) l. reg \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> l"
  sorry *)

lemma
  assumes "(f,reg) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> z \<^esup> v1"
  shows "\<exists>T l. reg \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> l \<and>
    (case l of
        Value v2 \<Rightarrow> v2 = v1
      | Tail xs' \<Rightarrow> (f,reg) \<turnstile> (f,[],xs') \<Rightarrow>\<^bsup>z - interp_trace reg T - 1\<^esup> v)"
  sorry




term eval_to_tail

inductive teval_to_tail where
  "teval_to_tail s tSKIP None" |
  "teval_to_tail s (tAssign x a) None" |
  "\<lbrakk> f \<turnstile> (c1,s) \<Rightarrow>\<^bsup>z1\<^esup> s2; teval_to_tail s2 c2 s3 \<rbrakk> \<Longrightarrow> teval_to_tail s (tSeq c1 c2) s3" |
  "\<lbrakk> s x \<noteq> 0; teval_to_tail s c1 t \<rbrakk> \<Longrightarrow> teval_to_tail s (tIf x c1 c2) t" |
  "\<lbrakk> s x = 0; teval_to_tail s c2 t \<rbrakk> \<Longrightarrow> teval_to_tail s (tIf x c1 c2) t" |
  "teval_to_tail s (tCall c x) None" |
  "teval_to_tail s tTAIL (Some s)"

inductive_cases teval_to_tail_tIfE[elim!]: "teval_to_tail s (tIf x c1 c2) t"

inductive ttime_to_tail :: "state \<Rightarrow> tcom \<Rightarrow> nat \<Rightarrow> bool" where
  "ttime_to_tail s tSKIP 1" |
  "ttime_to_tail s (tAssign x a) 2" |
  "\<lbrakk> f \<turnstile> (c1,s) \<Rightarrow>\<^bsup>z1\<^esup> s2; ttime_to_tail s2 c2 z2; z = z1 + z2 \<rbrakk> \<Longrightarrow> ttime_to_tail s (tSeq c1 c2) z" |
  "\<lbrakk> s x \<noteq> 0; ttime_to_tail s c1 z; z' = z + 1 \<rbrakk> \<Longrightarrow> ttime_to_tail s (tIf x c1 c2) z'" |
  "\<lbrakk> s x = 0; ttime_to_tail s c2 z; z' = z + 1 \<rbrakk> \<Longrightarrow> ttime_to_tail s (tIf x c1 c2) z'" |
  "\<lbrakk> (c,s) \<Rightarrow>\<^bsup>z\<^esup> s2 \<rbrakk> \<Longrightarrow> ttime_to_tail s (tCall c x) z" |
  "ttime_to_tail s tTAIL 5"


lemma tnon_tail_ctxt_swap:
  fixes f c :: tcom
  assumes "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
  assumes "\<not>tails c"
  shows "g \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
  using assms apply (induction f "(c,s)" z t arbitrary: c s rule: tbig_step_t.induct) apply simp_all
       apply blast
      apply blast
     apply blast (* TODO *)
  by auto

theorem ttime_to_tail:
  fixes c :: tcom
  assumes "invar c"
  assumes "f \<turnstile> (c,s1) \<Rightarrow>\<^bsup>z\<^esup> s3"
  assumes "teval_to_tail s1 c (Some s2)"
  shows "\<exists>z1 z2. z = z1 + z2 \<and> ttime_to_tail s1 c z1 \<and> f \<turnstile> (f,s2) \<Rightarrow>\<^bsup>z2\<^esup> s3"
using assms proof (induction c arbitrary: s1 z)
  case tSKIP
  then show ?case using teval_to_tail.cases by fastforce
next
  case (tAssign x1 x2)
  then show ?case using teval_to_tail.cases by fastforce
next
  case (tSeq c1 c2) (* TODO cleanup *)
  (* with tnon_tail_ctxt_swap tdeterm show ?case sledgehammer *)

  obtain z11 s'1 z2 where a: "f \<turnstile> (c1,s1) \<Rightarrow>\<^bsup>z11 \<^esup> s'1" and b: "f \<turnstile> (c2,s'1) \<Rightarrow>\<^bsup>z2 \<^esup> s3" and c: "z=z11+z2"
    using tSeq tSeq_tE by blast
  thm tSeq.IH(2) tSeq.prems(2)

  have "invar c2" using tSeq by simp

  obtain f' z1 s' where 1: "f' \<turnstile> (c1,s1) \<Rightarrow>\<^bsup>z1\<^esup> s'" and 2: "teval_to_tail s' c2 (Some s2)"
    using teval_to_tail.cases[OF tSeq.prems(3), simplified] by metis
  then have "f \<turnstile> (c1,s1) \<Rightarrow>\<^bsup>z1\<^esup> s'" using tnon_tail_ctxt_swap tSeq by simp

  with a tdeterm have d: (* "z1 = z11" *) "s' = s'1" by simp_all

  obtain z1a z2a where "z2 = z1a + z2a \<and> ttime_to_tail s'1 c2 z1a \<and> f \<turnstile> (f, s2) \<Rightarrow>\<^bsup>z2a\<^esup>  s3"
    using tSeq.IH(2)[OF \<open>invar c2\<close> b 2[simplified d]] by blast

  with a c show ?case by (metis add.assoc ttime_to_tail.intros(3))
next
  case (tIf x1 c1 c2) (* TODO cleanup *)
  then show ?case
  proof (cases rule: tIf_tE[OF tIf.prems(2)])
    case (1 x)
    then show ?thesis
      by (smt (verit, ccfv_SIG) Suc_eq_plus1 add.assoc add.commute invar.simps(2) not_gr_zero tIf.IH(1) tIf.prems(1,3) teval_to_tail_tIfE
          ttime_to_tail.intros(4))
  next
    case (2 x)
    then show ?thesis
      by (smt (verit, ccfv_threshold) Suc_eq_plus1 add.assoc add.commute invar.simps(2) less_numeral_extra(3) tIf.IH(2) tIf.prems(1,3) teval_to_tail_tIfE
          ttime_to_tail.intros(5))
  qed
next
  case (tCall x1 x2)
  then show ?case using teval_to_tail.cases by fastforce
next
  case tTAIL
  then obtain z' where z': "z = 5 + z'" "f \<turnstile> (f,s1) \<Rightarrow>\<^bsup>z'\<^esup> s3" using tTail_tE by blast
  then have "f \<turnstile> (f,s2) \<Rightarrow>\<^bsup>z - 5\<^esup>  s3" using tTAIL teval_to_tail.cases by auto
  with z' show ?case using ttime_to_tail.intros(7) by auto
qed

(*

inductive ttime_to_tail where
  "ttime_to_tail s tSKIP [] (Suc (0::nat))" |
  "ttime_to_tail s (tAssign x a) [] (Suc (Suc (0::nat)))" |
  "\<lbrakk> ttime_to_tail s c1 gs1 k1; f \<turnstile> (c1,s) \<Rightarrow>\<^bsup>z1\<^esup> s2; ttime_to_tail s2 c2 gs2 k2; k = k1 + k2 \<rbrakk>
   \<Longrightarrow> ttime_to_tail s (tSeq c1 c2) (gs1 @ gs2) k" |
  "\<lbrakk> s x \<noteq> 0; ttime_to_tail s c1 gs k; k' = k + 1 \<rbrakk> \<Longrightarrow> ttime_to_tail s (tIf x c1 c2) gs k'" |
  "\<lbrakk> s x = 0; ttime_to_tail s c2 gs k; k' = k + 1 \<rbrakk> \<Longrightarrow> ttime_to_tail s (tIf x c1 c2) gs k'" |
  "ttime_to_tail s (tCall c x) [(c,s)] 0" |
  "ttime_to_tail s tTAIL [] 5"

definition "tinterp_time gs k z \<equiv>
  (\<exists>zgs. (\<forall>(zg,(c,s)) \<in> set (zip zgs gs). \<exists>s'. (c,s) \<Rightarrow>\<^bsup>zg\<^esup> s') \<and> z = sum_list zgs + k)"

theorem ttime_to_tail:
  fixes c :: tcom
  assumes "invar c"
  assumes "f \<turnstile> (c,s1) \<Rightarrow>\<^bsup>z\<^esup> s3"
  assumes "teval_to_tail s c (Some s2)"
  shows "\<exists>gs k z1 z2. z = z1 + z2 \<and> ttime_to_tail s c gs k \<and> tinterp_time gs k z1 \<and> f \<turnstile> (f,s2) \<Rightarrow>\<^bsup>z2\<^esup> s3"
using assms proof (induction c arbitrary: s)
*)

(* assumptions:
    - variable names of function arguments and return values of
      called functions and f itself do not conflict
    - correct number of arguments to call/recurse constructors *)

(* let us switch between definitions easily *)
abbreviation "fresh' \<equiv> Fresh.fresh"

(*
definition map_fresh where
  "map_fresh stale name f xs =
    snd ((foldl (\<lambda>(st0, xs') x. (fresh' st0 name # st0, xs' @ [f st0 (fresh' st0 name) x])) (stale, [])) xs)"

value "map_fresh [] ''x'' (\<lambda>v vs (x :: nat). (x, v, vs)) [1, 2, 3]"

definition "fresh_n (n :: nat) stale name = snd (fold (\<lambda>_ (st0, r).
  let x = fresh' st0 name in (x # st0, r @ [(x, st0)])) [1..int n] (stale, []))" *)

(* definition "make_n (n :: nat) name = [name @ string_of_nat i . i <- [0..<n]]" *)
definition "make_n_fresh n stale name = map (fresh' stale o ((@) name) o string_of_nat) [0..<n]"

lemma distinct_make_n_fresh: "distinct (make_n_fresh n stale name)"
unfolding make_n_fresh_def proof (subst distinct_map, standard)
  show "inj_on (fresh' stale \<circ> (@) name \<circ> string_of_nat) (set [0..<n])"
    using comp_inj_on inj_string_of_nat inj_append2 Fresh.inj_fresh inj_on_subset[where A = UNIV, simplified]
    by metis
qed simp

value "make_n_fresh 5 [''f.args.2.0'', ''f.args.2.1'', ''f.args.3.0''] ''f.args.''"

(* definition "foldr1 f xs = foldr f (butlast xs) (last xs)" *)
(* definition "t_seqs ts = foldr1 tSeq ts" (* (if ts = [] then tSKIP else  *) *)
definition "t_seqs ts = foldr tSeq ts" (* (if ts = [] then tSKIP else  *)
value "t_seqs ([c1, c2, c3]) c4"

(* lemma foldr1_append: assumes "xs \<noteq> []" "ys \<noteq> []" shows "foldr1 f (xs @ ys) = foldr tSeq xs (foldr1 tSeq ys)" *)

lemma invar_tseqs[simp]: assumes "\<forall>t \<in> set xs. \<not> tails t" "invar x" shows "invar (t_seqs xs x)"
  unfolding t_seqs_def using assms by (induction xs) simp_all
lemma non_tails_tseqs[simp]: assumes "\<forall>t \<in> set xs. \<not> tails t" "\<not> tails x" shows "\<not> tails (t_seqs xs x)"
  unfolding t_seqs_def using assms by (induction xs) simp_all
(* lemma non_tails_tseqs_append: assumes "\<not> tails (t_seqs xs)" "\<not> tails (t_seqs ys)" shows "\<not> tails (t_seqs (xs @ ys) x)" *)
  (* using assms unfolding t_seqs_def foldr1_def apply (induction xs) apply simp_all *)
  (* apply (cases xs) unfolding t_seqs_def foldr1_def apply simp *)
  (* apply (cases ys) *)
  (* apply simp sledgehammer *)
   (* apply (induction xs) unfolding t_seqs_def foldr1_def apply simp_all *)

abbreviation "mapi f xs \<equiv> snd (fold (\<lambda>x (i, ys). (i + 1, ys @ [f i x])) xs (0, []))"

lemma mapi_map2[simp]: "mapi f xs = map2 f [0..<length xs] xs"
proof-
  have gen: "snd (fold (\<lambda>x (i, ys). (i + 1, ys @ [f i x])) xs (length ys, ys))
             = ys @ map2 f [length ys..<length ys + length xs] xs" for xs ys
  proof (induction xs arbitrary: ys)
    case (Cons x xs)
    have "[length ys..<length ys + length (x # xs)]
          = length ys # [Suc (length ys)..<length ys + length (x # xs)]"
      using upt_conv_Cons upt_rec by simp
    thus ?case using Cons[of "ys @ [f (length ys) x]"] by simp
  qed simp
  from gen[where ys = "[]"] show "mapi f xs = map2 f [0..<length xs] xs" by simp
qed

find_theorems "?t \<in> set (map ?f ?xs)"

lemma map_obtain: assumes "y \<in> set (map f xs)" obtains x where "y = f x" "x \<in> set xs" using assms by auto

lemma mapi_obtain:
  assumes "y \<in> set (mapi f xs)"
  obtains i x where "y = f i x" "i < length xs" "x \<in> set xs"
proof-
  from assms have "y \<in> set (map2 f [0..<length xs] xs)" by (simp only: mapi_map2)
  then obtain i1 x1 where 1: "y = f i1 x1" "(i1, x1) \<in> set (zip [0..<length xs] xs)" by auto
  then have "i1 \<in> set [0..<length xs]" and 3: "x1 \<in> set xs" using in_set_zipE by meson+
  then have 2: "i1 < length xs" by simp
  from 1 2 3 show thesis using that[where i = i1 and x = x1] by simp
qed


fun to_imp_tc ::
    "vname list \<Rightarrow> thol_ctxt
    \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow> vname list \<Rightarrow> thol
    \<Rightarrow> tcom" where
  (* f_args: list of argument registers' names
     ctxt: see type def
     bs: names of bound variables
     r: return register name
     stale: variable names that must not be written to *)
  (* fresh variables: need two conditions:
    - must not overwrite live variables
    - must not be overwritten before any use *)
  "to_imp_tc f_args ctxt bs r stale (hIf t1 t2 t3) =
    (let x_var = fresh' stale ''If.x'';
         c1 = to_imp_tc f_args ctxt bs x_var stale t1;
         c2 = to_imp_tc f_args ctxt bs r stale t2;
         c3 = to_imp_tc f_args ctxt bs r stale t3
      in tSeq c1 (tIf x_var c2 c3))" |
  "to_imp_tc f_args ctxt bs r stale (hLet t1 t2) =
    (let x_var = fresh' stale ''Let.x'';
         c1 = to_imp_tc f_args ctxt bs x_var stale t1;
         c2 = to_imp_tc f_args ctxt (x_var # bs) r (x_var # stale) t2
      in tSeq c1 c2)" |
  "to_imp_tc f_args ctxt bs r stale (hLetBound n) = tAssign r (A (V (bs ! n)))" |
  "to_imp_tc f_args ctxt bs r stale (hArg n) = tAssign r (A (V (f_args ! n)))" |
  "to_imp_tc f_args ctxt bs r stale (hNumber n) = tAssign r (A (N n))" |
  (* TODO: call/TAIL cases could be written more nicely, but need termination proofs.
      On the other hand, this more closely follows the written presentation. *)
  "to_imp_tc f_args ctxt bs r stale (hCall g ts) =
    (let (g_args, c_g, g_ret) = ctxt g;
         xs = make_n_fresh (length ts) stale ''Call.x.'';
         cs1 = mapi (\<lambda>i t. to_imp_tc f_args ctxt bs (xs ! i) (xs @ stale) t) ts;
         cs2 = mapi (\<lambda>i t. tAssign (g_args ! i) (A (V (xs ! i)))) ts
      in t_seqs (cs1 @ cs2) (tSeq (tCall c_g g_ret) (tAssign r (A (V g_ret)))))" |
  "to_imp_tc f_args ctxt bs r stale (hTAIL ts) =
    (let xs = make_n_fresh (length ts) stale ''TAIL.x.'';
         cs1 = mapi (\<lambda>i t. to_imp_tc f_args ctxt bs (xs ! i) (xs @ stale) t) ts;
         cs2 = mapi (\<lambda>i t. tAssign (f_args ! i) (A (V (xs ! i)))) ts
      in t_seqs (cs1 @ cs2) tTAIL)"

lemma to_imp_nontail: "non_tail t \<Longrightarrow> \<not> tails (to_imp_tc f_args ctxt bs r stale t)"
proof (induction t arbitrary: bs r stale)
  case (hCall g ts)
  let ?xs = "make_n_fresh (length ts) stale ''Call.x.''"
  let ?cs1 = "mapi (\<lambda>i t. to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t) ts"
  let ?cs2 = "mapi (\<lambda>i t. tAssign (args_from_ctxt ctxt g ! i) (A (V (?xs ! i)))) ts"

  have 1: "\<forall>s \<in> set ?cs1. \<not> tails s"
  proof
    fix s
    assume 1: "s \<in> set ?cs1"
    obtain i t where "s = to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t" "t \<in> set ts"
      using mapi_obtain[OF 1] by blast
    with hCall show "\<not> tails s" by simp
  qed
  have 2: "\<forall>s \<in> set ?cs2. \<not> tails s" apply (subst mapi_map2) apply simp apply (subst split_beta) by simp

  show ?case
    apply (simp only: to_imp_tc.simps Let_def split_beta)
    apply (rule non_tails_tseqs) prefer 2 apply simp
    thm ball_Un
    apply (simp only: set_append ball_Un, standard)
    using 1 apply simp using 2 apply simp
    done
qed (simp_all add: Let_def) (* why do all the other cases go through by simp ???? TODO: figure it out and clean up these proofs *)

lemma to_imp_invar: "tailrec t \<Longrightarrow> invar (to_imp_tc f_args ctxt bs r stale t)"
proof (induction t arbitrary: bs r stale)
  case (hCall g ts)
  let ?xs = "make_n_fresh (length ts) stale ''Call.x.''"
  let ?cs1 = "mapi (\<lambda>i t. to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t) ts"
  let ?cs2 = "mapi (\<lambda>i t. tAssign (fst (ctxt g) ! i) (A (V (?xs ! i)))) ts"

  have 1: "\<forall>s \<in> set ?cs1. \<not> tails s"
  proof
    fix s
    assume 1: "s \<in> set ?cs1"
    obtain i t where "s = to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t" "t \<in> set ts"
      using mapi_obtain[OF 1] by blast
    with hCall to_imp_nontail show "\<not> tails s" by simp
  qed
  have 2: "\<forall>s \<in> set ?cs2. \<not> tails s" apply (subst mapi_map2) apply simp apply (subst split_beta) by simp

  show ?case
    apply (simp only: to_imp_tc.simps Let_def split_beta)
    apply (rule invar_tseqs) prefer 2 apply simp
    apply (simp only: set_append ball_Un, standard)
    using 1 apply simp using 2 apply simp
    done
next
  case (hTAIL ts)
  let ?xs = "make_n_fresh (length ts) stale ''TAIL.x.''"
  let ?cs1 = "mapi (\<lambda>i t. to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t) ts"
  let ?cs2 = "mapi (\<lambda>i t. tAssign (f_args ! i) (A (V (?xs ! i)))) ts"

  have 1: "\<forall>s \<in> set ?cs1. \<not> tails s"
  proof
    fix s
    assume 1: "s \<in> set ?cs1"
    obtain i t where "s = to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t" "t \<in> set ts"
      using mapi_obtain[OF 1] by blast
    with hTAIL to_imp_nontail show "\<not> tails s" by simp
  qed
  have 2: "\<forall>s \<in> set ?cs2. \<not> tails s" apply (subst mapi_map2) apply simp apply (subst split_beta) by simp

  show ?case
    apply (simp only: to_imp_tc.simps Let_def)
    apply (rule invar_tseqs) prefer 2 apply simp
    apply (simp only: set_append ball_Un, standard)
    using 1 apply simp using 2 apply simp
    done
qed (simp_all add: Let_def to_imp_nontail)

(* TODO: rename our tailrec \<rightarrow> h_invar, non_tail \<rightarrow> \<not> h_tails or the likes *)

fun h_calls where
  "h_calls (hLet t1 t2) = h_calls t1 @ h_calls t2" |
  "h_calls (hLetBound _) = []" |
  "h_calls (hArg _) = []" |
  "h_calls (hNumber _) = []" |
  "h_calls (hIf t1 t2 t3) = h_calls t1 @ h_calls t2 @ h_calls t3" |
  "h_calls (hCall f ts) = f # concat (map h_calls ts)" |
  "h_calls (hTAIL ts) = concat (map h_calls ts)"

definition "reserved_regs f_args ctxt bs t =
    (f_args @ bs @ concat (map (fst o ctxt) (h_calls t)) @ map (snd o snd o ctxt) (h_calls t))"

(* mark argument/return registers of all called functions and of f itself as stale *)
definition "to_imp_tc' f_args ctxt bs r t =
  to_imp_tc f_args ctxt bs r (reserved_regs f_args ctxt bs t) t"
(* TODO: right-assoc ? *)

definition "h_let_1 = hLet (hNumber 7) (hLetBound 0)"
value "to_imp_tc_1 [] null ''r'' h_let_1"

definition "h_call_1 = hCall ''g'' [hNumber 7, hNumber 5]"
value "to_imp_tc_1 [] (null(''g'' := ([''g.x1'', ''g.x2''], Assign ''g.r'' (A (V ''g.x1'')), ''g.r''))) ''r'' h_call_1"

definition "com_plus = ([''plus.x'', ''plus.y''], Assign ''plus.ret'' (Plus (V ''plus.x'') (V ''plus.y'')), ''plus.ret'')"
definition "h_sum3 = hLet (hCall ''plus'' [hArg 0, hArg 1]) (hCall ''plus'' [hLetBound 0, hArg 2])"
value "to_imp_tc_1 [''x'', ''y'', ''z''] (null(''plus'' := com_plus)) ''r'' h_sum3"


definition "time_thol f reg (t :: thol) vs_b vs_arg z0 = (\<exists>v. \<exists>z. z \<le> z0 \<and> (f,reg) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup>z\<^esup> v)"
definition "time_imp c (p :: tcom) s z0 = (\<exists>s'. \<exists>z. z \<le> z0 \<and> c \<turnstile> (p,s) \<Rightarrow>\<^bsup>z\<^esup> s')"


definition "t_thol fcs (s's :: state list) = (sum_map (\<lambda>((f_i, _), s'_i). f_i s'_i) (zip fcs s's) :: nat)"
definition "t_tcom fcs (k :: nat) (s's :: state list) = k + sum_map (\<lambda>((f_i, c_i), s'_i). c_i * f_i s'_i) (zip fcs s's)"

lemma t_thol_sum1: "f s' + t_thol fcs s's = t_thol ((f, c) # fcs) (s' # s's)"
  unfolding t_thol_def by (simp add: zip_Cons)

(*
thm list_induct2'
find_theorems "(\<And>x1 x2 y1 y2. ?P x2 y2 \<Longrightarrow> ?P (x1 # x2) (y1 # y2) )"

lemma t_thol_sum: "t_thol fcs1 s's1 + t_thol fcs2 s's2 = t_thol (fcs1 @ fcs2) (s's1 @ s's2)"
  unfolding t_thol_def sum_map_def using t_thol_sum1 apply (induction fcs1 s's1 rule: list_induct2')
  apply simp different lengths... *)

abbreviation "lookups names (s :: state) \<equiv> map s names"

definition "is_call_in t f = (f \<in> set (h_calls t))"

term time_to_tail term ttime_to_tail
thm time_to_tail ttime_to_tail


fun tstruct_k :: "tcom \<Rightarrow> nat" where
  "tstruct_k tSKIP = 1" |
  "tstruct_k (tAssign _ _) = 2" |
  "tstruct_k (tSeq c1 c2) = tstruct_k c1 + tstruct_k c2 + 1" |
  "tstruct_k (tIf x c1 c2) = max (tstruct_k c1) (tstruct_k c2) + 1" |
  "tstruct_k (tCall _ _) = 0" |
  "tstruct_k tTAIL = 5"



end
