theory HOL_TCN_Timing
  imports "HOL-Library.Log_Nat" IMP_Tailcall Fresh
begin

(* HOL-TCN *)
datatype
  thol = hLet thol thol
  | hLetBound nat
  | hArg nat
  | hNumber nat
  | hIf thol thol thol
  | hCall vname "thol list"
  | hTAIL "thol list"


(* function name \<Rightarrow> (function \<times> timing function) *)
type_synonym thol_reg = "vname \<Rightarrow> ((nat list \<Rightarrow> nat) \<times> (nat list \<Rightarrow> nat))"
abbreviation "f_from_reg (reg :: thol_reg) name \<equiv> fst (reg name)"
abbreviation "T_f_from_reg (reg :: thol_reg) name \<equiv> snd (reg name)"

(* function name \<Rightarrow> (argument registers' names \<times> IMP command \<times> return register's name *)
type_synonym thol_ctxt = "vname \<Rightarrow> (vname list \<times> com \<times> vname)"
abbreviation "args_from_ctxt (ctxt :: thol_ctxt) name \<equiv> fst (ctxt name)"
abbreviation "com_from_ctxt (ctxt :: thol_ctxt) name \<equiv> fst (snd (ctxt name))"
abbreviation "ret_from_ctxt (ctxt :: thol_ctxt) name \<equiv> snd (snd (ctxt name))"
(* TODO: use these abbrev. *)

definition "null = (\<lambda>_. undefined)"

lemma tdeterm:
  assumes "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z1\<^esup> t1"
  assumes "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z2\<^esup> t2"
  shows "z1 = z2" "t1 = t2"
  using assms apply (induction arbitrary: z2 t2 rule: tbig_step_t.induct)
               apply blast apply blast apply blast apply blast apply blast apply blast
         apply fastforce
  apply (meson tIf_tE)
       apply fastforce
  using bot_nat_0.not_eq_extremum apply blast
  using determ apply blast
  using determ apply blast
  apply (metis tTail_tE)
  apply (metis tTail_tE)
  done
 (* TODO cleanup *)


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
          \<Longrightarrow> (f,reg) \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>z''\<^esup> v'"

print_theorems

(* code_pred [show_modes] hbig_step_t . (* can't handle the universal quantifier *) *)

inductive_cases hLet_case [elim!]: "env \<turnstile> (hLet t1 t2,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hLetBound_case [elim!]: "env \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hArg_case [elim!]: "env \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hNumber_case [elim!]: "env \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hIf_case [elim!]: "env \<turnstile> (hIf t1 t2 t3,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hCall_case [elim!]: "(f,reg) \<turnstile> (hCall g ts,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hTAIL_case [elim!]: "(f,reg) \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
lemmas hbig_step_t_cases = hLet_case hLetBound_case hArg_case hNumber_case hIf_case hCall_case hTAIL_case


lemma plus_eqI:
  assumes "x1 = x2"
  assumes "y1 = y2"
  shows "x1 + y1 = x2 + y2"
  using assms by simp

lemma list_eq_by_zip:
  assumes "length xs = length ys"
  assumes "\<forall>(x,y) \<in> set (zip xs ys). x = y"
  shows "xs = ys"
  using assms by (induction rule: list_induct2) simp_all

abbreviation "sum_map f xs \<equiv> sum_list (map f xs)"

lemma sum_map_concat: "sum_map f (concat xss) = sum_list (concat (map (map f) xss))"
  using map_concat by metis

(* todo: rename bs to vs_b, rename xs to vs_arg, change bs/xs order *)
fun eval_non_tail :: "thol_reg \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> thol \<Rightarrow> nat" where
  "eval_non_tail reg bs xs (hLet t1 t2) = eval_non_tail reg ((eval_non_tail reg bs xs t1) # bs) xs t2" |
  "eval_non_tail reg bs xs (hLetBound n) = bs ! n" |
  "eval_non_tail reg bs xs (hArg n) = xs ! n" |
  "eval_non_tail reg bs xs (hNumber n) = n" |
  "eval_non_tail reg bs xs (hIf t1 t2 t3) = (
    if eval_non_tail reg bs xs t1 \<noteq> 0
    then eval_non_tail reg bs xs t2
    else eval_non_tail reg bs xs t3)" |
  "eval_non_tail reg bs xs (hCall g ts) = f_from_reg reg g (map (eval_non_tail reg bs xs) ts)" |
  "eval_non_tail _ _ _ (hTAIL _) = undefined"

fun eval_to_tail :: "thol_reg \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> thol \<Rightarrow> nat list option" where
  "eval_to_tail reg bs xs (hLet t1 t2) = eval_to_tail reg (eval_non_tail reg bs xs t1 # bs) xs t2" |
  "eval_to_tail reg bs xs (hLetBound n) = None" |
  "eval_to_tail reg bs xs (hArg n) = None" |
  "eval_to_tail reg bs xs (hNumber n) = None" |
  "eval_to_tail reg bs xs (hIf t1 t2 t3) = (
    if eval_non_tail reg bs xs t1 \<noteq> 0
    then eval_to_tail reg bs xs t2
    else eval_to_tail reg bs xs t3)" |
  "eval_to_tail reg bs xs (hCall g ts) = None" |
  "eval_to_tail reg bs xs (hTAIL ts) = Some (map (eval_non_tail reg bs xs) ts)"

fun time_to_tail :: "thol_reg \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> thol \<Rightarrow> (string \<times> nat list) list" where
  "time_to_tail reg bs xs (hLet t1 t2) =
    time_to_tail reg bs xs t1 @
    time_to_tail reg ((eval_non_tail reg bs xs t1) # bs) xs t2" |
  "time_to_tail reg bs xs (hLetBound n) = []" |
  "time_to_tail reg bs xs (hArg n) = []" |
  "time_to_tail reg bs xs (hNumber n) = []" |
  "time_to_tail reg bs xs (hIf t1 t2 t3) =
    time_to_tail reg bs xs t1 @ (
      if eval_non_tail reg bs xs t1 \<noteq> 0
      then time_to_tail reg bs xs t2
      else time_to_tail reg bs xs t3)" |
  "time_to_tail reg bs xs (hCall g ts) =
    concat (map (time_to_tail reg bs xs) ts) @
    [(g, map (eval_non_tail reg bs xs) ts)]" |
  "time_to_tail reg bs xs (hTAIL ts) = concat (map (time_to_tail reg bs xs) ts)"

value "time_to_tail null [] [] (hCall ''r'' [hNumber 9])"
value "eval_to_tail null [1] [5] (hTAIL [hLetBound 0, hArg 0])"

fun non_tail where
  "non_tail (hTAIL _) = False" |
  "non_tail (hLet t1 t2) = (non_tail t1 \<and> non_tail t2)" |
  "non_tail (hIf t1 t2 t3) = (non_tail t1 \<and> non_tail t2 \<and> non_tail t3)" |
  "non_tail (hCall g ts) = (\<forall>t \<in> set ts. non_tail t)" |
  "non_tail _ = True"

fun tailrec where
  "tailrec (hLet t1 t2) = (non_tail t1 \<and> tailrec t2)" |
  "tailrec (hIf t1 t2 t3) = (non_tail t1 \<and> tailrec t2 \<and> tailrec t3)" |
  "tailrec (hCall g ts) = (\<forall>t \<in> set ts. non_tail t)" |
  "tailrec (hTAIL ts) = (\<forall>t \<in> set ts. non_tail t)" |
  "tailrec _ = True"

lemma set_map:
  assumes "\<forall>x \<in> set xs. P (f x)"
  shows "\<forall>y \<in> set (map f xs). P y"
  using assms by simp

(* not really commutative.... *)
lemma set_zip_com:
  assumes "\<forall>(x,y) \<in> set (zip xs ys). P x y"
  shows "\<forall>(y,x) \<in> set (zip ys xs). P x y"
  using assms by (induction xs ys rule: list_induct2') simp_all

lemma set_zip_com':
  assumes "(x, y) \<in> set (zip xs ys)"
  shows "(y, x) \<in> set (zip ys xs)"
  using assms by (metis in_set_zip prod.sel(1,2))

lemma set_zip_assoc1':
  assumes "(x,y,z) \<in> set (zip xs (zip ys zs))"
  shows "((x,y),z) \<in> set (zip (zip xs ys) zs)"
  using assms by (smt (verit) in_set_zip length_zip min_less_iff_conj nth_zip prod.sel(1,2))

lemma set_zip_assoc2':
  assumes "((x,y),z) \<in> set (zip (zip xs ys) zs)"
  shows "(x,y,z) \<in> set (zip xs (zip ys zs))"
  using assms by (smt (verit) in_set_zip length_zip min_less_iff_conj nth_zip prod.sel(1,2))

lemma set_zip_rot:
  assumes "(x,y,z) \<in> set (zip xs (zip ys zs))"
  shows "(y,z,x) \<in> set (zip ys (zip zs xs))"
  using assms by (smt (verit) in_set_zip length_zip min_less_iff_conj nth_zip prod.sel(1,2))

lemma set_zip_rot2:
  assumes "(x,y,z) \<in> set (zip xs (zip ys zs))"
  shows "(y,x,z) \<in> set (zip ys (zip xs zs))"
  using assms by (smt (verit) in_set_zip length_zip min_less_iff_conj nth_zip prod.sel(1,2))


lemma set_zip_assoc1:
  assumes "\<forall>(x,y,z) \<in> set (zip xs (zip ys zs)). P x y z"
  shows "\<forall>((x,y),z) \<in> set (zip (zip xs ys) zs). P x y z"
  using assms apply (induction xs "zip ys zs" rule: list_induct2') apply simp_all
   apply (induction ys zs rule: list_induct2') apply simp_all
   apply (induction ys zs rule: list_induct2') apply simp_all
  by (metis list.exhaust list.set_cases list.simps(3) not_Cons_self2 zip_eq_Nil_iff) (* aaaa *)

lemma set_zip_assoc2:
  assumes "\<forall>((x,y),z) \<in> set (zip (zip xs ys) zs). P x y z"
  shows "\<forall>(x,y,z) \<in> set (zip xs (zip ys zs)). P x y z"
  using assms apply (induction xs "zip ys zs" rule: list_induct2') apply simp_all
   apply (induction ys zs rule: list_induct2') apply simp_all
   apply (induction ys zs rule: list_induct2') apply simp_all
  by (metis list.exhaust list.set_cases list.simps(3) not_Cons_self2 zip_eq_Nil_iff) (* aaaa *)

lemma set_zip_drop:
  assumes "length xs \<le> length ys"
  assumes "\<forall>(x,y) \<in> set (zip xs ys). P x"
  shows "\<forall>x \<in> set xs. P x"
  using assms by (induction xs ys rule: list_induct2') simp_all

lemma map2_zip: "map (\<lambda>(x, y). (f x, g y)) (zip xs ys) = zip (map f xs) (map g ys)"
  by (induction xs ys rule: list_induct2') simp_all

lemma map2_zip1: "map (\<lambda>(x, y). (f x, y)) (zip xs ys) = zip (map f xs) ys"
  using map2_zip[where g = id] by auto

lemma map2_zip2: "map (\<lambda>(x, y). (x, g y)) (zip xs ys) = zip xs (map g ys)"
  using map2_zip[where f = id] by auto


lemma set_in_I2:
  assumes "\<And>x y. (x, y) \<in> xys \<Longrightarrow> P x y"
  shows "\<forall>(x, y) \<in> xys. P x y"
  using assms by blast

lemma eval_non_tail:
  assumes "non_tail t"
  assumes "(f,reg) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup>z\<^esup> v"
  shows "v = eval_non_tail reg vs_b vs_arg t"
  using assms proof (induction t arbitrary: vs_b z v)
  case (hLet t1 t2)
  then show ?case using hLet_case by force
next
  case (hLetBound n)
  then show ?case apply simp using hbig_step_t.cases by blast
next
  case (hArg n)
  then show ?case apply simp using hbig_step_t.cases by blast
next
  case (hNumber n)
  then show ?case apply simp using hbig_step_t.cases by blast
next
  case (hIf t1 t2 t3)
  then obtain z1 v1 where *: "(f,reg) \<turnstile> (t1,vs_b,vs_arg) \<Rightarrow>\<^bsup>z1\<^esup> v1" using hIf_case by blast
  then show ?case
  proof (cases "v1 = 0")
    case False
    then show ?thesis using hIf_case hIf *
      by (metis (no_types, lifting) eval_non_tail.simps(5) non_tail.simps(3))
  next
    case True
    then show ?thesis using hIf_case hIf *
      by (smt (verit) eval_non_tail.simps(5) less_numeral_extra(3) non_tail.simps(3))
    qed
next
  case (hCall vg ts)

  then obtain g T_g zs vs where
    reg: "reg vg = (g, T_g)"
    and len_zs: "length zs = length ts" and len: "length vs = length ts"
    and args: "\<And>ti vi zi. (ti, zi, vi) \<in> set (zip ts (zip zs vs)) \<longrightarrow> (f,reg) \<turnstile> (ti,vs_b,vs_arg) \<Rightarrow>\<^bsup>zi\<^esup> vi"
    and g: "g vs = v"
    using hCall_case by blast

  from len len_zs have lens: "length (zip vs ts) = length zs" by simp

  have 1: "f_from_reg reg vg = g" using reg by simp
  have 2: "vs = map (eval_non_tail reg vs_b vs_arg) ts"
  proof (rule list_eq_by_zip[OF _ set_in_I2])
    show "length vs = length (map (eval_non_tail reg vs_b vs_arg) ts)"
      using len by simp
  next
    fix vi v'

    assume 1: "(vi, v') \<in> set (zip vs (map (eval_non_tail reg vs_b vs_arg) ts))"

    from 1 have "(vi, v') \<in> set (map (\<lambda>(vi, ti). (vi, eval_non_tail reg vs_b vs_arg ti)) (zip vs ts))"
      apply (subst map2_zip2) by simp
    then obtain ti where b: "(vi, ti) \<in> set (zip vs ts)" and *: "v' = eval_non_tail reg vs_b vs_arg ti"
      using set_map by auto

    from b obtain zi where "((vi, ti), zi) \<in> set (zip (zip vs ts) zs)"
      using in_set_impl_in_set_zip1[OF lens] by auto
    then have "(ti, zi, vi) \<in> set (zip ts (zip zs vs))"
      using set_zip_com' set_zip_assoc1' by metis
    with args have 3: "(f,reg) \<turnstile> (ti,vs_b,vs_arg) \<Rightarrow>\<^bsup>zi\<^esup> vi" by simp

    have 1: "ti \<in> set ts" using set_zip_rightD[OF b] .
    then have 2: "non_tail ti" using hCall by simp
    from hCall.IH[OF 1 2 3] have vi: "vi = eval_non_tail reg vs_b vs_arg ti" by simp

    show "vi = v'" using vi * by simp
  qed

  then show ?case using g 1 2 by simp
next
  case (hTAIL ts)
  then show ?case by simp
qed

definition "interp_time1 reg g vs_arg_g = T_f_from_reg reg g vs_arg_g"
definition "interp_time reg = sum_map (\<lambda>(g, vs_arg_g). interp_time1 reg g vs_arg_g)"

lemma interp_time_append[simp]:
  "interp_time reg (xs @ ys) = interp_time reg xs + interp_time reg ys"
  unfolding interp_time_def by simp
lemma interp_time_concat_is_sum_map:
  "interp_time reg (concat xss) = sum_list (map (interp_time reg) xss)"
  unfolding interp_time_def by (induction xss) auto


(* TODO: find general lemma that subsumes eval_arg_values/eval_arg_times *)
lemma eval_arg_values:
  assumes non_tail: "\<forall>t \<in> set ts. non_tail t"
  assumes len_zs: "length zs = length ts" and len_vs: "length vs = length ts"
  assumes args: "\<And>ti vi zi. (ti, zi, vi) \<in> set (zip ts (zip zs vs)) \<longrightarrow> (f,reg) \<turnstile> (ti,vs_b,vs_arg) \<Rightarrow>\<^bsup>zi\<^esup> vi"
  shows "vs = map (eval_non_tail reg vs_b vs_arg) ts"
  proof (rule list_eq_by_zip[OF _ set_in_I2])
    show "length vs = length (map (eval_non_tail reg vs_b vs_arg) ts)"
      using len_vs by simp
  next
    fix vi v'

    assume 1: "(vi, v') \<in> set (zip vs (map (eval_non_tail reg vs_b vs_arg) ts))"

    from 1 have "(vi, v') \<in> set (map (\<lambda>(vi, ti). (vi, eval_non_tail reg vs_b vs_arg ti)) (zip vs ts))"
      apply (subst map2_zip2) by simp
    then obtain ti where b: "(vi, ti) \<in> set (zip vs ts)" and *: "v' = eval_non_tail reg vs_b vs_arg ti"
      using set_map by auto

    from len_zs len_vs have "length (zip vs ts) = length zs" by simp
    with b obtain zi where "((vi, ti), zi) \<in> set (zip (zip vs ts) zs)"
      using in_set_impl_in_set_zip1 by metis
    then have "(ti, zi, vi) \<in> set (zip ts (zip zs vs))"
      using set_zip_com' set_zip_assoc1' by metis
    with args have 3: "(f,reg) \<turnstile> (ti,vs_b,vs_arg) \<Rightarrow>\<^bsup>zi\<^esup> vi" by simp

    have "ti \<in> set ts" using set_zip_rightD[OF b] .
    then have 2: "non_tail ti" using non_tail by simp
    from eval_non_tail[OF 2 3] have vi: "vi = eval_non_tail reg vs_b vs_arg ti" .

    show "vi = v'" using vi * by simp
  qed

lemma eval_arg_times:
  assumes len_zs: "length zs = length ts" and len_vs: "length vs = length ts"
  assumes args: "\<And>ti vi zi. (ti, zi, vi) \<in> set (zip ts (zip zs vs)) \<longrightarrow> (f,reg) \<turnstile> (ti,vs_b,vs_arg) \<Rightarrow>\<^bsup>zi\<^esup> vi"
  assumes time_non_tail: "\<And>z v t. t \<in> set ts \<Longrightarrow> (f,reg) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup>z\<^esup> v \<Longrightarrow> z = interp_time reg (time_to_tail reg vs_b vs_arg t)"
  shows "zs = map (interp_time reg \<circ> time_to_tail reg vs_b vs_arg) ts"
  proof (rule list_eq_by_zip[OF _ set_in_I2])
    show "length zs = length (map (interp_time reg \<circ> time_to_tail reg vs_b vs_arg) ts)"
      using len_zs by simp
  next
    fix zi z'

    assume 1: "(zi, z') \<in> set (zip zs (map (interp_time reg \<circ> time_to_tail reg vs_b vs_arg) ts))"

    from 1 have "(zi, z') \<in> set (map (\<lambda>(zi, ti). (zi, (interp_time reg \<circ> time_to_tail reg vs_b vs_arg) ti)) (zip zs ts))"
      apply (subst map2_zip2) by simp
    then obtain ti where b: "(zi, ti) \<in> set (zip zs ts)" and *: "z' = interp_time reg (time_to_tail reg vs_b vs_arg ti)"
      using set_map by auto

    from len_zs len_vs have "length (zip zs ts) = length vs" by simp
    with b obtain vi where "((zi, ti), vi) \<in> set (zip (zip zs ts) vs)"
      using in_set_impl_in_set_zip1 by metis
    then have "(ti, zi, vi) \<in> set (zip ts (zip zs vs))"
      using set_zip_com' set_zip_rot set_zip_rot2 by metis
    with args have 3: "(f,reg) \<turnstile> (ti,vs_b,vs_arg) \<Rightarrow>\<^bsup>zi\<^esup> vi" by simp

    have 1: "ti \<in> set ts" using set_zip_rightD[OF b] .
    from time_non_tail[OF 1 3] have vi: "zi = interp_time reg (time_to_tail reg vs_b vs_arg ti)"
      using "3" eval_non_tail by auto
(* TODO: clean up *)

    show "zi = z'" using vi * by simp
  qed

lemma time_non_tail:
  assumes "non_tail t"
  assumes "(f,reg) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup>z\<^esup> v"
  shows "z = interp_time reg (time_to_tail reg vs_b vs_arg t)"
using assms proof (induction t arbitrary: vs_b z v)
  case (hLet t1 t2)
  then show ?case
  proof (cases rule: hLet_case[OF hLet(4)])
    case (1 z1 v1 z2)
    with hLet show ?thesis using eval_non_tail by force
  qed
next
  case (hLetBound n)
  then show ?case unfolding interp_time_def by auto
next
  case (hArg n)
  then show ?case unfolding interp_time_def by auto
next
  case (hNumber n)
  then show ?case unfolding interp_time_def by auto
next
  case (hIf t1 t2 t3)
  show ?case
  proof (cases rule: hIf_case[OF hIf.prems(2)])
    case (1 z1 v1 z2)
    with hIf show ?thesis using eval_non_tail by force
  next
    case (2 z1 z2)
    with hIf show ?thesis using eval_non_tail by force
  qed
next
  case (hCall vg ts)
  thm hCall.IH
  then show ?case
    thm hCall_case[OF hCall.prems(2)]
  proof (cases rule: hCall_case[OF hCall.prems(2)])
    case (1 g T_g zs vs)

    have g: "f_from_reg reg vg = g" using 1 by simp
  
    from hCall have "\<forall>t\<in>set ts. non_tail t" by simp
    with 1 have "vs = map (eval_non_tail reg vs_b vs_arg) ts" (* 2 *)
      using eval_arg_values by blast
    then have *: "T_g vs = interp_time reg [(vg, map (eval_non_tail reg vs_b vs_arg) ts)]"
      unfolding interp_time_def interp_time1_def using 1 by simp

    have "zs = map (interp_time reg \<circ> time_to_tail reg vs_b vs_arg) ts"
      apply (rule eval_arg_times[where vs = vs])
      using 1 hCall by simp_all
    then have **: "sum_list zs = interp_time reg (concat (map (time_to_tail reg vs_b vs_arg) ts))"
      by (simp add: interp_time_concat_is_sum_map)

    show ?thesis using 1 * ** by simp
  qed
next
  case (hTAIL ts)
  then show ?case by simp
qed


definition "has_time_to_tail reg t vs_b vs_arg f vs_arg' v z = (\<exists>z'.
  z = 1 + interp_time reg (time_to_tail reg vs_b vs_arg t) + z' \<and> (f,reg) \<turnstile> (f,[],vs_arg') \<Rightarrow>\<^bsup>z'\<^esup> v)"

lemma has_time_to_tailI:
  assumes "z = 1 + interp_time reg (time_to_tail reg vs_b vs_arg t) + z'"
  assumes "(f,reg) \<turnstile> (f,[],vs_arg') \<Rightarrow>\<^bsup>z'\<^esup> v"
  shows "has_time_to_tail reg t vs_b vs_arg f vs_arg' v z"
  unfolding has_time_to_tail_def using assms by blast

theorem time_to_tail:
  assumes "tailrec t"
  assumes "(f,reg) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup>z\<^esup> v"
  assumes "eval_to_tail reg vs_b vs_arg t = Some vs_arg'"
  shows "has_time_to_tail reg t vs_b vs_arg f vs_arg' v z"
using assms proof (induction t arbitrary: vs_b z)
  case (hLet t1 t2)
  from \<open>tailrec (hLet t1 t2)\<close> have "non_tail t1" "tailrec t2" by simp_all
  from \<open>(f, reg) \<turnstile> (hLet t1 t2, vs_b, vs_arg) \<Rightarrow>\<^bsup>z\<^esup> v\<close>
  obtain z1 v1 z2
    where t1: "(f, reg) \<turnstile> (t1,vs_b,vs_arg) \<Rightarrow>\<^bsup>z1\<^esup> v1"
      and t2: "(f, reg) \<turnstile> (t2,v1#vs_b,vs_arg) \<Rightarrow>\<^bsup>z2\<^esup> v"
      and z: "z = z1+z2"
    using hLet_case by blast

  from \<open>non_tail t1\<close> t1 have z1: "z1 = interp_time reg (time_to_tail reg vs_b vs_arg t1)"
    using time_non_tail by blast

  from \<open>non_tail t1\<close> t1 have v1: "v1 = eval_non_tail reg vs_b vs_arg t1"
    using eval_non_tail by blast
  with hLet.prems(3) have "eval_to_tail reg (v1 # vs_b) vs_arg t2 = Some vs_arg'" by simp
  then have "has_time_to_tail reg t2 (v1 # vs_b) vs_arg f vs_arg' v z2"
    using hLet.IH(2) \<open>tailrec t2\<close> t2 by blast
  then obtain z'
    where "z2 = 1 + interp_time reg (time_to_tail reg (v1 # vs_b) vs_arg t2) + z'"
      and z': "(f,reg) \<turnstile> (f,[],vs_arg') \<Rightarrow>\<^bsup>z'\<^esup> v"
    unfolding has_time_to_tail_def by blast
  with v1 have z2: "z2 =
    1 + interp_time reg (time_to_tail reg (eval_non_tail reg vs_b vs_arg t1 # vs_b) vs_arg t2) + z'"
    by blast

  have t: "interp_time reg (time_to_tail reg vs_b vs_arg (hLet t1 t2)) =
    interp_time reg (time_to_tail reg vs_b vs_arg t1)
    + interp_time reg (time_to_tail reg (eval_non_tail reg vs_b vs_arg t1 # vs_b) vs_arg t2)"
    using interp_time_append by auto

  show ?case
    apply (rule has_time_to_tailI[where z' = z'])
    by (simp only: z z1 z2 t) (rule z')
next
  case (hLetBound x)
  then show ?case by simp
next
  case (hArg x)
  then show ?case by simp
next
  case (hNumber x)
  then show ?case by simp
next
  case (hIf t1 t2 t3)
  from \<open>tailrec (hIf t1 t2 t3)\<close> have "non_tail t1" "tailrec t2" "tailrec t3" by simp_all

  show ?case
  proof (cases rule: hIf_case[OF \<open>(f,reg) \<turnstile> (hIf t1 t2 t3,vs_b,vs_arg) \<Rightarrow>\<^bsup>z\<^esup> v\<close>])
    case (1 z1 v1 z2)

    have z1: "z1 = interp_time reg (time_to_tail reg vs_b vs_arg t1)"
      using \<open>non_tail t1\<close> 1(2) time_non_tail by blast

    have v1: "eval_non_tail reg vs_b vs_arg t1 \<noteq> 0"
      using \<open>non_tail t1\<close> 1(2,3) eval_non_tail by auto
    have "eval_to_tail reg vs_b vs_arg t2 = Some vs_arg'"
      using hIf.prems(3) v1 by simp
    then have "has_time_to_tail reg t2 vs_b vs_arg f vs_arg' v z2"
      using hIf.IH(2) \<open>tailrec t2\<close> 1(4) by blast
    then obtain z'
      where z2: "z2 = 1 + interp_time reg (time_to_tail reg vs_b vs_arg t2) + z'"
        and z': "(f,reg) \<turnstile> (f,[],vs_arg') \<Rightarrow>\<^bsup>z'\<^esup> v"
      unfolding has_time_to_tail_def by blast

    have t: "interp_time reg (time_to_tail reg vs_b vs_arg (hIf t1 t2 t3)) =
      interp_time reg (time_to_tail reg vs_b vs_arg t1)
      + interp_time reg (time_to_tail reg vs_b vs_arg t2)"
      using interp_time_append v1 by auto
    
    show ?thesis
      apply (rule has_time_to_tailI[where z' = z'])
      by (simp only: \<open>z = z1 + z2\<close> z1 z2 t) (rule z')
  next
    case (2 z1 z2)

    have z1: "z1 = interp_time reg (time_to_tail reg vs_b vs_arg t1)"
      using \<open>non_tail t1\<close> 2(2) time_non_tail by blast

    have v1: "0 = eval_non_tail reg vs_b vs_arg t1"
      using \<open>non_tail t1\<close> 2(2) eval_non_tail by blast
    have "eval_to_tail reg vs_b vs_arg t3 = Some vs_arg'"
      using hIf.prems(3) v1 by simp
    then have "has_time_to_tail reg t3 vs_b vs_arg f vs_arg' v z2"
      using hIf.IH(3) \<open>tailrec t3\<close> 2(3) by blast
    then obtain z'
      where z2: "z2 = 1 + interp_time reg (time_to_tail reg vs_b vs_arg t3) + z'"
        and z': "(f,reg) \<turnstile> (f,[],vs_arg') \<Rightarrow>\<^bsup>z'\<^esup> v"
      unfolding has_time_to_tail_def by blast

    have t: "interp_time reg (time_to_tail reg vs_b vs_arg (hIf t1 t2 t3)) =
      interp_time reg (time_to_tail reg vs_b vs_arg t1)
      + interp_time reg (time_to_tail reg vs_b vs_arg t3)"
      using interp_time_append v1 by auto
    
    show ?thesis
      apply (rule has_time_to_tailI[where z' = z'])
      by (simp only: \<open>z = z1 + z2\<close> z1 z2 t) (rule z')
  qed
next
  case (hCall vg ts)
  then show ?case by simp
next
  case (hTAIL ts)

  then obtain zs vs z' where
    len_zs: "length zs = length ts" and len_vs: "length vs = length ts"
    and args: "\<And>ti vi zi. (ti, zi, vi) \<in> set (zip ts (zip zs vs)) \<longrightarrow> (f,reg) \<turnstile> (ti,vs_b,vs_arg) \<Rightarrow>\<^bsup>zi\<^esup> vi"
    and rec: "(f,reg) \<turnstile> (f,[],vs) \<Rightarrow>\<^bsup>z'\<^esup> v"
    and z: "z = sum_list zs + z' + 1"
    using hTAIL_case by auto

  have nt: "\<forall>t \<in> set ts. non_tail t" using hTAIL by simp
  with len_zs len_vs args have "vs = map (eval_non_tail reg vs_b vs_arg) ts"
    using eval_arg_values by blast

  with hTAIL have vs_arg': "vs = vs_arg'" by simp

  show ?case
  proof (rule has_time_to_tailI)
    have "z = sum_list zs + (z' + 1)" using z by simp
    also have "... = interp_time reg (time_to_tail reg vs_b vs_arg (hTAIL ts)) + (z' + 1)"
    proof (rule plus_eqI)
      have "zs = map (interp_time reg \<circ> time_to_tail reg vs_b vs_arg) ts"
        apply (rule eval_arg_times[where vs = vs])
        using len_zs len_vs nt hTAIL time_non_tail args time_non_tail by blast+
      then show "sum_list zs = interp_time reg (time_to_tail reg vs_b vs_arg (hTAIL ts))"
        by (simp add: interp_time_concat_is_sum_map)
    qed simp
    finally show "z = 1 + interp_time reg (time_to_tail reg vs_b vs_arg (hTAIL ts)) + z'" by simp
  next
    show "(f, reg) \<turnstile> (f, [], vs_arg') \<Rightarrow>\<^bsup>z'\<^esup>  v"
      using vs_arg' rec by simp
  qed
qed


fun teval_non_tail :: "state \<Rightarrow> tcom \<Rightarrow> state" where
  "teval_non_tail s tSKIP = s" |
  "teval_non_tail s (tAssign x a) = s(x := aval a s)" |
  "teval_non_tail s (tSeq c1 c2) = teval_non_tail (teval_non_tail s c1) c2" |
  "teval_non_tail s (tIf x c1 c2) = teval_non_tail s (if s x \<noteq> 0 then c1 else c2)" |
  "teval_non_tail s (tCall c x) = s" | (* TODO *)
  "teval_non_tail s tTAIL = undefined"

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
  let ?cs2 = "mapi (\<lambda>i t. tAssign (fst (ctxt g) ! i) (A (V (?xs ! i)))) ts"

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
  unfolding t_thol_def sum_map_def by (simp add: zip_Cons)

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
