theory HOL_TCN_To_IMP
  (* TODO: move file *)
  imports IMP_Tailcall_Traces HOL_TCN_Timing Fresh
begin

(* function name \<Rightarrow> (argument registers' names \<times> IMP command \<times> return register's name *)
type_synonym com_registry = "fun_ref \<Rightarrow> (vname list \<times> com \<times> vname)"
abbreviation "args_from_crgt (crgt :: com_registry) name \<equiv> fst (crgt name)"
abbreviation "com_from_crgt (crgt :: com_registry) name \<equiv> fst (snd (crgt name))"
abbreviation "ret_from_crgt (crgt :: com_registry) name \<equiv> snd (snd (crgt name))"
(* TODO: use these abbrev. *)

definition "null = (\<lambda>_. undefined)"


(* fresh *)

(* let us switch between definitions easily *)
abbreviation "fresh' \<equiv> Fresh.fresh"

(* TODO: this should go in Fresh (but then can't swap out fresh' anymore) *)
definition "make_nth_fresh stale name = fresh' stale o ((@) name) o string_of_nat" 
definition "make_n_fresh stale name n = map (make_nth_fresh stale name) [0..<n]"

lemma inj_make_nth_fresh[simp]: "inj (make_nth_fresh stale name)"
  by (simp add: inj_append2 inj_compose inj_fresh inj_string_of_nat make_nth_fresh_def)

lemma distinct_make_n_fresh[simp]: "distinct (make_n_fresh stale name n)"
  unfolding make_n_fresh_def using distinct_map inj_make_nth_fresh distinct_upt inj_on_subset by blast

lemma make_n_fresh_not_in_stale: "set (make_n_fresh stale name n) \<inter> set stale = {}"
  unfolding make_n_fresh_def make_nth_fresh_def using fresh_not_in_stale by auto

value "make_n_fresh [''f.args.2.0'', ''f.args.2.1'', ''f.args.3.0''] ''f.args.'' 5"


lemma inj_inj_on: fixes A assumes "inj f" shows "inj_on f A" using assms inj_on_subset by auto
(* lemma inj_neq: fixes A assumes "inj_on f A" "x \<noteq> y" "x \<in> A" "y \<in> A" shows "f x \<noteq> f y" using assms  *)
  (* thm inj_on_contraD[where A = UNIV, simplified] *)
lemma none_equal_not_in: fixes A shows "(\<forall>y\<in>A. x \<noteq> y) \<longleftrightarrow> x \<notin> A" by blast
lemma some_equal_in: fixes A shows "(\<exists>y\<in>A. x = y) \<longleftrightarrow> x \<in> A" by blast

(*
find_theorems "_ \<notin> _" "inj_on"

lemma fixes A assumes "inj_on f (insert x A)" "x \<notin> A" shows "f x \<notin> f ` A" using assms by blast *)


(* t_seqs *)

lemma tbig_step_t_tSeq_assoc:
  (* from Compile_HOL_Nat_To_IMP *)
  shows "C \<turnstile> (c1 ;; (c2 ;; c3), s) \<Rightarrow>\<^bsup>t\<^esup> s' \<longleftrightarrow> C \<turnstile> (c1 ;; c2 ;; c3, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  by auto

lemma tbig_step_t_tSeq_Skip_id1[simp]: "f \<turnstile> (tSKIP;; c, s) \<Rightarrow>\<^bsup>Suc z\<^esup> t \<longleftrightarrow> f \<turnstile> (c, s) \<Rightarrow>\<^bsup>z\<^esup> t"
  by fastforce

lemma tbig_step_t_tSeq_Skip_id2[simp]: "f \<turnstile> (c;; tSKIP, s) \<Rightarrow>\<^bsup>Suc z\<^esup> t \<longleftrightarrow> f \<turnstile> (c, s) \<Rightarrow>\<^bsup>z\<^esup> t"
  by fastforce

definition "t_seqs ts = foldr tSeq ts"
abbreviation "t_seqs' ts \<equiv> t_seqs ts tSKIP"
value "t_seqs ([c1, c2, c3]) c4"

lemma t_seqs_nil[simp]: "t_seqs [] c = c" unfolding t_seqs_def by simp
lemma t_seqs_cons[simp]: "t_seqs (c1 # cs) c = c1;; t_seqs cs c" unfolding t_seqs_def by simp

lemma t_seqs_append[simp]: "t_seqs (cs1 @ cs2) c = t_seqs cs1 (t_seqs cs2 c)"
  by (induction cs1) auto

lemmas t_seqs_rewrite = t_seqs_nil t_seqs_cons t_seqs_append

lemma t_seqs_Seq: "f \<turnstile> (t_seqs cs (c1;; c2),s) \<Rightarrow>\<^bsup>z\<^esup> t \<longleftrightarrow> f \<turnstile> (t_seqs cs c1;; c2,s) \<Rightarrow>\<^bsup>z\<^esup> t"
  by (induction cs arbitrary: s z) fastforce+

lemma t_seqs'_snoc: "f \<turnstile> (t_seqs' (cs @ [c]),s) \<Rightarrow>\<^bsup>Suc z\<^esup> t \<longleftrightarrow> f \<turnstile> (t_seqs cs c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
  using t_seqs_Seq by simp

lemma t_seqs'_t_seqs:
  shows "f \<turnstile> (t_seqs' cs;; c,s) \<Rightarrow>\<^bsup>Suc z\<^esup> t \<longleftrightarrow> f \<turnstile> (t_seqs cs c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
proof
  assume "f \<turnstile> (t_seqs cs c, s) \<Rightarrow>\<^bsup>z\<^esup> t" then show "f \<turnstile> (t_seqs' cs;; c, s) \<Rightarrow>\<^bsup>Suc z\<^esup> t"
    by (induction cs arbitrary: s z) fastforce+
next
  assume "f \<turnstile> (t_seqs' cs;; c, s) \<Rightarrow>\<^bsup>Suc z\<^esup> t"
  then show "f \<turnstile> (t_seqs cs c, s) \<Rightarrow>\<^bsup>z\<^esup> t"
  proof (induction cs arbitrary: s z)
    case Nil then show ?case by auto
  next
    case (Cons c1 cs)
    then have "f \<turnstile> (c1;; (t_seqs' cs;; c), s) \<Rightarrow>\<^bsup>Suc z\<^esup>  t" using tbig_step_t_tSeq_assoc by simp
    then obtain z1 s2 z2 where "f \<turnstile> (c1, s) \<Rightarrow>\<^bsup>z1\<^esup> s2" "f \<turnstile> (t_seqs' cs;; c, s2) \<Rightarrow>\<^bsup>Suc z2\<^esup> t" "Suc z = z1 + Suc z2"
      using bigstep_progressE tSeq_tE by metis
    then show ?case using Cons.IH by auto
  qed
qed

lemma t_seqs'_append: "f \<turnstile> (t_seqs' cs1;; t_seqs' cs2,s) \<Rightarrow>\<^bsup>Suc z\<^esup> t \<longleftrightarrow> f \<turnstile> (t_seqs' (cs1 @ cs2),s) \<Rightarrow>\<^bsup>z\<^esup> t"
  using t_seqs'_t_seqs by simp

lemma t_seqs_append_t_seqs': "f \<turnstile> (t_seqs' cs1;; t_seqs' cs2;; c,s) \<Rightarrow>\<^bsup>Suc (Suc z)\<^esup> t \<longleftrightarrow> f \<turnstile> (t_seqs (cs1 @ cs2) c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
  apply (induction cs1)
  apply (simp add: t_seqs'_t_seqs tbig_step_t_tSeq_assoc[symmetric])
  apply (simp add: t_seqs'_append)
  apply (metis t_seqs'_t_seqs t_seqs_cons)
  done

lemmas tbig_step_t_t_seqs_rewrite = t_seqs_Seq t_seqs'_snoc t_seqs'_t_seqs t_seqs'_append t_seqs_append_t_seqs'

(* lemma foldr1_append: assumes "xs \<noteq> []" "ys \<noteq> []" shows "foldr1 f (xs @ ys) = foldr tSeq xs (foldr1 tSeq ys)" *)

lemma invar_tseqs[simp]:
  assumes "\<forall>t \<in> set xs. \<not> IMP_Tailcall.tails t" "IMP_Tailcall.invar x"
  shows "IMP_Tailcall.invar (t_seqs xs x)"
  unfolding t_seqs_def using assms by (induction xs) simp_all
lemma non_tails_tseqs[simp]:
  assumes "\<forall>t \<in> set xs. \<not> IMP_Tailcall.tails t" "\<not> IMP_Tailcall.tails x"
  shows "\<not> IMP_Tailcall.tails (t_seqs xs x)"
  unfolding t_seqs_def using assms by (induction xs) simp_all
(* lemma non_tails_tseqs_append: assumes "\<not> tails (t_seqs xs)" "\<not> tails (t_seqs ys)" shows "\<not> tails (t_seqs (xs @ ys) x)" *)
  (* using assms unfolding t_seqs_def foldr1_def apply (induction xs) apply simp_all *)
  (* apply (cases xs) unfolding t_seqs_def foldr1_def apply simp *)
  (* apply (cases ys) *)
  (* apply simp sledgehammer *)
   (* apply (induction xs) unfolding t_seqs_def foldr1_def apply simp_all *)

abbreviation "mapi' n ys f xs \<equiv> snd (fold (\<lambda>x (i, ys). (i + 1, ys @ [f i x])) xs (n, ys))"
abbreviation "mapi \<equiv> mapi' 0 []"

lemma mapi'_map:
  "mapi' (length ys) ys f xs = ys @ map (\<lambda>i. f i (xs ! (i - length ys))) [length ys..<length ys + length xs]"
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  let ?y = "f (length ys) x"
  have "ys @ map (\<lambda>i. f i ((x # xs) ! (i - length ys))) [length ys..<length ys + length (x # xs)] =
      ys @ ?y # map (\<lambda>i. f i ((x # xs) ! (i - length ys))) [Suc (length ys) ..< length ys + length (x # xs)]"
    using upt_rec by simp
  also have "... = ys @ ?y # map (\<lambda>i. f i (xs ! (i - Suc (length ys)))) [Suc (length ys)..<length ys + length (x # xs)]"
    by (simp add: nth_Cons')
  also have "... = mapi' (length ys) ys f (x # xs)" using Cons[where ys = "ys @ [?y]"] by simp
  finally show ?case by fastforce
qed simp

corollary mapi_map: "mapi f xs = map (\<lambda>i. f i (xs ! i)) [0..<length xs]"
  using mapi'_map[where ys = "[]" and f = f and xs = xs] by simp

lemma mapi'_map2: "mapi' (length ys) ys f xs = ys @ map2 f [length ys..<length ys + length xs] xs"
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  have "[length ys..<length ys + length (x # xs)]
        = length ys # [Suc (length ys)..<length ys + length (x # xs)]"
    using upt_conv_Cons upt_rec by simp
  thus ?case using Cons[of "ys @ [f (length ys) x]"] by simp
qed simp

corollary mapi_map2: "mapi f xs = map2 f [0..<length xs] xs"
  using mapi'_map2[where ys = "[]" and f = f and xs = xs] by simp


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
    "vname list \<Rightarrow> com_registry
    \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow> vname list \<Rightarrow> thol
    \<Rightarrow> tcom" where
  (* f_args: list of argument registers' names
     crgt: see type def
     bs: names of bound variables
     r: return register name
     stale: variable names that must not be written to *)
  (* fresh variables: need two conditions:
    - must not overwrite live variables
    - must not be overwritten before any use *)
  "to_imp_tc f_args crgt bs r stale (hIf t1 t2 t3) =
    (let x_var = fresh' stale ''If.x'';
         c1 = to_imp_tc f_args crgt bs x_var stale t1;
         c2 = to_imp_tc f_args crgt bs r stale t2;
         c3 = to_imp_tc f_args crgt bs r stale t3
      in tSeq c1 (tIf x_var c2 c3))" |
  "to_imp_tc f_args crgt bs r stale (hLet t1 t2) =
    (let x_var = fresh' stale ''Let.x'';
         c1 = to_imp_tc f_args crgt bs x_var stale t1;
         c2 = to_imp_tc f_args crgt (x_var # bs) r (x_var # stale) t2
      in tSeq c1 c2)" |
  "to_imp_tc f_args crgt bs r stale (hLetBound n) = tAssign r (A (V (bs ! n)))" |
  "to_imp_tc f_args crgt bs r stale (hArg n) = tAssign r (A (V (f_args ! n)))" |
  "to_imp_tc f_args crgt bs r stale (hNumber n) = tAssign r (A (N n))" |
  (* TODO: call/TAIL cases could be written more nicely, but need termination proofs.
      On the other hand, this more closely follows the written presentation. *)
  (* could use nth consistently *)
  "to_imp_tc f_args crgt bs r stale (hCall g ts) =
    (let (g_args, c_g, g_ret) = crgt g;
         xs = make_n_fresh stale ''Call.x.'' (length ts);
         cs1 = mapi (\<lambda>i t. to_imp_tc f_args crgt bs (xs ! i) (xs @ stale) t) ts;
         cs2 = map (\<lambda>i. tAssign (g_args ! i) (A (V (xs ! i)))) [0..<length ts]
      in t_seqs (cs1 @ cs2) (tSeq (tCall c_g g_ret) (tAssign r (A (V g_ret)))))" |
  "to_imp_tc f_args crgt bs r stale (hTAIL ts) =
    (let xs = make_n_fresh stale ''TAIL.x.'' (length ts);
         cs1 = mapi (\<lambda>i t. to_imp_tc f_args crgt bs (xs ! i) (xs @ stale) t) ts;
         cs2 = map (\<lambda>i. tAssign (f_args ! i) (A (V (xs ! i)))) [0..<length ts]
      in t_seqs (cs1 @ cs2) tTAIL)"
(*
  "to_imp_tc f_args crgt bs r stale (hCall g ts) =
    (let (g_args, c_g, g_ret) = crgt g;
         xs = make_n_fresh (length ts) stale ''Call.x.'';
         cs1 = mapi (\<lambda>i t. to_imp_tc f_args crgt bs (xs ! i) (xs @ stale) t) ts;
         cs2 = mapi (\<lambda>i t. tAssign (g_args ! i) (A (V (xs ! i)))) ts
      in t_seqs (cs1 @ cs2) (tSeq (tCall c_g g_ret) (tAssign r (A (V g_ret)))))" |
  "to_imp_tc f_args crgt bs r stale (hTAIL ts) =
    (let xs = make_n_fresh (length ts) stale ''TAIL.x.'';
         cs1 = mapi (\<lambda>i t. to_imp_tc f_args crgt bs (xs ! i) (xs @ stale) t) ts;
         cs2 = mapi (\<lambda>i t. tAssign (f_args ! i) (A (V (xs ! i)))) ts
      in t_seqs (cs1 @ cs2) tTAIL)" *)

lemma to_imp_nontail: "\<not> HOL_TCN_Timing.tails t \<Longrightarrow> \<not> IMP_Tailcall.tails (to_imp_tc f_args crgt bs r stale t)"
proof (induction t arbitrary: bs r stale)
  case (hCall g ts)
  let ?xs = "make_n_fresh stale ''Call.x.'' (length ts)"
  let ?cs1 = "mapi (\<lambda>i t. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ stale) t) ts"
  let ?cs2 = "mapi (\<lambda>i t. tAssign (args_from_crgt crgt g ! i) (A (V (?xs ! i)))) ts"

  have 1: "\<forall>s \<in> set ?cs1. \<not> IMP_Tailcall.tails s"
  proof
    fix s
    assume 1: "s \<in> set ?cs1"
    obtain i t where "s = to_imp_tc f_args crgt bs (?xs ! i) (?xs @ stale) t" "t \<in> set ts"
      using mapi_obtain[OF 1] by blast
    with hCall show "\<not> IMP_Tailcall.tails s" by simp
  qed
  have 2: "\<forall>s \<in> set ?cs2. \<not> IMP_Tailcall.tails s" apply (subst mapi_map2) apply simp apply (subst split_beta) by simp

  show ?case
    apply (simp only: to_imp_tc.simps Let_def split_beta)
    apply (rule non_tails_tseqs) prefer 2 apply simp
    thm ball_Un
    apply (simp only: set_append ball_Un, standard)
    using 1 apply simp using 2 apply simp
    done
qed (simp_all add: Let_def) (* why do all the other cases go through by simp ???? TODO: figure it out and clean up these proofs *)

lemma to_imp_invar: "HOL_TCN_Timing.invar t \<Longrightarrow> IMP_Tailcall.invar (to_imp_tc f_args crgt bs r stale t)"
proof (induction t arbitrary: bs r stale)
  case (hCall g ts)
  let ?xs = "make_n_fresh stale ''Call.x.'' (length ts)"
  let ?cs1 = "mapi (\<lambda>i t. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ stale) t) ts"
  let ?cs2 = "mapi (\<lambda>i t. tAssign (fst (crgt g) ! i) (A (V (?xs ! i)))) ts"

  have 1: "\<forall>s \<in> set ?cs1. \<not> IMP_Tailcall.tails s"
  proof
    fix s
    assume 1: "s \<in> set ?cs1"
    obtain i t where "s = to_imp_tc f_args crgt bs (?xs ! i) (?xs @ stale) t" "t \<in> set ts"
      using mapi_obtain[OF 1] by blast
    with hCall to_imp_nontail show "\<not> IMP_Tailcall.tails s" by simp
  qed
  have 2: "\<forall>s \<in> set ?cs2. \<not> IMP_Tailcall.tails s" apply (subst mapi_map2) apply simp apply (subst split_beta) by simp

  show ?case
    apply (simp only: to_imp_tc.simps Let_def split_beta)
    apply (rule invar_tseqs) prefer 2 apply simp
    apply (simp only: set_append ball_Un, standard)
    using 1 apply simp using 2 apply simp
    done
next
  case (hTAIL ts)
  let ?xs = "make_n_fresh stale ''TAIL.x.'' (length ts)"
  let ?cs1 = "mapi (\<lambda>i t. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ stale) t) ts"
  let ?cs2 = "mapi (\<lambda>i t. tAssign (f_args ! i) (A (V (?xs ! i)))) ts"

  have 1: "\<forall>s \<in> set ?cs1. \<not> IMP_Tailcall.tails s"
  proof
    fix s
    assume 1: "s \<in> set ?cs1"
    obtain i t where "s = to_imp_tc f_args crgt bs (?xs ! i) (?xs @ stale) t" "t \<in> set ts"
      using mapi_obtain[OF 1] by blast
    with hTAIL to_imp_nontail show "\<not> IMP_Tailcall.tails s" by simp
  qed
  have 2: "\<forall>s \<in> set ?cs2. \<not> IMP_Tailcall.tails s" apply (subst mapi_map2) apply simp apply (subst split_beta) by simp

  show ?case
    apply (simp only: to_imp_tc.simps Let_def)
    apply (rule invar_tseqs) prefer 2 apply simp
    apply (simp only: set_append ball_Un, standard)
    using 1 apply simp using 2 apply simp
    done
qed (simp_all add: Let_def to_imp_nontail)


definition "reserved_regs f_args crgt bs t =
    (f_args @ bs @ concat (map (args_from_crgt crgt o fst) (calls t)) @ map (ret_from_crgt crgt o fst) (calls t))"

(* mark argument/return registers of all called functions and of f itself as stale *)
definition "to_imp_tc' f_args crgt bs r t =
  to_imp_tc f_args crgt bs r (reserved_regs f_args crgt bs t) t"
(* TODO: right-assoc ? *)

definition "h_let_1 = hLet (hNumber 7) (hLetBound 0)"
value "to_imp_tc' [] null [] ''r'' h_let_1"

definition "h_call_1 = hCall ''g'' [hNumber 7, hNumber 5]"
value "to_imp_tc' [] (null(''g'' := ([''g.x1'', ''g.x2''], Assign ''g.r'' (A (V ''g.x1'')), ''g.r''))) [] ''r'' h_call_1"

definition "com_plus = ([''plus.x'', ''plus.y''], Assign ''plus.ret'' (Plus (V ''plus.x'') (V ''plus.y'')), ''plus.ret'')"
definition "h_sum3 = hLet (hCall ''plus'' [hArg 0, hArg 1]) (hCall ''plus'' [hLetBound 0, hArg 2])"
value "to_imp_tc' [''x'', ''y'', ''z''] (null(''plus'' := com_plus)) [] ''r'' h_sum3"

end