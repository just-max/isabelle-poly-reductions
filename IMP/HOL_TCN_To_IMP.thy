theory HOL_TCN_To_IMP
  (* TODO: move file *)
  imports IMP_Tailcall_Traces HOL_TCN_Timing Fresh
(* "HOL-Library.Log_Nat"  *)
begin

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
  (* could use nth consistently *)
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

lemma to_imp_nontail: "\<not> HOL_TCN_Timing.tails t \<Longrightarrow> \<not> IMP_Tailcall.tails (to_imp_tc f_args ctxt bs r stale t)"
proof (induction t arbitrary: bs r stale)
  case (hCall g ts)
  let ?xs = "make_n_fresh (length ts) stale ''Call.x.''"
  let ?cs1 = "mapi (\<lambda>i t. to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t) ts"
  let ?cs2 = "mapi (\<lambda>i t. tAssign (args_from_ctxt ctxt g ! i) (A (V (?xs ! i)))) ts"

  have 1: "\<forall>s \<in> set ?cs1. \<not> IMP_Tailcall.tails s"
  proof
    fix s
    assume 1: "s \<in> set ?cs1"
    obtain i t where "s = to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t" "t \<in> set ts"
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

lemma to_imp_invar: "HOL_TCN_Timing.invar t \<Longrightarrow> IMP_Tailcall.invar (to_imp_tc f_args ctxt bs r stale t)"
proof (induction t arbitrary: bs r stale)
  case (hCall g ts)
  let ?xs = "make_n_fresh (length ts) stale ''Call.x.''"
  let ?cs1 = "mapi (\<lambda>i t. to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t) ts"
  let ?cs2 = "mapi (\<lambda>i t. tAssign (fst (ctxt g) ! i) (A (V (?xs ! i)))) ts"

  have 1: "\<forall>s \<in> set ?cs1. \<not> IMP_Tailcall.tails s"
  proof
    fix s
    assume 1: "s \<in> set ?cs1"
    obtain i t where "s = to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t" "t \<in> set ts"
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
  let ?xs = "make_n_fresh (length ts) stale ''TAIL.x.''"
  let ?cs1 = "mapi (\<lambda>i t. to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t) ts"
  let ?cs2 = "mapi (\<lambda>i t. tAssign (f_args ! i) (A (V (?xs ! i)))) ts"

  have 1: "\<forall>s \<in> set ?cs1. \<not> IMP_Tailcall.tails s"
  proof
    fix s
    assume 1: "s \<in> set ?cs1"
    obtain i t where "s = to_imp_tc f_args ctxt bs (?xs ! i) (?xs @ stale) t" "t \<in> set ts"
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


definition "reserved_regs f_args ctxt bs t =
    (f_args @ bs @ concat (map (fst o ctxt) (calls t)) @ map (snd o snd o ctxt) (calls t))"

(* mark argument/return registers of all called functions and of f itself as stale *)
definition "to_imp_tc' f_args ctxt bs r t =
  to_imp_tc f_args ctxt bs r (reserved_regs f_args ctxt bs t) t"
(* TODO: right-assoc ? *)

definition "h_let_1 = hLet (hNumber 7) (hLetBound 0)"
value "to_imp_tc' [] null [] ''r'' h_let_1"

definition "h_call_1 = hCall ''g'' [hNumber 7, hNumber 5]"
value "to_imp_tc' [] (null(''g'' := ([''g.x1'', ''g.x2''], Assign ''g.r'' (A (V ''g.x1'')), ''g.r''))) [] ''r'' h_call_1"

definition "com_plus = ([''plus.x'', ''plus.y''], Assign ''plus.ret'' (Plus (V ''plus.x'') (V ''plus.y'')), ''plus.ret'')"
definition "h_sum3 = hLet (hCall ''plus'' [hArg 0, hArg 1]) (hCall ''plus'' [hLetBound 0, hArg 2])"
value "to_imp_tc' [''x'', ''y'', ''z''] (null(''plus'' := com_plus)) [] ''r'' h_sum3"

end