\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Arithmetics
  imports
    HOL_To_IMP_Minus_Fun_Pattern_Setup
    "HOL-Library.Discrete"
begin

context HOL_To_IMP_Minus
begin

definition [compiled_IMP_Minus_const_def]:
  "suc_IMP \<equiv> Com.Assign ''suc.ret'' (V ''suc.args.x'' \<oplus> N 1)"

declare_compiled_const Suc
  return_register "suc.ret"
  argument_registers "suc.args.x"
  compiled suc_IMP

HOL_To_IMP_Minus_func_correct Suc
  unfolding suc_IMP_def
  by (fastforce intro: terminates_with_res_IMP_MinusI terminates_with_IMP_MinusI)

fun mul_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"mul_acc_nat 0 _ z = z" |
"mul_acc_nat (Suc x) y z = mul_acc_nat x y (y + z)"
declare mul_acc_nat.simps[simp del]

lemma mul_acc_nat_eq_mul_add[simp]: "mul_acc_nat x y z = x * y + z"
  by (induction x y z arbitrary: z rule: mul_acc_nat.induct)
  (auto simp: mul_acc_nat.simps mult_eq_if)

case_of_simps mul_acc_nat_eq[simplified Nitpick.case_nat_unfold] : mul_acc_nat.simps
compile_nat mul_acc_nat_eq basename mul_acc


ML\<open>

structure GU = General_Util
structure HTIB = HOL_To_IMP_Tactics_Base
structure HTIU = HOL_To_IMP_Util
structure HTIT = HOL_To_IMP_Tailcalls_Tactics
structure TU = Tactic_Util
structure SUT = State_Update_Tracking
structure SUTIT = State_Update_Tracking_IMP_Tailcalls
structure PU = Parse_Util

structure HA = struct
open HA

val dest_terminates_with_res_IMP_Tailcall =
  \<^Const_fn>\<open>terminates_with_res_IMP_Tailcall for tc c s r v => \<open>(tc, c, s, r, v)\<close>\<close>
val dest_terminates_with_res_IMP_Tailcall_prop =
  HTIU.dest_Trueprop #> dest_terminates_with_res_IMP_Tailcall

val dest_terminates_with_res_IMP_Minus =
  \<^Const_fn>\<open>terminates_with_res_IMP_Minus for c s r v => \<open>(c, s, r, v)\<close>\<close>

val dest_tailcall_to_IMP_Minus =
  \<^Const_fn>\<open>tailcall_to_IMP_Minus for c => c\<close>

val dest_terminates_with_res_IMP_Minus_tailcall_to_IMP_Minus =
  dest_terminates_with_res_IMP_Minus #> (fn (c, _, _, _) => c) #> dest_tailcall_to_IMP_Minus

val dest_terminates_with_res_IMP_Minus_tailcall_to_IMP_Minus_prop =
  HTIU.dest_Trueprop #> dest_terminates_with_res_IMP_Minus_tailcall_to_IMP_Minus

fun preprocess_tac get_IMP_def =
  let fun tac ctxt conclusion =
    case try dest_terminates_with_res_IMP_Minus_tailcall_to_IMP_Minus_prop conclusion of
      NONE =>
        (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
          Pretty.str "Could not find ",
          Syntax.pretty_term ctxt @{term tailcall_to_IMP_Minus},
          Pretty.str " big step in conclusion ",
          Syntax.pretty_term ctxt conclusion
        ] |> Pretty.string_of);
        K no_tac)
      | SOME c =>
        let val solve_simple_goal_tac =
          (EqSubst.eqsubst_tac ctxt [0] (get_IMP_def ctxt c |> the_list)
          THEN' Simplifier.simp_tac ctxt)
          |> SOLVED'
        in
          resolve_tac ctxt [@{thm terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI}]
          (* solve the invariant: invar f_IMP_tailcall *)
          THEN' solve_simple_goal_tac
          (* solve the assumption: ''f.ret'' in vars f_IMP_tailcall *)
          THEN' solve_simple_goal_tac
        end
  in TU.SUBGOAL_STRIPPED (snd o snd) o tac end

fun flip_eq_thm thm = Thm.proof_attributes [Calculation.symmetric] thm #> fst

val rewrite_eq_state_retrieval_sym_tac =
  let
    fun rewrite_focused_tac {prems, context=ctxt, ...} =
      let
        val prems_flipped = map (fn thm => flip_eq_thm thm ctxt) prems
      in
        REPEAT_ALL_NEW (HTIU.subst_first_tac ctxt prems_flipped)
        THEN' TU.insert_tac prems_flipped ctxt
      end
    fun rewrite_tac ctxt ((* binders,  *)(cprems, cconcl)) =
      case try dest_terminates_with_res_IMP_Tailcall_prop (Thm.term_of cconcl) of
        NONE => K no_tac (* TODO: error message *)
      | SOME (_, _, state, _, _) =>
        let
          (* val _ = writeln ("cprems: " ^ @{make_string} cprems)
          val _ = writeln ("binders: " ^ @{make_string} binders)
          val _ = writeln ("cconcl: " ^ @{make_string} cconcl) *)
          val is_eq_state_retrieval_prem = GU.try_bool
            (Thm.term_of #> HTIU.dest_Trueprop
              #> \<^Const_fn>\<open>HOL.eq _ for _ s_app => \<open>SUT.is_state_state_retrieval state s_app\<close>\<close>)
          (* val is_eq_state_retrieval_prem = GU.try_bool (Thm.term_of #> HTIU.dest_Trueprop #>
            \<^Const_fn>\<open>HOL.eq _ for _ s_app => \<open>
              let
                val _ = Pretty.block [Syntax.pretty_term ctxt state, Pretty.str " / ", Syntax.pretty_term ctxt s_app] |> Pretty.string_of |> writeln
              in SUT.is_state_state_retrieval state s_app end\<close>\<close>) *)
          val eq_state_retrieval_prems = GU.find_indices is_eq_state_retrieval_prem cprems
          (* val _ = writeln ("eq_state_retrieval_prems: " ^ @{make_string} eq_state_retrieval_prems) *)
        in
          TU.focus_delete_prems_tac (HTIU.successors eq_state_retrieval_prems)
            rewrite_focused_tac ctxt
        end
  in TU.FOCUS_PARAMS_CTXT' (TU.CSUBGOAL_STRIPPED ((* fst o *) snd) o rewrite_tac) end

fun setup_induction_tac get_inducts =
  let fun focused_tac ctxt concl =
    case try dest_terminates_with_res_IMP_Tailcall_prop concl of
      (* state s, result value v *)
      SOME (_, _, s, _, v) =>
        let
          (* v is of the form f (s ''...'') (s ''...'') ..., where f is the HOL function we are after *)
          val head = head_of v
          val instantiations =
            head |> dest_Const |> fst
            |> Compile_Nat.get_compiled_const (Context.Proof ctxt) |> #arg_regs
            |> map (HOL_To_IMP_Util.mk_state_register_retrieval s)
            |> map (fn t => SOME (NONE, (t, false)))
          val arbitrary = [dest_Free s]
          val inducts = get_inducts ctxt head
        in
          Induction.induction_tac ctxt true [instantiations] [arbitrary] [] inducts []
          (* needed for inductions of functions defined on pattern matching; they create equalities of the
             form "t = s ''<register>''", which have to be rewritten in the goal's conclusion" *)
          THEN_ALL_NEW (TU.TRY' (rewrite_eq_state_retrieval_sym_tac ctxt))
        end
   | NONE => (writeln "Could not find IMP terminates_with_res in conclusion"; K no_tac)
  in TU.FOCUS_PARAMS_CTXT' (TU.SUBGOAL_STRIPPED (snd o snd) o focused_tac) end

fun start_case_tac get_IMP_def =
  let
    fun rewrite_tac ctxt cconcl =
      case try dest_terminates_with_res_IMP_Tailcall_prop (Thm.term_of cconcl) of
        NONE => K no_tac (* TODO: error message *)
      | SOME (_, c, _, _, _) =>
          EqSubst.eqsubst_tac ctxt [2] (get_IMP_def ctxt c |> the_list)
          THEN' resolve_tac ctxt [@{thm terminates_with_res_IMP_Tailcall_start}]
  in TU.FOCUS_PARAMS_CTXT' (TU.CSUBGOAL_STRIPPED (snd o snd) o rewrite_tac) end

(* methods as tactics *)

fun SIMPS_TO_tac simps ctxt =
  TU.TRY' (simp_tac (ctxt addsimps simps))
  THEN' resolve_tac ctxt [@{thm SIMPS_TOI}]

fun SIMPS_TO_UNIF_tac simps ctxt = (* @{thms STATE_eq interp_state_State_eq} *)
  resolve_tac ctxt [@{thm SIMPS_TO_UNIFI}]
  THEN' TU.TRY' (SIMPS_TO_tac simps ctxt)
  THEN' resolve_tac ctxt [@{thm reflexive}] (* TODO: does \<open>reflexive\<close> apply generally to SIMPS_TO_UNIF? -> yes, to solve s === t premise *)

val STATE_interp_state_State_thms = @{thms STATE_eq interp_state_State_eq}

fun SIMPS_TO_UNIF_STATE_interp_state_State_tac ctxt =
  SIMPS_TO_UNIF_tac STATE_interp_state_State_thms ctxt
  (* THEN' resolve_tac ctxt [@{thm reflexive}] *)

fun STATE_interp_update_eq_STATE_interp_fun_upd ctxt =
  resolve_tac ctxt [@{thm STATE_interp_update_eq_STATE_interp_fun_updI}]
  THEN' SIMPS_TO_UNIF_STATE_interp_state_State_tac ctxt

fun STATE_interp_retrieve_key_eq_tac ctxt =
  resolve_tac ctxt [@{thm STATE_interp_retrieve_key_eqI}]
  THEN' SIMPS_TO_UNIF_STATE_interp_state_State_tac ctxt
  THEN' simp_tac (ctxt addsimps STATE_interp_state_State_thms)

fun terminates_with_res_step_tac correctness ctxt =
  let
    val terminates_with_res_tSeq_tac =
      resolve_tac ctxt [@{thm terminates_with_res_tSeqI}]
    val terminates_with_tAssign_tac =
      resolve_tac ctxt [@{thm terminates_with_tAssignI}]
      THEN' STATE_interp_update_eq_STATE_interp_fun_upd ctxt
    val terminates_with_tCall_tac =
      resolve_tac ctxt [@{thm terminates_with_tCallI}]
      (* solve correctness assumption *)
      THEN' resolve_tac ctxt correctness
      (* solve state update assumption: s' = s(r := val) *)
      THEN' STATE_interp_update_eq_STATE_interp_fun_upd ctxt
    val terminates_with_res_tAssign_tac =
      resolve_tac ctxt [@{thm terminates_with_res_tAssignI}]
      THEN' STATE_interp_update_eq_STATE_interp_fun_upd ctxt
    val terminates_with_res_tIf_tac =
      resolve_tac ctxt [@{thm terminates_with_res_tIf_processedI}]
      THEN' STATE_interp_retrieve_key_eq_tac ctxt
      THEN' SIMPS_TO_UNIF_STATE_interp_state_State_tac ctxt
      THEN' SIMPS_TO_UNIF_STATE_interp_state_State_tac ctxt
  in
    (terminates_with_res_tSeq_tac
      THEN' (terminates_with_tAssign_tac ORELSE' terminates_with_tCall_tac))
    ORELSE' terminates_with_res_tAssign_tac
    ORELSE' terminates_with_res_tIf_tac
  end

fun terminates_with_res_steps_tac correctness ctxt = K no_tac

(* finish in the inductive case *)

val foo = Subgoal.FOCUS_PARAMS

fun pretty_focus ({ asms, concl, context, params, prems, schematics=_ } : Subgoal.focus) =
  let
    open Pretty
    val blbr = block o breaks
    val pretty_cterm = Syntax.pretty_term context o Thm.term_of
    fun pretty_param (name, cterm) = block [str name, str " as ", pretty_cterm cterm]
    fun label_len lbl xs = block [str lbl, str " (", str (List.length xs |> string_of_int), str "):"]
  in
    (block o fbreaks) [
      str "focus:",
      blbr (label_len "asms" asms :: List.map (cartouche o pretty_cterm) asms),
      blbr [str "concl:", cartouche (Syntax.pretty_term context (Thm.term_of concl))],
      blbr (str "context:" :: Proof.pretty_state (Proof.init context)),
      blbr (label_len "params" params :: List.map (cartouche o pretty_param) params),
      blbr (label_len "prems" prems :: List.map (cartouche o pretty_cterm o Thm.cprop_of) prems),
      blbr [str "schematics:", str "(...)"]
    ]
  end

end
\<close>

lemma add_assumption: assumes P and "P ==> Q" shows "Q" using assms by blast

(* technical lemma that lets us isolate the return value in its own subgoal *)
lemma rewrite_terminates_with_res_IMP_Tailcall_value:
  assumes "v = v'" and "terminates_with_res_IMP_Tailcall tc c s r v'"
  shows "terminates_with_res_IMP_Tailcall tc c s r v"
  using assms by blast

ML\<open>

structure HA = struct
open HA

fun pretty_cterm ctxt = Syntax.pretty_term ctxt o Thm.term_of

(* TODO: nicer destructor *)
(* destructure s from terminates_with_res_IMP_Tailcall tc c s r v *)
(* val cdest_terminates_with_res_IMP_Tailcall_state =
  Thm.dest_arg o Thm.dest_fun o Thm.dest_fun o HTIU.cdest_Trueprop *)

fun cstrip_comb ctm =
  let
    fun strip f args =
      case Thm.term_of f of
        (_ $ _) => let val (f', arg) = Thm.dest_comb f in strip f' (arg :: args) end
      | _ => (f, args)
  in strip ctm [] end

fun cdest_terminates_with_res_IMP_Tailcall ct =
  case HTIU.cdest_Trueprop ct |> cstrip_comb |>> Thm.term_of of
    (Const (@{const_name terminates_with_res_IMP_Tailcall}, _), [tc, c, s, r, v]) => (tc, c, s, r, v)
  | _ => raise CTERM ("cdest_terminates_with_res_IMP_Tailcall", [ct])

(* val _ = let open Pretty in
    (block o breaks) [
      str "in finish_tail_tac:",
      (block o breaks) (str "cprems:" :: List.map (cartouche o pretty_cterm ctxt) cprems),
      (block o breaks) [str "cconcl:", cartouche (pretty_cterm ctxt cconcl)],
    ] |> writeln end *)


val finish_tail_tac =
  let fun main_tac ctxt =
    let fun extract_state_tac ({ context = ctxt, prems, concl, ... } : Subgoal.focus) =
      case try cdest_terminates_with_res_IMP_Tailcall concl of
        NONE => (writeln "couldn't find ... in conclusion"; K no_tac (* TODO: error case *))
      | SOME (_, _, s, _, v) =>
          let
            val ih =
              let val is_ih = Thm.cconcl_of #> can cdest_terminates_with_res_IMP_Tailcall
              in find_first is_ih prems |> the (* TODO *) end

            (* v is of the form f t1 t2 ..., where f is the relevant HOL function;
               extract the list of argument registers of f, and the terms t1, t2, ... *)
            val ({ arg_regs, ... }, arg_terms) =
              v |> Thm.term_of |> Term.strip_comb
              |>> (dest_Const #> fst #> Compile_Nat.get_compiled_const (Context.Proof ctxt))

            (* construct equalities of the form t_i = s ''reg_i'' *)
            val arg_reg_eqs =
              map2
                (fn t => fn reg =>
                  HTIU.mk_eq (t, HTIU.mk_state_register_retrieval (Thm.term_of s) reg)
                  |> HTIU.mk_Trueprop |> Thm.cterm_of ctxt)
                arg_terms arg_regs

            (* tactic for proving the equalities: add existing premises, then simp *)
            val arg_reg_eq_tac =
              Tactic.cut_facts_tac prems
              THEN'
              (* TODO: narrow down the simpset here... or come up with a better tactic *)
              Simplifier.simp_tac (
                Simplifier.clear_simpset ctxt
                addsimps @{thms STATE_eq interp_update_state_eq interp_state_State_eq})
              THEN' Simplifier.simp_tac ctxt

            (* prove the equalities *)
            val arg_reg_eq_thms =
              arg_reg_eqs |> map (Tactic_Util.apply_tac arg_reg_eq_tac 1 #> Seq.hd)
              (* TODO: Seq.hd OK ?? Or does one really need to consider all combinations... *)

            val rewrite_concl_tac =
              resolve_tac ctxt [@{thm rewrite_terminates_with_res_IMP_Tailcall_value}]
              THEN' EVERY' (rev arg_reg_eq_thms |> map (single #> HTIU.subst_first_tac ctxt))
              THEN' resolve_tac ctxt [@{thm refl}]

            val instantiate_ih_tac =
              (* TU.insert_tac, Tactic.cut_tac or resolve_tac ??? *)
              resolve_tac ctxt [Drule.infer_instantiate' ctxt [SOME s] ih]

            val solve_ih_prem_tac =
              Tactic.cut_facts_tac prems
              THEN' (HTIU.subst_first_tac ctxt (map (fn thm => flip_eq_thm thm ctxt) arg_reg_eq_thms))
              THEN' Simplifier.simp_tac ctxt (* TODO: narrow simp set *)

          in
            rewrite_concl_tac
            THEN' (instantiate_ih_tac THEN_ALL_NEW solve_ih_prem_tac)
          end
    in
      Simplifier.simp_tac (Simplifier.clear_simpset ctxt addsimps @{thms mul_acc_nat.simps})
      THEN' TU.FOCUS_PREMS' extract_state_tac ctxt
    end
  in
    TU.FOCUS_PARAMS_CTXT' main_tac
  end

end
\<close>

HOL_To_IMP_Minus_func_correct mul_acc_nat
  (* apply (rule terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI) *)
  apply (tactic \<open>HA.preprocess_tac H.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HA.setup_induction_tac HA.get_HOL_inducts @{context} 1\<close>)

  (* apply (subst (2) mul_acc_IMP_tailcall_def)
  apply (rule terminates_with_res_IMP_Tailcall_start) *)
  apply (tactic \<open>HA.start_case_tac H.get_IMP_def @{context} 1\<close>)

(*   apply (terminates_with_res_tSeq)
  apply (rule terminates_with_tAssignI)
  apply (rule STATE_interp_update_eq_STATE_interp_fun_updI)
  apply (rule SIMPS_TO_UNIFI)
  apply (simp add: STATE_eq interp_state_State_eq)
  apply (rule SIMPS_TOI)
  apply (rule reflexive) *)

  (* apply (terminates_with_res_step correctness:
    eq_nat_IMP_Minus_func_correct add_nat_IMP_Minus_func_correct
  )+ *)
  apply (tactic \<open>
    HA.terminates_with_res_step_tac
      (* TODO: look up correctness in context: scan the command? *)
      @{thms eq_nat_IMP_Minus_func_correct}
      @{context} 1
  \<close>)+
  (* supply mul_acc_nat.simps[simp del] mul_acc_nat_eq_mul_add[simp del] *)
  apply STATE_interp_retrieve_key_eq (* end of branch after assign *)

  (* apply (terminates_with_res_step correctness:
    eq_nat_IMP_Minus_func_correct add_nat_IMP_Minus_func_correct sub_nat_IMP_Minus_func_correct
  )+ *)
  apply (tactic \<open>
    HA.terminates_with_res_step_tac
      @{thms add_nat_IMP_Minus_func_correct sub_nat_IMP_Minus_func_correct}
      @{context} 1
  \<close>)+
  (* apply terminates_with_res_tTail *) (* end of branch after tail-call *)
  apply metis (*  *)

  (* apply (subst (2) mul_acc_IMP_tailcall_def)
  apply (rule terminates_with_res_IMP_Tailcall_start) *)
  apply (tactic \<open>HA.start_case_tac H.get_IMP_def @{context} 1\<close>)
  
  (* apply (terminates_with_res_step correctness:
    eq_nat_IMP_Minus_func_correct add_nat_IMP_Minus_func_correct sub_nat_IMP_Minus_func_correct
  )+ *)
  apply (tactic \<open>
    HA.terminates_with_res_step_tac
      @{thms eq_nat_IMP_Minus_func_correct add_nat_IMP_Minus_func_correct sub_nat_IMP_Minus_func_correct}
      @{context} 1
  \<close>)+
  apply STATE_interp_retrieve_key_eq

  (* apply (terminates_with_res_step correctness:
    eq_nat_IMP_Minus_func_correct add_nat_IMP_Minus_func_correct sub_nat_IMP_Minus_func_correct
  )+ *)
  apply (tactic \<open>
    HA.terminates_with_res_step_tac
      @{thms eq_nat_IMP_Minus_func_correct add_nat_IMP_Minus_func_correct sub_nat_IMP_Minus_func_correct}
      @{context} 1
  \<close>)+
  apply terminates_with_res_tTail
  (* apply (simp (no_asm) only: STATE_eq interp_update_state_eq interp_state_State_eq) *) (* ? *)
  apply (tactic \<open>HA.finish_tail_tac @{context} 1\<close>)
done

  (* proof-
    fix x s

    let ?s' = "
      (STATE (interp_state
        (update_state (update_state (update_state (update_state (update_state
        (update_state (update_state (update_state (update_state (update_state
        (update_state (update_state (update_state
        (State s)
        ''eq.args.x'' (s ''mul_acc.args.x1a''))
        ''eq.args.y'' 0)
        ''eq.ret'' (nat_of_bool (s ''mul_acc.args.x1a'' = 0)))
        ''.If.3'' (nat_of_bool (s ''mul_acc.args.x1a'' = 0)))
        ''sub.args.x'' (s ''mul_acc.args.x1a''))
        ''sub.args.y'' 1)
        ''sub.ret'' (s ''mul_acc.args.x1a'' - 1))
        ''mul_acc.args.x1a'' (s ''mul_acc.args.x1a'' - 1))
        ''mul_acc.args.x2a'' (s ''mul_acc.args.x2a''))
        ''add.args.x'' (s ''mul_acc.args.x2a''))
        ''add.args.y'' (s ''mul_acc.args.x3ba''))
        ''add.ret'' (s ''mul_acc.args.x2a'' + s ''mul_acc.args.x3ba''))
        ''mul_acc.args.x3ba'' (s ''mul_acc.args.x2a'' + s ''mul_acc.args.x3ba''))))"

    assume ih: "
      x = sa ''mul_acc.args.x1a'' \<Longrightarrow>
      s ''mul_acc.args.x2a'' = sa ''mul_acc.args.x2a'' \<Longrightarrow>
      s ''mul_acc.args.x2a'' + s ''mul_acc.args.x3ba'' = sa ''mul_acc.args.x3ba'' \<Longrightarrow>
      terminates_with_res_IMP_Tailcall mul_acc_IMP_tailcall mul_acc_IMP_tailcall sa ''mul_acc.ret''
        (mul_acc_nat (sa ''mul_acc.args.x1a'') (sa ''mul_acc.args.x2a'') (sa ''mul_acc.args.x3ba''))"
      for sa
    then have ih': "
      x = sa ''mul_acc.args.x1a'' \<Longrightarrow>
      s ''mul_acc.args.x2a'' = sa ''mul_acc.args.x2a'' \<Longrightarrow>
      s ''mul_acc.args.x2a'' + s ''mul_acc.args.x3ba'' = sa ''mul_acc.args.x3ba'' \<Longrightarrow>
      terminates_with_res_IMP_Tailcall mul_acc_IMP_tailcall mul_acc_IMP_tailcall sa ''mul_acc.ret''
        (mul_acc_nat x (s ''mul_acc.args.x2a'') (s ''mul_acc.args.x2a'' + s ''mul_acc.args.x3ba''))"
      for sa
      by simp

    assume case_d: "s ''mul_acc.args.x1a'' = Suc x" "s ''mul_acc.args.x1a'' \<noteq> 0"

    show "terminates_with_res_IMP_Tailcall mul_acc_IMP_tailcall mul_acc_IMP_tailcall ?s' ''mul_acc.ret'' (mul_acc_nat (Suc x) (s ''mul_acc.args.x2a'') (s ''mul_acc.args.x3ba''))"
      apply (simp (no_asm) only: mul_acc_nat.simps)
      apply (rule ih'[where sa = ?s'])
      apply (simp_all only: case_d)
      apply (simp_all only: STATE_eq interp_update_state_eq interp_state_State_eq)
      apply simp_all
    done

  qed *)

definition mul_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mul_nat x y = mul_acc_nat x y 0"

lemma mul_nat_eq_mul [simp]: "mul_nat x y = x * y"
  unfolding mul_nat_def by simp

compile_nat mul_nat_def basename mul

declare_compiled_const "times"
  return_register "mul.ret"
  argument_registers "mul.args.x" "mul.args.y"
  compiled "tailcall_to_IMP_Minus mul_IMP_tailcall"

HOL_To_IMP_Minus_func_correct mul_nat
  by (terminates_with_res_IMP_Minus tailcall_def: mul_IMP_tailcall_def
    correctness: mul_acc_nat_IMP_Minus_func_correct)


fun div_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_acc_nat x y z = (if y = 0 then z else if x < y then z else div_acc_nat (x - y) y (z + 1))"
declare div_acc_nat.simps[simp del]

lemma div_acc_nat_eq_div[simp]: "div_acc_nat x y z = x div y + z"
  by (induction x y z rule: div_acc_nat.induct) (auto simp: div_acc_nat.simps div_if)

compile_nat div_acc_nat.simps basename div_acc

HOL_To_IMP_Minus_func_correct div_acc_nat by (cook mode = tailcall)

definition div_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_nat x y = div_acc_nat x y 0"

lemma div_nat_eq_div[simp]: "div_nat x y = x div y"
  unfolding div_nat_def by simp

compile_nat div_nat_def basename div

declare_compiled_const "divide"
  return_register "div.ret"
  argument_registers "div.args.x" "div.args.y"
  compiled "tailcall_to_IMP_Minus div_IMP_tailcall"

HOL_To_IMP_Minus_func_correct div_nat by cook

definition square_nat :: "nat \<Rightarrow> nat" where
  "square_nat x \<equiv> mul_nat x x"

compile_nat square_nat_def basename square

HOL_To_IMP_Minus_func_correct square_nat by cook

lemma square_nat_eq_square[simp]: "square_nat x = x\<^sup>2"
  unfolding square_nat_def by (simp add: power2_eq_square)

(*takes lower and upper bound for root*)
function sqrt_aux_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sqrt_aux_nat x L R = (if Suc L < R
    then
      let M = (L + R) div 2
      in
        if square_nat M \<le> x
        then sqrt_aux_nat x M R
        else sqrt_aux_nat x L M
    else L)"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(_, L, R). R - L)") auto
declare sqrt_aux_nat.simps[simp del]

compile_nat sqrt_aux_nat.simps basename sqrt_aux

HOL_To_IMP_Minus_func_correct sqrt_aux_nat sorry
(*Example step-by-step tactic invocation. Do not remove for debugging purposes*)
(*
apply (tactic \<open>HA.preprocess_tac H.get_IMP_def @{context} 1\<close>)
apply (tactic \<open>HA.setup_induction_tac HA.get_HOL_inducts @{context} 1\<close>)
apply (tactic \<open>H.start_tac H.get_IMP_def @{context} 1\<close>)
apply (tactic \<open>H.run_tac H.get_func_corrects @{context} 1\<close>)
apply (tactic \<open>H.finish_tailcall_tac HOL_To_IMP_Tactics_Base.get_HOL_eqs @{context} 1\<close>)
apply (tactic \<open>H.finish_tailcall_tac HOL_To_IMP_Tactics_Base.get_HOL_eqs @{context} 1\<close>)
apply (tactic \<open>H.finish_non_tailcall_tac HOL_To_IMP_Tactics_Base.get_HOL_eqs @{context} 1\<close>)
done
*)

lemma square_sqrt_aux_nat_le:
  assumes "L\<^sup>2 \<le> x" "x < R\<^sup>2"
  shows "(sqrt_aux_nat x L R)\<^sup>2 \<le> x"
  using assms
  by (induction x L R rule: sqrt_aux_nat.induct)
  (auto simp: sqrt_aux_nat.simps Let_def)

lemma lt_square_Suc_sqrt_aux_nat:
  assumes "L\<^sup>2 \<le> x" "x < R\<^sup>2"
  shows "x < (Suc (sqrt_aux_nat x L R))\<^sup>2"
  using assms
  by (induction x L R rule: sqrt_aux_nat.induct)
  (use order_less_le_trans in \<open>force simp: sqrt_aux_nat.simps Let_def\<close>)

definition sqrt_nat :: "nat \<Rightarrow> nat" where
  "sqrt_nat x = sqrt_aux_nat x 0 (Suc x)"

compile_nat sqrt_nat_def basename sqrt

HOL_To_IMP_Minus_func_correct sqrt_nat by cook

lemma square_sqrt_nat_le: "(sqrt_nat x)\<^sup>2 \<le> x"
  using square_sqrt_aux_nat_le unfolding sqrt_nat_def by (simp add: power2_eq_square)

lemma lt_square_Suc_sqrt_nat: "x < (Suc (sqrt_nat x))\<^sup>2"
  using lt_square_Suc_sqrt_aux_nat unfolding sqrt_nat_def by (simp add: power2_eq_square)

corollary sqrt_nat_sqrt[simp]: "sqrt_nat y = Discrete.sqrt y"
  using square_sqrt_nat_le lt_square_Suc_sqrt_nat
  by (intro sqrt_unique[symmetric]) auto

end

end



(* lemma foo:
  assumes "PROP SIMPS_TO_UNIF val val'"
  shows "STATE (interp_state (update_state s k val')) = (STATE (interp_state s))(k := val)"
  using assms unfolding STATE_eq SIMPS_TO_UNIF_eq by (simp add: interp_state_State_eq) *)

(* find_theorems "_ \<turnstile> (tCall _ _, _) \<Rightarrow>\<^bsup>_\<^esup> _" *)

(* thm tCall *)


(* context
  notes
    terminates_with_IMP_MinusE[elim] terminates_with_res_IMP_MinusE[elim]
    (* terminates_with_IMP_TailcallE[elim] terminates_with_res_IMP_TailcallE[elim] *)
(*     terminates_with_res_IMP_MinusI[intro] terminates_with_IMP_MinusI[intro]
    terminates_with_res_IMP_TailcallI[intro] *) terminates_with_IMP_TailcallI[intro]
begin *)
(* 
lemma bar:
  assumes "terminates_with_res_IMP_Minus c s r v"
  and "s' = s(r := v)"
  shows "terminates_with_IMP_Tailcall tc (tCall c r) s s'"

using assms proof-
  obtain s'' where "terminates_with_IMP_Minus c s s''" "s'' r = v" using terminates_with_res_IMP_MinusE[OF assms(1)] by blast
  have "\<exists>t. (c, s) \<Rightarrow>\<^bsup>t\<^esup> s''" using terminates_with_IMP_MinusE[OF \<open>terminates_with_IMP_Minus c s s''\<close>] by blast
  then have "\<exists>t. tc \<turnstile> (tCall c r, s) \<Rightarrow>\<^bsup>t\<^esup> s(r := v)" using \<open>s'' r = v\<close> by auto
  then have "\<exists>t. tc \<turnstile> (tCall c r, s) \<Rightarrow>\<^bsup>t\<^esup> s'" using assms by simp
  then show "terminates_with_IMP_Tailcall tc (tCall c r) s s'" using terminates_with_IMP_TailcallI by blast
qed
 *)