\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Arithmetics
  imports
    HOL_To_IMP_Minus_Fun_Pattern_Setup
    "HOL-Library.Discrete"
    "ML_Unification.ML_Unification_HOL_Setup"
    "ML_Unification.Unify_Resolve_Tactics"
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

case_of_simps mul_acc_nat_eq[simplified Nitpick.case_nat_unfold] : mul_acc_nat.simps
compile_nat mul_acc_nat_eq basename mul_acc

(* isolates the return value in its own subgoal *)
lemma rewrite_terminates_with_res_IMP_Tailcall_value:
  assumes "v = v'" and "terminates_with_res_IMP_Tailcall tc c s r v'"
  shows "terminates_with_res_IMP_Tailcall tc c s r v"
  using assms by blast

(* isolates the function and its argument from a function application *)
lemma rewrite_comb: assumes "f = g" "x = y" shows "f x = g y" using assms by blast

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

type terminates_with_res_IMP_Tailcall_args = {tc: term, c: term, s: term, r: term, v: term}

val dest_terminates_with_res_IMP_Tailcall =
  \<^Const_fn>\<open>terminates_with_res_IMP_Tailcall for tc c s r v => \<open>{tc = tc, c = c, s = s, r = r, v = v}\<close>\<close>
val dest_terminates_with_res_IMP_Tailcall_prop =
  HTIU.dest_Trueprop #> dest_terminates_with_res_IMP_Tailcall

fun with_dest_terminates_with_res_IMP_Tailcall_prop tac =
  let
    fun wrap_tac concl =
      case try dest_terminates_with_res_IMP_Tailcall_prop concl of
        NONE => (writeln "couldn't find dest_terminates_with_res_IMP_Tailcall in conclusion"; K no_tac (* TODO: error case *))
      | SOME args => tac args
  in
    TU.SUBGOAL_STRIPPED (snd o snd) wrap_tac
  end


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

fun flip_eq_thm ctxt thm = Thm.proof_attributes [Calculation.symmetric] thm ctxt |> fst

val rewrite_eq_state_retrieval_sym_tac =
  let
    fun rewrite_focused_tac {prems, context = ctxt, ...} =
      let val prems_flipped = map (flip_eq_thm ctxt) prems
      in
        REPEAT_ALL_NEW (HTIU.subst_first_tac ctxt prems_flipped)
        THEN' TU.insert_tac prems_flipped ctxt
      end
    fun rewrite_tac ctxt prems {s, ...}  =
      let
        val is_eq_state_retrieval_prem =
          GU.try_bool
            (HTIU.dest_Trueprop #>
            \<^Const_fn>\<open>HOL.eq _ for _ s_app => \<open>SUT.is_state_state_retrieval s s_app\<close>\<close>)
        val eq_state_retrieval_prems = GU.find_indices is_eq_state_retrieval_prem prems
      in
        TU.focus_delete_prems_tac (HTIU.successors eq_state_retrieval_prems)
          rewrite_focused_tac ctxt
      end
  in
    TU.FOCUS_PARAMS_CTXT' (
      TU.SUBGOAL_STRIPPED (fst o snd) o (
        with_dest_terminates_with_res_IMP_Tailcall_prop oo rewrite_tac))
  end

fun setup_induction_tac get_inducts =
  let fun focused_tac ctxt {s, v, ...} =
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
  in TU.FOCUS_PARAMS_CTXT' (with_dest_terminates_with_res_IMP_Tailcall_prop o focused_tac) end

fun start_case_tac get_IMP_def =
  let fun focused_tac ctxt {c, ...} =
    EqSubst.eqsubst_tac ctxt [2] (get_IMP_def ctxt c |> the_list)
    THEN' resolve_tac ctxt [@{thm terminates_with_res_IMP_Tailcall_start}]
  in TU.FOCUS_PARAMS_CTXT' (with_dest_terminates_with_res_IMP_Tailcall_prop o focused_tac) end


(* SIMPS_TO helper tactics *)

fun SIMPS_TO_tac simps ctxt =
  TU.TRY' (simp_tac (ctxt addsimps simps))
  THEN' resolve_tac ctxt [@{thm SIMPS_TOI}]

fun SIMPS_TO_UNIF_tac simps ctxt =
  resolve_tac ctxt [@{thm SIMPS_TO_UNIFI}]
  THEN' TU.TRY' (SIMPS_TO_tac simps ctxt)
  THEN' resolve_tac ctxt [@{thm reflexive}]

(* helpers for updating and retrieving protected STATEs *)

val STATE_interp_state_State_thms = @{thms STATE_eq interp_state_State_eq}

fun SIMPS_TO_UNIF_STATE_interp_state_State_tac ctxt =
  SIMPS_TO_UNIF_tac STATE_interp_state_State_thms ctxt

fun STATE_interp_update_eq_STATE_interp_fun_upd ctxt =
  resolve_tac ctxt [@{thm STATE_interp_update_eq_STATE_interp_fun_updI}]
  THEN' SIMPS_TO_UNIF_STATE_interp_state_State_tac ctxt

fun STATE_interp_retrieve_key_eq_tac finish_eq_tac ctxt = (* TODO: kind of ugly *)
  resolve_tac ctxt [@{thm STATE_interp_retrieve_key_eqI}]
  THEN' SIMPS_TO_UNIF_STATE_interp_state_State_tac (ctxt addsimps STATE_interp_state_State_thms)
  THEN' finish_eq_tac

(* tactics for tAssign, tSeq, and tIf that run one step of the tailcall program *)

fun terminates_with_res_tAssign_tac ctxt =
  resolve_tac ctxt [@{thm terminates_with_res_tAssignI}]
  THEN' STATE_interp_update_eq_STATE_interp_fun_upd ctxt

fun terminates_with_res_tSeq_tac ctxt =
  resolve_tac ctxt [@{thm terminates_with_res_tSeqI}]

fun terminates_with_res_tIf_tac ctxt =
  resolve_tac ctxt [@{thm terminates_with_res_tIf_processedI}]
  THEN' STATE_interp_retrieve_key_eq_tac (simp_tac ctxt) ctxt
  THEN' SIMPS_TO_UNIF_STATE_interp_state_State_tac ctxt
  THEN' SIMPS_TO_UNIF_STATE_interp_state_State_tac ctxt

(* tactics for tAssign and tCall that handle the terminates_with (instead of terminates_with_res) case *)

fun terminates_with_tAssign_tac ctxt =
  resolve_tac ctxt [@{thm terminates_with_tAssignI}]
  THEN' STATE_interp_update_eq_STATE_interp_fun_upd ctxt

fun terminates_with_tCall_tac ctxt correctness =
  resolve_tac ctxt [@{thm terminates_with_tCallI}]
  (* solve correctness assumption *)
  THEN' resolve_tac ctxt correctness
  (* solve state update assumption: s' = s(r := val) *)
  THEN' STATE_interp_update_eq_STATE_interp_fun_upd ctxt

(* given a constant term like eq_IMP, returns a list of potentially suitable IMP- correctness theorems *)
fun get_func_corrects ctxt t =
  let
    open Find_Theorems
    val thms = find_theorems ctxt NONE NONE true [
      (* search for the equality theorem *)
      (true, Pattern (@{term terminates_with_res_IMP_Minus} $ t (*TODO: wildcard for remaining args*))),
      (* ignore conditional rules *)
      (false, Pattern @{term "(\<Longrightarrow>)"})
    ] |> snd |> map snd
  in if null thms then NONE else SOME thms end

(* run one tSeq or tIf step of a tailcall program, preserves the terminates_with_res ... structure *)
fun terminates_with_res_step_tac get_func_corrects =
  let
    fun tac ctxt {c, ...} =
      case c of
        Const (@{const_name tSeq}, _) $ (Const (@{const_name tAssign}, _) $ _ $ _) $ _ =>
          terminates_with_res_tSeq_tac ctxt THEN' terminates_with_tAssign_tac ctxt
      | Const (@{const_name tSeq}, _) $ (Const (@{const_name tCall}, _) $ com $ _) $ _ =>
          (case get_func_corrects ctxt com of
            NONE => (writeln "no correctness found"; K no_tac (* TODO *))
          | SOME cs => terminates_with_res_tSeq_tac ctxt THEN' terminates_with_tCall_tac ctxt cs)
      | Const (@{const_name tIf}, _) $ _ $ _ $ _ => terminates_with_res_tIf_tac ctxt
      | _ => K no_tac
  in
    TU.FOCUS_PARAMS_CTXT' (with_dest_terminates_with_res_IMP_Tailcall_prop o tac)
  end

(* finishing tactics *)

val finish_tail_tac =
  let fun tac ctxt =
    let fun extract_state_tac ({ context = ctxt, prems, ... } : Subgoal.focus) {s, v, ...} =
      let

        (* v is of the form f t1 t2 ..., where f is the relevant HOL function;
           extract the list of argument registers of f, and the terms t1, t2, ... *)
        val ({ arg_regs, ... }, arg_terms) =
          v |> Term.strip_comb
          |>> (dest_Const #> fst #> Compile_Nat.get_compiled_const (Context.Proof ctxt))

        (* construct equalities of the form t_i = s ''reg_i'' *)
        val arg_reg_eqs =
          map2
            (fn t => fn reg =>
              HTIU.mk_eq (t, HTIU.mk_state_register_retrieval s reg)
              |> HTIU.mk_Trueprop |> Thm.cterm_of ctxt)
            arg_terms arg_regs

        (* tactic for proving the equalities: add existing premises, then simp *)
        val arg_reg_eq_tac =
          Tactic.cut_facts_tac prems
          THEN'
          (* TODO: narrow down the simpset here... or come up with a better tactic *)
          Simplifier.asm_simp_tac (
            Simplifier.clear_simpset ctxt
            addsimps @{thms STATE_eq interp_update_state_eq interp_state_State_eq})
          THEN' Simplifier.asm_simp_tac ctxt

        (* prove the equalities *)
        val arg_reg_eq_thms =
          arg_reg_eqs |> map (TU.HEADGOAL (TU.apply_tac arg_reg_eq_tac) #> Seq.hd)
          (* TODO: Seq.hd OK ?? Or does one really need to consider all combinations... *)

        fun refl_tac ctxt = resolve_tac ctxt [@{thm refl}]

        fun unify_resolve_tac thm =
          Standard_Unify_Resolve.unify_resolve_tac (Unify_Resolve_Args.PRM.r ()) [thm] [] ctxt

        (* rewrite each argument t_i to s ''reg_i''; each argument is first drawn out
           into a separate subgoal t_i = ?v s to prevent substitution from occurring inside s *)
        fun rewrite_args_tac [] = refl_tac ctxt
          | rewrite_args_tac (thm :: thms) =
              unify_resolve_tac @{thm rewrite_comb}
              THEN' rewrite_args_tac thms
              THEN' HTIU.subst_first_tac ctxt [thm] THEN' refl_tac ctxt

        val rewrite_concl_tac =
          resolve_tac ctxt [@{thm rewrite_terminates_with_res_IMP_Tailcall_value}]
          THEN' rewrite_args_tac (rev arg_reg_eq_thms)

        val is_ih = Thm.concl_of #> can dest_terminates_with_res_IMP_Tailcall_prop

        val instantiate_apply_ih_tac =
          (* TU.insert_tac, Tactic.cut_tac or resolve_tac ??? *)
          filter is_ih prems
          |> map_filter (try (Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt s)]))
          |> resolve_tac ctxt

        val solve_ih_prem_tac =
          Tactic.cut_facts_tac prems
          THEN' TU.TRY' (HTIU.subst_first_tac ctxt (map (flip_eq_thm ctxt) arg_reg_eq_thms))
          THEN' Simplifier.asm_simp_tac ctxt (* TODO: narrow simp set *)

      in
        rewrite_concl_tac
        THEN' instantiate_apply_ih_tac
        THEN_ALL_NEW SOLVED' solve_ih_prem_tac
      end
    in
      resolve_tac ctxt [@{thm terminates_with_res_tTailI}]
      THEN' TU.FOCUS_PREMS' (with_dest_terminates_with_res_IMP_Tailcall_prop o extract_state_tac) ctxt
    end
  in
    TU.FOCUS_PARAMS_CTXT' tac
  end

fun finish_non_tail_tac ctxt =
  terminates_with_res_tAssign_tac ctxt
  THEN' STATE_interp_retrieve_key_eq_tac (asm_simp_tac (ctxt addsimps (@{thms Let_def}))) ctxt

fun finish_tac get_HOL_eqs =
  let
    (* replace the HOL function call with its body *)
    fun subst_hol_fun_tac ctxt {v, ...} =
      case get_HOL_eqs ctxt (head_of v) of
        NONE => (writeln "Could not find HOL equality for HOL term in conclusion"; (* TODO *) K no_tac)
      | SOME thms => HTIU.subst_first_tac ctxt thms
    fun decide_finish_tac ctxt {c, ...} =
      case c of
        Const (@{const_name tTAIL}, _) => finish_tail_tac ctxt
      | Const (@{const_name tAssign}, _) $ _ $ _ => finish_non_tail_tac ctxt
      | _ => (writeln "finish_tac: expected tTAIL or tAssign"; K no_tac (* TODO: nicer error *))
    fun tac ctxt =
      with_dest_terminates_with_res_IMP_Tailcall_prop (subst_hol_fun_tac ctxt)
      (* TODO: the simplification step is fragile if there is any
          other theorem about the HOL function in the simpset *)
      (* TODO: target the relevant assumptions only (?) *)
      THEN' TU.TRY' (Simplifier.asm_simp_tac ctxt)
      THEN' with_dest_terminates_with_res_IMP_Tailcall_prop (decide_finish_tac ctxt)
  in
    TU.FOCUS_PARAMS_CTXT' tac
  end

fun cook tailcall =
  let
    (* fun metis ctxt = Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt [] *)
    fun tac ctxt =
      preprocess_tac H.get_IMP_def ctxt
      THEN' (if tailcall then HA.setup_induction_tac HA.get_HOL_inducts ctxt else K all_tac)
      THEN_ALL_NEW (
        start_case_tac H.get_IMP_def ctxt
        THEN' REPEAT_ALL_NEW (terminates_with_res_step_tac get_func_corrects ctxt)
        THEN_ALL_NEW (
          finish_tac HTIB.get_HOL_eqs ctxt
          ORELSE' Simplifier.asm_simp_tac ctxt
          ORELSE' K all_tac))
  in
    TU.FOCUS_PARAMS_CTXT' tac
  end

end
\<close>

HOL_To_IMP_Minus_func_correct mul_acc_nat
  apply (tactic \<open>HA.cook true @{context} 1\<close>)
  done

lemma mul_acc_nat_eq_mul_add[simp]: "mul_acc_nat x y z = x * y + z"
  by (induction x y z arbitrary: z rule: mul_acc_nat.induct)
  (auto simp: mul_acc_nat.simps mult_eq_if)

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

compile_nat div_acc_nat.simps basename div_acc

thm div_acc_nat.induct

HOL_To_IMP_Minus_func_correct div_acc_nat
  apply (tactic \<open>HA.cook true @{context} 1\<close>) done

lemma div_acc_nat_eq_div[simp]: "div_acc_nat x y z = x div y + z"
  by (induction x y z rule: div_acc_nat.induct) (auto simp: div_acc_nat.simps div_if)

definition div_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_nat x y = div_acc_nat x y 0"

lemma div_nat_eq_div[simp]: "div_nat x y = x div y"
  unfolding div_nat_def by simp

compile_nat div_nat_def basename div

declare_compiled_const "divide"
  return_register "div.ret"
  argument_registers "div.args.x" "div.args.y"
  compiled "tailcall_to_IMP_Minus div_IMP_tailcall"

HOL_To_IMP_Minus_func_correct div_nat
  apply (tactic \<open>HA.cook false @{context} 1\<close>) done

definition square_nat :: "nat \<Rightarrow> nat" where
  "square_nat x \<equiv> mul_nat x x"

compile_nat square_nat_def basename square

HOL_To_IMP_Minus_func_correct square_nat
  apply (tactic \<open>HA.cook false @{context} 1\<close>) done

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

HOL_To_IMP_Minus_func_correct sqrt_aux_nat
  apply (tactic \<open>HA.cook true @{context} 1\<close>) done

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

HOL_To_IMP_Minus_func_correct sqrt_nat
  apply (tactic \<open>HA.cook false @{context} 1 \<close>) done

lemma square_sqrt_nat_le: "(sqrt_nat x)\<^sup>2 \<le> x"
  using square_sqrt_aux_nat_le unfolding sqrt_nat_def by (simp add: power2_eq_square)

lemma lt_square_Suc_sqrt_nat: "x < (Suc (sqrt_nat x))\<^sup>2"
  using lt_square_Suc_sqrt_aux_nat unfolding sqrt_nat_def by (simp add: power2_eq_square)

corollary sqrt_nat_sqrt[simp]: "sqrt_nat y = Discrete.sqrt y"
  using square_sqrt_nat_le lt_square_Suc_sqrt_nat
  by (intro sqrt_unique[symmetric]) auto

end

end
