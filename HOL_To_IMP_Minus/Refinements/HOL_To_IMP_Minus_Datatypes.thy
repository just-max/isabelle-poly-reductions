\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Datatypes
  imports
    HOL_To_IMP_Minus_Arithmetics
  keywords
    "unrelate_nat" :: thy_decl
begin

(* obviously don't do this, but how to declare constants from within a command??? *)
consts some_const :: "nat \<Rightarrow> nat \<Rightarrow> nat"

locale HOL_To_HOL_Nat =
  notes transport_eq_id.partial_equivalence_rel_equivalenceI[per_intro del]
  and transport_eq_restrict_id.partial_equivalence_rel_equivalence[per_intro del]
begin

fun rev_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_aux acc [] = acc" |
  "rev_aux acc (x # xs) = rev_aux (x # acc) xs"

case_of_simps rev_aux_eq (* [simplified Nitpick.case_nat_unfold] *) : rev_aux.simps

function_compile_nat rev_aux_eq
print_theorems

(*
thm zip.simps

fun zip :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
  "zip (x # xs) (y # ys) = (x, y) # zip xs ys" |
  "zip _ _ = []"

case_of_simps zip_eq : zip.simps
function_compile_nat zip_eq
print_theorems
thm zip_nat_eq_unfolded[simplified case_list_nat_def]
fun zip_nat_magic :: "nat \<Rightarrow> nat \<Rightarrow> nat"  where
  "zip_nat_magic x xa =
  (if fst_nat x = 0 then Nil_nat
   else if fst_nat xa = 0 then Nil_nat
   else
     Cons_nat
       (Pair_nat (fst_nat (snd_nat x)) (fst_nat (snd_nat xa)))
       (zip_nat_magic (snd_nat (snd_nat x)) (snd_nat (snd_nat xa))))"
*)

definition rev :: "'a list \<Rightarrow> 'a list" where
  "rev = rev_aux []"

function_compile_nat rev_def

end


context HOL_To_IMP_Minus
begin

compile_nat Cons_nat_def
HOL_To_IMP_Minus_correct Cons_nat by cook

compile_nat Nil_nat_def
HOL_To_IMP_Minus_correct Nil_nat by cook


ML\<open>

(* structure BU = BNF_Util *)
structure HTHNU = HOL_To_HOL_Nat_Util

(*
fun register_fun binding_name lhs rhs lthy =
  let
    val l = Syntax.pretty_term lthy #> Pretty.writeln
    val _ = (@{print} (binding_name, lhs, rhs); l lhs; l rhs)
    val fixes = [(binding_name, SOME (Term.head_of lhs |> Term.fastype_of), NoSyn)]
    val specs = [((Binding.empty_atts, BU.mk_Trueprop_eq (lhs, rhs)), [], [])]
  in Function_Fun.add_fun fixes specs Function_Fun.fun_config lthy end *)

fun unrelate_nat_command f_eq _ lthy =
  let
    val (lhs, rhs) = HTHNU.dest_eq_equals_thm f_eq
    val f as (f_name, f_typ) =  lhs |> Term.head_of |> Term.dest_Const

    fun is_typrep (Type (@{type_name itself}, [_])) = true | is_typrep _ = false
    fun is_nat (Type (@{type_name nat}, [])) = true | is_nat _ = false
    val (typrep_arg_count, rem_args) =
      Term.args_of lhs
      |> chop_prefix (is_typrep o Term.fastype_of)
      |>> List.length
    val _ =
      (List.all (is_nat o Term.fastype_of) rem_args andalso is_nat (Term.fastype_of lhs))
      orelse raise TERM ("Expected type: function taking zero or more '_ itself' arguments, followed by zero or more 'nat' arguments, and returning 'nat'", [lhs])

    val f'_typ = List.map Term.fastype_of rem_args ---> @{typ nat}

    (* val _ = Proof_Context.theory_of *)
    (* val _ = Proof_Context.init_global *)
    val t = @{const some_const}
    val binding = Binding.name (Term.dest_Const_name t) (* "some_const" *)
    (* val (t, lthy' : theory) =
      Sign.declare_const lthy ((binding, f'_typ), NoSyn) (Context.theory_of (Context.Proof lthy)) *)

    val f'_name = Term.dest_Const_name t
    val _ = @{print} f'_name
    val f' = Const (f'_name, f'_typ)

    val rewrite_vars = Term.map_aterms (fn Var ((name, _), typ) => Free (name, typ) | t => t)

    fun rewrite_rhs t =
      let
        val (head, args) = Term.strip_comb t
        val is_rec_call = case head of Const g => f = g | _ => false
        val _ = (is_rec_call andalso length args < typrep_arg_count)
          andalso raise TERM ("Can't strip all '_ itself' arguments", [t])
        val head' = if is_rec_call then f' else head
        val args' =
          (if is_rec_call then drop typrep_arg_count args else args)
          |> map rewrite_rhs
      in Term.list_comb (head', args') end

    val lhs' = Term.list_comb (f', rem_args) |> rewrite_vars
    val rhs' = rhs |> rewrite_rhs |> rewrite_vars

    (* val _ = HOLogic.mk_eq (lhs', rhs') |> Thm.cterm_of lthy |> @{print} *)

    val lthy' = HTHNU.register_fun binding lhs' rhs' lthy

  in lthy' end

local
  val parser = Parse.thm -- Scan.option (\<^keyword>\<open>basename\<close> |-- Parse.name_position)
in
  val _ = Outer_Syntax.local_theory
    \<^command_keyword>\<open>unrelate_nat\<close>
    "remove Rel_nat/rel_fun assumptions and TYPE(_) args"
    (parser >> (fn ((thm_ref, _), namepos_opt) => fn lthy =>
      let val thm = Proof_Context.get_fact lthy thm_ref |> the_single
      in unrelate_nat_command thm namepos_opt lthy end))
end
\<close>

lemmas rev_aux_nat_eq = HOL_To_HOL_Nat.rev_aux_nat_eq_unfolded[simplified case_list_nat_def]
unrelate_nat rev_aux_nat_eq basename base1


(* TODO: magic, goal: *)
(*
fun rev_aux_nat_magic where
  "rev_aux_nat_magic x xa =
    (if fst_nat xa = 0 then x
     else rev_aux_nat_magic (Cons_nat (fst_nat (snd_nat xa)) x) (snd_nat (snd_nat xa)))"

declare rev_aux_nat_magic.simps[simp del]

compile_nat rev_aux_nat_magic.simps
HOL_To_IMP_Minus_correct rev_aux_nat_magic by (cook mode = tailcall)
*)

end

end
