open preamble ml_progLib ml_translatorLib
     basisFunctionsLib fsioProgLib
     cfTacticsLib cfLetAutoLib fsioConstantsProgTheory

open argsParseTheory pegTheory pegexecTheory

val _ = new_theory"argsParseProg";

val _ = translation_extends"fsioProg";


val INTRO_FLOOKUP = Q.store_thm("INTRO_FLOOKUP",
  `(if n IN FDOM G.rules
     then EV (G.rules ' n) i r y fk
     else Result xx) =
    (case FLOOKUP G.rules n of
       NONE => Result xx
     | SOME x => EV x i r y fk)`,
  SRW_TAC [] [finite_mapTheory.FLOOKUP_DEF]);

val coreloop_def' =
( pegexecTheory.coreloop_def
    |> REWRITE_RULE [INTRO_FLOOKUP]
    |> SPEC_ALL |> ONCE_REWRITE_RULE [FUN_EQ_THM]);

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  in def end

val _ = find_def_for_const := def_of_const;

val r = translate coreloop_def';

val r = translate (pegexecTheory.peg_exec_def);

val r = translate (argsPEG_def |> REWRITE_RULE [tokeq_def]);

val r = translate parse_args_def;

val termination_lemma =
  MATCH_MP pegexecTheory.coreloop_total wfG_argsPEG
  |> SIMP_RULE(srw_ss())[coreloop_def'];

val parse_args_side = Q.prove(
  `∀x. parse_args_side x = T`,
  rw[definition"parse_args_side_def"] \\
  rw[definition"peg_exec_side_def"] \\
  rw[definition"coreloop_side_def"]
  >- (qspec_then`add_locs x` strip_assume_tac (Q.GEN`i`termination_lemma) \\
      qmatch_abbrev_tac`IS_SOME (OWHILE f g h)` \\
      qmatch_assum_abbrev_tac`OWHILE f g' h = SOME _` \\
      `g' = g` by (
      unabbrev_all_tac
      \\ simp[FUN_EQ_THM]
      \\ Cases \\ simp[]
      \\ TOP_CASE_TAC \\ simp[] ) \\ fs[])
 >- (PairRules.PMATCH_MP peg_exec_total wfG_argsPEG
                         |> SIMP_RULE std_ss [argsPEG_start]
                         |> INST [``i : (char ,locs) alist`` |-> ``add_locs x``]
                         |> ASSUME_TAC  \\
     fs [definition"destresult_side_def"])) |> update_precondition;

val print_args_def = Define`
  print_args args =
    let prntarg a = case a of
                      | Option x (SOME y) => strlit (x ++ " -> " ++ y)
                      | Option x NONE => strlit (x ++ " -> NONE")
                      | Single x => strlit x
    in case parse_args args of
         | NONE   => (strlit "Error")
         | SOME l => concatWith (strlit "\n") (MAP prntarg l)
`;

val _ = export_theory()