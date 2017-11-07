open preamble basis compilationLib
open argParseTheory pegTheory pegexecTheory

val _ = new_theory"argPrintProg";

val _ = translation_extends"basisProg";


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
                      | Option x (SOME y) => implode (x ++ " -> " ++ y)
                      | Option x NONE => implode (x ++ " -> NONE")
                      | Single x => implode x;
        argstr = explode (concatWith (implode " ") args)
    in case parse_args argstr of
         | NONE   => (implode "Error")
         | SOME l => concatWith (implode "\n") (MAP prntarg l)
`;

val r = translate print_args_def;

val main = process_topdecs
  `fun main u =
     let
       val cl = Commandline.arguments ()
       val args = print_args cl
       val ok = TextIO.print_string args
     in TextIO.print_newline() end`;

val () = append_prog main;

val st = get_ml_prog_state();

val main_spec = Q.store_thm("main",
  `!fs ls b bv.
   app (p:'ffi ffi_proj) ^(fetch_v "main" st) [Conv NONE []]
   (STDIO fs * COMMANDLINE cl)
   (POSTv uv. &UNIT_TYPE () uv *
      (STDIO (add_stdout fs (explode (print_args (MAP implode (TL cl))) ++ "\n"))) *
      COMMANDLINE cl)`,
  xcf "main" st \\
  cases_on`¬ STD_streams fs` >-(fs[STDIO_def] >> xpull) >>
  xlet_auto >- (xcon \\ xsimpl) \\
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull) \\
  `¬NULL cl` by fs[wfcl_def] \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  xlet`POSTv uv.  &UNIT_TYPE () uv * COMMANDLINE cl *
        STDIO (add_stdout fs (explode (print_args (MAP implode (TL cl)))))`
  >- (xapp >> xsimpl >> instantiate >> xsimpl >>
      (* TODO: why? *)
      qexists_tac`COMMANDLINE cl` >> xsimpl >>
      qexists_tac`fs` >> rw [MAP_TL] >> xsimpl) >>
  xlet_auto >- (xcon >> xsimpl) >>
  xapp >> xsimpl >>
  qmatch_goalsub_abbrev_tac`STDIO fs'` \\
  CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`fs'` \\
  unabbrev_all_tac \\
  simp[concatWith_CONCAT_WITH,MAP_TL,implode_def] \\
  xsimpl >> fs[] >>
  imp_res_tac STD_streams_stdout >>
  imp_res_tac add_stdo_o >> xsimpl);

val st = get_ml_prog_state();

val spec = main_spec |> SPEC_ALL |> UNDISCH_ALL |>
            SIMP_RULE(srw_ss())[STDIO_def] |>
            add_basis_proj;

val name = "main";
val (call_thm_main, main_prog_tm) = call_thm st name spec;
val main_prog_def = Define`main_prog = ^main_prog_tm`;

val main_semantics = save_thm("main_semantics",
  call_thm_main
  |> ONCE_REWRITE_RULE[GSYM main_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE std_ss [LENGTH,APPEND,AND_IMP_INTRO,STD_streams_add_stdout,GSYM CONJ_ASSOC]);

val main_compiled = save_thm("main_compiled",
  compile_x64 500 500 "main" main_prog_def);


val _ = export_theory()
