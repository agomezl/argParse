open preamble basisFunctionsLib

open pegTheory pegexecTheory pegLib


val _ = new_theory"argsParse";

val _ = Datatype`
  args = Single string
       | Option string (string option)
`;

val arb_option_def = Define`
  arb_option = Single ""
`;

val destSingle_def = Define`
  destSingle (Single s) = s ∧
  destSingle _ = ""
`;

val destOption_def = Define`
  destOption (Option opt (SOME arg)) = (opt, arg) ∧
  destOption (Option opt NONE) = (opt, "") ∧
  destOption _ = ("","")
`;

val _ = Datatype`
  args_NT = argList_NT
          | argOption_NT
          | argSingle_NT
`;

val _ = type_abbrev("NT", ``:args_NT inf``);
val _ = overload_on("mkNT", ``INL : args_NT -> NT``);

val pnt_def = Define`pnt ntsym = nt (mkNT ntsym) I`;

(* have to use these versions of choicel and pegf below because the
   versions from pegTheory use ARB in their definitions.
   Logically, the ARBs are harmless, but they completely mess with the
   CakeML translator.
*)
val choicel_def = Define`
  choicel [] = not (empty ([] : args list)) [] ∧
  choicel (h::t) = choice h (choicel t) (λs. case s of INL x => x | INR y => y)
`;

val pegf_def = Define`pegf sym f = seq sym (empty ([] : args list)) (λl1 l2. f l1)`;

val seql_def = Define`
  seql l f = pegf (FOLDR (\p acc. seq p acc (++)) (empty []) l) f
`;

val peg_eval_choicel_NIL = store_thm(
  "peg_eval_choicel_NIL[simp]",
  ``peg_eval G (i0, choicel []) x = (x = NONE)``,
  simp[choicel_def, Once peg_eval_cases]);

val peg_eval_choicel_CONS = store_thm(
  "peg_eval_choicel_CONS",
  ``∀x. peg_eval G (i0, choicel (h::t)) x ⇔
          peg_eval G (i0, h) x ∧ x <> NONE ∨
          peg_eval G (i0,h) NONE ∧ peg_eval G (i0, choicel t) x``,
  simp[choicel_def, SimpLHS, Once peg_eval_cases] >>
  simp[pairTheory.FORALL_PROD, optionTheory.FORALL_OPTION]);

val peg0_choicel = store_thm(
  "peg0_choicel[simp]",
  ``(peg0 G (choicel []) = F) ∧
    (peg0 G (choicel (h::t)) ⇔ peg0 G h ∨ pegfail G h ∧ peg0 G (choicel t))``,
  simp[choicel_def])

val peg0_pegf = store_thm(
  "peg0_pegf[simp]",
  ``peg0 G (pegf s f) = peg0 G s``,
  simp[pegf_def])

val tokeq_def = Define`tokeq t f = tok ((=) t) (K (f t))`
val grabWS_def = Define`
  grabWS s = rpt (tok isSpace (K [arb_option])) (K [arb_option]) ~> s
`;

val ident_def = Define`
  ident = rpt (tok isAlphaNum (λt. [Single [FST t]]))
              ((λn. if n = "" then [] else [Single n]) o CONCAT o (MAP (CONCAT o MAP destSingle)))
`;

val argsPEG_def = zDefine`
  argsPEG : (char, args_NT, args list) peg = <|
    start := pnt argList_NT ;
    rules :=
    FEMPTY |++
    [(mkNT argList_NT, grabWS (choicel [seq (choice (pnt argOption_NT)
                                                    (pnt argSingle_NT)
                                                    (λs. case s of INL x => x
                                                                 | INR y => y))
                                            (pnt argList_NT)
                                            (++);
                                        empty []]));
     (mkNT argSingle_NT, tokeq #"-" (K []) ~> tok isAlphaNum (λt. [Single [FST t]]));
     (mkNT argOption_NT, seq (seql [tokeq #"-" (K []); tokeq #"-" (K [])] (K []) ~> ident)
                             (grabWS ident)
                             (λopt arg. [Option (FOLDR (λa b. destSingle a) [] opt)
                                                (FOLDR (λa b. SOME (destSingle a)) NONE arg)]))
    ]|>
`;

(* wfG proof *)

val argsPEG_start = save_thm(
  "argsPEG_start[simp]",
  SIMP_CONV(srw_ss())[argsPEG_def]``argsPEG.start``);

val ds = derive_compset_distincts ``:args_NT``
val {lookups,fdom_thm,applieds} =
  derive_lookup_ths {pegth = argsPEG_def
                    , ntty = ``:args_NT``
                    , simp = SIMP_CONV (srw_ss())};

val argsPEG_exec_thm = save_thm(
  "argsPEG_exec_thm",
  LIST_CONJ(argsPEG_start::ds::lookups));

val _ = computeLib.add_persistent_funs["argsPEG_exec_thm"];
val _ = save_thm("FDOM_argsPEG", fdom_thm);
val _ = save_thm("argsPEG_applied", LIST_CONJ applieds);

val frange_image = prove(
  ``FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)``,
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION] >> metis_tac[]);

val argsPEG_range =
    SIMP_CONV (srw_ss())
              (fdom_thm :: frange_image :: applieds)
              ``FRANGE argsPEG.rules``;

val subexprs_pnt = prove(
  ``subexprs (pnt n) = {pnt n}``,
  simp[subexprs_def, pnt_def]);

val Gexprs_argsPEG = save_thm(
  "Gexprs_argsPEG",
  ``Gexprs argsPEG``
    |> SIMP_CONV (srw_ss())
         [Gexprs_def, subexprs_def,
          subexprs_pnt, argsPEG_start, argsPEG_range,
          ignoreR_def, ignoreL_def,
          choicel_def, tokeq_def, pegf_def, grabWS_def,
          checkAhead_def, seql_def,
          pred_setTheory.INSERT_UNION_EQ
         ]);


val wfpeg_rwts = wfpeg_cases
                   |> ISPEC ``argsPEG``
                   |> (fn th => map (fn t => Q.SPEC t th)
                                    [`seq e1 e2 f`, `choice e1 e2 f`, `tok P f`,
                                     `any f`, `empty v`, `not e v`, `rpt e f`,
                                     `tokeq t f`, `pegf e f`, `choicel []`,
                                     `choicel (h::l)`
                      ])
                   |> map (CONV_RULE
                             (RAND_CONV (SIMP_CONV (srw_ss())
                                [choicel_def, tokeq_def, ignoreL_def,
                                 ignoreR_def, pegf_def, grabWS_def, seql_def])));

val peg0_grabWS = Q.prove(
  `peg0 argsPEG (grabWS e) = peg0 argsPEG e`,
  simp [ignoreL_def, grabWS_def, peg0_rules]);

val wfpeg_grabWS = (* wfpeg argsPEG (grabWS e) ⇔ wfpeg argsPEG e *)
  SIMP_CONV (srw_ss()) ([grabWS_def, ignoreL_def, peg0_grabWS] @ wfpeg_rwts)
                       ``wfpeg argsPEG (grabWS e)``;

val peg0_seql = store_thm(
  "peg0_seql",
  ``(peg0 G (seql [] f) ⇔ T) ∧
    (peg0 G (seql (h::t) f) ⇔ peg0 G h ∧ peg0 G (seql t I))``,
  simp[seql_def]);

val wfpeg_seql = (* wfpeg argsPEG (grabWS e) ⇔ wfpeg argsPEG e *)
  SIMP_CONV (srw_ss()) ([seql_def, ignoreL_def, peg0_seql] @ wfpeg_rwts)
                       ``wfpeg argsPEG (seql l f)``;

val wfpeg_pnt = wfpeg_cases
                  |> ISPEC ``argsPEG``
                  |> Q.SPEC `pnt n`
                  |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def]));


val peg0_rwts = peg0_cases
                  |> ISPEC ``argsPEG`` |> CONJUNCTS
                  |> map (fn th => map (fn t => Q.SPEC t th)
                                       [`tok P f`, `choice e1 e2 f`, `seq e1 e2 f`,
                                        `tokeq t f`, `empty l`, `not e v`, `rpt e f`])
                  |> List.concat
                  |> map (CONV_RULE
                            (RAND_CONV (SIMP_CONV (srw_ss())
                                                  [tokeq_def])));


val pegfail_t = ``pegfail``;

val peg0_rwts = let
  fun filterthis th = let
    val c = concl th
    val (l,r) = dest_eq c
    val (f,_) = strip_comb l
  in
    not (same_const pegfail_t f) orelse is_const r
  end
in
  List.filter filterthis peg0_rwts
end;

val pegnt_case_ths = peg0_cases
                      |> ISPEC ``argsPEG`` |> CONJUNCTS
                      |> map (Q.SPEC `pnt n`)
                      |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def])))

fun pegnt(t,acc) = let
  val th =
      prove(``¬peg0 argsPEG (pnt ^t)``,
            simp (seql_def::ident_def::fdom_thm::choicel_def::ignoreL_def::grabWS_def::ignoreR_def::applieds @ pegnt_case_ths) >>
            simp(peg0_rwts @ acc))
  val nm = "peg0_" ^ term_to_string t
  val th' = save_thm(nm, SIMP_RULE bool_ss [pnt_def] th)
  val _ = export_rewrites [nm]
in
  th::acc
end;

val npeg0_rwts =
    List.foldl pegnt []
   [``argOption_NT``,
    ``argSingle_NT``];

fun wfnt(t,acc) = let
  val th =
    prove(``wfpeg argsPEG (pnt ^t)``,
          SIMP_TAC (srw_ss())
                   (applieds @
                    [wfpeg_pnt, fdom_thm, ignoreL_def, ignoreR_def,
                     checkAhead_def, ident_def]) THEN
          fs(peg0_seql :: peg0_grabWS :: wfpeg_seql :: wfpeg_grabWS :: wfpeg_rwts @ npeg0_rwts @ acc) THEN
         rw [choicel_def])
in
  th::acc
end;

val wfpeg_thm = LIST_CONJ (List.foldl wfnt [] [``argOption_NT``,
                                               ``argSingle_NT``,
                                               ``argList_NT``]);

val wfG_argsPEG = store_thm(
  "wfG_argsPEG",
  ``wfG argsPEG``,
  rw[wfG_def,Gexprs_argsPEG,ident_def] >>
  srw_tac[boolSimps.DNF_ss][] >>
  simp(wfpeg_thm :: wfpeg_rwts));

val _ = export_rewrites ["wfG_argsPEG"];


val _ = monadsyntax.temp_add_monadsyntax()
val _ = overload_on ("monad_bind", “OPTION_BIND”)
val _ = overload_on ("assert", “OPTION_GUARD”)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def",
                                        "option.OPTION_IGNORE_BIND_def",
                                        "option.OPTION_GUARD_def",
                                        "option.OPTION_CHOICE_def"];


val start_locs_def = Define`
  start_locs : locs = Locs (<|row := 0 ; col := 0 ; offset := 0|>)
                           (<|row := 0 ; col := 0 ; offset := 0|>)
`;

val add_locs_def = Define`
  add_locs l =
    let new_char loc = loc with <| col  := loc.col + 1 ;
                                 offset := loc.offset + 1 |>;
        new_line loc = loc with <| row  := loc.row + 1 ;
                                 offset := loc.offset + 1 ;
                                 col    := 0 |>;
       update_locs locs f = locs_CASE locs (λl r. Locs (f l) (f r));
       update c (locs,s) = case c of
                            | #"\n" => let l = update_locs locs new_line
                                       in (l,(#"\n",l)::s)
                            | _     => let l = update_locs locs new_char
                                       in (l,(c,l)::s)
    in SND (FOLDR update (start_locs,[]) l)
`;

val parse_args_def = Define`
  parse_args s = do
    (rest,args) <- destResult (peg_exec argsPEG (pnt argList_NT) (add_locs s) [] done failed);
    if rest <> [] then NONE else SOME args
  od
`;


val _ = export_theory()
