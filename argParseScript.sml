open preamble basis

open pegTheory pegexecTheory pegLib

open argTheory

val _ = new_theory"argParse";

(* Non Terminal for the grammar *)
val _ = Datatype`
  arg_NT = init_NT
         | ShortFlag_NT
         | LongFlag_NT
         | OptionFlag_NT
         | Option_NT
`;

(* Some abbreviations to make things nicer *)
val _ = type_abbrev("NT", ``:arg_NT inf``);
val _ = overload_on("mkNT", ``INL : arg_NT -> NT``);


(* Generates a 'pegsym' non terminal from a 'arg_NT' *)
(* TODO: maybe generalize this? *)
val pnt_def = Define`pnt ntsym = nt (mkNT ntsym) I`;

(* have to use these versions of choicel and pegf below because the
   versions from pegTheory use ARB in their definitions.
   Logically, the ARBs are harmless, but they completely mess with the
   CakeML translator.
*)

(* Chooses from a list of posible options *)
val choicel_def = Define`
  choicel [] = not (empty arb_arg) arb_arg ∧
  choicel (h::t) = choice h (choicel t) (λs. case s of INL x => x | INR y => y)
`;

(* Applies a function over the result of 'sym' *)
val pegf_def = Define`pegf sym f = seq sym (empty arb_arg) (λl1 l2. f l1)`;

(* Some proofs about pegf and choicel *)

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

val tokeq_def = Define`tokeq t f = tok ((=) t) (K (f t))`;

val grabWS_def = Define`
  grabWS s = rpt (tok isSpace (K arb_arg)) (K arb_arg) ~> s
`;

(* Identifiers *)
(* TODO: add extra characters [-._/\] *)
val ident_def = Define`
  ident = let id      = tok isAlphaNum (λt. Option (implode [FST t]));
              arb_str = implode "";
              joins   = Option o FOLDR (λw l. strcat (destOption w) l) arb_str;
              join    = (λx y. Option (strcat (destOption x) (destOption y)))
          in seq id (rpt id joins) join

`;

val argPEG_def = zDefine`
  argPEG : (char, arg_NT, arg) peg = <|
    start := pnt init_NT ;
    rules :=
    FEMPTY |++
    (*  A argument is one of four options *)
    [(mkNT init_NT, choicel [pnt ShortFlag_NT;
                             pnt LongFlag_NT;
                             pnt OptionFlag_NT;
                             pnt Option_NT]);
     (* A short flag, containing 1 or more letters, each letter
        representing a diferent flag
      *)
     (mkNT ShortFlag_NT, tokeq #"-" (K arb_arg) ~>
                               pegf ident (ShortFlag o destOption));
     (* A long flag *)
     (mkNT LongFlag_NT, (tokeq #"-" (K arb_arg) ~> tokeq #"-" (K arb_arg) ~>
                              pegf ident (LongFlag o destOption))
                         <~ not (tokeq #"=" (K arb_arg)) arb_arg);
     (* A Composed flag with an attached value *)
     (mkNT OptionFlag_NT, tokeq #"-" (K arb_arg) ~> tokeq #"-" (K arb_arg) ~>
                             seq ident                      (* Flag *)
                                 (tokeq #"=" (K arb_arg) ~> (* = *)
                                 ident)                     (* Value *)
                                 (λopt str. OptionFlag (destOption opt)
                                                       (destOption str)));
     (* Any other option *)
     (mkNT Option_NT, ident)
    ]|>
`;

(* wfG proof for argPEG *)
val argPEG_start = save_thm(
  "argPEG_start[simp]",
  SIMP_CONV(srw_ss())[argPEG_def]``argPEG.start``);

val ds = derive_compset_distincts ``:arg_NT``
val {lookups,fdom_thm,applieds} =
  derive_lookup_ths {pegth = argPEG_def
                    , ntty = ``:arg_NT``
                    , simp = SIMP_CONV (srw_ss())};

val argPEG_exec_thm = save_thm(
  "argPEG_exec_thm",
  LIST_CONJ(argPEG_start::ds::lookups));

val _ = computeLib.add_persistent_funs["argPEG_exec_thm"];
val _ = save_thm("FDOM_argPEG", fdom_thm);
val _ = save_thm("argPEG_applied", LIST_CONJ applieds);

val frange_image = prove(
  ``FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)``,
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION] >> metis_tac[]);

val argPEG_range =
    SIMP_CONV (srw_ss())
              (fdom_thm :: frange_image :: applieds)
              ``FRANGE argPEG.rules``;

val subexprs_pnt = prove(
  ``subexprs (pnt n) = {pnt n}``,
  simp[subexprs_def, pnt_def]);

val Gexprs_argPEG = save_thm(
  "Gexprs_argPEG",
  ``Gexprs argPEG``
    |> SIMP_CONV (srw_ss())
         [Gexprs_def, subexprs_def,
          subexprs_pnt, argPEG_start, argPEG_range,
          ignoreR_def, ignoreL_def,
          choicel_def, tokeq_def, pegf_def, grabWS_def,
          checkAhead_def,
          pred_setTheory.INSERT_UNION_EQ
         ]);

val wfpeg_rwts = wfpeg_cases
                   |> ISPEC ``argPEG``
                   |> (fn th => map (fn t => Q.SPEC t th)
                                    [`seq e1 e2 f`, `choice e1 e2 f`, `tok P f`,
                                     `any f`, `empty v`, `not e v`, `rpt e f`,
                                     `tokeq t f`, `pegf e f`, `choicel []`,
                                     `choicel (h::l)`
                      ])
                   |> map (CONV_RULE
                             (RAND_CONV (SIMP_CONV (srw_ss())
                                [choicel_def, tokeq_def, ignoreL_def,
                                 ignoreR_def, pegf_def, grabWS_def])));

val peg0_grabWS = Q.prove(
  `peg0 argPEG (grabWS e) = peg0 argPEG e`,
  simp [ignoreL_def, grabWS_def, peg0_rules]);

val wfpeg_grabWS = (* wfpeg argPEG (grabWS e) ⇔ wfpeg argPEG e *)
  SIMP_CONV (srw_ss()) ([grabWS_def, ignoreL_def, peg0_grabWS] @ wfpeg_rwts)
                       ``wfpeg argPEG (grabWS e)``;

val wfpeg_pnt = wfpeg_cases
                  |> ISPEC ``argPEG``
                  |> Q.SPEC `pnt n`
                  |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def]));


val peg0_rwts = peg0_cases
                  |> ISPEC ``argPEG`` |> CONJUNCTS
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
                      |> ISPEC ``argPEG`` |> CONJUNCTS
                      |> map (Q.SPEC `pnt n`)
                      |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def])))

fun pegnt(t,acc) = let
  val th =
      prove(``¬peg0 argPEG (pnt ^t)``,
            simp (pegf_def::ident_def::fdom_thm::choicel_def::ignoreL_def::grabWS_def::ignoreR_def::applieds @ pegnt_case_ths) >>
            simp(peg0_rwts @ acc))
  val nm = "peg0_" ^ term_to_string t
  val th' = save_thm(nm, SIMP_RULE bool_ss [pnt_def] th)
  val _ = export_rewrites [nm]
in
  th::acc
end;

val npeg0_rwts =
    List.foldl pegnt []
   [``ShortFlag_NT``
   ,``LongFlag_NT``
   ,``OptionFlag_NT``
   ,``Option_NT``];

fun wfnt(t,acc) = let
  val th =
    prove(``wfpeg argPEG (pnt ^t)``,
          SIMP_TAC (srw_ss())
                   (applieds @
                    [wfpeg_pnt, fdom_thm, ignoreL_def, ignoreR_def,
                     checkAhead_def, ident_def]) THEN
          fs(peg0_grabWS :: wfpeg_grabWS :: wfpeg_rwts @ npeg0_rwts @ acc) THEN
         rw [choicel_def])
in
  th::acc
end;

val wfpeg_thm = LIST_CONJ (List.foldl wfnt [] [``ShortFlag_NT``
                                              ,``LongFlag_NT``
                                              ,``OptionFlag_NT``
                                              ,``Option_NT``
                                              ,``init_NT``]);

(* This is the actual well-formedness proof for argPEG *)
val wfG_argPEG = store_thm(
  "wfG_argPEG",
  ``wfG argPEG``,
  rw[wfG_def,Gexprs_argPEG,ident_def] >>
  srw_tac[boolSimps.DNF_ss][] >>
  simp(wfpeg_thm :: wfpeg_rwts));

(* Export 'wfG argPEG' into the simpset *)
val _ = export_rewrites ["wfG_argPEG"];

(* Setup monad syntax for the 'option' monad *)
val _ = monadsyntax.temp_add_monadsyntax()
val _ = overload_on ("monad_bind", “OPTION_BIND”)
val _ = overload_on ("assert", “OPTION_GUARD”)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def",
                                        "option.OPTION_IGNORE_BIND_def",
                                        "option.OPTION_GUARD_def",
                                        "option.OPTION_CHOICE_def"];


(* Default start location *)
(* TODO: make sure this is correct *)
val start_locs_def = Define`
  start_locs : locs = Locs (<|row := 0 ; col := 0 ; offset := 0|>)
                           (<|row := 0 ; col := 0 ; offset := 0|>)
`;

(* Given a 'string' generates a '(char, locs) alist' with information
   about the location of each character in the string
*)
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

val parse_arg_def = Define`
  parse_arg s = do
    (rest,args) <- destResult (peg_exec argPEG (pnt init_NT) (add_locs s) [] done failed);
    if rest <> [] then NONE else SOME args
  od
`;

val parse_arg_list_aux = Define`
  parse_arg_list_aux [] fs      = INR (REVERSE fs) ∧
  parse_arg_list_aux (x::xs) fs =
    case parse_arg x of
        NONE   => INL ("Parse error on: " ++ x)
      | SOME s => parse_arg_list_aux xs (s::fs)
`;

val parse_arg_list_def = Define`
  parse_arg_list l = parse_arg_list_aux l []
`;

val parse_conf_def = Define`
  parse_conf l conf = case parse_arg_list l of
                          INL m    => INL (implode m)
                       |  INR args => conf args
`;

val _ = export_theory()
