open preamble basis

val _ = new_theory"arg";

(* Datatype representing each posible argument/flag/option in a
   tipical command line argument list (eg: char* argv[] in C)
*)
val _ = Datatype`
  arg =
  (* Simple flags of the form -<ident> eg: -h *)
         ShortFlag mlstring
  (* Long flags of the form --<ident>+ eg: --help *)
       | LongFlag mlstring
  (* Long flags with option of the form --<ident>+=<ident>+
     eg: --arch=arm6 *)
       | OptionFlag mlstring mlstring
  (* Standalone option of the form <ident>+ eg: cake.S*)
       | Option mlstring
  (* Where <ident> is equal to the regular expression [a-zA-Z0-9.-/_]
     (or similar) *)
`;

(* An arbitrary term of 'arg' to serve as ARB in some definitions *)
val arb_arg_def = Define`
  arb_arg = Option (implode "")
`;

(* Destructors for 'arg' terms *)

val destShortFlag_def = Define`
  destShortFlag (ShortFlag flag) = flag ∧
  destShortFlag _ = (implode "")
`;

val destOption_def = Define`
  destOption (Option opt) = opt ∧
  destOption _ = (implode "")
`;

val destLongFlag_def = Define`
  destLongFlag (LongFlag flag) = flag ∧
  destLongFlag _ = (implode "")
`;

val destOptionFlag_def = Define`
  destOptionFlag (OptionFlag flag opt) = (flag,opt) ∧
  destOptionFlag _ = ((implode ""),(implode ""))
`;

(* Auxiliary functions *)

(* Get the name of each flag and the empty string in case of an option *)
val getFlagName_def = Define`
  getFlagName (ShortFlag f)    = f   ∧
  getFlagName (LongFlag f)     = f   ∧
  getFlagName (OptionFlag f _) = f ∧
  getFlagName _                = implode ""
`;

(* Wheter the argument is a Flag *)
val isFlag_def = Define`
  isFlag (Option _) = F ∧
  isFlag _          = T
`;

(* Pretty prints values or type 'arg' *)
val showFlag_def = Define`
  showFlag (ShortFlag f)     = implode "-"  ^ f ∧
  showFlag (LongFlag f)      = implode "--" ^ f ∧
  showFlag (OptionFlag f s)  = implode "--" ^ f ^ implode "=" ^ s ∧
  showFlag (Option s)        = s
`;

(* Expands shortFlag(s) into single values when grouped in a single
   shortFlag (eg: '[ShortFlag "ab"]' expands to [ShortFlag "a", ShortFlag "b"])
 *)

val expandArgs_def = Define`
  expandArgs l =
    let expandFlags = MAP (ShortFlag o str) o explode;
        expand = λx l.
          case x of ShortFlag x => expandFlags x ++ l
                  | _           => x :: l
    in FOLDR expand [] l
`;

(* Flags description types *)
val _ = Datatype`
  flag = <| name  : mlstring; (* Long flag  ("-"  if disable) *)
            short : char;     (* Short flag (#"-" if disable) *)
            desc  : mlstring; (* Short description used in the help msg *)
            opt   : bool;     (* Does it have and acompaning option/value? *)
            (* Continuation modifing the underlying structure
               representing the options where 'flag.cont opt x' takes
               an optional value 'opt' and a value 'x' of ''a' and
               uses these to update 'x' to represent the precense of
               the flag 'flag.name' or 'flag.short' with potentially
               some argument
             *)
            cont : mlstring option -> 'a -> 'a |>
`;


val matchArgs_def = Define`
  matchArg [] arg mOpt a = (if isFlag arg
                            then INL (implode "Unrecognized flag: " ^ showFlag arg)
                            (* TODO: Check for extra options *)
                            else INR (a,F)) ∧
  matchArg (f::fs) arg mOpt a =
    let flagName = getFlagName arg;
        strEq = (λx y. case compare x y of Equal => T | _ => F);
        pArg = showFlag arg;
        (* Does the current argument match with the current flag options? *)
        matchFlag  = (isFlag arg ∧ (* is the current argument a flag? *)
                     (strEq f.name flagName ∨  (* match the long name?  *)
                      strEq (str f.short) flagName)) (* match the short name? *)
    in if matchFlag
       then if f.opt
            then if IS_SOME mOpt
                 then INR (f.cont mOpt a,T)
                 else INL (implode "Missing value to: " ^ pArg)
            else case arg of
                     OptionFlag _ _ => INL (implode "Malformed flag: " ^ pArg)
                  | _               => INR (f.cont NONE a,F)
       else matchArg fs arg mOpt a
`;

val mkArgsConf_def = tDefine "mkArgsConf" `
  mkArgsConf fs a [] = INR a ∧
  mkArgsConf fs a (x::xs) =
    let flagOpt = (* Tries to find and option after a flag *)
          case xs of (* Look for the tail of the argument list *)
              []      => NONE (* If empty there is no extra option *)
            | (x::xs) => if isFlag x (* is the next value a flag? *)
                         then NONE   (* There is no option then *)
                         else SOME (destOption x) (* That is you options *)
    in
    case matchArg fs x flagOpt a of
        INL m => INL m
     |  INR (b,T) => mkArgsConf fs b (DROP 1 xs)
     |  INR (b,F) => mkArgsConf fs b xs`
(wf_rel_tac `measure (LENGTH o SND o SND)` >> rw [LENGTH]);


val test_conf_def = Define`
  test_conf = mkArgsConf [<| name  := implode "one" ;
                             short := #"1" ;
                             desc  := implode "flag1" ;
                             opt   := F;
                             cont  := K (λx. case x of (_,b,c) => (T,b,c))|>;
                          <| name  := implode "two" ;
                             short := #"2" ;
                             desc  := implode "flag2" ;
                             opt   := T;
                             cont  := (λx y. case y of (a,_,c) => (a,x,c))|>;
                          <| name  := implode "three" ;
                             short := #"3" ;
                             desc  := implode "flag3" ;
                             opt   := F;
                             cont  := K (λx. case x of (a,b,_) => (a,b,T))|>
                         ]
                    (F,NONE,F)
`;

val _ = export_theory()
