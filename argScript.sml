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

val _ = export_theory()
