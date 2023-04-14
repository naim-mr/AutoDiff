open Surface

val print_type : ty -> string
(**[print_type] converts a type to a string. *)

exception Failure of string
(**This exception can be raised by [infer] and [check_expr]. *)

val on_failure : (string -> 'a) -> (unit -> 'a) -> 'a
(**[on_failure handle f] evaluates [f()] and returns its result.
   If [Failure msg] is raised, then [handle msg] is invoked. *)

val infer : prog -> fenv
(**[infer prog] verifies that the program [prog] is well-formed and
   well-typed. If so, a function type environment is returned. *)

val check_expr : fenv -> expr -> ty -> unit
(**[check_expr fenv e ty] checks that the closed expression [e]
   has type [ty] under the environment [fenv]. *)
