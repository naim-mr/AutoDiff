open PPrint
open Surface

val print_expr : expr -> document
(**[print_expr] converts a Surface expression to a PPrint document. *)

val print_program : prog -> document
(**[print_program] converts a Surface program to a PPrint document. *)
