open Linear

(**A value is either a real number or a tuple of values. *)
type value = SurfaceInterpreter.value = VReal of real | VTuple of values

and values = value list

val print_value : value -> string
(**[print_value] converts a value to a string. *)

exception RuntimeError of Surface.range
(**[RuntimeError] is raised by [eval] when encountering an ill-formed
   or ill-typed program. *)

type env = value Env.env * value Env.env
(**A local variable environment is a pair of two maps: a map of unrestricted
   variables to values and a map of linear variables to values. *)

type result = values * values
(**Evaluating an expression returns a multi-value result, that is, a pair of a
   tuple of unrestricted values and a tuple of linear values. *)

val bind_many :
  env -> (uvar * _) list * (lvar * _) list -> values * values -> env

val eval : prog -> env -> expr -> result
(**[eval prog env e] evaluates the closed expression [e] in the context of the
   function definitions found in the program [prog] and in the local
   environment [env]. *)
