type key = string

type 'a env
(**An environment is an immutable map of identifiers (strings) to data. *)

val empty : 'a env
(**[empty] is the empty environment. *)

val lookup : 'a env -> key -> 'a
(**[lookup env x] returns the datum associated with [x] in the environment
   [env]. It raises [Not_found] if there is no such datum. *)

val bind : 'a env -> key -> 'a -> 'a env
(**[bind env x v] is an environment that extends [env] with a mapping of
   [x] to [v]. This new mapping can hide an existing mapping. *)

val remove : 'a env -> key -> 'a env
(**[remove env x] is an environment obtained from [env] by removing
   a mapping of [x] to some value, if there is one. *)

val bind_many : 'a env -> key list -> 'a list -> 'a env
(**[bind_many env xs vs] is an environment that extends [env] with a mapping
   of every variable in the list [xs] to the corresponding datum in the list
   [vs]. [Invalid_argument _] is raised if the lists [xs] and [vs] do not
   have the same length. *)

exception Collision of key

val bind_new : 'a env -> key -> 'a -> 'a env
(**[bind_new env x v] is an environment that extends [env] with a mapping of
   [x] to [v]. This new mapping is not allowed to hide an existing mapping:
   if this occurs, then [Collision x] is raised. *)

val bind_many_new : 'a env -> key list -> 'a list -> 'a env
(**[bind_many_new env xs vs] is an environment that extends [env] with a
   mapping of every variable in the list [xs] to the corresponding datum in
   the list [vs]. [Invalid_argument _] is raised if the lists [xs] and [vs]
   do not have the same length. The new mappings are created one by one, and
   [Collision _] is raised if a new mapping hides an earlier mapping. *)

val check_distinct : key list -> unit
(**[check_distinct xs] checks that the names in the list [xs] are pairwise
   distinct. If this is not the case, then [Collision _] is raised. *)

val is_empty : 'a env -> bool
(**[is_empty env] determines whether [env] is empty. *)

val extract : 'a env -> ('a env * key * 'a) option
(**If [env] is empty, then [extract env] returns [None]. Otherwise, it
   returns [Some (env', x, v)] where [x : v] is an arbitrary entry in
   [env] and [env'] is [env] deprived of this entry. *)

val bindings : 'a env -> (key * 'a) list
(**[bindings env] is a list of the key-value pairs in [env]. *)
