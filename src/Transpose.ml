(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-27-32-33-39"]

open Linear
open LinearHelp
open LinearHelp.Constructors
open LVarSet

let length, map, zip = List.(length, map, combine)
let assoc xs x = List.assoc x xs

(* -------------------------------------------------------------------------- *)

(* Naming conventions. *)

(* For each function [f] in the source program, if [f] has no unrestricted
   outputs, then we transpose [f] and define a function [tf]. *)

(* -------------------------------------------------------------------------- *)

(* Linear type environments. *)

type lenv = ty Env.env

let llookup (lenv : lenv) (L x : lvar) : ty =
  try Env.lookup lenv x with Not_found -> assert false

let lbind (lenv : lenv) ((L x, ty) : lbinding) : lenv = Env.bind lenv x ty

let lbind_many (lenv : lenv) (lbs : lbindings) : lenv =
  List.fold_left lbind lenv lbs

(* -------------------------------------------------------------------------- *)
(* Utils functions *)
let rec n_first l n =
  match (l, n) with
  | [], _ -> []
  | x :: q, 0 -> []
  | x :: q, n -> x :: n_first q (n - 1)

let separate l n =
  match (l, n) with
  | [], _ -> ([], [])
  | x :: q, 0 -> ([], x :: q)
  | x :: q, n -> (x :: n_first q (n - 1), [])

let pop_lv u = match u with L s -> s
let pop_uv u = match u with U s -> s

(* -------------------------------------------------------------------------- *)
(* Transposing an expression. *)

(* An expression [e] can be thought of as a data flow graph whose input wires
   are named (they are represented by free variables) and whose output wires
   are numbered (they are represented by a position in a [Ret] expression). *)

(* When transposing an expression [e], yielding a new expression [t], the
   linear inputs of [e] become linear outputs of [t], and the linear outputs
   of [e] become linear inputs of [t]. Thus, for each (named) linear input of
   [e], we must provide a number (its desired position in the output of [t]);
   and, for each (numbered) linear output of [e], we must provide a name (its
   name as an input wire of [t]). We do so as follows:

   - The list [inputs] is a list of the free linear variables of [e], in a
     certain order. (This list corresponds to Delta-dot in the paper.) It
     defines a bijection between the linear inputs of [e] and their indices.
     This list determines in what order the transposed expression [t] must
     produce its outputs.

   - The list [outputs] is a list of variables whose length must be the linear
     output arity of [e], that is, the number of linear results of [e].
     (This list corresponds to Delta-dot-dot in the paper.)
     This list assigns a name to every linear output of [e]. These names
     become the free linear variables of the transposed expression [t]. *)

(* We assume that [e] has zero unrestricted outputs. *)

(* [e] may have unrestricted inputs, but these are not a source of worry. The
   free unrestricted variables of [e] are also free unrestricted variables in
   the transposed expression. *)

(* The type environment [lenv] must map every linear variable to its type.
   It is used in the case of [Drop x]: in this case, we return [LZero ty]
   where [ty] is the type of [x]. *)

(* The function type environment [fenv] is used in an assertion in the case
   [FunCall _]. It is otherwise not needed. *)

let print_expr e =
  let open LinearPrinter in
  print_string
    (" --- ["
    ^ PPrintExtra.to_string
        (LinearPrinter.expr { ranges = RangeSet.empty; style = No_highlight } e)
    ^ "] --- \n")

let rec transform_expr (fenv : fenv) (lenv : lenv) (inputs : lvars)
    (outputs : lvars) (e : expr) : expr =
  (*

      print_endline "outputs : \n";
    List.iter (fun a -> Printf.printf "%s" (pop_lv a)) outputs;
    print_endline "\ninputs : ";
    List.iter (fun a -> Printf.printf "%s" (pop_lv a)) inputs;
    print_endline "\n fle :";

    LVarSet.iter ((fun a -> Printf.printf "%s" (pop_lv a))) (flv e);
    print_endline "----";*)
  (* The lists [inputs] and [outputs] must contain distinct names. *)
  assert (pairwise_distinct inputs);
  assert (pairwise_distinct outputs);
  (* The free linear variables of [e] must match the list [inputs]. *)
  assert (equal (of_list inputs) (flv e));

  (* The free linear variables of the transposed expression (which we
     are about to construct) must match the list [outputs]. *)
  let t : expr =
    match e with
    (* TRet *)
    | Ret ([], lvs) -> Ret ([], outputs)
    (* TLetLin *)
    | Let ([], lbs, e1, e2) ->
        (* free variable in e1*)
        let fle = flv e1 in
        (* delta_dot_1 , delta_dot_2 *)
        let input1, input2 =
          List.partition (fun a -> LVarSet.mem a fle) inputs
        in
        (* Create the correspondings lists of bidings*)
        let intpu1_bidings = List.map (fun d -> (d, llookup lenv d)) input1 in
        let input2_binding = List.map (fun l -> (l, llookup lenv l)) input2 in
        (* Prepare sub env *)
        let env1 = lbind_many Env.empty lbs in
        let env1 = lbind_many env1 intpu1_bidings in
        (* Compute dod_dot_e1*)
        let dde1 = transform_expr fenv env1 input1 (List.map fst lbs) e1 in

        (* Prepare sub env *)
        let env2 =
          lbind_many Env.empty
            (List.map (fun d -> (d, llookup lenv d)) input2 @ lbs)
        in
        let env2 = lbind_many env2 lbs in
        (* Compute dod_dot_e2*)
        let dde2 =
          transform_expr fenv env2 (input2 @ List.map fst lbs) outputs e2
        in

        (* We need to make the invariant order always valid, that's why we use lwiden to manage the outputs wires *)
        Let ([], input2_binding @ lbs, dde2, lwiden input1 inputs dde1)
    (* TLetNonLin *)
    | Let (ubs, [], e1, e2) ->
        let dde2 = transform_expr fenv lenv inputs outputs e2 in
        Let (ubs, [], e1, dde2)
    (* TLinUnpack *)
    | LTupleElim (lbs, l, e) ->
        (* Similar to TLinLet. *)
        let input1, input2 = ([ l ], List.filter (fun x -> x <> l) inputs) in
        let input2_binding = List.map (fun l -> (l, llookup lenv l)) input2 in
        let lvs = List.map fst lbs in
        let env = lbind_many Env.empty input2_binding in
        let env = lbind_many env lbs in
        let dde = transform_expr fenv env (input2 @ lvs) outputs e in
        Let
          ([], input2_binding @ lbs, dde, lwiden input1 inputs (LTupleIntro lvs))
    (* TDup *)
    | Dup l ->
        assert (List.length inputs = 1);
        assert (List.length outputs = 2);
        LAdd (List.nth outputs 0, List.nth outputs 1)
    (* TDropLin *)
    | Drop l ->
        assert (List.length inputs = 1);
        assert (List.length outputs = 0);
        let t = llookup lenv (List.hd inputs) in
        with_lvar (LZero t) (fun k -> Ret ([], [ k ]))
    (* TLinMul *)
    | LMul (uv, lv) ->
        assert (List.length inputs = 1);
        assert (List.length outputs = 1);
        LMul (uv, List.hd outputs)
    (* TLinTup *)
    | LTupleIntro lvs ->
        assert (List.length outputs = 1);
        (* types of dot_dot_v *)
        let lbs = map (fun l -> (l, llookup lenv l)) lvs in
        (* It has to be a tuple *)
        let e = lwiden lvs inputs (Ret ([], List.map fst lbs)) in
        LTupleElim (lbs, List.hd outputs, e)
    (* TApp *)
    | FunCall (n, uvs, lvs) ->
        assert (ufrag (codomain (flookup fenv n)) = []);
        lwiden lvs inputs
          (FunCall (NamingConventions.transpose n, uvs, outputs))
    (* TLinAdd *)
    | LAdd (lv1, lv2) ->
        assert (List.length inputs = 2);
        assert (List.length outputs = 1);
        Dup (List.hd outputs)
    (* TLinZero *)
    | LZero t ->
        assert (inputs = []);
        assert (List.length outputs = 1);
        Drop (List.hd outputs)
    (* TNonLin *)
    | _ ->
        assert (List.length inputs = 0);
        assert (0 = 1);
        assert (List.length outputs = 0);
        e
  in

  (*print_endline "\n outputs:";

    List.iter (fun a -> Printf.printf "%s " (pop_lv a)) outputs;
    print_endline "\nflv t : ";
    LVarSet.iter (fun a -> Printf.printf "%s " (pop_lv a)) (flv t);
    print_endline "";*)

  (* The free linear variables of [t] must match the list [outputs]. *)
  assert (equal (flv t) (of_list outputs));
  t

(* -------------------------------------------------------------------------- *)

(* Declarations. *)

(* We transpose a function [f] only if its name appears in the list [fs].
   Every function in this list must have zero unrestricted outputs. *)

(* The transposed function [tf] has the same unrestricted arguments and
   unrestricted results as the function [f]. (It has no unrestricted
   results.) Its linear arguments and linear results are those of [f],
   exchanged: linear arguments become linear results, and vice-versa.
   The order of arguments and results is preserved. *)

let transform_decl (fs : NameSet.t) fenv decl =
  clear ();
  let must_transpose = NameSet.mem (name decl) fs in
  if not must_transpose then [ decl ]
  else
    let (Decl (range, f, ubs, lbs, e)) = decl in
    (*print_endline ("--- tanspose " ^ f ^ "---");*)
    (* Look up the type of [f], and determine the number and types of
       its unrestricted and linear outputs. *)
    let utys, ltys = codomain (flookup fenv f) in
    (* [f] must have no unrestricted outputs. *)
    assert (utys = []);
    let tf = NamingConventions.transpose f in
    (* The linear inputs of [f] already have names. *)
    let inputs = map fst lbs and lenv = lbind_many Env.empty lbs in
    (* Invent fresh names for the linear outputs of [f]. *)
    let lbs = map lfreshb ltys in
    let outputs = map fst lbs in
    (* Keep the definition of [f] and emit the definition of [tf]. *)
    [
      decl; Decl (range, tf, ubs, lbs, transform_expr fenv lenv inputs outputs e);
    ]

let transform fs prog =
  fresh_names_in_namespace "t";
  let fs = NameSet.of_list fs in
  let fenv = LinearTypeChecker.environment prog in
  let decls = prog in
  List.flatten (map (transform_decl fs fenv) decls)