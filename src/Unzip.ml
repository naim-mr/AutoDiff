(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-27-32-33-39"]

open Linear
open LinearHelp
open LinearHelp.Constructors
open LinearHelp.Contexts
open LinearTypeChecker

(* -------------------------------------------------------------------------- *)

(* Naming conventions. *)

(* Each function [f] in the original program is transformed into two
   functions, [uf] and [lf]. *)

(* The function [uf] takes just the unrestricted parameters of [f] and
   returns its unrestricted results plus a number of unrestricted
   auxiliary results. *)

(* The function [lf] takes the auxiliary results of [uf] plus the
   linear parameters of [f] and returns the linear results of [f]. *)

open NamingConventions

(* -------------------------------------------------------------------------- *)

(* Types. *)

(* The type of [uf] depends not only on the type of [f], but also on the
   body of the function [f]. *)

(* Because we do not have recursive functions, when we unzip a call of a
   function [f], we have already unzipped the definition of [f]. This allows
      us to look up (in a suitable environment) the type of the translated
      function [uf]. (This is noted at the end of Section 4 in the paper.) *)

(* An environment [env] is a pair [ifenv, ofenv]. *)

(* [ifenv] maps every function [f] in the original program to its type. *)

(* [ofenv] maps every function [uf] in the unzipped program to its type. *)

type env = fenv * fenv

(* -------------------------------------------------------------------------- *)

(* Expressions. *)

(* The environment [env] records the type of every source function [f] and of
   every transformed function [uf]. It does not evolve when [transform_expr]
   recursively calls itself. *)
let x = ref 0

let rec n_first l n =
  if n = 0 then l
  else
    match (l, n) with
    | [], _ -> []
    | x :: q, 0 -> x :: q
    | x :: q, n -> n_first q (n - 1)

let rec n_last l n =
  match (l, n) with
  | l, 0 -> []
  | [], n -> []
  | x :: q, n -> x :: n_last q (n - 1)

let rec transform_expr (env : env) (e : expr) : uctx * expr * expr =
  match e with
  | Loc (e, range) -> (empty, e, e)
  (* URet *)
  | Ret (us, ls) -> (empty, Ret (us, []), Ret ([], ls))
  (* ULet *)
  | Let (ubs, lbs, e1, e2) ->
      let c1, e1', de1' = transform_expr env e1 in
      let c2, e2', de2' = transform_expr env e2 in
      (c1 ++ ulet ubs e1' ++ c2, e2', Let ([], lbs, de1', de2'))
  (* Next are ULeaf *)
  | ULiteral _ | UUnOp _ | UBinOp _ | UTupleIntro _ -> (empty, e, Ret ([], []))
  (* Next are ULinLeaf *)
  | Dup _ | Drop _ | LTupleIntro _ | LZero _ | LAdd _ | LMul _ ->
      (empty, Ret ([], []), e)
  | LTupleElim (lbs, lvs, e) ->
      let ce, e', de' = transform_expr env e in
      (ce, e', LTupleElim (lbs, lvs, de'))
  | UTupleElim (ubs, uvs, e) ->
      let ce, e', de' = transform_expr env e in
      (utuple_elim ubs uvs ++ ce, e', de')
  | FunCall (n, uvs, lvs) ->
      (* get f.nonlin name  *)
      let unf = unrestricted n in
      (* util functions  *)
      let rec get_last l =
        match l with [ x ] -> Some x | x :: q -> get_last q | [] -> None
      in
      let rec remove_last l =
        match l with x :: [] -> [] | x :: q -> x :: remove_last q | [] -> []
      in
      (* Get the types of f.nonlin that is (taus,sigma) where taus is a vecteur and sigma is TUple.
         This is always true because of the extensions of the env in the transform_decl function*)
      let tfy =
        try ufrag (codomain (flookup (snd env) unf))
        with Not_found ->
          failwith ("In transform_expr- FUNcall : " ^ unf ^ " Need to be typed")
      in
      (* Search the type sigma= Tuples (tys ) in tfy and create a vector of variable w  matching the the type inside the tuple *)
      let w =
        match get_last tfy with
        | None -> []
        | Some t -> (
            match t with
            | TTuple ts ->
                List.init (List.length ts) (fun i -> ufreshb (List.nth ts i))
            | t -> failwith "Should not happen")
      in
      (* Now I create a vector of var matching taus  *)
      let ubs =
        List.init
          (List.length (remove_last tfy))
          (fun i -> ufreshb (List.nth tfy i))
      in
      (* Then I return as in the rule *)
      ( ulet (ubs @ w) (FunCall (unf, uvs, [])),
        Ret (List.map fst ubs, []),
        FunCall (linear n, List.map fst w, lvs) )

(* -------------------------------------------------------------------------- *)

(* Declarations. *)

(* While declarations are processed, [ifenv] is fixed, and [ofenv] grows. *)

(* A function [f] is unzipped only if its name occurs in [fs].  *)

let transform_decl (fs : NameSet.t) (ifenv : fenv) (ofenv : fenv) (decl : decl)
    : fenv * decls =
  clear ();
  let must_unzip = NameSet.mem (name decl) fs in
  if not must_unzip then (ofenv, [ decl ])
  else
    let (Decl (range, f, ubs, lbs, e)) = decl in

    let uf, lf, cf = (unrestricted f, linear f, combined f) in

    (* Construct the definitions of the functions [uf], [lf], [cf]. *)
    let ce, e', de' = transform_expr (ifenv, ofenv) e in
    let w =
      List.filter (fun u -> UVarSet.mem (fst u) (fuv de')) (ubs @ bindings ce)
    in
    let wvars : uvars = List.map (fun e -> fst e) w in
    let wtypes : tys = List.map (fun e -> snd e) w in
    let sigma = ufrag (codomain (flookup ifenv f)) in
    (*let dsigma = lfrag (codomain (flookup ifenv f)) in *)
    let uret = List.init (List.length sigma) (fun i -> ufreshb TUnknown) in
    let uret =
      uret
      @ List.init (List.length wvars) (fun i -> ufreshb (List.nth wtypes i))
    in

    let expr =
      Let
        ( uret,
          [],
          FunCall (uf, List.map fst ubs, []),
          FunCall
            ( lf,
              List.map fst (n_first uret (List.length sigma)),
              List.map fst lbs ) )
    in
    let udef, ldef, cdef =
      ( Decl (range, uf, ubs, [], Contexts.fill ce (uwiden e' wvars)),
        Decl (range, lf, w, lbs, de'),
        Decl (range, cf, ubs, lbs, expr) )
    in
    (* Extend [ofenv] with the type of [uf]. *)
    let ufty = ((List.map snd ubs, []), (sigma @ [ TTuple wtypes ], [])) in
    let ofenv = fbind ofenv uf ufty in
    (* Done. *)
    (ofenv, [ udef; ldef; cdef ])

(* -------------------------------------------------------------------------- *)

(* Programs. *)

let transform (fs : names) (prog : prog) : prog =
  fresh_names_in_namespace "u";
  let fs = NameSet.of_list fs in
  let decls = prog in
  let ifenv = LinearTypeChecker.environment decls in
  let ofenv = Env.empty in
  let _ofenv, decls =
    List.fold_left_map (transform_decl fs ifenv) ofenv decls
  in
  List.flatten decls
