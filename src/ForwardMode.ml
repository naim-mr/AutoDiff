(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-27-32-33-39"]

open Linear
open LinearHelp
open LinearHelp.Constructors

(* We assume that the source program does not use any linear variables. *)

(* We assume that every multi-result in the source program has arity 1. *)

(* The paper assumes that every variable is used at least once. This applies
   even to nonlinear variables: see the first paragraph of Section 2.2.
   Because of this assumption, the transformation J (Figure 8) does not
   need to introduce any drops. We do not impose this restriction, so we
   can produce code where some [drop] instructions are missing. *)

(* If the source expression uses an unrestricted variable [x : tau] then
   the transformed expression uses both an unrestricted variable [x : tau]
   and a linear variable [dx : tau]. If the source expression produces an
   unrestricted result of type [tau] then (in the same position) the
   transformed expression produces both an unrestricted result of type
   [tau] and a linear result of type [tau]. *)

(* For simplicity, the mapping of the name [x] to the name [dx] is fixed.
   Collisions are avoided by assuming that the name [x] never begins with
   the character [d]. *)

(* -------------------------------------------------------------------------- *)

(* Naming conventions. *)

open NamingConventions

let dot (U x : uvar) : lvar =
  assert (String.length x > 0 && x.[0] <> 'd');
  L ("d" ^ x)

let dots (xs : uvars) : lvars = map dot xs
let transform_var (x : uvar) : expr = lvar (dot x)

let transform_binding ((x, ty) : ubinding) : lbinding =
  let dx = dot x in
  (dx, ty)

let transform_bindings (ubs : ubindings) : lbindings = map transform_binding ubs

(* -------------------------------------------------------------------------- *)

(* Expressions. *)

let rec transform_expr (e : expr) : expr =
  match e with
  | Loc (e, range) -> e
  (* JRet *)
  | Ret (us, ls) ->
      assert (length ls = 0);
      assert (UVarSet.pairwise_distinct us);
      Ret (us, dots us)
  (* JLet *)
  | Let (ubs, lbs, e1, e2) ->
      assert (length lbs = 0);
      let e1' = transform_expr e1 in
      let e2' = transform_expr e2 in
      Let (ubs, transform_bindings ubs, e1', e2')
  (* JLit *)
  | ULiteral r -> pair (ULiteral r) (LZero TReal)
  (* JPrimSin *)
  | UUnOp (OpSin, uv) ->
      let dsin = with_uvar (UUnOp (OpCos, uv)) (fun k -> LMul (k, dot uv)) in
      pair e dsin
  (* JPrimCos *)
  | UUnOp (OpCos, uv) ->
      let dcos =
        with_uvar (uminus (UUnOp (OpSin, uv))) (fun k -> LMul (k, dot uv))
      in
      pair e dcos
  (* JPrimExp *)
  | UUnOp (OpExp, uv) ->
      let dexp = with_uvar e (fun k -> LMul (k, dot uv)) in
      pair e dexp
  (* JPrimAdd *)
  | UBinOp (uv1, OpAdd, uv2) -> pair e (LAdd (dot uv1, dot uv2))
  (* JPrimSub *)
  | UBinOp (uv1, OpSub, uv2) ->
      let dsub =
        with_lvar
          (with_uvar minus_one (fun k -> LMul (k, dot uv2)))
          (fun k -> LAdd (dot uv1, k))
      in
      pair e dsub
  (* JPrimMul *)
  | UBinOp (uv1, OpMul, uv2) ->
      (*assert (uv1 <> uv2);*)
      let dmul = LMul (uv1, dot uv2) +. LMul (uv2, dot uv1) in
      pair e dmul
  (* JPrimDiv *)
  | UBinOp (uv1, OpDiv, uv2) ->
      let ddiv =
        with_uvar
          (with_uvar
             (UBinOp (uv2, OpMul, uv2))
             (fun m2 -> with_uvar minus_one (fun k -> UBinOp (k, OpDiv, m2))))
          (fun den ->
            with_lvar
              (with_lvar
                 (LMul (uv1, dot uv2))
                 (fun k2 ->
                   with_lvar
                     (lminus (LMul (uv2, dot uv1)))
                     (fun k1 -> LAdd (k1, k2))))
              (fun num -> LMul (den, num)))
      in
      pair e ddiv
  (* JTup *)
  | UTupleIntro uvs ->
      (*
        assert(UVarSet.pairwise_distinct uvs);
        Canno't put it. It's ask by the rules (cf:paper) but the generator generate program without distinct
        uvs
      *)
      pair e (LTupleIntro (dots uvs))
  (* JUnpackA *)
  | UTupleElim (ubs, uvs, e1) ->
      assert (UVarSet.disjoint (UVarSet.of_list [ uvs ]) (fuv e) = false);
      UTupleElim
        ( ubs,
          uvs,
          LTupleElim (transform_bindings ubs, dot uvs, transform_expr e1) )
  (* JApp*)
  | FunCall (n, uvs, lvs) ->
      (*
        assert(UVarSet.pairwise_distinct uvs);
        Canno't put it. It's ask by the rules (cf:paper) but the generator generate program without distinct
        uvs
      *)
      FunCall (derivative n, uvs, dots uvs)
  (* JDrop *)
  | Drop e -> Drop e
  (* Shouldn't be linear *)
  | _ -> assert false

(* -------------------------------------------------------------------------- *)

(* Declarations. *)

let transform_decl (decl : decl) : decl =
  clear ();
  match decl with
  | Decl (range, f, ubs, lbs, e) ->
      assert (lbs = []);
      let df = derivative f and lbs = transform_bindings ubs in
      Decl (range, df, ubs, lbs, transform_expr e)

let transform prog =
  fresh_names_in_namespace "l";
  List.fold_right
    (fun decl decls -> decl :: transform_decl decl :: decls)
    prog []
