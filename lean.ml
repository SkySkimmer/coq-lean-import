(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Univ
module RelDecl = Context.Rel.Declaration

let __ () = assert false

let invalid = Constr.(mkApp (mkSet, [| mkSet |]))

let quickdef ~name entry impls =
  let scope = DeclareDef.Global Declare.ImportDefaultBehavior in
  let kind = Decls.(IsDefinition Definition) in
  DeclareDef.declare_definition ~scope ~name ~kind UnivNames.empty_binders entry
    impls

(** produce [args, recargs] inside mixed context [args/recargs]
    [info] is in reverse order, ie the head is about the last arg in application order

    examples:
    [] -> [],[]
    [false] -> [1],[]
    [true] -> [2],[1]
    [true;false] -> [3;2],[1]
    [false;true] -> [3;1],[2]
    [false;false] -> [2;1],[]
    [true;true] -> [4;2],[3;1]

*)
let reorder_inside_core info =
  let rec aux i args recargs = function
    | [] -> (args, recargs)
    | false :: info -> aux (i + 1) (i :: args) recargs info
    | true :: info -> aux (i + 2) ((i + 1) :: args) (i :: recargs) info
  in
  aux 1 [] [] info

let reorder_inside info =
  let args, recargs = reorder_inside_core info in
  CArray.map_of_list Constr.mkRel (List.append args recargs)

let rec insert_after k ((n, t) as v) c =
  if k = 0 then Constr.mkProd (n, t, Vars.lift 1 c)
  else
    match Constr.kind c with
    | Prod (na, a, b) -> Constr.mkProd (na, a, insert_after (k - 1) v b)
    | _ -> assert false

let insert_after k (n, t) c =
  insert_after k (n, Vars.lift k t) (Vars.subst1 invalid c)

let rec reorder_outside info hyps c =
  match (info, hyps) with
  | [], [] -> (c, 0)
  | false :: info, (n, t) :: hyps ->
    let c, k = reorder_outside info hyps c in
    (Constr.mkProd (n, t, c), k + 1)
  | true :: info, (n, t) :: rhyp :: hyps ->
    let c, k = reorder_outside info hyps c in
    let c = insert_after k rhyp c in
    (Constr.mkProd (n, t, c), k + 1)
  | _ -> assert false

(** produce [forall args recargs, P (C args)] from mixed [forall args/recargs, P (C args)] *)
let reorder_outside info ft =
  let hyps, out = Term.decompose_prod ft in
  fst (reorder_outside (List.rev info) (List.rev hyps) out)

(** Build the body of a Lean-style scheme. [u] instantiates the
    inductive, [s] is [None] for the SProp scheme and [Some l]
    for a scheme with motive [l].

    Lean schemes differ from Coq schemes:
    - the motive universe is the first bound universe for Lean
      but the last for Coq (handled by caller)
    - Lean puts induction hypotheses after all the constructor arguments,
      Coq puts them immediately after the corresponding recursive argument.
 *)
let lean_scheme env ~dep mind u s =
  let mib = Global.lookup_mind mind in
  let nparams = mib.mind_nparams in
  assert (Array.length mib.mind_packets = 1);
  (* if we start using non recursive params in the translation it will
     involve reordering arguments *)
  assert (nparams = mib.mind_nparams_rec);
  let mip = mib.mind_packets.(0) in

  let body =
    let sigma = Evd.from_env env in
    let sigma, body =
      Indrec.build_induction_scheme env sigma
        ((mind, 0), u)
        dep
        (if Level.is_sprop s then InSProp else InType)
    in
    let uctx = Evd.universe_context_set sigma in
    if Level.is_sprop s then begin
      assert (ContextSet.is_empty uctx);
      body
    end
    else begin
      assert (LSet.cardinal (fst uctx) = 1 && Constraint.is_empty (snd uctx));
      let v = LSet.choose (fst uctx) in
      Vars.subst_univs_level_constr (LMap.singleton v s) body
    end
  in

  assert (
    CArray.for_all2 Int.equal mip.mind_consnrealargs mip.mind_consnrealdecls);
  let recinfo =
    Array.mapi
      (fun i (args, _) ->
        let nargs = mip.mind_consnrealargs.(i) in
        (* skip params *)
        let args = CList.firstn nargs args in
        CList.map_i
          (fun j arg ->
            let t = RelDecl.get_type arg in
            not (Vars.noccurn (nargs + nparams - j) t))
          0 args)
      mip.mind_nf_lc
  in
  let hasrec =
    (* NB: if the only recursive arg is the last arg, no need for reordering *)
    Array.exists
      (function [] -> false | _ :: info -> List.exists (fun x -> x) info)
      recinfo
  in

  if not hasrec then body
  else
    (* body := fun params P (fc : forall args/recargs, P (C args)) => ...

     becomes

     fun params P (fc : forall args, forall recargs, P (C args)) =>
     body params P (fun args/recargs, fc args recargs)
    *)
    let open Constr in
    let nlc = Array.length recinfo in
    let paramsP, inside = Term.decompose_lam_n_assum (nparams + 1) body in
    let fcs, inside = Term.decompose_lam_n nlc inside in
    let fcs = List.rev fcs in

    let body =
      mkApp
        (body, Array.init (nparams + 1) (fun i -> mkRel (nlc + nparams + 1 - i)))
    in
    let body =
      mkApp
        ( body,
          Array.of_list
            (CList.map_i
               (fun i (_, ft) ->
                 let info = recinfo.(i) in
                 if not (List.exists (fun x -> x) info) then mkRel (nlc - i)
                 else
                   let hyps, _ = Term.decompose_prod ft in
                   let args = reorder_inside info in
                   Term.it_mkLambda_or_LetIn
                     (mkApp (mkRel (nlc - i + List.length hyps), args))
                     (List.map (fun (n, t) -> RelDecl.LocalAssum (n, t)) hyps))
               0 fcs) )
    in

    let fcs =
      CList.map_i
        (fun i (n, ft) ->
          let info = recinfo.(i) in
          let ft = reorder_outside info ft in
          RelDecl.LocalAssum (n, ft))
        0 fcs
    in
    let fcs = List.rev fcs in
    let body =
      let env = Environ.push_rel_context paramsP env in
      let env = Environ.push_rel_context fcs env in
      Reduction.nf_betaiota env body
    in
    Term.it_mkLambda_or_LetIn (Term.it_mkLambda_or_LetIn body fcs) paramsP

let with_unsafe_univs f () =
  let flags = Global.typing_flags () in
  Global.set_typing_flags { flags with check_universes = false };
  try
    let v = f () in
    Global.set_typing_flags flags;
    v
  with e ->
    let e = CErrors.push e in
    Global.set_typing_flags flags;
    Exninfo.iraise e

module RRange : sig
  type +'a t
  (** Like Range.t, but instead of cons we append *)

  val empty : 'a t

  val length : 'a t -> int

  val append : 'a t -> 'a -> 'a t

  val get : 'a t -> int -> 'a

  val singleton : 'a -> 'a t
end = struct
  type 'a t = { data : 'a Range.t; len : int }

  let empty = { data = Range.empty; len = 0 }

  let length x = x.len

  let append { data; len } x = { data = Range.cons x data; len = len + 1 }

  let get { data; len } i =
    if i >= len then raise Not_found else Range.get data (len - i - 1)

  let singleton x = { data = Range.cons x Range.empty; len = 1 }
end

module LeanName : sig
  type t = private string

  val anon : t

  val append : t -> string -> t

  val equal : t -> t -> bool

  val raw_append : t -> string -> t
  (** for private names *)

  val to_string : t -> string

  val to_id : t -> Id.t

  val to_name : t -> Name.t

  val pp : t -> Pp.t

  module Set : CSet.S with type elt = t

  module Map : CMap.ExtS with type key = t and module Set := Set
end = struct
  type t = string
  (** "foo.bar.baz" is [baz;bar;foo] (like with dirpaths) *)

  let anon : t = ""

  let append a b = if a = "" then b else a ^ "_" ^ b

  let raw_append a b = a ^ b

  let to_id (x : t) = Id.of_string x

  let to_name x = if x = "" then Anonymous else Name (to_id x)

  let to_string x = x

  let pp = Pp.str

  let equal = String.equal

  module Set = CString.Set
  module Map = CString.Map
end

module N = LeanName

module U = struct
  type t = Prop | Succ of t | Max of t * t | IMax of t * t | UNamed of N.t

  let compare : t -> t -> int = compare

  module Self = struct
    type nonrec t = t

    let compare = compare
  end

  module Map = CMap.Make (Self)
end

(** [map] goes from lean names to universes (in practice either SProp or a named level) *)
let rec to_universe map = function
  | U.Prop -> Universe.sprop
  | UNamed n -> Universe.make (N.Map.get n map)
  | Succ u -> Universe.super (to_universe map u)
  | Max (a, b) -> Universe.sup (to_universe map a) (to_universe map b)
  | IMax (a, b) ->
    let ub = to_universe map b in
    if Universe.is_sprop ub then ub else Universe.sup (to_universe map a) ub

let rec do_n f x n = if n = 0 then x else do_n f (f x) (n - 1)

(** in lean, max(Prop+1,l)+1 <= max(Prop+1,l+1)
   because:
   - either l=Prop, so Prop+1 <= Prop+1
   - or Prop+1 <= l so l+1 <= l+1

   to simulate this, each named level becomes > Set and we compute maxes accordingly
*)

let simplify_universe u =
  match Universe.repr u with
  | (l, n) :: (_ :: _ as rest) when Level.is_set l ->
    if List.exists (fun (_, n') -> n <= n' + 1) rest then
      List.fold_left
        (fun u (l, n) ->
          Universe.sup u (do_n Universe.super (Universe.make l) n))
        Universe.sprop rest
    else u
  | _ -> u

let to_universe map u =
  let u = to_universe map u in
  simplify_universe u

type uconv = {
  map : Level.t N.Map.t;  (** Map from lean names to Coq universes *)
  levels : Level.t Universe.Map.t;
      (** Map from algebraic universes to levels (only levels representing
          an algebraic) *)
  graph : UGraph.t;
}

let lean_id = Id.of_string "Lean"

let lean_fancy_univs =
  Goptions.declare_bool_option_and_ref ~depr:false
    ~key:[ "Lean"; "Fancy"; "Universes" ]
    ~value:true

let level_of_universe u =
  let u = Universe.repr u in
  let u =
    List.map
      (fun (l, n) ->
        let open Level in
        if is_sprop l then (
          assert (n = 0);
          "SProp")
        else if is_set l then "Set+" ^ string_of_int n
        else
          match name l with
          | None -> assert false
          | Some name ->
            let d, i = UGlobal.repr name in
            let d = DirPath.repr d in
            (match (d, i) with
            | [ name; l ], 0 when Id.equal l lean_id ->
              Id.to_string name ^ if n = 0 then "" else "+" ^ string_of_int n
            | _ -> to_string l))
      u
  in
  let s = (match u with [ _ ] -> "" | _ -> "max__") ^ String.concat "_" u in
  Level.(make (UGlobal.make (DirPath.make [ Id.of_string_soft s; lean_id ]) 0))

let level_of_universe u =
  if lean_fancy_univs () then level_of_universe u else UnivGen.fresh_level ()

let update_graph (l, u) (l', u') graph =
  if UGraph.check_leq graph (Universe.super u) u' then
    UGraph.enforce_constraint (l, Lt, l') graph
  else if UGraph.check_leq graph (Universe.super u') u then
    UGraph.enforce_constraint (l', Lt, l) graph
  else if UGraph.check_leq graph u u' then
    UGraph.enforce_constraint (l, Le, l') graph
  else if UGraph.check_leq graph u' u then
    UGraph.enforce_constraint (l', Le, l) graph
  else graph

let to_univ_level u uconv =
  match Universe.level u with
  | Some l -> (uconv, l)
  | None ->
    (match Universe.Map.find_opt u uconv.levels with
    | Some l -> (uconv, l)
    | None ->
      let l = level_of_universe u in
      let graph =
        UGraph.add_universe l ~lbound:Level.set ~strict:true uconv.graph
      in
      let graph =
        Universe.Map.fold
          (fun u' l' graph -> update_graph (l, u) (l', u') graph)
          uconv.levels graph
      in
      let graph =
        N.Map.fold
          (fun _ l' graph ->
            if Level.is_sprop l' then graph
            else update_graph (l, u) (l', Universe.make l') graph)
          uconv.map graph
      in
      let uconv =
        { uconv with levels = Universe.Map.add u l uconv.levels; graph }
      in
      (uconv, l))

type binder_kind =
  | NotImplicit
  | Maximal
  | NonMaximal
  | Typeclass  (** WRT Coq, Typeclass is like Maximal. *)

type expr =
  | Bound of int
  | Sort of U.t
  | Const of N.t * U.t list
  | App of expr * expr
  | Let of { name : N.t; ty : expr; v : expr; rest : expr }
      (** Let: undocumented in export_format.md *)
  | Lam of binder_kind * N.t * expr * expr
  | Pi of binder_kind * N.t * expr * expr

type def = { ty : expr; body : expr; univs : N.t list }

type ax = { ty : expr; univs : N.t list }

type ind = {
  params : (binder_kind * N.t * expr) list;
  ty : expr;
  ctors : (N.t * expr) list;
  univs : N.t list;
}

type entry = Def of def | Ax of ax | Ind of ind | Quot

type notation_kind = Prefix | Infix | Postfix

type notation = {
  kind : notation_kind;
  head : N.t;
  level : int;
  token : string;
}

type instantiation = {
  ref : GlobRef.t;
  algs : Universe.t list;
      (** For each extra universe, produce the algebraic it corresponds to
          (the initial universes are replaced by the appropriate Var) *)
}

(*
Lean classifies inductives in the following way:
- inductive landing in always >Prop (even when instantiated to all Prop) -> never squashed
- inductive which has Prop instantiation:
  + no constructor -> never squashed
  + multi constructor -> always squashed
  + 1 constructor
    * no non param arguments
      -> not squashed, special reduction
      typically [eq]
    * all arguments appear in the output type
      -> not squashed, basic reduction
      no real world examples? eg [Inductive foo : nat -> Prop := bar : forall x, foo x.]
      2019 "type theory of lean" implies that there should be special reduction
      but testing says otherwise
    * some arguments don't appear in the output type, but are Prop or recursive
      -> not squashed, basic reduction
      typically [Acc], [and]
    * some non-Prop non-recursive arguments (for some instantiation) don't appear in the output type
      -> squashed
      typically [exists]

Additionally, the recursor is nondependent when the type is always Prop,
otherwise dependent (including for sometimes-Prop types)
(this implem detail isn't in the TTofLean paper)
Special reduction also seems restricted to always-Prop types.

NB: in practice (all stdlib and mathlib) the target universe is available without reduction
(ie syntactic arity) even though the system doesn't require it.
so we can just look at it directly (we don't want to implement a reduction system)

Difference with Coq:
- a non-Prop instantiation of possibly Prop types will never be squashed
- non squashed possibly-Prop types at a Prop instantiation are squashed
  (unless empty or uip branch)
- we need uip branch for the special reduction.
  TTofLean sounds like we need an encoding with primitive records
  but testing indicates otherwise (all args in output type case).
- we will always need unsafe flags for [Acc], and possibly for [and].

Instantiating the type with all-Prop may side-effect instantiate
some other globals with Prop that won't actually be used
(assuming the inductive is not used with all-Prop)
This probably doesn't matter much, also if we start using upfront
instantiations it won't matter at all.
*)

type squashy = {
  maybe_prop : bool;  (** used for optim, not fundamental *)
  always_prop : bool;
      (** controls whether the lean eliminator is dependent (and
              special reduction, but we just let Coq do its thing for that). *)
  lean_squashes : bool;
      (** Self descriptive. We handle necessity of unsafe flags per-instantiation. *)
}

let noprop = { maybe_prop = false; always_prop = false; lean_squashes = false }

let pp_squashy { maybe_prop; always_prop; lean_squashes } =
  let open Pp in
  (if maybe_prop then
   if always_prop then str "is always Prop" else str "may be Prop"
  else str "is never Prop")
  ++ spc ()
  ++
  if lean_squashes then str "and is squashed by Lean"
  else str "and is not squashed by Lean"

let coq_squashes graph (entry : Entries.mutual_inductive_entry) =
  let env = Global.env () in
  let env = Environ.set_universes env graph in
  let ind =
    match entry.mind_entry_inds with [ ind ] -> ind | _ -> assert false
  in
  let params = entry.mind_entry_params in
  let ty = ind.mind_entry_arity in
  let env_params = Environ.push_rel_context params env in
  let _, s = Reduction.dest_arity env_params ty in
  (* TODO merge with uip branch *)
  if not (Sorts.is_sprop s) then false
  else
    match ind.mind_entry_lc with
    | [] -> false
    | _ :: _ :: _ -> true
    | [ c ] -> (match Constr.kind c with Rel _ | App _ -> false | _ -> true)

type 'uconv state = {
  names : N.t RRange.t;
  exprs : expr RRange.t;
  univs : U.t RRange.t;
  uconv : 'uconv;
  skips : int;
  entries : entry N.Map.t;
  squash_info : squashy N.Map.t;
  declared : instantiation Int.Map.t N.Map.t;
      (** For each name, the instantiation with all non-sprop univs should
     always be declared, but the instantiations with SProp are lazily
     declared. We expect small instance lengths (experimentally at
     most 4 in the stdlib) so we represent instantiations as bit
     fields, bit n is 1 iff universe n is instantiated by SProp. *)
  notations : notation list;
}
(** 'uconv is unit when not converting an entry *)

(** the kernel will deal with the relevance annot *)
let to_annot n = Context.annotR (N.to_name n)

(* bit n of [int_of_univs univs] is 1 iff [List.nth univs n] is SProp *)
let int_of_univs =
  let rec aux i acc = function
    | [] -> (i, acc)
    | u :: rest ->
      let sprop = Universe.is_sprop u in
      aux
        ((i * 2) + if sprop then 1 else 0)
        (if sprop then acc else u :: acc)
        rest
  in
  fun l -> aux 0 [] (List.rev l)

let univ_of_name u =
  if lean_fancy_univs () then
    let u = DirPath.make [ N.to_id u; lean_id ] in
    Level.(make (UGlobal.make u 0))
  else UnivGen.fresh_level ()

let start_uconv (state : unit state) univs i =
  let rec aux map graph i = function
    | [] ->
      assert (i = 0);
      (map, graph)
    | u :: univs ->
      let map, graph =
        if i mod 2 = 0 then
          let v = univ_of_name u in
          ( N.Map.add u v map,
            UGraph.add_universe v ~lbound:Level.set ~strict:true graph )
        else (N.Map.add u Level.sprop map, graph)
      in
      aux map graph (i / 2) univs
  in
  let map, graph = aux N.Map.empty UGraph.initial_universes i univs in
  { state with uconv = { map; levels = Universe.Map.empty; graph } }

let rec make_unames univs ounivs =
  match (univs, ounivs) with
  | _, [] ->
    List.map (fun u -> Name (Id.of_string_soft (Level.to_string u))) univs
  | _u :: univs, o :: ounivs -> N.to_name o :: make_unames univs ounivs
  | [], _ :: _ -> assert false

let univ_entry { map; levels; graph } ounivs =
  let ounivs =
    CList.map_filter
      (fun u ->
        let v = N.Map.get u map in
        if Level.is_sprop v then None else Some (u, v))
      ounivs
  in
  let ounivs, univs = List.split ounivs in
  let univs, algs =
    if Universe.Map.is_empty levels then (univs, [])
    else
      let univs = List.rev univs in
      (* add the new levels to univs, add constraints between maxes
         (eg max(a,b) <= max(a,b,c)) *)
      let univs, algs =
        Universe.Map.fold
          (fun alg l (univs, algs) -> (l :: univs, alg :: algs))
          levels (univs, [])
      in
      let univs = List.rev univs in
      (univs, algs)
  in
  let kept = LSet.singleton Level.set in
  let kept = List.fold_left (fun kept l -> LSet.add l kept) kept univs in
  let csts = UGraph.constraints_for ~kept graph in
  let unames = Array.of_list (make_unames univs ounivs) in
  let univs = Instance.of_array (Array.of_list univs) in
  let uctx = UContext.make (univs, csts) in
  let subst = make_instance_subst univs in
  let algs = List.rev_map (subst_univs_level_universe subst) algs in
  (Entries.Polymorphic_entry (unames, uctx), algs)

(* TODO restrict univs (eg [has_add : Sort (u+1) -> Sort(u+1)] can
   drop the [u] and keep only the replacement for [u+1]??

   Preserve algebraics in codomain position? *)
let finish_uconv state ounivs =
  let univs = univ_entry state.uconv ounivs in
  ({ state with uconv = () }, univs)

let name_for_core n i =
  if i = 0 then N.to_id n
  else Id.of_string (N.to_string n ^ "_inst" ^ string_of_int i)

(* NB collisions for constructors/recursors are still possible but
   should be rare *)
let name_for n i =
  let base = name_for_core n i in
  if not (Global.exists_objlabel (Label.of_id base)) then base
  else
    (* prevent resetting the number *)
    let base = if i = 0 then base else Id.of_string (Id.to_string base ^ "_") in
    Namegen.next_global_ident_away base Id.Set.empty

let get_predeclared_eq n i =
  if String.equal (N.to_string n) "eq" then
    let ind_name = name_for_core n i in
    match Nametab.locate (Libnames.qualid_of_ident ind_name) with
    | IndRef (ind, 0) as ref ->
      if Global.is_polymorphic ref then Some (ind_name, ind) else None
    | _ -> None
    | exception Not_found -> None
  else None

let add_declared declared n i inst =
  N.Map.update n
    (function
      | None -> Some (Int.Map.singleton i inst)
      | Some m -> Some (Int.Map.add i inst m))
    declared

let to_univ_level' u state =
  let u = to_universe state.uconv.map u in
  let uconv, u = to_univ_level u state.uconv in
  ({ state with uconv }, u)

let std_prec_max = N.raw_append N.anon "std_prec_max"

let rec to_constr =
  let open Constr in
  let ( >>= ) x f state =
    let state, x = x state in
    f x state
  in
  let ret x state = (state, x) in
  function
  | Bound i -> ret (mkRel (i + 1))
  | Sort univ ->
    to_univ_level' univ >>= fun u ->
    ret (mkSort (Sorts.sort_of_univ (Universe.make u)))
  | Const (n, univs) -> instantiate n univs
  | App (a, b) ->
    to_constr a >>= fun a ->
    to_constr b >>= fun b -> ret (mkApp (a, [| b |]))
  | Let { name; ty; v; rest } ->
    to_constr ty >>= fun ty ->
    to_constr v >>= fun v ->
    to_constr rest >>= fun rest -> ret (mkLetIn (to_annot name, v, ty, rest))
  | Lam (_bk, n, a, b) ->
    to_constr a >>= fun a ->
    to_constr b >>= fun b -> ret (mkLambda (to_annot n, a, b))
  | Pi (_bk, n, a, b) ->
    to_constr a >>= fun a ->
    to_constr b >>= fun b -> ret (mkProd (to_annot n, a, b))

and instantiate n univs state =
  assert (List.length univs < Sys.int_size);
  (* TODO what happens when is_large_elim and the motive is instantiated with Prop? *)
  let univs = List.map (to_universe state.uconv.map) univs in
  let i, univs = int_of_univs univs in
  let uconv = state.uconv in
  let (state : unit state), inst =
    ensure_exists { state with uconv = () } n i
  in
  let subst l =
    match Level.var_index l with
    | None -> Universe.make l
    | Some n -> List.nth univs n
  in
  let extra =
    List.map
      (fun alg -> simplify_universe (subst_univs_universe subst alg))
      inst.algs
  in
  let univs = List.concat [ univs; extra ] in
  let uconv, univs =
    CList.fold_left_map (fun state u -> to_univ_level u state) uconv univs
  in
  let u = Instance.of_array (Array.of_list univs) in
  ({ state with uconv }, Constr.mkRef (inst.ref, u))

and ensure_exists (state : unit state) n i =
  try (state, state.declared |> N.Map.find n |> Int.Map.find i)
  with Not_found ->
    (* TODO can we end up asking for a ctor or eliminator before
       asking for the inductive type? *)
    if i = 0 then CErrors.anomaly Pp.(N.pp n ++ str " was not instantiated!");
    (match N.Map.get n state.entries with
    | Def def -> declare_def state n def i
    | Ax ax -> declare_ax state n ax i
    | Ind ind -> declare_ind state n ind i
    | Quot -> CErrors.anomaly Pp.(str "quot must be predeclared"))

and declare_def state n { ty; body; univs } i =
  let state = start_uconv state univs i in
  let state, ty = to_constr ty state in
  let state, body = to_constr body state in
  let state, (univs, algs) = finish_uconv state univs in
  let entry = Declare.definition_entry ~opaque:false ~types:ty ~univs body in
  let ref = quickdef ~name:(name_for n i) entry [] in
  let () =
    if N.equal n std_prec_max then
      (* HACK needed to pass [std.prec.max.equations._eqn_1 : std.prec.max = 1024]
         without taking forever *)
      let c = match ref with ConstRef c -> c | _ -> assert false in
      Global.set_strategy (ConstKey c) Expand
  in
  let inst = { ref; algs } in
  let declared = add_declared state.declared n i inst in
  ({ state with declared }, inst)

and declare_ax state n { ty; univs } i =
  let state = start_uconv state univs i in
  let state, ty = to_constr ty state in
  let state, (univs, algs) = finish_uconv state univs in
  let entry = Declare.ParameterEntry (None, (ty, univs), None) in
  let c =
    Declare.declare_constant ~name:(name_for n i)
      ~kind:Decls.(IsAssumption Definitional)
      entry
  in
  let inst = { ref = GlobRef.ConstRef c; algs } in
  let declared = add_declared state.declared n i inst in
  ({ state with declared }, inst)

and to_params state params =
  let state, params =
    CList.fold_left_map
      (fun state (_bk, p, ty) ->
        let state, ty = to_constr ty state in
        (state, RelDecl.LocalAssum (to_annot p, ty)))
      state params
  in
  (state, List.rev params)

and declare_ind state n { params; ty; ctors; univs } i =
  let state, mind, algs, ind_name, cnames, univs, squashy =
    match get_predeclared_eq n i with
    | Some (ind_name, mind) ->
      (* Hack to let the user predeclare eq and quot before running Lean Import
         TODO make a more general Register-like API? *)
      Feedback.msg_info Pp.(Id.print ind_name ++ str " is predeclared");
      let cname = N.append n "refl" in
      let squashy =
        { maybe_prop = true; always_prop = true; lean_squashes = false }
      in
      let univs =
        match i with
        | 0 ->
          Entries.Polymorphic_entry
            ( [| Name (Id.of_string "u") |],
              UContext.make
                ( Instance.of_array [| univ_of_name (N.append N.anon "u") |],
                  Constraint.empty ) )
        | 1 -> Entries.Polymorphic_entry ([||], UContext.empty)
        | _ -> assert false
      in
      (state, mind, [], ind_name, [ cname ], univs, squashy)
    | None ->
      let state = start_uconv state univs i in
      let state, params = to_params state params in
      let state, ty = to_constr ty state in
      let state, ctors =
        CList.fold_left_map
          (fun state (n, ty) ->
            let state, ty = to_constr ty state in
            (state, (n, ty)))
          state ctors
      in
      let cnames, ctys = List.split ctors in
      let graph = state.uconv.graph in
      let state, (univs, algs) = finish_uconv state univs in
      let ind_name = name_for n i in
      let entry =
        {
          Entries.mind_entry_params = params;
          mind_entry_record = None;
          mind_entry_finite = Finite;
          mind_entry_inds =
            [
              {
                mind_entry_typename = ind_name;
                mind_entry_arity = ty;
                mind_entry_template = false;
                mind_entry_consnames = List.map (fun n -> name_for n i) cnames;
                mind_entry_lc = ctys;
              };
            ];
          mind_entry_private = None;
          mind_entry_universes = univs;
          mind_entry_cumulative = false;
        }
      in
      let squashy = N.Map.get n state.squash_info in
      let coq_squashes =
        if squashy.maybe_prop then coq_squashes graph entry else false
      in
      let mind =
        let act () =
          DeclareInd.declare_mutual_inductive_with_eliminations entry
            UnivNames.empty_binders []
        in
        if squashy.lean_squashes || not coq_squashes then act ()
        else with_unsafe_univs act ()
      in
      assert (
        squashy.lean_squashes
        || (Global.lookup_mind mind).mind_packets.(0).mind_kelim == InType);
      (state, mind, algs, ind_name, cnames, univs, squashy)
  in

  (* add ind and ctors to [declared] *)
  let inst = { ref = GlobRef.IndRef (mind, 0); algs } in
  let declared = add_declared state.declared n i inst in
  let declared =
    CList.fold_left_i
      (fun cnum declared cname ->
        add_declared declared cname i
          { ref = GlobRef.ConstructRef ((mind, 0), cnum + 1); algs })
      0 declared cnames
  in

  (* elim *)
  let make_scheme fam =
    match univs with
    | Monomorphic_entry _ -> assert false
    | Polymorphic_entry (names, uctx) as entry ->
      let u =
        if fam = Sorts.InSProp then Level.sprop
        else if lean_fancy_univs () then
          let u = DirPath.make [ Id.of_string "motive"; lean_id ] in
          Level.(make (UGlobal.make u 0))
        else UnivGen.fresh_level ()
      in
      let env = Environ.push_context ~strict:true uctx (Global.env ()) in
      let env =
        if fam = InSProp then env
        else Environ.push_context_set ~strict:false (ContextSet.singleton u) env
      in
      let inst, uentry =
        let inst, csts = UContext.dest uctx in
        ( inst,
          if fam = InSProp then entry
          else
            Polymorphic_entry
              ( Array.append [| Name (Id.of_string "motive") |] names,
                UContext.make
                  ( Instance.of_array
                      (Array.append [| u |] (Instance.to_array inst)),
                    csts ) ) )
      in
      (lean_scheme env ~dep:(not squashy.always_prop) mind inst u, uentry)
  in
  let nrec = N.append n "rec" in
  let elims =
    if squashy.lean_squashes then [ ("_indl", Sorts.InSProp) ]
    else [ ("_recl", InType); ("_indl", InSProp) ]
  in
  let declared =
    List.fold_left
      (fun declared (suffix, sort) ->
        let id = Id.of_string (Id.to_string ind_name ^ suffix) in
        let body, uentry = make_scheme sort in
        let elim =
          quickdef ~name:id
            (Declare.definition_entry ~opaque:false ~univs:uentry body)
            []
          (* TODO implicits? *)
        in
        let liftu l =
          match Level.var_index l with
          | None -> Universe.make l (* Set *)
          | Some i -> Universe.make (Level.var (i + 1))
        in
        let algs =
          if sort = InSProp then algs
          else List.map (subst_univs_universe liftu) algs
        in
        let elim = { ref = elim; algs } in
        let j =
          if squashy.lean_squashes then i
          else if sort == InType then 2 * i
          else (2 * i) + 1
        in
        add_declared declared nrec j elim)
      declared elims
  in
  ({ state with declared }, inst)

(** Generate and add the squashy info *)
let squashify state n { params; ty; ctors; univs } =
  let stateP =
    (* NB: if univs = [] this is just instantiation 0 *)
    start_uconv state univs ((1 lsl List.length univs) - 1)
  in
  let stateP, paramsP = to_params stateP params in
  let stateP, tyP = to_constr ty stateP in
  let state = { state with declared = stateP.declared } in
  let envP =
    Environ.push_rel_context paramsP
      (Environ.set_universes (Global.env ()) stateP.uconv.graph)
  in
  let _, sortP = Reduction.dest_arity envP tyP in
  if not (Sorts.is_sprop sortP) then (state, noprop)
  else
    let stateT = start_uconv state univs 0 in
    let stateT, paramsT = to_params stateT params in
    let stateT, tyT = to_constr ty stateT in
    let envT =
      Environ.push_rel_context paramsT
        (Environ.set_universes (Global.env ()) stateT.uconv.graph)
    in
    let _, sortT = Reduction.dest_arity envT tyT in
    let always_prop = Sorts.is_sprop sortT in
    match ctors with
    | [] ->
      ( { state with declared = stateT.declared },
        { maybe_prop = true; always_prop; lean_squashes = false } )
    | _ :: _ :: _ ->
      ( { state with declared = stateT.declared },
        { maybe_prop = true; always_prop; lean_squashes = true } )
    | [ (_, ctor) ] ->
      let stateT, ctorT = to_constr ctor stateT in
      let envT =
        Environ.push_rel_context paramsT
          (Environ.push_rel
             (LocalAssum
                ( Context.make_annot (N.to_name n)
                    (Sorts.relevance_of_sort sortT),
                  Term.it_mkProd_or_LetIn tyT paramsT ))
             (Environ.set_universes (Global.env ()) stateT.uconv.graph))
      in
      let args, out = Reduction.dest_prod envT ctorT in
      let forced =
        (* NB dest_prod returns [out] in whnf *)
        let _, outargs = Constr.decompose_appvect out in
        Array.fold_left
          (fun forced arg ->
            match Constr.kind arg with
            | Rel i -> Int.Set.add i forced
            | _ -> forced)
          Int.Set.empty outargs
      in
      let sigma = Evd.from_env envT in
      let npars = List.length params in
      let nargs = List.length args in
      let lean_squashes, _, _ =
        Context.Rel.fold_outside
          (fun d (squashed, i, envT) ->
            let squashed =
              if squashed then true
              else if Int.Set.mem (nargs - i) forced then false
              else
                let t = RelDecl.get_type d in
                if not (Vars.noccurn (npars + i + 1) t) then
                  (* recursive argument *)
                  false
                else
                  not
                    (Sorts.is_sprop
                       (Retyping.get_sort_of envT sigma (EConstr.of_constr t)))
            in

            (squashed, i + 1, Environ.push_rel d envT))
          args ~init:(false, 0, envT)
      in
      (* TODO translate to use non recursively uniform params (fix extraction)*)
      ( { state with declared = stateT.declared },
        { maybe_prop = true; always_prop; lean_squashes } )

let squashify state n ind =
  let state, s = squashify state n ind in
  { state with squash_info = N.Map.add n s state.squash_info }

let quot_name = N.append N.anon "quot"

let quot_modname = Id.of_string "Quot"

(* pairs of (name * number of univs) *)
let quots = [ ("", 1); ("mk", 1); ("lift", 2); ("ind", 1) ]

let declare_quot state =
  let declared =
    List.fold_left
      (fun declared (n, nunivs) ->
        let rec loop declared i =
          if i = 1 lsl nunivs then declared
          else
            let lean =
              if CString.is_empty n then quot_name else N.append quot_name n
            in
            let id =
              if CString.is_empty n then name_for_core quot_name i
              else name_for_core (N.append N.anon n) i
            in
            let qualid =
              Libnames.make_qualid (DirPath.make [ quot_modname ]) id
            in
            let ref =
              try Nametab.locate qualid
              with Not_found ->
                CErrors.user_err Pp.(str "missing Quot." ++ Id.print id)
            in
            let declared = add_declared declared lean i { ref; algs = [] } in
            loop declared (i + 1)
        in
        loop declared 0)
      state.declared quots
  in
  Feedback.msg_info Pp.(str "quot registered");
  { state with declared }

let skip_missing_quot =
  Goptions.declare_bool_option_and_ref ~depr:false
    ~name:"lean skip missing quotient"
    ~key:[ "Lean"; "Skip"; "Missing"; "Quotient" ]
    ~value:true

let declare_quot state =
  match
    Nametab.locate
      (Libnames.make_qualid (DirPath.make [ quot_modname ]) (N.to_id quot_name))
  with
  | _ -> declare_quot state
  | exception Not_found ->
    if skip_missing_quot () then (
      Feedback.msg_info Pp.(str "Skipping: missing quotient");
      state)
    else CErrors.user_err Pp.(str "missing quotient")

let empty_state =
  {
    names = RRange.singleton N.anon;
    exprs = RRange.empty;
    univs = RRange.singleton U.Prop;
    uconv = ();
    skips = 0;
    entries = N.Map.empty;
    squash_info = N.Map.empty;
    declared = N.Map.empty;
    notations = [];
  }

let do_bk = function
  | "#BD" -> NotImplicit
  | "#BI" -> Maximal
  | "#BS" -> NonMaximal
  | "#BC" -> Typeclass
  | bk ->
    CErrors.user_err
      Pp.(str "unknown binder kind " ++ str bk ++ str "." ++ fnl ())

let do_notation_kind = function
  | "#PREFIX" -> Prefix
  | "#INFIX" -> Infix
  | "#POSTFIX" -> Postfix
  | k -> assert false

let get_name state n =
  let n = int_of_string n in
  RRange.get state.names n

let get_expr state e =
  let e = int_of_string e in
  RRange.get state.exprs e

let rec do_ctors state nctors acc l =
  if nctors = 0 then (List.rev acc, l)
  else
    match l with
    | name :: ty :: rest ->
      let name = get_name state name
      and ty = get_expr state ty in
      do_ctors state (nctors - 1) ((name, ty) :: acc) rest
    | _ -> CErrors.user_err Pp.(str "Not enough constructors")

(** Replace [n] (meant to be an the inductive type appearing in the
    constructor type) by (Bound k). *)
let rec replace_ind ind k = function
  | Const (n', _) when N.equal ind n' -> Bound k
  | (Const _ | Bound _ | Sort _) as e -> e
  | App (a, b) -> App (replace_ind ind k a, replace_ind ind k b)
  | Let { name; ty; v; rest } ->
    Let
      {
        name;
        ty = replace_ind ind k ty;
        v = replace_ind ind k v;
        rest = replace_ind ind (k + 1) rest;
      }
  | Lam (bk, name, a, b) ->
    Lam (bk, name, replace_ind ind k a, replace_ind ind (k + 1) b)
  | Pi (bk, name, a, b) ->
    Pi (bk, name, replace_ind ind k a, replace_ind ind (k + 1) b)

let rec pop_params npar ty =
  if npar = 0 then ([], ty)
  else
    match ty with
    | Pi (bk, name, a, b) ->
      let pars, ty = pop_params (npar - 1) b in
      ((bk, name, a) :: pars, ty)
    | _ -> assert false

let fix_ctor ind nparams ty =
  let _, ty = pop_params nparams ty in
  replace_ind ind nparams ty

let add_entry state n entry =
  { state with entries = N.Map.add n entry state.entries }

let as_univ state s = RRange.get state.univs (int_of_string s)

let just_parse =
  Goptions.declare_bool_option_and_ref ~depr:false
    ~key:[ "Lean"; "Just"; "Parsing" ]
    ~value:false

let upfront_instances =
  Goptions.declare_bool_option_and_ref ~depr:false
    ~key:[ "Lean"; "Upfront"; "Instantiation" ]
    ~value:false

let declare_instances act state univs =
  let stop = if upfront_instances () then 1 lsl List.length univs else 1 in
  let rec loop state i =
    if i = stop then state
    else
      let state = act state i in
      loop state (i + 1)
  in
  loop state 0

let declare_def state name def =
  declare_instances
    (fun state i -> fst (declare_def state name def i))
    state def.univs

let declare_ax state name ax =
  declare_instances
    (fun state i -> fst (declare_ax state name ax i))
    state ax.univs

let declare_ind state name ind =
  let state = squashify state name ind in
  declare_instances
    (fun state i -> fst (declare_ind state name ind i))
    state ind.univs

let cur_name = ref N.anon

let do_line state l =
  cur_name := N.anon;
  (* Lean printing strangeness: sometimes we get double spaces (typically with INFIX) *)
  match
    List.filter (fun s -> s <> "") (String.split_on_char ' ' (String.trim l))
  with
  | [] -> state (* empty line *)
  | "#DEF" :: name :: ty :: body :: univs ->
    let name = get_name state name in
    cur_name := name;
    let ty = get_expr state ty
    and body = get_expr state body
    and univs = List.map (get_name state) univs in
    let def = { ty; body; univs } in
    let state = if just_parse () then state else declare_def state name def in
    add_entry state name (Def def)
  | "#AX" :: name :: ty :: univs ->
    let name = get_name state name in
    cur_name := name;
    let ty = get_expr state ty
    and univs = List.map (get_name state) univs in
    let ax = { ty; univs } in
    let state = if just_parse () then state else declare_ax state name ax in
    add_entry state name (Ax ax)
  | "#IND" :: nparams :: name :: ty :: nctors :: rest ->
    let name = get_name state name in
    cur_name := name;
    let nparams = int_of_string nparams
    and ty = get_expr state ty
    and nctors = int_of_string nctors in
    let params, ty = pop_params nparams ty in
    let ctors, univs = do_ctors state nctors [] rest in
    let ctors =
      List.map (fun (nctor, ty) -> (nctor, fix_ctor name nparams ty)) ctors
    in
    let univs = List.map (get_name state) univs in
    let ind = { params; ty; ctors; univs } in
    let state = if just_parse () then state else declare_ind state name ind in
    add_entry state name (Ind ind)
  | [ "#QUOT" ] ->
    let state = if just_parse () then state else declare_quot state in
    add_entry state quot_name Quot
  | (("#PREFIX" | "#INFIX" | "#POSTFIX") as kind) :: rest ->
    (match rest with
    | [ n; level; token ] ->
      let kind = do_notation_kind kind
      and n = get_name state n
      and level = int_of_string level in
      {
        state with
        notations = { kind; head = n; level; token } :: state.notations;
      }
    | _ ->
      CErrors.user_err
        Pp.(
          str "bad notation: " ++ prlist_with_sep (fun () -> str "; ") str rest))
  | next :: rest ->
    let next = int_of_string next in
    (match rest with
    | [ "#NS"; base; cons ] ->
      assert (next = RRange.length state.names);
      let base = get_name state base in
      let cons = N.append base cons in
      { state with names = RRange.append state.names cons }
    | [ "#NI"; base; cons ] ->
      assert (next = RRange.length state.names);
      (* NI: private name. cons is an int, base is expected to be _private :: stuff
         (true in lean stdlib, dunno elsewhere) *)
      let base = get_name state base in
      let n = N.raw_append base cons in
      { state with names = RRange.append state.names n }
    | [ "#US"; base ] ->
      assert (next = RRange.length state.univs);
      let base = as_univ state base in
      { state with univs = RRange.append state.univs (Succ base) }
    | [ "#UM"; a; b ] ->
      assert (next = RRange.length state.univs);
      let a = as_univ state a
      and b = as_univ state b in
      { state with univs = RRange.append state.univs (Max (a, b)) }
    | [ "#UIM"; a; b ] ->
      assert (next = RRange.length state.univs);
      let a = as_univ state a
      and b = as_univ state b in
      { state with univs = RRange.append state.univs (IMax (a, b)) }
    | [ "#UP"; n ] ->
      assert (next = RRange.length state.univs);
      let n = get_name state n in
      { state with univs = RRange.append state.univs (UNamed n) }
    | [ "#EV"; n ] ->
      assert (next = RRange.length state.exprs);
      let n = int_of_string n in
      { state with exprs = RRange.append state.exprs (Bound n) }
    | [ "#ES"; u ] ->
      assert (next = RRange.length state.exprs);
      let u = as_univ state u in
      { state with exprs = RRange.append state.exprs (Sort u) }
    | "#EC" :: n :: univs ->
      assert (next = RRange.length state.exprs);
      let n = get_name state n
      and univs = List.map (as_univ state) univs in
      { state with exprs = RRange.append state.exprs (Const (n, univs)) }
    | [ "#EA"; a; b ] ->
      assert (next = RRange.length state.exprs);
      let a = get_expr state a
      and b = get_expr state b in
      { state with exprs = RRange.append state.exprs (App (a, b)) }
    | [ "#EZ"; n; ty; v; rest ] ->
      assert (next = RRange.length state.exprs);
      let n = get_name state n
      and ty = get_expr state ty
      and v = get_expr state v
      and rest = get_expr state rest in
      {
        state with
        exprs = RRange.append state.exprs (Let { name = n; ty; v; rest });
      }
    | [ "#EL"; bk; n; ty; body ] ->
      assert (next = RRange.length state.exprs);
      let bk = do_bk bk
      and n = get_name state n
      and ty = get_expr state ty
      and body = get_expr state body in
      { state with exprs = RRange.append state.exprs (Lam (bk, n, ty, body)) }
    | [ "#EP"; bk; n; ty; body ] ->
      assert (next = RRange.length state.exprs);
      let bk = do_bk bk
      and n = get_name state n
      and ty = get_expr state ty
      and body = get_expr state body in
      { state with exprs = RRange.append state.exprs (Pi (bk, n, ty, body)) }
    | _ ->
      CErrors.user_err
        Pp.(str "cannot understand " ++ str l ++ str "." ++ fnl ()))

let lcnt = ref 0

let rec is_arity = function
  | Sort _ -> true
  | Pi (_, _, _, b) -> is_arity b
  | _ -> false

let print_squashes =
  Goptions.declare_bool_option_and_ref ~depr:false
    ~key:[ "Lean"; "Print"; "Squash"; "Info" ]
    ~value:false

let finish state =
  let max_univs, cnt =
    N.Map.fold
      (fun _ entry (m, cnt) ->
        match entry with
        | Ax { univs } | Def { univs } | Ind { univs } ->
          let l = List.length univs in
          (max m l, cnt + (1 lsl l))
        | Quot -> (max m 1, cnt + 2))
      state.entries (0, 0)
  in
  let nonarities =
    N.Map.fold
      (fun _ entry cnt ->
        match entry with
        | Ax _ | Def _ | Quot -> cnt
        | Ind ind -> if is_arity ind.ty then cnt else cnt + 1)
      state.entries 0
  in
  let squashes =
    if not (print_squashes ()) then Pp.mt ()
    else
      N.Map.fold
        (fun n s pp -> Pp.(pp ++ fnl () ++ N.pp n ++ spc () ++ pp_squashy s))
        state.squash_info
        Pp.(mt ())
  in
  Feedback.msg_info
    Pp.(
      fnl () ++ str "Done!" ++ fnl () ++ str "- "
      ++ int (N.Map.cardinal state.entries)
      ++ str " entries (" ++ int cnt ++ str " possible instances)"
      ++ (if N.Map.exists (fun _ x -> Quot == x) state.entries then
          str " (including quot)."
         else str ".")
      ++ fnl () ++ str "- "
      ++ int (RRange.length state.univs)
      ++ str " universe expressions"
      ++ fnl () ++ str "- "
      ++ int (RRange.length state.names)
      ++ str " names" ++ fnl () ++ str "- "
      ++ int (RRange.length state.exprs)
      ++ str " expression nodes" ++ fnl () ++ str "Skipped " ++ int state.skips
      ++ fnl ()
      ++ str "Max universe instance length "
      ++ int max_univs ++ str "." ++ fnl () ++ int nonarities
      ++ str " inductives have non syntactically arity types."
      ++ squashes)

let skip_errors =
  Goptions.declare_bool_option_and_ref ~depr:false
    ~key:[ "Lean"; "Skip"; "Errors" ]
    ~value:false

let rec do_input state ch =
  match input_line ch with
  | exception End_of_file ->
    close_in ch;
    finish state
  | l ->
    (match do_line state l with
    | state ->
      incr lcnt;
      do_input state ch
    | exception e ->
      let e = CErrors.push e in
      if skip_errors () then begin
        Feedback.msg_info
          Pp.(
            str "Skipping: issue at line "
            ++ int !lcnt
            ++ str (": " ^ l)
            ++ str " (current entry " ++ N.pp !cur_name ++ str ")" ++ fnl ()
            ++ CErrors.iprint e);
        incr lcnt;
        do_input { state with skips = state.skips + 1 } ch
      end
      else begin
        close_in ch;
        finish state;
        Feedback.msg_info
          Pp.(
            str "issue at line " ++ int !lcnt
            ++ str (": " ^ l)
            ++ str " (current entry " ++ N.pp !cur_name ++ str ")" ++ fnl ()
            ++ fnl () ++ CErrors.iprint e)
      end)

let import f =
  lcnt := 1;
  do_input empty_state (open_in f)

(* Lean stdlib:
- 10244 entries (24065 possible instances)
- 274 universe expressions
- 28 named universes
- 14091 names
- 562009 expression nodes

Max universe instance length 4.
0 inductives have non syntactically arity types.

export: 46s, 450KB ram(?)
leanchecker: 8s, 80KB ram(?)
*)

(* mathlib:
- 66400 entries (275215 possible instances)
- 2707 universe expressions
- 87141 names
- 8013226 expression nodes

Max universe instance length 10.
0 inductives have non syntactically arity types.

NB: mathlib travis checker job says "checked 68170 declarations",
I think it counts recursors separately from the inductive
+ maybe the quotient stuff

export: takes a while and eats lots of ram
leanchecker: 6min, 1GB ram (pretty stable ram usage)

Coq takes 690KB ram in just parsing mode

*)

(* TODO: best line 23000 in stdlib
   stack overflow

   with upfront instances: 39860 in stdlib
   missing quot

   current skip (including at will interrupts): 815 in stdlib
 *)
