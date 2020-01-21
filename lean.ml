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

let to_universe map u =
  let u = to_universe map u in
  match Universe.repr u with
  | (l, n) :: (_ :: _ as rest) when Level.is_set l ->
    if List.exists (fun (_, n') -> n <= n' + 1) rest then
      List.fold_left
        (fun u (l, n) ->
          Universe.sup u (do_n Universe.super (Universe.make l) n))
        Universe.sprop rest
    else u
  | _ -> u

type uconv = {
  map : Level.t N.Map.t;  (** Map from lean names to Coq universes *)
  levels : Level.t Universe.Map.t;
      (** Map from algebraic universes to levels (only levels representing
          an algebraic) *)
  graph : UGraph.t;
}

let lean_id = Id.of_string "Lean"

let lean_fancy_univs =
  Goptions.declare_bool_option_and_ref ~depr:false ~name:"lean fancy univs"
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

type entry = Def of def | Ax of ax | Ind of ind

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
  is_large_elim : bool;
      (** When declaring the eliminator for an inductive, the motive's
          universe is the first explicit universe for Lean and after the algebraics for Coq. *)
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

how to decide which case we're in?
we can't use the type after instantiating for 0 as at that point
we have already forgotten the distinction between max(1,u) and u

in practice (all stdlib and mathlib) the target universe is available without reduction
(ie syntactic arity) even though the system doesn't require it.
so we can just look at it directly (we don't want to implement a reduction system)

strictly speaking, we need to reduce the all-Prop instantiation of the type,
and (if the type is maybe-Prop) reduce and retype the all-non-Prop
instantiation of each constructor types (careful with fix_ctor)
NB lemma: some instantiation is in Prop iff the all-Prop instantiation is in Prop

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

type squashy =
  | NoProp  (** Type cannot be in Prop *)
  | MaybeProp of {
      always_prop : bool;
          (** controls whether the lean eliminator is dependent (and
              special reduction, but we just let Coq do its thing for that). *)
      lean_squashed : bool;
          (** Self descriptive. We handle necessity of unsafe flags per-instantiation. *)
    }

type 'uconv state = {
  names : N.t RRange.t;
  exprs : expr RRange.t;
  univs : U.t RRange.t;
  uconv : 'uconv;
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
  let univs =
    CList.map_filter
      (fun u ->
        let u = N.Map.get u map in
        if Level.is_sprop u then None else Some u)
      ounivs
  in
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

let name_for n i =
  if i = 0 then N.to_id n else Id.of_string (N.to_string n ^ string_of_int i)

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
    to_constr rest >>= fun rest -> ret (mkLetIn (to_annot name, ty, v, rest))
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
  let motive, univs =
    if inst.is_large_elim then
      match univs with [] -> assert false | m :: univs -> ([ m ], univs)
    else ([], univs)
  in
  let subst l =
    match Level.var_index l with
    | None -> Universe.make l
    | Some n -> List.nth univs n
  in
  let extra = List.map (fun alg -> subst_univs_universe subst alg) inst.algs in
  let univs = List.concat [ univs; extra; motive ] in
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
    | Ind ind -> declare_ind state n ind i)

and declare_def state n { ty; body; univs } i =
  let state = start_uconv state univs i in
  let state, ty = to_constr ty state in
  let state, body = to_constr body state in
  let state, (univs, algs) = finish_uconv state univs in
  let kind = Decls.(IsDefinition Definition) in
  let entry = Declare.definition_entry ~opaque:false ~types:ty ~univs body in
  let scope = DeclareDef.Global Declare.ImportDefaultBehavior in
  let ref =
    DeclareDef.declare_definition ~scope ~name:(name_for n i) ~kind
      UnivNames.empty_binders entry []
  in
  let inst = { ref; algs; is_large_elim = false } in
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
  let inst = { ref = GlobRef.ConstRef c; algs; is_large_elim = false } in
  let declared = add_declared state.declared n i inst in
  ({ state with declared }, inst)

and declare_ind state n { params; ty; ctors; univs } i =
  let state = start_uconv state univs i in
  let state, params =
    CList.fold_left_map
      (fun state (_bk, p, ty) ->
        let state, ty = to_constr ty state in
        (state, Context.Rel.Declaration.LocalAssum (to_annot p, ty)))
      state params
  in
  let params = List.rev params in
  let state, ty = to_constr ty state in
  let state, ctors =
    CList.fold_left_map
      (fun state (n, ty) ->
        let state, ty = to_constr ty state in
        (state, (n, ty)))
      state ctors
  in
  let cnames, ctys = List.split ctors in
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
  let mind =
    DeclareInd.declare_mutual_inductive_with_eliminations entry
      UnivNames.empty_binders []
  in
  let inst = { ref = GlobRef.IndRef (mind, 0); algs; is_large_elim = false } in
  let declared = add_declared state.declared n i inst in
  let declared =
    CList.fold_left_i
      (fun cnum declared cname ->
        add_declared declared cname i
          {
            ref = GlobRef.ConstructRef ((mind, 0), cnum + 1);
            algs;
            is_large_elim = false;
          })
      0 declared cnames
  in
  let squashed, relevant =
    let mib = Global.lookup_mind mind in
    let mip = mib.mind_packets.(0) in
    (mip.mind_kelim == Sorts.InSProp, mip.mind_relevance == Sorts.Relevant)
  in
  (* TODO I think we should autodeclare both in the _rect case *)
  let elim_suffix, is_large_elim =
    if squashed then ("_sind", false) else ("_rect", true)
  in
  let elim_id = Id.of_string (Id.to_string ind_name ^ elim_suffix) in
  let () =
    Indschemes.do_mutual_induction_scheme
      [
        ( CAst.make elim_id,
          relevant,
          (mind, 0),
          if is_large_elim then InType else InSProp );
      ]
  in
  let elim = Nametab.locate (Libnames.qualid_of_ident elim_id) in
  let elim = { ref = elim; algs; is_large_elim } in
  let declared =
    add_declared declared (N.append n "rec")
      (if is_large_elim then 2 * i else i)
      elim
  in
  ({ state with declared }, inst)

let declare_quot state = state (* TODO *)

let _ = to_constr

let empty_state =
  {
    names = RRange.singleton N.anon;
    exprs = RRange.empty;
    univs = RRange.singleton U.Prop;
    uconv = ();
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
  Goptions.declare_bool_option_and_ref ~depr:false ~name:"lean just parse"
    ~key:[ "Lean"; "Just"; "Parsing" ]
    ~value:false

let do_line state l =
  (* Lean printing strangeness: sometimes we get double spaces (typically with INFIX) *)
  match
    List.filter (fun s -> s <> "") (String.split_on_char ' ' (String.trim l))
  with
  | [] -> state (* empty line *)
  | "#DEF" :: name :: ty :: body :: univs ->
    let name = get_name state name
    and ty = get_expr state ty
    and body = get_expr state body
    and univs = List.map (get_name state) univs in
    let def = { ty; body; univs } in
    let state =
      if just_parse () then state else fst (declare_def state name def 0)
    in
    add_entry state name (Def def)
  | "#AX" :: name :: ty :: univs ->
    let name = get_name state name
    and ty = get_expr state ty
    and univs = List.map (get_name state) univs in
    let ax = { ty; univs } in
    let state =
      if just_parse () then state else fst (declare_ax state name ax 0)
    in
    add_entry state name (Ax ax)
  | "#IND" :: nparams :: name :: ty :: nctors :: rest ->
    let nparams = int_of_string nparams
    and name = get_name state name
    and ty = get_expr state ty
    and nctors = int_of_string nctors in
    let params, ty = pop_params nparams ty in
    let ctors, univs = do_ctors state nctors [] rest in
    let ctors =
      List.map (fun (nctor, ty) -> (nctor, fix_ctor name nparams ty)) ctors
    in
    let univs = List.map (get_name state) univs in
    let ind = { params; ty; ctors; univs } in
    let state =
      if just_parse () then state else fst (declare_ind state name ind 0)
    in
    add_entry state name (Ind ind)
  | [ "#QUOT" ] -> if just_parse () then state else declare_quot state
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

let finish state =
  let max_univs, cnt =
    N.Map.fold
      (fun _ entry (m, cnt) ->
        match entry with
        | Ax { univs } | Def { univs } | Ind { univs } ->
          let l = List.length univs in
          (max m l, cnt + (1 lsl l)))
      state.entries (0, 0)
  in
  let nonarities =
    N.Map.fold
      (fun _ entry cnt ->
        match entry with
        | Ax _ | Def _ -> cnt
        | Ind ind -> if is_arity ind.ty then cnt else cnt + 1)
      state.entries 0
  in
  Feedback.msg_info
    Pp.(
      str "Read "
      ++ int (N.Map.cardinal state.entries)
      ++ str " entries (" ++ int cnt
      ++ str " possible instances). Found "
      ++ int (RRange.length state.univs)
      ++ str " universe expressions, "
      ++ int (RRange.length state.names)
      ++ str " names and "
      ++ int (RRange.length state.exprs)
      ++ str " expression nodes." ++ fnl ()
      ++ str "Max universe instance length "
      ++ int max_univs ++ str "." ++ fnl () ++ int nonarities
      ++ str " inductives have non syntactically arity types.")

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
      close_in ch;
      Feedback.msg_info
        Pp.(
          str "issue at line " ++ int !lcnt
          ++ str (": " ^ l)
          ++ fnl () ++ CErrors.iprint e))

let import f =
  lcnt := 1;
  (* we don't use autodeclared schemes to control if we use dependent elim *)
  Flags.without_option Indschemes.elim_flag
    (fun () -> do_input empty_state (open_in f))
    ();
  ()

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

(* TODO: best line 742 in core.out
   bad instantiation of eq.rec to eq_sind because bad singleton elim
 *)
