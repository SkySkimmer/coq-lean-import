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
  type t

  val anon : t

  val append : t -> string -> t

  val raw_append : t -> string -> t
  (** for private names *)

  val to_string : t -> string

  val to_name : t -> Name.t

  val pp : t -> Pp.t

  module Set : CSet.S with type elt = t

  module Map : CMap.ExtS with type key = t and module Set := Set
end = struct
  type t = string
  (** "foo.bar.baz" is [baz;bar;foo] (like with dirpaths) *)

  let anon : t = ""

  let append a b = if a = "" then b else a ^ "." ^ b

  let raw_append a b = a ^ b

  let to_id (x : t) = Id.of_string x

  let to_name x = if x = "" then Anonymous else Name (to_id x)

  let to_string x = x

  let pp = Pp.str

  module Set = CString.Set
  module Map = CString.Map
end

module N = LeanName

type uid = UId of int

type uexpr =
  | Prop
  | Succ of uid
  | Max of uid * uid
  | IMax of uid * uid
  | UNamed of N.t

type uconv = {
  map : Univ.Level.t Int.Map.t;  (** Map from univ ids to Coq levels *)
  csts : Univ.Constraint.t;  (** Constraints verified by the levels *)
}

let rec to_univ_level exprs (UId i) uconv =
  let open Univ in
  match Int.Map.find_opt i uconv.map with
  | Some u -> (uconv, u)
  | None ->
    (match RRange.get exprs i with
    | Prop -> (uconv, Level.sprop)
    | UNamed n ->
      CErrors.anomaly ~label:"to_univ_level"
        Pp.(str "unknown name " ++ N.pp n ++ str ".")
    | Succ u ->
      let uconv, u = to_univ_level exprs u uconv in
      let n = UnivGen.fresh_level () in
      let csts =
        if Level.is_sprop u then Constraint.add (Level.set, Lt, n) uconv.csts
        else Constraint.add (u, Lt, n) uconv.csts
      in
      let uconv = { map = Int.Map.add i n uconv.map; csts } in
      (uconv, n)
    | Max (a, b) ->
      let uconv, a = to_univ_level exprs a uconv in
      let uconv, b = to_univ_level exprs b uconv in
      let n = UnivGen.fresh_level () in
      let csts = uconv.csts in
      let csts =
        if Level.is_sprop a then csts else Constraint.add (a, Le, n) csts
      in
      let csts =
        if Level.is_sprop b then csts else Constraint.add (b, Le, n) csts
      in
      let uconv = { map = Int.Map.add i n uconv.map; csts } in
      (uconv, n)
    | IMax (a, b) ->
      let uconv, b = to_univ_level exprs b uconv in
      if Level.is_sprop b then (uconv, b)
      else
        let uconv, a = to_univ_level exprs a uconv in
        let n = UnivGen.fresh_level () in
        let csts = uconv.csts in
        let csts =
          if Level.is_sprop a then csts else Constraint.add (a, Le, n) csts
        in
        let csts =
          if Level.is_sprop b then csts else Constraint.add (b, Le, n) csts
        in
        let uconv = { map = Int.Map.add i n uconv.map; csts } in
        (uconv, n))

type binder_kind =
  | NotImplicit
  | Maximal
  | NonMaximal
  | Typeclass  (** WRT Coq, Typeclass is like Maximal. *)

type expr =
  | Bound of int
  | Sort of uid
  | Const of N.t * uid list
  | App of expr * expr
  | Let of { name : N.t; ty : expr; v : expr; rest : expr }
      (** Let: undocumented in export_format.md *)
  | Lam of binder_kind * N.t * expr * expr
  | Pi of binder_kind * N.t * expr * expr

type def = { ty : expr; body : expr; univs : N.t list }

type ax = { ty : expr; univs : N.t list }

type ind = {
  nparams : int;
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

type instantiation = { ref : GlobRef.t }

type 'uconv state = {
  names : N.t RRange.t;
  exprs : expr RRange.t;
  univs : uexpr RRange.t;
  rev_univs : uid N.Map.t;
  uconv : 'uconv;
  entries : entry N.Map.t;
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

let int_of_univs =
  let rec aux i = function
    | [] -> i
    | u :: rest -> aux ((i * 2) + if Univ.Level.is_sprop u then 1 else 0) rest
  in
  fun l -> aux 0 (List.rev l)

let start_uconv (state : unit state) univs i =
  let rec aux map i = function
    | [] ->
      assert (i = 0);
      map
    | u :: univs ->
      let (UId u) = N.Map.get u state.rev_univs in
      let map =
        if i mod 2 = 0 then Int.Map.add u (UnivGen.fresh_level ()) map
        else Int.Map.add u Univ.Level.sprop map
      in
      aux map (i / 2) univs
  in
  let map = aux Int.Map.empty i univs in
  { state with uconv = { map; csts = Univ.Constraint.empty } }

let rec to_constr =
  let open Constr in
  let ( >>= ) x f state =
    let state, x = x state in
    f x state
  in
  let to_univ_level x state =
    let uconv, x = to_univ_level state.univs x state.uconv in
    ({ state with uconv }, x)
  in
  let ret x state = (state, x) in
  function
  | Bound i -> ret (mkRel (i + 1))
  | Sort uid ->
    to_univ_level uid >>= fun u ->
    ret (mkSort (Sorts.sort_of_univ (Univ.Universe.make u)))
  | Const (n, univs) ->
    fun state ->
      let state, univs =
        CList.fold_left_map
          (fun state uid -> to_univ_level uid state)
          state univs
      in
      instantiate state n univs
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

and instantiate state n univs =
  assert (List.length univs < Sys.int_size);
  let i = int_of_univs univs in
  let uconv = state.uconv in
  let (state : unit state), inst =
    ensure_exists { state with uconv = () } n i
  in
  let state = { state with uconv } in
  let inst = state.declared |> N.Map.find n |> Int.Map.find i in
  (* TODO adjust instantiation for the ref's extra univs *)
  (state, Constr.mkRef (inst.ref, Univ.Instance.of_array (Array.of_list univs)))

and ensure_exists (state : unit state) n i =
  try (state, state.declared |> N.Map.find n |> Int.Map.find i)
  with Not_found ->
    assert (i <> 0);
    (match N.Map.find n state.entries with
    | Def def -> declare_def state n def i
    | Ax ax -> assert false
    | Ind ind -> assert false)

and declare_def state n { ty; body; univs } i =
  let state = start_uconv state univs i in
  let state, ty = to_constr ty state in
  let state, body = to_constr body state in
  let state = { state with uconv = () } in
  ignore state;
  assert false

let _ = to_constr

let empty_state =
  {
    names = RRange.singleton N.anon;
    exprs = RRange.empty;
    univs = RRange.singleton Prop;
    rev_univs = N.Map.empty;
    uconv = ();
    entries = N.Map.empty;
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

let add_entry state n entry =
  { state with entries = N.Map.add n entry state.entries }

let as_uid s = UId (int_of_string s)

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
    add_entry state name (Def def)
  | "#AX" :: name :: ty :: univs ->
    let name = get_name state name
    and ty = get_expr state ty
    and univs = List.map (get_name state) univs in
    let ax = { ty; univs } in
    add_entry state name (Ax ax)
  | "#IND" :: nparams :: name :: ty :: nctors :: rest ->
    let nparams = int_of_string nparams
    and name = get_name state name
    and ty = get_expr state ty
    and nctors = int_of_string nctors in
    let ctors, univs = do_ctors state nctors [] rest in
    let univs = List.map (get_name state) univs in
    let ind = { nparams; ty; ctors; univs } in
    add_entry state name (Ind ind)
  | [ "#QUOT" ] -> state (* TODO *)
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
      let base = as_uid base in
      { state with univs = RRange.append state.univs (Succ base) }
    | [ "#UM"; a; b ] ->
      assert (next = RRange.length state.univs);
      let a = as_uid a
      and b = as_uid b in
      { state with univs = RRange.append state.univs (Max (a, b)) }
    | [ "#UIM"; a; b ] ->
      assert (next = RRange.length state.univs);
      let a = as_uid a
      and b = as_uid b in
      { state with univs = RRange.append state.univs (IMax (a, b)) }
    | [ "#UP"; n ] ->
      assert (next = RRange.length state.univs);
      let n = get_name state n in
      {
        state with
        univs = RRange.append state.univs (UNamed n);
        rev_univs = N.Map.add n (UId next) state.rev_univs;
      }
    | [ "#EV"; n ] ->
      assert (next = RRange.length state.exprs);
      let n = int_of_string n in
      { state with exprs = RRange.append state.exprs (Bound n) }
    | [ "#ES"; u ] ->
      assert (next = RRange.length state.exprs);
      let u = as_uid u in
      { state with exprs = RRange.append state.exprs (Sort u) }
    | "#EC" :: n :: univs ->
      assert (next = RRange.length state.exprs);
      let n = get_name state n
      and univs = List.map as_uid univs in
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

let rec do_input state ch =
  match input_line ch with
  | exception End_of_file -> state
  | l ->
    let state =
      try do_line state l
      with e ->
        let e = CErrors.push e in
        Feedback.msg_info
          Pp.(str "issue at line " ++ int !lcnt ++ str (": " ^ l) ++ fnl ());
        Util.iraise e
    in
    incr lcnt;
    do_input state ch

let import f =
  let ch = open_in f in
  let state =
    try
      lcnt := 0;
      let s = do_input empty_state ch in
      close_in ch;
      s
    with e ->
      close_in ch;
      raise e
  in
  Feedback.msg_info
    Pp.(
      str "Read "
      ++ int (N.Map.cardinal state.entries)
      ++ str " entries. Found "
      ++ int (RRange.length state.univs)
      ++ str " universe expressions, "
      ++ int (N.Map.cardinal state.rev_univs)
      ++ str " named universes,"
      ++ int (RRange.length state.names)
      ++ str " names and "
      ++ int (RRange.length state.exprs)
      ++ str " expression nodes.")

(* Lean stdlib:
- 10244 entries
- 274 universe expressions
- 28 named universes
- 14091 names
- 562009 expression nodes
*)