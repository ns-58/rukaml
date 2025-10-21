let todo () = failwith "todo"

type start = cfg_out * consts
and return = cfg_in * returned
and const = Frontend.Parsetree.const * data_sucs
and binop = string * data_pred * data_pred * data_sucs
and cfg_suc = [ `Return of return ]
and cfg_pred = [ `Start of start ]
and returned = { mutable returned : data_pred option }

and data_pred =
  [ `Const of const
  | `BinOp of binop
  ]

and data_suc =
  [ `Return of return
  | `BinOp of binop
  ]

and cfg_in = { mutable cfg_in : cfg_pred }
and cfg_out = { mutable cfg_out : cfg_suc }
and data_sucs = { mutable data_sucs : data_suc list }
and consts = { mutable consts : [ `Const of const ] list }

type node =
  [ data_pred
  | data_suc
  | cfg_pred
  | cfg_suc
  ]
(*todo: remove unused mutables*)

open Compile_lib.ANF
open Frontend.Ident
module SMap = Map.Make (String)
open Monads.Store

let ( >>| ) f x = f >>= fun t -> return @@ x t
let ( let+ ) = ( >>| )

let both f x1 x2 =
  let* a = f x1 in
  let+ b = f x2 in
  a, b
;;

let find k = get >>| SMap.find k
let add k v = get >>| SMap.add k v >>= put

let add_data_suc1 suc : data_pred -> unit = function
  | `Const (_, ds) | `BinOp (_, _, _, ds) -> ds.data_sucs <- suc :: ds.data_sucs
;;

let add_data_suc suc = List.iter @@ add_data_suc1 suc

let from_anf vb =
  let c = { consts = [] } in
  let r = { returned = None } in
  let rec start_node = { cfg_out = `Return fin_node }, c
  and fin_node = { cfg_in = `Start start_node }, r in
  let add_const n = c.consts <- n :: c.consts in
  match vb with
  | _, { hum_name = "main"; _ }, e ->
    let helper_a = function
      | AConst c ->
        let c = `Const (c, { data_sucs = [] }) in
        add_const c;
        return c
      | AVar { hum_name = name; _ } -> find name
      | _ -> todo ()
    in
    let rec helper_c = function
      | CApp (APrimitive op, a1, [ a2 ]) when is_infix_binop op ->
        let+ a1, a2 = both helper_a a1 a2 in
        let bo = `BinOp (op, a1, a2, { data_sucs = [] }) in
        add_data_suc bo [ a1; a2 ];
        bo
      | CAtom i -> helper_a i
      | _ -> todo ()
    and helper =
      let open Frontend.Typedtree in
      function
      | EComplex c -> helper_c c
      | ELet (NonRecursive, Tpat_var { hum_name = name; _ }, c, e) ->
        let* () = helper_c c >>= add name in
        helper e
      | _ -> todo ()
    in
    run (helper e) SMap.empty
    |> fun (_, returned) ->
    r.returned <- Some returned;
    add_data_suc1 (`Return fin_node) returned;
    start_node, fin_node
  | _ -> todo ()
;;

open Compile_lib

let equal () =
  let seen = Hashtbl.create 58 in
  let rec ( = ) x y =
    let lists2 = List.fold_left2 (fun acc x y -> acc && (x :> node) = (y :> node)) true in
    let ds d1 d2 =
      List.fold_left2
        (fun acc x y -> acc && (x :> node) = (y :> node))
        true
        d1.data_sucs
        d2.data_sucs
    in
    let hashed_xy = Hashtbl.hash (x, y) in
    match Hashtbl.find seen hashed_xy with
    | () -> true
    | exception Not_found ->
      Hashtbl.add seen hashed_xy ();
      (match
         match x, y with
         | `Start (c1, { consts = con1 }), `Start (c2, { consts = con2 }) ->
           lists2 con1 con2 && (c1.cfg_out :> node) = (c2.cfg_out :> node)
         | `Return (c1, { returned = None }), `Return (c2, { returned = None }) ->
           (c1.cfg_in :> node) = (c2.cfg_in :> node)
         | `Return (c1, { returned = Some r1 }), `Return (c2, { returned = Some r2 }) ->
           (c1.cfg_in :> node) = (c2.cfg_in :> node) && (r1 :> node) = (r2 :> node)
         | `Const (data1, d1), `Const (data2, d2) -> Stdlib.( = ) data1 data2 && ds d1 d2
         | `BinOp (op1, a11, a12, d1), `BinOp (op2, a21, a22, d2) ->
           Stdlib.( = ) op1 op2
           && (a11 :> node) = (a21 :> node)
           && (a12 :> node) = (a22 :> node)
           && ds d1 d2
         | (`Start _ | `Return _ | `Const _ | `BinOp _), _ -> false
       with
       | r -> r
       | exception Invalid_argument _ -> false)
  in
  ( = )
;;

let from_string_vb text =
  let open Frontend in
  let open Result in
  let ( let* ) = bind in
  get_ok
  @@ let* _, ttree = Inferencer.vb @@ Parsing.parse_vb_exn text in
     ANF.anf_vb ttree |> from_anf |> fst |> ok
;;

let%test "ret0" =
  let rec start = { cfg_out = `Return fin }, { consts = [ `Const zero ] }
  and fin = { cfg_in = `Start start }, { returned = Some (`Const zero) }
  and zero = Frontend.Parsetree.const_int 0, { data_sucs = [ `Return fin ] } in
  let ( = ) = equal () in
  `Start (from_string_vb "let main = 0") = `Start start
;;

let%test "binops" =
  let rec start =
    { cfg_out = `Return fin }, { consts = [ `Const one; `Const three; `Const two ] }
  and fin = { cfg_in = `Start start }, { returned = Some (`BinOp sub2) }
  and sub1 = "-", `Const two, `Const three, { data_sucs = [ `BinOp sub2 ] }
  and sub2 = "-", `Const one, `BinOp sub1, { data_sucs = [ `Return fin ] }
  and one = Frontend.Parsetree.const_int 1, { data_sucs = [ `BinOp sub2 ] }
  and two = Frontend.Parsetree.const_int 2, { data_sucs = [ `BinOp sub1 ] }
  and three = Frontend.Parsetree.const_int 3, { data_sucs = [ `BinOp sub1 ] } in
  let ( = ) = equal () in
  `Start (from_string_vb "let main = 1 - (2 - 3) ") = `Start start
;;
