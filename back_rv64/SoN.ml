let todo () = failwith "todo"

type start = cfg_out * consts
and return = cfg_in * returned
and const = Frontend.Parsetree.const * data_sucs
and binop = string * data_pred * data_pred * data_sucs
and ite = cfg_in * data_pred * cfg_out * cfg_out
and region = cfg_in * cfg_in * due_phi * cfg_out
and phi = data_pred * data_pred * due_region * data_sucs

and cfg_suc =
  [ `Return of return
  | `ITE of ite
  | `Region of region
  ]

and cfg_pred =
  [ `Start of start
  | `ITE of ite
  | `Region of region
  ]

and returned = { mutable returned : data_pred option }

and data_pred =
  [ `Const of const
  | `BinOp of binop
  | `Phi of phi
  ]

and data_suc =
  [ `Return of return
  | `BinOp of binop
  | `ITE of ite
  | `Phi of phi
  ]

and cfg_in = { mutable cfg_in : cfg_pred }
and cfg_out = { mutable cfg_out : cfg_suc }
and data_sucs = { mutable data_sucs : data_suc list }

(*ввести дата-предц, для мутабельности*)
(*remove Const constructor ?*)
and consts = { mutable consts : [ `Const of const ] list }
and due_region = { mutable region : [ `Region of region ] }
and due_phi = { mutable phi : [ `Phi of phi ] option }

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

let add_data_suc1 suc : data_pred -> unit = function
  | `Const (_, ds) | `BinOp (_, _, _, ds) | `Phi (_, _, _, ds) ->
    ds.data_sucs <- suc :: ds.data_sucs
;;

type br =
  | Then
  | Else

let set_cfg_suc1 ?(br = Then) suc : cfg_pred -> unit = function
  | `ITE (_, _, c, _) when br = Then -> c.cfg_out <- suc
  | `Start (c, _) | `ITE (_, _, _, c) | `Region (_, _, _, c) -> c.cfg_out <- suc
;;

let find k = get >>| fst >>| SMap.find k
let add k v = get >>= fun (env, control) -> put (SMap.add k v env, control)
let add_data_suc suc = List.iter @@ add_data_suc1 suc
let set_cfg_suc ?(br = Then) suc = List.iter @@ set_cfg_suc1 suc ~br

(* todo tail-rec? *)
let from_anf vb =
  let c = { consts = [] } in
  let r = { returned = None } in
  let rec start_node = `Start ({ cfg_out = (fin_node :> cfg_suc) }, c)
  and fin_node = `Return (rci, r)
  and rci = { cfg_in = (start_node :> cfg_pred) } in
  let add_const n = c.consts <- n :: c.consts in
  match vb with
  | _, { hum_name = "main"; _ }, e ->
    let helper_a ~br = function
      | AConst c ->
        let c = `Const (c, { data_sucs = [] }) in
        add_const c;
        return c
      | AVar { hum_name = name; _ } -> find name
      | _ -> todo ()
    in
    let rec helper_c ~br = function
      | CApp (APrimitive op, a1, [ a2 ]) when is_infix_binop op ->
        let+ a1, a2 = both (helper_a ~br) a1 a2 in
        let bo = `BinOp (op, a1, a2, { data_sucs = [] }) in
        add_data_suc bo [ a1; a2 ];
        bo
      | CAtom i -> helper_a ~br i
      | CIte (cond, th, el) ->
        let* cond = helper_c ~br cond in
        let* env, control = get in
        let rec ite =
          let cfg_out = (region :> cfg_suc) in
          `ITE ({ cfg_in = control }, cond, { cfg_out }, { cfg_out })
        and region : [ `Region of region ] =
          `Region (th_cfg, el_cfg, ph, { cfg_out = (fin_node :> cfg_suc) })
        and th_cfg = { cfg_in = (ite :> cfg_pred) }
        and el_cfg = { cfg_in = (ite :> cfg_pred) }
        and ph = { phi = None } in
        let () = add_data_suc1 (ite :> data_suc) cond in
        let () = set_cfg_suc1 ~br (ite :> cfg_suc) control in
        let* () = put (env, ite) in
        let br_hndl br =
          let* data = helper ~br:(if br == th then Then else Else) br in
          let+ _, control = get in
          data, control
        in
        let* phi =
          return (fun (d1, c1) (d2, c2) ->
            let phi = `Phi (d1, d2, { region }, { data_sucs = [] }) in
            let () = set_cfg_suc ~br (region :> cfg_suc) [ c1; c2 ] in
            let () = add_data_suc (phi :> data_suc) [ d1; d2 ] in
            th_cfg.cfg_in <- c1;
            el_cfg.cfg_in <- c2;
            ph.phi <- Some phi;
            phi)
          <&> br_hndl th
          <&> br_hndl el
        in
        put (env, (region :> cfg_pred)) >>| fun () -> phi
      | _ -> todo ()
    and helper ?(br = Then) =
      let open Frontend.Typedtree in
      function
      | EComplex c -> helper_c ~br c
      | ELet (NonRecursive, Tpat_var { hum_name = name; _ }, c, e) ->
        let* () = helper_c ~br c >>= add name in
        helper e
      | _ -> todo ()
    in
    run (helper e) (SMap.empty, (start_node :> cfg_pred))
    |> fun ((_, control), returned) ->
    r.returned <- Some returned;
    add_data_suc1 (fin_node :> data_suc) returned;
    rci.cfg_in <- (control :> cfg_pred);
    (match start_node, fin_node with
     | `Start s, `Return f -> s, f)
  | _ -> todo ()
;;

open Compile_lib

let print_sceleton () =
  let seen = Hashtbl.create 58 in
  let open Format in
  let rec print_full ppf : node list -> unit = function
    | [] -> ()
    | n :: q ->
      let upd_queue =
        List.fold_left
          (fun q n -> if Hashtbl.mem seen @@ Hashtbl.hash n then q else n :: q)
          q
      in
      let ds =
        match n with
        | `Const (_, { data_sucs })
        | `BinOp (_, _, _, { data_sucs })
        | `Phi (_, _, _, { data_sucs }) -> List.map (fun c -> (c :> node)) data_sucs
        | `Start _ | `Return _ | `ITE _ | `Region _ -> []
      in
      let opt = function
        | Some x -> [ x ]
        | None -> []
      in
      let pp_print_list = pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") in
      Hashtbl.add seen (Hashtbl.hash n) ();
      print_full ppf
      @@
        (match n with
        | `Start ({ cfg_out }, { consts }) ->
          let c = (cfg_out :> node) in
          let cs = List.map (fun c -> (c :> node)) consts in
          fprintf ppf "Start (%a, [%a])\n" print_sh c (pp_print_list print_sh) cs;
          upd_queue (c :: cs)
        | `Const (data, _) ->
          fprintf
            ppf
            "Const (%a, [%a])\n"
            Frontend.Pprint.pp_const
            data
            (pp_print_list print_sh)
            ds;
          upd_queue ds
        | `BinOp (op, d1, d2, _) ->
          let d1 = (d1 :> node) in
          let d2 = (d2 :> node) in
          fprintf
            ppf
            "Binop (%s, *%a, *%a, [%a])\n"
            op
            print_sh
            d1
            print_sh
            d2
            (pp_print_list print_sh)
            ds;
          upd_queue (d1 :: d2 :: ds)
        | `Return ({ cfg_in }, { returned }) ->
          let c1 = (cfg_in :> node) in
          let returned = Option.map (fun r -> (r :> node)) returned in
          fprintf
            ppf
            "Return (*%a, *%a)\n"
            print_sh
            c1
            (pp_print_option print_sh)
            returned;
          upd_queue @@ List.cons c1 @@ opt returned
        | `ITE ({ cfg_in }, d, { cfg_out }, { cfg_out = cfg_out' }) ->
          let c1 = (cfg_in :> node) in
          let c2 = (cfg_out :> node) in
          let c3 = (cfg_out' :> node) in
          let d = (d :> node) in
          fprintf
            ppf
            "ITE (*%a, *%a, %a, %a)\n"
            print_sh
            c1
            print_sh
            d
            print_sh
            c2
            print_sh
            c3;
          upd_queue [ c1; d; c2; c3 ]
        | `Region ({ cfg_in }, { cfg_in = cfg_in' }, { phi }, { cfg_out }) ->
          let c1 = (cfg_in :> node) in
          let c2 = (cfg_in' :> node) in
          let c3 = (cfg_out :> node) in
          let phi = Option.map (fun r -> (r :> node)) phi in
          fprintf
            ppf
            "Region (*%a, *%a, %a, %a)\n"
            print_sh
            c1
            print_sh
            c2
            (pp_print_option print_sh)
            phi
            print_sh
            c3;
          upd_queue @@ List.append (opt phi) [ c1; c2; c3 ]
        | `Phi (d1, d2, { region }, _) ->
          let d1 = (d1 :> node) in
          let d2 = (d2 :> node) in
          let r = (region :> node) in
          fprintf
            ppf
            "Phi (*%a, *%a, *%a, [%a])\n"
            print_sh
            d1
            print_sh
            d2
            print_sh
            r
            (pp_print_list print_sh)
            ds;
          upd_queue (d1 :: d2 :: r :: ds))
  and print_sh ppf : node -> unit = function
    | `Start _ -> fprintf ppf "Start"
    | `Const (c, _) -> Frontend.Pprint.pp_const ppf c
    | `BinOp (op, _, _, _) -> fprintf ppf "%s" op
    | `Return _ -> fprintf ppf "Return"
    | `ITE _ -> fprintf ppf "ITE"
    | `Region _ -> fprintf ppf "Region"
    | `Phi _ -> fprintf ppf "Phi"
  in
  fun n -> print_full Format.std_formatter [ n ]
;;

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
         | `Region (c11, c12, p1, c13), `Region (c21, c22, p2, c23) ->
           (c11.cfg_in :> node) = (c21.cfg_in :> node)
           && (c12.cfg_in :> node) = (c22.cfg_in :> node)
           && (c13.cfg_out :> node) = (c23.cfg_out :> node)
           &&
             (match p1.phi, p2.phi with
             | None, None -> true
             | Some ph1, Some ph2 -> (ph1 :> node) = (ph2 :> node)
             | _ -> false)
         | `ITE (c11, d1, c12, c13), `ITE (c21, d2, c22, c23) ->
           (c11.cfg_in :> node) = (c21.cfg_in :> node)
           && (c12.cfg_out :> node) = (c22.cfg_out :> node)
           && (c13.cfg_out :> node) = (c23.cfg_out :> node)
           && (d1 :> node) = (d2 :> node)
         | `Phi (d11, d12, reg1, d1), `Phi (d21, d22, reg2, d2) ->
           (d11 :> node) = (d21 :> node)
           && (d12 :> node) = (d22 :> node)
           && ds d1 d2
           && (reg1.region :> node) = (reg2.region :> node)
         | (`Start _ | `Return _ | `Const _ | `BinOp _ | `Phi _ | `ITE _ | `Region _), _
           -> false
       with
       | r -> r
       | exception Invalid_argument _ -> false)
  in
  ( = )
;;

let from_string_vb ?(debug = false) text =
  let open Frontend in
  let open Result in
  let ( let* ) = bind in
  get_ok
  @@ let* _, ttree = Inferencer.vb @@ Parsing.parse_vb_exn text in
     ANF.anf_vb ttree
     |> from_anf
     |> fst
     |> fun st ->
     if debug then print_sceleton () @@ `Start st else ();
     ok st
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

let%test "if-then-else" =
  let rec start =
    ( { cfg_out = `ITE ite1 }
    , { consts = [ `Const one; `Const two; `Const zero; `Const fls; `Const tr ] } )
  and ite1 =
    ( { cfg_in = `Start start }
    , `Const tr
    , { cfg_out = `Region reg1 }
    , { cfg_out = `ITE ite2 } )
  and ite2 =
    ( { cfg_in = `ITE ite1 }
    , `Const fls
    , { cfg_out = `Region reg2 }
    , { cfg_out = `Region reg2 } )
  and reg2 =
    let phi = Some (`Phi phi2) in
    { cfg_in = `ITE ite2 }, { cfg_in = `ITE ite2 }, { phi }, { cfg_out = `Region reg1 }
  and reg1 =
    let phi = Some (`Phi phi1) in
    { cfg_in = `ITE ite1 }, { cfg_in = `Region reg2 }, { phi }, { cfg_out = `Return fin }
  and phi2 =
    `Const one, `Const two, { region = `Region reg2 }, { data_sucs = [ `Phi phi1 ] }
  and phi1 =
    `Const zero, `Phi phi2, { region = `Region reg1 }, { data_sucs = [ `Return fin ] }
  and fin = { cfg_in = `Region reg1 }, { returned = Some (`Phi phi1) }
  and tr = Frontend.Parsetree.const_bool true, { data_sucs = [ `ITE ite1 ] }
  and fls = Frontend.Parsetree.const_bool false, { data_sucs = [ `ITE ite2 ] }
  and zero = Frontend.Parsetree.const_int 0, { data_sucs = [ `Phi phi1 ] }
  and one = Frontend.Parsetree.const_int 1, { data_sucs = [ `Phi phi2 ] }
  and two = Frontend.Parsetree.const_int 2, { data_sucs = [ `Phi phi2 ] } in
  let ( = ) = equal () in
  `Start (from_string_vb "let main =  if true then 0 else if false then 1 else 2     ")
  = `Start start
;;
