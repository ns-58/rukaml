let todo () = failwith "todo"

(*todo use refs instead of size one records*)

type start = cfg_out * consts * fns
and return = cfg_in * returned * fnc * call_ends
and const = Frontend.Parsetree.const * data_outs
and binop = string * data_in * data_in * data_outs
and ite = cfg_in * data_in * cfg_out * cfg_out
and region = cfg_ins * phis * cfg_out
and phi = data_ins * due_region * data_outs
and stop = cfg_in * returned (* return for program. Not the same with original SoN stop*)
and fn = region * return * data_outs

and call =
  cfg_in * data_in * data_in * data_ins (* f, arg, arg list*) * call_end * cfg_outs

and call_end = cl * rets * data_outs * cfg_out

and cfg_suc =
  [ `Return of return
  | `Stop of stop
  | `ITE of ite
  | `Region of region
  | `Call of call
  | `CallEnd of call_end
  ]

and cfg_pred =
  [ `Start of start
  | `ITE of ite
  | `Region of region
  | `Call of call
  | `CallEnd of call_end
  ]

and returned = { mutable returned : data_pred option }

and data_pred =
  [ `Const of const
  | `BinOp of binop
  | `Phi of phi
  | `CallEnd of call_end
  | `Function of fn
  ]

and data_suc =
  [ `Return of return
  | `Stop of stop
  | `BinOp of binop
  | `ITE of ite
  | `Phi of phi
  | `Call of call
  | `CallEnd of call_end
  ]

and cl = { mutable call : call }
and cfg_in = { mutable cfg_in : cfg_pred }
and cfg_ins = { mutable cfg_ins : cfg_pred list }
and cfg_out = { mutable cfg_out : cfg_suc }
and cfg_outs = { mutable cfg_outs : cfg_suc list }
and data_outs = { mutable data_outs : data_suc list }
and data_in = { mutable data_in : data_pred }
and data_ins = { mutable data_ins : data_pred list }
and consts = { mutable consts : [ `Const of const ] list }
and due_region = { mutable region : [ `Region of region ] }
and phis = { mutable phis : [ `Phi of phi ] list }
and fns = { mutable fns : [ `Function of fn ] list }
and fnc = { mutable fnc : fn }
and call_ends = { mutable call_ends : [ `CallEnd of call_end ] list }
and rets = { mutable rets : [ `Return of return ] list }

type node =
  [ data_pred
  | data_suc
  | cfg_pred
  | cfg_suc
  ]
(*todo: remove unused mutables*)

open Compile_lib.ANF
open Frontend.Ident

(*todo: use IMap?*)
module SMap = Map.Make (String)
open Monads.Store

let ( >>| ) f x = f >>= fun t -> return @@ x t
let ( let+ ) = ( >>| )

(*todo: remove*)

let add_data_suc1 suc : data_pred -> unit = function
  | `Const (_, ds)
  | `BinOp (_, _, _, ds)
  | `Phi (_, _, ds)
  | `Function (_, _, ds)
  | `CallEnd (_, _, ds, _) -> ds.data_outs <- suc :: ds.data_outs
;;

type br =
  | Then
  | Else

let set_cfg_suc1 ?(br = Then) suc : cfg_pred -> unit = function
  | `ITE (_, _, c, _) when br = Then -> c.cfg_out <- suc
  | `Start (c, _, _) | `ITE (_, _, _, c) | `Region (_, _, c) | `CallEnd (_, _, _, c) ->
    c.cfg_out <- suc
  | `Call (_, _, _, _, _, cc) -> cc.cfg_outs <- suc :: cc.cfg_outs
;;

let env = get >>| fst
let add k v = get >>= fun (env, control) -> put (SMap.add k v env, control)
let add_data_suc suc = List.iter @@ add_data_suc1 suc
let set_cfg_suc ?(br = Then) suc = List.iter @@ set_cfg_suc1 suc ~br

(* todo tail-rec? *)
let from_anf vbs =
  let c = { consts = [] } in
  let r = { returned = None } in
  let fns = { fns = [] } in
  let rec start_node = `Start ({ cfg_out = (fin_node :> cfg_suc) }, c, fns)
  and fin_node = `Stop (ret_cfg_in, r)
  and ret_cfg_in = { cfg_in = (start_node :> cfg_pred) } in
  let add_const n = c.consts <- n :: c.consts in
  let vb local_fin_node =
    let helper_a a env =
      match a with
      | AConst c ->
        let c = `Const (c, { data_outs = [] }) in
        add_const c;
        c
      | AVar { hum_name = name; _ } -> SMap.find name env
      | _ -> todo ()
    in
    let rec helper_c ~br = function
      | CApp (APrimitive op, a1, [ a2 ]) when is_infix_binop op ->
        let+ env = env in
        let a1, a2 = helper_a a1 env, helper_a a2 env in
        let bo = `BinOp (op, { data_in = a1 }, { data_in = a2 }, { data_outs = [] }) in
        add_data_suc bo [ a1; a2 ];
        bo
      | CApp (f, arg, args) ->
        let* env, control = get in
        let helper_a a = helper_a a env in
        (match helper_a f with
         | `Function ((((cfg_ins, phis, _) : region) as region), (_, _, _, call_ends), _)
           as fn ->
           let arg = helper_a arg in
           let args = List.map helper_a args in
           let cos = { cfg_outs = [ (`Region region :> cfg_suc) ] } in
           let co = { cfg_out = local_fin_node } in
           let d = { data_outs = [] } in
           let rec call =
             ( { cfg_in = control }
             , { data_in = fn }
             , { data_in = arg }
             , { data_ins = args }
             , call_end
             , cos )
           and call_end = { call }, rs, d, co
           and rs = { rets = [] } in
           let call_end = `CallEnd call_end in
           let call = `Call call in
           set_cfg_suc1 ~br call control;
           cfg_ins.cfg_ins <- call :: cfg_ins.cfg_ins;
           List.iter2
             (fun (`Phi (di, _, _) as phi) arg ->
                add_data_suc1 phi arg;
                di.data_ins <- arg :: di.data_ins)
             phis.phis
             (arg :: args);
           call_ends.call_ends <- call_end :: call_ends.call_ends;
           add_data_suc1 call fn;
           let+ () = put (env, call_end) in
           call_end
         | _ -> todo ())
      | CAtom i -> env >>| helper_a i
      | CIte (cond, th, el) ->
        let* cond = helper_c ~br cond in
        let* env, control = get in
        let rec ite =
          let cfg_out = (region :> cfg_suc) in
          `ITE ({ cfg_in = control }, { data_in = cond }, { cfg_out }, { cfg_out })
        and region : [ `Region of region ] = `Region (cf, ph, { cfg_out = local_fin_node })
        and cf = { cfg_ins = [ (ite :> cfg_pred); (ite :> cfg_pred) ] }
        and ph = { phis = [] } in
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
            let phi = `Phi ({ data_ins = [ d1; d2 ] }, { region }, { data_outs = [] }) in
            let () = set_cfg_suc ~br (region :> cfg_suc) [ c1; c2 ] in
            let () = add_data_suc (phi :> data_suc) [ d1; d2 ] in
            cf.cfg_ins <- [ c1; c2 ];
            ph.phis <- [ phi ];
            phi)
          <&> br_hndl th
          <&> br_hndl el
        in
        put (env, (region :> cfg_pred)) >>| fun () -> phi
    and helper ?(br = Then) =
      let open Frontend.Typedtree in
      function
      | EComplex c -> helper_c ~br c
      | ELet (NonRecursive, Tpat_var { hum_name = name; _ }, c, e) ->
        let* () = helper_c ~br c >>= add name in
        helper e
      | _ -> todo ()
    in
    helper
  in
  (* todo error handling *)
  let open Base.List in
  Base.List.fold_until
    vbs
    ~init:SMap.empty
    ~finish:(failwith "have no main")
    ~f:(fun globals (_, { hum_name; _ }, e) ->
      match hum_name, Compile_lib.ANF.group_abstractions e with
      | "main", ([], e) ->
        let (_, control), returned =
          run (vb fin_node e) (globals, (start_node :> cfg_pred))
        in
        r.returned <- Some returned;
        ret_cfg_in.cfg_in <- (control :> cfg_pred);
        (match start_node, fin_node with
         | `Start s, `Stop f -> Stop (s, f))
      | name, (arg :: args, b) ->
        let cfg_ins, phis, data_ins, data_outs, call_ends = [], [], [], [], [] in
        let rec reg = { cfg_ins }, ph, { cfg_out = return }
        and ret = ret_cfg_in, rd, { fnc = fn }, { call_ends }
        and fn = reg, ret, { data_outs }
        and region = `Region reg
        and return = `Return ret
        and ph = { phis }
        and rd = { returned = None } in
        let env, phis' =
          fold_map (arg :: args) ~init:globals ~f:(fun env (APname { hum_name; _ }) ->
            let ph = `Phi ({ data_ins }, { region }, { data_outs = [] }) in
            SMap.add hum_name (ph :> data_pred) env, ph)
        in
        ph.phis <- phis';
        let (_, control), returned = run (vb return b) (env, (region :> cfg_pred)) in
        rd.returned <- Some returned;
        ret_cfg_in.cfg_in <- (control :> cfg_pred);
        let f = `Function fn in
        fns.fns <- f :: fns.fns;
        Continue (SMap.add name (f :> data_pred) globals)
      | _ -> todo ())
;;

(*
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
        | `Const (_, { data_outs })
        | `BinOp (_, _, _, { data_outs })
        | `Phi (_, _, { data_outs }) -> (data_outs :> node list)
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
          let cs = (consts :> node list) in
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
        | `BinOp (op, { data_in }, { data_in = data_in' }, _) ->
          let d1 = (data_in :> node) in
          let d2 = (data_in' :> node) in
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
          let returned = (Option.map (fun r -> (r :> node))) returned in
          fprintf
            ppf
            "Return (*%a, *%a)\n"
            print_sh
            c1
            (pp_print_option print_sh)
            returned;
          upd_queue @@ List.cons c1 @@ opt returned
        | `ITE ({ cfg_in }, { data_in }, { cfg_out }, { cfg_out = cfg_out' }) ->
          let c1 = (cfg_in :> node) in
          let c2 = (cfg_out :> node) in
          let c3 = (cfg_out' :> node) in
          let d = (data_in :> node) in
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
        | `Region ({ cfg_ins }, { phis }, { cfg_out }) ->
          let cf = (cfg_ins :> node list) in
          let co = (cfg_out :> node) in
          let phis = (phis :> node list) in
          fprintf
            ppf
            "Region (*[%a], [%a], %a)\n"
            (pp_print_list print_sh)
            cf
            (pp_print_list print_sh)
            phis
            print_sh
            co;
          upd_queue @@ (co :: cf) @ phis
        | `Phi ({ data_ins }, { region }, _) ->
          let dis = (data_ins :> node list) in
          let r = (region :> node) in
          fprintf
            ppf
            "Phi (*[%a],  *%a, [%a])\n"
            (pp_print_list print_sh)
            dis
            print_sh
            r
            (pp_print_list print_sh)
            ds;
          upd_queue @@ (r :: ds) @ dis)
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

(* could be false-positive rarely I guess*)
let equal () =
  let seen = Hashtbl.create 58 in
  let rec ( = ) x y =
    let lists2 = List.fold_left2 (fun acc x y -> acc && x = y) true in
    let ds d1 d2 = lists2 (d1.data_outs :> node list) (d2.data_outs :> node list) in
    let hashed_xy = Hashtbl.hash (x, y) in
    match Hashtbl.find seen hashed_xy with
    | () -> true
    | exception Not_found ->
      Hashtbl.add seen hashed_xy ();
      (match
         match x, y with
         | `Start (c1, { consts = con1 }), `Start (c2, { consts = con2 }) ->
           lists2 (con1 :> node list) (con2 :> node list)
           && (c1.cfg_out :> node) = (c2.cfg_out :> node)
         | `Return (c1, { returned = None }), `Return (c2, { returned = None }) ->
           (c1.cfg_in :> node) = (c2.cfg_in :> node)
         | `Return (c1, { returned = Some r1 }), `Return (c2, { returned = Some r2 }) ->
           (c1.cfg_in :> node) = (c2.cfg_in :> node) && (r1 :> node) = (r2 :> node)
         | `Const (data1, d1), `Const (data2, d2) -> Stdlib.( = ) data1 data2 && ds d1 d2
         | `BinOp (op1, a11, a12, d1), `BinOp (op2, a21, a22, d2) ->
           Stdlib.( = ) op1 op2
           && (a11.data_in :> node) = (a21.data_in :> node)
           && (a12.data_in :> node) = (a22.data_in :> node)
           && ds d1 d2
         | `Region (cc1, p1, co1), `Region (cc2, p2, co2) ->
           lists2 (cc1.cfg_ins :> node list) (cc2.cfg_ins :> node list)
           && (co1.cfg_out :> node) = (co2.cfg_out :> node)
           && lists2 (p1.phis :> node list) (p2.phis :> node list)
         | `ITE (c11, d1, c12, c13), `ITE (c21, d2, c22, c23) ->
           (c11.cfg_in :> node) = (c21.cfg_in :> node)
           && (c12.cfg_out :> node) = (c22.cfg_out :> node)
           && (c13.cfg_out :> node) = (c23.cfg_out :> node)
           && (d1.data_in :> node) = (d2.data_in :> node)
         | `Phi (dis1, reg1, d1), `Phi (dis2, reg2, d2) ->
           lists2 (dis1.data_ins :> node list) (dis2.data_ins :> node list)
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
  and zero = Frontend.Parsetree.const_int 0, { data_outs = [ `Return fin ] } in
  let ( = ) = equal () in
  `Start (from_string_vb "let main = 0") = `Start start
;;

let%test "binops" =
  let rec start =
    { cfg_out = `Return fin }, { consts = [ `Const one; `Const three; `Const two ] }
  and fin = { cfg_in = `Start start }, { returned = Some (`BinOp sub2) }
  and sub1 =
    ( "-"
    , { data_in = `Const two }
    , { data_in = `Const three }
    , { data_outs = [ `BinOp sub2 ] } )
  and sub2 =
    ( "-"
    , { data_in = `Const one }
    , { data_in = `BinOp sub1 }
    , { data_outs = [ `Return fin ] } )
  and one = Frontend.Parsetree.const_int 1, { data_outs = [ `BinOp sub2 ] }
  and two = Frontend.Parsetree.const_int 2, { data_outs = [ `BinOp sub1 ] }
  and three = Frontend.Parsetree.const_int 3, { data_outs = [ `BinOp sub1 ] } in
  let ( = ) = equal () in
  `Start (from_string_vb "let main = 1 - (2 - 3) ") = `Start start
;;

let%test "if-then-else" =
  let rec start =
    ( { cfg_out = `ITE ite1 }
    , { consts = [ `Const one; `Const two; `Const zero; `Const fls; `Const tr ] } )
  and ite1 =
    ( { cfg_in = `Start start }
    , { data_in = `Const tr }
    , { cfg_out = `Region reg1 }
    , { cfg_out = `ITE ite2 } )
  and ite2 =
    ( { cfg_in = `ITE ite1 }
    , { data_in = `Const fls }
    , { cfg_out = `Region reg2 }
    , { cfg_out = `Region reg2 } )
  and reg2 =
    let phis = [ `Phi phi2 ] in
    { cfg_ins = [ `ITE ite2; `ITE ite2 ] }, { phis }, { cfg_out = `Region reg1 }
  and reg1 =
    let phis = [ `Phi phi1 ] in
    { cfg_ins = [ `ITE ite1; `Region reg2 ] }, { phis }, { cfg_out = `Return fin }
  and phi2 =
    ( { data_ins = [ `Const one; `Const two ] }
    , { region = `Region reg2 }
    , { data_outs = [ `Phi phi1 ] } )
  and phi1 =
    ( { data_ins = [ `Const zero; `Phi phi2 ] }
    , { region = `Region reg1 }
    , { data_outs = [ `Return fin ] } )
  and fin = { cfg_in = `Region reg1 }, { returned = Some (`Phi phi1) }
  and tr = Frontend.Parsetree.const_bool true, { data_outs = [ `ITE ite1 ] }
  and fls = Frontend.Parsetree.const_bool false, { data_outs = [ `ITE ite2 ] }
  and zero = Frontend.Parsetree.const_int 0, { data_outs = [ `Phi phi1 ] }
  and one = Frontend.Parsetree.const_int 1, { data_outs = [ `Phi phi2 ] }
  and two = Frontend.Parsetree.const_int 2, { data_outs = [ `Phi phi2 ] } in
  let ( = ) = equal () in
  `Start (from_string_vb "let main =  if true then 0 else if false then 1 else 2     ")
  = `Start start
;; *)
