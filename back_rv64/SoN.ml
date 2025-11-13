let todo () = failwith "todo"

open Compile_lib.ANF
open Frontend.Ident
open SoNNodes

(*todo: use IMap?*)
module SMap = Map.Make (String)
open Monads.Store

let ( >>| ) f x = f >>= fun t -> return @@ x t
let ( let+ ) = ( >>| )

let add_data_suc1 suc : data_pred -> unit = function
  | `Const (_, (_, ds))
  | `BinOp (_, (_, _, _, ds))
  | `Phi (_, (_, _, ds))
  | `Function (_, (_, _, ds))
  | `CallEnd (_, (_, _, ds, _)) -> ds := suc :: !ds
;;

type br =
  | Then
  | Else

let set_cfg_suc1 ?(br = Then) suc : cfg_pred -> unit = function
  | `ITE (_, (_, _, c, _)) when br = Then -> c := suc
  | `Start (_, (c, _, _))
  | `ITE (_, (_, _, _, c))
  | `Region (_, (_, _, c))
  | `CallEnd (_, (_, _, _, c)) -> c := suc
  | `Call (_, (_, _, _, _, _, cc)) -> cc := suc :: !cc
;;

let env = get >>| fst
let add k v = get >>= fun (env, control) -> put (SMap.add k v env, control)
let add_data_suc suc = List.iter @@ add_data_suc1 suc
let set_cfg_suc ?(br = Then) suc = List.iter @@ set_cfg_suc1 suc ~br

(* todo tail-rec? *)
let from_anf vbs =
  let consts = ref [] in
  let retd = ref None in
  let functions = ref [] in
  let rec start_node = `Start (gensym (), (ref (fin_node :> cfg_suc), consts, functions))
  and fin_node = `Stop (gensym (), (ret_cfg_in, retd))
  and ret_cfg_in = ref (start_node :> cfg_pred) in
  let add_const n = consts := n :: !consts in
  let vb local_fin_node =
    let helper_a a env =
      match a with
      | AConst c ->
        let c = `Const (gensym (), (c, ref [])) in
        add_const c;
        c
      | AVar { hum_name = name; _ } -> SMap.find name env
      | _ -> todo ()
    in
    let rec helper_c ~br = function
      | CApp (APrimitive op, a1, [ a2 ]) when is_infix_binop op ->
        let+ env = env in
        let a1, a2 = helper_a a1 env, helper_a a2 env in
        let bo = `BinOp (gensym (), (op, ref a1, ref a2, ref [])) in
        add_data_suc bo [ a1; a2 ];
        bo
      | CApp (f, arg, args) ->
        let* env, control = get in
        let helper_a a = helper_a a env in
        (match helper_a f with
         | `Function
             ( _
             , ( (`Region (_, (cfg_ins, phis, _)) as region)
               , (`Return (_, (_, _, _, call_ends)) as ret)
               , _ ) ) as fn ->
           let arg = helper_a arg in
           let args = List.map helper_a args in
           let rec call =
             `Call
               ( gensym ()
               , ( ref control
                 , ref fn
                 , ref arg
                 , ref args
                 , call_end
                 , ref [ (region :> cfg_suc) ] ) )
           and call_end =
             `CallEnd (gensym (), (ref call, ref [ ret ], ref [], ref local_fin_node))
           in
           set_cfg_suc1 ~br (call :> cfg_suc) control;
           cfg_ins := (call :> cfg_pred) :: !cfg_ins;
           List.iter2
             (fun (`Phi (_, (data_ins, _, _)) as phi) arg ->
                add_data_suc1 phi arg;
                data_ins := arg :: !data_ins)
             !phis
             (arg :: args);
           call_ends := call_end :: !call_ends;
           add_data_suc1 (call :> data_suc) fn;
           let+ () = put (env, (call_end :> cfg_pred)) in
           (call_end :> data_pred)
         | _ -> todo ())
      | CAtom i -> env >>| helper_a i
      | CIte (cond, th, el) ->
        let* cond = helper_c ~br cond in
        let* env, control = get in
        let rec ite =
          let cfg_out = (region :> cfg_suc) in
          `ITE (gensym (), (ref control, ref cond, ref cfg_out, ref cfg_out))
        and region = `Region (gensym (), (cfg_ins, phis, ref local_fin_node))
        and cfg_ins = ref [ (ite :> cfg_pred); (ite :> cfg_pred) ]
        and phis = ref [] in
        let () = add_data_suc1 (ite :> data_suc) cond in
        let () = set_cfg_suc1 ~br (ite :> cfg_suc) control in
        let* () = put (env, ite) in
        let br_hndl br =
          let* data = helper ~br:(if br = th then Then else Else) br in
          let+ _, control = get in
          data, control
        in
        let* phi =
          return (fun (d1, c1) (d2, c2) ->
            let phi = `Phi (gensym (), (ref [ d1; d2 ], ref region, ref [])) in
            let () = set_cfg_suc ~br (region :> cfg_suc) [ c1; c2 ] in
            let () = add_data_suc (phi :> data_suc) [ d1; d2 ] in
            cfg_ins := [ c1; c2 ];
            phis := [ phi ];
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
    ~f:(fun globals (fl, { hum_name; _ }, e) ->
      match hum_name, Compile_lib.ANF.group_abstractions e with
      | "main", ([], e) ->
        let (_, control), returned =
          run (vb fin_node e) (globals, (start_node :> cfg_pred))
        in
        retd := Some returned;
        ret_cfg_in := (control :> cfg_pred);
        (match start_node, fin_node with
         | `Start (_, s), `Stop (_, f) -> Stop (s, f))
      | name, (arg :: args, b) ->
        let rec region = `Region (gensym (), (ref [], phis, ref (ret :> cfg_suc)))
        and ret = `Return (gensym (), (ret_cfg_in, retd, ref fn, ref []))
        and fn = `Function (gensym (), (region, ret, ref []))
        and phis = ref []
        and retd = ref None in
        let init =
          match fl with
          | Frontend.Parsetree.NonRecursive -> globals
          | Frontend.Parsetree.Recursive -> SMap.add name (fn :> data_pred) globals
        in
        let env, phis' =
          fold_map (arg :: args) ~init ~f:(fun env (APname { hum_name; _ }) ->
            let ph = `Phi (gensym (), (ref [], ref region, ref [])) in
            SMap.add hum_name (ph :> data_pred) env, ph)
        in
        phis := phis';
        let (_, control), returned =
          run (vb (ret :> cfg_suc) b) (env, (region :> cfg_pred))
        in
        retd := Some returned;
        ret_cfg_in := (control :> cfg_pred);
        functions := fn :: !functions;
        Continue (SMap.add name (fn :> data_pred) globals)
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
