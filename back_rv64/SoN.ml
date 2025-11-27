let todo () = failwith "todo"

open Compile_lib.ANF
open Frontend.Ident
open SoNNodes

(*todo: use IMap?*)
module SMap = Map.Make (String)
module IMap = Map.Make (Int)
open Monads.Store

let ( >>| ) f x = f >>= fun t -> return @@ x t
let ( let+ ) = ( >>| )

let add_data_suc1 suc (n : data_pred) =
  match n with
  | `Const (_, (_, ds))
  | `BinOp (_, (_, _, _, _, ds))
  | `Phi (_, (_, _, ds))
  | `Function (_, (_, _, ds))
  | `CallEnd (_, (_, _, ds, _)) -> ds := suc :: !ds
;;

let set_cfg_suc1 suc (n : cfg_pred) =
  match n with
  | `Start (_, (_, c, _, _))
  | `Region (_, (_, _, _, c))
  | `CallEnd (_, (_, _, _, c))
  | `ITEProj (_, (_, c, _)) -> c := suc
  | `Call (_, (_, _, _, _, _, cc)) -> cc := suc :: !cc
;;

let env = get >>| fst
let add k v = get >>= fun (env, control) -> put (SMap.add k v env, control)
let add_data_suc suc = List.iter @@ add_data_suc1 suc
let set_cfg_suc suc = List.iter @@ set_cfg_suc1 suc

(* todo tail-rec? *)
let from_anf vbs =
  let consts = ref [] in
  let retd = ref None in
  let functions = ref [] in
  let rec start_node =
    `Start (gensym (), (ref [], ref (fin_node :> cfg_suc), consts, functions))
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
    let rec helper_c = function
      | CApp (APrimitive op, a1, [ a2 ]) when is_infix_binop op ->
        let+ env = env in
        let a1, a2 = helper_a a1 env, helper_a a2 env in
        let bo = `BinOp (gensym (), (ref None, op, ref a1, ref a2, ref [])) in
        add_data_suc bo [ a1; a2 ];
        bo
      | CApp (f, arg, args) ->
        let* env, control = get in
        let helper_a a = helper_a a env in
        (match helper_a f with
         | `Function
             ( _
             , ( (`Region (_, (_, cfg_ins, phis, _)) as region)
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
           set_cfg_suc1 (call :> cfg_suc) control;
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
        let* cond = helper_c cond in
        let* env, control = get in
        let rec ite = `ITE (gensym (), (ref control, ref cond, th_proj, el_proj))
        and region = `Region (gensym (), (ref [], cfg_ins, phis, ref local_fin_node))
        and cfg_ins = ref []
        and phis = ref []
        and th_proj = `ITEProj (gensym (), (ite, ref (region :> cfg_suc), ref []))
        and el_proj = `ITEProj (gensym (), (ite, ref (region :> cfg_suc), ref [])) in
        let () = add_data_suc1 (ite :> data_suc) cond in
        let () = set_cfg_suc1 (ite :> cfg_suc) control in
        let br_hndl (proj : [ `ITEProj of id * ite_proj ]) ebr =
          let* () = put (env, (proj :> cfg_pred)) in
          let* data = helper ebr in
          let+ _, control = get in
          data, control
        in
        let* phi =
          return (fun (d1, c1) (d2, c2) ->
            let phi = `Phi (gensym (), (ref [ d1; d2 ], ref region, ref [])) in
            let () = set_cfg_suc (region :> cfg_suc) [ c1; c2 ] in
            let () = add_data_suc (phi :> data_suc) [ d1; d2 ] in
            cfg_ins := [ c1; c2 ];
            phis := [ phi ];
            phi)
          <&> br_hndl th_proj th
          <&> br_hndl el_proj el
        in
        put (env, (region :> cfg_pred)) >>| fun () -> phi
    and helper =
      let open Frontend.Typedtree in
      function
      | EComplex c -> helper_c c
      | ELet (NonRecursive, Tpat_var { hum_name = name; _ }, c, e) ->
        let* () = helper_c c >>= add name in
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
        let rec region = `Region (gensym (), (ref [], ref [], phis, ref (ret :> cfg_suc)))
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

let get_cfg_preds (n : cfg_suc) =
  match n with
  | `Call (_, (cfg_in, _, _, _, _, _))
  | `ITE (_, (cfg_in, _, _, _))
  | `Stop (_, (cfg_in, _))
  | `Return (_, (cfg_in, _, _, _)) -> [ !cfg_in ]
  | `CallEnd (_, (c, _, _, _)) -> [ (!c :> cfg_pred) ]
  | `Region (_, (_, cfg_ins, _, _)) -> !cfg_ins
;;

module Env : sig
  type t

  val find : t -> cfg_pred -> int * sched_m
  (* depth and due basic block begining node*)

  val empty : t
  val add_self : t -> int -> sched_m -> t
  val add : t -> [ `CallEnd of id * call_end | `Call of id * call ] -> int * sched_m -> t
end = struct
  type t = int IMap.t * (int * sched_m) IMap.t

  let empty = IMap.empty, IMap.empty

  let id : sched_m -> id = function
    | `Start (id, _) | `ITEProj (id, _) | `Region (id, _) -> id
  ;;

  let find (sched_env, cfg_env) = function
    | #sched_m as s -> IMap.find (id s) sched_env, s
    | `CallEnd (id, _) | `Call (id, _) -> IMap.find id cfg_env
  ;;

  let add_self (sched_env, cfg_env) depth sched_m =
    IMap.add (id sched_m) depth sched_env, cfg_env
  ;;

  let add (sched_env, cfg_env) (`CallEnd (id, _) | `Call (id, _)) (depth, sched_m) =
    sched_env, IMap.add id (depth, sched_m) cfg_env
  ;;
end

let sched_early
      (`Start (_, (_, _, _, { contents = funcs })) as start)
      (`Stop (_, returned))
  =
  let set (sl : sched_sl) (m : sched_m) =
    match sl, m with
    | ( `BinOp (_, (sched_m, _, _, _, _))
      , ( `Start (_, (sched_sls, _, _, _))
        | `ITEProj (_, (_, _, sched_sls))
        | `Region (_, (sched_sls, _, _, _)) ) ) ->
      sched_m := Some m;
      sched_sls := sl :: !sched_sls
  in
  let minim = 0, start in
  let min x1 x2 = if snd x1 > snd x2 then x1 else x2 in
  let rec helper env loc_deepest wt =
    let upd_deepest = min loc_deepest in
    match wt with
    | [] -> ()
    | ((sched_sl, deepest), []) :: tl ->
      let deepest' = upd_deepest deepest in
      set sched_sl @@ snd deepest';
      helper env deepest' tl
    | (((sched_sl, deepest) as sd), hd :: itl) :: tl ->
      let continue m = helper env (upd_deepest m) ((sd, itl) :: tl) in
      let tl' () = ((sched_sl, upd_deepest deepest), itl) :: tl in
      process_node tl' env continue hd
  and process_node tl' env continue (n : data_pred) =
    match n with
    | `Const _ -> continue minim
    | `BinOp (_, ({ contents = None }, _, { contents = a1 }, { contents = a2 }, _)) as bo
      -> helper env minim ((((bo :> sched_sl), minim), [ a1; a2 ]) :: tl' ())
    | `BinOp (_, ({ contents = Some m }, _, _, _, _)) ->
      helper_cfg continue env (m :> cfg_pred)
    | `Function _ -> failwith "shouldn't happen for now"
    | `Phi (_, (_, { contents = reg }, _)) ->
      let cfg = (reg :> cfg_pred) in
      helper_cfg continue env cfg
    | `CallEnd _ as cfg -> helper_cfg continue env (cfg :> cfg_pred)
  and helper_cfg k =
    let rec aux loc_deepest wt env =
      let upd_deepest = min loc_deepest in
      match wt with
      | [] -> k loc_deepest
      | (((#sched_m as m), (depth, _)), []) :: tl ->
        let depth' = depth + 1 in
        aux (depth', m) tl @@ Env.add_self env (depth + 1) m
      | ((((`Call _ | `CallEnd _) as c), deepest), []) :: tl ->
        let deepest' = upd_deepest deepest in
        aux deepest' tl @@ Env.add env c deepest'
      | (((sched_sl, deepest) as sd), hd :: itl) :: tl ->
        let continue m = aux (upd_deepest m) ((sd, itl) :: tl) env in
        let tl' () = ((sched_sl, upd_deepest deepest), itl) :: tl in
        process_node tl' continue env hd
    and process_node tl' continue env (n : cfg_pred) =
      let find preds =
        match Env.find env n with
        | m -> continue m
        | exception Not_found ->
          let wt' = ((n, minim), preds) :: tl' () in
          aux minim wt' env
      in
      match n with
      | `Start _ -> continue minim
      | `Call (_, (cin, _, _, _, _, _)) | `ITEProj (_, (`ITE (_, (cin, _, _, _)), _, _))
        -> find [ !cin ]
      | `Region (_, (_, { contents = cfg_preds }, _, _)) -> find cfg_preds
      | `CallEnd (_, ({ contents = call }, _, _, _)) -> find [ (call :> cfg_pred) ]
    in
    process_node (Fun.const []) k
  in
  List.iter (function
    | { contents = Some v } -> process_node (Fun.const []) Env.empty ignore v
    | { contents = None } -> failwith "unreachable" (*todo: avoiding that on type level*))
  @@ List.cons returned
  @@ List.map
       (function
         | `Function (_, (_, `Return (_, (_, returned, _, _)), _)) -> returned)
       funcs
;;
