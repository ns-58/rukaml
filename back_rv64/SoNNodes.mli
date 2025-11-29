type id = int

(*todo: remove unused mutables*)

(*nodes starting basic blocks*)
type sched_m =
  [ `Start of id * start
  | `ITEProj of id * ite_proj
  | `Region of id * region
  ]

(*floating node*)
and sched_sl = [ `BinOp of id * binop ]
and start = sched_sl list ref * cfg_out * consts * [ `Function of id * fn ] list ref
and ite = cfg_in * data_in * [ `ITEProj of id * ite_proj ] * [ `ITEProj of id * ite_proj ]
and ite_proj = [ `ITE of id * ite ] * cfg_out * sched_sl list ref
and binop = sched_m option ref * string * data_in * data_in * data_outs

and region =
  sched_sl list ref * cfg_pred list ref * [ `Phi of id * phi ] list ref * cfg_out

and phi = data_ins * [ `Region of id * region ] ref * data_outs
and stop = cfg_in * returned (* return for program. Not the same with original SoN stop*)
and const = Frontend.Parsetree.const * data_outs

and return =
  cfg_in
  * returned
  * [ `Function of id * fn ] ref
  * [ `CallEnd of id * call_end ] list ref

and fn = [ `Region of id * region ] * [ `Return of id * return ] * data_outs

and call =
  cfg_in
  * data_in
  * data_in
  * data_ins (* f, arg, arg list*)
  * [ `CallEnd of id * call_end ]
  * cfg_suc list ref

and call_end =
  [ `Call of id * call ] ref * [ `Return of id * return ] list ref * data_outs * cfg_out

and cfg_suc =
  [ `Return of id * return
  | `Stop of id * stop
  | `ITE of id * ite
  | `Region of id * region
  | `Call of id * call
  | `CallEnd of id * call_end
  ]

and cfg_pred =
  [ `Start of id * start
  | `ITEProj of id * ite_proj
  | `Region of id * region
  | `Call of id * call
  | `CallEnd of id * call_end
  ]

and data_pred =
  [ `Const of id * const
  | `BinOp of id * binop
  | `Phi of id * phi
  | `CallEnd of id * call_end
  | `Function of id * fn
  ]

and data_suc =
  [ `Return of id * return
  | `Stop of id * stop
  | `BinOp of id * binop
  | `ITE of id * ite
  | `Phi of id * phi
  | `Call of id * call
  | `CallEnd of id * call_end
  ]

and cfg_in = cfg_pred ref
and cfg_out = cfg_suc ref
and data_outs = data_suc list ref
and data_in = data_pred ref
and data_ins = data_pred list ref
and consts = [ `Const of id * const ] list ref
and returned = data_pred option ref

type node =
  [ data_pred
  | data_suc
  | cfg_pred
  | cfg_suc
  ]
