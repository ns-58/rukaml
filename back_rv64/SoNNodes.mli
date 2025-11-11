type start = cfg_out * consts * [ `Function of fn ] list ref

and return =
  cfg_in * returned * [ `Function of fn ] ref * [ `CallEnd of call_end ] list ref

and const = Frontend.Parsetree.const * data_outs
and binop = string * data_in * data_in * data_outs
and ite = cfg_in * data_in * cfg_out * cfg_out
and region = cfg_pred list ref * [ `Phi of phi ] list ref * cfg_out
and phi = data_ins * [ `Region of region ] ref * data_outs
and stop = cfg_in * returned (* return for program. Not the same with original SoN stop*)
and fn = [ `Region of region ] * [ `Return of return ] * data_outs

and call =
  cfg_in
  * data_in
  * data_in
  * data_ins (* f, arg, arg list*)
  * [ `CallEnd of call_end ]
  * cfg_suc list ref

and call_end =
  [ `Call of call ] ref * [ `Return of return ] list ref * data_outs * cfg_out

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

and cfg_in = cfg_pred ref
and cfg_out = cfg_suc ref
and data_outs = data_suc list ref
and data_in = data_pred ref
and data_ins = data_pred list ref
and consts = [ `Const of const ] list ref
and returned = data_pred option ref

type node =
  [ data_pred
  | data_suc
  | cfg_pred
  | cfg_suc
  ]

(*todo: remove unused mutables*)
