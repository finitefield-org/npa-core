type reduction_result =
  | Reduced of Ext_term.t
  | Reduction_not_implemented

let whnf term = Reduced term
