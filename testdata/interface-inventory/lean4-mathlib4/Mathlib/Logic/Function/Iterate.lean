public import Mathlib.Logic.Function.Defs

namespace Function

theorem iterate_invariant : True := by
  have h := Function.comp_assoc
  rw [Function.comp_assoc]
  exact True.intro

end Function
