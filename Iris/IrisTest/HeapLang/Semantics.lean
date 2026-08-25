module

public import Iris.HeapLang.Instances

@[expose] public section
namespace IrisTest.HeapLang.Semantics

open Iris.HeapLang

example (b : Bool) : UnOp.eval .neg (.lit (.bool b)) = some (.lit (.bool (!b))) := by rfl
example (n : Int) : UnOp.eval .neg (.lit (.int n)) = some (.lit (.int (~~~n))) := by rfl

example : BinOp.eval .plus (.lit (.int 2)) (.lit (.int 3)) = some (.lit (.int 5)) := by decide
example : BinOp.eval .xor (.lit (.bool true)) (.lit (.bool false)) =
    some (.lit (.bool true)) := by decide
example : BinOp.eval .le (.lit (.loc ⟨2⟩)) (.lit (.loc ⟨3⟩)) =
    some (.lit (.bool true)) := by decide
example : BinOp.eval .lt (.lit (.loc ⟨3⟩)) (.lit (.loc ⟨3⟩)) =
    some (.lit (.bool false)) := by decide
example : BinOp.eval .offset (.lit (.loc ⟨2⟩)) (.lit (.int 3)) =
    some (.lit (.loc ⟨5⟩)) := by decide
example : BinOp.eval .eq (.lit (.int 2)) (.lit (.int 2)) =
    some (.lit (.bool true)) := by decide
example : BinOp.eval .eq (.pair (.lit .unit) (.lit .unit))
    (.pair (.lit .unit) (.lit .unit)) = none := by decide

end IrisTest.HeapLang.Semantics
