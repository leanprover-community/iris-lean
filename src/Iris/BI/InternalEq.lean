import Iris.BI.BI

namespace Iris.BI

class InternalEq (PROP : Type _) [BI PROP] (α : Type _) where
  internalEq : α → α → PROP

export InternalEq (internalEq)

infix:50 " ≡ " => internalEq

end Iris.BI
