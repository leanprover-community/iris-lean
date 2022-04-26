import Iris.BI
import Iris.Proofmode.Classes

namespace Iris.Proofmode
open Iris.BI

variable [bi : BI PROP]

-- AsEmpValid
instance as_emp_valid_emp_valid (P : PROP) : AsEmpValid (⊢ P) P where
  bi := bi
  as_emp_valid := sorry
instance as_emp_valid_entails (P Q : PROP) : AsEmpValid (P ⊢ Q) `[iprop| P -∗ Q] where
  bi := bi
  as_emp_valid := sorry
instance as_emp_valid_equiv (P Q : PROP) : AsEmpValid (P ≡ Q) `[iprop| P ∗-∗ Q] where
  bi := bi
  as_emp_valid := sorry

end Iris.Proofmode
