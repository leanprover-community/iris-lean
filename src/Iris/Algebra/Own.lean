import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Algebra.IProp

structure inG (FF : Iris.GFunctors) (A : Type) [Iris.UCMRA A] where
  id : Iris.GId FF
  ap := Iris.RFunctor.ap (FF[id].car)
  prf : ap (Iris.IProp FF)

theorem subG_inG FF [Iris.IsGFunctors FF] (F : Iris.COFE.OFunctorPre) :
  Iris.SubG #[F] FF -> inG FF (Iris.RFunctor.ap F (Iris.IProp FF)) := by
