import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Algebra.IProp
import Iris.Instances.UPred.Instance

import Iris.ProofMode

def cmra_transport {A : Type} {B : Type} (H : A = B) : Iris.CMRA A = Iris.CMRA B := by
  simp [H]

abbrev discrete_fun_insert [DecidableEq A] {B : A → Type}
  (x : A) (y : B x) (f : ∀ a, B a) : ∀ a, B a := λ x' =>
  if h : (x = x') then Eq.ndrec y h else f x'

def discrete_fun_singleton [DecidableEq A] {B : A -> Type} [i : ∀ a, Iris.UCMRA (B a)] (x : A) (y : B x) :
  ∀ a, B a := discrete_fun_insert x y (λ a => (i a).unit)

theorem discrete_fun_lookup_singleton [DecidableEq A] {B : A -> Type} [∀ a, Iris.UCMRA (B a)] (x : A) (y : B x) :
  (discrete_fun_singleton x y) x = y := by
  unfold discrete_fun_singleton
  simp [discrete_fun_insert]

def ap (F : Iris.GFunctor) T [Iris.OFE T] := @Iris.RFunctor.ap F.car T F.rFunctor _

class inG (FF : Iris.GFunctors) (A : Type) [i : Iris.CMRA A] where
  id : Iris.GId FF
  prf : A = @ap FF[id] (Iris.iPrePropO FF) _

instance instA [iA : Iris.CMRA A] [i : inG FF A] :
  Iris.CMRA (FF[i.id].car (Iris.iPrePropO FF) (Iris.iPrePropO FF)) := by
  unfold inG.id
  rcases i with ⟨ id, prf ⟩
  simp [ap, Iris.RFunctor.ap] at prf
  rewrite [<- prf]; apply iA

def iRes_singleton [Iris.CMRA A] [i : inG FF A] (a : A) : Iris.IResUR FF :=
  discrete_fun_singleton (i.id) (fun _ => some (Eq.mp i.prf a))

theorem discrete_fun_validI' [Iris.UCMRA M] {A : Type _} {B : A -> Type _} [instcmra : ∀ a, Iris.CMRA (B a)] [∀ x, Iris.CMRA.IsTotal (B x)] (g : ∀ a, B a) a :
  @UPred.cmraValid M _ (∀ a, B a) (Iris.cmraDiscreteFunO B) g ⊢ @UPred.cmraValid _ _ (B a) (instcmra a) (g a) := by
  simp [UPred.cmraValid]
  simp [Iris.CMRA.ValidN]; iintro Hg; istop
  simp [Iris.BI.Entails, UPred.Entails]
  intros n x Hx Hg; apply Hg

theorem discrete_fun_validI [Iris.UCMRA M] {A : Type _} {B : A -> Type _} [instcmra : ∀ a, Iris.CMRA (B a)] [∀ x, Iris.CMRA.IsTotal (B x)] (g : ∀ a, B a) :
  @UPred.cmraValid M _ (∀ a, B a) (Iris.cmraDiscreteFunO B) g ⊣⊢ ∀ a, @UPred.cmraValid _ _ (B a) (instcmra a) (g a) := by
  simp [UPred.cmraValid]; constructor
  · iintro h a; istop; simp [Iris.BI.Entails, UPred.Entails]
    intros n x Hx Hg
    simp [Iris.CMRA.ValidN] at Hg; apply Hg
  · simp [Iris.CMRA.ValidN]; iintro Hg; istop
    simp [Iris.BI.Entails, UPred.Entails]
    intros n x Hx Hg
    simp [Iris.BI.forall, Iris.BI.sForall, UPred.sForall] at Hg
    apply Hg

theorem singleton_validI [Iris.UCMRA M] [Iris.CMRA A] (a : A) :
  @UPred.cmraValid _ _ _ _ (λ (γ : Iris.GName) => some a) ⊢ @UPred.cmraValid M _ _ _ a := by
  sorry

theorem iRes_singleton_valid [Iris.UCMRA M] [iA : Iris.CMRA A] [i : inG FF A] (a : A) :
  @UPred.cmraValid _ _ _ _ (@iRes_singleton _ FF _ _ a) ⊢ @UPred.cmraValid M _ _ _ a := by
  unfold iRes_singleton
  apply Iris.BI.Entails.trans
  apply discrete_fun_validI'; apply i.id
  rewrite [discrete_fun_lookup_singleton]
  apply Iris.BI.Entails.trans
  have := (Eq.mp (cmra_transport i.prf) iA)
  sorry
  sorry
  sorry

abbrev own [Iris.CMRA A] [inG FF A] (a : A) : Iris.IProp FF :=
  UPred.ownM (iRes_singleton a)
