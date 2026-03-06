import Iris.Algebra.Agree
import Iris.Algebra.DFrac

namespace Iris

abbrev DFracAgree (F : Type _) (A : Type _) [UFraction F] [OFE A] := DFrac F × Agree A

namespace DFracAgree

open DFrac Agree OFE CMRA

variable {F A : Type _} [UFraction F] [OFE A]

def toDFracAgree (d : DFrac F) (a : A) : DFracAgree F A :=
  (d, toAgree a)

def toFracAgree (q : F) (a : A) : DFracAgree F A :=
  toDFracAgree (DFrac.own q) a

instance toDFracAgree_ne (d : DFrac F) : NonExpansive (toDFracAgree (F := F) (A := A) d) where
  ne {_ _ _} h := OFE.dist_prod_ext rfl <| toAgree.ne.ne h

instance toFracAgree_one_exclusive {a : A} :
    CMRA.Exclusive (toFracAgree (F := F) (A := A) One.one a) := by
  change CMRA.Exclusive (DFrac.own One.one, toAgree a)
  infer_instance

theorem dfracAgree_op (d1 d2 : DFrac F) (a : A) :
    toDFracAgree (F := F) (A := A) (d1 • d2) a ≡
      toDFracAgree d1 a • toDFracAgree d2 a :=
  OFE.equiv_prod_ext rfl Agree.idemp.symm

theorem fracAgree_op (q1 q2 : F) (a : A) :
    toFracAgree (F := F) (A := A) (q1 + q2) a ≡
      toFracAgree q1 a • toFracAgree q2 a :=
  dfracAgree_op (F := F) (A := A) (d1 := DFrac.own q1) (d2 := DFrac.own q2) a

theorem dfracAgree_op_valid (d1 d2 : DFrac F) (a1 a2 : A) :
    ✓ (toDFracAgree (F := F) (A := A) d1 a1 • toDFracAgree d2 a2) ↔
      ✓ (d1 • d2) ∧ a1 ≡ a2 := by
  change (✓ (d1 • d2) ∧ ✓ (toAgree a1 • toAgree a2)) ↔ ✓ (d1 • d2) ∧ a1 ≡ a2
  simp [Agree.toAgree_op_valid_iff_equiv]

theorem dfracAgree_op_valid_L [Leibniz A] (d1 d2 : DFrac F) (a1 a2 : A) :
    ✓ (toDFracAgree (F := F) (A := A) d1 a1 • toDFracAgree d2 a2) ↔
      ✓ (d1 • d2) ∧ a1 = a2 := by
  simpa using dfracAgree_op_valid (F := F) (A := A) d1 d2 a1 a2

theorem dfracAgree_op_validN (n : Nat) (d1 d2 : DFrac F) (a1 a2 : A) :
    ✓{n} (toDFracAgree (F := F) (A := A) d1 a1 • toDFracAgree d2 a2) ↔
      ✓{n} (d1 • d2) ∧ a1 ≡{n}≡ a2 := by
  change (✓{n} (d1 • d2) ∧ ✓{n} (toAgree a1 • toAgree a2)) ↔ ✓{n} (d1 • d2) ∧ a1 ≡{n}≡ a2
  simp [Agree.toAgree_op_validN_iff_dist]

theorem fracAgree_op_valid (q1 q2 : F) (a1 a2 : A) :
    ✓ (toFracAgree (F := F) (A := A) q1 a1 • toFracAgree q2 a2) ↔
      ✓ (DFrac.own q1 • DFrac.own q2 : DFrac F) ∧ a1 ≡ a2 :=
  dfracAgree_op_valid (F := F) (A := A) (DFrac.own q1) (DFrac.own q2) a1 a2

theorem fracAgree_op_valid_L [Leibniz A] (q1 q2 : F) (a1 a2 : A) :
    ✓ (toFracAgree (F := F) (A := A) q1 a1 • toFracAgree q2 a2) ↔
      ✓ (DFrac.own q1 • DFrac.own q2 : DFrac F) ∧ a1 = a2 :=
  dfracAgree_op_valid_L (F := F) (A := A) (DFrac.own q1) (DFrac.own q2) a1 a2

theorem fracAgree_op_validN (n : Nat) (q1 q2 : F) (a1 a2 : A) :
    ✓{n} (toFracAgree (F := F) (A := A) q1 a1 • toFracAgree q2 a2) ↔
      ✓{n} (DFrac.own q1 • DFrac.own q2 : DFrac F) ∧ a1 ≡{n}≡ a2 :=
  dfracAgree_op_validN (F := F) (A := A) n (DFrac.own q1) (DFrac.own q2) a1 a2

theorem dfracAgree_update_2 (d1 d2 : DFrac F) (a1 a2 a' : A)
    (hd : d1 • d2 = DFrac.own (One.one : F)) :
    toDFracAgree (F := F) (A := A) d1 a1 • toDFracAgree d2 a2 ~~>
      toDFracAgree d1 a' • toDFracAgree d2 a' := by
  refine Update.equiv_left ?_ <|
    Update.exclusive
      (x := ((DFrac.own (One.one : F)), (toAgree a1 • toAgree a2)))
      (y := toDFracAgree d1 a' • toDFracAgree d2 a') ?_
  · change ((DFrac.own (One.one : F)), toAgree a1 • toAgree a2) ≡
      (d1 • d2, toAgree a1 • toAgree a2)
    exact OFE.equiv_prod_ext (Equiv.of_eq hd).symm Equiv.rfl
  · refine (dfracAgree_op_valid (F := F) (A := A) d1 d2 a' a').2 ?_
    exact ⟨hd ▸ DFrac.valid_own_one, Equiv.rfl⟩

theorem fracAgree_update_2 (q1 q2 : F) (a1 a2 a' : A)
    (hq : q1 + q2 = (One.one : F)) :
    toFracAgree (F := F) (A := A) q1 a1 • toFracAgree q2 a2 ~~>
      toFracAgree q1 a' • toFracAgree q2 a' := by
  apply dfracAgree_update_2 (F := F) (A := A) (d1 := DFrac.own q1) (d2 := DFrac.own q2)
  simp [CMRA.op, DFrac.op, hq]

theorem dfracAgree_persist (d : DFrac F) (a : A) :
    toDFracAgree (F := F) (A := A) d a ~~>
      toDFracAgree DFrac.discard a :=
  Update.prod (x := toDFracAgree d a) DFrac.update_discard Update.id

theorem dfracAgree_unpersist [IsSplitFraction F] (a : A) :
    toDFracAgree (F := F) (A := A) DFrac.discard a ~~>:
      fun k => ∃ q, k = toDFracAgree (DFrac.own q) a := by
  refine UpdateP.prod (x := toDFracAgree DFrac.discard a)
    DFrac.update_acquire (UpdateP.id (x := toAgree a) rfl) ?_
  intro d ag hd hag
  rcases hd with ⟨q, rfl⟩
  subst hag
  exact ⟨q, rfl⟩

end DFracAgree

section dfracAgree_rfunctor

open COFE

abbrev DFracAgreeRF (Q : Type _) [UFraction Q] (F : COFE.OFunctorPre) : COFE.OFunctorPre :=
  ProdOF (constOF (DFrac Q)) (AgreeRF F)

instance {Q F} [UFraction Q] [COFE.OFunctor F] : RFunctor (DFracAgreeRF Q F) where
  map f g := Prod.mapC (CMRA.Hom.id (α := DFrac Q)) (RFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ := Prod.map_ne (fun _ => rfl) (fun _ => RFunctor.map_ne.ne Hx Hy _)
  map_id x := by
    cases x
    exact OFE.equiv_prod_ext (OFE.Equiv.of_eq rfl) (RFunctor.map_id _)
  map_comp f g f' g' x := by
    cases x
    exact OFE.equiv_prod_ext (OFE.Equiv.of_eq rfl) (RFunctor.map_comp f g f' g' _)

instance {Q F} [UFraction Q] [COFE.OFunctorContractive F] : RFunctorContractive (DFracAgreeRF Q F) where
  map_contractive.1 H _ := Prod.map_ne (fun _ => rfl) (fun _ => RFunctorContractive.map_contractive.1 H _)

end dfracAgree_rfunctor

end Iris
