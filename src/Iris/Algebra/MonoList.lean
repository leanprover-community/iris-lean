import Iris.Algebra.Auth
import Iris.Algebra.MaxPrefixList

namespace Iris

open OFE CMRA Auth

abbrev MonoListRes (Q : Type _) (A : Type _) [UFraction Q] [OFE A] := Auth Q (MaxPrefixList A)

namespace MonoList

variable {Q A : Type _} [UFraction Q] [OFE A]

def monoListAuth (dq : DFrac Q) (l : List A) : MonoListRes Q A :=
  (Auth.auth dq (toMaxPrefixList l)) • Auth.frag (toMaxPrefixList l)

def monoListLb (l : List A) : MonoListRes Q A :=
  Auth.frag (toMaxPrefixList l)

theorem monoListLbDistInj {l1 l2 : List A} :
    monoListLb (Q := Q) l1 ≡{n}≡ monoListLb l2 → l1 ≡{n}≡ l2 := by
  intro h
  exact toMaxPrefixList_dist_inj (A := A) ((Auth.frag_dist_inj (F := Q) h))

theorem monoListLbInj {l1 l2 : List A} :
    monoListLb (Q := Q) l1 ≡ monoListLb l2 → l1 ≡ l2 := by
  intro h
  exact toMaxPrefixList_inj (A := A) ((Auth.frag_inj (F := Q) h))

theorem monoListAuthDfracValidN (n : Nat) (dq : DFrac Q) (l : List A) :
    ✓{n} (monoListAuth (Q := Q) dq l) ↔ ✓ dq := by
  unfold monoListAuth
  rw [Auth.both_dfrac_validN]
  constructor
  · rintro ⟨hdq, _, _⟩
    exact hdq
  · intro hdq
    exact ⟨hdq, CMRA.incN_refl _, toMaxPrefixList_validN (A := A) n l⟩

theorem monoListAuthDfracValid (dq : DFrac Q) (l : List A) :
    ✓ (monoListAuth (Q := Q) dq l) ↔ ✓ dq := by
  unfold monoListAuth
  rw [Auth.both_dfrac_valid]
  constructor
  · rintro ⟨hdq, _, _⟩
    exact hdq
  · intro hdq
    exact ⟨hdq, fun _ => CMRA.incN_refl _, toMaxPrefixList_valid (A := A) l⟩

theorem monoListAuthValid (l : List A) :
    ✓ (monoListAuth (Q := Q) (DFrac.own (1 : Q)) l) := by
  rw [monoListAuthDfracValid]
  exact DFrac.valid_own_one

theorem monoListAuthValidN (n : Nat) (l : List A) :
    ✓{n} (monoListAuth (Q := Q) (DFrac.own (1 : Q)) l) := by
  rw [monoListAuthDfracValidN]
  exact DFrac.valid_own_one

theorem monoListLbOpL {l1 l2 : List A} :
    l1 <+: l2 → monoListLb (Q := Q) l1 • monoListLb l2 ≡ monoListLb l2 := by
  intro h
  unfold monoListLb
  calc
    ((Auth.frag (toMaxPrefixList l1) • Auth.frag (toMaxPrefixList l2)) : MonoListRes Q A)
        ≡ (Auth.frag (toMaxPrefixList l1 • toMaxPrefixList l2) : MonoListRes Q A) := by
            exact OFE.Equiv.of_eq (Auth.frag_op (F := Q)
              (b1 := toMaxPrefixList l1) (b2 := toMaxPrefixList l2)).symm
    _ ≡ (Auth.frag (toMaxPrefixList l2) : MonoListRes Q A) := OFE.NonExpansive.eqv (toMaxPrefixList_op_l (A := A) h)

theorem monoListLbOpR {l1 l2 : List A} :
    l1 <+: l2 → monoListLb (Q := Q) l2 • monoListLb l1 ≡ monoListLb l2 := by
  intro h
  unfold monoListLb
  calc
    ((Auth.frag (toMaxPrefixList l2) • Auth.frag (toMaxPrefixList l1)) : MonoListRes Q A)
        ≡ (Auth.frag (toMaxPrefixList l2 • toMaxPrefixList l1) : MonoListRes Q A) := by
            exact OFE.Equiv.of_eq (Auth.frag_op (F := Q)
              (b1 := toMaxPrefixList l2) (b2 := toMaxPrefixList l1)).symm
    _ ≡ (Auth.frag (toMaxPrefixList l2) : MonoListRes Q A) := OFE.NonExpansive.eqv (toMaxPrefixList_op_r (A := A) h)

theorem monoListLbMono {l1 l2 : List A} :
    l1 <+: l2 → monoListLb (Q := Q) l1 ≼ monoListLb (Q := Q) l2 := by
  intro h
  exact Auth.frag_inc_of_inc (toMaxPrefixList_mono (A := A) h)

theorem monoListIncluded (dq : DFrac Q) (l : List A) :
    monoListLb (Q := Q) l ≼ monoListAuth (Q := Q) dq l := by
  unfold monoListLb monoListAuth
  exact ⟨Auth.auth dq (toMaxPrefixList l), comm⟩

theorem monoListUpdate {l1 l2 : List A} :
    l1 <+: l2 →
      monoListAuth (Q := Q) (DFrac.own (1 : Q)) l1 ~~>
        monoListAuth (DFrac.own (1 : Q)) l2 := by
  intro h
  unfold monoListAuth
  exact Auth.auth_update (maxPrefixList_localUpdate (A := A) h)

theorem monoListAuthPersist (dq : DFrac Q) (l : List A) :
    monoListAuth (Q := Q) dq l ~~> monoListAuth DFrac.discard l := by
  unfold monoListAuth
  exact Update.op (Auth.auth_update_auth_persist (F := Q) (dq := dq) (a := toMaxPrefixList l)) Update.id

theorem monoListAuthUnpersist [IsSplitFraction Q] (l : List A) :
    monoListAuth (Q := Q) DFrac.discard l ~~>:
      fun k => ∃ q, k = monoListAuth (Q := Q) (DFrac.own q) l := by
  unfold monoListAuth
  simpa using (Auth.auth_updateP_both_unpersist (F := Q)
    (a := toMaxPrefixList l) (b := toMaxPrefixList l))

abbrev MonoListURF (T : COFE.OFunctorPre) [RFunctor T] : COFE.OFunctorPre :=
  AuthURF (F := Q) (MaxPrefixListURF T)

instance {T} [RFunctor T] : URFunctor (MonoListURF (Q := Q) T) := by
  simpa [MonoListURF] using (inferInstance : URFunctor (AuthURF (F := Q) (MaxPrefixListURF T)))

instance {T} [RFunctorContractive T] : URFunctorContractive (MonoListURF (Q := Q) T) := by
  simpa [MonoListURF] using
    (inferInstance : URFunctorContractive (AuthURF (F := Q) (MaxPrefixListURF T)))

abbrev MonoListRF (T : COFE.OFunctorPre) [RFunctor T] : COFE.OFunctorPre :=
  AuthRF (F := Q) (MaxPrefixListURF T)

instance {T} [RFunctor T] : RFunctor (MonoListRF (Q := Q) T) := by
  simpa [MonoListRF] using (inferInstance : RFunctor (AuthRF (F := Q) (MaxPrefixListURF T)))

instance {T} [RFunctorContractive T] : RFunctorContractive (MonoListRF (Q := Q) T) := by
  simpa [MonoListRF] using
    (inferInstance : RFunctorContractive (AuthRF (F := Q) (MaxPrefixListURF T)))

end MonoList

end Iris
