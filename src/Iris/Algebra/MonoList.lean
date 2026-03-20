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

instance monoListLb_coreId (l : List A) : CoreId (monoListLb (Q := Q) l) := by
  unfold monoListLb
  infer_instance

instance monoListAuth_coreId (l : List A) : CoreId (monoListAuth (Q := Q) DFrac.discard l) := by
  unfold monoListAuth
  infer_instance

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

theorem monoListLbOpValidN (n : Nat) (l1 l2 : List A) :
    ✓{n} (monoListLb (Q := Q) l1 • monoListLb l2) ↔
      (∃ t, l2 ≡{n}≡ l1 ++ t) ∨ (∃ t, l1 ≡{n}≡ l2 ++ t) := by
  unfold monoListLb
  constructor
  · intro h
    have hEq : ✓{n} (Auth.frag (toMaxPrefixList l1 • toMaxPrefixList l2) : MonoListRes Q A) := by
      exact (OFE.Equiv.of_eq (Auth.frag_op (F := Q)
        (b1 := toMaxPrefixList l1) (b2 := toMaxPrefixList l2)).symm).dist.validN.mpr h
    exact (Auth.frag_validN (F := Q) (b := toMaxPrefixList l1 • toMaxPrefixList l2)).1 hEq |>
      (toMaxPrefixList_op_validN (A := A) n l1 l2).1
  · intro h
    have hEq : ✓{n} (toMaxPrefixList (A := A) l1 • toMaxPrefixList l2) := (toMaxPrefixList_op_validN (A := A) n l1 l2).2 h
    exact (OFE.Equiv.of_eq (Auth.frag_op (F := Q)
      (b1 := toMaxPrefixList l1) (b2 := toMaxPrefixList l2)).symm).dist.validN.mp <|
      (Auth.frag_validN (F := Q) (b := toMaxPrefixList l1 • toMaxPrefixList l2)).2 hEq

theorem monoListLbOpValid (l1 l2 : List A) :
    ✓ (monoListLb (Q := Q) l1 • monoListLb l2) ↔
      (∃ t, l2 ≡ l1 ++ t) ∨ (∃ t, l1 ≡ l2 ++ t) := by
  unfold monoListLb
  constructor
  · intro h
    have hEq : ✓ (Auth.frag (toMaxPrefixList l1 • toMaxPrefixList l2) : MonoListRes Q A) := by
      exact CMRA.valid_of_eqv
        (OFE.Equiv.of_eq (Auth.frag_op (F := Q)
          (b1 := toMaxPrefixList l1) (b2 := toMaxPrefixList l2)).symm)
        h
    exact (Auth.frag_valid (F := Q) (b := toMaxPrefixList l1 • toMaxPrefixList l2)).1 hEq |>
      (toMaxPrefixList_op_valid (A := A) l1 l2).1
  · intro h
    have hEq : ✓ (toMaxPrefixList (A := A) l1 • toMaxPrefixList l2) := (toMaxPrefixList_op_valid (A := A) l1 l2).2 h
    exact CMRA.valid_of_eqv
      (OFE.Equiv.of_eq (Auth.frag_op (F := Q)
        (b1 := toMaxPrefixList l1) (b2 := toMaxPrefixList l2)).symm)
      ((Auth.frag_valid (F := Q) (b := toMaxPrefixList l1 • toMaxPrefixList l2)).2 hEq)

theorem monoListBothDfracValidN (n : Nat) (dq : DFrac Q) (l1 l2 : List A) :
    ✓{n} (monoListAuth (Q := Q) dq l1 • monoListLb (Q := Q) l2) ↔
      ✓ dq ∧ ∃ t, l1 ≡{n}≡ l2 ++ t := by
  let a := toMaxPrefixList (A := A) l1
  let b := toMaxPrefixList (A := A) l2
  have hEq : monoListAuth (Q := Q) dq l1 • monoListLb (Q := Q) l2 ≡
      (((Auth.auth dq a) • Auth.frag ((a • b : MaxPrefixList A)) : MonoListRes Q A)) := by
    unfold monoListAuth monoListLb
    have hAssoc : (((Auth.auth dq a) • Auth.frag a) • Auth.frag b : MonoListRes Q A) ≡
        ((Auth.auth dq a) • (Auth.frag a • Auth.frag b) : MonoListRes Q A) := assoc.symm
    have hFrag : ((Auth.auth dq a) • (Auth.frag a • Auth.frag b) : MonoListRes Q A) ≡
        (((Auth.auth dq a) • Auth.frag ((a • b : MaxPrefixList A)) : MonoListRes Q A)) :=
      (OFE.Equiv.of_eq (Auth.frag_op (F := Q) (b1 := a) (b2 := b)).symm).op_r
    exact hAssoc.trans hFrag
  constructor
  · intro h
    have h' : ✓{n} (((Auth.auth dq a) • Auth.frag ((a • b : MaxPrefixList A)) : MonoListRes Q A)) := hEq.dist.validN.mp h
    have hBoth := (Auth.both_dfrac_validN (F := Q) (dq := dq) (a := a) (b := (a • b))).1 h'
    have hvalidAB : ✓{n} (a • b) := CMRA.validN_of_incN hBoth.2.1 (toMaxPrefixList_validN (A := A) n l1)
    rcases (toMaxPrefixList_op_validN (A := A) n l1 l2).1 hvalidAB with hleft | hright
    · rcases hleft with ⟨t, ht⟩
      have hp : l1 <+: l1 ++ t := ⟨t, rfl⟩
      have hmap : b ≡{n}≡ toMaxPrefixList (A := A) (l1 ++ t) := toMaxPrefixList_ne.ne ht
      have hop : a • toMaxPrefixList (A := A) (l1 ++ t) ≡{n}≡ toMaxPrefixList (A := A) (l1 ++ t) :=
        (toMaxPrefixList_op_l (A := A) hp).dist
      have hab_eq : a • b ≡{n}≡ b := (hmap.op_r).trans (hop.trans hmap.symm)
      have hbinc : b ≼{n} a := (hab_eq.incN_l).1 hBoth.2.1
      rcases (toMaxPrefixList_includedN (A := A) n l2 l1).1 hbinc with ⟨u, hu⟩
      exact ⟨hBoth.1, ⟨u, hu⟩⟩
    · exact ⟨hBoth.1, hright⟩
  · rintro ⟨hdq, ⟨t, ht⟩⟩
    have hmap : a ≡{n}≡ toMaxPrefixList (A := A) (l2 ++ t) := toMaxPrefixList_ne.ne ht
    have hp : l2 <+: l2 ++ t := ⟨t, rfl⟩
    have hop : toMaxPrefixList (A := A) (l2 ++ t) • b ≡{n}≡ toMaxPrefixList (A := A) (l2 ++ t) :=
      (toMaxPrefixList_op_r (A := A) hp).dist
    have hincl : a • b ≼{n} a := by
      refine ⟨CMRA.unit, ?_⟩
      calc
        a ≡{n}≡ toMaxPrefixList (A := A) (l2 ++ t) := hmap
        _ ≡{n}≡ toMaxPrefixList (A := A) (l2 ++ t) • b := hop.symm
        _ ≡{n}≡ a • b := (hmap.op_l).symm
        _ ≡{n}≡ (a • b) • CMRA.unit := (CMRA.unit_right_id_dist (a • b)).symm
    have hBoth : ✓{n} (((Auth.auth dq a) • Auth.frag ((a • b : MaxPrefixList A)) : MonoListRes Q A)) :=
      (Auth.both_dfrac_validN (F := Q) (dq := dq) (a := a) (b := (a • b))).2 ⟨hdq, hincl, toMaxPrefixList_validN (A := A) n l1⟩
    exact hEq.dist.validN.mpr hBoth

theorem monoListBothValidN (n : Nat) (l1 l2 : List A) :
    ✓{n} (monoListAuth (Q := Q) (DFrac.own (1 : Q)) l1 • monoListLb (Q := Q) l2) ↔
      ∃ t, l1 ≡{n}≡ l2 ++ t := by
  rw [monoListBothDfracValidN]
  constructor
  · rintro ⟨_, ht⟩
    exact ht
  · intro ht
    exact ⟨DFrac.valid_own_one, ht⟩

theorem monoListBothDfracValid (dq : DFrac Q) (l1 l2 : List A) :
    ✓ (monoListAuth (Q := Q) dq l1 • monoListLb (Q := Q) l2) ↔
      ✓ dq ∧ ∃ t, l1 ≡ l2 ++ t := by
  let a : MaxPrefixList A := toMaxPrefixList (A := A) l1
  let b : MaxPrefixList A := toMaxPrefixList (A := A) l2
  have hEq : monoListAuth (Q := Q) dq l1 • monoListLb (Q := Q) l2 ≡
      ((Auth.auth (F := Q) dq a) • Auth.frag (a • b) : MonoListRes Q A) := by
    unfold monoListAuth monoListLb
    calc
      (((Auth.auth (F := Q) dq a) • Auth.frag a) • Auth.frag b : MonoListRes Q A)
          ≡ ((Auth.auth (F := Q) dq a) • (Auth.frag a • Auth.frag b) : MonoListRes Q A) := assoc.symm
      _ ≡ ((Auth.auth (F := Q) dq a) • Auth.frag (a • b) : MonoListRes Q A) := by
            exact (OFE.Equiv.of_eq (Auth.frag_op (F := Q) (b1 := a) (b2 := b)).symm).op_r
  rw [CMRA.valid_iff hEq, Auth.both_dfrac_valid]
  constructor
  · rintro ⟨hdq, hinc, _⟩
    refine ⟨hdq, ?_⟩
    have hbincN : ∀ n, b ≼{n} a := fun n => CMRA.incN_trans (CMRA.incN_op_right n a b) (hinc n)
    exact (toMaxPrefixList_included (A := A) l2 l1).1 <|
      (maxPrefixList_included_includedN (A := A) b a).2 hbincN
  · rintro ⟨hdq, hprefix⟩
    refine ⟨hdq, ?_, toMaxPrefixList_valid (A := A) l1⟩
    intro n
    have hbinc : b ≼ a := (toMaxPrefixList_included (A := A) l2 l1).2 hprefix
    have hab : a • b ≼ a := by
      calc
        a • b ≼ a • a := CMRA.op_mono_right a hbinc
        _ ≡ a := CMRA.op_self a
    exact CMRA.incN_of_inc n hab

theorem monoListBothValid (l1 l2 : List A) :
    ✓ (monoListAuth (Q := Q) (DFrac.own (1 : Q)) l1 • monoListLb (Q := Q) l2) ↔
      ∃ t, l1 ≡ l2 ++ t := by
  rw [monoListBothDfracValid]
  constructor
  · rintro ⟨_, ht⟩
    exact ht
  · intro ht
    exact ⟨DFrac.valid_own_one, ht⟩

theorem monoListBothDfracValid_L [Leibniz A] (dq : DFrac Q) (l1 l2 : List A) :
    ✓ (monoListAuth (Q := Q) dq l1 • monoListLb (Q := Q) l2) ↔
      ✓ dq ∧ l2 <+: l1 := by
  rw [monoListBothDfracValid]
  constructor
  · rintro ⟨hdq, ⟨t, ht⟩⟩
    exact ⟨hdq, ⟨t, Leibniz.eq_of_eqv ht.symm⟩⟩
  · rintro ⟨hdq, ⟨t, rfl⟩⟩
    exact ⟨hdq, ⟨t, Equiv.rfl⟩⟩

theorem monoListBothValid_L [Leibniz A] (l1 l2 : List A) :
    ✓ (monoListAuth (Q := Q) (DFrac.own (1 : Q)) l1 • monoListLb (Q := Q) l2) ↔
      l2 <+: l1 := by
  rw [monoListBothValid]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Leibniz.eq_of_eqv ht.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, Equiv.rfl⟩

theorem monoListLbOpValid_L [Leibniz A] (l1 l2 : List A) :
    ✓ (monoListLb (Q := Q) l1 • monoListLb l2) ↔ l1 <+: l2 ∨ l2 <+: l1 := by
  rw [monoListLbOpValid]
  constructor
  · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · exact Or.inl ⟨t, Leibniz.eq_of_eqv ht.symm⟩
    · exact Or.inr ⟨t, Leibniz.eq_of_eqv ht.symm⟩
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact Or.inl ⟨t, Equiv.rfl⟩
    · exact Or.inr ⟨t, Equiv.rfl⟩

theorem monoListLbOpValid_1_L [Leibniz A] (l1 l2 : List A) :
    ✓ (monoListLb (Q := Q) l1 • monoListLb l2) → l1 <+: l2 ∨ l2 <+: l1 :=
  (monoListLbOpValid_L (Q := Q) l1 l2).1

theorem monoListLbOpValid_2_L [Leibniz A] (l1 l2 : List A) :
    l1 <+: l2 ∨ l2 <+: l1 → ✓ (monoListLb (Q := Q) l1 • monoListLb l2) :=
  (monoListLbOpValid_L (Q := Q) l1 l2).2

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
