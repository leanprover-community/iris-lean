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

end MonoList

end Iris
