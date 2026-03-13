import Iris.Algebra.Auth
import Iris.Algebra.MonoNumbers

namespace Iris

open OFE CMRA Auth

abbrev MonoIntRes (Q : Type _) [UFraction Q] := Auth Q (Option MaxInt)

namespace MonoInt

variable {Q : Type _} [UFraction Q]

def monoIntAuth (dq : DFrac Q) (n : Int) : MonoIntRes Q :=
  (Auth.auth dq (some ((n : Int) : MaxInt))) • Auth.frag (some ((n : Int) : MaxInt))

def monoIntLb (n : Int) : MonoIntRes Q :=
  Auth.frag (some ((n : Int) : MaxInt))

theorem monoIntAuthDfracValid (dq : DFrac Q) (n : Int) :
    ✓ (monoIntAuth (Q := Q) dq n) ↔ ✓ dq := by
  unfold monoIntAuth
  rw [Auth.both_dfrac_valid_discrete]
  constructor
  · rintro ⟨hdq, _, _⟩
    exact hdq
  · intro hdq
    exact ⟨hdq, CMRA.inc_refl _, trivial⟩

theorem monoIntAuthValid (n : Int) :
    ✓ (monoIntAuth (Q := Q) (DFrac.own (1 : Q)) n) := by
  rw [monoIntAuthDfracValid]
  exact DFrac.valid_own_one

theorem monoIntBothDfracValid (dq : DFrac Q) (n m : Int) :
    ✓ (monoIntAuth (Q := Q) dq n • monoIntLb (Q := Q) m) ↔ ✓ dq ∧ m ≤ n := by
  let a : Option MaxInt := some (n : MaxInt)
  let b : Option MaxInt := some (m : MaxInt)
  have hEq :
      monoIntAuth (Q := Q) dq n • monoIntLb (Q := Q) m ≡
        ((Auth.auth dq a) • Auth.frag (a • b) : MonoIntRes Q) := by
    unfold monoIntAuth monoIntLb
    have hAssoc :
        (((Auth.auth dq a) • Auth.frag a) • Auth.frag b : MonoIntRes Q) ≡
          ((Auth.auth dq a) • (Auth.frag a • Auth.frag b) : MonoIntRes Q) := assoc.symm
    have hFrag :
        ((Auth.auth dq a) • (Auth.frag a • Auth.frag b) : MonoIntRes Q) ≡
          ((Auth.auth dq a) • Auth.frag (a • b) : MonoIntRes Q) := by
            exact (OFE.Equiv.of_eq (Auth.frag_op (F := Q) (b1 := a) (b2 := b)).symm).op_r
    exact hAssoc.trans hFrag
  rw [CMRA.valid_iff hEq, Auth.both_dfrac_valid_discrete]
  constructor
  · rintro ⟨hdq, hinc, _⟩
    have hle : (((n : Int) : MaxInt) • ((m : Int) : MaxInt)) ≼ ((n : Int) : MaxInt) :=
      Option.some_inc_some_iff_isTotal.mp hinc
    have hmax : max n m ≤ n := (MaxInt.included _ _).1 hle
    exact ⟨hdq, (Int.max_le.mp hmax).2⟩
  · rintro ⟨hdq, hle⟩
    refine ⟨hdq, ?_, trivial⟩
    apply Option.some_inc_some_iff_isTotal.mpr
    exact (MaxInt.included _ _).2 <| Int.max_le.mpr ⟨Int.le_refl _, hle⟩

theorem monoIntBothValid (n m : Int) :
    ✓ (monoIntAuth (Q := Q) (DFrac.own (1 : Q)) n • monoIntLb (Q := Q) m) ↔ m ≤ n := by
  rw [monoIntBothDfracValid]
  constructor
  · exact fun ⟨_, h⟩ => h
  · exact fun h => ⟨DFrac.valid_own_one, h⟩

theorem monoIntLbMono (n1 n2 : Int) :
    n1 ≤ n2 → monoIntLb (Q := Q) n1 ≼ monoIntLb (Q := Q) n2 := by
  intro h
  apply Auth.frag_inc_of_inc
  apply Option.some_inc_some_iff_isTotal.mpr
  exact (MaxInt.included _ _).2 h

theorem monoIntIncluded (dq : DFrac Q) (n : Int) :
    monoIntLb (Q := Q) n ≼ monoIntAuth (Q := Q) dq n := by
  unfold monoIntLb monoIntAuth
  exact ⟨Auth.auth dq (some ((n : Int) : MaxInt)), comm⟩

theorem monoIntUpdate {n : Int} (n' : Int) :
    n ≤ n' → monoIntAuth (Q := Q) (DFrac.own (1 : Q)) n ~~> monoIntAuth (DFrac.own (1 : Q)) n' := by
  intro h
  unfold monoIntAuth
  apply Auth.auth_update
  apply LocalUpdate.option
  exact MaxInt.localUpdate ((n : Int) : MaxInt) ((n : Int) : MaxInt) ((n' : Int) : MaxInt) h

theorem monoIntAuthPersist (dq : DFrac Q) (n : Int) :
    monoIntAuth (Q := Q) dq n ~~> monoIntAuth DFrac.discard n := by
  unfold monoIntAuth
  exact Update.op (Auth.auth_update_auth_persist (F := Q) (dq := dq) (a := some ((n : Int) : MaxInt))) Update.id

theorem monoIntAuthUnpersist [IsSplitFraction Q] (n : Int) :
    monoIntAuth (Q := Q) DFrac.discard n ~~>:
      fun k => ∃ q, k = monoIntAuth (Q := Q) (DFrac.own q) n := by
  unfold monoIntAuth
  simpa using (Auth.auth_updateP_both_unpersist (F := Q)
    (a := some ((n : Int) : MaxInt)) (b := some ((n : Int) : MaxInt)))

end MonoInt

end Iris
