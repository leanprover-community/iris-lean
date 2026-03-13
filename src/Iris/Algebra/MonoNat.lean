import Iris.Algebra.Auth
import Iris.Algebra.MonoNumbers

namespace Iris

open OFE CMRA Auth

abbrev MonoNatRes (Q : Type _) [UFraction Q] := Auth Q MaxNat

namespace MonoNat

variable {Q : Type _} [UFraction Q]

def monoNatAuth (dq : DFrac Q) (n : Nat) : MonoNatRes Q :=
  (Auth.auth dq ((n : Nat) : MaxNat)) • Auth.frag ((n : Nat) : MaxNat)

def monoNatLb (n : Nat) : MonoNatRes Q :=
  Auth.frag ((n : Nat) : MaxNat)

theorem monoNatAuthDfracValid (dq : DFrac Q) (n : Nat) :
    ✓ (monoNatAuth (Q := Q) dq n) ↔ ✓ dq := by
  unfold monoNatAuth
  rw [Auth.both_dfrac_valid_discrete]
  constructor
  · rintro ⟨hdq, _, _⟩
    exact hdq
  · intro hdq
    exact ⟨hdq, CMRA.inc_refl _, trivial⟩

theorem monoNatAuthValid (n : Nat) :
    ✓ (monoNatAuth (Q := Q) (DFrac.own (1 : Q)) n) := by
  rw [monoNatAuthDfracValid]
  exact DFrac.valid_own_one

theorem monoNatBothDfracValid (dq : DFrac Q) (n m : Nat) :
    ✓ (monoNatAuth (Q := Q) dq n • monoNatLb (Q := Q) m) ↔ ✓ dq ∧ m ≤ n := by
  let a : MaxNat := (n : MaxNat)
  let b : MaxNat := (m : MaxNat)
  have hEq :
      monoNatAuth (Q := Q) dq n • monoNatLb (Q := Q) m ≡
        (((Auth.auth dq a) • Auth.frag ((a • b : MaxNat))) : MonoNatRes Q) := by
    unfold monoNatAuth monoNatLb
    have hAssoc :
        (((Auth.auth dq a) • Auth.frag a) • Auth.frag b : MonoNatRes Q) ≡
          ((Auth.auth dq a) • (Auth.frag a • Auth.frag b) : MonoNatRes Q) := assoc.symm
    have hFrag :
        ((Auth.auth dq a) • (Auth.frag a • Auth.frag b) : MonoNatRes Q) ≡
          (((Auth.auth dq a) • Auth.frag ((a • b : MaxNat))) : MonoNatRes Q) := by
            exact (OFE.Equiv.of_eq (Auth.frag_op (F := Q) (b1 := a) (b2 := b)).symm).op_r
    exact hAssoc.trans hFrag
  rw [CMRA.valid_iff hEq, Auth.both_dfrac_valid_discrete]
  constructor
  · rintro ⟨hdq, hinc, _⟩
    have hle : Nat.max n m ≤ n := (MaxNat.included _ _).1 hinc
    exact ⟨hdq, (Nat.max_le.mp hle).2⟩
  · rintro ⟨hdq, hle⟩
    refine ⟨hdq, ?_, trivial⟩
    exact (MaxNat.included _ _).2 <| Nat.max_le.mpr ⟨Nat.le_refl _, hle⟩

theorem monoNatBothValid (n m : Nat) :
    ✓ (monoNatAuth (Q := Q) (DFrac.own (1 : Q)) n • monoNatLb (Q := Q) m) ↔ m ≤ n := by
  rw [monoNatBothDfracValid]
  constructor
  · exact fun ⟨_, h⟩ => h
  · exact fun h => ⟨DFrac.valid_own_one, h⟩

theorem monoNatLbMono (n1 n2 : Nat) :
    n1 ≤ n2 → monoNatLb (Q := Q) n1 ≼ monoNatLb (Q := Q) n2 := by
  intro h
  exact Auth.frag_inc_of_inc ((MaxNat.included _ _).2 h)

theorem monoNatIncluded (dq : DFrac Q) (n : Nat) :
    monoNatLb (Q := Q) n ≼ monoNatAuth (Q := Q) dq n := by
  unfold monoNatLb monoNatAuth
  exact ⟨Auth.auth dq ((n : Nat) : MaxNat), comm⟩

theorem monoNatUpdate {n : Nat} (n' : Nat) :
    n ≤ n' → monoNatAuth (Q := Q) (DFrac.own (1 : Q)) n ~~> monoNatAuth (DFrac.own (1 : Q)) n' := by
  intro h
  unfold monoNatAuth
  exact Auth.auth_update (MaxNat.localUpdate (((n : Nat) : MaxNat)) (((n : Nat) : MaxNat)) (((n' : Nat) : MaxNat)) h)

theorem monoNatAuthPersist (dq : DFrac Q) (n : Nat) :
    monoNatAuth (Q := Q) dq n ~~> monoNatAuth DFrac.discard n := by
  unfold monoNatAuth
  exact Update.op (Auth.auth_update_auth_persist (F := Q) (dq := dq) (a := ((n : Nat) : MaxNat))) Update.id

theorem monoNatAuthUnpersist [IsSplitFraction Q] (n : Nat) :
    monoNatAuth (Q := Q) DFrac.discard n ~~>:
      fun k => ∃ q, k = monoNatAuth (Q := Q) (DFrac.own q) n := by
  unfold monoNatAuth
  simpa using (Auth.auth_updateP_both_unpersist (F := Q)
    (a := ((n : Nat) : MaxNat)) (b := ((n : Nat) : MaxNat)))

end MonoNat

end Iris
