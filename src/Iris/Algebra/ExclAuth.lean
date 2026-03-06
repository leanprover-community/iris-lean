import Iris.Algebra.Auth
import Iris.Algebra.Excl

namespace Iris

abbrev ExclAuth (Q : Type _) (A : Type _) [UFraction Q] [OFE A] :=
  Auth Q (Option (Excl A))

namespace ExclAuth

open COFE OFE CMRA Auth

variable {Q A : Type _} [UFraction Q] [OFE A]

def exclAuthAuth (a : A) : ExclAuth Q A :=
  ● (some (Excl.excl a))

def exclAuthFrag (a : A) : ExclAuth Q A :=
  ◯ (some (Excl.excl a))

theorem exclAuth_validN (n : Nat) (a : A) :
    ✓{n} (exclAuthAuth (Q := Q) a • exclAuthFrag a) := by
  change ✓{n} ((● (some (Excl.excl a)) : ExclAuth Q A) • ◯ some (Excl.excl a))
  rw [Auth.both_validN]
  exact ⟨CMRA.incN_refl _, trivial⟩

theorem exclAuth_valid (a : A) :
    ✓ (exclAuthAuth (Q := Q) a • exclAuthFrag a) := by
  change ✓ ((● (some (Excl.excl a)) : ExclAuth Q A) • ◯ some (Excl.excl a))
  exact Auth.auth_both_valid_2 trivial (CMRA.inc_refl _)

theorem exclAuth_agreeN (n : Nat) (a b : A) :
    ✓{n} (exclAuthAuth (Q := Q) a • exclAuthFrag b) → a ≡{n}≡ b := by
  intro h
  change ✓{n} ((● (some (Excl.excl a)) : ExclAuth Q A) • ◯ some (Excl.excl b)) at h
  have hboth := (Auth.both_validN (F := Q) (a := some (Excl.excl a)) (b := some (Excl.excl b))).1 h
  have hdist : (Excl.excl b : Excl A) ≡{n}≡ Excl.excl a :=
    Option.dist_of_inc_exclusive (a := Excl.excl b) (b := Excl.excl a) hboth.1 trivial
  simpa using hdist.symm

theorem exclAuth_agree (a b : A) :
    ✓ (exclAuthAuth (Q := Q) a • exclAuthFrag b) → a ≡ b := by
  intro h
  refine equiv_dist.mpr fun n => ?_
  exact exclAuth_agreeN (Q := Q) n a b h.validN

theorem exclAuth_agree_L [Leibniz A] (a b : A) :
    ✓ (exclAuthAuth (Q := Q) a • exclAuthFrag b) → a = b :=
  Leibniz.eq_of_eqv ∘ exclAuth_agree (Q := Q) a b

theorem exclAuth_auth_op_validN (n : Nat) (a b : A) :
    ✓{n} (exclAuthAuth (Q := Q) a • exclAuthAuth b) ↔ False := by
  change (✓{n} ((● (some (Excl.excl a)) : ExclAuth Q A) • ● some (Excl.excl b))) ↔ False
  simpa using (Auth.auth_op_validN (F := Q) (a1 := some (Excl.excl a)) (a2 := some (Excl.excl b)))

theorem exclAuth_auth_op_valid (a b : A) :
    ✓ (exclAuthAuth (Q := Q) a • exclAuthAuth b) ↔ False := by
  change (✓ (((● (some (Excl.excl a)) : ExclAuth Q A) • ● some (Excl.excl b)))) ↔ False
  simpa using (Auth.auth_op_valid (F := Q) (a1 := some (Excl.excl a)) (a2 := some (Excl.excl b)))

theorem exclAuth_frag_op_validN (n : Nat) (a b : A) :
    ✓{n} (exclAuthFrag (Q := Q) a • exclAuthFrag b) ↔ False := by
  constructor
  · intro h
    change ✓{n} ((◯ (some (Excl.excl a)) : ExclAuth Q A) • ◯ some (Excl.excl b)) at h
    have h' :=
      (Auth.frag_op_validN (F := Q) (b1 := some (Excl.excl a)) (b2 := some (Excl.excl b))).1 h
    exact Option.not_valid_some_exclN_op_left (x := Excl.excl a) (y := Excl.excl b) h'
  · intro h
    exact False.elim h

theorem exclAuth_frag_op_valid (a b : A) :
    ✓ (exclAuthFrag (Q := Q) a • exclAuthFrag b) ↔ False := by
  constructor
  · intro h
    exact (exclAuth_frag_op_validN (Q := Q) 0 a b).1 (h 0)
  · intro h
    exact False.elim h

theorem exclAuth_excl_local_update (a b a' : A) :
    ((some (Excl.excl a) : Option (Excl A)), some (Excl.excl b)) ~l~>
      (some (Excl.excl a'), some (Excl.excl a')) := by
  exact LocalUpdate.option (LocalUpdate.exclusive (y := Excl.excl b) trivial)

theorem exclAuth_update (a b a' : A) :
    exclAuthAuth (Q := Q) a • exclAuthFrag b ~~> exclAuthAuth a' • exclAuthFrag a' := by
  change ((● (some (Excl.excl a)) : ExclAuth Q A) • ◯ some (Excl.excl b)) ~~>
      ((● (some (Excl.excl a')) : ExclAuth Q A) • ◯ some (Excl.excl a'))
  exact Auth.auth_update (exclAuth_excl_local_update a b a')

abbrev ExclAuthURF (Q : Type _) [UFraction Q] (T : COFE.OFunctorPre) [COFE.OFunctor T] :
    COFE.OFunctorPre :=
  AuthURF (F := Q) (OptionOF (ExclOF T))

instance {T} [COFE.OFunctor T] : URFunctor (ExclAuthURF (Q := Q) T) := by
  let _ : RFunctor (ExclOF T) := inferInstance
  simpa [ExclAuthURF] using
    (inferInstance : URFunctor (AuthURF (F := Q) (OptionOF (ExclOF T))))

instance {T} [COFE.OFunctorContractive T] : URFunctorContractive (ExclAuthURF (Q := Q) T) := by
  let _ : RFunctor (ExclOF T) := inferInstance
  let _ : RFunctorContractive (ExclOF T) := inferInstance
  simpa [ExclAuthURF] using
    (inferInstance : URFunctorContractive (AuthURF (F := Q) (OptionOF (ExclOF T))))

abbrev ExclAuthRF (Q : Type _) [UFraction Q] (T : COFE.OFunctorPre) [COFE.OFunctor T] :
    COFE.OFunctorPre :=
  AuthRF (F := Q) (OptionOF (ExclOF T))

instance {T} [COFE.OFunctor T] : RFunctor (ExclAuthRF (Q := Q) T) := by
  let _ : RFunctor (ExclOF T) := inferInstance
  simpa [ExclAuthRF] using
    (inferInstance : RFunctor (AuthRF (F := Q) (OptionOF (ExclOF T))))

instance {T} [COFE.OFunctorContractive T] : RFunctorContractive (ExclAuthRF (Q := Q) T) := by
  let _ : RFunctor (ExclOF T) := inferInstance
  let _ : RFunctorContractive (ExclOF T) := inferInstance
  simpa [ExclAuthRF] using
    (inferInstance : RFunctorContractive (AuthRF (F := Q) (OptionOF (ExclOF T))))

end ExclAuth

end Iris
