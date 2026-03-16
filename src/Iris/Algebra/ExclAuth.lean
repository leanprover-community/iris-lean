/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Algebra.Auth
import Iris.Algebra.Excl
import Iris.Std.RocqAlias

/-!
# Exclusive Authoritative CMRA

Authoritative CMRA where the fragment is exclusively owned.
This is effectively a single "ghost variable" with two views, the fragment `◯E a`
and the authority `●E a`.
-/

namespace Iris

open OFE CMRA Auth Excl Option

namespace ExclAuth

variable [UFraction F] [OFE A]

@[rocq_alias excl_authR]
abbrev ExclAuthR := Auth F (Option (Excl A))

@[rocq_alias excl_authUR]
abbrev ExclAuthUR := Auth F (Option (Excl A))

@[rocq_alias excl_auth_auth]
abbrev auth (a : A) : ExclAuthR (F := F) (A := A) := ● (some (excl a))

@[rocq_alias excl_auth_frag]
abbrev frag (a : A) : ExclAuthR (F := F) (A := A) := ◯ (some (excl a))

scoped notation "●E " a => ExclAuth.auth a
scoped notation "◯E " a => ExclAuth.frag a

@[rocq_alias excl_auth_auth_ne]
instance auth_ne : NonExpansive (auth (F := F) (A := A)) where
  ne _ _ _ h := Auth.auth_ne.ne (some_dist_some.mpr h)

@[rocq_alias excl_auth_frag_ne]
instance frag_ne : NonExpansive (frag (F := F) (A := A)) where
  ne _ _ _ h := Auth.frag_ne.ne (some_dist_some.mpr h)

@[rocq_alias excl_auth_auth_discrete]
instance auth_discrete {a : A} [DiscreteE a] :
    DiscreteE (●E a : ExclAuthR (F := F) (A := A)) :=
  Auth.auth_discrete (some_is_discrete inferInstance) none_is_discrete

@[rocq_alias excl_auth_frag_discrete]
instance frag_discrete {a : A} [DiscreteE a] :
    DiscreteE (◯E a : ExclAuthR (F := F) (A := A)) :=
  Auth.frag_discrete (some_is_discrete inferInstance)

@[rocq_alias excl_auth_validN]
theorem validN {n : Nat} {a : A} : ✓{n} ((●E a : ExclAuthR (F := F) (A := A)) • ◯E a) :=
  Auth.both_validN.mpr ⟨.rfl, trivial⟩

@[rocq_alias excl_auth_valid]
theorem valid {a : A} : ✓ ((●E a : ExclAuthR (F := F) (A := A)) • ◯E a) :=
  Auth.auth_both_valid_2 trivial .rfl

@[rocq_alias excl_auth_agreeN]
theorem agreeN {n : Nat} {a b : A} (h : ✓{n} ((●E a : ExclAuthR (F := F) (A := A)) • ◯E b)) :
    a ≡{n}≡ b :=
  (dist_of_inc_exclusive (Auth.both_validN.mp h).1 trivial).symm

@[rocq_alias excl_auth_agree]
theorem agree {a b : A} (h : ✓ ((●E a : ExclAuthR (F := F) (A := A)) • ◯E b)) : a ≡ b :=
  equiv_dist.mpr fun _ => agreeN (Valid.validN h)

@[rocq_alias excl_auth_agree_L]
theorem agree_L [Leibniz A] {a b : A} (h : ✓ ((●E a : ExclAuthR (F := F) (A := A)) • ◯E b)) :
    a = b :=
  eq_of_eqv (agree h)

@[rocq_alias excl_auth_auth_op_validN]
theorem auth_op_validN {n : Nat} {a b : A} :
    (✓{n} ((●E a : ExclAuthR (F := F) (A := A)) • ●E b)) ↔ False :=
  Auth.auth_op_validN

@[rocq_alias excl_auth_auth_op_valid]
theorem auth_op_valid {a b : A} :
    (✓ ((●E a : ExclAuthR (F := F) (A := A)) • ●E b)) ↔ False :=
  Auth.auth_op_valid

@[rocq_alias excl_auth_frag_op_validN]
theorem frag_op_validN {n : Nat} {a b : A} :
    (✓{n} ((◯E a : ExclAuthR (F := F) (A := A)) • ◯E b)) ↔ False := by
  rw [show ((◯E a : ExclAuthR (F := F) (A := A)) • ◯E b) =
    (◯ (some (excl a) • some (excl b))) from Auth.frag_op.symm, Auth.frag_validN]
  exact ⟨fun h => not_valid_some_exclN_op_left h, False.elim⟩

@[rocq_alias excl_auth_frag_op_valid]
theorem frag_op_valid {a b : A} :
    (✓ ((◯E a : ExclAuthR (F := F) (A := A)) • ◯E b)) ↔ False := by
  rw [show ((◯E a : ExclAuthR (F := F) (A := A)) • ◯E b) =
    (◯ (some (excl a) • some (excl b))) from Auth.frag_op.symm, Auth.frag_valid]
  exact ⟨fun h => not_valid_some_exclN_op_left (n := 0) h.validN, False.elim⟩

@[rocq_alias excl_auth_update]
theorem update {a b a' : A} :
    ((●E a : ExclAuthR (F := F) (A := A)) • ◯E b) ~~> ((●E a') • ◯E a') :=
  Auth.auth_update (.option (.exclusive (x' := excl a') trivial))

/-! ## Functors -/

@[rocq_alias excl_authURF]
abbrev ExclAuthURF (T : COFE.OFunctorPre) [URFunctor T] : COFE.OFunctorPre :=
  AuthURF (F := F) (OptionOF (ExclOF T))

@[rocq_alias excl_authRF]
abbrev ExclAuthRF (T : COFE.OFunctorPre) [URFunctor T] : COFE.OFunctorPre :=
  AuthRF (F := F) (OptionOF (ExclOF T))

end ExclAuth

end Iris
