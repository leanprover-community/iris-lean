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

open OFE CMRA Auth Excl

namespace ExclAuth

variable [UFraction F] [OFE A]

abbrev ExclAuthR := Auth F (Option (Excl A))
rocq_alias excl_authR := ExclAuth.ExclAuthR

abbrev ExclAuthUR := Auth F (Option (Excl A))
rocq_alias excl_authUR := ExclAuth.ExclAuthUR

abbrev auth (a : A) : ExclAuthR (F := F) (A := A) := ● (some (excl a))
rocq_alias excl_auth_auth := ExclAuth.auth

abbrev frag (a : A) : ExclAuthR (F := F) (A := A) := ◯ (some (excl a))
rocq_alias excl_auth_frag := ExclAuth.frag

scoped notation "●E " a => ExclAuth.auth a
scoped notation "◯E " a => ExclAuth.frag a

instance auth_ne : NonExpansive (auth (F := F) (A := A)) where
  ne _ _ _ h := Auth.auth_ne.ne (some_dist_some.mpr h)
rocq_alias excl_auth_auth_ne := ExclAuth.auth_ne

instance frag_ne : NonExpansive (frag (F := F) (A := A)) where
  ne _ _ _ h := Auth.frag_ne.ne (some_dist_some.mpr h)
rocq_alias excl_auth_frag_ne := ExclAuth.frag_ne

instance auth_discrete {a : A} [DiscreteE a] :
    DiscreteE (●E a : ExclAuthR (F := F) (A := A)) :=
  Auth.auth_discrete (Option.some_is_discrete inferInstance) Option.none_is_discrete
rocq_alias excl_auth_auth_discrete := ExclAuth.auth_discrete

instance frag_discrete {a : A} [DiscreteE a] :
    DiscreteE (◯E a : ExclAuthR (F := F) (A := A)) :=
  Auth.frag_discrete (Option.some_is_discrete inferInstance)
rocq_alias excl_auth_frag_discrete := ExclAuth.frag_discrete

theorem validN {n : Nat} {a : A} : ✓{n} ((●E a : ExclAuthR (F := F) (A := A)) • ◯E a) :=
  Auth.both_validN.mpr ⟨.rfl, trivial⟩
rocq_alias excl_auth_validN := ExclAuth.validN

theorem valid {a : A} : ✓ ((●E a : ExclAuthR (F := F) (A := A)) • ◯E a) :=
  Auth.auth_both_valid_2 trivial .rfl
rocq_alias excl_auth_valid := ExclAuth.valid

theorem agreeN {n : Nat} {a b : A} (h : ✓{n} ((●E a : ExclAuthR (F := F) (A := A)) • ◯E b)) :
    a ≡{n}≡ b :=
  (Option.dist_of_inc_exclusive (Auth.both_validN.mp h).1 trivial).symm
rocq_alias excl_auth_agreeN := ExclAuth.agreeN

theorem agree {a b : A} (h : ✓ ((●E a : ExclAuthR (F := F) (A := A)) • ◯E b)) : a ≡ b :=
  equiv_dist.mpr fun _ => agreeN (Valid.validN h)
rocq_alias excl_auth_agree := ExclAuth.agree

theorem agree_L [Leibniz A] {a b : A} (h : ✓ ((●E a : ExclAuthR (F := F) (A := A)) • ◯E b)) :
    a = b :=
  eq_of_eqv (agree h)
rocq_alias excl_auth_agree_L := ExclAuth.agree_L

theorem auth_op_validN {n : Nat} {a b : A} :
    (✓{n} ((●E a : ExclAuthR (F := F) (A := A)) • ●E b)) ↔ False :=
  Auth.auth_op_validN
rocq_alias excl_auth_auth_op_validN := ExclAuth.auth_op_validN

theorem auth_op_valid {a b : A} :
    (✓ ((●E a : ExclAuthR (F := F) (A := A)) • ●E b)) ↔ False :=
  Auth.auth_op_valid
rocq_alias excl_auth_auth_op_valid := ExclAuth.auth_op_valid

theorem frag_op_validN {n : Nat} {a b : A} :
    (✓{n} ((◯E a : ExclAuthR (F := F) (A := A)) • ◯E b)) ↔ False := by
  rw [show ((◯E a : ExclAuthR (F := F) (A := A)) • ◯E b) =
    (◯ (some (excl a) • some (excl b))) from Auth.frag_op.symm, Auth.frag_validN]
  exact ⟨fun h => Option.not_valid_some_exclN_op_left h, False.elim⟩
rocq_alias excl_auth_frag_op_validN := ExclAuth.frag_op_validN

theorem frag_op_valid {a b : A} :
    (✓ ((◯E a : ExclAuthR (F := F) (A := A)) • ◯E b)) ↔ False := by
  rw [show ((◯E a : ExclAuthR (F := F) (A := A)) • ◯E b) =
    (◯ (some (excl a) • some (excl b))) from Auth.frag_op.symm, Auth.frag_valid]
  exact ⟨fun h => Option.not_valid_some_exclN_op_left (n := 0) h.validN, False.elim⟩
rocq_alias excl_auth_frag_op_valid := ExclAuth.frag_op_valid

theorem update {a b a' : A} :
    ((●E a : ExclAuthR (F := F) (A := A)) • ◯E b) ~~> ((●E a') • ◯E a') :=
  Auth.auth_update (.option (.exclusive (x' := excl a') trivial))
rocq_alias excl_auth_update := ExclAuth.update

/-! ## Functors -/

abbrev ExclAuthURF (T : COFE.OFunctorPre) [URFunctor T] : COFE.OFunctorPre :=
  AuthURF (F := F) (OptionOF (ExclOF T))
rocq_alias excl_authURF := ExclAuth.ExclAuthURF

abbrev ExclAuthRF (T : COFE.OFunctorPre) [URFunctor T] : COFE.OFunctorPre :=
  AuthRF (F := F) (OptionOF (ExclOF T))
rocq_alias excl_authRF := ExclAuth.ExclAuthRF

end ExclAuth

end Iris
