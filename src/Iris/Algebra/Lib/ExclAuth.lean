/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.Excl
meta import Iris.Std.RocqAlias

/-!
# Exclusive Authoritative CMRA

Authoritative CMRA where the fragment is exclusively owned.
This is effectively a single "ghost variable" with two views, the fragment `◯E a`
and the authority `●E a`.
-/

namespace Iris

open OFE CMRA Auth Excl Option

namespace ExclAuth

variable [OFE A]

@[rocq_alias excl_authR]
public abbrev ExclAuthR := Auth PNat (Option (Excl A))

@[rocq_alias excl_authUR]
public abbrev ExclAuthUR := Auth PNat (Option (Excl A))

@[rocq_alias excl_auth_auth]
public abbrev auth (a : A) : ExclAuthR (A := A) := ● (some (excl a))

@[rocq_alias excl_auth_frag]
public abbrev frag (a : A) : ExclAuthR (A := A) := ◯ (some (excl a))

scoped notation "●E " a => ExclAuth.auth a
scoped notation "◯E " a => ExclAuth.frag a

@[rocq_alias excl_auth_auth_ne]
instance auth_ne : NonExpansive (auth (A := A)) where
  ne _ _ _ h := Auth.auth_ne.ne (some_dist_some.mpr h)

@[rocq_alias excl_auth_frag_ne]
instance frag_ne : NonExpansive (frag (A := A)) where
  ne _ _ _ h := Auth.frag_ne.ne (some_dist_some.mpr h)

@[rocq_alias excl_auth_auth_discrete]
instance auth_discrete {a : A} [DiscreteE a] : DiscreteE (●E a) :=
  Auth.auth_discrete (some_is_discrete inferInstance) none_is_discrete

@[rocq_alias excl_auth_frag_discrete]
instance frag_discrete {a : A} [DiscreteE a] : DiscreteE (◯E a) :=
  Auth.frag_discrete (some_is_discrete inferInstance)

@[rocq_alias excl_auth_validN]
theorem validN {a : A} : ✓{n} (●E a) • ◯E a :=
  Auth.both_validN.mpr ⟨.rfl, trivial⟩

@[rocq_alias excl_auth_valid]
theorem valid {a : A} : ✓ (●E a) • ◯E a :=
  Auth.auth_both_valid_2 trivial .rfl

@[rocq_alias excl_auth_agreeN]
theorem agreeN {a b : A} (h : ✓{n} (●E a) • ◯E b) : a ≡{n}≡ b :=
  dist_of_inc_exclusive (Auth.both_validN.mp h).1 trivial |>.symm

@[rocq_alias excl_auth_agree]
theorem agree {a b : A} (h : ✓ (●E a) • ◯E b) : a ≡ b :=
  equiv_dist.mpr fun _ => agreeN (Valid.validN h)

@[rocq_alias excl_auth_agree_L]
theorem agree_L [Leibniz A] {a b : A} (h : ✓ (●E a) • ◯E b) : a = b :=
  eq_of_eqv (agree h)

@[rocq_alias excl_auth_auth_op_validN]
theorem auth_op_validN {a b : A} : (✓{n} (●E a) • ●E b) ↔ False :=
  Auth.auth_op_validN

@[rocq_alias excl_auth_auth_op_valid]
theorem auth_op_valid {a b : A} : (✓ (●E a) • ●E b) ↔ False :=
  Auth.auth_op_valid

@[rocq_alias excl_auth_frag_op_validN]
theorem frag_op_validN {a b : A} : (✓{n} (◯E a) • ◯E b) ↔ False := by
  suffices H : ✓{n} some (excl a) • some (excl b) ↔ False by rwa [Auth.frag_op.symm, Auth.frag_validN]
  exact ⟨not_valid_some_exclN_op_left, False.elim⟩

@[rocq_alias excl_auth_frag_op_valid]
theorem frag_op_valid {a b : A} : (✓ (◯E a) • ◯E b) ↔ False := by
  suffices H : ✓ some (excl a) • some (excl b) ↔ False by rwa [Auth.frag_op.symm, Auth.frag_valid]
  exact ⟨fun h => not_valid_some_exclN_op_left (n := 0) h.validN, False.elim⟩

@[rocq_alias excl_auth_update]
theorem update {a b a' : A} : ((●E a) • ◯E b) ~~> ((●E a') • ◯E a') :=
  Auth.auth_update (.option (.exclusive trivial))

/-! ## Functors -/

@[rocq_alias excl_authURF]
abbrev ExclAuthURF (T : COFE.OFunctorPre) [URFunctor T] : COFE.OFunctorPre :=
  AuthURF (F := PNat) (OptionOF (ExclOF T))

@[rocq_alias excl_authRF]
abbrev ExclAuthRF (T : COFE.OFunctorPre) [URFunctor T] : COFE.OFunctorPre :=
  AuthRF (F := PNat) (OptionOF (ExclOF T))

end ExclAuth
end Iris
