/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.Excl

public section

/-!
# Exclusive Authoritative ORA

Authoritative ORA where the fragment is exclusively owned.
This is effectively a single "ghost variable" with two views, the fragment `◯E a`
and the authority `●E a`.
-/

namespace Iris

variable {SI : Type _} [instSI : SIdx SI]

open OFE ORA Auth Excl Iris.Option Iris.OFE.Option

namespace ExclAuth

variable [OFE SI A]

@[rocq_alias excl_authR]
abbrev ExclAuthR := Auth (SI := SI) (Option (Excl A))

@[rocq_alias excl_authUR]
abbrev ExclAuthUR := Auth (SI := SI) (Option (Excl A))

@[rocq_alias excl_auth_auth]
abbrev auth (a : A) : ExclAuthR (SI := SI) (A := A) := ● (some (excl a))

@[rocq_alias excl_auth_frag]
abbrev frag (a : A) : ExclAuthR (SI := SI) (A := A) := ◯ (some (excl a))

scoped notation "●E " a => ExclAuth.auth a
scoped notation "◯E " a => ExclAuth.frag a

@[rocq_alias excl_auth_auth_ne]
instance auth_ne : NonExpansive SI (auth (SI := SI) (A := A)) where
  ne _ _ _ h := Auth.auth_ne.ne (some_dist_some.mpr h)

#rocq_ignore excl_auth_auth_proper "Derivable from auth_ne with NonExpansive.eqv"

@[rocq_alias excl_auth_frag_ne]
instance frag_ne : NonExpansive SI (frag (SI := SI) (A := A)) where
  ne _ _ _ h := Auth.frag_ne.ne (some_dist_some.mpr h)
#rocq_ignore excl_auth_frag_proper "Derivable from frag_ne with NonExpansive.eqv"

@[rocq_alias excl_auth_auth_discrete]
instance auth_discrete {a : A} [DiscreteE SI a] : DiscreteE SI (●E a : ExclAuthR (SI := SI)) :=
  letI _ : DiscreteE SI (some (excl a)) := some_is_discrete
  letI _ : DiscreteE SI (unit : Option (Excl A)) := none_is_discrete
  by infer_instance

@[rocq_alias excl_auth_frag_discrete]
instance frag_discrete {a : A} [DiscreteE SI a] : DiscreteE SI (◯E a : ExclAuthR (SI := SI)) :=
  letI _ : DiscreteE SI (some (excl a)) := some_is_discrete
  by infer_instance

@[rocq_alias excl_auth_validN]
theorem validN {n : SI} {a : A} : ✓{n} (●E a : ExclAuthR (SI := SI)) • ◯E a :=
  Auth.both_validN.mpr ⟨.rfl, trivial⟩

@[rocq_alias excl_auth_valid]
theorem valid {a : A} : ✓[SI] (●E a : ExclAuthR (SI := SI)) • ◯E a :=
  Auth.auth_both_valid_2 trivial .rfl

@[rocq_alias excl_auth_agreeN]
theorem agreeN {n : SI} {a b : A} (h : ✓{n} (●E a : ExclAuthR (SI := SI)) • ◯E b) : a ≡{n}≡ b :=
  dist_of_inc_exclusive (Auth.both_validN.mp h).1 trivial |>.symm

@[rocq_alias excl_auth_agree]
theorem agree {a b : A} (h : ✓[SI] (●E a : ExclAuthR (SI := SI)) • ◯E b) : a = b :=
  OFE.eq_dist_2 fun _ => agreeN (Valid.validN h)

#rocq_ignore excl_auth_agree_L "Use agree"

@[rocq_alias excl_auth_auth_op_validN]
theorem auth_op_validN {n : SI} {a b : A} : (✓{n} (●E a : ExclAuthR (SI := SI)) • ●E b) ↔ False :=
  Auth.auth_op_validN

@[rocq_alias excl_auth_auth_op_valid]
theorem auth_op_valid {a b : A} : (✓[SI] (●E a : ExclAuthR (SI := SI)) • ●E b) ↔ False :=
  Auth.auth_op_valid (SI := SI)

@[rocq_alias excl_auth_frag_op_validN]
theorem frag_op_validN {n : SI} {a b : A} : (✓{n} (◯E a : ExclAuthR (SI := SI)) • ◯E b) ↔ False := by
  suffices H : ✓{n} some (excl a) • some (excl b) ↔ False by rwa [Auth.frag_op.symm, Auth.frag_validN]
  exact ⟨not_valid_some_exclN_op_left, False.elim⟩

@[rocq_alias excl_auth_frag_op_valid]
theorem frag_op_valid {a b : A} : (✓[SI] (◯E a : ExclAuthR (SI := SI)) • ◯E b) ↔ False := by
  suffices H : ✓[SI] some (excl a) • some (excl b) ↔ False by rwa [Auth.frag_op.symm, Auth.frag_valid]
  exact ⟨fun h => not_valid_some_exclN_op_left (n := 0) h.validN, False.elim⟩

@[rocq_alias excl_auth_update]
theorem update {a b a' : A} : ((●E a : ExclAuthR (SI := SI)) • ◯E b) ~~>[SI] ((●E a') • ◯E a') :=
  Auth.auth_update (.option (.exclusive trivial))

/-! ## Functors -/

@[rocq_alias excl_authURF]
abbrev ExclAuthURF (T : COFE.OFunctorPre SI) [COFE.OFunctor SI T] : COFE.OFunctorPre SI :=
  AuthURF (OptionOF (SI := SI) (ExclOF T))

#rocq_ignore excl_authURF_contractive "Found by typeclass inference"

@[rocq_alias excl_authRF]
abbrev ExclAuthRF (T : COFE.OFunctorPre SI) [COFE.OFunctor SI T] : COFE.OFunctorPre SI :=
  AuthRF (OptionOF (SI := SI) (ExclOF T))

#rocq_ignore excl_authRF_contractive "Found by typeclass inference"

end ExclAuth
end Iris
