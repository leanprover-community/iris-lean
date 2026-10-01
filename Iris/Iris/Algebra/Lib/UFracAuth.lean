/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Markus de Medeiros
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.IsOp
public import Iris.Algebra.UFrac
import Iris.Algebra.LocalUpdates

/-!
# Unbounded Fractional Authoritative Camera

The unbounded fractional authoritative camera supports authoritative elements and fragments whose
fractions may exceed one. In addition to the usual fractional-authoritative operations, an
authoritative element can allocate a new fragment by increasing its fraction and adding the
fragment's resource to its payload.
-/

@[expose] public section

namespace Iris
open OFE ORA UORA Auth Iris.Option Iris.OFE.Option UFrac

/-! ## Definitions -/

@[rocq_alias ufrac_authR, rocq_alias ufrac_authUR]
abbrev UFracAuth [ORA A] := Auth (Option (UFrac × A))

namespace UFracAuth

variable [ORA A]

@[rocq_alias ufrac_auth_auth]
nonrec abbrev auth (q : Qp) (a : A) : UFracAuth (A := A) :=
  auth (.own 1) (some (⟨q⟩, a))

@[rocq_alias ufrac_auth_frag]
nonrec abbrev frag (q : Qp) (a : A) : UFracAuth (A := A) :=
  frag (some (⟨q⟩, a))

notation "●U{" q "} " a => auth q a
notation "◯U{" q "} " a => frag q a

/-! ## NonExpansive instances -/

@[rocq_alias ufrac_auth_auth_ne]
nonrec instance auth_ne {q : Qp} : NonExpansive (auth q : A → UFracAuth) where
  ne _ _ _ h := auth_ne.ne ⟨.rfl, h⟩

#rocq_ignore ufrac_auth_auth_proper "Derivable from auth_ne with NonExpansive.eqv"

@[rocq_alias ufrac_auth_frag_ne]
nonrec instance frag_ne {q : Qp} : NonExpansive (frag q : A → UFracAuth) where
  ne _ _ _ h := frag_ne.ne ⟨.rfl, h⟩

#rocq_ignore ufrac_auth_frag_proper "Derivable from frag_ne with NonExpansive.eqv"

/-! ## Discrete instances -/

@[rocq_alias ufrac_auth_auth_discrete]
instance auth_discrete {q : Qp} {a : A} [DiscreteE a] : DiscreteE (●U{q} a) :=
  letI _ : DiscreteE (unit : Option (UFrac × A)) := none_is_discrete
  by infer_instance

@[rocq_alias ufrac_auth_frag_discrete]
instance frag_discrete {q : Qp} {a : A} [DiscreteE a] : DiscreteE (◯U{q} a) :=
  by infer_instance

/-! ## Validity -/

@[rocq_alias ufrac_auth_validN]
theorem validN {n : Nat} {a : A} {p : Qp} (ha : ✓{n} a) : ✓{n} (●U{p} a) • ◯U{p} a :=
  both_validN_frame.mpr ⟨⟨none, ordN_refl _⟩, trivial, ha⟩

@[rocq_alias ufrac_auth_valid]
theorem valid {p : Qp} {a : A} (ha : ✓ a) : ✓ (●U{p} a) • ◯U{p} a :=
  auth_both_valid_2_ord ⟨trivial, ha⟩ (ord_refl _)

/-! ## Agreement -/

@[rocq_alias ufrac_auth_agreeN]
theorem agreeN {n : Nat} {p : Qp} {a b : A} (h : ✓{n} (●U{p} a) • ◯U{p} b) : a ≡{n}≡ b := by
  obtain ⟨⟨c, hc⟩, _⟩ := both_validN_frame.mp h
  match c, hc with
  | none, hc =>
    rcases some_ordN_some_iff.mp hc with e | i
    · exact e.2.symm
    · obtain ⟨r, hr⟩ := i.1
      have hp : p = p + r.frac := ext_iff.mp hr
      grind
  | some (r, _), hc =>
    rcases some_ordN_some_iff.mp hc with e | i
    · have hp : p + r.frac = p := ext_iff.mp e.1
      grind
    · obtain ⟨s, hs⟩ := i.1
      have hp : p = p + r.frac + s.frac := ext_iff.mp hs
      grind

@[rocq_alias ufrac_auth_agree]
theorem agree {p : Qp} {a b : A} (h : ✓ (●U{p} a) • ◯U{p} b) : a = b :=
  eq_dist_2 (agreeN <| valid_iff_validN.mp h ·)

#rocq_ignore ufrac_auth_agree_L "Use agree"

/-! ## Inclusion -/

theorem ordN_frame {n : Nat} {p q : Qp} {a b : A} (h : ✓{n} (●U{p} a) • ◯U{q} b) :
    ∃ c, some b • c ≼ₒ{n} some a := by
  obtain ⟨⟨c, hc⟩, _⟩ := both_validN_frame.mp h
  have snd {x : UFrac × A} (hx : some x ≼ₒ{n} some (⟨p⟩, a)) : some x.2 ≼ₒ{n} some a :=
    (some_ordN_some_iff.mp hx).elim (some_ordN_some_iff.mpr <| .inl ·.2)
      (some_ordN_some_iff.mpr <| .inr ·.2)
  match c, hc with
  | none, hc => exact ⟨none, snd hc⟩
  | some (_, d), hc => exact ⟨some d, snd hc⟩

theorem ordN [IncOrd A] {n : Nat} {p q : Qp} {a b : A}
    (h : ✓{n} (●U{p} a) • ◯U{q} b) : some b ≼ₒ{n} some a :=
  exists_op_ordN_iff_ordN.mp (ordN_frame h)

@[rocq_alias ufrac_auth_includedN]
theorem includedN [OrdInc A] {n : Nat} {p q : Qp} {a b : A}
    (h : ✓{n} (●U{p} a) • ◯U{q} b) : some b ≼{n} some a :=
  exists_op_ordN_iff_incN.mp (ordN_frame h)

theorem ord_frame [ORA.Discrete A] {q p : Qp} {a b : A} (h : ✓ (●U{p} a) • ◯U{q} b) :
    ∃ c, some b • c ≼ₒ some a := by
  obtain ⟨⟨c, hc⟩, _⟩ := auth_both_valid_discrete_frame.mp h
  have snd {x : UFrac × A} (hx : some x ≼ₒ some (⟨p⟩, a)) : some x.2 ≼ₒ some a :=
    (some_ord_some_iff.mp hx).elim (some_ord_some_iff.mpr <| .inl <| congrArg Prod.snd ·)
      (some_ord_some_iff.mpr <| .inr ·.2)
  match c, hc with
  | none, hc => exact ⟨none, snd hc⟩
  | some (_, d), hc => exact ⟨some d, snd hc⟩

theorem ord [ORA.Discrete A] [IncOrd A] {q p : Qp} {a b : A} (h : ✓ (●U{p} a) • ◯U{q} b) :
    some b ≼ₒ some a :=
  exists_op_ord_iff_ord.mp (ord_frame h)

@[rocq_alias ufrac_auth_included]
theorem included [ORA.Discrete A] [OrdInc A] {q p : Qp} {a b : A}
    (h : ✓ (●U{p} a) • ◯U{q} b) : some b ≼ some a :=
  exists_op_ord_iff_inc.mp (ord_frame h)

theorem ordN_total [OrderRefl A] [IncOrd A] {n : Nat} {q p : Qp} {a b : A}
    (h : ✓{n} (●U{p} a) • ◯U{q} b) : b ≼ₒ{n} a :=
  (Option.some_ordN_some_iff.mp (ordN h)).elim (·.to_ordN) id

@[rocq_alias ufrac_auth_includedN_total]
theorem includedN_total [OrderRefl A] [OrdInc A] {n : Nat} {q p : Qp} {a b : A}
    (h : ✓{n} (●U{p} a) • ◯U{q} b) : b ≼{n} a :=
  (dist_or_incN_of_some_incN_some (includedN h)).elim (OrdInc.ordN_incN ·.to_ordN) id

theorem ord_total [ORA.Discrete A] [OrderRefl A] [IncOrd A] {q p : Qp} {a b : A}
    (h : ✓ (●U{p} a) • ◯U{q} b) : b ≼ₒ a :=
  (Option.some_ord_some_iff.mp (ord h)).elim (· ▸ ord_refl b) id

@[rocq_alias ufrac_auth_included_total]
theorem included_total [ORA.Discrete A] [OrderRefl A] [OrdInc A] {q p : Qp} {a b : A}
    (h : ✓ (●U{p} a) • ◯U{q} b) : b ≼ a :=
  (eq_or_inc_of_some_inc_some (included h)).elim (· ▸ OrdInc.ord_inc (ord_refl b)) id

/-! ## Auth-only validity -/

@[rocq_alias ufrac_auth_auth_validN]
theorem auth_validN {n : Nat} {q : Qp} {a : A} : (✓{n} ●U{q} a) ↔ ✓{n} a := by
  rw [Auth.auth_validN]
  exact ⟨(·.2), (⟨trivial, ·⟩)⟩

@[rocq_alias ufrac_auth_auth_valid]
theorem auth_valid {q : Qp} {a : A} : (✓ ●U{q} a) ↔ ✓ a := by
  rw [Auth.auth_valid]
  exact ⟨(·.2), (⟨trivial, ·⟩)⟩

/-! ## Fragment-only validity -/

@[rocq_alias ufrac_auth_frag_validN]
theorem frag_validN {n : Nat} {q : Qp} {a : A} : (✓{n} ◯U{q} a) ↔ ✓{n} a := by
  rw [Auth.frag_validN]
  exact ⟨(·.2), (⟨trivial, ·⟩)⟩

@[rocq_alias ufrac_auth_frag_valid]
theorem frag_valid {q : Qp} {a : A} : (✓ ◯U{q} a) ↔ ✓ a := by
  rw [Auth.frag_valid]
  exact ⟨(·.2), (⟨trivial, ·⟩)⟩

/-! ## Operations -/

@[rocq_alias ufrac_auth_frag_op]
theorem frag_op {q1 q2 : Qp} {a1 a2 : A} : (◯U{q1 + q2} (a1 • a2)) = (◯U{q1} a1) • ◯U{q2} a2 := rfl

@[rocq_alias ufrac_auth_frag_op_validN]
theorem frag_op_validN {n : Nat} {q1 q2 : Qp} {a b : A} :
    (✓{n} (◯U{q1} a) • ◯U{q2} b) ↔ ✓{n} (a • b) := frag_validN

@[rocq_alias ufrac_auth_frag_op_valid]
theorem frag_op_valid {q1 q2 : Qp} {a b : A} : ✓ ((◯U{q1} a) • ◯U{q2} b) ↔ ✓ (a • b) := frag_valid

/-! ## IsOp type class instances -/

@[rocq_alias ufrac_auth_is_op]
instance isOp_ufrac_auth {q q1 q2 : Qp} {a1 a2 : A} {a : outParam A}
    [h1 : IsOp io q q1 q2] [h2 : IsOp io a a1 a2] : IsOp io (◯U{q} a) (◯U{q1} a1) (◯U{q2} a2) where
  is_op := calc
        ◯U{q} a
    _ = ◯U{q1 • q2} a := congrArg (frag · a) h1.is_op
    _ = ◯U{q1 • q2} a1 • a2 := congrArg _ h2.is_op

set_option synthInstance.checkSynthOrder false in
@[rocq_alias ufrac_auth_is_op_core_id]
instance isOp_ufrac_auth_core_id {q q1 q2 : Qp} {a : A} [h1 : CoreId a] [h2 : IsOp io q q1 q2] :
    IsOp io (◯U{q} a) (◯U{q1} a) (◯U{q2} a) where
  is_op := calc
        (◯U{q} a)
    _ = ◯U{q1 • q2} a := congrArg (frag · a) h2.is_op
    _ = ◯U{q1 • q2} a • a := congrArg _ (op_self a).symm

/-! ## Updates -/

@[rocq_alias ufrac_auth_update]
theorem update [OrdInc A] {p q : Qp} {a b a' b' : A} (h : (a, b) ~l~> (a', b')) :
    ((●U{p} a) • ◯U{q} b) ~~> (●U{p} a') • ◯U{q} b' :=
  auth_update (.option (.prod_2 _ _ h))

@[rocq_alias ufrac_auth_update_surplus]
theorem update_surplus {p q : Qp} {a b : A} (h : ✓ (a • b)) :
    (●U{p} a) ~~> (●U{p + q} (a • b)) • ◯U{q} b := by
  refine auth_update_alloc_ord fun n bf hinc _ => ⟨ordN_ne .rfl ?_ (op_monoN_right _ hinc),
    ⟨trivial, h.validN⟩⟩
  refine some_dist_some.mpr ⟨Dist.of_eq (UFrac.ext_iff.mpr ?_), comm.dist⟩
  change ((⟨q⟩ : UFrac) • ⟨p⟩).frac = p + q
  rw [frac_op]; grind

@[rocq_alias ufrac_auth_update_surplus_cancel]
theorem update_surplus_cancel [OrdInc A] {p q : Qp} {a b : A} [Cancelable b] :
    ((●U{p + q} (a • b)) • ◯U{q} b) ~~> ●U{p} a := by
  refine auth_update_dealloc
    (local_update_unital.mpr fun n mpa hv heq => ?_)
  match mpa with
  | none =>
    grind [show p + q = q from ext_iff.mp heq.1]
  | some (p', a') =>
    have hp : p = p'.frac := by grind [show p + q = q + p'.frac from ext_iff.mp heq.1]
    refine ⟨⟨trivial, validN_op_left hv.2⟩, ?_⟩
    refine ⟨.of_eq (ext_iff.mpr hp), ?_⟩
    refine cancelableN ?_ (op_commN.trans heq.2)
    exact (Dist.validN op_commN).mp hv.2

/-! ## Functors -/

@[rocq_alias ufrac_authURF]
abbrev UFracAuthURF (T : COFE.OFunctorPre) [RFunctor T] : COFE.OFunctorPre :=
  AuthURF (OptionOF (ProdOF (constOF UFrac) T))

#rocq_ignore ufrac_authURF_contractive "Found by typeclass inference"

@[rocq_alias ufrac_authRF]
abbrev UFracAuthRF (T : COFE.OFunctorPre) [RFunctor T] : COFE.OFunctorPre :=
  AuthRF (OptionOF (ProdOF (constOF UFrac) T))

#rocq_ignore ufrac_authRF_contractive "Found by typeclass inference"

end UFracAuth

end Iris
