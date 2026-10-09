/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.DFrac
public import Iris.Algebra.Agree

/-!
# The DFrac Agree Camera

The product of the discardable fraction camera and the agree camera, bundled with
convenience definitions and lemmas.
-/

@[expose] public section

namespace Iris

variable {SI : Type _} [instSI : SIdx SI]

open OFE ORA DFrac

namespace DFracAgree

@[nolint unusedArguments, rocq_alias dfrac_agreeR]
abbrev DFracAgreeR (A : Type _) [OFE SI A] := DFrac × Agree A

@[rocq_alias to_dfrac_agree]
def mk [OFE SI A] (d : DFrac) (a : A) : DFracAgreeR (SI := SI) A := (d, toAgree a)

variable {A : Type _} [OFE SI A]

instance mk_discarded_coreId {a : A} : CoreId (mk (SI := SI) .discard a) :=
  inferInstanceAs (CoreId (DFrac.discard, toAgree a))

@[rocq_alias to_dfrac_agree_ne]
instance mk_ne {d : DFrac} : NonExpansive SI (mk (SI := SI) d : A → DFracAgreeR A) where
  ne _ _ _ h := ⟨.rfl, NonExpansive.ne (f := toAgree) h⟩

#rocq_ignore to_dfrac_agree_proper "Derivable from mk_ne with NonExpansive.eqv"

@[rocq_alias to_dfrac_agree_exclusive]
instance mk_exclusive {a : A} : Exclusive SI (mk (SI := SI) (.own (1 : Qp)) a) := one_exclusive_left

theorem mk_valid {d : DFrac} {a : A} : ✓[SI] mk (SI := SI) d a ↔ ✓[SI] d :=
  ⟨And.left, (⟨·, Agree.toAgree_valid⟩)⟩

@[rocq_alias to_dfrac_agree_discrete]
instance mk_discrete {d : DFrac} {a : A} [DiscreteE SI a] : DiscreteE SI (mk (SI := SI) d a) :=
  ⟨fun h => Prod.ext (is_discrete.discrete h.1) (Agree.toAgree.is_discrete.discrete h.2)⟩

@[rocq_alias to_dfrac_agree_injN]
theorem mk_injN {n : SI} {d₁ d₂ : DFrac} {a₁ a₂ : A} (h : mk (SI := SI) d₁ a₁ ≡{n}≡ mk d₂ a₂) : d₁ ≡{n}≡ d₂ ∧ a₁ ≡{n}≡ a₂ :=
  ⟨h.1, toAgree.inj h.2⟩

@[rocq_alias to_dfrac_agree_inj]
theorem mk_inj {d₁ d₂ : DFrac} {a₁ a₂ : A} (h : mk (SI := SI) d₁ a₁ = mk d₂ a₂) : d₁ = d₂ ∧ a₁ = a₂ :=
  ⟨congrArg Prod.fst h, Agree.toAgree_inj (congrArg Prod.snd h)⟩

@[rocq_alias dfrac_agree_op]
theorem mk_op {d₁ d₂ : DFrac} {a : A} : mk (d₁ • d₂) a = mk (SI := SI) d₁ a • mk d₂ a :=
  equiv_prod_ext rfl Agree.idemp.symm

@[rocq_alias dfrac_agree_op_valid]
theorem op_valid {d₁ d₂ : DFrac} {a₁ a₂ : A} : ✓[SI] (mk (SI := SI) d₁ a₁ • mk d₂ a₂) ↔ ✓[SI] (d₁ • d₂) ∧ a₁ = a₂ := by
  simp only [Prod.op, ORA.op, mk]
  exact and_congr_right fun _ => toAgree_op_valid_iff_eq

#rocq_ignore dfrac_agree_op_valid_L "Use op_valid"

@[rocq_alias dfrac_agree_op_validN]
theorem op_validN {n : SI} {d₁ d₂ : DFrac} {a₁ a₂ : A} :
    ✓{n} (mk (SI := SI) d₁ a₁ • mk d₂ a₂) ↔ ✓[SI] (d₁ • d₂) ∧ a₁ ≡{n}≡ a₂ := by
  change Prod.ValidN n (Prod.op (mk d₁ a₁) (mk d₂ a₂)) ↔ _
  simp only [Prod.ValidN, mk]
  rw [Agree.toAgree_op_validN_iff_dist]
  exact and_congr_left' (valid_iff_validN' (α := DFrac) n)

theorem ord {d₁ d₂ : DFrac} {a₁ a₂ : A} :
    mk (SI := SI) d₁ a₁ ≼ₒ[SI] mk d₂ a₂ ↔ (d₁ ≼ₒ[SI] d₂) ∧ a₁ = a₂ :=
  and_congr_right' Agree.toAgree_ord

@[rocq_alias dfrac_agree_included]
theorem included {d₁ d₂ : DFrac} {a₁ a₂ : A} :
    mk (SI := SI) d₁ a₁ ≼ mk d₂ a₂ ↔ (d₁ ≼ d₂) ∧ a₁ = a₂ :=
  inc_iff_ord.trans ord

#rocq_ignore dfrac_agree_included_L "Use included"

theorem ordN {n : SI} {d₁ d₂ : DFrac} {a₁ a₂ : A} :
    mk (SI := SI) d₁ a₁ ≼ₒ{n} mk d₂ a₂ ↔ (d₁ ≼ₒ[SI] d₂) ∧ a₁ ≡{n}≡ a₂ :=
  and_congr (ord_iff_ordN (α := DFrac) n).symm Agree.toAgree_ordN

@[rocq_alias dfrac_agree_includedN]
theorem includedN {n : SI} {d₁ d₂ : DFrac} {a₁ a₂ : A} :
    mk (SI := SI) d₁ a₁ ≼{n} mk d₂ a₂ ↔ (d₁ ≼ d₂) ∧ a₁ ≡{n}≡ a₂ :=
  incN_iff_ordN.trans ordN

@[rocq_alias dfrac_agree_update_2]
theorem update₂ {d₁ d₂ : DFrac} {a₁ a₂ a' : A} (hd : d₁ • d₂ = .own 1) :
    mk d₁ a₁ • mk d₂ a₂ ~~>[SI] mk (SI := SI) d₁ a' • mk d₂ a' := by
  calc
    _ = (own (1 : Qp), toAgree a₁ • toAgree a₂) := hd ▸ rfl
    _ ~~>[SI] mk d₁ a' • mk d₂ a' :=
      have := one_exclusive_left (SI := SI) (v := toAgree a₁ • toAgree a₂)
      Update.exclusive (op_valid.mpr ⟨hd ▸ valid_own_one, rfl⟩)

@[rocq_alias dfrac_agree_persist]
theorem persist {d : DFrac} {a : A} : mk (SI := SI) d a ~~>[SI] mk .discard a := by
  intro n mz hv
  simp only [mk, op?] at hv ⊢
  rcases mz with _ | ⟨mz₁, mz₂⟩
  · exact ⟨DFrac.update_discard n none hv.1, hv.2⟩
  · exact ⟨DFrac.update_discard n (some mz₁) hv.1, hv.2⟩

@[rocq_alias dfrac_agree_unpersist]
theorem unpersist {a : A} :
    mk (.discard : DFrac) a ~~>:[SI] fun k => ∃ q, k = mk (SI := SI) (.own q) a := by
  intro n mz hv
  simp only [mk, op?] at hv ⊢
  rcases mz with _ | ⟨mz₁, mz₂⟩
  · obtain ⟨d', ⟨q, rfl⟩, hv'⟩ := DFrac.update_acquire n none hv.1
    exact ⟨(.own q, toAgree a), ⟨q, rfl⟩, hv', hv.2⟩
  · obtain ⟨d', ⟨q, rfl⟩, hv'⟩ := DFrac.update_acquire n (some mz₁) hv.1
    exact ⟨(.own q, toAgree a), ⟨q, rfl⟩, hv', hv.2⟩

/-! ## Frac variants -/

namespace Frac

@[rocq_alias to_frac_agree]
def mk [OFE SI A] (q : Qp) (a : A) : DFracAgreeR (SI := SI) A := DFracAgree.mk (.own q) a

variable {A : Type _} [OFE SI A]

@[rocq_alias frac_agree_op]
theorem mk_op {q₁ q₂ : Qp} {a : A} : mk (q₁ + q₂) a = mk (SI := SI) q₁ a • mk q₂ a :=
  DFracAgree.mk_op (d₁ := .own q₁) (d₂ := .own q₂)

@[rocq_alias frac_agree_op_valid]
theorem op_valid {q₁ q₂ : Qp} {a₁ a₂ : A} :
    ✓[SI] (mk (SI := SI) q₁ a₁ • mk q₂ a₂) ↔ (q₁ + q₂).val ≤ 1 ∧ a₁ = a₂ := DFracAgree.op_valid

#rocq_ignore frac_agree_op_valid_L "Use op_valid"

@[rocq_alias frac_agree_op_validN]
theorem op_validN {n : SI} {q₁ q₂ : Qp} {a₁ a₂ : A} :
    ✓{n} (mk (SI := SI) q₁ a₁ • mk q₂ a₂) ↔ (q₁ + q₂).val ≤ 1 ∧ a₁ ≡{n}≡ a₂ :=
  DFracAgree.op_validN

theorem ord {q₁ q₂ : Qp} {a₁ a₂ : A} :
    mk (SI := SI) q₁ a₁ ≼ₒ[SI] mk q₂ a₂ ↔ (own q₁ ≼ₒ[SI] own q₂) ∧ a₁ = a₂ := DFracAgree.ord

@[rocq_alias frac_agree_included]
theorem included {q₁ q₂ : Qp} {a₁ a₂ : A} :
    mk (SI := SI) q₁ a₁ ≼ mk q₂ a₂ ↔ (own q₁ ≼ own q₂) ∧ a₁ = a₂ := DFracAgree.included

#rocq_ignore frac_agree_included_L "Use included"

theorem ordN {n : SI} {q₁ q₂ : Qp} {a₁ a₂ : A} :
    mk (SI := SI) q₁ a₁ ≼ₒ{n} mk q₂ a₂ ↔ (own q₁ ≼ₒ[SI] own q₂) ∧ a₁ ≡{n}≡ a₂ := DFracAgree.ordN

@[rocq_alias frac_agree_includedN]
theorem includedN {n : SI} {q₁ q₂ : Qp} {a₁ a₂ : A} :
    mk (SI := SI) q₁ a₁ ≼{n} mk q₂ a₂ ↔ (own q₁ ≼ own q₂) ∧ a₁ ≡{n}≡ a₂ := DFracAgree.includedN

@[rocq_alias frac_agree_update_2]
theorem update₂ {q₁ q₂ : Qp} {a₁ a₂ a' : A} (hq : q₁ + q₂ = 1) :
    mk q₁ a₁ • mk q₂ a₂ ~~>[SI] mk (SI := SI) q₁ a' • mk q₂ a' :=
  DFracAgree.update₂ (show own q₁ • own q₂ = .own 1 from congrArg _ hq)

end Frac

/-! ## Functors -/

@[rocq_alias dfrac_agreeRF]
abbrev DFracAgreeRF (T : COFE.OFunctorPre SI) : COFE.OFunctorPre SI :=
  ProdOF (constOF (SI := SI) DFrac) (AgreeRF T)

#rocq_ignore dfrac_agreeRF_contractive "Found by typeclass inference"

end DFracAgree

end Iris
