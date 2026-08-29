/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.Lib.MonoList
public import Iris.BI
public import Iris.BI.Lib.Fractional
public import Iris.ProofMode
public import Iris.Instances.IProp

/-!
# Ghost state for append-only lists

Wraps the `MonoList` RA, providing three assertions:
- an authoritative proposition `γ ↪●ML{dq} l` for the authoritative list `l`;
- a persistent assertion `γ ↪◯ML l` witnessing that the authoritative list is at least `l`;
- a persistent assertion `γ ↪◯ML[i] a` witnessing that index `i` holds `a`.
-/

@[expose] public section

namespace Iris

open BI MonoList

@[rocq_alias mono_listG]
class MonoListG (GF : BundledGFunctors) (α : Type _) where
  elem : ElemG GF (constOF (MonoList (DiscreteO α)))

attribute [reducible, instance] MonoListG.elem

#rocq_ignore «mono_listΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore «subG_mono_listΣ» "Subsumed by BundledGFunctors typeclass synthesis"

namespace MonoList

variable {GF : BundledGFunctors} {α : Type _} [MonoListG GF α]

/-! ## Helper functions -/

theorem map_mk_inj : ∀ {l1 l2 : List α}, l1.map DiscreteO.mk = l2.map DiscreteO.mk → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [DiscreteO.eqv_inj h.1, map_mk_inj h.2]

theorem map_mk_prefix {l1 l2 : List α} (h : l1.map DiscreteO.mk <+: l2.map DiscreteO.mk) :
    l1 <+: l2 := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨a, b, rfl, ha, _⟩ := List.map_eq_append_iff.mp ht.symm
  exact ⟨b, by rw [map_mk_inj ha]⟩

theorem prefix_getElem? {l1 l2 : List α} {i : Nat} {a : α} (h : l1 <+: l2)
    (hi : l1[i]? = some a) : l2[i]? = some a := by
  obtain ⟨t, rfl⟩ := h
  grind

/-! ## Definitions -/

@[rocq_alias mono_list_auth_own]
def auth_own (γ : GName) (dq : DFrac) (l : List α) : IProp GF :=
  iOwn (E := MonoListG.elem) γ (auth dq (l.map DiscreteO.mk))

#rocq_ignore mono_list_auth_own_def "Not needed"
#rocq_ignore mono_list_auth_own_aux "Not needed"
#rocq_ignore mono_list_auth_own_unseal "Not needed"

@[rocq_alias mono_list_lb_own]
def lb_own (γ : GName) (l : List α) : IProp GF :=
  iOwn (E := MonoListG.elem) γ (lb (l.map DiscreteO.mk))

#rocq_ignore mono_list_lb_own_def "Not needed"
#rocq_ignore mono_list_lb_own_aux "Not needed"
#rocq_ignore mono_list_lb_own_unseal "Not needed"

notation γ " ↪●ML{" dq "} " l => auth_own γ dq l
notation γ " ↪●ML " l => auth_own γ (DFrac.own 1) l
notation γ " ↪●ML□ " l => auth_own γ DFrac.discard l
notation γ " ↪◯ML " l => lb_own γ l

@[rocq_alias mono_list_idx_own]
def idx_own (γ : GName) (i : Nat) (a : α) : IProp GF := iprop%
  ∃ l, ⌜l[i]? = some a⌝ ∗ lb_own γ l

notation γ " ↪◯ML[" i "] " a => idx_own γ i a

/-! ## Instances -/

@[rocq_alias mono_list_auth_own_timeless]
instance {γ dq} {l : List α} : Timeless (PROP := IProp GF) (γ ↪●ML{dq} l) := by
  unfold auth_own
  infer_instance

@[rocq_alias mono_list_auth_own_persistent]
instance {γ} {l : List α} : Persistent (PROP := IProp GF) (γ ↪●ML□ l) := by
  unfold auth_own
  infer_instance

@[rocq_alias mono_list_lb_own_timeless]
instance {γ} {l : List α} : Timeless (PROP := IProp GF) (γ ↪◯ML l) := by
  unfold lb_own
  infer_instance

@[rocq_alias mono_list_lb_own_persistent]
instance {γ} {l : List α} : Persistent (PROP := IProp GF) (γ ↪◯ML l) := by
  unfold lb_own
  infer_instance

@[rocq_alias mono_list_idx_own_timeless]
instance {γ i} {a : α} : Timeless (PROP := IProp GF) (γ ↪◯ML[i] a) := by
  unfold idx_own
  infer_instance

@[rocq_alias mono_list_idx_own_persistent]
instance {γ i} {a : α} : Persistent (PROP := IProp GF) (γ ↪◯ML[i] a) := by
  unfold idx_own
  infer_instance

@[rocq_alias mono_list_auth_own_fractional]
instance {γ} {l : List α} :
    Fractional (PROP := IProp GF) (fun q : Qp => γ ↪●ML{.own q} l) where
  fractional p q := by
    unfold auth_own
    rw [← iOwn_op.to_eq]
    exact (congrArg (iOwn _) (auth_dfrac_op (.own p) (.own q) _)).to_bi

@[rocq_alias mono_list_auth_own_as_fractional]
instance {γ} {l : List α} q :
   AsFractional (PROP := IProp GF) (γ ↪●ML{.own q} l) ioΦ (γ ↪●ML{.own ·} l) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := inferInstance

/-! ## Agreement -/

@[rocq_alias mono_list_auth_own_agree]
theorem auth_own_agree (γ : GName) (dq1 dq2 : DFrac) (l1 l2 : List α) :
    ⊢@{IProp GF} (γ ↪●ML{dq1} l1) -∗ (γ ↪●ML{dq2} l2) -∗
      ⌜✓ (dq1 • dq2) ∧ l1 = l2⌝ := by
  unfold auth_own
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  obtain ⟨hdq, hl⟩ := (auth_dfrac_op_valid ..).mp Hvalid
  exact ⟨hdq, map_mk_inj hl⟩

@[rocq_alias mono_list_auth_own_exclusive]
theorem auth_own_exclusive (γ : GName) (l1 l2 : List α) :
    ⊢@{IProp GF} (γ ↪●ML l1) -∗ (γ ↪●ML l2) -∗ False := by
  unfold auth_own
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  exact (auth_op_valid ..).mp Hvalid

@[rocq_alias mono_list_auth_lb_own_valid]
theorem auth_lb_own_valid (γ : GName) (dq : DFrac) (l1 l2 : List α) :
    ⊢@{IProp GF} (γ ↪●ML{dq} l1) -∗ (γ ↪◯ML l2) -∗ ⌜✓ dq ∧ l2 <+: l1⌝ := by
  unfold auth_own lb_own
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  obtain ⟨hdq, hpre⟩ := (both_dfrac_valid ..).mp Hvalid
  exact ⟨hdq, map_mk_prefix hpre⟩

@[rocq_alias mono_list_lb_own_valid]
theorem lb_own_valid (γ : GName) (l1 l2 : List α) :
    ⊢@{IProp GF} (γ ↪◯ML l1) -∗ (γ ↪◯ML l2) -∗ ⌜l1 <+: l2 ∨ l2 <+: l1⌝ := by
  unfold lb_own
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  exact (lb_op_valid ..).mp Hvalid |>.imp map_mk_prefix map_mk_prefix

@[rocq_alias mono_list_idx_agree]
theorem idx_agree (γ : GName) (i : Nat) (a1 a2 : α) :
    ⊢@{IProp GF} (γ ↪◯ML[i] a1) -∗ (γ ↪◯ML[i] a2) -∗ ⌜a1 = a2⌝ := by
  unfold idx_own
  iintro H1 H2
  icases H1 with ⟨%l1, %Hl1, H1⟩
  icases H2 with ⟨%l2, %Hl2, H2⟩
  icases lb_own_valid γ l1 l2 $$ H1 H2 with %Hpre
  ipureintro
  grind [prefix_getElem?]

@[rocq_alias mono_list_auth_idx_lookup]
theorem auth_idx_lookup (γ : GName) (dq : DFrac) (l : List α) (i : Nat) (a : α) :
    ⊢@{IProp GF} (γ ↪●ML{dq} l) -∗ (γ ↪◯ML[i] a) -∗ ⌜l[i]? = some a⌝ := by
  unfold idx_own
  iintro H1 H2
  icases H2 with ⟨%l1, %Hl1, H2⟩
  icases auth_lb_own_valid γ dq l l1 $$ H1 H2 with %Hpre
  ipureintro
  exact prefix_getElem? Hpre.2 Hl1

/-! ## Snapshots -/

@[rocq_alias mono_list_lb_own_get]
theorem lb_own_get (γ : GName) (dq : DFrac) (l : List α) :
    ⊢@{IProp GF} (γ ↪●ML{dq} l) -∗ (γ ↪◯ML l) := by
  unfold auth_own lb_own
  iintro H
  iapply iOwn_mono $$ H
  exact included ..

@[rocq_alias mono_list_lb_own_le]
theorem lb_own_le (γ : GName) {l : List α} (l' : List α) (h : l' <+: l) :
    ⊢@{IProp GF} (γ ↪◯ML l) -∗ (γ ↪◯ML l') := by
  unfold lb_own
  iintro H
  iapply iOwn_mono $$ H
  exact lb_mono (h.map _)

@[rocq_alias mono_list_lb_own_nil]
theorem lb_own_nil (γ : GName) : ⊢@{IProp GF} |==> (γ ↪◯ML ([] : List α)) := by
  unfold lb_own
  rw [List.map_nil]
  iapply iOwn_unit

@[rocq_alias mono_list_idx_own_get]
theorem idx_own_get (γ : GName) {l : List α} (i : Nat) (a : α) (h : l[i]? = some a) :
    ⊢@{IProp GF} (γ ↪◯ML l) -∗ (γ ↪◯ML[i] a) := by
  unfold idx_own
  iintro H
  iexists l
  iframe H %h

/-! ## Allocation and updates -/

@[rocq_alias mono_list_own_alloc]
theorem own_alloc (l : List α) :
    ⊢@{IProp GF} |==> ∃ γ, (γ ↪●ML l) ∗ (γ ↪◯ML l) := by
  unfold auth_own lb_own
  imod iOwn_alloc (F := constOF (MonoList (DiscreteO α)))
      (●ML (l.map DiscreteO.mk) • ◯ML (l.map DiscreteO.mk)) with ⟨%γ, H⟩
  · exact (both_valid ..).mpr List.prefix_rfl
  imodintro
  iexists γ
  icases iOwn_op $$ H with ⟨$, $⟩

@[rocq_alias mono_list_auth_own_update]
theorem auth_own_update (γ : GName) {l : List α} (l' : List α) (h : l <+: l') :
    ⊢@{IProp GF} (γ ↪●ML l) ==∗ (γ ↪●ML l') ∗ (γ ↪◯ML l') := by
  iintro H
  ihave >Hauth : |==> (γ ↪●ML l') $$ [H]
  · unfold auth_own
    iapply iOwn_update $$ H
    exact update _ (h.map _)
  · ihave #$ := lb_own_get $$ Hauth
    iframe

@[rocq_alias mono_list_auth_own_update_app]
theorem auth_own_update_app (γ : GName) {l : List α} (l' : List α) :
    ⊢@{IProp GF} (γ ↪●ML l) ==∗ (γ ↪●ML (l ++ l')) ∗ (γ ↪◯ML (l ++ l')) :=
  auth_own_update γ (l ++ l') (List.prefix_append ..)

@[rocq_alias mono_list_auth_own_persist]
theorem auth_own_persist (γ : GName) (dq : DFrac) (l : List α) :
    ⊢@{IProp GF} (γ ↪●ML{dq} l) ==∗ (γ ↪●ML□ l) := by
  unfold auth_own
  iintro H
  iapply iOwn_update $$ H
  exact auth_persist dq (l.map DiscreteO.mk)

@[rocq_alias mono_list_auth_own_unpersist]
theorem auth_own_unpersist (γ : GName) (l : List α) :
    ⊢@{IProp GF} (γ ↪●ML□ l) ==∗ ∃ q, γ ↪●ML{DFrac.own q} l := by
  unfold auth_own
  iintro H
  imod iOwn_updateP (auth_unpersist _) $$ H with ⟨%a, %⟨q, rfl⟩, H⟩
  iexists q
  iframe

end MonoList

end Iris
