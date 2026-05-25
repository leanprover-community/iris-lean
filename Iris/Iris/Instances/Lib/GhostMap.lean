module

public import Iris.Instances.IProp
public import Iris.Std.HeapInstances
public import Iris.BI.Lib.Fractional

namespace Iris

open Iris Std HeapView

class GhostMapG (GF : BundledGFunctors) (F: outParam (Type _))
    (K V: Type _)(H : outParam <| Type _ → Type _)
    [UFraction F][LawfulPartialMap H K] where
  elem: ElemG GF (constOF (HeapView F K (Agree (LeibnizO V)) H))

section definitions

variable [UFraction F][LawfulPartialMap H K][hgm: GhostMapG GF F K V H]

public def ghost_map_auth (γ : GName) (dq : DFrac F) (m : H V): IProp GF :=
  iOwn (E := hgm.elem) γ
    (HeapView.Auth dq (Iris.Std.PartialMap.map (fun x ↦ toAgree ⟨x⟩) m))

public def ghost_map_elem (γ : GName) (dq : DFrac F) (k: K) (v: V): IProp GF :=
  iOwn (E := hgm.elem) γ (HeapView.Frag k dq (toAgree ⟨v⟩))

end definitions

notation γ " ↪●MAP " dq m => ghost_map_auth γ dq m
notation γ " ↪◯MAP[" k "]{" dq "} " v => ghost_map_elem γ dq k v

section lemmas

variable (F K V : Type _) (H : Type _ → Type _) [UFraction F] [LawfulPartialMap H K] [CMRA V]
variable [hgm: GhostMapG GF F K V H]

@[rocq_alias ghost_map_elem_timeless]
instance (γ : GName)(k: K)(dq: DFrac F)(v: V): BI.Timeless (PROP := IProp GF) (γ ↪◯MAP[k]{dq} v) :=
  iOwn_timeless (E := hgm.elem)

instance (γ : GName)(k: K)(v: V): BI.Persistent (PROP := IProp GF) (γ ↪◯MAP[k]{.discard} v) := by
  unfold ghost_map_elem
  exact instPersistentIPropIOwnOfCoreIdAp (E := hgm.elem)

instance (γ : GName)(k: K)(v: V)
    : Fractional (PROP := IProp GF) iprop(fun q: F => γ ↪◯MAP[k]{.own q} v) where
  fractional p q := by
    unfold ghost_map_elem
    let ta := @toAgree (LeibnizO V) { car := v }
    have :
        Frag (H := H) k (DFrac.own (p + q)) (ta • ta) ≡
        Frag k (DFrac.own (p + q)) ta
      := OFE.NonExpansive.eqv Iris.Agree.idemp
    have := frag_add_op_equiv.symm.trans this
    have := (@iOwn_ne GF _ _ GhostMapG.elem γ).eqv this
    have := (BI.equiv_iff (PROP := IProp GF)).mp this
    exact this.symm.trans <| iOwn_op (E := hgm.elem)

end lemmas
