module

public import Iris.Instances.IProp
public import Iris.Std.HeapInstances

namespace Iris

open Iris Std HeapView

class GhostMapG (GF : BundledGFunctors)(F K V: Type _)(H : Type _ → Type _)
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
notation γ " ↪◯MAP[" k "]{" dq "}" v => ghost_map_elem γ dq k v

section lemmas

variable (F K V : Type _) (H : Type _ → Type _) [UFraction F] [LawfulPartialMap H K] [CMRA V]
variable [hgm: GhostMapG GF F K V H]

@[rocq_alias ghost_map_elem_timeless]
instance (γ : GName)(k: K)(dq: DFrac F)(v: V): BI.Timeless (ghost_map_elem (hgm := hgm) γ dq k v) :=
  iOwn_timeless (E := hgm.elem)

end lemmas
