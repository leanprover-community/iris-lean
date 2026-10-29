module

public import IrisITree

@[expose] public section

namespace IrisITreeTest

open Iris BI IrisITree ITree CancelableInvariant

section iinv

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]
  {E : Effect} {R : Type} {H : IHandler (IProp GF) E}
  {N : Namespace} {P Q : IProp GF} (Φ : R → IProp GF) (r : R)

/-- Tests `iinv` with `elimInv_acc_without_close`, `elimAcc_wpi` and `intoAcc_inv`. -/
example : inv N iprop(<pers> P) -∗ Φ r -∗ WPi .ret r @> H; ⊤ {{ Φ }} := by
  iintro #Hinv HΦ
  iinv Hinv with #HP Hclose
  imod Hclose $$ HP
  iapply wpi_pure $$ HΦ

/-- Tests `iinv` with a timeless invariant: `>HP` strips the later via `isExcept0_wpi`. -/
example [Timeless P] : inv N P -∗ (P -∗ P ∗ Φ r) -∗ WPi .ret r @> H; ⊤ {{ Φ }} := by
  iintro #Hinv HΦ
  iinv Hinv with >HP
  icases HΦ $$ HP with ⟨HP, HΦ⟩
  iapply wpi_pure
  imodintro; iframe HP HΦ

/-- Tests `iinv` relying on the side condition `↑N ⊆ Ms`. -/
example {Ms : CoPset} (h : ↑N ⊆ Ms) :
    inv N iprop(<pers> P) -∗ Φ r -∗
    WPi .ret r @> H; Ms {{ Φ }} := by
  iintro #Hinv HΦ
  iinv Hinv with #HP
  iapply wpi_pure
  imodintro; iframe HP HΦ

/-- Tests that `iinv` keeps the end mask of a two-mask `WPi` goal. -/
example : inv N iprop(<pers> P) -∗ (|={⊤, ∅}=> Φ r) -∗
    WPi .ret r @> H; ⊤, ∅ {{ Φ }} := by
  iintro #Hinv HΦ
  iinv Hinv with #HP
  iapply wpi_pure
  imodintro; iframe HP HΦ

/-- Tests opening two invariants one after the other. -/
example {N₁ N₂ : Namespace} (h : ↑N₂ ⊆ (⊤ : CoPset) \ ↑N₁) :
    inv N₁ iprop(<pers> P) -∗ inv N₂ iprop(<pers> Q) -∗ Φ r -∗
    WPi .ret r @> H; ⊤ {{ Φ }} := by
  iintro #HinvP #HinvQ HΦ
  iinv HinvP with #HP
  iinv HinvQ with #HQ
  iapply wpi_pure
  imodintro; iframe HQ
  imodintro; iframe HP
  imodintro; iframe

/-- Tests `iinv` with `elimInv_acc_without_close`, `elimAcc_wpi` and `intoAcc_cinv`. -/
example [CInvG GF] {γ : GName} {p : Qp} {P : IProp GF} (Φ : R → IProp GF) (r : R) :
    cinv N γ iprop(<pers> P) -∗ own γ p -∗ Φ r -∗
    WPi .ret r @> H; ⊤ {{ v, own γ p ∗ Φ v }} := by
  iintro #Hinv Hown HΦ
  iinv Hinv with ⟨#HP, Hown⟩
  iapply wpi_pure
  imodintro; iframe HP; iframe

/- Tests `iinv` with an invalid invariant. -/
/-- error: iinv: invalid invariant P (ElimInv type class synthesis failed) -/
#guard_msgs in
example : □ P -∗ WPi .ret r @> H; ⊤ {{ Φ }} := by
  iintro #HP
  iinv HP with #HP'

end iinv

section heaplang

open Iris.HeapLang

variable {GF : BundledGFunctors} [InvGS GF] [heaplangHGS GF]
  {m : StepMod (IProp GF)} {N : Namespace}
  {P : IProp GF} (v : Val) (Φ : Val → IProp GF)

/-- Tests `iinv` on a HeapLang `WP` goal, which unfolds to `WPi` for `elimAcc_wpi`. -/
example : inv N iprop(<pers> P) -∗ Φ v -∗ WP (Exp.val v) @ m; ⊤ {{ Φ }} := by
  iintro #Hinv HΦ
  iinv Hinv with #HP
  iapply wp_val
  imodintro; iframe HP HΦ

/-- Tests `iinv` with a timeless invariant on a HeapLang `WP` goal, via `isExcept0_wp`. -/
example {P : IProp GF} [Timeless P] (v : Val) (Φ : Val → IProp GF) :
    inv N P -∗ (P -∗ P ∗ Φ v) -∗ WP (Exp.val v) @ m; ⊤ {{ Φ }} := by
  iintro #Hinv HΦ
  iinv Hinv with >HP
  icases HΦ $$ HP with ⟨HP, HΦ⟩
  iapply wp_val
  imodintro; iframe HP HΦ

end heaplang

end IrisITreeTest
