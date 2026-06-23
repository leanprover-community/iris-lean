module

public import Iris.Instances.Lib.Invariants
public import Iris.Std.Namespaces
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

namespace LandinKnot

def landinsKnot : Val := hl_val%
  λ f,
    let r := ref(λ x, x);
    r ← (λ x, f (!r) x);
    !r

def landinN : Namespace := ndot nroot "landin"

section Spec

variable {GF} [HeapLangGS hlc GF]

-- TODO: Convert to texan triple
theorem wp_landinsKnot (P : Val → IProp GF) (Q : Val → Val → IProp GF) (F v1 : Val) :
    ⊢ □ ∀ (Φ : Val → IProp GF),
      ((∀ (f v2 : Val), □ ∀ (Ψ : Val → IProp GF),
          ((∀ (v3 : Val), □ ∀ (Ξ : Val → IProp GF),
              P v3 -∗ ▷ (∀ u, Q u v3 -∗ Ξ u) -∗ WP hl(&f &v3) {{ Ξ }}) ∗ P v2) -∗
          ▷ (∀ u, Q u v2 -∗ Ψ u) -∗ WP hl(&F &f &v2) {{ Ψ }}) ∗ P v1) -∗
      ▷ (∀ u, Q u v1 -∗ Φ u) -∗
      WP hl(&landinsKnot &F &v1) {{ Φ }} := by
  iintro !> %Φ ⟨#H, HP⟩ HQ
  wp_bind &landinsKnot _
  wp_rec
  wp_bind ref(_)
  wp_pures
  iapply wp_alloc
  iintro !> %r Hr
  wp_pures
  wp_bind (_ ← _)
  iapply wp_store $$ Hr
  iintro !> Hr
  wp_pures
  iapply wp_load $$ Hr
  iintro !> Hr
  imod inv_alloc landinN ⊤ _ $$ Hr with #Hinv
  ihave HQ : ▷ (∀ u, Q u v1 -∗ Φ u) $$ [HQ]
  · inext; iexact HQ
  iloeb as IH generalizing %v1 %Φ
  wp_rec
  wp_bind !_
  iapply wp_atomic
  imod inv_acc $$ Hinv with ⟨Hr, Hcl⟩
  simp only [CoPset.subseteq_top]
  imodintro
  iapply wp_load $$ Hr
  iintro !> Hr
  imod Hcl $$ Hr
  iapply H $$ [HP] [$]
  iframe HP
  iintro %v3 !> %Φ HP HQ
  iapply IH $$ HP HQ

end Spec

end LandinKnot
end
