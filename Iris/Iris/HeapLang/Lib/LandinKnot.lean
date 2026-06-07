module

public import Iris.Instances.Lib.Invariants
public import Iris.Std.Namespaces
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

namespace LandinKnot

def myrec : Val := hl_val(
  λ f,
    let r := ref(λ x, x);
    r ← (λ x, f (!r) x);
    !r)

def landinN : Namespace := ndot nroot "landin"

section Spec

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

-- TODO: fold  {{{ P }}} e {{{ u, RET u; Q }}} when it's supported
-- https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/bi/weakestpre.v#L86-90
theorem myrec_spec (P : Val → IProp GF) (Q : Val → Val → IProp GF) (F v1 : Val) :
    ⊢ □ ∀ (Φ : Val → IProp GF),
      ((∀ (f v2 : Val), □ ∀ (Ψ : Val → IProp GF),
          ((∀ (v3 : Val), □ ∀ (Ξ : Val → IProp GF),
              P v3 -∗ ▷ (∀ u, Q u v3 -∗ Ξ u) -∗ WP hl(&f &v3) {{ Ξ }}) ∗ P v2) -∗
          ▷ (∀ u, Q u v2 -∗ Ψ u) -∗ WP hl(&F &f &v2) {{ Ψ }}) ∗ P v1) -∗
      ▷ (∀ u, Q u v1 -∗ Φ u) -∗
      WP hl(&myrec &F &v1) {{ Φ }} := by
  iintro !> %Φ ⟨#H, HP⟩ HQ
  wp_bind &myrec _
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
  imod inv_alloc landinN ⊤ _ $$ [Hr] with #Hinv; inext; iexact Hr
  ihave HQ : ▷ (∀ u, Q u v1 -∗ Φ u) $$ [HQ]; inext; iexact HQ
  iloeb as IH generalizing %v1 %Φ
  wp_rec
  wp_bind !_
  iapply wp_atomic
  imod inv_acc $$ Hinv with ⟨Hr, Hcl⟩; simp
  imodintro
  iapply wp_load $$ Hr
  iintro !> Hr
  imod Hcl $$ [Hr]; inext; iexact Hr; imodintro
  iapply H $$ [HP] [$HQ]
  iframe HP
  iintro %v3 !> %Φ HP HQ
  iapply IH $$ HP HQ

end Spec

end LandinKnot
end
