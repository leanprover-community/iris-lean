/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.HeapLang
public import Iris.HeapLang.Lib.NondetBool

/-! # The clairvoyant coin -/

namespace Iris.HeapLang

@[rocq_alias heap_lang.clairvoyant_coin.new_coin]
def newCoin := hl_val%
  λ _, (ref(&nondetBool #()), newProph())

@[rocq_alias heap_lang.clairvoyant_coin.read_coin]
def readCoin := hl_val% λ cp, !fst(cp)

@[rocq_alias heap_lang.toss_coin]
def tossCoin := hl_val%
  λ cp,
    let c := fst(cp);
    let p := snd(cp);
    let r := &nondetBool #();
    c ← r;
    resolveProph(p, r);
    #()

variable {hlc GF} [HeapLangGS hlc GF]

section Proofs

@[rocq_alias heap_lang.prophecy_to_list_bool]
def prophecyToListBool (vs : List (Val × Val)) : List Bool :=
  vs.map (·.2 = hl_val(#true))

private theorem prophecyToListBool_cons (vs : List (Val × Val)) (v : Val) (b : Bool) :
    prophecyToListBool ((v, hl_val(#b)) :: vs) = b :: prophecyToListBool vs := by
  cases b <;> rfl

@[rocq_alias heap_lang.clairvoyant_coin.coin]
def coin (cp : Val) (bs : List Bool) : IProp GF := iprop%
  ∃ (c : Loc) (p : ProphId) (vs : List (Val × Val)),
  ⌜cp = hl_val((#c, #p))⌝ ∗ ⌜bs ≠ []⌝ ∗ ⌜bs.tail = prophecyToListBool vs⌝ ∗
  proph p vs ∗ bs.head?.elim iprop(∃ (b : Bool), c ↦ hl_val(#b)) (fun b => iprop(c ↦ hl_val(#b)))

@[rocq_alias heap_lang.clairvoyant_coin.new_coin_spec]
theorem newCoin.spec :
    {{ True }} hl(&newCoin #()) {{ c bs, RET c; coin (GF := GF) c bs }} := by
  iunfold coin
  iintro %Φ - K
  wp_lam
  wp_apply wp_new_proph $$ [//] with %pvs %p proph
  wp_apply nondetBool.spec $$ [//] with %b -
  wp_alloc c with Hc
  wp_pair
  iintro !>
  iapply K $$ %_ %(b :: prophecyToListBool pvs)
  iexists c, p, pvs
  isimp
  iframe

@[rocq_alias heap_lang.clairvoyant_coin.read_coin_spec]
theorem readCoin.spec (cp : Val) (bs : List Bool) :
    {{ coin (GF := GF) cp bs }} hl(&readCoin &cp)
    {{ (b : Bool) bs', RET hl_val(#b); ⌜bs = b :: bs'⌝ ∗ coin cp bs }} := by
  iunfold coin
  iintro %Φ ⟨%c, %p, %pvs, %rfl, %hne, %htl, Hp, Hb⟩ K
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
  isimp at Hb
  wp_lam
  wp_load
  iintro !>
  iapply K $$ %b %bs
  isplitr; itrivial
  iexists c, p, pvs
  isimp [htl]
  iframe

@[rocq_alias heap_lang.toss_coin_spec]
theorem tossCoin.spec (cp : Val) (bs : List Bool) :
    {{ coin (GF := GF) cp bs }} hl(&tossCoin &cp)
    {{ (b : Bool) bs', RET hl_val(#()); ⌜bs = b :: bs'⌝ ∗ coin cp bs' }} := by
  iunfold coin
  iintro %Φ ⟨%c, %p, %pvs, %rfl, %hne, %htl, Hp, Hb⟩ K
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
  isimp at Hb
  wp_lam
  wp_pures
  wp_apply nondetBool.spec $$ [//] with %r -
  wp_store
  wp_apply wp_resolve_proph $$ Hp with %pvs' ⟨%rfl, Hp⟩
  simp only [List.tail_cons, prophecyToListBool_cons] at htl
  wp_seq
  iintro !>
  iapply K $$ %b %bs
  isplitr; itrivial
  iexists c, p, pvs'
  isimp [htl]
  iframe

end Proofs
