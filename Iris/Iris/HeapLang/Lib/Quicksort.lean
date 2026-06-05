module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

namespace Quicksort

def cons : Val := hl_val% λ x, some(ref(x))

def append : Val := hl_val%
  rec append x :=
    let l1 := fst(x);
    let l2 := snd(x);
    match l1 with
    | none() => l2
    | some(x) =>
      (let p := !x;
       let head := fst(p);
       let tail := snd(p);
       ?cons (head, append (tail, l2)))

def partition : Val := hl_val%
  rec partition arg :=
    let x := fst(arg);
    let l := snd(arg);
    match l with
    | none() => (none(), none())
    | some(lx) =>
      (let p := !lx;
       let head := fst(p);
       let tail := snd(p);
       let part := partition (x, tail);
       if head ≤ x then
        (?cons (head, fst(part)), snd(part))
       else
        (fst(part), ?cons (head, snd(part))))

def quicksort : Val := hl_val%
  rec quicksort l :=
    match l with
    | none() => l
    | some(x) =>
      (let p := !x;
       let head := fst(p);
       let tail := snd(p);
       let part := ?partition (head, tail);
       let a := quicksort (fst(part));
       let b := quicksort (snd(part));
       let e := ?cons (head, b);
       ?append (a, e))

section Predicates

variable [HeapLangGS hlc GF]

def isList (v : Val) : List Int → IProp GF
  | [] => iprop% ⌜v = hl_val(none())⌝
  | x :: xs => iprop% ∃ l tl, ⌜v = hl_val(some(#(.loc l)))⌝ ∗
    l ↦ some hl_val((#x, ?tl)) ∗ isList tl xs

end Predicates

section Specs

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

theorem cons_spec x l ls Φ :
    isList (GF:=GF) l ls -∗
    (∀ v, isList v (x :: ls) -∗ Φ v) -∗
    WP hl(?cons v((#x, ?l))) {{ Φ }} := by
  iintro Hl HΦ
  wp_rec
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %l Hl
  wp_pures
  imodintro
  iapply HΦ
  rw (occs:=[3]) [isList.eq_def]
  simp only
  iexists _, _; iframe
  itrivial

theorem append_spec l1 ls1 l2 ls2 Φ :
    isList (GF:=GF) l1 ls1 -∗
    isList l2 ls2 -∗
    (∀ v, isList v (ls1 ++ ls2) -∗ Φ v) -∗
    WP hl(?append v((?l1, ?l2))) {{ Φ }} := by
  iintro Hl1 Hl2 HΦ
  iloeb as IH generalizing %l1 %ls1 %Φ
  wp_rec
  rw (occs:=[3]) [isList.eq_def]
  cases ls1 with
  | nil =>
    simp only
    icases Hl1 with %hl1; subst hl1
    wp_pures; imodintro; simp
    iapply HΦ $$ [$]
  | cons x ls1 =>
    simp only
    icases Hl1 with ⟨%x, %tl, %hl1, Hpt, Hl1⟩; subst hl1
    wp_pures
    wp_bind !_
    iapply wp_load $$ [$]
    iintro !> Hpt
    wp_pures
    wp_bind ?append _
    iapply IH $$ Hl1 Hl2
    iintro %_ Hl
    wp_pures
    iapply cons_spec $$ [$]
    iintro %_ Hl; simp
    iapply HΦ $$ [$]

theorem partition_spec x l ls Φ :
    isList (GF:=GF) l ls -∗
    (∀ l1 l2,
      isList l1 (ls.filter (· ≤ x)) -∗
      isList l2 (ls.filter (x < ·)) -∗
      Φ hl_val((?l1, ?l2))) -∗
    WP hl(?partition v((#x, ?l))) {{ Φ }} := by
  iintro Hl HΦ
  iloeb as IH generalizing %l %ls %Φ
  wp_rec; wp_pures
  rw (occs:=[2]) [isList.eq_def]
  cases ls with
  | nil =>
    simp only
    icases Hl with %hl; subst hl
    wp_pures; imodintro; simp
    iapply HΦ <;> simp [isList] <;> itrivial
  | cons hd ls =>
    simp only
    icases Hl with ⟨%_, %tl, %hl, Hpt, Hl⟩; subst hl
    wp_pures
    wp_bind !_
    iapply wp_load $$ [$]
    iintro !> Hpt
    wp_pures
    wp_bind ?partition _
    iapply IH $$ Hl
    iintro %l1 %l2 Hl1 Hl2
    wp_pures
    by_cases hd ≤ x <;> simp [*] <;> wp_pures
    all_goals wp_bind ?cons _
    · iapply cons_spec $$ Hl1
      iintro %_ _
      wp_pures
      imodintro
      iapply HΦ $$ [$] [$]
    · iapply cons_spec $$ Hl2
      iintro %_ _
      wp_pures
      imodintro
      iapply HΦ $$ Hl1
      have : x < hd := by grind
      simp [*]
      iframe

-- set_option profiler true in
theorem quicksort_spec l ls Φ :
    isList (GF:=GF) l ls -∗
    (∀ l' ls',
      isList l' ls' -∗
      ⌜List.Pairwise LE.le ls'⌝ -∗
      ⌜List.Perm ls ls'⌝ -∗
      Φ l') -∗
    WP hl(?quicksort ?l) {{ Φ }} := by
  iintro Hl HΦ
  iloeb as IH generalizing %l %ls %Φ
  wp_rec
  rw (occs:=[2]) [isList.eq_def]
  cases ls with
  | nil =>
    simp
    iclear IH
    icases Hl with %heq; subst heq
    wp_pures
    imodintro
    iapply HΦ $$ %_ %([])
    · unfold isList; itrivial
    · itrivial
    · itrivial
  | cons head tail =>
    simp
    icases Hl with ⟨%l, %tl, %heq, Hpt, Hl⟩; subst heq
    wp_pures
    wp_bind !_
    iapply wp_load $$ [$]
    iintro !> Hpt
    wp_pures
    wp_bind ?partition _
    iapply partition_spec $$ [$]
    iintro %l1 %l2 Hl1 Hl2
    wp_pures
    wp_bind ?quicksort _
    iapply IH $$ [$]
    iintro %l1' %ls1' Hl1 %_ %_
    wp_pures
    wp_bind ?quicksort _
    iapply IH $$ [$]
    iintro %l2' %ls2' Hl2 %_ %_
    wp_pures
    wp_bind ?cons _
    iapply cons_spec $$ Hl2
    iintro %_ _
    wp_pures
    iapply append_spec $$ [$] [$]
    iintro %_ _
    iapply HΦ $$ [$]
    · ipureintro
      have : ls2'.all (head < ·) := by grind
      grind [List.pairwise_cons]
    · ipureintro
      grind [List.filter_append_perm]


-- example (l l1 l2 : List Int) x :
--   List.Perm (l.filter (· ≤ x)) l1 →
--   List.Perm (l.filter (x < ·)) l2 →
--   List.Perm (x :: l) (l1 ++ x :: l2) := by
--     intro h1 h2
--     have : List.Perm l (l.filter (· ≤ x) ++ l.filter (x < ·)) := by
--       grind [List.filter_append_perm]
--     grind

-- example (l l1 l2 : List Int) x :
--   List.Perm (l.filter (· ≤ x)) l1 →
--   List.Pairwise LE.le l1 →
--   List.Pairwise LE.le l2 →
--   List.Perm (l.filter (x < ·)) l2 →
--   List.Pairwise LE.le (l1 ++ x :: l2) := by
--     intro h1 h2 h3 h4
--     have : l2.all (x < ·) := by grind [List.Perm.mem_iff]
--     grind [List.pairwise_cons]
