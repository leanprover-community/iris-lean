# Lean vs Rocq big_op.v: Translation Differences

This document tracks theorems in the lean translation that differ from or are missing compared to the Rocq Iris `big_op.v` file.

---

## Part A: BigSepL (Single List) Differences

### 1. Missing `Timeless` Instances

**Location:** Lines 262-297 (commented out)

**Rocq has:**
- `big_sepL_timeless`
- `big_sepL_timeless'`
- `big_sepL_timeless_id`

**Reason:** The Lean version lacks a `sep_timeless` instance (Timeless for `P ∗ Q` when both are Timeless). The Rocq version relies on `big_opL_closed` which requires this infrastructure.

---

### 2. `big_sepL_submseteq` Signature Difference

**Rocq:** Uses `l1 ⊆+ l2` (submultiset relation from stdpp)

**Lean:** Takes explicit permutation witness `(l₁ ++ l).Perm l₂`

**Reason:** Lean lacks stdpp's submultiset relation. The explicit permutation witness is how stdpp defines submultiset internally.

---

### 3. `big_sepL_intro` Signature Difference

**Rocq:** `□ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x) ⊢ [∗ list] k↦x ∈ l, Φ k x`

**Lean:** Uses `[Intuitionistic P]` typeclass constraint on source proposition

**Reason:** Different encoding styles. Lean's approach is more explicit about the resource P being duplicable via typeclass.

---

## Part B: BigSepL2 (Two Lists) Differences

### 8. `big_sepL2_later_1`

**Rocq:**
```coq
Lemma big_sepL2_later_1 `{BiAffine PROP} Φ l1 l2 :
  ▷ ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢
    ◇ [∗ list] k↦x1;x2 ∈ l1;l2, ▷ Φ k x1 x2.
```

**Lean:**
```lean
theorem later_1 [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}:
    later (bigSepL2 Φ l1 l2) ⊢ except0 (bigSepL2 (fun k x1 x2 => later (Φ k x1 x2)) l1 l2)
```

**Status:** Now ported with except-0 (`◇`) support. Both versions require BIAffine.

---

### 9. Missing `big_sepL2_proper_2` (OFE on A, B)

**Rocq has:**
```coq
Lemma big_sepL2_proper_2 {A B : ofe} (Φ Ψ : nat → A → B → PROP) l1 l2 l1' l2' :
  l1 ≡ l1' → l2 ≡ l2' →
  (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 ⊣⊢ Ψ k y1 y2) →
  ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢ ([∗ list] k↦y1;y2 ∈ l1';l2', Ψ k y1 y2).
```

**Lean:** Not ported.

**Reason:** Requires OFE structure on `A` and `B` (list element types). Current Lean formalization focuses on cases where `A` and `B` are plain types.

---

### 10. Missing `big_sepL2_closed` (Meta-Lemma)

**Rocq has:**
```coq
Lemma big_sepL2_closed (C : PROP → Prop) Φ l1 l2 :
  C emp →
  C False →
  (∀ P Q, C P → C Q → C (P ∗ Q)) →
  (∀ k x1 x2, l1 !! k = Some x1 → l2 !! k = Some x2 → C (Φ k x1 x2)) →
  C ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2).
```

**Lean:** Not ported.

**Reason:** This is a meta-lemma for proving properties like Persistent, Affine, Timeless close under bigSepL2. Lean uses direct inductive proofs for each typeclass instance instead.

---

### 11. Missing `big_sepL2_timeless` Family

**Rocq has:**
- `big_sepL2_nil_timeless`
- `big_sepL2_timeless`
- `big_sepL2_timeless'`

**Lean:** Not ported.

**Reason:** Same as BigSepL - requires `sep_timeless` infrastructure.

## Part C: BigAndL (Big Conjunction) Differences

### 12. `big_andL_submseteq` Not Ported

**Rocq:**
```coq
Lemma big_andL_submseteq (Φ : A → PROP) l1 l2 :
  l1 ⊆+ l2 → ([∧ list] y ∈ l2, Φ y) ⊢ [∧ list] y ∈ l1, Φ y.
```

**Lean:** Not ported.

**Reason:** Lean lacks stdpp's `⊆+` (submultiset) relation. The `perm` lemma covers the permutation case directly.

---

### 13. `big_andL_mono'` and `big_andL_id_mono'` Not Ported

**Rocq has:**
- `big_andL_mono'` - unconditional pointwise entailment
- `big_andL_id_mono'` - Proper instance for Forall2

**Lean:** Not ported (uses direct `mono` and `proper` instead).

**Reason:** These are convenience wrappers. Lean's `mono` covers the conditional case, and `proper`/`congr` handle equivalences.

---

### 14. Missing `big_andL_ne` (OFE Non-Expansiveness)

**Rocq has:**
```coq
Lemma big_andL_ne Φ Ψ l n :
  (∀ k y, l !! k = Some y → Φ k y ≡{n}≡ Ψ k y) →
  ([∧ list] k ↦ y ∈ l, Φ k y) ≡{n}≡ ([∧ list] k ↦ y ∈ l, Ψ k y).
```

**Lean:** Not ported.

**Reason:** The OFE-level non-expansiveness is handled at the `BigOpL.congr_ne` level in the algebra layer. BI-level lemmas typically work with `≡` (equivalence) via `proper` rather than `≡{n}≡` (n-distance).

---

### 15. Missing `big_andL_timeless` Family

**Rocq has:**
- `big_andL_nil_timeless`
- `big_andL_timeless`
- `big_andL_timeless'`

**Lean:** Not ported.

**Reason:** Timeless instances require infrastructure for `and_timeless : Timeless P → Timeless Q → Timeless (P ∧ Q)`. This is simpler than `sep_timeless` and could be added.

---

### 16. Missing `big_andL_absorbing` Family

**Rocq has:**
- `big_andL_nil_absorbing` - instance for nil
- `big_andL_absorbing` - conditional lemma
- `big_andL_absorbing'` - unconditional instance

**Lean:** Not ported.

**Reason:** Absorbing typeclass instances for BigAndL not yet implemented.

---

## Part D: BigOrL (Big Disjunction) Differences

### 17. `big_orL_submseteq` Signature Difference

**Rocq:**
```coq
Lemma big_orL_submseteq (Φ : A → PROP) l1 l2 :
  l1 ⊆+ l2 → ([∨ list] y ∈ l1, Φ y) ⊢ [∨ list] y ∈ l2, Φ y.
```

**Lean:**
```lean
theorem submseteq {Φ : A → PROP} {l₁ l₂ l : List A}
    (h : (l₁ ++ l).Perm l₂) :
    ([∨ list] x ∈ l₁, Φ x) ⊢ [∨ list] x ∈ l₂, Φ x
```

**Reason:** Lean lacks stdpp's `⊆+` relation. Uses explicit permutation witness instead. Note direction: for BigOrL the entailment goes FROM smaller list TO larger.

---

### 18. `big_orL_id_mono'` Signature Difference

**Rocq:**
```coq
Global Instance big_orL_id_mono' :
  Proper (Forall2 (⊢) ==> (⊢)) (big_opL (@bi_or PROP) (λ _ P, P)).
```

**Lean:**
```lean
theorem id_mono' {l₁ l₂ : List PROP}
    (hlen : l₁.length = l₂.length)
    (h : ∀ (i : Nat) (P Q : PROP), l₁[i]? = some P → l₂[i]? = some Q → P ⊢ Q) :
    ([∨ list] P ∈ l₁, P) ⊢ [∨ list] P ∈ l₂, P
```

**Reason:** Lean lacks `Forall2` in its standard library. Uses indexed lookup instead.

---

### 19. Missing `big_orL_ne` (OFE Non-Expansiveness)

**Rocq has:**
```coq
Lemma big_orL_ne Φ Ψ l n :
  (∀ k y, l !! k = Some y → Φ k y ≡{n}≡ Ψ k y) →
  ([∨ list] k ↦ y ∈ l, Φ k y) ≡{n}≡ ([∨ list] k ↦ y ∈ l, Ψ k y).
```

**Lean:** Not ported.

**Reason:** Same as BigAndL - handled at the algebra layer via `BigOpL.congr_ne`.

---

### 20. Missing `big_orL_timeless` Family

**Rocq has:**
- `big_orL_nil_timeless`
- `big_orL_timeless`
- `big_orL_timeless'`

**Lean:** Not ported.

**Reason:** Requires `or_timeless : Timeless P → Timeless Q → Timeless (P ∨ Q)` infrastructure.

---

## Part G: BigSepM Additional Differences

### 21. Ported: `big_sepM_fn_insert*`

**Rocq has:**
```coq
Lemma big_sepM_fn_insert {B} (Ψ : K → A → B → PROP) (f : K → B) m i x b :
  m !! i = None →
     ([∗ map] k↦y ∈ <[i:=x]> m, Ψ k y (<[i:=b]> f k))
  ⊣⊢ (Ψ i x b ∗ [∗ map] k↦y ∈ m, Ψ k y (f k)).

Lemma big_sepM_fn_insert' (Φ : K → PROP) m i x P :
  m !! i = None →
  ([∗ map] k↦y ∈ <[i:=x]> m, <[i:=P]> Φ k) ⊣⊢ (P ∗ [∗ map] k↦y ∈ m, Φ k).
```

**Lean:**
```lean
theorem fn_insert {B : Type _} {Ψ : K → V → B → PROP} {f : K → B} {m : M} {i : K} {x : V} {b : B}
    (h : get? m i = none) :
    ([∗ map] k ↦ y ∈ FiniteMap.insert m i x, Ψ k y (fnInsert f i b k)) ⊣⊢
      Ψ i x b ∗ [∗ map] k ↦ y ∈ m, Ψ k y (f k)

theorem fn_insert' {Φ : K → PROP} {m : M} {i : K} {x : V} {P : PROP}
    (h : get? m i = none) :
    ([∗ map] k ↦ _y ∈ FiniteMap.insert m i x, fnInsert Φ i P k) ⊣⊢
      P ∗ [∗ map] k ↦ _y ∈ m, Φ k
```

**Status:** Ported. Uses `fnInsert` helper function for function updates.

---

### 22. Ported: `big_sepM_sep_zip*`

**Rocq has:**
```coq
Lemma big_sepM_sep_zip_with ... (f : A → B → C) ... m1 m2 :
  ...
  ([∗ map] k↦xy ∈ map_zip_with f m1 m2, Φ1 k (g1 xy) ∗ Φ2 k (g2 xy)) ⊣⊢
  ([∗ map] k↦x ∈ m1, Φ1 k x) ∗ ([∗ map] k↦y ∈ m2, Φ2 k y).

Lemma big_sepM_sep_zip ...
```

**Lean:**
```lean
theorem sep_zip {MZ : Type _} [FiniteMap MZ K (V₁ × V₂)] ...
    ([∗ map] k ↦ xy ∈ FiniteMap.zip m₁ m₂, Φ₁ k xy.1 ∗ Φ₂ k xy.2) ⊣⊢
      ([∗ map] k ↦ x ∈ m₁, Φ₁ k x) ∗ [∗ map] k ↦ y ∈ m₂, Φ₂ k y

theorem sep_zip_with {C : Type _} {MZ : Type _} [FiniteMap MZ K C] ...
    ([∗ map] k ↦ xy ∈ mz, Φ₁ k (g₁ xy) ∗ Φ₂ k (g₂ xy)) ⊣⊢
      ([∗ map] k ↦ x ∈ m₁, Φ₁ k x) ∗ [∗ map] k ↦ y ∈ m₂, Φ₂ k y
```

**Status:** Ported (proofs use sorry). Takes explicit permutation proof for `zip` result.

---

### 23. Ported: `big_sepM_impl_strong`, `big_sepM_impl_dom_subseteq`

**Rocq has:** These lemmas for advanced impl patterns with filtered maps.

**Lean:**
```lean
theorem impl_strong [FiniteMapLawsSelf M K V] {M₂ : Type _} {V₂ : Type _} ...
    ([∗ map] k ↦ x ∈ m₁, Φ k x) ⊢
      □ (∀ k, ∀ y, (match get? m₁ k with | some x => Φ k x | none => emp) -∗ ...) -∗ ...

theorem impl_dom_subseteq [FiniteMapLawsSelf M K V] ...
    (hdom : ∀ k, (get? m₂ k).isSome → (get? m₁ k).isSome) :
    ([∗ map] k ↦ x ∈ m₁, Φ k x) ⊢ ...
```

**Status:** Ported (proofs use sorry). Complex lemmas for advanced impl patterns.

---

### 24. Ported: `big_sepM_kmap`

**Rocq:**
```coq
Lemma big_sepM_kmap `{Countable K1, Countable K2} {A}
    (h : K1 → K2) `{!Inj (=) (=) h} (Φ : K2 → A → PROP) (m : gmap K1 A) :
  ([∗ map] k2 ↦ y ∈ kmap h m, Φ k2 y) ⊣⊢ ([∗ map] k1 ↦ y ∈ m, Φ (h k1) y).
```

**Lean:**
```lean
def kmap (h : K → K₂) (m : M) : M₂ :=
  ofList ((toList m).map (fun kv => (h kv.1, kv.2)))

theorem kmap' {Φ : K₂ → V → PROP} {m : M}
    (h : K → K₂) (hinj : Function.Injective h)
    (hperm : (toList (kmap h m)).Perm ((toList m).map (fun kv => (h kv.1, kv.2)))) :
    ([∗ map] k₂ ↦ y ∈ kmap h m, Φ k₂ y) ⊣⊢ [∗ map] k₁ ↦ y ∈ m, Φ (h k₁) y
```

**Status:** Ported. Defines `kmap` and proves the big sep equivalence.

---

## Part I: BigAndM Additional Differences

### 25. BigAndM `later` Does NOT Require `BIAffine`

**Rocq:**
```coq
Lemma big_andM_later Φ m :
  ▷ ([∧ map] k↦x ∈ m, Φ k x) ⊣⊢ [∧ map] k↦x ∈ m, ▷ Φ k x.
```

**Lean:**
```lean
theorem later {Φ : K → V → PROP} {m : M} :
    iprop(▷ [∧ map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∧ map] k ↦ x ∈ m, ▷ Φ k x
```

**Status:** Same - neither requires `BIAffine`. This is a key difference from `BigSepM.later` which requires `BIAffine`.

---

### 26. BigAndM `affine` Instance Requires `BIAffine`

**Rocq:** BigAndM doesn't have Affine instances in general.

**Lean:**
```lean
instance affine {Φ : K → V → PROP} {m : M} [BIAffine PROP] :
    Affine ([∧ map] k ↦ x ∈ m, Φ k x)
```

**Reason:** In a `BIAffine` setting, any proposition is affine, including big conjunctions. This is a Lean-only convenience instance.

---

### 27. BigAndM Map Transformation Lemmas

Same as BigSepM, the following BigAndM lemmas take explicit permutation proofs:

| Lemma | Permutation Required |
|-------|---------------------|
| `fmap` | `(toList (map f m)).Perm ((toList m).map ...)` |
| `omap` | `(toList (filterMap f m)).Perm ((toList m).filterMap ...)` |
| `union` | `(toList (m₁ ∪ m₂)).Perm (toList m₁ ++ toList m₂)` |

---

### 28. BigAndM `union` Disjointness vs Permutation

Same as BigSepM - Rocq takes `m1 ##ₘ m2`, Lean takes explicit permutation proof.

---

### 29. Not Ported: `big_andM_fn_insert*`

**Rocq has:**
```coq
Lemma big_andM_fn_insert {B} (Ψ : K → A → B → PROP) (f : K → B) m i x b :
  m !! i = None →
     ([∧ map] k↦y ∈ <[i:=x]> m, Ψ k y (<[i:=b]> f k))
  ⊣⊢ (Ψ i x b ∧ [∧ map] k↦y ∈ m, Ψ k y (f k)).

Lemma big_andM_fn_insert' (Φ : K → PROP) m i x P :
  m !! i = None →
  ([∧ map] k↦y ∈ <[i:=x]> m, <[i:=P]> Φ k) ⊣⊢ (P ∧ [∧ map] k↦y ∈ m, Φ k).
```

**Lean:** Not ported.

**Reason:** Low priority. Same as BigSepM version.

---

### 30. Not Ported: `big_andM_kmap`

**Rocq:**
```coq
Lemma big_andM_kmap `{Countable K1, Countable K2} {A}
    (h : K1 → K2) `{!Inj (=) (=) h} (Φ : K2 → A → PROP) (m : gmap K1 A) :
  ([∧ map] k2 ↦ y ∈ kmap h m, Φ k2 y) ⊣⊢ ([∧ map] k1 ↦ y ∈ m, Φ (h k1) y).
```

**Lean:** Not ported.

**Reason:** Requires `kmap` (key mapping) operation on maps.

---

### 31. Not Ported: `big_andM_map_seq*`

**Rocq has:**
```coq
Lemma big_andM_map_seq {A} (Φ : nat → A → PROP) (start : nat) (l : list A) :
  ([∧ map] k ↦ x ∈ map_seq start l, Φ k x) ⊣⊢ ([∧ list] i ↦ x ∈ l, Φ (start + i) x).
```

**Lean:** Not ported.

**Reason:** Requires `map_seq` operation.

---

### 32. BigAndM Timeless Instances Not Ported

**Rocq has:**
```coq
Global Instance big_andM_empty_timeless Φ :
  Timeless ([∧ map] k↦x ∈ ∅, Φ k x).

Lemma big_andM_timeless Φ m :
  (∀ k x, m !! k = Some x → Timeless (Φ k x)) →
  Timeless ([∧ map] k↦x ∈ m, Φ k x).

Global Instance big_andM_timeless' Φ m :
  (∀ k x, Timeless (Φ k x)) → Timeless ([∧ map] k↦x ∈ m, Φ k x).
```

**Lean:** Not ported.

**Reason:** Requires `and_timeless : Timeless P → Timeless Q → Timeless (P ∧ Q)` infrastructure.

---

## Implementation Notes

### Blocking Dependencies

1. **Timeless instances** require `sep_timeless : Timeless P → Timeless Q → Timeless (P ∗ Q)` to be defined first.

### Design Decisions

- Lean uses `[k]?` (Lean 4 list indexing) vs Rocq's `!! k` notation
- Lean uses `l.set i x` vs Rocq's `<[i:=x]>l` for list update
- Lean uses explicit `Intuitionistic` typeclass vs Rocq's `□` modality in some lemma statements
- Lean exposes permutation witnesses explicitly rather than using stdpp's `⊆+` relation
- Lean splits TCOr-based lemmas into separate Affine and Absorbing versions
- Lean adds `∧ emp` to nil_inv lemmas to preserve BI structure in non-affine settings

### Notation Differences

| Rocq | Lean |
|------|------|
| `[∗ list] k↦x1;x2 ∈ l1;l2, Φ` | `[∗ list] k ↦ x1,x2 ∈ l1,l2, Φ` |
| `l !! i` | `l[i]?` |
| `<[i:=x]>l` | `l.set i x` |
| `S n` | `n + 1` |
| `length l` | `l.length` |
| `reverse l` | `l.reverse` |
| `replicate n x` | `List.replicate n x` |
