import Mathlib.Data.Finset.SDiff

namespace Bluebell

-- Indexed tuples used across the development
def indexedTuple (α : Type*) (I : Finset ℕ) := I → α

def indexedTuple.remove (α : Type*) (I : Finset ℕ) (J : Finset ℕ) (_ : J ⊆ I) :
    indexedTuple α I → indexedTuple α (I \ J) :=
  fun x i => x ⟨i.1, by
    rcases i with ⟨i, hi⟩
    -- hi : i ∈ I \ J
    -- show i ∈ I
    exact (Finset.mem_sdiff.mp hi).1⟩

end Bluebell
