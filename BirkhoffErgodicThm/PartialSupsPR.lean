import Mathlib

/- The following is a generalization but can it be more general? The induction proof requires
`[SuccOrder ι]` but does the result require this? However this might be pointless generality, is
there any use case? -/

-- To be added to `Mathlib/Order/PartialSups`. Correct name?
lemma map_partialSups' {α β F ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [SuccOrder ι]
    [OrderBot ι] [SemilatticeSup α] [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
    (f : ι → α) (g : F) : partialSups (g ∘ f) = g ∘ partialSups f :=
  funext fun i ↦ Succ.rec (by simp) (fun _ _ _ ↦ (by simp_all)) (bot_le (a := i))

lemma map_partialSups
    [SemilatticeSup α] [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
    (f : ℕ → α) (g : F) : partialSups (g ∘ f) = g ∘ partialSups f := by
  exact map_partialSups' f g

-- To be added to `Mathlib/Order/PartialSups`. Correct name?
open OrderIso in
lemma add_partialSups' {ι α : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [SuccOrder ι]
    [OrderBot ι] [Lattice α] [AddGroup α] [CovariantClass α α ((· + ·)) (· ≤ ·)]
    (f : ι → α) (c : α) (i : ι): partialSups (c + f ·) i = c + partialSups f i := by
  change (partialSups (addLeft c ∘ _)) i = _
  rw [map_partialSups' f (addLeft c)]
  rfl

open OrderIso in
lemma add_partialSups
    [Lattice α] [AddGroup α] [CovariantClass α α ((· + ·)) (· ≤ ·)]
    (f : ℕ → α) (c : α) : partialSups (c + f ·) n = c + partialSups f n := by
  exact add_partialSups' f c n

/- Note for curiosity with `partialSups_succ'`: In `partialSups_succ` slightly weaker assumptions on
`ι` are used: `[LinearOrder ι] [LocallyFiniteOrderBot ι] [SuccOrder ι]`. However using just this
breaks the statement because it can't sythesise `[OrderBot ι]`. These assumptions permit an empty
set and perhaps it can't use the hypothesis to exclude this and guarantee the existence of `⊥`.
The assumptions used here match those of `partialSups_bot` in the same file. -/

-- To be added to `Mathlib/Order/PartialSups`
open Finset in
lemma partialSups_succ' {α ι : Type*} [SemilatticeSup α] [LinearOrder ι]
    [LocallyFiniteOrder ι] [SuccOrder ι] [OrderBot ι] (f : ι → α) (i : ι) :
    (partialSups f) (Order.succ i) = f ⊥ ⊔ (partialSups (f ∘ Order.succ)) i := by
  refine Succ.rec (by simp) (fun j _ h ↦ ?_) (bot_le (a := i))
  have : (partialSups (f ∘ Order.succ)) (Order.succ j) =
      ((partialSups (f ∘ Order.succ)) j ⊔ (f ∘ Order.succ) (Order.succ j)) := by simp
  simp [this, h, sup_assoc]

-- To be added to `Mathlib/Algebra/Order/PartialSups`
lemma partialSups_add_one' [SemilatticeSup α] (f : ℕ → α) (n : ℕ) :
    partialSups f (n + 1) = f 0 ⊔ partialSups (f ∘ (fun k ↦ k + 1)) n := by
  exact Order.succ_eq_add_one n ▸ partialSups_succ' f n

#check partialSups_add_one
#check partialSups_succ
