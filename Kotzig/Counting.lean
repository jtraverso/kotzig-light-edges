/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Planar.Orbits

/-!
# Counting along the classes of a setoid and the cycles of a permutation

* `sum_inv_card_cls`: `∑ₐ 1 / |[a]| = numClasses s`;
* `sum_avg_cls`: averaging a function over the classes does not change its sum;
* `card_add_card_le`: if `S ⊆ F` and `π` maps `F` into itself, then at least `2|S| - |F|`
  elements `x` of `S` have `π x ∈ S`;
* `card_add_card_le_of_not`: if `π` maps a class into itself and no two consecutive elements
  satisfy `p`, at most half the class satisfies `p`;
* `exists_pow_eq_self`: if the cycle of `y` has fewer than `n` elements, then `π ^ m` fixes `y`
  for some `0 < m < n`.
-/

@[expose] public section

namespace Kotzig

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {α : Type*} [Fintype α]

open scoped Classical in
/-- The class of `a`, as a finset. -/
noncomputable def cls (s : Setoid α) (a : α) : Finset α := Finset.univ.filter (s a ·)

theorem mem_cls {s : Setoid α} {a b : α} : b ∈ cls s a ↔ s a b := by
  simp [cls]

theorem cls_eq {s : Setoid α} {a b : α} (h : s a b) : cls s a = cls s b := by
  ext c
  simp only [mem_cls]
  exact ⟨fun h' => s.trans (s.symm h) h', fun h' => s.trans h h'⟩

theorem card_cls_pos (s : Setoid α) (a : α) : 0 < (cls s a).card :=
  Finset.card_pos.2 ⟨a, mem_cls.2 (s.refl a)⟩

theorem sum_inv_card_cls (s : Setoid α) :
    ∑ a, (1 : ℚ) / (cls s a).card = numClasses s := by
  classical
  have h1 : ∀ q : Quotient s,
      ∑ a ∈ Finset.univ.filter (fun a => Quotient.mk s a = q), (1 : ℚ) / (cls s a).card = 1 := by
    intro q
    induction q using Quotient.inductionOn with
    | h r =>
    have hset : Finset.univ.filter (fun a => Quotient.mk s a = Quotient.mk s r) = cls s r := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_cls]
      exact ⟨fun h => s.symm (Quotient.exact h), fun h => Quotient.sound (s.symm h)⟩
    rw [hset, Finset.sum_congr rfl (fun a ha => by rw [cls_eq (s.symm (mem_cls.1 ha))]),
      Finset.sum_const, nsmul_eq_mul]
    have := card_cls_pos s r
    field_simp
  rw [← Finset.sum_fiberwise Finset.univ (Quotient.mk s), Finset.sum_congr rfl
    (fun q _ => h1 q), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, numClasses,
    Nat.card_eq_fintype_card]

theorem sum_avg_cls (s : Setoid α) (h : α → ℚ) :
    ∑ a, (∑ b ∈ cls s a, h b) / (cls s a).card = ∑ b, h b := by
  classical
  calc ∑ a, (∑ b ∈ cls s a, h b) / (cls s a).card
      = ∑ a, ∑ b ∈ cls s a, h b / (cls s b).card := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun b hb => ?_)
        rw [cls_eq (mem_cls.1 hb)]
    _ = ∑ b, ∑ a ∈ cls s b, h b / (cls s b).card := by
        simp only [cls, Finset.sum_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
        by_cases hab : s a b
        · rw [if_pos hab, if_pos (s.symm hab)]
        · rw [if_neg hab, if_neg (fun h' => hab (s.symm h'))]
    _ = ∑ b, h b := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        have := card_cls_pos s b
        field_simp

theorem card_add_card_le [DecidableEq α] (π : Perm α) {F S : Finset α} (hF : ∀ x ∈ F, π x ∈ F) (hS : S ⊆ F) :
    S.card + S.card ≤ F.card + (S.filter (fun x => π x ∈ S)).card := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := S) (fun x => π x ∈ S)
  have h2 := Finset.card_filter_add_card_filter_not (s := F) (fun x => x ∈ S)
  have h3 : F.filter (fun x => x ∈ S) = S := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have h4 : (S.filter (fun x => ¬ π x ∈ S)).card ≤ (F.filter (fun x => ¬ x ∈ S)).card := by
    refine Finset.card_le_card_of_injOn π ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
      exact ⟨hF x (hS hx.1), hx.2⟩
    · intro x _ y _ hxy
      exact π.injective hxy
  rw [h3] at h2
  omega

theorem card_add_card_le_of_not (π : Perm α) {O : Finset α} (p : α → Prop) [DecidablePred p]
    (hO : ∀ x ∈ O, π x ∈ O) (hp : ∀ x ∈ O, p x → ¬ p (π x)) :
    (O.filter p).card + (O.filter p).card ≤ O.card := by
  have h1 := Finset.card_filter_add_card_filter_not (s := O) p
  have h2 : (O.filter p).card ≤ (O.filter (fun x => ¬ p x)).card := by
    refine Finset.card_le_card_of_injOn π ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
      exact ⟨hO x hx.1, hp x hx.1 hx.2⟩
    · intro x _ y _ hxy
      exact π.injective hxy
  omega

theorem exists_pow_eq_self (π : Perm α) (y : α) {n : ℕ}
    (h : (cls (SameCycle.setoid π) y).card < n) :
    ∃ m, 0 < m ∧ m < n ∧ (π ^ m) y = y := by
  classical
  obtain ⟨i, hi, j, hj, hij, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range n) (t := cls (SameCycle.setoid π) y) (f := fun i => (π ^ i) y)
    (by simpa using h) (by
      intro i _
      exact mem_cls.2 ⟨i, by simp⟩)
  simp only [Finset.mem_range] at hi hj
  have key : ∀ a b, a < b → b < n → (π ^ a) y = (π ^ b) y →
      ∃ m, 0 < m ∧ m < n ∧ (π ^ m) y = y := by
    intro a b hab hb he
    refine ⟨b - a, by omega, by omega, ?_⟩
    apply (π ^ a).injective
    rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le, he]
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt hj he
  · exact key j i hlt hi he.symm

end Kotzig
