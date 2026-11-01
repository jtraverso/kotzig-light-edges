/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Kotzig.Discharging

/-!
# Kotzig's theorem and its relatives

For a finite simple planar graph `G` (with a plane map in the sense of the
`LeanPool.K5MinorFreeChoosability` library):

* `kotzig_borodin`: minimum degree at least three gives an edge of weight at most `13`;
* `light_edge_minDegree_four`: minimum degree at least four gives an edge of weight at most `11`;
* `kotzig`: a `3`-connected planar graph has an edge of weight at most `13`, and at most `11` if
  it has no vertex of degree three;
* `wernicke`: minimum degree five gives a `5`-vertex adjacent to a vertex of degree at most `6`.
-/

@[expose] public section

namespace Kotzig

open LeanPool.K5MinorFreeChoosability

/-- The vertex inequality for minimum degree three and no edge of weight below `14`. -/
theorem arith_three (k s : ℕ) (L : ℚ) (hk : 6 ≤ k) (hs : s ≤ k)
    (hm : 0 < s → max 3 (14 - k) ≤ 5) (h0 : 0 ≤ L) (h1 : (2 * s - k : ℚ) ≤ L) :
    0 ≤ (k : ℚ) - 6 - s * (6 / ((max 3 (14 - k) : ℕ) : ℚ) - 1) + L := by
  have hk' : (6 : ℚ) ≤ k := by exact_mod_cast hk
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · simp only [Nat.cast_zero, zero_mul, sub_zero]
    linarith
  · have h5 := (le_max_right 3 (14 - k)).trans (hm hs0)
    by_cases hk11 : 11 ≤ k
    · rw [max_eq_left (by omega : 14 - k ≤ 3)]
      rcases le_or_gt (2 * s) k with h2 | h2
      · have : ((s + 6 : ℕ) : ℚ) ≤ k := by exact_mod_cast (by omega : s + 6 ≤ k)
        push_cast at this
        norm_num
        linarith
      · have : ((6 : ℕ) : ℚ) ≤ s := by exact_mod_cast (by omega : 6 ≤ s)
        push_cast at this
        norm_num
        linarith
    · rw [max_eq_right (by omega : 3 ≤ 14 - k)]
      have hk9 : 9 ≤ k := by omega
      interval_cases k <;> interval_cases s <;> norm_num at h1 ⊢ <;> linarith

/-- The vertex inequality for minimum degree four and no edge of weight below `12`. -/
theorem arith_four (k s : ℕ) (L : ℚ) (hk : 6 ≤ k) (hs : s ≤ k)
    (hm : 0 < s → max 4 (12 - k) ≤ 5) (h0 : 0 ≤ L) (h1 : (2 * s - k : ℚ) ≤ L) :
    0 ≤ (k : ℚ) - 6 - s * (6 / ((max 4 (12 - k) : ℕ) : ℚ) - 1) + L := by
  have hk' : (6 : ℚ) ≤ k := by exact_mod_cast hk
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · simp only [Nat.cast_zero, zero_mul, sub_zero]
    linarith
  · have h5 := (le_max_right 4 (12 - k)).trans (hm hs0)
    by_cases hk8 : 8 ≤ k
    · rw [max_eq_left (by omega : 12 - k ≤ 4)]
      rcases le_or_gt s (2 * k - 12) with h2 | h2
      · have : ((s + 12 : ℕ) : ℚ) ≤ 2 * k := by exact_mod_cast (by omega : s + 12 ≤ 2 * k)
        push_cast at this
        norm_num
        linarith
      · have : ((4 : ℕ) : ℚ) ≤ s := by exact_mod_cast (by omega : 4 ≤ s)
        push_cast at this
        norm_num
        linarith
    · rw [max_eq_right (by omega : 4 ≤ 12 - k)]
      have hk7 : 7 ≤ k := by omega
      interval_cases k <;> interval_cases s <;> norm_num at h1 ⊢ <;> linarith

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Kotzig's theorem**, in the form conjectured by Erdős and proved by Borodin: a finite simple
planar graph of minimum degree at least three has an edge of weight at most `13`. -/
theorem kotzig_borodin [Nonempty V] (hG : IsPlanar G) (hδ : ∀ v, 3 ≤ G.degree v) :
    ∃ u v, G.Adj u v ∧ G.degree u + G.degree v ≤ 13 := by
  classical
  obtain ⟨u, v, huv, h⟩ := exists_light hG 3 14 le_rfl (by norm_num) hδ arith_three
  exact ⟨u, v, huv, by omega⟩

/-- A finite simple planar graph of minimum degree at least four has an edge of weight at most
`11`. -/
theorem light_edge_minDegree_four [Nonempty V] (hG : IsPlanar G) (hδ : ∀ v, 4 ≤ G.degree v) :
    ∃ u v, G.Adj u v ∧ G.degree u + G.degree v ≤ 11 := by
  classical
  obtain ⟨u, v, huv, h⟩ := exists_light hG 4 12 (by norm_num) (by norm_num) hδ arith_four
  exact ⟨u, v, huv, by omega⟩

/-- **Wernicke's theorem** (1904): a finite simple planar graph of minimum degree at least five
has a vertex of degree five adjacent to a vertex of degree at most six. -/
theorem wernicke [Nonempty V] (hG : IsPlanar G) (hδ : ∀ v, 5 ≤ G.degree v) :
    ∃ u v, G.Adj u v ∧ G.degree u = 5 ∧ G.degree v ≤ 6 := by
  obtain ⟨u, v, huv, h⟩ := light_edge_minDegree_four hG (fun v => (by norm_num : 4 ≤ 5).trans (hδ v))
  have hu := hδ u
  have hv := hδ v
  by_cases hu5 : G.degree u = 5
  · exact ⟨u, v, huv, hu5, by omega⟩
  · exact ⟨v, u, huv.symm, by omega, by omega⟩

/-- `G` is `3`-connected: it has at least four vertices and stays connected after the deletion
of any set of at most two vertices. -/
def ThreeConnected (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧ ∀ S : Finset V, S.card ≤ 2 → (G.induce {v | v ∉ S}).Connected

theorem three_le_degree_of_threeConnected (h : ThreeConnected G) (v : V) : 3 ≤ G.degree v := by
  classical
  by_contra hlt
  set S := G.neighborFinset v with hS
  have hSc : S.card ≤ 2 := by
    rw [hS, G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨w, hw⟩ : ∃ w, w ∉ insert v S := by
    by_contra hcon
    push Not at hcon
    have : (Finset.univ : Finset V) ⊆ insert v S := fun x _ => hcon x
    have h1 := Finset.card_le_card this
    have h2 := Finset.card_insert_le v S
    rw [Finset.card_univ] at h1
    have := h.1
    omega
  have hvS : v ∉ S := by simp [hS]
  have hwS : w ∉ S := fun hw' => hw (Finset.mem_insert_of_mem hw')
  have hwv : w ≠ v := fun e => hw (e ▸ Finset.mem_insert_self v S)
  obtain ⟨p⟩ := (h.2 S hSc).preconnected ⟨v, hvS⟩ ⟨w, hwS⟩
  cases p with
  | nil => exact hwv rfl
  | @cons _ x _ hadj _ =>
    have hx : x.1 ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset _ _ _).2 hadj
    exact x.2 hx

/-- **Kotzig's theorem** (1955): a `3`-connected planar graph has an edge of weight at most `13`,
and of weight at most `11` if it has no vertex of degree three. -/
theorem kotzig (hG : IsPlanar G) (h3 : ThreeConnected G) :
    (∃ u v, G.Adj u v ∧ G.degree u + G.degree v ≤ 13) ∧
      ((∀ v, G.degree v ≠ 3) → ∃ u v, G.Adj u v ∧ G.degree u + G.degree v ≤ 11) := by
  have : Nonempty V := Fintype.card_pos_iff.1 (by have := h3.1; omega)
  refine ⟨kotzig_borodin hG (three_le_degree_of_threeConnected h3), fun h4 => ?_⟩
  refine light_edge_minDegree_four hG (fun v => ?_)
  have := three_le_degree_of_threeConnected h3 v
  have := h4 v
  omega

end Kotzig
