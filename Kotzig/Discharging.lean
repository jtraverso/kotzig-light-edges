/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Kotzig.Counting
public import LeanPool.K5MinorFreeChoosability.Planar.Embedding

/-!
# Light edges in plane maps by discharging

Let `M` be a plane map of a finite simple graph `G` with minimum degree at least `δ ≥ 3` in which
every edge has weight (degree sum) at least `W ≥ 11`. Give every dart `d` the charge
`(1 - 6 / deg (tail d)) + (2 - 6 / |face d|)`; by Euler's formula the total is `-12 K < 0`
(`sum_charge`), where `K ≥ 1` is the number of components.

Small vertices (degree at most five) take `(6 - deg u) / deg u` through each of their darts,
and every face gives `1` to each corner whose vertex is big and whose two darts end at small
vertices (`Spec`). Since two small vertices are never adjacent, such a corner never lies on a
triangle, so a face of length `ℓ` has at most `ℓ / 2` of them and `ℓ ≥ 4`: faces stay
nonnegative (`face_sum_nonneg`). A big vertex of degree `k` with `s` small neighbours loses
at most `s (6 / m - 1)`, where `m = max δ (W - k)` bounds the degree of a small neighbour from
below, and gains at least `2 s - k`; the arithmetic hypothesis `harith` makes it nonnegative
(`vertex_sum_nonneg`). This contradicts Euler's formula (`exists_light`).

The proof works directly on the rotation system: no triangulation is needed.
-/

@[expose] public section

namespace Kotzig

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The charge a small vertex takes through each of its darts. -/
noncomputable def take (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℚ :=
  if G.degree v ≤ 5 then (6 - (G.degree v : ℚ)) / G.degree v else 0

variable {G : SimpleGraph V} [DecidableRel G.Adj] (M : PlaneMap G)

/-- The length of the face to the left of a dart. -/
noncomputable def fLen (d : G.Dart) : ℕ := (cls (SameCycle.setoid M.facePerm) d).card

/-- A dart of a face whose tail is small, whose head is big and whose successor on the face ends
at a small vertex: the corner at its head lies between two small neighbours. -/
def Spec (x : G.Dart) : Prop :=
  G.degree x.fst ≤ 5 ∧ 5 < G.degree x.snd ∧ G.degree (M.facePerm x).snd ≤ 5

instance (x : G.Dart) : Decidable (Spec M x) := by
  unfold Spec
  infer_instance

/-- The charge a face gives through a dart. -/
noncomputable def specI (x : G.Dart) : ℚ := if Spec M x then 1 else 0

/-! ### Darts, rotation and faces -/

theorem fst_facePerm (d : G.Dart) : (M.facePerm d).fst = d.snd := by
  rw [M.facePerm_apply, M.isRotationSystem.fst_apply]
  rfl

theorem sameCycle_rot_iff {d e : G.Dart} : SameCycle M.rot d e ↔ d.fst = e.fst := by
  constructor
  · intro h
    have := sameCycle_of_step (Setoid.ker (fun d : G.Dart => d.fst))
      (fun z => by rw [Setoid.ker_def]; exact (M.isRotationSystem.fst_apply z).symm) h
    rwa [Setoid.ker_def] at this
  · exact M.isRotationSystem.sameCycle d e

theorem card_cls_rot (d : G.Dart) :
    (cls (SameCycle.setoid M.rot) d).card = G.degree d.fst := by
  rw [← G.dart_fst_fiber_card_eq_degree d.fst]
  congr 1
  ext e
  rw [mem_cls, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact (sameCycle_rot_iff M).trans eq_comm

theorem facePerm_ne_self (d : G.Dart) : M.facePerm d ≠ d := by
  intro h
  have := fst_facePerm M d
  rw [h] at this
  exact d.adj.ne this

theorem facePerm_facePerm_ne (hδ : ∀ v, 2 ≤ G.degree v) (y : G.Dart) :
    M.facePerm (M.facePerm y) ≠ y := by
  intro h
  have hz1 : (M.facePerm y).fst = y.snd := fst_facePerm M y
  have hz2 : (M.facePerm y).snd = y.fst := by
    have := fst_facePerm M (M.facePerm y)
    rw [h] at this
    exact this.symm
  have hzy : M.facePerm y = y.symm := by
    rw [SimpleGraph.Dart.ext_iff]
    exact Prod.ext hz1 hz2
  have hfix : M.rot y.symm = y.symm := by
    rw [← M.facePerm_apply]
    exact hzy
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1
    (show 1 < (G.neighborFinset y.snd).card by
      rw [G.card_neighborFinset_eq_degree]
      have := hδ y.snd
      omega)
  rw [SimpleGraph.mem_neighborFinset] at ha hb
  have e1 : y.symm = ⟨(y.snd, a), ha⟩ :=
    (M.isRotationSystem.sameCycle y.symm ⟨(y.snd, a), ha⟩ rfl).eq_of_left hfix
  have e2 : y.symm = ⟨(y.snd, b), hb⟩ :=
    (M.isRotationSystem.sameCycle y.symm ⟨(y.snd, b), hb⟩ rfl).eq_of_left hfix
  exact hab (congrArg (fun d : G.Dart => d.snd) (e1.symm.trans e2))

theorem three_le_fLen (hδ : ∀ v, 2 ≤ G.degree v) (y : G.Dart) : 3 ≤ fLen M y := by
  by_contra hlt
  obtain ⟨m, hm0, hm3, hm⟩ := exists_pow_eq_self M.facePerm y (n := 3)
    (by unfold fLen at hlt; omega)
  interval_cases m
  · exact facePerm_ne_self M y (by simpa using hm)
  · exact facePerm_facePerm_ne M hδ y (by simpa [pow_two] using hm)

theorem not_spec_facePerm {x : G.Dart} (h : Spec M x) : ¬ Spec M (M.facePerm x) := by
  intro h'
  have h1 := h'.1
  rw [fst_facePerm] at h1
  exact absurd h1 (not_le.2 h.2.1)

theorem four_le_fLen (hδ : ∀ v, 2 ≤ G.degree v) {W : ℕ} (hW : 11 ≤ W)
    (hlight : ∀ u v, G.Adj u v → W ≤ G.degree u + G.degree v) {y : G.Dart} (h : Spec M y) :
    4 ≤ fLen M y := by
  by_contra hlt
  obtain ⟨m, hm0, hm4, hm⟩ := exists_pow_eq_self M.facePerm y (n := 4)
    (by unfold fLen at hlt; omega)
  interval_cases m
  · exact facePerm_ne_self M y (by simpa using hm)
  · exact facePerm_facePerm_ne M hδ y (by simpa [pow_two] using hm)
  · have e : M.facePerm (M.facePerm (M.facePerm y)) = y := by simpa [pow_three] using hm
    have h1 := fst_facePerm M (M.facePerm y)
    have h2 := fst_facePerm M (M.facePerm (M.facePerm y))
    rw [e] at h2
    have hw := hlight _ _ (M.facePerm (M.facePerm y)).adj
    rw [h1, ← h2] at hw
    have := h.1
    have := h.2.2
    omega

/-! ### Euler's formula as a sum over darts -/

theorem sum_charge :
    ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + (2 - 6 / (fLen M d : ℚ))) =
      -12 * (numComponents M.rot (dartSymm G) : ℚ) := by
  have hE := M.euler
  have hD := card_dart_eq_two_mul G
  have hEd := card_edgeSet_eq_cycleCount G
  have hV : ∑ d : G.Dart, (1 : ℚ) / G.degree d.fst = cycleCount M.rot := by
    rw [show cycleCount M.rot = numClasses (SameCycle.setoid M.rot) from rfl,
      ← sum_inv_card_cls (SameCycle.setoid M.rot)]
    exact Finset.sum_congr rfl (fun d _ => by rw [card_cls_rot M d])
  have hF : ∑ d : G.Dart, (1 : ℚ) / fLen M d = M.numFaces :=
    sum_inv_card_cls (SameCycle.setoid M.facePerm)
  have hc : (Fintype.card G.Dart : ℚ) = 2 * Nat.card G.edgeSet := by
    rw [← Nat.card_eq_fintype_card, hD, hEd]
    push_cast
    ring
  have hE' : (cycleCount M.rot : ℚ) - Nat.card G.edgeSet + M.numFaces =
      2 * numComponents M.rot (dartSymm G) := by
    exact_mod_cast hE
  have hsplit : ∀ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + (2 - 6 / (fLen M d : ℚ))) =
      3 - 6 * (1 / (G.degree d.fst : ℚ)) - 6 * (1 / (fLen M d : ℚ)) := fun d => by ring
  rw [Finset.sum_congr rfl (fun d _ => hsplit d), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hV, hF, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hc]
  linarith

theorem one_le_numComponents (d : G.Dart) : 1 ≤ numComponents M.rot (dartSymm G) := by
  unfold numComponents numClasses
  have : Nonempty (Quotient (compSetoid M.rot (dartSymm G))) := ⟨Quotient.mk _ d⟩
  exact Nat.card_pos

/-- The discharging moves charge between darts without changing the total. -/
theorem sum_split :
    ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + (2 - 6 / (fLen M d : ℚ))) =
      ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + take G d.fst - take G d.snd +
        specI M d.symm) + ∑ d : G.Dart, ((2 - 6 / (fLen M d : ℚ)) - specI M d) := by
  have h1 : ∑ d : G.Dart, take G d.snd = ∑ d : G.Dart, take G d.fst :=
    Equiv.sum_comp (dartSymm G) (fun d => take G d.fst)
  have h2 : ∑ d : G.Dart, specI M d.symm = ∑ d : G.Dart, specI M d :=
    Equiv.sum_comp (dartSymm G) (specI M)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2]
  ring

/-! ### Faces end nonnegative -/

theorem face_sum_nonneg (hδ : ∀ v, 2 ≤ G.degree v) {W : ℕ} (hW : 11 ≤ W)
    (hlight : ∀ u v, G.Adj u v → W ≤ G.degree u + G.degree v) :
    0 ≤ ∑ x : G.Dart, ((2 - 6 / (fLen M x : ℚ)) - specI M x) := by
  rw [← sum_avg_cls (SameCycle.setoid M.facePerm)]
  refine Finset.sum_nonneg (fun x _ => div_nonneg ?_ (Nat.cast_nonneg _))
  set O := cls (SameCycle.setoid M.facePerm) x with hO
  have hlen : ∀ y ∈ O, fLen M y = O.card := fun y hy => by
    unfold fLen
    rw [← cls_eq (mem_cls.1 hy)]
  have hℓ3 : 3 ≤ O.card := three_le_fLen M hδ x
  have h2t := card_add_card_le_of_not M.facePerm (O := O) (Spec M)
    (fun y hy => mem_cls.2 (sameCycle_apply_right.2 (mem_cls.1 hy)))
    (fun y _ h => not_spec_facePerm M h)
  have h4 : 0 < (O.filter (Spec M)).card → 4 ≤ O.card := by
    intro hpos
    obtain ⟨y, hy⟩ := Finset.card_pos.1 hpos
    rw [Finset.mem_filter] at hy
    rw [← hlen y hy.1]
    exact four_le_fLen M hδ hW hlight hy.2
  have hnat : 6 + (O.filter (Spec M)).card ≤ 2 * O.card := by
    rcases Nat.eq_zero_or_pos (O.filter (Spec M)).card with h0 | hpos
    · omega
    · have := h4 hpos
      omega
  have hpos : (0 : ℚ) < O.card := by exact_mod_cast (by omega : 0 < O.card)
  have hsp : ∑ y ∈ O, specI M y = ((O.filter (Spec M)).card : ℚ) := by
    simp only [specI]
    rw [Finset.sum_boole]
  rw [Finset.sum_sub_distrib, hsp, Finset.sum_congr rfl (fun y hy =>
    show (2 - 6 / (fLen M y : ℚ)) = 2 - 6 / (O.card : ℚ) by rw [hlen y hy]),
    Finset.sum_const, nsmul_eq_mul]
  have hmul : (O.card : ℚ) * (2 - 6 / O.card) = 2 * O.card - 6 := by
    field_simp
  rw [hmul]
  have hcast : ((6 + (O.filter (Spec M)).card : ℕ) : ℚ) ≤ ((2 * O.card : ℕ) : ℚ) := by
    exact_mod_cast hnat
  push_cast at hcast
  linarith

/-! ### Vertices end nonnegative -/

theorem vertex_sum_nonneg (δ W : ℕ) (hδ3 : 3 ≤ δ) (hdeg : ∀ v, δ ≤ G.degree v)
    (hlight : ∀ u v, G.Adj u v → W ≤ G.degree u + G.degree v) (hW : 11 ≤ W)
    (harith : ∀ (k s : ℕ) (L : ℚ), 6 ≤ k → s ≤ k → (0 < s → max δ (W - k) ≤ 5) → 0 ≤ L →
      (2 * s - k : ℚ) ≤ L → 0 ≤ (k : ℚ) - 6 - s * (6 / ((max δ (W - k) : ℕ) : ℚ) - 1) + L)
    (v : V) :
    0 ≤ ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v),
      ((1 - 6 / (G.degree d.fst : ℚ)) + take G d.fst - take G d.snd + specI M d.symm) := by
  set F := Finset.univ.filter (fun d : G.Dart => d.fst = v) with hF
  have hFk : F.card = G.degree v := G.dart_fst_fiber_card_eq_degree v
  have hk3 : 3 ≤ G.degree v := hδ3.trans (hdeg v)
  have hkpos : (0 : ℚ) < G.degree v := by exact_mod_cast (by omega : 0 < G.degree v)
  have hmemF : ∀ d ∈ F, d.fst = v := fun d hd => (Finset.mem_filter.1 hd).2
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hA : ∑ d ∈ F, (1 - 6 / (G.degree d.fst : ℚ)) = G.degree v - 6 := by
    rw [Finset.sum_congr rfl (fun d hd => show (1 - 6 / (G.degree d.fst : ℚ)) =
      1 - 6 / (G.degree v : ℚ) by rw [hmemF d hd]), Finset.sum_const, hFk, nsmul_eq_mul]
    field_simp
  have hB : ∑ d ∈ F, take G d.fst = G.degree v * take G v := by
    rw [Finset.sum_congr rfl (fun d hd => show take G d.fst = take G v by rw [hmemF d hd]),
      Finset.sum_const, hFk, nsmul_eq_mul]
  rw [hA, hB]
  by_cases hv : G.degree v ≤ 5
  · have hC : ∑ d ∈ F, take G d.snd = 0 := by
      refine Finset.sum_eq_zero (fun d hd => ?_)
      have := hlight _ _ d.adj
      rw [hmemF d hd] at this
      unfold take
      rw [if_neg (by omega)]
    have hD : ∑ d ∈ F, specI M d.symm = 0 := by
      refine Finset.sum_eq_zero (fun d hd => ?_)
      unfold specI
      rw [if_neg]
      rintro ⟨-, h2, -⟩
      have : d.symm.snd = v := hmemF d hd
      rw [this] at h2
      omega
    rw [hC, hD]
    have ht : take G v = (6 - (G.degree v : ℚ)) / G.degree v := by
      unfold take
      rw [if_pos hv]
    have hmul : (G.degree v : ℚ) * ((6 - G.degree v) / G.degree v) = 6 - G.degree v := by
      field_simp
    rw [ht, hmul]
    linarith
  · have htv : take G v = 0 := by
      unfold take
      rw [if_neg hv]
    rw [htv, mul_zero, add_zero]
    set k := G.degree v with hk
    set m := max δ (W - k) with hm
    set S := F.filter (fun d => G.degree d.snd ≤ 5) with hS
    -- bounds for the small neighbours
    have hsmall : ∀ d ∈ S, m ≤ G.degree d.snd ∧ G.degree d.snd ≤ 5 := by
      intro d hd
      have hd := Finset.mem_filter.1 hd
      have hl := hlight _ _ d.adj
      rw [hmemF d hd.1] at hl
      have := hdeg d.snd
      exact ⟨max_le this (by omega), hd.2⟩
    have hm3 : 3 ≤ m := hδ3.trans (le_max_left _ _)
    have hmpos : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
    have hC : ∑ d ∈ F, take G d.snd ≤ S.card * (6 / (m : ℚ) - 1) := by
      have : ∑ d ∈ F, take G d.snd = ∑ d ∈ S, (6 - (G.degree d.snd : ℚ)) / G.degree d.snd := by
        rw [hS]
        exact (Finset.sum_filter _ _).symm
      rw [this, ← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul S _ _ (fun d hd => ?_)
      obtain ⟨h1, -⟩ := hsmall d hd
      have hj : (0 : ℚ) < G.degree d.snd := by exact_mod_cast (by omega : 0 < G.degree d.snd)
      have hmj : (m : ℚ) ≤ G.degree d.snd := by exact_mod_cast h1
      rw [sub_div, div_self hj.ne']
      have : (6 : ℚ) / G.degree d.snd ≤ 6 / m :=
        div_le_div_of_nonneg_left (by norm_num) hmpos hmj
      linarith
    have hrotF : ∀ d ∈ F, M.rot d ∈ F := fun d hd =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, (M.isRotationSystem.fst_apply d).trans (hmemF d hd)⟩
    have hcount := card_add_card_le M.rot hrotF
      (Finset.filter_subset (fun d : G.Dart => G.degree d.snd ≤ 5) F)
    rw [← hS, hFk] at hcount
    have hsub : S.filter (fun d => M.rot d ∈ S) ⊆ F.filter (fun d => Spec M d.symm) := by
      intro d hd
      have hd := Finset.mem_filter.1 hd
      have hd1 := Finset.mem_filter.1 hd.1
      have hd2 := Finset.mem_filter.1 hd.2
      refine Finset.mem_filter.2 ⟨hd1.1, hd1.2, ?_, ?_⟩
      · change 5 < G.degree d.fst
        rw [hmemF d hd1.1]
        omega
      · rw [M.facePerm_apply, SimpleGraph.Dart.symm_symm]
        exact hd2.2
    have hL : ∑ d ∈ F, specI M d.symm = ((F.filter (fun d => Spec M d.symm)).card : ℚ) := by
      simp only [specI]
      rw [Finset.sum_boole]
    have hL1 : (2 * S.card - k : ℚ) ≤ ∑ d ∈ F, specI M d.symm := by
      rw [hL]
      have := Finset.card_le_card hsub
      have h' : ((S.card + S.card : ℕ) : ℚ) ≤ ((k + (S.filter (fun d => M.rot d ∈ S)).card : ℕ) : ℚ) := by
        exact_mod_cast hcount
      have h'' : (((S.filter (fun d => M.rot d ∈ S)).card : ℕ) : ℚ) ≤
          (((F.filter (fun d => Spec M d.symm)).card : ℕ) : ℚ) := by
        exact_mod_cast this
      push_cast at h' h''
      linarith
    have hL0 : 0 ≤ ∑ d ∈ F, specI M d.symm := by
      rw [hL]
      exact Nat.cast_nonneg _
    have hSk : S.card ≤ k := by
      rw [← hFk]
      exact Finset.card_le_card (Finset.filter_subset _ F)
    have hm5 : 0 < S.card → m ≤ 5 := by
      intro hpos
      obtain ⟨d, hd⟩ := Finset.card_pos.1 hpos
      obtain ⟨h1, h2⟩ := hsmall d hd
      omega
    have key : 0 ≤ (k : ℚ) - 6 - S.card * (6 / (m : ℚ) - 1) + ∑ d ∈ F, specI M d.symm :=
      harith k S.card _ (by omega) hSk hm5 hL0 hL1
    linarith

/-! ### The light edge -/

theorem exists_light [Nonempty V] (hG : IsPlanar G) (δ W : ℕ) (hδ3 : 3 ≤ δ) (hW : 11 ≤ W)
    (hdeg : ∀ v, δ ≤ G.degree v)
    (harith : ∀ (k s : ℕ) (L : ℚ), 6 ≤ k → s ≤ k → (0 < s → max δ (W - k) ≤ 5) → 0 ≤ L →
      (2 * s - k : ℚ) ≤ L → 0 ≤ (k : ℚ) - 6 - s * (6 / ((max δ (W - k) : ℕ) : ℚ) - 1) + L) :
    ∃ u v, G.Adj u v ∧ G.degree u + G.degree v < W := by
  obtain ⟨M⟩ := hG
  by_contra hcon
  push Not at hcon
  have hlight : ∀ u v, G.Adj u v → W ≤ G.degree u + G.degree v := fun u v h => hcon u v h
  obtain ⟨v0⟩ := ‹Nonempty V›
  obtain ⟨u, hu⟩ : ∃ u, G.Adj v0 u := by
    have hpos : 0 < (G.neighborFinset v0).card := by
      rw [G.card_neighborFinset_eq_degree]
      have := hdeg v0
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.1 hpos
    exact ⟨u, by simpa using hu⟩
  have hK : (1 : ℚ) ≤ numComponents M.rot (dartSymm G) := by
    exact_mod_cast one_le_numComponents M ⟨(v0, u), hu⟩
  have hsum := sum_charge M
  rw [sum_split M] at hsum
  have hV : 0 ≤ ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + take G d.fst - take G d.snd +
      specI M d.symm) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun d : G.Dart => d.fst)]
    exact Finset.sum_nonneg (fun v _ => vertex_sum_nonneg M δ W hδ3 hdeg hlight hW harith v)
  have hFc := face_sum_nonneg M (fun v => by have := hdeg v; omega) hW hlight
  linarith

end Kotzig
