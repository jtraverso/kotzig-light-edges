# Kotzig's theorem on light edges of planar graphs in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of Kotzig's theorem on light edges and its relatives. The
*weight* of an edge `uv` is `deg u + deg v`.

| Lean (namespace `KotzigTheorem`) | Statement |
|---|---|
| `kotzig_borodin` | A planar graph of minimum degree at least three has an edge of weight at most `13` (the form without `3`-connectivity, conjectured by Erdős and proved by Borodin, 1989). |
| `light_edge_minDegree_four` | A planar graph of minimum degree at least four has an edge of weight at most `11`. |
| `kotzig` | **Kotzig (1955).** A `3`-connected planar graph has an edge of weight at most `13`, and at most `11` if it has no vertex of degree three. |
| `wernicke` | **Wernicke (1904).** A planar graph of minimum degree at least five has a vertex of degree five adjacent to a vertex of degree at most six. |

All graphs are finite simple graphs (Mathlib `SimpleGraph` on a `Fintype`).

## Planarity

Planarity is combinatorial, as in the registered entry
[Kuratowski's theorem](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000018&version=1)
([`jtraverso/kuratowski`](https://github.com/jtraverso/kuratowski) @ `696ec89`, a pinned
dependency): a *plane map* is a rotation system of the darts of `G` whose hypermap has Euler defect
`0`, and `G` is planar if it has one. The definitions, from `numClasses` to `IsPlanar`, are copied
verbatim from that entry's `Challenge.lean`. By the Heffter–Edmonds–Ringel rotation principle
these are the embeddings in the sphere; that correspondence is not formalized.

## The proof

A discharging argument run directly on the rotation system (`Kotzig/Discharging.lean`), after
the proof of Lemma 3.2 of Cranston–West, *An introduction to the discharging method via graph
coloring* ([arXiv:1306.4434](https://arxiv.org/abs/1306.4434)), with the triangulation step
replaced by face charges:

- every dart `d` gets `(1 - 6 / deg (tail d)) + (2 - 6 / |face d|)`; by Euler's formula
  (`PlaneMap.euler` of the Kuratowski library) the total is `-12 K < 0` (`sum_charge`);
- assume every edge has weight at least `W` (`14`, resp. `12`); small vertices (degree at most
  five) take `(6 - deg) / deg` through each dart; every face gives `1` to each corner of a big
  vertex between two small neighbours: such corners are never consecutive on a face and never on a
  triangle, so faces stay nonnegative (`face_sum_nonneg`);
- a big vertex of degree `k` with `s` small neighbours loses at most `s (6/m - 1)`, where
  `m = max δ (W - k)`, and gains at least `2s - k`; it stays nonnegative (`vertex_sum_nonneg`,
  with the arithmetic in `Kotzig/Main.lean`), a contradiction.

Kotzig's statement follows because a `3`-connected graph has minimum degree at least three, and
Wernicke's from the weight-`11` bound.

## Files

- [`KotzigChallenge.lean`](KotzigChallenge.lean): the definitions and the four statements; it
  imports only Mathlib.
- [`KotzigSolution.lean`](KotzigSolution.lean): the same definitions, the planarity bridge to the
  Kuratowski library (field by field) and the four theorems.
- `Kotzig/Counting.lean` (sums over orbits, pigeonhole on cycles), `Kotzig/Discharging.lean`,
  `Kotzig/Main.lean`.
- [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml).

## Not included

The sharpness examples (`13` and `11` are attained) and the stronger alternative of Borodin's
lemma (an edge of weight at most `11` or a `4`-cycle through two `3`-vertices and a common
neighbour of degree at most `10`).

## Checks

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```
lake exe cache get
lake build
```

No `sorry`; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` for the four
theorems; the elaborated statements and definitions of `KotzigChallenge.lean` and
`KotzigSolution.lean` are identical (`pp.all`).

The Lean development is AI-written under the author's direction (see `formalization.yaml`).
