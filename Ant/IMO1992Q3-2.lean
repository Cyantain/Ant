import Mathlib

/-
Consider nine points in space, no four of which are coplanar. Each pair of points is joined by an edge (that is, a line segment) and each edge is either colored blue or red or left uncolored. Find the smallest value of n such that whenever exactly n edges are colored, the set of colored edges necessarily contains a triangle all of whose edges have the same color.
-/

section port

-- Helper lemmas ported from or similar to mathlib for Finset min/max properties.

/-- The minimum of a nonempty finset $s$ is $a$ iff $a$ is in $s$ and is a lower bound for $s$. -/
lemma Finset.min'_eq_iff {α : Type*} [LinearOrder α] (s : Finset α) (H : s.Nonempty)
    (a : α) : s.min' H = a ↔ a ∈ s ∧ ∀ (b : α), b ∈ s → a ≤ b :=
  ⟨(· ▸ ⟨min'_mem _ _, min'_le _⟩),
    fun h ↦ le_antisymm (min'_le _ _ h.1) (le_min' _ _ _ h.2)⟩

/-- The maximum of a nonempty finset $s$ is $a$ iff $a$ is in $s$ and is an upper bound for $s$. -/
lemma Finset.max'_eq_iff {α : Type*} [LinearOrder α] (s : Finset α) (H : s.Nonempty)
    (a : α) : s.max' H = a ↔ a ∈ s ∧ ∀ (b : α), b ∈ s → b ≤ a :=
  ⟨(· ▸ ⟨max'_mem _ _, le_max' _⟩),
    fun h ↦ le_antisymm (max'_le _ _ _ h.2) (le_max' _ _ h.1)⟩

end port

section setup

/-- Represents a segment (edge) between two points, identified by indices from "Fin 9".
    The $ini < ter$ condition ensures a canonical representation for each edge. -/
@[ext]
class Seg where
  ini : Fin 9
  ter : Fin 9
  nodup : ini < ter := by decide

/-- A type alias for a finset of 2 points, representing an edge. -/
local notation3 "Fseg" => Finset.powersetCard 2 (Finset.range 9)

/-- Converts a "Seg" to its "Fseg" representation (a 2-element "finset"). -/
abbrev Seg.toFseg : Seg → Fseg := by
  intro x
  use {x.ini.1, x.ter.1}
  refine Finset.mem_powersetCard.2 ?_
  constructor
  · -- Proof that elements are in "range 9".
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    casesm* _ ∨ _
    · exact hy ▸ Finset.mem_range.2 Seg.ini.isLt
    · exact hy ▸ Finset.mem_range.2 Seg.ter.isLt
  · -- Proof that card is 2.
    exact Finset.card_pair <| Nat.ne_of_lt Seg.nodup

/-- A 2-element "finset" is nonempty. -/
lemma nonem {y : Fseg} : y.1.Nonempty :=
  Finset.card_pos.1
    <| Eq.mpr (congrArg _
      (Finset.mem_powersetCard.1 y.2).2) Nat.zero_lt_two

/-- The smaller point index in an "Fseg". -/
def Fseg_min (y : Fseg) := y.1.min' nonem
/-- The larger point index in an "Fseg". -/
def Fseg_max (y : Fseg) := y.1.max' nonem

/-- The smaller point index lies in "Fseg". -/
lemma Fseg_min_mem (y : Fseg) : Fseg_min y ∈ y.1 :=
  Finset.min'_mem y.1 nonem
/-- The larger point index lies in "Fseg". -/
lemma Fseg_max_mem (y : Fseg) : Fseg_max y ∈ y.1 :=
  Finset.max'_mem y.1 nonem
/-- The smaller point index is strictly smaller than the larger point index. -/
lemma Fseg_min_lt_max (y : Fseg) : Fseg_min y < Fseg_max y :=
  have := Finset.mem_powersetCard.1 y.2
  Finset.min'_lt_max'_of_card y.1 (by omega)

/-- A 2-element "finset" is determined by its min and max elements. -/
lemma Fseg_eq (y : Fseg) : y.1 = {y.1.min' nonem, y.1.max' nonem} := by
  have : {Fseg_min y, Fseg_max y} ⊆ y.1 :=
    Finset.insert_subset (Fseg_min_mem y) <|
      Finset.singleton_subset_iff.mpr (Fseg_max_mem y)
  refine Finset.eq_of_superset_of_card_ge this ?_
  show _ ≤ Finset.card {Fseg_min y, Fseg_max y}
  rw [Finset.card_pair <| Nat.ne_of_lt (Fseg_min_lt_max y),
    (Finset.mem_powersetCard.1 y.2).2]

/-- Converts an "Fseg" (a 2-element "finset") back to a "Seg". -/
abbrev Seg.ofFseg : Fseg → Seg := fun y ↦
  ⟨⟨Fseg_min y, List.mem_range.mp <|
    (Finset.mem_powersetCard.1 y.2).1 (Fseg_min_mem y)⟩,
   ⟨Fseg_max y, List.mem_range.mp <|
    (Finset.mem_powersetCard.1 y.2).1 (Fseg_max_mem y)⟩, Fseg_min_lt_max y⟩

/-- "ofFseg" is the left inverse of "toFseg". -/
lemma left_inv {x : Seg} : Seg.ofFseg x.toFseg = x := by
  simp [Seg.toFseg, Seg.ofFseg]
  ext
  · simp [Fseg_min, Finset.min'_eq_iff]
    exact Fin.le_of_lt x.nodup
  · simp [Fseg_max, Finset.max'_eq_iff]
    exact Fin.le_of_lt x.nodup

/-- "toFseg" is the right inverse of "ofFseg". -/
lemma right_inv {y : Fseg} : (Seg.ofFseg y).toFseg = y := by
  simp [Seg.toFseg, Seg.ofFseg]
  apply Subtype.val_inj.1
  nth_rw 2 [Fseg_eq]
  rfl

/-- An equivalence between the canonical "Seg" representation and the "Fseg" representation. -/
def Seg_FS : Seg ≃ Fseg where
  toFun := Seg.toFseg
  invFun := Seg.ofFseg
  left_inv := fun _ ↦ left_inv
  right_inv := fun _ ↦ right_inv

/-- Establishes "Seg" as a finite type. -/
instance : Fintype Seg :=
  Fintype.ofEquiv Fseg Seg_FS.symm

/-- A coloring scheme: maps each edge to an optional color (red/blue, i.e., "Fin 2").
    "none" means the edge is uncolored. -/
notation "scheme" => Seg → Option (Fin 2)

/-- Represents a triangle, defined by three ordered points $a < b < c$. -/
class Tri where
  a : Fin 9
  b : Fin 9
  c : Fin 9
  nodup : a < b ∧ b < c := by decide

/-- The three segments (edges) forming a triangle. -/
abbrev Tri.toSegs (y : Tri) : List Seg :=
  [⟨y.a, y.b, y.nodup.1⟩, ⟨y.b, y.c, y.nodup.2⟩,
    ⟨y.a, y.c, y.nodup.1.trans y.nodup.2⟩]

/-- A triangle is "not monochromatic" if at least one edge is uncolored,
    or if the colored edges have more than one distinct color. -/
abbrev Tri.notMono (y : Tri) (f : scheme) : Prop :=
  have list := (Tri.toSegs y).map f
  list.contains (none (α := Fin 2)) ∨ 1 < list.dedup.length

/-- The set of uncolored ("void") edges in a scheme. -/
abbrev void (f : scheme) : Finset Seg :=
  (Finset.univ (α := Seg)).filter (f · = none)

/-- The set of colored edges in a scheme. -/
abbrev colored (f : scheme) : Finset Seg :=
  (Finset.univ (α := Seg)).filter (f · ≠ none)

/-- predicate that a scheme has no monochromatic triangles. -/
abbrev Scheme.noMono (f : scheme) : Prop :=
  ∀ y : Tri, y.notMono f

end setup

/-- The minimal number of colored edges that guarantees a monochromatic triangle is 33. -/
theorem IMO1992Q3 :
    Minimal {n : ℕ | ∀ f : scheme, (colored f).card = n → ¬ Scheme.noMono f} 33 := by
  sorry
