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

/-- The total number of segments (edges) is $\binom{9}{2} = 36$. -/
lemma Seg.card : Nat.card Seg = 36 := by
  rw [Nat.card_congr Seg_FS, Nat.card_eq_finsetCard,
    Finset.card_powersetCard]
  decide

/-- A specific coloring scheme with 32 colored edges, used as a counterexample. -/
def n_32 : scheme := fun ⟨ini, ter, _⟩ ↦
  match ini with
  | 0 => match ter with
    | 1 => some 0 | 2 => none   | 3 => some 0 | 4 => some 0
    | 5 => some 1 | 6 => some 0 | 7 => some 1 | 8 => some 1
  | 1 => match ter with
    | 2 => some 0 | 3 => none   | 4 => some 1 | 5 => some 0
    | 6 => some 1 | 7 => some 0 | 8 => some 1
  | 2 => match ter with
    | 3 => some 0 | 4 => some 0 | 5 => some 1 | 6 => some 0
    | 7 => some 1 | 8 => some 1
  | 3 => match ter with
    | 4 => some 1 | 5 => some 0 | 6 => some 1 | 7 => some 0
    | 8 => some 1
  | 4 => match ter with
    | 5 => some 1 | 6 => none   | 7 => some 1 | 8 => some 0
  | 5 => match ter with
    | 6 => some 1 | 7 => none   | 8 => some 0
  | 6 => match ter with
    | 7 => some 1 | 8 => some 0
  | 7 => match ter with | 8 => some 0
  | 8 => by omega

/-- Asserts that "Seg" has decidable equality. -/
instance : DecidableEq Seg := by
  intro a b
  rw [Seg.ext_iff]
  exact instDecidableAnd

/-- The sum of uncolored and colored edges is the total number of edges (36). -/
lemma void_add_colored (f : scheme) :
    (void f).card + (colored f).card = 36 := by
  rw [← Seg.card, Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _)]
  congr
  exact Finset.filter_union_filter_neg_eq _ _

/-- Proof that the "n_32" scheme has no monochromatic triangles. -/
lemma n_32_noMono : Scheme.noMono n_32 := by
  intro ⟨a, b, c, nodup⟩
  -- Proof by exhaustive case check. This step is slow, please wait patiently.
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals first | omega | decide +revert

/-- If a triangle is monochromatic, all its edges are colored with the same color $i$. -/
lemma Tri.not_notMono (y : Tri) (f : scheme) (hf : ¬ y.notMono f) :
    ∃ i, (Tri.toSegs y).map f = [i, i, i] ∧ i ≠ none := by
  unfold Tri.notMono at hf
  set list := List.map f y.toSegs with def_2
  -- hf now means no "none" and "dedup.length" $\leq 1$.
  simp at hf
  obtain ⟨hf1 : ¬ (none ∈ list), hf2⟩ := hf
  rw [List.mem_map] at hf1
  push_neg at hf1
  -- Since the list is non-empty and has no "none", "dedup.length" must be 1.
  obtain (hf | hf) : list.dedup.length = 0 ∨ list.dedup.length = 1 := by omega
  · replace hf := (List.dedup_eq_nil _).1 <| List.eq_nil_of_length_eq_zero hf
    rw [def_2, List.map_eq_nil_iff] at hf
    tauto
  · -- "dedup" has a single element $a$.
    obtain ⟨a, ha⟩ := List.length_eq_one.1 hf
    -- This means all elements of the original list are $a$.
    have : ∀ x ∈ list, x = a := by
      intro x hx
      rw [← List.mem_dedup, ha] at hx
      simpa using hx
    use a
    constructor
    · simpa [def_2] using this
    · -- $a$ cannot be none.
      intro ha_none
      rw [def_2] at this
      absurd hf1
      push_neg
      use y.toSegs[0]
      constructor
      · tauto
      · specialize this (f y.toSegs[0]) (List.mem_of_mem_head? rfl)
        exact ha_none ▸ this

/-- For any $y \leq 32$, there exists a coloring with $y$ edges that has no monochromatic triangle.
    This shows that the answer $n$ must be greater than 32. -/
lemma IMO1992Q3_n_32_case_1 {y : ℕ} (ylt : y ≤ 32) : ¬ ∀ (f : scheme),
    (colored f).card = y → ¬Scheme.noMono f := by
  -- We construct a counterexample by taking a subset of $y$ edges from the "n_32" scheme.
  set new := ((colored n_32).toList.splitAt y).1.toFinset with new_def
  push_neg
  use fun x ↦ if x ∈ new then n_32 x else none
  have foo : (List.splitAt y (colored n_32).toList).1 ⊆ (colored n_32).toList := by
    simp only [List.splitAt_eq]
    exact List.take_subset _ _
  have nodup : (List.splitAt y (colored n_32).toList).1.Nodup := by
    refine (List.Sublist.nodup (l₂ := (colored n_32).toList)) ?_ ?_
    · simp only [List.splitAt_eq]
      exact List.take_sublist _ _
    · exact Finset.nodup_toList (colored n_32)
  have mem_new {x} : x ∈ new → ¬n_32 x = none := by
    intro h
    rw [new_def, List.mem_toFinset] at h
    simpa only [Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, ne_eq, true_and] using foo h
  constructor
  · -- The number of colored edges is exactly $y$.
    simp [colored]
    have {x} : (x ∈ new ∧ ¬n_32 x = none) ↔ x ∈ new := by
      constructor
      · tauto
      · exact fun h ↦ And.symm ⟨mem_new h, h⟩
    conv =>
      enter [1, 1, 1, x]
      rw [this]
    rw [Finset.filter_univ_mem, new_def, List.toFinset_card_of_nodup nodup,
      List.splitAt_eq, List.length_take, Finset.length_toList, inf_eq_left]
    exact ylt
  · -- This new scheme has no monochromatic triangles.
    intro t
    have h_n32 := n_32_noMono t
    -- Assume there is a monochromatic triangle $t$.
    by_contra h
    obtain ⟨a, ha⟩ := Tri.not_notMono t _ h
    unfold Tri.notMono at h_n32
    set list' := List.map n_32 t.toSegs with def_2
    dsimp at h_n32
    -- If $t$ is monochromatic in our new scheme, all its edges must be in "new".
    have {x} : x ∈ t.toSegs → x ∈ new := by
      intro hx
      by_contra!
      have : none ∈ [a, a, a] := by
        rw [← ha.1, List.mem_map]
        use x, hx
        simp [this]
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at this
      exact ha.2 this.symm
    -- This implies $t$ would also be monochromatic in the original "n_32" scheme.
    replace this : [a, a, a] = list' := by
      rw [def_2, ← ha.1]
      refine List.map_inj_left.mpr ?_
      intro a ha
      simp [this ha]
    -- This contradicts "n_32_noMono".
    absurd h_n32
    push_neg
    constructor
    · rw [← this]
      simp only [List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, or_self, ne_eq,
        decide_eq_true_eq]
      exact ha.2.symm
    · rw [← this]
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self, List.dedup_cons_of_mem,
        not_false_eq_true, List.dedup_cons_of_not_mem, List.dedup_nil, List.length_cons,
        List.length_nil, zero_add, le_refl]

/-- If exactly 3 edges are uncolored, there exists a set of 6 points (a $K6$)
    where all edges are colored. -/
lemma select {f : scheme} (hf : (void f).card = 3) :
    ∃ xs : Finset (Fin 9), xs.card = 6 ∧
      ∀ x ∈ xs, ∀ y ∈ xs, (hxy : x < y) → f ⟨x, y, hxy⟩ ≠ none := by
  -- Get the three uncolored edges.
  obtain ⟨s1, s2, s3, h⟩ := Finset.card_eq_three.1 hf
  -- Consider the set of points that are NOT the starting point of an uncolored edge.
  set base : Finset (Fin 9) := Finset.univ \ {s1.1, s2.1, s3.1} with def_base
  -- This set has at least $9 - 3 = 6$ points.
  have base_card : 6 ≤ base.card := by
    rw [Finset.card_univ_diff]
    show 6 ≤ 9 - _
    have : Finset.card {s1.1, s2.1, s3.1} ≤ 3 := Finset.card_le_three
    omega
  -- Take a subset "xs" of size 6 from "base".
  obtain ⟨xs, hxs⟩ : ∃ xs : Finset (Fin 9), xs ⊆ base ∧ xs.card = 6 :=
    Finset.le_card_iff_exists_subset_card.mp base_card
  use xs, hxs.2
  -- Any edge between two points in "xs" must be colored.
  intro x hx y hy hxy
  -- Assume an edge $c$ between $x$ and $y$ is uncolored.
  by_contra!
  replace this : ⟨x, y, hxy⟩ ∈ void f := by
    simpa [void]
  set c : Seg := ⟨x, y, hxy⟩
  -- Then $c$ must be one of $s1, s2, s3$.
  simp [h.2.2.2] at this
  rw [def_base] at hxs
  have hxs1 := hxs.1 hx
  have hxs2 := hxs.1 hy
  simp at hxs1 hxs2
  -- This implies $c.ini = x$ is one of $\{s1.ini, s2.ini, s3.ini\}$.
  -- But $x$ was chosen from "base", which excludes these points. Contradiction.
  simp [Seg.ext_iff] at this
  tauto

/-- A helper lemma for ordering three distinct points. -/
lemma split_or {xs : Finset (Fin 9)} {a b c : xs}
  (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c) (hab : a < b) :
    c < a ∨ (a < c ∧ c < b) ∨ b < c := by
  replace habc : a.1 ≠ b ∧ a.1 ≠ c ∧ b.1 ≠ c := by
    simp only [ne_eq, Subtype.val_inj]
    exact habc
  replace hab : a.1 < b.1 := hab
  show c.1 < a ∨ (a.1 < c ∧ c.1 < b) ∨ b.1 < c
  by_cases hbc : b.1 < c
  · omega
  · replace hbc : c.1 < b := by omega
    · by_cases hac : a.1 < c
      · omega
      · replace hac : c.1 < a := by omega
        omega

/-- If an option is not "none" and not "some $y$", it must be "some $(1-y)$". -/
lemma option_reduce {y : Fin 2} {x : Option (Fin 2)} (hx1 : x ≠ none) (hx2 : x ≠ y) :
    x = some (1 - y) := by
  match hx : x with
  | none => exact False.elim (hx1 rfl)
  | some 0 =>
    rw [Fin.eq_one_of_neq_zero y fun a ↦ hx2 (congrArg some a.symm)]; rfl
  | some 1 => match y with | 0 => rfl | 1 => exact False.elim (hx2 rfl)

/-- Ramsey's Theorem $R(3,3)=6$: Any 2-coloring of the edges of a $K6$ contains a
    monochromatic triangle. -/
lemma ramsey {f : scheme} {xs : Finset (Fin 9)} (hxs1 : xs.card = 6)
  (hxs2 : ∀ x ∈ xs, ∀ y ∈ xs, (hxy : x < y) → f ⟨x, y, hxy⟩ ≠ none) :
    ∃ t : Tri, ¬ t.notMono f := by
  have xs_nonem : xs.Nonempty := by
    rw [← Finset.card_ne_zero, hxs1]
    decide
  -- Pick a vertex $p$ from the $K6$.
  set p := xs.max' xs_nonem with def_p
  -- Consider the other 5 vertices "xs'".
  set xs' := xs.erase p with def_xs'
  have xs'_card : xs'.card = 5 := by
    rw [def_xs', Finset.card_erase_of_mem, hxs1]
    exact Finset.max'_mem xs xs_nonem
  have i_lt_p {i : xs'} := xs.lt_max'_of_mem_erase_max' xs_nonem i.2
  -- The 5 edges from $p$ to "xs'" are all colored.
  have f_ip {i : xs'} := Option.ne_none_iff_exists'.1 <|
    hxs2 i ((Finset.erase_subset p xs) i.2) p
      (xs.max'_mem xs_nonem) i_lt_p
  -- By pigeonhole, at least 3 of these 5 edges have the same color.
  set f' : xs' → Fin 2 := fun i ↦
    Classical.choose f_ip
  have card1 : Fintype.card (Fin 2) = 2 := by decide
  have card2 : Fintype.card xs' = 5 := by
    rw [Fintype.card.eq_1, Finset.univ_eq_attach,
      Finset.card_attach, xs'_card]
  obtain ⟨y, hy⟩ := @Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to xs' (Fin 2) _
    Finset.univ Finset.univ f' 2 (fun a _ ↦ Finset.mem_univ (f' a))
    <| by rw [Finset.univ_eq_attach, Finset.card_attach, xs'_card]; decide
  simp only [Finset.mem_univ, Finset.univ_eq_attach, true_and] at hy
  -- Let these 3 vertices be $a, b, c$, and the common color be $y$.
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := Finset.two_lt_card.1 hy
  simp only [Finset.mem_filter, Finset.mem_attach, true_and] at ha hb hc
  wlog hab : a < b
  · specialize @this f xs hxs1 hxs2 xs_nonem def_p def_xs' xs'_card _ _ card1 card2
      y hy b a c ⟨habc.1.symm, habc.2.2, habc.2.1⟩ hb ha hc
    refine this ?_
    simp at hab
    exact lt_of_le_of_ne hab habc.1.symm
  -- Edges (a,p), (b,p), (c,p) are all colored $y$.
  have h1 : f ⟨b, p, i_lt_p⟩ = f' b := Classical.choose_spec f_ip
  have h2 : f ⟨a, p, i_lt_p⟩ = f' a := Classical.choose_spec f_ip
  have h3 : f ⟨c, p, i_lt_p⟩ = f' c := Classical.choose_spec f_ip
  rw [ha] at h2
  rw [hb] at h1
  rw [hc] at h3
  have f_none {i j : {x // x ∈ xs'}} (hij : i < j) :=
    hxs2 i ((Finset.erase_subset p xs) i.2) j
      ((Finset.erase_subset p xs) j.2) hij
  -- Consider the triangle formed by $a, b, c$.
  obtain (hγ | hγ | hγ) := split_or habc hab
  · -- Case 1: $c < a < b$
    -- If any edge of triangle $(a,b,c)$ has color $y$...
    by_cases bottom :
      f ⟨a, b, hab⟩ = some y ∨
      f ⟨c, a, hγ⟩ = some y ∨
      f ⟨c, b, hγ.trans hab⟩ = some y
    · -- ...we have a monochromatic triangle of color $y$.
      casesm* _ ∨ _
      · use ⟨a, b, p, ⟨hab, i_lt_p⟩⟩
        simp [Tri.notMono, h1, h2, h3, bottom]
      · use ⟨c, a, p, ⟨hγ, i_lt_p⟩⟩
        simp [Tri.notMono, h1, h2, h3, bottom]
      · use ⟨c, b, p, ⟨hγ.trans hab, i_lt_p⟩⟩
        simp [Tri.notMono, h1, h2, h3, bottom]
    · -- Otherwise, all edges of triangle $(a,b,c)$ have the other color $1-y$.
      use ⟨c, a, b, ⟨hγ, hab⟩⟩
      push_neg at bottom
      replace h1 := option_reduce (f_none hab) bottom.1
      replace h2 := option_reduce (f_none hγ) bottom.2.1
      replace h3 := option_reduce (f_none (hγ.trans hab)) bottom.2.2
      simp [Tri.notMono, h1, h2, h3, bottom]
  · -- Case 2: $a < c < b$ (and other cases are similar)
    by_cases bottom :
      f ⟨a, c, hγ.1⟩ = some y ∨
      f ⟨c, b, hγ.2⟩ = some y ∨
      f ⟨a, b, hγ.1.trans hγ.2⟩ = some y
    · casesm* _ ∨ _
      · use ⟨a, c, p, ⟨hγ.1, i_lt_p⟩⟩
        simp [Tri.notMono, h1, h2, h3, bottom]
      · use ⟨c, b, p, ⟨hγ.2, i_lt_p⟩⟩
        simp [Tri.notMono, h1, h2, h3, bottom]
      · use ⟨a, b, p, ⟨hγ.1.trans hγ.2, i_lt_p⟩⟩
        simp [Tri.notMono, h1, h2, h3, bottom]
    · use ⟨a, c, b, hγ⟩
      push_neg at bottom
      replace h1 := option_reduce (f_none hγ.1) bottom.1
      replace h2 := option_reduce (f_none hγ.2) bottom.2.1
      replace h3 := option_reduce (f_none (hγ.1.trans hγ.2)) bottom.2.2
      simp [Tri.notMono, h1, h2, h3, bottom]
  · -- Case 3: $a < b < c$
    by_cases bottom :
      f ⟨a, b, hab⟩ = some y ∨
      f ⟨b, c, hγ⟩ = some y ∨
      f ⟨a, c, hab.trans hγ⟩ = some y
    · casesm* _ ∨ _
      · use ⟨a, b, p, ⟨hab, i_lt_p⟩⟩
        simp [Tri.notMono, h1, h2, h3, bottom]
      · use ⟨b, c, p, ⟨hγ, i_lt_p⟩⟩
        simp [Tri.notMono, h1, h2, h3, bottom]
      · use ⟨a, c, p, ⟨hab.trans hγ, i_lt_p⟩⟩
        simp [Tri.notMono, h1, h2, h3, bottom]
    · use ⟨a, b, c, ⟨hab, hγ⟩⟩
      push_neg at bottom
      replace h1 := option_reduce (f_none hab) bottom.1
      replace h2 := option_reduce (f_none hγ) bottom.2.1
      replace h3 := option_reduce (f_none (hab.trans hγ)) bottom.2.2
      simp [Tri.notMono, h1, h2, h3, bottom]

/-- The minimal number of colored edges that guarantees a monochromatic triangle is 33. -/
theorem IMO1992Q3 :
    Minimal {n : ℕ | ∀ f : scheme, (colored f).card = n → ¬ Scheme.noMono f} 33 := by
  apply minimal_iff_forall_lt.2
  constructor
  · -- Part 1: Show that $n=33$ is sufficient.
    change ∀ (f : scheme), (colored f).card = 33 → ¬Scheme.noMono f
    intro f hf
    -- If 33 edges are colored, then $36 - 33 = 3$ edges are uncolored.
    replace hf : (void f).card = 3 := by
      have := hf ▸ void_add_colored f
      omega
    -- This implies there is a $K6$ with all edges colored.
    obtain ⟨xs, hxs1, hxs2⟩ := select hf
    dsimp [Scheme.noMono]
    push_neg
    -- By Ramsey's theorem, this $K6$ must contain a monochromatic triangle.
    exact ramsey hxs1 hxs2
  · -- Part 2: Show that any $n < 33$ is not sufficient.
    intro y ylt hy
    change ∀ (f : scheme), (colored f).card = y → ¬Scheme.noMono f at hy
    replace ylt : y ≤ 32 := Nat.le_of_lt_succ ylt
    -- We use the counterexample "n_32" to show that for any $y \leq 32$,
    -- there exists a coloring with no monochromatic triangle.
    exact IMO1992Q3_n_32_case_1 ylt hy
