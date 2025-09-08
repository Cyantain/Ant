import Mathlib

section port

lemma Finset.min'_eq_iff {α : Type*} [LinearOrder α] (s : Finset α) (H : s.Nonempty)
    (a : α) : s.min' H = a ↔ a ∈ s ∧ ∀ (b : α), b ∈ s → a ≤ b :=
  ⟨(· ▸ ⟨min'_mem _ _, min'_le _⟩),
    fun h ↦ le_antisymm (min'_le _ _ h.1) (le_min' _ _ _ h.2)⟩

lemma Finset.max'_eq_iff {α : Type*} [LinearOrder α] (s : Finset α) (H : s.Nonempty)
    (a : α) : s.max' H = a ↔ a ∈ s ∧ ∀ (b : α), b ∈ s → b ≤ a :=
  ⟨(· ▸ ⟨max'_mem _ _, le_max' _⟩),
    fun h ↦ le_antisymm (max'_le _ _ _ h.2) (le_max' _ _ h.1)⟩

end port

@[ext]
class Seg where
  ini : Fin 9
  ter : Fin 9
  nodup : ini < ter := by decide

local notation3 "Fseg" => Finset.powersetCard 2 (Finset.range 9)

abbrev Seg.toFseg : Seg → Fseg := by
  intro x
  use {x.ini.1, x.ter.1}
  refine Finset.mem_powersetCard.2 ?_
  constructor
  · intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    casesm* _ ∨ _
    · exact hy ▸ Finset.mem_range.2 Seg.ini.isLt
    · exact hy ▸ Finset.mem_range.2 Seg.ter.isLt
  · exact Finset.card_pair <| Nat.ne_of_lt Seg.nodup

lemma nonem {y : Fseg} : y.1.Nonempty :=
  Finset.card_pos.1
    <| Eq.mpr (congrArg _
      (Finset.mem_powersetCard.1 y.2).2) Nat.zero_lt_two

def Fseg_min (y : Fseg) := y.1.min' nonem
def Fseg_max (y : Fseg) := y.1.max' nonem

lemma Fseg_min_mem (y : Fseg) : Fseg_min y ∈ y.1 :=
  Finset.min'_mem y.1 nonem
lemma Fseg_max_mem (y : Fseg) : Fseg_max y ∈ y.1 :=
  Finset.max'_mem y.1 nonem
lemma Fseg_min_lt_max (y : Fseg) : Fseg_min y < Fseg_max y :=
  have := Finset.mem_powersetCard.1 y.2
  Finset.min'_lt_max'_of_card y.1 (by omega)

lemma Fseg_eq (y : Fseg) : y.1 = {y.1.min' nonem, y.1.max' nonem} := by
  have : {Fseg_min y, Fseg_max y} ⊆ y.1 :=
    Finset.insert_subset (Fseg_min_mem y) <|
      Finset.singleton_subset_iff.mpr (Fseg_max_mem y)
  refine Finset.eq_of_superset_of_card_ge this ?_
  show _ ≤ Finset.card {Fseg_min y, Fseg_max y}
  rw [Finset.card_pair <| Nat.ne_of_lt (Fseg_min_lt_max y),
    (Finset.mem_powersetCard.1 y.2).2]

abbrev Seg.ofFseg : Fseg → Seg := fun y ↦
  ⟨⟨Fseg_min y, List.mem_range.mp <|
    (Finset.mem_powersetCard.1 y.2).1 (Fseg_min_mem y)⟩,
   ⟨Fseg_max y, List.mem_range.mp <|
    (Finset.mem_powersetCard.1 y.2).1 (Fseg_max_mem y)⟩, Fseg_min_lt_max y⟩

lemma left_inv {x : Seg} : Seg.ofFseg x.toFseg = x := by
  simp [Seg.toFseg, Seg.ofFseg]
  ext
  · simp [Fseg_min, Finset.min'_eq_iff]
    exact Fin.le_of_lt x.nodup
  · simp [Fseg_max, Finset.max'_eq_iff]
    exact Fin.le_of_lt x.nodup

lemma right_inv {y : Fseg} : (Seg.ofFseg y).toFseg = y := by
  simp [Seg.toFseg, Seg.ofFseg]
  apply Subtype.val_inj.1
  nth_rw 2 [Fseg_eq]
  rfl

def Seg_FS : Seg ≃ Fseg where
  toFun := Seg.toFseg
  invFun := Seg.ofFseg
  left_inv := fun _ ↦ left_inv
  right_inv := fun _ ↦ right_inv

instance : Fintype Seg :=
  Fintype.ofEquiv Fseg Seg_FS.symm

lemma Seg.card : Nat.card Seg = 36 := by
  rw [Nat.card_congr Seg_FS, Nat.card_eq_finsetCard,
    Finset.card_powersetCard]
  decide

local notation "scheme" => Seg → Option (Fin 2)

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

class Tri where
  a : Fin 9
  b : Fin 9
  c : Fin 9
  nodup : a < b ∧ b < c := by decide

abbrev Tri.toSegs (y : Tri) : List Seg :=
  [⟨y.a, y.b, y.nodup.1⟩, ⟨y.b, y.c, y.nodup.2⟩,
    ⟨y.a, y.c, y.nodup.1.trans y.nodup.2⟩]

abbrev Tri.notMono (y : Tri) (f : scheme) : Prop :=
  have list := (Tri.toSegs y).map f
  list.contains (none (α := Fin 2)) ∨ 1 < list.dedup.length

abbrev void (f : scheme) : Finset Seg :=
  (Finset.univ (α := Seg)).filter (f · = none)

abbrev colored (f : scheme) : Finset Seg :=
  (Finset.univ (α := Seg)).filter (f · ≠ none)

instance : DecidableEq Seg := by
  intro a b
  rw [Seg.ext_iff]
  exact instDecidableAnd

lemma void_add_colored (f : scheme) :
    (void f).card + (colored f).card = 36 := by
  rw [← Seg.card, Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _)]
  congr
  exact Finset.filter_union_filter_neg_eq _ _

abbrev Scheme.noMono (f : scheme) : Prop :=
  ∀ y : Tri, y.notMono f

lemma n_32_noMono : Scheme.noMono n_32 := by
  intro ⟨a, b, c, nodup⟩
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals first | omega | decide +revert

example : Tri.notMono {a := 0, b := 2, c := 4} n_32 := by decide
example : (void n_32).card = 4 := by decide
example : (colored n_32).card = 32 := by decide

lemma Tri.not_notMono (y : Tri) (f : scheme) (hf : ¬ y.notMono f) :
    ∃ i, (Tri.toSegs y).map f = [i, i, i] ∧ i ≠ none := by
  unfold Tri.notMono at hf
  set list := List.map f y.toSegs with def_2
  simp at hf
  obtain ⟨hf1 : ¬ (none ∈ list), hf2⟩ := hf
  rw [List.mem_map] at hf1
  push_neg at hf1
  obtain (hf | hf) : list.dedup.length = 0 ∨ list.dedup.length = 1 := by omega
  · replace hf := (List.dedup_eq_nil _).1 <| List.eq_nil_of_length_eq_zero hf
    rw [def_2, List.map_eq_nil_iff] at hf
    tauto
  · obtain ⟨a, ha⟩ := List.length_eq_one.1 hf
    have : ∀ x ∈ list, x = a := by
      intro x hx
      rw [← List.mem_dedup, ha] at hx
      simpa using hx
    use a
    constructor
    · simpa [def_2] using this
    · intro ha_none
      rw [def_2] at this
      absurd hf1
      push_neg
      use y.toSegs[0]
      constructor
      · tauto
      · specialize this (f y.toSegs[0]) (List.mem_of_mem_head? rfl)
        exact ha_none ▸ this

lemma IMO1992Q3_n_32_case_1 {y : ℕ} (ylt : y ≤ 32) : ¬ ∀ (f : scheme),
    (colored f).card = y → ¬Scheme.noMono f := by
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
  · simp [colored]
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
  · intro t
    have h_n32 := n_32_noMono t
    by_contra h
    obtain ⟨a, ha⟩ := Tri.not_notMono t _ h
    unfold Tri.notMono at h_n32
    set list' := List.map n_32 t.toSegs with def_2
    dsimp at h_n32
    have {x} : x ∈ t.toSegs → x ∈ new := by
      intro hx
      by_contra!
      have : none ∈ [a, a, a] := by
        rw [← ha.1, List.mem_map]
        use x, hx
        simp [this]
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at this
      exact ha.2 this.symm
    replace this : [a, a, a] = list' := by
      rw [def_2, ← ha.1]
      refine List.map_inj_left.mpr ?_
      intro a ha
      simp [this ha]
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

lemma select {f : scheme} (hf : (void f).card = 3) :
    ∃ xs : Finset (Fin 9), xs.card = 6 ∧
      ∀ x ∈ xs, ∀ y ∈ xs, (hxy : x < y) → f ⟨x, y, hxy⟩ ≠ none := by
  obtain ⟨s1, s2, s3, h⟩ := Finset.card_eq_three.1 hf
  set base : Finset (Fin 9) := Finset.univ \ {s1.1, s2.1, s3.1} with def_base
  have base_card : 6 ≤ base.card := by
    rw [Finset.card_univ_diff]
    show 6 ≤ 9 - _
    have : Finset.card {s1.1, s2.1, s3.1} ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨xs, hxs⟩ : ∃ xs : Finset (Fin 9), xs ⊆ base ∧ xs.card = 6 :=
    Finset.le_card_iff_exists_subset_card.mp base_card
  use xs, hxs.2
  intro x hx y hy hxy
  by_contra!
  replace this : ⟨x, y, hxy⟩ ∈ void f := by
    simpa [void]
  set c : Seg := ⟨x, y, hxy⟩
  simp [h.2.2.2] at this
  rw [def_base] at hxs
  have hxs1 := hxs.1 hx
  have hxs2 := hxs.1 hy
  simp at hxs1 hxs2
  simp [Seg.ext_iff] at this
  tauto

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

lemma option_reduce {y : Fin 2} {x : Option (Fin 2)} (hx1 : x ≠ none) (hx2 : x ≠ y) :
    x = some (1 - y) := by
  match hx : x with
  | none => exact False.elim (hx1 rfl)
  | some 0 =>
    rw [Fin.eq_one_of_neq_zero y fun a ↦ hx2 (congrArg some a.symm)]; rfl
  | some 1 => match y with | 0 => rfl | 1 => exact False.elim (hx2 rfl)

lemma ramsey {f : scheme} {xs : Finset (Fin 9)} (hxs1 : xs.card = 6)
  (hxs2 : ∀ x ∈ xs, ∀ y ∈ xs, (hxy : x < y) → f ⟨x, y, hxy⟩ ≠ none) :
    ∃ t : Tri, ¬ t.notMono f := by
  have xs_nonem : xs.Nonempty := by
    rw [← Finset.card_ne_zero, hxs1]
    decide
  set p := xs.max' xs_nonem with def_p
  set xs' := xs.erase p with def_xs'
  have xs'_card : xs'.card = 5 := by
    rw [def_xs', Finset.card_erase_of_mem, hxs1]
    exact Finset.max'_mem xs xs_nonem
  have i_lt_p {i : xs'} := xs.lt_max'_of_mem_erase_max' xs_nonem i.2
  have f_ip {i : xs'} := Option.ne_none_iff_exists'.1 <|
    hxs2 i ((Finset.erase_subset p xs) i.2) p
      (xs.max'_mem xs_nonem) i_lt_p
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
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := Finset.two_lt_card.1 hy
  simp only [Finset.mem_filter, Finset.mem_attach, true_and] at ha hb hc
  wlog hab : a < b
  · specialize @this f xs hxs1 hxs2 xs_nonem def_p def_xs' xs'_card _ _ card1 card2
      y hy b a c ⟨habc.1.symm, habc.2.2, habc.2.1⟩ hb ha hc
    refine this ?_
    simp at hab
    exact lt_of_le_of_ne hab habc.1.symm
  have h1 : f ⟨b, p, i_lt_p⟩ = f' b := Classical.choose_spec f_ip
  have h2 : f ⟨a, p, i_lt_p⟩ = f' a := Classical.choose_spec f_ip
  have h3 : f ⟨c, p, i_lt_p⟩ = f' c := Classical.choose_spec f_ip
  rw [ha] at h2
  rw [hb] at h1
  rw [hc] at h3
  have f_none {i j : {x // x ∈ xs'}} (hij : i < j) :=
    hxs2 i ((Finset.erase_subset p xs) i.2) j
      ((Finset.erase_subset p xs) j.2) hij
  obtain (hγ | hγ | hγ) := split_or habc hab
  · by_cases bottom :
      f ⟨a, b, hab⟩ = some y ∨
      f ⟨c, a, hγ⟩ = some y ∨
      f ⟨c, b, hγ.trans hab⟩ = some y
    · casesm* _ ∨ _
      · use ⟨a, b, p, ⟨hab, i_lt_p⟩⟩
        simp [Tri.notMono, h1, h2, h3, bottom]
      · use ⟨c, a, p, ⟨hγ, i_lt_p⟩⟩
        simp [Tri.notMono, h1, h2, h3, bottom]
      · use ⟨c, b, p, ⟨hγ.trans hab, i_lt_p⟩⟩
        simp [Tri.notMono, h1, h2, h3, bottom]
    · use ⟨c, a, b, ⟨hγ, hab⟩⟩
      push_neg at bottom
      replace h1 := option_reduce (f_none hab) bottom.1
      replace h2 := option_reduce (f_none hγ) bottom.2.1
      replace h3 := option_reduce (f_none (hγ.trans hab)) bottom.2.2
      simp [Tri.notMono, h1, h2, h3, bottom]
  · by_cases bottom :
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
  · by_cases bottom :
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

theorem IMO1992Q3 :
    Minimal {n : ℕ | ∀ f : scheme, (colored f).card = n → ¬ Scheme.noMono f} 33 := by
  apply minimal_iff_forall_lt.2
  constructor
  · change ∀ (f : scheme), (colored f).card = 33 → ¬Scheme.noMono f
    intro f hf
    replace hf : (void f).card = 3 := by
      have := hf ▸ void_add_colored f
      omega
    obtain ⟨xs, hxs1, hxs2⟩ := select hf
    dsimp [Scheme.noMono]
    push_neg
    exact ramsey hxs1 hxs2
  · intro y ylt hy
    change ∀ (f : scheme), (colored f).card = y → ¬Scheme.noMono f at hy
    replace ylt : y ≤ 32 := Nat.le_of_lt_succ ylt
    exact IMO1992Q3_n_32_case_1 ylt hy
