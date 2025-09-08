import Mathlib

open Finset Function Set

variable (n : ℕ)

/-- Define a square board as a product of two ranges -/
abbrev SquareBoard := range n × range n

/-- Instance showing SquareBoard is a finite type -/
instance : Fintype (SquareBoard n) := instFintypeProd (range n) (range n)

/-- Instance for decidable equality on SquareBoard -/
instance : DecidableEq (SquareBoard n) := instDecidableEqProd

/-- Define adjacency between two squares on the board -/
abbrev adjacent {n : ℕ} (a b : SquareBoard n) : Prop :=
  (a.1.val = b.1.val ∧ (a.2.val = b.2.val + 1 ∨ b.2.val = a.2.val + 1)) ∨
  (a.2.val = b.2.val ∧ (a.1.val = b.1.val + 1 ∨ b.1.val = a.1.val + 1))

/-- Predicate that all squares are adjacent to at least one marked square -/
def all_covered (marked : Finset (SquareBoard n)) : Prop :=
  ∀ s : SquareBoard n, ∃ m ∈ marked, adjacent s m

/-- Set of squares adjacent to a given square -/
noncomputable def adjacentSet (x : SquareBoard n) : Finset (SquareBoard n) := {p | adjacent p x}

/-- Manhattan distance between two squares -/
def dist_p (a b : SquareBoard n) : ℕ := Nat.dist a.1.val b.1.val + Nat.dist a.2.val b.2.val

/-- Lemma: adjacency is equivalent to Manhattan distance 1 -/
lemma adjacent_iff_dist_eq_one (a b : SquareBoard n) : adjacent a b ↔ dist_p n a b = 1 := by
  constructor
  · intro adj
    simp only [adjacent, and_or_left] at adj
    simp only [dist_p, Nat.dist]
    omega
  · intro hdis
    simp only [dist_p, Nat.dist] at hdis
    simp only [adjacent, and_or_left]
    omega

/-- Lemma: Manhattan distance is symmetric -/
lemma dist_p_comm (a b : SquareBoard n) : dist_p n a b = dist_p n b a := by
  simp [dist_p]
  rw [Nat.dist_comm]
  nth_rewrite 2 [Nat.dist_comm]
  rfl

/-- Lemma: distance from a point to itself is zero -/
@[simp]
lemma dist_p_self (a : SquareBoard n) : dist_p n a a = 0 := by
  simp only [dist_p, Nat.dist_self, add_zero]

/-- Lemma: zero distance implies equality -/
lemma dist_eq_zero_iff_eq (a b : SquareBoard n) : dist_p n a b = 0 ↔ a = b := by
  constructor
  · intro heq
    simp only [dist_p, AddLeftCancelMonoid.add_eq_zero] at heq
    obtain ⟨ha, hb⟩ := heq
    ext
    · exact Nat.eq_of_dist_eq_zero ha
    · exact Nat.eq_of_dist_eq_zero hb
  · intro heq
    rw [heq]
    simp only [dist_p, Nat.dist_self, add_zero]

/-- Lemma: triangle inequality for Manhattan distance -/
lemma dist_p_triangle_inequality (a b c : SquareBoard n) : dist_p n a b + dist_p n b c ≥ dist_p n a c := by
  unfold dist_p
  have le1 := Nat.dist.triangle_inequality ↑a.1 ↑b.1 ↑c.1
  have le2 := Nat.dist.triangle_inequality ↑a.2 ↑b.2 ↑c.2
  linarith

/-- Lemma: adjacency is symmetric -/
lemma adjacent_symm {a b : SquareBoard n} : adjacent a b ↔ adjacent b a := by
  have (a b : SquareBoard n) : adjacent a b → adjacent b a := by
    intro h
    simp [adjacent] at h ⊢
    rw [and_or_left, and_or_left] at h ⊢
    rcases h with (h | h) | (h | h)
    all_goals rcases h with ⟨h1, h2⟩
    · left; right
      rw [h1, h2]
      simp only [and_self]
    · left; left
      rw [h1, h2]
      simp only [and_self]
    · right; right
      rw [h1, h2]
      simp only [and_self]
    · right; left
      rw [h1, h2]
      simp only [and_self]
  constructor
  · exact this a b
  · exact this b a

/-- Define chessboard coloring (true for white, false for black) -/
def Color (p : SquareBoard n) : Bool := (p.1.val + p.2.val) % 2 = 0

/-- Lemma: adjacent squares have opposite colors -/
lemma adjacent_Color_diff {a b : SquareBoard n} (adj : adjacent a b) : Color n a = ¬(Color n b) := by
  simp only [Color, decide_eq_true_eq, Nat.mod_two_not_eq_zero, eq_iff_iff]
  simp only [adjacent, and_or_left] at adj
  omega

/-- Helper lemma for symmetric position in range -/
lemma symmInRange {x : ℕ} (hx : x ∈ range n) : n - 1 - x ∈ range n := by
  simp at hx ⊢
  omega

/-- Define membership in a diagonal -/
abbrev InDiagonal (x : ℕ) (p : SquareBoard n) : Prop := p.1.val + p.2.val = x

/-- Define symmetric square along the x-axis -/
abbrev Symm (p : SquareBoard n) : SquareBoard n :=
  ⟨⟨n - 1 - p.1.val, symmInRange n p.1.prop⟩, ⟨p.2.val, p.2.prop⟩⟩

/-- Define central symmetry (point reflection) -/
abbrev centralSymm (p : SquareBoard n) : SquareBoard n :=
  ⟨⟨n - 1 - p.1.val, symmInRange n p.1.prop⟩, ⟨n - 1 - p.2.val, symmInRange n p.2.prop⟩⟩

/-- Define a line (diagonal) with potential symmetry based on parity -/
def Line (i : ℕ) : Finset (SquareBoard n) := {p | if i % 2 = 0 then InDiagonal n (2 * i) p else InDiagonal n (2 * i) (centralSymm n p)}

/-- Define reflected line -/
def reLine (i : ℕ) : Finset (SquareBoard n) := {p | if i % 2 = 0 then InDiagonal n (2 * i) (Symm n p) else InDiagonal n (2 * i) (centralSymm n (Symm n p))}

/-- Lemma: relationship between diagonal and central symmetry -/
lemma InDiagonal_centralSymm {p : SquareBoard n} {x : ℕ} : InDiagonal n x (centralSymm n p) → InDiagonal n (2 * (n - 1) - x) p := by
  simp [InDiagonal]
  have le1 : p.1.val ≤ n - 1 := by
    have := p.1.prop
    rw [Finset.mem_range] at this
    omega
  have le2 : p.2.val ≤ n - 1 := by
    have := p.2.prop
    rw [Finset.mem_range] at this
    omega
  omega

/-- Lemma: equivalence for diagonal membership under central symmetry -/
lemma InDiagonal_centralSymm_iff {p : SquareBoard n} {x : ℕ} (hx : x ≤ 2 * (n - 1)) : InDiagonal n x (centralSymm n p) ↔ InDiagonal n (2 * (n - 1) - x) p := by
  simp [InDiagonal]
  constructor
  · have le1 : p.1.val ≤ n - 1 := by
      have := p.1.prop
      rw [Finset.mem_range] at this
      omega
    have le2 : p.2.val ≤ n - 1 := by
      have := p.2.prop
      rw [Finset.mem_range] at this
      omega
    omega
  · have le1 : p.1.val ≤ n - 1 := by
      have := p.1.prop
      rw [Finset.mem_range] at this
      omega
    have le2 : p.2.val ≤ n - 1 := by
      have := p.2.prop
      rw [Finset.mem_range] at this
      omega
    omega


/-- Lemma: All squares in Line n i are black (Color n x = true) -/
lemma allLineBlack {i : ℕ} {x : SquareBoard n} (hx : x ∈ Line n i) : Color n x = true := by
  simp [Color]
  -- Consider cases based on parity of i
  rcases em (i % 2 = 0) with h | h
  · simp [h, Line, InDiagonal] at hx
    omega
  · simp [h, Line, InDiagonal] at hx
    have p1 := x.1.prop
    rw [Finset.mem_range] at p1
    have p2 := x.2.prop
    rw [Finset.mem_range] at p2
    omega

/-- Lemma: All squares in reLine n i are white (Color n x = false) -/
lemma allreLineWhite {i : ℕ} {x : SquareBoard n} (hx : x ∈ reLine n i) [fact_even : Fact (Even n)] : Color n x = false := by
  simp [Color]
  have : n % 2 = 0 := Nat.even_iff.mp fact_even.out
  -- Consider cases based on parity of i
  rcases em (i % 2 = 0) with h | h
  · simp [h, reLine, InDiagonal] at hx
    have p1 := x.1.prop
    rw [Finset.mem_range] at p1
    omega
  · simp [h, reLine, InDiagonal] at hx
    have p1 := x.1.prop
    rw [Finset.mem_range] at p1
    have p2 := x.2.prop
    rw [Finset.mem_range] at p2
    omega

/-- Define points in Line n i that satisfy an additional parity condition as part of black key-points  -/
def PointInLine (i : ℕ) : Finset (SquareBoard n) := {p | p ∈ Line n i ∧ p.1.val % 2 = i % 2}

/-- Define points in reLine n i that satisfy an additional parity condition as part of white key-points -/
def PointInreLine (i : ℕ) : Finset (SquareBoard n) := {p | p ∈ reLine n i ∧ (Symm n p).1.val % 2 = i % 2}

/-- Define the set of key points as union over ranges -/
def KeyPoint : Finset (SquareBoard n) := Finset.biUnion (range (n / 2)) (PointInLine n) ∪ Finset.biUnion (range (n / 2)) (PointInreLine n)

set_option maxHeartbeats 0

/-- Equivalence between range (i+1) and PointInLine i -/
def cong_Line (i : ℕ) (ile : i * 2 < n) [n_ne : NeZero n] [fact_even : Fact (Even n)] : range (i + 1) ≃ PointInLine n i where
  toFun := by
    -- Maps x to (2(i-x), 2x) if i % 2 = 0 and Symm (2(i-x), 2x) if i % 2 = 1
    refine fun ⟨x, xmem⟩ ↦ ⟨if i % 2 = 0 then ⟨⟨2 * i - 2 * x, ?_⟩, ⟨2 * x, ?_⟩⟩ else ⟨⟨(n - 1) - (2 * i - 2 * x), ?_⟩, ⟨(n - 1) - 2 * x, ?_⟩⟩, ?_⟩
    all_goals simp only [Finset.mem_range] at xmem
    all_goals have lt1 : 2 * i - 2 * x < n := by omega
    all_goals have lt2 : 2 * x < n := by omega
    · simp only [Finset.mem_range, gt_iff_lt]
      omega
    · simp only [Finset.mem_range, gt_iff_lt]
      omega
    · simp only [Finset.mem_range, gt_iff_lt]
      omega
    · simp only [Finset.mem_range, gt_iff_lt]
      omega
    -- Prove that our equivalence defined maps x to PointInLine i
    · rcases em (i % 2 = 0) with h | h
      · simp only [PointInLine, Line, h, ↓reduceIte, mem_filter, Finset.mem_univ, true_and]
        constructor
        · simp [InDiagonal]
          omega
        · omega
      · simp only [PointInLine, Line, h, ↓reduceIte, mem_filter, Finset.mem_univ, true_and]
        constructor
        · simp [InDiagonal]
          omega
        · simp at h
          rw [h]
          obtain ⟨m, meq⟩ := Even.exists_two_nsmul n fact_even.out
          rw [smul_eq_mul] at meq
          rw [meq]
          have : m ≥ 1 := by
            by_contra hm
            simp only [ge_iff_le, not_le, Nat.lt_one_iff] at hm
            simp only [hm, smul_eq_mul, mul_zero] at meq
            exact n_ne.out meq
          have : (2 * m - 1 - (2 * i - 2 * x)) = (1 + 2 * (m - 1 -  i + x)) := by
            omega
          rw [this]
          simp only [Nat.add_mul_mod_self_left, Nat.mod_succ]
  invFun := by
    -- The inverse maps (x, y) to y / 2 if i % 2 = 0 else (n - 1 - y) / 2
    refine fun ⟨x, xmem⟩ ↦ ⟨if i % 2 = 0 then x.2.val / 2 else (centralSymm n x).2.val / 2, ?_⟩
    rw [Finset.mem_range]
    rcases em (i % 2 = 0) with h | h
    · simp only [h, ↓reduceIte]
      simp [PointInLine, Line, h, InDiagonal] at xmem
      omega
    · simp only [h, ↓reduceIte]
      simp [PointInLine, Line, h, InDiagonal] at xmem
      omega
  -- Prove our equivalence is bijection
  left_inv := by
    intro x
    rcases em (i % 2 = 0) with h | h
    · simp only [h, ↓reduceIte]
      apply Subtype.eq
      simp only
      omega
    · simp only [h, ↓reduceIte]
      apply Subtype.eq
      simp only
      have : 2 * x.val ≤ n - 1 := by
        have := x.prop
        rw [Finset.mem_range] at this
        omega
      omega
  -- Prove our equivalence is bijection
  right_inv := by
    intro x
    rcases em (i % 2 = 0) with h | h
    · simp only [h, ↓reduceIte]
      apply Subtype.eq
      simp only
      ext
      · simp only
        have := x.prop
        simp [PointInLine, h, Line, InDiagonal] at this
        omega
      · simp only
        have := x.prop
        simp [PointInLine, h, Line, InDiagonal] at this
        omega
    · simp only [h, ↓reduceIte]
      apply Subtype.eq
      simp only
      ext
      · simp only
        have := x.prop
        simp [PointInLine, h, Line, InDiagonal] at this
        simp only [Nat.mod_two_not_eq_zero] at h
        let p1 := x.val.1.prop
        rw [Finset.mem_range] at p1
        let p2 := x.val.2.prop
        rw [Finset.mem_range] at p2
        have : n % 2 = 0 := Nat.even_iff.mp fact_even.out
        omega
      · simp only
        have := x.prop
        simp [PointInLine, h, Line, InDiagonal] at this
        simp only [Nat.mod_two_not_eq_zero] at h
        let p1 := x.val.1.prop
        rw [Finset.mem_range] at p1
        let p2 := x.val.2.prop
        rw [Finset.mem_range] at p2
        have : n % 2 = 0 := Nat.even_iff.mp fact_even.out
        omega

/-- Lemma: Symm is an involution -/
lemma symm_symm (p : SquareBoard n) : Symm n (Symm n p) = p := by
  simp only [Symm, Subtype.coe_eta]
  ext
  · simp only
    let p1 := p.1.prop
    rw [Finset.mem_range] at p1
    omega
  · simp only

/-- Lemma: Characterization of membership in reLine -/
lemma in_reLine_iff_Symm_in_line {p : SquareBoard n} {i : ℕ} : p ∈ reLine n i ↔ Symm n p ∈ Line n i := by
  simp only [reLine, mem_filter, Finset.mem_univ, true_and, Line]

/-- Equivalence between PointInreLine and PointInLine via symmetry -/
def cong_Line_reLine (i : ℕ) : PointInreLine n i ≃ PointInLine n i where
  toFun := by
    -- Define the function maps p to Symm p
    refine fun ⟨x, xmem⟩ ↦ ⟨Symm n x, ?_⟩
    simp only [PointInreLine, mem_filter, Finset.mem_univ, true_and] at xmem
    simp only [PointInLine, mem_filter, Finset.mem_univ, true_and]
    rw [in_reLine_iff_Symm_in_line n] at xmem
    exact xmem
  invFun := by
    -- The inverse function is same the function
    refine fun ⟨x, xmem⟩ ↦ ⟨Symm n x, ?_⟩
    simp only [PointInLine, mem_filter, Finset.mem_univ, true_and] at xmem
    simp only [PointInreLine, mem_filter, Finset.mem_univ, true_and]
    nth_rewrite 1 [← symm_symm n x] at xmem
    rw [← in_reLine_iff_Symm_in_line n] at xmem
    constructor
    · exact xmem.left
    · let p1 := x.1.prop
      rw [Finset.mem_range] at p1
      omega
  left_inv := by
    -- By lemma we proved we have Symm (Symm p) = p
    intro x
    simp only
    apply Subtype.eq
    simp only
    rw [symm_symm n x]
  right_inv := by
    -- By lemma we proved we have Symm (Symm p) = p
    intro x
    simp only
    apply Subtype.eq
    simp only
    rw [symm_symm n x]

/-- Lemma: Cardinality of PointInLine is i+1 -/
lemma card_line (i : ℕ) (ile : i * 2 < n) [n_ne : NeZero n] [fact_even : Fact (Even n)] : #(PointInLine n i) = i + 1 := by
  -- Use the equivalence of cong_Line such that the cardinality of PointInLine equals to #range(i+1) = i + 1
  rw [← Finset.card_eq_of_equiv (cong_Line n i ile)]
  simp only [card_range]

/-- Lemma: Cardinality of PointInreLine is i+1 -/
lemma card_reline (i : ℕ) (ile : i * 2 < n) [n_ne : NeZero n] [fact_even : Fact (Even n)] : #(PointInreLine n i) = i + 1 := by
  -- Use the equivalence of cong_Line_reLine such that #(PointInreLine i) = #(PointInLine i) = i + 1
  rw [Finset.card_eq_of_equiv (cong_Line_reLine n i)]
  exact card_line n i ile

/-- Lemma : The distance between two point in PointInLine is at least 4 -/
lemma PointInLine_i_dist_ge {i : ℕ} {a b : SquareBoard n} (ha : a ∈ PointInLine n i) (hb : b ∈ PointInLine n i) (hne : a ≠ b) :
    dist_p n a b ≥ 4 := by
  simp [PointInLine] at ha hb
  obtain ⟨ain, ax⟩ := ha
  obtain ⟨bin, bx⟩ := hb
  -- Suppose a b are squares in PointInLine i, then a.x + a.y = b.x + b.y
  have val_add_eq : a.1.val + a.2.val = b.1.val + b.2.val := by
    rcases em (i % 2 = 0) with h | h
    · simp [Line, h] at ain bin
      rw [ain, bin]
    · simp [Line, h] at ain bin
      apply (InDiagonal_centralSymm n) at ain
      apply (InDiagonal_centralSymm n) at bin
      omega
  -- And by parity condition a.x % 2 = b.x % 2
  have eq1 : a.1.val % 2 = b.1.val % 2 := by
    rw [ax, bx]
  -- Also a.y % 2 = b.y % 2
  have eq2 : a.2.val % 2 = b.2.val % 2 := by
    rw [← ZMod.natCast_eq_natCast_iff'] at eq1 ⊢
    apply_fun (fun x ↦ (x : (ZMod 2))) at val_add_eq
    simp only [Nat.cast_add, eq1, add_right_inj] at val_add_eq
    exact val_add_eq
  unfold dist_p
  -- As for two numbers p q, p % 2 ≠ q % 2, they can't have distance 1.
  have dist_eq_one {p q : ℕ} : Nat.dist p q = 1 → p % 2 ≠ q % 2 := by
    intro dist_eq
    simp [Nat.dist] at dist_eq
    have : p = q + 1 ∨ q = p + 1 := by omega
    rcases this with h | h
    · rw [h]
      omega
    · rw [h]
      omega
  -- So |a.x - b.x| ≥ 2
  have : Nat.dist a.1.val b.1.val ≥ 2 := by
    by_contra lt
    have dcases : Nat.dist a.1.val b.1.val = 0 ∨ Nat.dist a.1.val b.1.val = 1 := by
      omega
    rcases dcases with h0 | h1
    · apply Nat.eq_of_dist_eq_zero at h0
      simp only [h0, add_right_inj] at val_add_eq
      have : a = b := by
        ext
        · exact h0
        · exact val_add_eq
      exact hne this
    · apply dist_eq_one at h1
      exact h1 eq1
  -- Also |a.y - b.y| ≥ 2
  have : Nat.dist a.2.val b.2.val ≥ 2 := by
    by_contra lt
    have dcases : Nat.dist a.2.val b.2.val = 0 ∨ Nat.dist a.2.val b.2.val = 1 := by
      omega
    rcases dcases with h0 | h1
    · apply Nat.eq_of_dist_eq_zero at h0
      simp only [h0, add_left_inj] at val_add_eq
      have : a = b := by
        ext
        · exact val_add_eq
        · exact h0
      exact hne this
    · apply dist_eq_one at h1
      exact h1 eq2
  -- Finally They have Manhattan distance at least 4
  linarith

/-- Lemma : The distance of two point a b equals to the distance between symmetric point of them. -/
lemma dist_p_symm {a b : SquareBoard n} : dist_p n a b = dist_p n (Symm n a) (Symm n b) := by
  simp only [dist_p, Nat.dist]
  let p1 := a.1.prop
  rw [Finset.mem_range] at p1
  let p2 := b.1.prop
  rw [Finset.mem_range] at p2
  omega

/-- Lemma : The distance between two point in PointInreLine is at least 4 -/
lemma PointInreLine_i_dist_ge {i : ℕ} {a b : SquareBoard n} (ha : a ∈ PointInreLine n i) (hb : b ∈ PointInreLine n i) (hne : a ≠ b) :
    dist_p n a b ≥ 4 := by
  rw [dist_p_symm n]
  -- We consider the symmetric squares of theses two squares
  have ha' : Symm n a ∈ PointInLine n i := by
    exact ((cong_Line_reLine n i) ⟨a, ha⟩).prop
  have hb' : Symm n b ∈ PointInLine n i := by
    exact ((cong_Line_reLine n i) ⟨b, hb⟩).prop
  -- By using the lemma dist_p_symm and PointInLine_i_dist_ge we similarly prove these lemma
  have hne' : Symm n a ≠ Symm n b := by
    intro eq
    replace eq : (⟨Symm n a, ha'⟩ : PointInLine n i) = ⟨Symm n b, hb'⟩ := by
      exact Subtype.mk_eq_mk.mpr eq
    apply_fun (cong_Line_reLine n i).symm at eq
    unfold cong_Line_reLine at eq
    rw [Equiv.coe_fn_symm_mk, Subtype.mk.injEq] at eq
    rw [symm_symm, symm_symm] at eq
    exact hne eq
  exact PointInLine_i_dist_ge n ha' hb' hne'

/-- Lemma : The distance between point of PointInLine i and point of PointInLine j is at least 4 -/
lemma inLine_dist_ge {i j : ℕ} {a b : SquareBoard n} (hne : i ≠ j) (ilt : i < n / 2) (jlt : j < n / 2) (ha : a ∈ PointInLine n i) (hb : b ∈ PointInLine n j) [fact_even : Fact (Even n)] :
    dist_p n a b ≥ 4 := by
  simp only [dist_p, ge_iff_le]
  -- For a point p in PointInLine we have p.x + p.y = const
  -- And for two points a b we have |a.x - b.x + a.y - b.y| ≤ |a.x - b.x| + |a.y - b.y|, it's sufficient to show 4 ≤ |const i - const j|
  have : Nat.dist (a.1.val + a.2.val) (b.1.val + b.2.val) ≤ Nat.dist a.1.val b.1.val + Nat.dist a.2.val b.2.val  := by
    rw [Nat.dist, Nat.dist, Nat.dist]
    omega
  refine le_trans ?_ this
  have n_mod_two : n % 2 = 0 := Nat.even_iff.mp fact_even.out
  -- By different cases we compute 4 ≤ |const i - const j|
  rcases em (i % 2 = 0) with hi | hi
  · rcases em (j % 2 = 0) with hj | hj
    · simp only [PointInLine, Line, hi, ↓reduceIte, mem_filter, Finset.mem_univ, true_and] at ha
      simp only [PointInLine, Line, hj, ↓reduceIte, mem_filter, Finset.mem_univ, true_and] at hb
      replace ha := ha.left
      replace hb := hb.left
      simp only [InDiagonal] at ha hb
      rw [ha, hb]
      unfold Nat.dist
      omega
    · simp only [PointInLine, Line, hi, ↓reduceIte, mem_filter, Finset.mem_univ, true_and] at ha
      simp only [PointInLine, Line, hj, ↓reduceIte, mem_filter, Finset.mem_univ, true_and] at hb
      simp only [Nat.mod_two_not_eq_zero] at hj
      replace ha := ha.left
      replace hb := InDiagonal_centralSymm n hb.left
      simp only [InDiagonal] at ha hb
      rw [ha, hb]
      unfold Nat.dist
      omega
  · rcases em (j % 2 = 0) with hj | hj
    · simp only [PointInLine, Line, hi, ↓reduceIte, mem_filter, Finset.mem_univ, true_and] at ha
      simp only [PointInLine, Line, hj, ↓reduceIte, mem_filter, Finset.mem_univ, true_and] at hb
      replace ha := InDiagonal_centralSymm n ha.left
      replace hb := hb.left
      simp only [InDiagonal] at ha hb
      rw [ha, hb]
      unfold Nat.dist
      omega
    · simp only [PointInLine, Line, hi, ↓reduceIte, mem_filter, Finset.mem_univ, true_and] at ha
      simp only [PointInLine, Line, hj, ↓reduceIte, mem_filter, Finset.mem_univ, true_and] at hb
      replace ha := InDiagonal_centralSymm n ha.left
      replace hb := InDiagonal_centralSymm n hb.left
      simp only [InDiagonal] at ha hb
      rw [ha, hb]
      unfold Nat.dist
      omega

/-- Lemma : The distance between point of PointInreLine i and point of PointInreLine j is at least 4 -/
lemma inreLine_dist_ge {i j : ℕ} {a b : SquareBoard n} (hne : i ≠ j) (ilt : i < n / 2) (jlt : j < n / 2) (ha : a ∈ PointInreLine n i) (hb : b ∈ PointInreLine n j) [fact_even : Fact (Even n)] :
    dist_p n a b ≥ 4 := by
  -- Similarly we choose the symmetric point of them and use lemma inLine_dist_ge
  rw [dist_p_symm n]
  have ha' : Symm n a ∈ PointInLine n i := by
    exact ((cong_Line_reLine n i) ⟨a, ha⟩).prop
  have hb' : Symm n b ∈ PointInLine n j := by
    exact ((cong_Line_reLine n j) ⟨b, hb⟩).prop
  exact inLine_dist_ge n hne ilt jlt ha' hb'

/-- Lemma : Prove PointInLine i are pairwise disjoint -/
lemma PointInLine_i_disj [fact_even : Fact (Even n)] : PairwiseDisjoint (Finset.range (n / 2)) (PointInLine n) := by
  intro i ilt j jlt ijne
  simp only [coe_range, Set.mem_Iio] at ilt jlt
  refine disjoint_iff_ne.mpr ?_
  intro a amem b bmem
  intro heq
  replace heq : dist_p n a b = 0 := by
    rw [heq]
    simp only [dist_p_self]
  -- Because there distance is at least 4
  have contra := inLine_dist_ge n ijne ilt jlt amem bmem
  linarith

/-- Lemma : Prove PointInreLine i are pairwise disjoint -/
lemma PointInreLine_i_disj [fact_even : Fact (Even n)] : PairwiseDisjoint (Finset.range (n / 2)) (PointInreLine n) := by
  intro i ilt j jlt ijne
  simp only [coe_range, Set.mem_Iio] at ilt jlt
  refine disjoint_iff_ne.mpr ?_
  intro a amem b bmem
  intro heq
  replace heq : dist_p n a b = 0 := by
    rw [heq]
    simp only [dist_p_self]
  -- Because there distance is at least 4
  have contra := inreLine_dist_ge n ijne ilt jlt amem bmem
  linarith

/-- Lemma : Prove PointInLine i and PointInreLine j are disjoint -/
lemma Line_union_disj_reLine_union [fact_even : Fact (Even n)] : Disjoint (Finset.biUnion (range (n / 2)) (PointInLine n)) (Finset.biUnion (range (n / 2)) (PointInreLine n)) := by
  refine disjoint_iff_ne.mpr ?_
  intro a amem b bmem abeq
  simp only [Finset.mem_biUnion, Finset.mem_range] at amem bmem
  simp only [PointInLine, PointInreLine, mem_filter, Finset.mem_univ, true_and] at amem bmem
  obtain ⟨i, ilt, ⟨amem, aprop⟩⟩ := amem
  obtain ⟨j, jlt, ⟨bmem, bprop⟩⟩ := bmem
  -- The point in PointInLine i is black
  have c1 := allLineBlack n amem
  -- The point in PointInreLine j is white
  have c2 := allreLineWhite n bmem
  rw [abeq] at c1
  -- Because they have different color, they can't be same
  exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false c1 c2

/-- Lemma : Prove the adjacentSet of KeyPoint are disjoint -/
lemma KeyPoint_area_disjoint [fact_even : Fact (Even n)] : PairwiseDisjoint (KeyPoint n) (adjacentSet n) := by
  -- Suppose a, b are key-points and x, y belongs to the adjacentSet of a, b respectively
  intro a amem b bmem abne
  -- If they have intersection suppose x = y.
  refine disjoint_iff_ne.mpr ?_
  intro x xmem y ymem
  simp [KeyPoint] at amem bmem
  simp [adjacentSet] at xmem ymem
  intro xyeq
  rw [← xyeq] at ymem
  -- It shows |a - b| ≤ 2 because |a - b| ≤ |a - x| + |y - b| = |a - x| + |x - b| = 1 + 1 = 2
  have dist_le : dist_p n a b ≤ 2 := by
    rw [adjacent_iff_dist_eq_one] at xmem ymem
    calc
      dist_p n a b ≤ dist_p n a x + dist_p n x b := dist_p_triangle_inequality n a x b
      _ = 2 := by rw [dist_p_comm, xmem, ymem]
  -- To make contradiction, consider a, b in PointInLine or PointInreLine respectively
  rcases amem with aline | are
  · obtain ⟨i, ilt, amemi⟩ := aline
    rcases bmem with bline | bre
    · obtain ⟨j, jlt, bmemj⟩ := bline
      -- If they both in PointInLine, their distance is at least 4, contradiction
      rcases em (i = j) with h | h
      · rw [h] at amemi
        have contra := PointInLine_i_dist_ge n amemi bmemj abne
        linarith
      · have contra := inLine_dist_ge n h ilt jlt amemi bmemj
        linarith
    · obtain ⟨j, jlt, bmemj⟩ := bre
      -- If one of them belongs to PointInLine and the other belongs to PointInreLine, then x, y must have different color
      simp only [PointInLine, mem_filter, Finset.mem_univ, true_and] at amemi
      have colora := allLineBlack n amemi.left
      simp only [PointInreLine, mem_filter, Finset.mem_univ, true_and] at bmemj
      have colorb := allreLineWhite n bmemj.left
      rw [adjacent_symm] at xmem
      rw [adjacent_Color_diff n xmem] at colora
      rw [adjacent_Color_diff n ymem] at colora
      simp only [Bool.not_eq_true, Bool.not_eq_false] at colora
      -- So they can't be same
      exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false colora colorb
  · obtain ⟨i, ilt, amemi⟩ := are
    rcases bmem with bline | bre
    · obtain ⟨j, jlt, bmemj⟩ := bline
      -- If one of them belongs to PointInLine and the other belongs to PointInreLine, then x, y must have different color
      simp only [PointInreLine, mem_filter, Finset.mem_univ, true_and] at amemi
      have colora := allreLineWhite n amemi.left
      simp only [PointInLine, mem_filter, Finset.mem_univ, true_and] at bmemj
      have colorb := allLineBlack n bmemj.left
      rw [adjacent_symm] at ymem
      rw [adjacent_Color_diff n ymem] at colorb
      rw [adjacent_Color_diff n xmem] at colorb
      simp only [Bool.not_eq_true, Bool.not_eq_false] at colorb
      -- So they can't be same
      exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false colorb colora
    · obtain ⟨j, jlt, bmemj⟩ := bre
      -- If they both in PointInreLine, their distance is at least 4, contradiction
      rcases em (i = j) with h | h
      · rw [h] at amemi
        have contra := PointInreLine_i_dist_ge n amemi bmemj abne
        linarith
      · have contra := inreLine_dist_ge n h ilt jlt amemi bmemj
        linarith

/-- Lemma : If x belongs to adjacentSet of p, then Symm x belongs to adjacentSet of Symm p -/
lemma symm_adjacentSet {x p : SquareBoard n} : x ∈ (adjacentSet n p) → (Symm n x) ∈ (adjacentSet n (Symm n p)) := by
  intro xmem
  simp only [adjacentSet, mem_filter, Finset.mem_univ, true_and] at xmem ⊢
  rw [adjacent_iff_dist_eq_one] at xmem ⊢
  rw [dist_p_symm n] at xmem
  exact xmem

/-- Define the equivalence between adjacentSet of p and adjacentSet of Symm p -/
def cong_adjacentSet (p : SquareBoard n) : (adjacentSet n p) ≃ (adjacentSet n (Symm n p)) where
  -- Simply use the the function of symmetric operator
  toFun := fun ⟨x, xmem⟩ ↦ ⟨Symm n x, symm_adjacentSet n xmem⟩
  -- Simply use the the function of symmetric operator
  invFun := fun ⟨x, xmem⟩ ↦ ⟨Symm n x, (symm_symm n p) ▸ (symm_adjacentSet n xmem)⟩
  -- By lemma symm_symm, x, p are adjacent iff Symm x, Symm p are adjacent which completes the proof
  left_inv := by
    intro x
    rw [← Subtype.coe_inj]
    simp only
    rw [symm_symm n]
  -- Same as proof above
  right_inv := by
    intro x
    rw [← Subtype.coe_inj]
    simp only
    rw [symm_symm n]

/-- Lemma : Formula to compute cardinality of adjacentSet p, which is usually 4, when p.x or p.y is on border, then subtracted by 1 -/
lemma card_adjacentSet {p : SquareBoard n} [n_ne : NeZero n] [fact_even : Fact (Even n)] : #(adjacentSet n p) =
    4 - (if p.1.val = 0 ∨ p.1.val = n - 1 then 1 else 0) - (if p.2.val = 0 ∨ p.2.val = n - 1 then 1 else 0) := by
  -- Divide adjacentSet p intro 4 sets, S_up, S_down, S_left, S_right, when p is on border let it as empty set.
  let S_up : Finset (SquareBoard n) := dite (p.2.val = n - 1) (fun _ ↦ ∅) (fun h ↦ {⟨p.1, ⟨p.2.val + 1, ?_⟩⟩})
  let pro := p.2.prop
  rw [Finset.mem_range] at pro ⊢
  omega
  let S_down : Finset (SquareBoard n) := dite (p.2.val = 0) (fun _ ↦ ∅) (fun h ↦ {⟨p.1, ⟨p.2.val - 1, ?_⟩⟩})
  let pro := p.2.prop
  rw [Finset.mem_range] at pro ⊢
  omega
  let S_left : Finset (SquareBoard n) := dite (p.1.val = 0) (fun _ ↦ ∅) (fun h ↦ {⟨⟨p.1.val - 1, ?_⟩, p.2⟩})
  let pro := p.1.prop
  rw [Finset.mem_range] at pro ⊢
  omega
  let S_right : Finset (SquareBoard n) := dite (p.1.val = n - 1) (fun _ ↦ ∅) (fun h ↦ {⟨⟨p.1.val + 1, ?_⟩, p.2⟩})
  let pro := p.1.prop
  rw [Finset.mem_range] at pro ⊢
  omega
  -- Prove that a point x belongs to four Sets iff x is adjacent to p
  have mem_up {x : SquareBoard n} : x ∈ S_up ↔ x.1.val = p.1.val ∧ x.2.val = p.2.val + 1 := by
    rcases em (p.2.val = n - 1) with h | h
    · simp only [h, ↓reduceDIte, Finset.not_mem_empty, false_iff, not_and, S_up]
      have pro := x.2.prop
      rw [Finset.mem_range] at pro
      omega
    · simp only [h, ↓reduceDIte, Finset.mem_singleton, S_up]
      rw [Prod.ext_iff]
      rw [← Subtype.coe_inj, ← Subtype.coe_inj]
  have mem_down {x : SquareBoard n} : x ∈ S_down ↔ x.1.val = p.1.val ∧ p.2.val = x.2.val + 1 := by
    rcases em (p.2.val = 0) with h | h
    · simp only [dite_eq_ite, h, ↓reduceIte, Finset.not_mem_empty, self_eq_add_left,
      AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, S_down]
    · simp only [dite_eq_ite, h, ↓reduceIte, Finset.mem_singleton, S_down]
      rw [Prod.ext_iff]
      rw [← Subtype.coe_inj, ← Subtype.coe_inj]
      simp only
      omega
  have mem_right {x : SquareBoard n} : x ∈ S_right ↔ x.2.val = p.2.val ∧ x.1.val = p.1.val + 1 := by
    rcases em (p.1.val = n - 1) with h | h
    · simp only [h, ↓reduceDIte, Finset.not_mem_empty, false_iff, not_and, S_right]
      have pro := x.1.prop
      rw [Finset.mem_range] at pro
      omega
    · simp only [h, ↓reduceDIte, Finset.mem_singleton, S_right]
      rw [Prod.ext_iff]
      rw [← Subtype.coe_inj, ← Subtype.coe_inj]
      simp
      rw [And.comm]
  have mem_left {x : SquareBoard n} : x ∈ S_left ↔ x.2.val = p.2.val ∧ p.1.val = x.1.val + 1 := by
    rcases em (p.1.val = 0) with h | h
    · simp only [dite_eq_ite, h, ↓reduceIte, Finset.not_mem_empty, self_eq_add_left,
      AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, S_left, S_up, S_right, S_down]
    · simp only [dite_eq_ite, h, ↓reduceIte, Finset.mem_singleton, S_left, S_up, S_right, S_down]
      rw [Prod.ext_iff]
      rw [← Subtype.coe_inj, ← Subtype.coe_inj]
      simp only
      omega
  -- Part adjacentSet of p into 4 parts
  have : (adjacentSet n p) = (S_up ∪ S_down) ∪ (S_left ∪ S_right) := by
    ext x
    simp only [adjacentSet, adjacent, and_or_left, mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.union_assoc, Finset.mem_union]
    rw [mem_up, mem_down, mem_left, mem_right]
    tauto
  rw [this]
  -- Prove the disjoint property between 4 sets
  have disj1 : Disjoint (S_up ∪ S_down) (S_left ∪ S_right) := by
    refine disjoint_iff_ne.mpr ?_
    intro a amem b bmem abeq
    simp only [Finset.mem_union] at amem bmem
    have avne : a.2.val ≠ p.2.val := by
      rcases amem with ha | ha
      · rw [mem_up] at ha
        rw [ha.right]
        simp only [ne_eq, add_right_eq_self, one_ne_zero, not_false_eq_true]
      · rw [mem_down] at ha
        rw [ha.right]
        simp only [ne_eq, self_eq_add_right, one_ne_zero, not_false_eq_true]
    have bveq : b.2.val = p.2.val := by
      rcases bmem with hb | hb
      · rw [mem_left] at hb
        rw [hb.left]
      · rw [mem_right] at hb
        rw [hb.left]
    apply_fun (fun x ↦ x.2.val) at abeq
    rw [abeq, bveq] at avne
    simp only [ne_eq, not_true_eq_false] at avne
  have disj2 : Disjoint S_up S_down := by
    refine disjoint_iff_ne.mpr ?_
    intro a amem b bmem abeq
    rw [mem_up] at amem
    rw [mem_down] at bmem
    apply_fun (fun x ↦ x.2.val) at abeq
    rw [amem.right, bmem.right] at abeq
    omega
  have disj3 : Disjoint S_left S_right := by
    refine disjoint_iff_ne.mpr ?_
    intro a amem b bmem abeq
    rw [mem_left] at amem
    rw [mem_right] at bmem
    apply_fun (fun x ↦ x.1.val) at abeq
    omega
  -- Then the cardinality of adjacentSet can be written as sum of cardinality of 4 sets
  rw [card_union_of_disjoint disj1]
  rw [card_union_of_disjoint disj2]
  rw [card_union_of_disjoint disj3]
  -- Compute the cardinality of 4 sets respectively
  have card_up : #S_up = if p.2.val = n - 1 then 0 else 1 := by
    rcases em (p.2.val = n - 1) with h | h
    · simp only [h, ↓reduceDIte, Finset.card_empty, ↓reduceIte, S_up]
    · simp only [h, ↓reduceDIte, Finset.card_singleton, ↓reduceIte, S_up]
  have card_down : #S_down = if p.2.val = 0 then 0 else 1 := by
    rcases em (p.2.val = 0) with h | h
    · simp only [dite_eq_ite, h, ↓reduceIte, Finset.card_empty, S_down, S_up]
    · simp only [dite_eq_ite, h, ↓reduceIte, Finset.card_singleton, S_down, S_up]
  have card_left : #S_left = if p.1.val = 0 then 0 else 1 := by
    rcases em (p.1.val = 0) with h | h
    · simp only [dite_eq_ite, h, ↓reduceIte, Finset.card_empty, S_left, S_up, S_down]
    · simp only [dite_eq_ite, h, ↓reduceIte, Finset.card_singleton, S_left, S_up, S_down]
  have card_right : #S_right = if p.1.val = n - 1 then 0 else 1 := by
    rcases em (p.1.val = n - 1) with h | h
    · simp only [h, ↓reduceDIte, Finset.card_empty, ↓reduceIte, S_right]
    · simp only [h, ↓reduceDIte, Finset.card_singleton, ↓reduceIte, S_right]
  rw [card_up, card_down, card_left, card_right]
  have ne_n_sub : 0 ≠ n - 1 := by
    have : n ≠ 0 := Ne.symm (NeZero.ne' n)
    have : n % 2 = 0 := Nat.even_iff.mp fact_even.out
    omega
  have n_sub_ne : n - 1 ≠ 0 := by
    exact id (Ne.symm ne_n_sub)
  -- An integer in range n has 3 cases : x = 0 or x = n - 1 or otherwise
  have case_three {x : ℕ} (hx : x ∈ range n) : x = 0 ∨ x = (n - 1) ∨ (x ≠ 0 ∧ x ≠ n - 1) := by
    simp only [Finset.mem_range] at hx
    omega
  -- By considering different cases of p.x and p.y we prove the formula holds
  rcases (case_three p.1.prop) with hx0 | hxn | ⟨hx0, hxn⟩
  · rcases (case_three p.2.prop) with hy0 | hyn | ⟨hy0, hyn⟩
    · simp only [hy0, ne_n_sub, n_sub_ne, ↓reduceIte, add_zero, hx0, zero_add, Nat.reduceAdd, or_false,
      Nat.add_one_sub_one]
    · simp only [hyn, ↓reduceIte, n_sub_ne, zero_add, hx0, ne_n_sub, Nat.reduceAdd, or_false,
      Nat.add_one_sub_one, or_true]
    · simp only [hyn, ↓reduceIte, hy0, Nat.reduceAdd, hx0, ne_n_sub, zero_add, or_false,
      Nat.add_one_sub_one, or_self, tsub_zero]
  · rcases (case_three p.2.prop) with hy0 | hyn | ⟨hy0, hyn⟩
    · simp only [hy0, ne_n_sub, ↓reduceIte, add_zero, hxn, n_sub_ne, Nat.reduceAdd, or_true,
      Nat.add_one_sub_one, or_false]
    · simp only [hyn, ↓reduceIte, n_sub_ne, zero_add, hxn, add_zero, Nat.reduceAdd, or_true,
      Nat.add_one_sub_one]
    · simp only [hyn, ↓reduceIte, hy0, Nat.reduceAdd, hxn, n_sub_ne, add_zero, or_true,
      Nat.add_one_sub_one, or_self, tsub_zero]
  · rcases (case_three p.2.prop) with hy0 | hyn | ⟨hy0, hyn⟩
    · simp only [hy0, ne_n_sub, ↓reduceIte, add_zero, hx0, hxn, Nat.reduceAdd, or_self, tsub_zero,
      or_false, Nat.add_one_sub_one]
    · simp only [hyn, ↓reduceIte, n_sub_ne, zero_add, hx0, hxn, Nat.reduceAdd, or_self, tsub_zero,
      or_true, Nat.add_one_sub_one]
    · simp only [hyn, ↓reduceIte, hy0, Nat.reduceAdd, hx0, hxn, or_self, tsub_zero]


/-- Lemma : The cardinality of adjacentSet of p equals the cardinality of adjacentSet of Symm p-/
lemma adjacent_card_symm {p : SquareBoard n} : #(adjacentSet n p) = #(adjacentSet n (Symm n p)) := by
  -- Because they have an equivalence
  exact Finset.card_eq_of_equiv (cong_adjacentSet n p)

/-- Lemma : The union of all adjacentSet of PointInLine has cardinality n * n / 2 -/
lemma sum_of_card_adjacent_on_Line [n_ne : NeZero n] [fact_even : Fact (Even n)] : ∑ i ∈ Finset.range (n / 2), ∑ x ∈ PointInLine n i, #(adjacentSet n x) = n * n / 2 := by
  -- We show the sum equals ∑ i ∈ Finset.range (n / 2), (2 + i * 4) then by computing we complete the proof
  have : ∑ i ∈ Finset.range (n / 2), ∑ x ∈ PointInLine n i, #(adjacentSet n x) = ∑ i ∈ Finset.range (n / 2), (2 + i * 4) := by
    -- It's sufficient to show ∑ x ∈ PointInLine n i, #(adjacentSet n x) = (2 + i * 4)
    rw [sum_congr (by rfl)]
    intro i imem
    simp only [Finset.mem_range] at imem
    have ilt : i * 2 < n := by omega
    rw [← Finset.sum_attach, ← univ_eq_attach]
    rw [← Fintype.sum_equiv (cong_Line n i ilt) (fun k ↦ #(adjacentSet n (cong_Line n i ilt k))) (fun x ↦ #(adjacentSet n x)) (by simp only [implies_true])]
    rw [univ_eq_attach]
    have : n % 2 = 0 := Nat.even_iff.mp fact_even.out
    -- Consider i = 0 or not
    rcases em (i = 0) with hi | hi
    · simp [cong_Line, hi]
      -- If i = 0, then PointInLine i has only one square in left-down side, the cardinality of adjacentSet equals 2
      have : (Finset.range (i + 1)).attach = {⟨0, by simp⟩} := by
        ext x
        simp only [mem_attach, Finset.mem_singleton, true_iff]
        let px := x.prop
        simp only [hi, zero_add, Finset.range_one, Finset.mem_singleton] at px
        apply Subtype.eq
        simp only [px]
      rw [this]
      simp only [sum_singleton, mul_zero]
      rw [card_adjacentSet n]
      simp only [true_or, ↓reduceIte, Nat.add_one_sub_one]
    · -- If i > 0, then divide PointInLine into 3 parts
      -- We have constructed an equivalence between PointInLine i and range (i + 1), use this equivalence, we divide PointInLine i into :
      -- S : Whole set
      let S : Finset { x // x ∈ Finset.range (i + 1) } := (Finset.range (i + 1)).attach
      -- S1 : Singleton set {0}
      let S1 : Finset { x // x ∈ Finset.range (i + 1) } := {⟨0, by simp⟩}
      -- S3 : Singleton set {i}
      let S3 : Finset { x // x ∈ Finset.range (i + 1) } := {⟨i, by simp⟩}
      -- S2 : Range of (0, i)
      let S2 := (S \ (S1 ∪ S3))
      -- We prove S = S1 ∪ S2 ∪ S3 such that #S = #S1 + #S2 + #S3
      have sub : (S1 ∪ S3) ⊆ S := by
        intro x xmem
        simp only [mem_attach, S]
      have eqU1 : S = (S1 ∪ S3) ∪ S2 := by
        exact Eq.symm (union_sdiff_of_subset sub)
      have disj1 : Disjoint (S1 ∪ S3) S2 := by
        unfold S2
        exact Disjoint.symm sdiff_disjoint
      have disj2 : Disjoint S1 S3 := by
        simp only [Finset.disjoint_singleton_right, Finset.mem_singleton, Subtype.mk.injEq, S1, S3]
        exact hi
      have card_S : #S = i + 1 := by
        simp only [card_attach, card_range, S]
      -- It obvious that singleton set S1 and S3 has cardinality 1
      have card_S1 : #S1 = 1 := by
        simp only [Finset.card_singleton, S1, S]
      have card_S3 : #S3 = 1 := by
        simp only [Finset.card_singleton, S3, S]
      -- Because S has cardinality i + 1, so S2 = S \ S1 \ S3 has cardinality (i + 1) - 1 - 1 = (i - 1)
      have card_S2 : #S2 = (i - 1) := by
        have card_eq_add : #S = #S1 + #S3 + #S2 := by
          rw [eqU1, card_union_of_disjoint disj1]
          rw [card_union_of_disjoint disj2]
        rw [card_S, card_S1, card_S3] at card_eq_add
        omega
      rw [show (Finset.range (i + 1)).attach = S by rfl]
      rw [eqU1, Finset.sum_union disj1, Finset.sum_union disj2]
      -- The cardinality of adjacentSet of p in S1 equals 3 because p is on border
      have : ∑ x ∈ S1, #(adjacentSet n ↑((cong_Line n i ilt) x)) = 3 := by
        simp only [sum_singleton, S1]
        simp [cong_Line]
        rw [card_adjacentSet n]
        rcases em (i % 2 = 0) with hi2 | hi2
        · simp only [hi2, ↓reduceIte, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, true_or,
          Nat.pred_eq_succ_iff, Nat.reduceAdd, S1]
          rw [if_neg]
          omega
        · simp only [hi2, ↓reduceIte, or_true, Nat.pred_eq_succ_iff, Nat.reduceAdd, S1]
          rw [if_neg]
          omega
      rw [this]
      -- The cardinality of adjacentSet of p in S3 equals 3 because p is on border
      have : ∑ x ∈ S3, #(adjacentSet n ↑((cong_Line n i ilt) x)) = 3 := by
        simp only [sum_singleton, S3]
        simp [cong_Line]
        rw [card_adjacentSet n]
        rcases em (i % 2 = 0) with hi2 | hi2
        · simp only [hi2, ↓reduceIte, true_or, Nat.add_one_sub_one, mul_eq_zero,
          OfNat.ofNat_ne_zero, false_or, S1, S3]
          rw [if_neg]
          omega
        · simp only [hi2, ↓reduceIte, or_true, Nat.add_one_sub_one, S1, S3]
          rw [if_neg]
          omega
      rw [this]
      -- For all points p in S2, the cardinality of adjacentSet of p equals 4, so the sum of cardinality equals 4 * #S2 = 4 * (i - 1)
      have : ∑ x ∈ S2, #(adjacentSet n ↑((cong_Line n i ilt) x)) = 4 * (i - 1) := by
        have : ∑ x ∈ S2, #(adjacentSet n ↑((cong_Line n i ilt) x)) = ∑ x ∈ S2, 4 := by
          rw [sum_congr (by rfl)]
          intro x xmem
          simp [S2, S, S1, S3] at xmem
          obtain ⟨xne1, xne2⟩ := xmem
          apply Subtype.coe_ne_coe.mpr at xne1
          apply Subtype.coe_ne_coe.mpr at xne2
          simp only at xne1 xne2
          rw [card_adjacentSet n]
          rcases em (i % 2 = 0) with hi2 | hi2
          · simp only [cong_Line, hi2, ↓reduceIte, Equiv.coe_fn_mk, mul_eq_zero,
            OfNat.ofNat_ne_zero, false_or, S, S2, S1, S3]
            rw [if_neg, if_neg]
            omega
            have p1 := x.prop
            rw [Finset.mem_range] at p1
            omega
          · simp only [cong_Line, hi2, ↓reduceIte, Equiv.coe_fn_mk, S, S2, S1, S3]
            rw [if_neg, if_neg]
            have p1 := x.prop
            rw [Finset.mem_range] at p1
            omega
            have p1 := x.prop
            rw [Finset.mem_range] at p1
            omega
        rw [this, sum_const, card_S2]
        rw [smul_eq_mul, mul_comm]
      rw [this]
      omega
  -- At last we compute 3 + 3 + 4 * (i - 1) = 2 + i * 4
  rw [this, sum_add_distrib, ← Finset.sum_mul, Finset.sum_const]
  rw [show (∑ i ∈ Finset.range (n / 2), i) * 4 = ((∑ i ∈ Finset.range (n / 2), i) * 2) * 2 by rw [mul_assoc]; norm_num]
  rw [Finset.sum_range_id_mul_two]
  simp only [card_range, smul_eq_mul]
  have : n % 2 = 0 := Nat.even_iff.mp fact_even.out
  have : n ≠ 0 := Ne.symm (NeZero.ne' n)
  obtain ⟨m, meq⟩ := fact_even.out
  have : n * n / 2 = n * (n / 2) := by
    replace meq : n = m * 2 := by omega
    rw [meq, mul_div_cancel_right₀ m (by norm_num)]
    rw [show m * 2 * (m * 2) = m * m * 2 * 2 by ring]
    rw [mul_div_cancel_right₀ (m * m * 2) (by norm_num)]
    ring
  rw [this]
  have : m ≥ 1 := by
    omega
  have meq' : n / 2 = m := by
    rw [meq, ← mul_two, mul_div_cancel_right₀ m (by norm_num)]
  rw [meq', meq]
  rw [Nat.mul_sub, Nat.sub_mul, Nat.add_mul, mul_one, ← mul_two]
  have : m * m * 2 ≥ m * 2 := by
    nlinarith
  omega

/-- Lemma : The union of all adjacentSet of PointInreLine has cardinality n * n / 2 -/
lemma sum_of_card_adjacent_on_reLine [n_ne : NeZero n] [fact_even : Fact (Even n)] : ∑ i ∈ Finset.range (n / 2), ∑ x ∈ PointInreLine n i, #(adjacentSet n x) = n * n / 2 := by
  -- By the symmetry we can use the lemma of sum_of_card_adjacent_on_Line to complete the proof
  rw [← sum_of_card_adjacent_on_Line]
  rw [sum_congr (by rfl)]
  intro i imem
  rw [← Finset.sum_attach, ← univ_eq_attach]
  nth_rewrite 2 [← Finset.sum_attach]
  rw [← univ_eq_attach]
  refine Fintype.sum_equiv (cong_Line_reLine n i) (fun x ↦ #(adjacentSet n x.val)) (fun x ↦ #(adjacentSet n x.val)) ?_
  intro x
  simp [cong_Line_reLine]
  exact adjacent_card_symm n

/-- Lemma : The union of all adjacentSet equals whole square board -/
lemma Union_eq_top [n_ne : NeZero n] [fact_even : Fact (Even n)] : Finset.biUnion (KeyPoint n) (adjacentSet n) = (univ : Finset (SquareBoard n)) := by
  -- It's sufficient to prove the cardinality of union equals the cardinality of square board, which is n * n
  rw [← Finset.card_eq_iff_eq_univ]
  simp only [Fintype.card_prod, Finset.mem_range, Fintype.card_coe, card_range]
  rw [Finset.card_biUnion (KeyPoint_area_disjoint n)]
  simp only [KeyPoint]
  -- Because all adjacentSet are pairwise disjoint, so the cardinality equals the sum of size of adjacent sets
  rw [Finset.sum_union (Line_union_disj_reLine_union n)]
  rw [Finset.sum_biUnion (PointInLine_i_disj n)]
  rw [Finset.sum_biUnion (PointInreLine_i_disj n)]
  -- And by lemma sum_of_card_adjacent_on_Line and sum_of_card_adjacent_on_reLine we have the sum equals n * n / 2 + n * n / 2 = n * n
  rw [sum_of_card_adjacent_on_Line, sum_of_card_adjacent_on_reLine]
  -- By computing we complete the proof
  obtain ⟨m, meq⟩ := fact_even.out
  replace meq : n = m * 2 := by rw [meq, mul_two];
  have : n * n / 2 = n * (n / 2) := by
    rw [meq, mul_div_cancel_right₀ m (by norm_num)]
    rw [show m * 2 * (m * 2) = m * m * 2 * 2 by ring]
    rw [mul_div_cancel_right₀ (m * m * 2) (by norm_num)]
    ring
  rw [this]
  have : n / 2 = m := by omega
  rw [this]
  rw [meq]
  ring

/-- Lemma : The cardinality of key-points equals n * (n + 2) / 4, which is the answer of the problem -/
lemma card_key_point [n_ne : NeZero n] [fact_even : Fact (Even n)] : #(KeyPoint n) = n * (n + 2) / 4 := by
  obtain ⟨m, meq⟩ := fact_even.out
  have meq' : n / 2 = m := by
    rw [meq, ← mul_two, mul_div_cancel_right₀ m (by norm_num)]
  have mge : m ≥ 1 := by
    by_contra lt
    simp only [ge_iff_le, not_le, Nat.lt_one_iff] at lt
    rw [lt, zero_add] at meq
    exact n_ne.out meq
  -- By the disjoint property, the cardinality equals the sum of key-points on each line
  rw [KeyPoint]
  rw [Finset.card_union_of_disjoint (Line_union_disj_reLine_union n)]
  rw [Finset.card_biUnion (PointInLine_i_disj n), Finset.card_biUnion (PointInreLine_i_disj n)]
  -- In PointInLine, the cardinality of key-points equals ∑ i ∈ Finset.range (n / 2), (i + 1) = (n / 2) * (n / 2 - 1) / 2
  have : ∑ i ∈ Finset.range (n / 2), #(PointInLine n i) = ∑ i ∈ Finset.range (n / 2), (i + 1) := by
    apply (sum_congr (by rfl))
    intro i imem
    rw [card_line n]
    simp only [Finset.mem_range] at imem
    omega
  rw [this]
  -- In PointInreLine, the cardinality of key-points equals ∑ i ∈ Finset.range (n / 2), (i + 1) = (n / 2) * (n / 2 - 1) / 2
  have : ∑ i ∈ Finset.range (n / 2), #(PointInreLine n i) = ∑ i ∈ Finset.range (n / 2), (i + 1) := by
    apply (sum_congr (by rfl))
    intro i imem
    rw [card_reline n]
    simp only [Finset.mem_range] at imem
    omega
  -- Then by computing, (n / 2) * (n / 2 - 1) / 2 + (n / 2) * (n / 2 - 1) / 2 = n * (n + 2) / 4
  rw [this]
  rw [← mul_two, meq', meq, sum_add_distrib, Finset.sum_const]
  rw [card_range, smul_eq_mul, mul_one, add_mul, sum_range_id_mul_two]
  rw [show (m + m) * (m + m + 2) = m * (m + 1) * 4 by ring]
  rw [mul_div_cancel_right₀ (m * (m + 1)) (by norm_num), ← mul_add]
  rw [show m - 1 + 2 = m + 1 by omega]


/--
Main theorem (IMO_1999_3) : Given an n x n square board, with n even and not zero.
Two distinct squares of the board are said to be adjacent if they share a common side, but a square is not adjacent to itself.
The minimum number of squares that can be marked so that every square is adjacent to at least one marked square is n * (n + 2) / 4
-/
theorem IMO_1999_3 [n_ne : NeZero n] [fact_even : Fact (Even n)] :
    IsLeast {k | ∃ marked : Finset (SquareBoard n), #marked = k ∧ (all_covered n marked)} (n * (n + 2) / 4) := by
  -- Unfold the definition of IsLeast and prove:
  -- (1) the candidate value lies in the set,
  -- (2) it is not greater than any other value in the set
  unfold IsLeast
  constructor
  · -- (1): We prove that there exist a set suffitient to the condition
    rw [Set.mem_setOf_eq]
    -- Use the set of key-points we defined as our marked set
    use KeyPoint n
    -- Prove: (i) its cardinality is n * (n + 2) / 4, and (ii) it covers the whole board.
    constructor
    · -- (i) By lemma, the cardinality of key-points equals n * (n + 2) / 4
      exact card_key_point n
    · -- (ii) We prove every square is adjacent to some key-point
      intro x
      -- Start from the obvious fact: every square x is in the full board
      have xmem : x ∈ (univ : Finset (SquareBoard n)) := Finset.mem_univ x
      -- We have proved that the union of adjacent sets equals full board
      -- Then there exist some key-point m such that x belongs to the adjacent set of m
      rw [← Union_eq_top, Finset.mem_biUnion] at xmem
      -- It shows m is adjacent to p, which means x is covered by marked point
      obtain ⟨m, mmem, xadj⟩ := xmem
      use m
      simp [adjacentSet] at xadj
      exact ⟨mmem, xadj⟩
  · -- (2): Minimality. Any covering marking has size at least n * (n + 2) / 4.
    -- Unfold the definition of lowerBounds
    unfold lowerBounds
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    -- Assume an arbitrary size k, a marking set mark, a size equality, and the covering property
    intro k mark card_eq covered
    -- Replace mark with mark ∩ univ to prepare for distributing intersection over a union
    rw [show mark = mark ∩ univ by simp only [Finset.inter_univ]] at card_eq
    -- Rewrite univ as the union over key points of their adjacent sets, then distribute the intersection
    rw [← Union_eq_top, Finset.inter_biUnion] at card_eq
    -- Prove that mark ∩ adjacentSet x is pairwise disjoint
    have : PairwiseDisjoint (KeyPoint n) (fun x ↦ mark ∩ adjacentSet n x) := by
      -- Take two distinct key points a ≠ b and prove the intersections are disjoint.
      intro a A b B abne
      -- Start from the disjointness of the adjacentSet of distinct key points.
      have := ((KeyPoint_area_disjoint n) A B abne)
      -- Simplify the form of lemma
      rw [onFun, ← disjoint_coe] at this ⊢
      rw [coe_inter, coe_inter]
      -- Because adjacentSet of a and adjacentSet of b are disjoint, so are mark ∩ adjacentSet a and mark ∩ adjacentSet b
      exact Disjoint.inter_right' mark (Disjoint.inter_left' mark this)
    -- With pairwise disjointness, the card of the big union equals the sum of the cards of parts.
    rw [Finset.card_biUnion this] at card_eq
    -- Move that equality to the goal side: we will bound this sum from below.
    rw [← card_eq]
    -- Claim: each summand #(mark ∩ adjacentSet n u) is ≥ 1; hence the sum ≥ (# of key points).
    have : ∑ u ∈ KeyPoint n, #(mark ∩ adjacentSet n u) ≥ ∑ u ∈ KeyPoint n, 1 := by
      -- We prove for every key-point u, #(mark ∩ adjacentSet n u) ≥ 1
      apply Finset.sum_le_sum
      -- Fix a key point p ∈ KeyPoint n
      intro p pmem
      -- Suppose it's less than 1
      by_contra ez
      -- Which shows the adjacentSet of p if empty set
      simp only [one_le_card, Finset.not_nonempty_iff_eq_empty] at ez
      -- Since the board is covered, there is m ∈ mark adjacent to p
      obtain ⟨m, padj⟩ := covered p
      -- That witness m lies in the intersection mark ∩ adjacentSet n p
      have : m ∈ mark ∩ adjacentSet n p := by
        -- Show membership in the intersection by showing each component.
        simp only [Finset.mem_inter]
        -- Right component: m ∈ adjacentSet n p because adjacent m p
        simp [adjacentSet]
        -- Use symmetry to convert adjacent p m  into adjacent m p
        rw [adjacent_symm]
        -- Then the goal is same as the property of m we chosen
        exact padj
      -- Contradiction: the intersection is empty but contains m
      rw [ez] at this
      exact Finset.not_mem_empty m this
    -- Evaluate the right-hand sum: summing 1 over all key points yields #(KeyPoint n), by lemma we proved, it equals n * (n + 2) / 4
    simp only [sum_const, smul_eq_mul, mul_one, ge_iff_le, card_key_point n] at this
    -- Done: n * (n + 2) / 4 ≤ k for any covering marking of size k, minimality holds.
    exact this
