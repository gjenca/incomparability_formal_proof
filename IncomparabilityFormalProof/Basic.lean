import Mathlib

/-! ## Orthoset typeclass -/

/-- An orthoset is a type equipped with a symmetric, irreflexive relation -/
class Orthoset (α : Type*) where
  /-- The orthogonality relation -/
  perp : α → α → Prop
  perp_symm : Symmetric perp
  perp_irrefl : ∀ a : α, ¬ perp a a

notation:50 a " ⊥ " b => Orthoset.perp a b

/-! ## Partial orders as orthosets via incomparability -/

/-- Two elements of a partial order are incomparable if neither is ≤ the other -/
def Incomparable {P : Type*} [PartialOrder P] (a b : P) : Prop := ¬ a ≤ b ∧ ¬ b ≤ a

/-- Every partial order is an orthoset via the incomparability relation -/
@[reducible] instance instOrthosetOfPartialOrder {P : Type*} [PartialOrder P] : Orthoset P where
  perp := Incomparable
  perp_symm := fun _ _ h => ⟨h.2, h.1⟩
  perp_irrefl := fun _ h => h.1 le_rfl

/-- For partial orders, ⊥ unfolds to the incomparability condition -/
@[simp] lemma perp_iff {P : Type*} [PartialOrder P] (a b : P) :
    (a ⊥ b) ↔ ¬ a ≤ b ∧ ¬ b ≤ a := Iff.rfl

/-! ## General orthoset concepts -/

variable {O : Type*} [Orthoset O]

/-- The orthogonal complement of a set X:
    all elements orthogonal to every element of X -/
def orthComp (X : Set O) : Set O := {y | ∀ x ∈ X, x ⊥ y}

/-- A set X is orthoclosed if X = (X⊥)⊥ -/
def IsOrthoclosed (X : Set O) : Prop := orthComp (orthComp X) = X

/-- B is an orthobase of X:
    B ⊆ X, elements of B are pairwise orthogonal,
    and B is maximal with these properties in X -/
def IsOrthoBase (B X : Set O) : Prop :=
  B ⊆ X ∧
  (∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ ⊥ b₂) ∧
  (∀ x ∈ X, (∀ b ∈ B, x ⊥ b) → x ∈ B)

/-- Characterization of orthocomplements:
    X is orthoclosed and Y = X⊥ if and only if
    (1) X ⊥ Y (every element of X is orthogonal to every element of Y), and
    (2) every z ∉ X ∪ Y is non-orthogonal to some element of X and
        non-orthogonal to some element of Y. -/
lemma orthoclosed_and_eq_orthComp_iff (X Y : Set O) :
    (IsOrthoclosed X ∧ Y = orthComp X) ↔
    ((∀ x ∈ X, ∀ y ∈ Y, x ⊥ y) ∧
     (∀ z ∉ X ∪ Y, (∃ x ∈ X, ¬ z ⊥ x) ∧ (∃ y ∈ Y, ¬ z ⊥ y))) := by
  constructor
  · rintro ⟨hX, hY⟩
    constructor
    · -- X ⊥ Y
      intro x hx y hy
      rw [hY] at hy
      exact hy x hx
    · -- every z ∉ X ∪ Y has a witness in X and a witness in Y
      intro z hz
      simp only [Set.mem_union, not_or] at hz
      obtain ⟨hzX, hzY⟩ := hz
      constructor
      · by_contra hall
        push Not at hall
        apply hzY; rw [hY]
        exact fun x hx => Orthoset.perp_symm (hall x hx)
      · by_contra hall
        push Not at hall
        apply hzX; rw [← hX]
        intro u hu
        apply Orthoset.perp_symm; apply hall
        rw [hY]; exact hu
  · rintro ⟨hXY, hwit⟩
    constructor
    · -- IsOrthoclosed X = orthComp (orthComp X) = X
      apply Set.Subset.antisymm
      · -- orthComp (orthComp X) ⊆ X
        intro z hz
        by_contra hzX
        by_cases hzY : z ∈ Y
        · -- z ∈ Y → z ∈ orthComp X → z ⊥ z, contradiction
          have hzOC : z ∈ orthComp X := fun x hx => hXY x hx z hzY
          exact Orthoset.perp_irrefl z (hz z hzOC)
        · -- z ∉ X ∪ Y → get y₀ ∈ Y with ¬ z ⊥ y₀, but y₀ ∈ orthComp X
          obtain ⟨-, y₀, hy₀Y, hzy₀⟩ := hwit z (by simp [Set.mem_union, hzX, hzY])
          have hy₀OC : y₀ ∈ orthComp X := fun x hx => hXY x hx y₀ hy₀Y
          exact hzy₀ (Orthoset.perp_symm (hz y₀ hy₀OC))
      · -- X ⊆ orthComp (orthComp X)
        intro x hx u hu
        exact Orthoset.perp_symm (hu x hx)
    · -- Y = orthComp X
      apply Set.Subset.antisymm
      · -- Y ⊆ orthComp X
        intro y hy x hx
        exact hXY x hx y hy
      · -- orthComp X ⊆ Y
        intro z hz
        by_contra hzY
        have hzX : z ∉ X := fun hzX => Orthoset.perp_irrefl z (hz z hzX)
        obtain ⟨x₀, hx₀X, hzx₀⟩ := (hwit z (by simp [Set.mem_union, hzX, hzY])).1
        exact hzx₀ (Orthoset.perp_symm (hz x₀ hx₀X))

/-! ## Basic properties of orthComp -/

lemma orthComp_antitone {X Y : Set O} (h : X ⊆ Y) : orthComp Y ⊆ orthComp X :=
  fun _ hz x hx => hz x (h hx)

lemma subset_orthComp_orthComp (X : Set O) : X ⊆ orthComp (orthComp X) :=
  fun x hx _ hu => Orthoset.perp_symm (hu x hx)

lemma orthComp_orthComp_orthComp (X : Set O) :
    orthComp (orthComp (orthComp X)) = orthComp X :=
  Set.Subset.antisymm
    (orthComp_antitone (subset_orthComp_orthComp X))
    (subset_orthComp_orthComp (orthComp X))

/-- X is a Dacey subset: an orthoclosed set X such that (B⊥)⊥ = X for every basis B of X -/
def IsDaceySubset (X : Set O) : Prop :=
  ∀ B : Set O, IsOrthoBase B X → orthComp (orthComp B) = X

/-- An orthoset is Dacey if every orthoclosed subset is a Dacey subset -/
def IsDacey (O : Type*) [Orthoset O] : Prop :=
  ∀ X : Set O, IsOrthoclosed X → IsDaceySubset X

/-- Characterization of Dacey subsets (Jenča 2023).
    For an orthoclosed set X the following are equivalent:
    (a) X is a Dacey subset: (B⊥)⊥ = X for every basis B of X
    (b) B⊥ = X⊥ for every basis B of X
    (c) B⊥ ⊆ X⊥ for every basis B of X
    We state this as (a) ↔ (c), the non-trivial direction being (c) → (a). -/
lemma chardacey {X : Set O} (hX : IsOrthoclosed X) :
    IsDaceySubset X ↔
    ∀ B : Set O, IsOrthoBase B X → orthComp B ⊆ orthComp X := by
  constructor
  · -- (a) → (c): B⊥ = B⊥⊥⊥ = X⊥
    intro hD B hB
    exact ((orthComp_orthComp_orthComp B).symm.trans (congrArg orthComp (hD B hB))).le
  · -- (c) → (a): B ⊆ X gives B⊥⊥ ⊆ X⊥⊥ = X; B⊥ ⊆ X⊥ gives X = X⊥⊥ ⊆ B⊥⊥
    intro hc B hB
    apply Set.Subset.antisymm
    · calc orthComp (orthComp B)
          ⊆ orthComp (orthComp X) := orthComp_antitone (orthComp_antitone hB.1)
        _ = X                     := hX
    · calc X = orthComp (orthComp X) := hX.symm
        _ ⊆ orthComp (orthComp B)    := orthComp_antitone (hc B hB)

/-! ## Basics -/

variable {P : Type*} [PartialOrder P]

/-- The incomparability set of x: all elements incomparable to x -/
def incompSet (x : P) : Set P := {z | x ⊥ z}

/-! ## Dacey incomparability orthospace -/

/-- Refinement of orthocomplements for the incomparability orthoset of a poset.
    X is orthoclosed and Y = X⊥ iff X ⊥ Y and for every z ∉ X ∪ Y there exist
    x ∈ X, y ∈ Y such that z < x and z < y (z below both), or x < z and y < z
    (z above both). -/
lemma updown (X Y : Set P) :
    (IsOrthoclosed X ∧ Y = orthComp X) ↔
    ((∀ x ∈ X, ∀ y ∈ Y, x ⊥ y) ∧
     (∀ z ∉ X ∪ Y, ∃ x ∈ X, ∃ y ∈ Y, (z < x ∧ z < y) ∨ (x < z ∧ y < z))) := by
  rw [orthoclosed_and_eq_orthComp_iff]
  constructor
  · rintro ⟨hXY, hwit⟩
    refine ⟨hXY, ?_⟩
    intro z hz
    obtain ⟨⟨x, hxX, hnzx⟩, ⟨y, hyY, hnzy⟩⟩ := hwit z hz
    simp only [Set.mem_union, not_or] at hz
    obtain ⟨hzX, hzY⟩ := hz
    simp only [perp_iff, not_and_or, not_not] at hnzx hnzy
    -- ¬ z ⊥ x and z ≠ x gives strict order; same for y
    have hzx : z < x ∨ x < z := by
      rcases hnzx with h | h
      · exact Or.inl (h.lt_of_ne (fun heq => hzX (heq ▸ hxX)))
      · exact Or.inr (h.lt_of_ne (fun heq => hzX (heq.symm ▸ hxX)))
    have hzy : z < y ∨ y < z := by
      rcases hnzy with h | h
      · exact Or.inl (h.lt_of_ne (fun heq => hzY (heq ▸ hyY)))
      · exact Or.inr (h.lt_of_ne (fun heq => hzY (heq.symm ▸ hyY)))
    -- hXY rules out mixed directions: z < x and y < z gives y < x, contradicting x ⊥ y
    have hxy := (perp_iff x y).mp (hXY x hxX y hyY)
    exact ⟨x, hxX, y, hyY,
      hzx.imp
        (fun hzx => ⟨hzx, hzy.resolve_right (fun hyz => hxy.2 (hyz.trans hzx).le)⟩)
        (fun hxz => ⟨hxz, hzy.resolve_left (fun hzy => hxy.1 (hxz.trans hzy).le)⟩)⟩
  · rintro ⟨hXY, hwit⟩
    refine ⟨hXY, ?_⟩
    intro z hz
    obtain ⟨x, hxX, y, hyY, h⟩ := hwit z hz
    rcases h with ⟨hzx, hzy⟩ | ⟨hxz, hyz⟩
    · exact ⟨⟨x, hxX, fun h => h.1 hzx.le⟩, ⟨y, hyY, fun h => h.1 hzy.le⟩⟩
    · exact ⟨⟨x, hxX, fun h => h.2 hxz.le⟩, ⟨y, hyY, fun h => h.2 hyz.le⟩⟩

/-- (a,b,c,d) form an N:
    a < c, b ⋖ c, b < d, a ⊥ b, a ⊥ d, c ⊥ d
    (like a weak N but with the additional condition a ⊥ d) -/
def IsN (a b c d : P) : Prop :=
  a < c ∧ b ⋖ c ∧ b < d ∧ (a ⊥ b) ∧ (a ⊥ d) ∧ (c ⊥ d)

/-- P is N-free: it contains no N -/
def IsNFree (P : Type*) [PartialOrder P] : Prop :=
  ¬ ∃ a b c d : P, IsN a b c d

/-! ## Definitions regarding the compatibility-/

/-- (a,b,c,d) form a very weak N:
    a < c, b < c, b < d, a ⊥ b, c ⊥ d
    (like a weak N but without the covering condition on b and c) -/
def IsVeryWeakN (a b c d : P) : Prop :=
  a < c ∧ b < c ∧ b < d ∧ (a ⊥ b) ∧ (c ⊥ d)

/-- (a,b,c,d) form a weak N:
    a < c, b ⋖ c, b < d, a ⊥ b, c ⊥ d -/
def IsWeakN (a b c d : P) : Prop :=
  a < c ∧ b ⋖ c ∧ b < d ∧ (a ⊥ b) ∧ (c ⊥ d)

/-- P has a compatible incomparability orthoset:
    for all comparable x, y, there exists z such that
    incompSet x ∪ incompSet y ⊆ incompSet z -/
def IsCompatible (P : Type*) [PartialOrder P] : Prop :=
  ∀ x y : P, ¬ (x ⊥ y) →
    ∃ z : P, incompSet x ∪ incompSet y ⊆ incompSet z

/-- (a,b,c,d;m) form an X:
    a < m < c, b < m < d, a ⊥ b, c ⊥ d -/
def IsX (a b c d m : P) : Prop :=
  a < m ∧ m < c ∧ b < m ∧ m < d ∧ (a ⊥ b) ∧ (c ⊥ d)

/-- (a,b,c,d;m) form a covering X: an X with m ⋖ c -/
def IsCoveringX (a b c d m : P) : Prop :=
  a < m ∧ m ⋖ c ∧ b < m ∧ m < d ∧ (a ⊥ b) ∧ (c ⊥ d)

/-! ## Basic helper -/

/-- Every weak N is a very weak N -/
lemma IsWeakN.isVeryWeakN {a b c d : P} (h : IsWeakN a b c d) : IsVeryWeakN a b c d :=
  ⟨h.1, h.2.1.lt, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-! ## Lemma 1: X ↔ covering X -/

/-- A finite poset contains an X iff it contains a covering X -/
lemma hasX_iff_hasCoveringX [Finite P] :
    (∃ a b c d m : P, IsX a b c d m) ↔
    (∃ a b c d m : P, IsCoveringX a b c d m) := by
  constructor
  · intro ⟨a, b, c, d, m, h1, h2, h3, h4, h5, h6⟩
    haveI : Fintype P := Fintype.ofFinite P
    haveI : DecidableRel (α := P) (· < ·) := fun _ _ => Classical.dec _
    haveI : DecidableRel (α := P) (· ≤ ·) := fun _ _ => Classical.dec _
    -- Step 1: pick a maximal element m' of M = {x | m ≤ x ∧ x < c ∧ x < d}
    let M : Finset P := Finset.univ.filter (fun x => m ≤ x ∧ x < c ∧ x < d)
    have hMne : M.Nonempty :=
      ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _, h2, h4⟩⟩
    obtain ⟨m', hm'M, hm'max⟩ := M.exists_maximal hMne
    rw [Finset.mem_filter] at hm'M
    obtain ⟨-, hm'm, hm'c, hm'd⟩ := hm'M
    -- Step 2: pick a minimal element c' of A = {x | m' < x ∧ x ≤ c}
    let A : Finset P := Finset.univ.filter (fun x => m' < x ∧ x ≤ c)
    have hAne : A.Nonempty :=
      ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm'c, le_refl _⟩⟩
    obtain ⟨c', hc'A, hc'min⟩ := A.exists_minimal hAne
    rw [Finset.mem_filter] at hc'A
    obtain ⟨-, hm'c', hc'c⟩ := hc'A
    -- Step 3: m' ⋖ c'
    have hcov : m' ⋖ c' :=
      ⟨hm'c', fun z hm'z hzc' => by
        have hzA : z ∈ A := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hm'z, (hzc'.trans_le hc'c).le⟩
        exact lt_irrefl c' (lt_of_le_of_lt (hc'min hzA hzc'.le) hzc')⟩
    -- Step 4: c' ⊥ d
    -- For ¬ c' ≤ d: if c' < c then c' ∈ M contradicts maximality of m';
    --               if c' = c then c ≤ d contradicts h6
    -- For ¬ d ≤ c': d < c' contradicts m' ⋖ c'; d = c' gives d ≤ c contradicting h6
    have hc'd : c' ⊥ d := by
      refine ⟨fun hle => ?_, fun hle => ?_⟩
      · rcases hc'c.lt_or_eq with hc'c_lt | hc'c_eq
        · rcases hle.lt_or_eq with hc'd_lt | hc'd_eq
          · -- c' < c and c' < d: c' ∈ M, contradicts maximality of m'
            have hc'M : c' ∈ M := Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, hm'm.trans hm'c'.le, hc'c_lt, hc'd_lt⟩
            exact lt_irrefl m' (lt_of_lt_of_le hm'c' (hm'max hc'M hm'c'.le))
          · -- c' = d, so d < c, contradicts c ⊥ d
            exact h6.2 (hc'd_eq.symm.le.trans hc'c_lt.le)
        · -- c' = c, so c ≤ d, contradicts c ⊥ d
          exact h6.1 (hc'c_eq.symm.le.trans hle)
      · rcases hle.lt_or_eq with hlt | heq
        · exact hcov.2 hm'd hlt
        · exact h6.2 (heq.le.trans hc'c)
    -- Conclude
    exact ⟨a, b, c', d, m',
      h1.trans_le hm'm, hcov, h3.trans_le hm'm, hm'd, h5, hc'd⟩
  · rintro ⟨a, b, c, d, m, h1, h2, h3, h4, h5, h6⟩
    exact ⟨a, b, c, d, m, h1, h2.lt, h3, h4, h5, h6⟩

/-! ## (b) → (a): compatible implies no weak N and no X -/

/-- If a poset contains a weak N, then it is not compatible -/
lemma not_compatible_if_weakN (a b c d : P) (h : IsWeakN a b c d) :
    ¬ IsCompatible P := by
  obtain ⟨hac, hbc, hbd, hab, hcd⟩ := h
  intro hcomp
  -- b and c are comparable (b < c), so compatibility applies
  obtain ⟨z, hz⟩ := hcomp b c (fun h => h.1 hbc.lt.le)
  -- z ⊥ a (a ∈ incompSet b since b ⊥ a) and z ⊥ d (d ∈ incompSet c since c ⊥ d)
  have hza : z ⊥ a := hz (Set.mem_union_left  _ (show b ⊥ a from ⟨hab.2, hab.1⟩))
  have hzd : z ⊥ d := hz (Set.mem_union_right _ hcd)
  -- ¬ z ⊥ b: otherwise z ∈ incompSet b, hence z ∈ incompSet z, giving z ⊥ z — impossible
  have hzb : ¬ (z ⊥ b) := fun h =>
    (hz (Set.mem_union_left _ (show b ⊥ z from ⟨h.2, h.1⟩))).1 le_rfl
  -- ¬ z ⊥ c: same argument on the right
  have hzc : ¬ (z ⊥ c) := fun h =>
    (hz (Set.mem_union_right _ (show c ⊥ z from ⟨h.2, h.1⟩))).1 le_rfl
  -- b < z: from ¬ z ⊥ b we get z ≤ b or b ≤ z;
  --        z ≤ b leads to z ≤ d (via hbd) contradicting z ⊥ d;
  --        b = z leads to b ≤ d (via hbd) contradicting z ⊥ d
  have hbz : b < z := by
    simp only [perp_iff, not_and_or, not_not] at hzb
    rcases hzb with hzb | hbz
    · exact absurd (hzb.trans hbd.le) hzd.1
    · rcases hbz.lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hbd.le) hzd.1
  -- z < c: from ¬ z ⊥ c we get z ≤ c or c ≤ z;
  --        c ≤ z leads to a ≤ z (via hac) contradicting z ⊥ a;
  --        z = c leads to a ≤ c (via hac) contradicting z ⊥ a
  have hzc' : z < c := by
    simp only [perp_iff, not_and_or, not_not] at hzc
    rcases hzc with hzc | hcz
    · rcases hzc.lt_or_eq with h | h
      · exact h
      · exact absurd hac.le (h ▸ hza).2
    · exact absurd (hac.le.trans hcz) hza.2
  -- b < z < c contradicts b ⋖ c
  exact hbc.2 hbz hzc'

/-- If a finite poset P contains an X, then P is not compatible -/
lemma not_compatible_if_X [Finite P] (a b c d m : P) (h : IsX a b c d m) :
    ¬ IsCompatible P := by
  -- Reduce to a covering X via hasX_iff_hasCoveringX
  obtain ⟨a, b, c, d, m, h1, h2, h3, h4, h5, h6⟩ :=
    hasX_iff_hasCoveringX.mp ⟨a, b, c, d, m, h⟩
  -- a < m ⋖ c, so a < c, hence a and c are comparable
  intro hcomp
  obtain ⟨z, hz⟩ := hcomp a c (fun h => h.1 (h1.trans h2.lt).le)
  -- z ⊥ b (b ∈ incompSet a via a ⊥ b = h5) and z ⊥ d (d ∈ incompSet c via c ⊥ d = h6)
  have hzb : z ⊥ b := hz (Set.mem_union_left  _ h5)
  have hzd : z ⊥ d := hz (Set.mem_union_right _ h6)
  -- ¬ z ⊥ a and ¬ z ⊥ c (same self-incomparability argument as in not_compatible_if_weakN)
  have hza : ¬ (z ⊥ a) := fun h =>
    (hz (Set.mem_union_left  _ (show a ⊥ z from ⟨h.2, h.1⟩))).1 le_rfl
  have hzc : ¬ (z ⊥ c) := fun h =>
    (hz (Set.mem_union_right _ (show c ⊥ z from ⟨h.2, h.1⟩))).1 le_rfl
  -- z < c: c ≤ z gives b ≤ z (via b < m < c ≤ z) contradicting z ⊥ b;
  --        z = c gives b ≤ c (via b < m < c) but (c ⊥ b = z ⊥ b) says ¬ b ≤ c
  have hzc' : z < c := by
    simp only [perp_iff, not_and_or, not_not] at hzc
    rcases hzc with hzc | hcz
    · rcases hzc.lt_or_eq with h | h
      · exact h
      · exact absurd (h3.trans h2.lt).le (h ▸ hzb).2
    · exact absurd ((h3.trans h2.lt).le.trans hcz) hzb.2
  -- a < z: z ≤ a gives z ≤ d (via a < m < d) contradicting z ⊥ d;
  --        z = a gives a ≤ d (via a < m < d) but (a ⊥ d = z ⊥ d) says ¬ a ≤ d
  have haz : a < z := by
    simp only [perp_iff, not_and_or, not_not] at hza
    rcases hza with hza | haz
    · exact absurd (hza.trans (h1.trans h4).le) hzd.1
    · rcases haz.lt_or_eq with h | h
      · exact h
      · exact absurd (h1.trans h4).le (h.symm ▸ hzd).1
  -- z ⊥ m: z < m gives z ≤ d (via m < d) contradicting z ⊥ d;
  --        m ≤ z gives b ≤ z (via b < m) contradicting z ⊥ b
  have hzm : z ⊥ m :=
    ⟨fun hzm => absurd (hzm.trans h4.le) hzd.1,
     fun hmz => absurd (h3.le.trans hmz) hzb.2⟩
  -- Now N^?(z, m, c, d): z < c, m ⋖ c, m < d, z ⊥ m, c ⊥ d
  exact not_compatible_if_weakN z m c d ⟨hzc', h2, h4, hzm, h6⟩ hcomp

/-! ## (a) → (b): infrastructure for the chain argument -/

/-- If x < y and no z witnesses compatibility for x, y, then there is a very weak N -/
private lemma veryWeakN_aux (x y : P) (hxy : x < y)
    (hfall : ∀ z : P, ¬ (incompSet x ∪ incompSet y ⊆ incompSet z)) :
    ∃ a d : P, IsVeryWeakN a x y d := by
  -- x⊥ ⊄ y⊥: otherwise z = y witnesses compatibility
  have hx_not_sub : ¬ (incompSet x ⊆ incompSet y) := fun h =>
    hfall y (Set.union_subset h (Set.Subset.refl _))
  -- y⊥ ⊄ x⊥: otherwise z = x witnesses compatibility
  have hy_not_sub : ¬ (incompSet y ⊆ incompSet x) := fun h =>
    hfall x (Set.union_subset (Set.Subset.refl _) h)
  -- pick a ∈ x⊥ \ y⊥ and d ∈ y⊥ \ x⊥
  obtain ⟨a, ha_x, ha_y⟩ := Set.not_subset.mp hx_not_sub
  obtain ⟨d, hd_y, hd_x⟩ := Set.not_subset.mp hy_not_sub
  -- unfold incompSet membership
  simp only [incompSet, Set.mem_setOf_eq] at ha_x ha_y hd_y hd_x
  -- ha_x : x ⊥ a,  ha_y : ¬ y ⊥ a  →  comparable, so y ≤ a ∨ a ≤ y
  -- hd_y : y ⊥ d,  hd_x : ¬ x ⊥ d  →  comparable, so x ≤ d ∨ d ≤ x
  simp only [perp_iff, not_and_or, not_not] at ha_y hd_x
  -- a < y: y ≤ a gives x ≤ a contradicting ha_x; a = y gives x ⊥ y contradicting hxy
  have hay : a < y := by
    rcases ha_y with hya | hay
    · exact absurd (hxy.le.trans hya) ha_x.1
    · rcases hay.lt_or_eq with h | h
      · exact h
      · exact absurd hxy.le (h ▸ ha_x).1
  -- x < d: d ≤ x gives d ≤ y contradicting hd_y; d = x gives y ⊥ x contradicting hxy
  have hxd : x < d := by
    rcases hd_x with hxd | hdx
    · rcases hxd.lt_or_eq with h | h
      · exact h
      · exact absurd hxy.le (h.symm ▸ hd_y).2
    · exact absurd (hdx.trans hxy.le) hd_y.2
  -- witnesses: IsVeryWeakN a x y d
  exact ⟨a, d, hay, hxy, hxd, ⟨ha_x.2, ha_x.1⟩, hd_y⟩

/-- Every incompatible poset contains a very weak N -/
lemma exists_veryWeakN_of_not_compatible (hP : ¬ IsCompatible P) :
    ∃ a b c d : P, IsVeryWeakN a b c d := by
  unfold IsCompatible at hP
  push Not at hP
  obtain ⟨x, y, hxy_comp, hfall⟩ := hP
  -- x ≠ y: if x = y then z = x is a valid witness, contradicting hfall
  have hne : x ≠ y := fun heq =>
    hfall x (heq ▸ (Set.union_self _).subset)
  -- ¬ (x ⊥ y) gives x ≤ y or y ≤ x; with x ≠ y this is x < y or y < x
  simp only [perp_iff, not_and_or, not_not] at hxy_comp
  rcases hxy_comp with hle | hle
  · -- x < y: apply the helper directly
    obtain ⟨a, d, hvw⟩ := veryWeakN_aux x y (hle.lt_of_ne hne) hfall
    exact ⟨a, x, y, d, hvw⟩
  · -- y < x: swap roles; union is commutative so hfall still applies
    obtain ⟨a, d, hvw⟩ := veryWeakN_aux y x (hle.lt_of_ne (Ne.symm hne))
      (fun z hz => hfall z (Set.union_comm _ _ ▸ hz))
    exact ⟨a, y, x, d, hvw⟩

/-- Claim (used in the chain argument): if no single element witnesses compatibility for x and y,
    then every z strictly between x and y either has some w ⊥ x with w < z,
    or some w ⊥ y with z < w. -/
private lemma chain_claim (x y : P)
    (hfall : ∀ z : P, ¬ (incompSet x ∪ incompSet y ⊆ incompSet z))
    {z : P} (hxz : x < z) (hzy : z < y) :
    (∃ w : P, (x ⊥ w) ∧ w < z) ∨ (∃ w : P, z < w ∧ (y ⊥ w)) := by
  -- z does not witness compatibility, so some u ∈ incompSet x ∪ incompSet y is comparable to z
  obtain ⟨u, hu_in, hu_ninc⟩ := Set.not_subset.mp (hfall z)
  simp only [incompSet, Set.mem_setOf_eq] at hu_ninc
  simp only [perp_iff, not_and_or, not_not] at hu_ninc
  -- hu_ninc : z ≤ u ∨ u ≤ z
  rw [Set.mem_union] at hu_in
  rcases hu_in with hxu | hyu
  · -- u ∈ incompSet x, i.e., x ⊥ u
    simp only [incompSet, Set.mem_setOf_eq] at hxu
    rcases hu_ninc with hzu | huz
    · -- z ≤ u: then x < z ≤ u contradicts x ⊥ u
      exact absurd (hxz.le.trans hzu) hxu.1
    · -- u ≤ z: witness w = u; u < z since u = z would give x ⊥ z contradicting x < z
      exact Or.inl ⟨u, hxu, huz.lt_of_ne (fun heq => absurd hxz.le (heq ▸ hxu.1))⟩
  · -- u ∈ incompSet y, i.e., y ⊥ u
    simp only [incompSet, Set.mem_setOf_eq] at hyu
    rcases hu_ninc with hzu | huz
    · -- z ≤ u: witness w = u; z < u since z = u would give y ⊥ z contradicting z < y
      exact Or.inr ⟨u, hzu.lt_of_ne (fun heq => absurd (heq ▸ hzy.le) hyu.2), hyu⟩
    · -- u ≤ z: then u ≤ z < y contradicts y ⊥ u
      exact absurd (huz.trans hzy.le) hyu.2


/-- If a finite poset contains a very weak N (a, x, y, d) where x < y witness
    incompatibility (no z covers both incomparability sets), then P contains
    a weak N or an X. -/
private lemma weakN_or_X_of_veryWeakN [Finite P]
    {a x y d : P} (hVW : IsVeryWeakN a x y d)
    (hfall : ∀ z : P, ¬ (incompSet x ∪ incompSet y ⊆ incompSet z)) :
    (∃ a b c d : P, IsWeakN a b c d) ∨ (∃ a b c d m : P, IsX a b c d m) := by
  haveI : Fintype P := Fintype.ofFinite P
  haveI : DecidableLT P := fun _ _ => Classical.dec _
  haveI : DecidableLE P := fun _ _ => Classical.dec _
  haveI : LocallyFiniteOrder P := Fintype.toLocallyFiniteOrder
  obtain ⟨hay, hxy, hxd, hax, hyd⟩ := hVW
  by_cases hcov : x ⋖ y
  · exact Or.inl ⟨a, x, y, d, hay, hcov, hxd, hax, hyd⟩
  · -- ¬ x ⋖ y: interior of [x,y] is nonempty
    -- Lower witnesses: all w with x ⊥ w that lie strictly below some z ∈ Ioo x y
    let L : Set P := {z | x < z ∧ z < y ∧ ∃ w, (x ⊥ w) ∧ w < z}
    by_cases hL : L = ∅
    · -- L = ∅: every z in Ioo x y has an upper witness
      -- Ioo x y is nonempty since ¬ x ⋖ y
      have hIoo_ne : (Finset.Ioo x y).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        exact hcov (covBy_iff_Ioo_eq.mpr ⟨hxy,
          by rw [← Finset.coe_Ioo, Finset.coe_eq_empty]; exact h⟩)
      -- Take a maximal element z_max of Ioo x y
      obtain ⟨z_max, hz_max_mem, hz_max_max⟩ := (Finset.Ioo x y).exists_maximal hIoo_ne
      rw [Finset.mem_Ioo] at hz_max_mem
      obtain ⟨hxz, hzy⟩ := hz_max_mem
      -- z_max ⋖ y: any b with z_max < b < y would be in Ioo x y, contradicting maximality
      have hcov_zy : z_max ⋖ y := ⟨hzy, fun b hzb hby =>
        lt_irrefl z_max (hzb.trans_le
          (hz_max_max (Finset.mem_Ioo.mpr ⟨hxz.trans hzb, hby⟩) hzb.le))⟩
      -- z_max has an upper witness: it has no lower witness (since L = ∅)
      obtain ⟨w, hzw, hyw⟩ : ∃ w, z_max < w ∧ y ⊥ w := by
        rcases chain_claim x y hfall hxz hzy with ⟨w, hxw, hwz⟩ | ⟨w, hzw, hyw⟩
        · exact absurd (show z_max ∈ L from ⟨hxz, hzy, w, hxw, hwz⟩)
            (by simp [hL])
        · exact ⟨w, hzw, hyw⟩
      by_cases haz : a ⊥ z_max
      · -- a ⊥ z_max: IsWeakN a z_max y w
        exact Or.inl ⟨a, z_max, y, w, hay, hcov_zy, hzw, haz, hyw⟩
      · simp only [perp_iff, not_and_or, not_not] at haz
        rcases haz with haz | hza
        · rcases haz.lt_or_eq with hlt | heq
          · -- a < z_max: IsX a x y w z_max
            exact Or.inr ⟨a, x, y, w, z_max, hlt, hzy, hxz, hzw, hax, hyw⟩
          · -- a = z_max: x < z_max = a contradicts a ⊥ x
            exact absurd (heq ▸ hxz).le hax.2
        · -- z_max ≤ a: x < z_max ≤ a contradicts a ⊥ x
          exact absurd (hxz.trans_le hza).le hax.2
    · -- L ≠ ∅: take a minimal element z_min of L
      haveI : DecidablePred (· ∈ L) := fun _ => Classical.dec _
      have hLne : (Set.toFinset L).Nonempty :=
        Set.toFinset_nonempty.mpr (Set.nonempty_iff_ne_empty.mpr hL)
      obtain ⟨z_min, hz_min_mem, hz_min_min⟩ := (Set.toFinset L).exists_minimal hLne
      rw [Set.mem_toFinset] at hz_min_mem
      obtain ⟨hxz, hzy, w, hxw, hwz⟩ := hz_min_mem
      by_cases hcov_xz : x ⋖ z_min
      · -- x ⋖ z_min: three cases on z_min vs d
        by_cases hdz : z_min ⊥ d
        · -- z_min ⊥ d: IsWeakN w x z_min d
          exact Or.inl ⟨w, x, z_min, d, hwz, hcov_xz, hxd, ⟨hxw.2, hxw.1⟩, hdz⟩
        · simp only [perp_iff, not_and_or, not_not] at hdz
          rcases hdz with hzd | hdz
          · -- z_min ≤ d: strengthen to z_min < d (z_min = d gives d < y contradicting hyd)
            have hzd_strict : z_min < d := hzd.lt_of_ne
              (fun heq => absurd (heq ▸ hzy).le hyd.2)
            -- IsX w x y d z_min
            exact Or.inr ⟨w, x, y, d, z_min, hwz, hzy, hxz, hzd_strict, ⟨hxw.2, hxw.1⟩, hyd⟩
          · -- d ≤ z_min: d ≤ z_min < y contradicts y ⊥ d
            exact absurd (hdz.trans_lt hzy).le hyd.2
      · -- ¬ x ⋖ z_min: interior of [x, z_min] is nonempty
        have hIoo_ne : (Finset.Ioo x z_min).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          exact hcov_xz (covBy_iff_Ioo_eq.mpr ⟨hxz,
            by rw [← Finset.coe_Ioo, Finset.coe_eq_empty]; exact h⟩)
        obtain ⟨z_prec, hz_prec_mem, hz_prec_max⟩ :=
          (Finset.Ioo x z_min).exists_maximal hIoo_ne
        rw [Finset.mem_Ioo] at hz_prec_mem
        obtain ⟨hxzp, hzpz⟩ := hz_prec_mem
        have hcov_pz : z_prec ⋖ z_min := ⟨hzpz, fun b hzpb hbz =>
          lt_irrefl z_prec (hzpb.trans_le
            (hz_prec_max (Finset.mem_Ioo.mpr ⟨hxzp.trans hzpb, hbz⟩) hzpb.le))⟩
        -- z_prec ∉ L: z_min is minimal in L and z_prec < z_min
        have hzp_notL : z_prec ∉ L := fun hzp_in =>
          lt_irrefl z_prec (hzpz.trans_le
            (hz_min_min (Set.mem_toFinset.mpr hzp_in) hzpz.le))
        -- z_prec has an upper witness (no lower witness since z_prec ∉ L)
        obtain ⟨w_prec, hwp, hywp⟩ : ∃ w_prec, z_prec < w_prec ∧ y ⊥ w_prec := by
          rcases chain_claim x y hfall hxzp (hzpz.trans hzy) with
            ⟨w', hxw', hw'z⟩ | ⟨w', hzw', hyw'⟩
          · exact absurd (show z_prec ∈ L from ⟨hxzp, hzpz.trans hzy, w', hxw', hw'z⟩) hzp_notL
          · exact ⟨w', hzw', hyw'⟩
        -- three cases on z_min vs w_prec
        by_cases hzw_prec : z_min ⊥ w_prec
        · -- z_min ⊥ w_prec: three cases on w vs z_prec
          by_cases hwzp : w ⊥ z_prec
          · -- w ⊥ z_prec: IsWeakN w z_prec z_min w_prec
            exact Or.inl ⟨w, z_prec, z_min, w_prec, hwz, hcov_pz, hwp, hwzp, hzw_prec⟩
          · simp only [perp_iff, not_and_or, not_not] at hwzp
            rcases hwzp with hwzp | hzpw
            · -- w ≤ z_prec, hence w < z_prec (w = z_prec contradicts x ⊥ w via x < z_prec)
              have hwlt : w < z_prec := hwzp.lt_of_ne
                (fun h => absurd (h ▸ hxzp).le hxw.1)
              -- IsX w x y w_prec z_prec
              exact Or.inr ⟨w, x, y, w_prec, z_prec, hwlt, hzpz.trans hzy,
                hxzp, hwp, ⟨hxw.2, hxw.1⟩, hywp⟩
            · -- z_prec ≤ w: x < z_prec ≤ w contradicts x ⊥ w
              exact absurd (hxzp.trans_le hzpw).le hxw.1
        · simp only [perp_iff, not_and_or, not_not] at hzw_prec
          rcases hzw_prec with hzw | hwz'
          · -- z_min ≤ w_prec: strengthen to z_min < w_prec
            -- (z_min = w_prec gives w_prec ≤ y contradicting hywp)
            have hlt : z_min < w_prec := hzw.lt_of_ne
              (fun heq => absurd (heq ▸ hzy).le hywp.2)
            -- IsX w x y w_prec z_min
            exact Or.inr ⟨w, x, y, w_prec, z_min, hwz, hzy, hxz, hlt,
              ⟨hxw.2, hxw.1⟩, hywp⟩
          · -- w_prec ≤ z_min: w_prec ≤ z_min < y contradicts y ⊥ w_prec
            exact absurd (hwz'.trans_lt hzy).le hywp.2

/-! ## Main theorem -/

/-- Main theorem: for a finite poset P, the following are equivalent:
    (a) P contains no weak N and no X
    (b) P has a compatible incomparability orthoset -/
theorem compatible_iff_no_weakN_no_X [Finite P] :
    IsCompatible P ↔
    (¬ ∃ a b c d : P, IsWeakN a b c d) ∧
    (¬ ∃ a b c d m : P, IsX a b c d m) := by
  constructor
  · -- (b) → (a): compatible implies no weak N and no X
    intro hcomp
    exact ⟨fun ⟨a, b, c, d, hw⟩ => not_compatible_if_weakN a b c d hw hcomp,
           fun ⟨a, b, c, d, m, hx⟩ => not_compatible_if_X a b c d m hx hcomp⟩
  · -- (a) → (b): no weak N and no X implies compatible
    intro ⟨hnoN, hnoX⟩
    by_contra hnotcomp
    unfold IsCompatible at hnotcomp
    push Not at hnotcomp
    obtain ⟨x, y, hxy_comp, hfall⟩ := hnotcomp
    have hne : x ≠ y := fun heq => hfall x (heq ▸ (Set.union_self _).subset)
    simp only [perp_iff, not_and_or, not_not] at hxy_comp
    rcases hxy_comp with hle | hle
    · obtain ⟨a, d, hVW⟩ := veryWeakN_aux x y (hle.lt_of_ne hne) hfall
      rcases weakN_or_X_of_veryWeakN hVW hfall with ⟨_, _, _, _, hw⟩ | ⟨_, _, _, _, _, hx⟩
      · exact hnoN ⟨_, _, _, _, hw⟩
      · exact hnoX ⟨_, _, _, _, _, hx⟩
    · obtain ⟨a, d, hVW⟩ := veryWeakN_aux y x (hle.lt_of_ne (Ne.symm hne))
        (fun z hz => hfall z (Set.union_comm _ _ ▸ hz))
      rcases weakN_or_X_of_veryWeakN hVW (fun z hz => hfall z (Set.union_comm _ _ ▸ hz))
        with ⟨_, _, _, _, hw⟩ | ⟨_, _, _, _, _, hx⟩
      · exact hnoN ⟨_, _, _, _, hw⟩
      · exact hnoX ⟨_, _, _, _, _, hx⟩
