/-
  Sylvester-Gallai Theorem

  Given a finite set of points in the Euclidean plane, not all collinear,
  there exists a line passing through exactly two of the points.

  This uses Kelly's proof via an extremal argument: consider all pairs (p, L)
  where L is a line through at least 2 points and p is a point not on L.
  Pick the pair minimizing distance from p to L. Then L is ordinary.
-/
import Mathlib
import Proofs.AreaProof

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

-- Plane and lineThrough are imported from Proofs.AreaProof

/-- A line in the plane is an affine subspace of dimension 1 -/
def IsLine (L : AffineSubspace ℝ Plane) : Prop :=
  Module.finrank ℝ L.direction = 1

/-- A line through a finite set S is ordinary if it contains exactly 2 points of S -/
def IsOrdinaryLine (S : Finset Plane) (L : AffineSubspace ℝ Plane) : Prop :=
  IsLine L ∧ (S.filter (· ∈ L)).card = 2

/-- Distance from a point to an affine subspace -/
def distToSubspace (p : Plane) (L : AffineSubspace ℝ Plane) : ℝ :=
  Metric.infDist p L

/-- The set of lines determined by pairs of points in S -/
def linesOf (S : Finset Plane) : Set (AffineSubspace ℝ Plane) :=
  {L | ∃ p q : Plane, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ L = lineThrough p q}

/-- Configuration: a point not on a line, with both from S -/
structure PointLinePair (S : Finset Plane) where
  point : Plane
  line : AffineSubspace ℝ Plane
  point_in_S : point ∈ S
  line_in_lines : line ∈ linesOf S
  point_not_on_line : point ∉ line

/-- Three points not collinear implies one is not on the line through the other two -/
lemma not_collinear_imp_not_mem_affineSpan {a b c : Plane} :
    ¬Collinear ℝ ({a, b, c} : Set Plane) → c ∉ affineSpan ℝ ({a, b} : Set Plane) := by
  intro h hc
  apply h
  -- c ∈ affineSpan ℝ {a, b} implies {a, b, c} collinear
  have : ({a, b, c} : Set Plane) = insert c ({a, b} : Set Plane) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      rcases hx with rfl | rfl | rfl
      · right; left; rfl
      · right; right; rfl
      · left; rfl
    · intro hx
      rcases hx with rfl | rfl | rfl
      · right; right; rfl
      · left; rfl
      · right; left; rfl
  rw [this]
  exact collinear_insert_iff_of_mem_affineSpan hc |>.mpr (collinear_pair ℝ a b)

/-- If all triples in S are collinear, then S is collinear -/
lemma collinear_of_all_triples_collinear {S : Finset Plane} (h_card : 2 < S.card)
    (h_all_col : ∀ a b c : Plane, a ∈ S → b ∈ S → c ∈ S → a ≠ b → a ≠ c → b ≠ c →
      Collinear ℝ ({a, b, c} : Set Plane)) :
    Collinear ℝ (S : Set Plane) := by
  -- Get two distinct points a, b from S
  rw [Finset.two_lt_card] at h_card
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := h_card
  -- Every point x in S lies on line(a,b) because {a,b,x} is collinear
  rw [collinear_iff_of_mem (Finset.mem_coe.mpr ha)]
  -- The direction is (b - a)
  use b -ᵥ a
  intro x hx
  by_cases hxa : x = a
  · exact ⟨0, by simp [hxa]⟩
  · by_cases hxb : x = b
    · exact ⟨1, by simp [hxb]⟩
    · -- x ≠ a and x ≠ b, so {a,b,x} is a distinct triple, hence collinear
      have h_col_abx : Collinear ℝ ({a, b, x} : Set Plane) :=
        h_all_col a b x ha hb (Finset.mem_coe.mp hx) hab (Ne.symm hxa) (Ne.symm hxb)
      -- x is on the line through a,b
      rw [collinear_iff_of_mem (Set.mem_insert a {b, x})] at h_col_abx
      obtain ⟨v, hv⟩ := h_col_abx
      -- Get the scalar for b
      obtain ⟨rb, hrb⟩ := hv b (Set.mem_insert_of_mem a (Set.mem_insert b {x}))
      -- Get the scalar for x
      obtain ⟨rx, hrx⟩ := hv x (Set.mem_insert_of_mem a (Set.mem_insert_of_mem b (Set.mem_singleton x)))
      -- v is parallel to (b - a), so we can express x in terms of (b - a)
      by_cases hv0 : v = 0
      · -- If v = 0, then b = a, contradiction
        simp [hv0] at hrb
        exact absurd hrb.symm hab
      · -- v ≠ 0, so rb ≠ 0 (since b ≠ a)
        have hrb_ne : rb ≠ 0 := by
          intro hrb0
          simp [hrb0] at hrb
          exact hab hrb.symm
        -- v = (1/rb) • (b -ᵥ a)
        have hv_eq : v = rb⁻¹ • (b -ᵥ a) := by
          have h1 : rb • v = b -ᵥ a := by
            have h2 : rb • v +ᵥ a = b := hrb.symm
            have h3 : rb • v = b -ᵥ a := by
              rw [← h2]
              simp only [vadd_vsub_assoc, vsub_self, add_zero]
            exact h3
          rw [← h1, smul_smul, inv_mul_cancel₀ hrb_ne, one_smul]
        -- x = rx • v +ᵥ a = rx • (rb⁻¹ • (b -ᵥ a)) +ᵥ a = (rx/rb) • (b -ᵥ a) +ᵥ a
        use rx * rb⁻¹
        rw [hrx, hv_eq, smul_smul]

/-- If S is not collinear, there exist 3 points in S that are not collinear -/
lemma exists_not_collinear_triple {S : Finset Plane} (h_card : 2 < S.card)
    (h_not_col : ¬Collinear ℝ (S : Set Plane)) :
    ∃ a b c : Plane, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ¬Collinear ℝ ({a, b, c} : Set Plane) := by
  -- Contrapositive: if all triples are collinear, S is collinear
  by_contra h_no_triple
  push_neg at h_no_triple
  -- h_no_triple : ∀ a b c, a ∈ S → b ∈ S → c ∈ S → a ≠ b → a ≠ c → b ≠ c → Collinear ℝ {a, b, c}
  apply h_not_col
  apply collinear_of_all_triples_collinear h_card
  exact h_no_triple

/-- The set of all (point, line) configurations where point ∉ line -/
def Configurations (S : Finset Plane) : Set (Plane × AffineSubspace ℝ Plane) :=
  {pl | pl.1 ∈ S ∧ pl.2 ∈ linesOf S ∧ pl.1 ∉ pl.2}

/-- Distance function for configurations -/
def configDist (pl : Plane × AffineSubspace ℝ Plane) : ℝ :=
  Metric.infDist pl.1 pl.2

/-- The direction of affineSpan {a, b} has dimension 1 when a ≠ b -/
lemma finrank_direction_lineThrough {a b : Plane} (hab : a ≠ b) :
    Module.finrank ℝ (lineThrough a b).direction = 1 := by
  unfold lineThrough
  -- The direction of affineSpan equals vectorSpan
  rw [direction_affineSpan]
  -- Two distinct points are affinely independent
  have h_indep : AffineIndependent ℝ ![a, b] := affineIndependent_of_ne ℝ hab
  -- For 2 affinely independent points, vectorSpan has finrank 1
  have h_range : Set.range ![a, b] = {a, b} := by
    simp only [Matrix.range_cons_cons_empty]
  -- Use the finrank lemma: card = 2 = 1 + 1 implies finrank = 1
  have h_card : Fintype.card (Fin 2) = 1 + 1 := rfl
  have h_finrank := AffineIndependent.finrank_vectorSpan h_indep h_card
  rw [h_range] at h_finrank
  exact h_finrank

/-- Two affine subspaces through two common distinct points are equal -/
lemma affineSpan_eq_of_two_mem {a b : Plane} {L : AffineSubspace ℝ Plane}
    (hab : a ≠ b) (ha : a ∈ L) (hb : b ∈ L) : lineThrough a b ≤ L := by
  apply affineSpan_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> assumption

/-- If b, c are in L and b is also in lineThrough p c, then lineThrough p c ≤ L -/
lemma line_subset_of_two_common {p b c : Plane} {L : AffineSubspace ℝ Plane}
    (hbc : b ≠ c) (hb_L : b ∈ L) (hc_L : c ∈ L) (hb_pc : b ∈ lineThrough p c) :
    lineThrough p c ≤ L := by
  -- b and c are both in lineThrough p c, so lineThrough b c ≤ lineThrough p c
  have hc_pc : c ∈ lineThrough p c := right_mem_affineSpan_pair ℝ p c
  have h1 : lineThrough b c ≤ lineThrough p c := affineSpan_eq_of_two_mem hbc hb_pc hc_pc
  -- lineThrough b c ≤ L (since b, c ∈ L)
  have h2 : lineThrough b c ≤ L := affineSpan_eq_of_two_mem hbc hb_L hc_L
  -- Show p ∈ lineThrough b c using collinearity
  have hp_bc : p ∈ lineThrough b c := by
    -- Since b ∈ lineThrough p c = affineSpan {p, c}, we have {b, p, c} collinear
    have h_col : Collinear ℝ ({b, p, c} : Set Plane) := collinear_insert_of_mem_affineSpan_pair hb_pc
    -- {p, b, c} = {b, p, c} so also collinear
    have h_col' : Collinear ℝ ({p, b, c} : Set Plane) := by
      convert h_col using 1
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    -- Since {p, b, c} collinear and b ≠ c, affineSpan {b, c} = affineSpan {p, b, c}
    have h_span_eq : affineSpan ℝ ({b, c} : Set Plane) = affineSpan ℝ ({p, b, c} : Set Plane) :=
      Collinear.affineSpan_eq_of_ne h_col'
        (Set.mem_insert_of_mem p (Set.mem_insert b {c}))
        (Set.mem_insert_of_mem p (Set.mem_insert_of_mem b (Set.mem_singleton c)))
        hbc
    -- p ∈ affineSpan {p, b, c}
    have hp_pbc : p ∈ affineSpan ℝ ({p, b, c} : Set Plane) :=
      subset_affineSpan ℝ _ (Set.mem_insert p {b, c})
    -- Therefore p ∈ affineSpan {b, c} = lineThrough b c
    unfold lineThrough
    rw [h_span_eq]
    exact hp_pbc
  -- p ∈ lineThrough b c and c ∈ lineThrough b c, so lineThrough p c ≤ lineThrough b c
  have hpc_ne : p ≠ c := fun h => by subst h; simp [lineThrough] at hb_pc; exact hbc hb_pc
  calc lineThrough p c ≤ lineThrough b c :=
        affineSpan_eq_of_two_mem hpc_ne hp_bc (right_mem_affineSpan_pair ℝ b c)
    _ ≤ L := h2

/-- Points in an affine subspace of dimension ≤ 1 are collinear -/
lemma collinear_of_mem_affineSubspace_finrank_le_one {L : AffineSubspace ℝ Plane}
    [Nonempty L] [FiniteDimensional ℝ L.direction]
    (h_dim : Module.finrank ℝ L.direction ≤ 1) {x y z : Plane}
    (hx : x ∈ L) (hy : y ∈ L) (hz : z ∈ L) :
    Collinear ℝ ({x, y, z} : Set Plane) := by
  have h_sub : ({x, y, z} : Set Plane) ⊆ (L : Set Plane) := by
    intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> assumption
  have h_dir : vectorSpan ℝ ({x, y, z} : Set Plane) ≤ L.direction := by
    rw [AffineSubspace.direction_eq_vectorSpan]
    exact vectorSpan_mono ℝ h_sub
  have h_finrank : Module.finrank ℝ (vectorSpan ℝ ({x, y, z} : Set Plane)) ≤ 1 :=
    calc Module.finrank ℝ (vectorSpan ℝ ({x, y, z} : Set Plane))
        ≤ Module.finrank ℝ L.direction := Submodule.finrank_mono h_dir
      _ ≤ 1 := h_dim
  exact collinear_iff_finrank_le_one.mpr h_finrank

-- cross2D is imported from Proofs.AreaProof

/-- The perpendicular distance from a point to a line through two other points
    equals |cross(q-p, r-p)| / dist(p, q) in 2D.
    This is the standard formula: area of parallelogram / base = height -/
lemma infDist_eq_cross_div_dist {p q r : Plane} (hpq : p ≠ q) :
    Metric.infDist r (lineThrough p q : Set Plane) =
    |cross2D (q -ᵥ p) (r -ᵥ p)| / dist p q := by
  -- Standard perpendicular distance formula via cross product
  -- The infDist to a line equals distance to orthogonal projection
  -- which equals |cross product| / |base| by Lagrange identity

  haveI : Nonempty (lineThrough p q) := ⟨⟨p, left_mem_affineSpan_pair ℝ p q⟩⟩
  haveI : FiniteDimensional ℝ (lineThrough p q).direction := inferInstance
  haveI : (lineThrough p q).direction.HasOrthogonalProjection := inferInstance

  -- Set up coordinates: let d = q - p be the direction, v = r - p be the vector to r
  set d : Plane := q -ᵥ p with hd_def
  set v : Plane := r -ᵥ p with hv_def

  have hd_ne : d ≠ 0 := vsub_ne_zero.mpr hpq.symm
  have hd_norm_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
  have hdist_eq : dist p q = ‖d‖ := by
    rw [hd_def]
    simp only [dist_eq_norm, vsub_eq_sub, norm_sub_rev]

  -- The orthogonal projection of r onto line(p,q)
  let F : Plane := ↑(EuclideanGeometry.orthogonalProjection (lineThrough p q) r)

  -- infDist r (line) = dist r F
  have h_infDist_eq : Metric.infDist r (lineThrough p q : Set Plane) = dist r F :=
    (EuclideanGeometry.dist_orthogonalProjection_eq_infDist (lineThrough p q) r).symm

  rw [h_infDist_eq, hdist_eq]

  -- The orthogonal projection satisfies:
  -- F = p + (⟨v, d⟩ / ‖d‖²) • d
  -- So r - F = v - (⟨v, d⟩ / ‖d‖²) • d
  -- And ‖r - F‖² = ‖v‖² - ⟨v, d⟩² / ‖d‖² (by Pythagoras)
  -- By Lagrange: cross² = ‖d‖² ‖v‖² - ⟨d,v⟩²
  -- So ‖r - F‖² = cross² / ‖d‖², hence ‖r - F‖ = |cross| / ‖d‖

  -- Use orthogonalProjection_singleton to express F explicitly
  -- F = p + orthogonalProjection (ℝ ∙ d) v
  -- The orthogonal projection of v onto span{d} is (⟨v,d⟩/‖d‖²) • d

  -- The perpendicular distance from r to line through p,q equals |cross2D d v| / ‖d‖
  -- where d = q - p and v = r - p
  -- This is a well-known geometric formula: area/base = height
  -- The area of the parallelogram with sides d and v is |cross2D d v|
  -- The height (perpendicular distance) is |cross2D d v| / ‖d‖

  have h_proj_formula : dist r F = |cross2D d v| / ‖d‖ := by
    -- Step 1: The direction of lineThrough p q is ℝ ∙ d (up to sign)
    have h_dir : (lineThrough p q).direction = ℝ ∙ (p -ᵥ q) := by
      unfold lineThrough
      rw [direction_affineSpan, vectorSpan_pair]
    have h_neg_d : (p -ᵥ q : Plane) = -d := by
      rw [hd_def]; simp only [neg_vsub_eq_vsub_rev]
    have h_span_neg : (ℝ ∙ (-d) : Submodule ℝ Plane) = ℝ ∙ d := by
      rw [show ({-d} : Set Plane) = -{d} by simp only [Set.neg_singleton]]
      exact Submodule.span_neg {d}
    have h_dir' : (lineThrough p q).direction = ℝ ∙ d := by
      rw [h_dir, h_neg_d, h_span_neg]

    -- Step 2: Express F using orthogonalProjection_apply_mem
    have hp_mem : p ∈ lineThrough p q := left_mem_affineSpan_pair ℝ p q

    -- Step 3: F = p + proj_direction(v)
    have h_F_eq' : (F : Plane) =
        ↑((lineThrough p q).direction.orthogonalProjection (r -ᵥ p)) +ᵥ p :=
      EuclideanGeometry.orthogonalProjection_apply_mem (lineThrough p q) hp_mem

    -- Define the projection coefficient
    have hd_sq_pos : 0 < ‖d‖^2 := sq_pos_of_pos hd_norm_pos
    set t := inner (𝕜 := ℝ) d v / ‖d‖ ^ 2 with ht_def

    -- The projection onto ℝ ∙ d is t • d (by starProjection_singleton)
    have h_proj_formula_d : (ℝ ∙ d).starProjection v = t • d := by
      simp only [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq, ht_def]

    -- The perpendicular component
    set perp := v - t • d with hperp_def

    -- Key: ‖perp‖² = ‖v‖² - (inner d v)² / ‖d‖² using Pythagorean theorem
    have h_pythag : ‖perp‖^2 = ‖v‖^2 - (inner (𝕜 := ℝ) d v)^2 / ‖d‖^2 := by
      rw [hperp_def]
      -- Use norm_sub_sq: ‖x - y‖² = ‖x‖² - 2 * re⟨x,y⟩ + ‖y‖²
      rw [norm_sub_sq (𝕜 := ℝ)]
      simp only [RCLike.re_to_real]
      -- ⟨v, t • d⟩ = t * ⟨v, d⟩ (for reals, conj = id)
      rw [real_inner_smul_right]
      -- ‖t • d‖ = |t| * ‖d‖
      rw [norm_smul, Real.norm_eq_abs]
      -- Simplify (|t| * ‖d‖)² = t² * ‖d‖² since |t|² = t²
      have h_abs_sq : (|t| * ‖d‖)^2 = t^2 * ‖d‖^2 := by
        rw [mul_pow, sq_abs]
      rw [h_abs_sq]
      -- Simplify with t = ⟨d,v⟩/‖d‖²
      rw [ht_def, real_inner_comm d v]
      have hd2_ne : ‖d‖^2 ≠ 0 := ne_of_gt hd_sq_pos
      field_simp
      ring

    -- By Lagrange identity: cross² + inner² = ‖d‖² * ‖v‖²
    have h_lagrange := cross2D_sq_add_inner_sq d v
    have h_cross_sq : (cross2D d v)^2 = ‖d‖^2 * ‖v‖^2 - (inner (𝕜 := ℝ) d v)^2 := by
      linarith

    -- So ‖perp‖² = cross² / ‖d‖²
    have h_perp_sq : ‖perp‖^2 = (cross2D d v)^2 / ‖d‖^2 := by
      rw [h_pythag, h_cross_sq]
      have hd2_ne : ‖d‖^2 ≠ 0 := ne_of_gt hd_sq_pos
      field_simp

    -- Therefore ‖perp‖ = |cross2D d v| / ‖d‖
    have h_perp_nonneg : 0 ≤ ‖perp‖ := norm_nonneg _
    have h_cross_div_nonneg : 0 ≤ |cross2D d v| / ‖d‖ :=
      div_nonneg (abs_nonneg _) (le_of_lt hd_norm_pos)
    have h_norm_perp : ‖perp‖ = |cross2D d v| / ‖d‖ := by
      have h_sq_eq : ‖perp‖^2 = (|cross2D d v| / ‖d‖)^2 := by
        rw [h_perp_sq, div_pow, sq_abs]
      exact sq_eq_sq₀ h_perp_nonneg h_cross_div_nonneg |>.mp h_sq_eq

    -- F = p + t • d (projection formula) using submodule equality
    have h_F_val : (F : Plane) = t • d +ᵥ p := by
      -- First prove the projection equals t • d as Plane vectors
      have h_proj_eq : ((lineThrough p q).direction.orthogonalProjection (r -ᵥ p) : Plane) = t • d := by
        rw [Submodule.coe_orthogonalProjection_apply, ← hv_def]
        -- simp handles dependent type rewrites better
        simp only [h_dir', h_proj_formula_d]
      -- Use show to make the coercion explicit, then rewrite
      rw [h_F_eq']
      show (↑((lineThrough p q).direction.orthogonalProjection (r -ᵥ p)) : Plane) +ᵥ p = t • d +ᵥ p
      rw [h_proj_eq]

    -- dist r F = ‖r - F‖ = ‖(r - p) - t • d‖ = ‖v - t • d‖ = ‖perp‖
    calc dist r F = ‖r - F‖ := dist_eq_norm r F
      _ = ‖r - (t • d +ᵥ p)‖ := by rw [h_F_val]
      _ = ‖(r - p) - t • d‖ := by congr 1; simp only [vadd_eq_add]; abel
      _ = ‖v - t • d‖ := by rw [hv_def]; simp only [vsub_eq_sub]
      _ = ‖perp‖ := by rw [hperp_def]
      _ = |cross2D d v| / ‖d‖ := h_norm_perp

  exact h_proj_formula

/-- Area formula: for collinear x, z and p off their line,
    the perpendicular distance from x to line(p, z) equals
    dist(x, z) * h / dist(p, z) where h is the height of p above line xz. -/
lemma area_formula_perp_dist {p x z : Plane} {L : AffineSubspace ℝ Plane}
    (hx : x ∈ L) (hz : z ∈ L) (hp_off : p ∉ L) (hxz : x ≠ z)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection]
    (h_dim : Module.finrank ℝ L.direction = 1) :
    Metric.infDist x (lineThrough p z : Set Plane) =
    dist x z * Metric.infDist p L / dist p z := by
  -- The area of triangle pxz can be computed two ways using the cross product:
  -- |cross2D (z -ᵥ x) (p -ᵥ x)| = dist(x, z) * infDist(p, line xz)
  -- |cross2D (z -ᵥ p) (x -ᵥ p)| = dist(p, z) * infDist(x, line pz)
  -- By abs_cross2D_triangle, these cross products have equal absolute value
  -- Therefore: dist(x, z) * infDist(p, L) = dist(p, z) * infDist(x, line pz)
  -- So: infDist(x, line pz) = dist(x, z) * infDist(p, L) / dist(p, z)

  have hp_ne_z : p ≠ z := fun h => hp_off (h ▸ hz)
  have hpz_pos : 0 < dist p z := dist_pos.mpr hp_ne_z
  have hxz_pos : 0 < dist x z := dist_pos.mpr hxz

  -- lineThrough x z = L (since L is 1-dimensional and contains x ≠ z)
  -- Both subspaces are 1-dimensional and share two distinct points x, z
  have h_line_eq : lineThrough x z = L := by
    unfold lineThrough
    apply le_antisymm
    · exact affineSpan_eq_of_two_mem hxz hx hz
    · -- L ≤ affineSpan {x, z} by dimension argument
      -- The affine span of {x,z} has dimension 1, same as L
      -- Both contain x, so they must be equal
      have h_dir_xz : Module.finrank ℝ (affineSpan ℝ ({x, z} : Set Plane)).direction = 1 := by
        rw [direction_affineSpan]
        have h_indep : AffineIndependent ℝ ![x, z] := affineIndependent_of_ne ℝ hxz
        have h_range : Set.range ![x, z] = {x, z} := by ext; simp [Set.mem_insert_iff]; tauto
        have h_finrank := AffineIndependent.finrank_vectorSpan h_indep
          (show Fintype.card (Fin 2) = 1 + 1 from rfl)
        rw [h_range] at h_finrank
        exact h_finrank
      have h_le : affineSpan ℝ ({x, z} : Set Plane) ≤ L := by
        apply affineSpan_le.mpr
        intro p' hp'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp'
        rcases hp' with rfl | rfl <;> assumption
      have h_dir_le : (affineSpan ℝ ({x, z} : Set Plane)).direction ≤ L.direction :=
        AffineSubspace.direction_le h_le
      have h_dir_eq : (affineSpan ℝ ({x, z} : Set Plane)).direction = L.direction := by
        apply Submodule.eq_of_le_of_finrank_eq h_dir_le
        rw [h_dir_xz, h_dim]
      have hx_in_xz : x ∈ affineSpan ℝ ({x, z} : Set Plane) :=
        subset_affineSpan ℝ _ (Set.mem_insert x {z})
      have h_eq : affineSpan ℝ ({x, z} : Set Plane) = L :=
        AffineSubspace.eq_iff_direction_eq_of_mem hx_in_xz hx |>.mpr h_dir_eq
      exact h_eq.symm.le

  -- Use the cross product formulas
  have h1 : Metric.infDist x (lineThrough p z : Set Plane) =
      |cross2D (z -ᵥ p) (x -ᵥ p)| / dist p z := infDist_eq_cross_div_dist hp_ne_z

  have h2 : Metric.infDist p (lineThrough x z : Set Plane) =
      |cross2D (z -ᵥ x) (p -ᵥ x)| / dist x z := infDist_eq_cross_div_dist hxz

  -- The key: |cross2D (z -ᵥ x) (p -ᵥ x)| = |cross2D (z -ᵥ p) (x -ᵥ p)|
  have h_cross_eq : |cross2D (z -ᵥ x) (p -ᵥ x)| = |cross2D (z -ᵥ p) (x -ᵥ p)| :=
    abs_cross2D_triangle p x z

  -- infDist p L = infDist p (lineThrough x z)
  have h_infDist_eq : Metric.infDist p L = Metric.infDist p (lineThrough x z : Set Plane) := by
    rw [h_line_eq]

  rw [h1, h_infDist_eq, h2, h_cross_eq]
  have h3 : dist p z ≠ 0 := ne_of_gt hpz_pos
  have h4 : dist x z ≠ 0 := ne_of_gt hxz_pos
  field_simp

/-- Key helper: segment intersection - if Wbtw a b c and F is in both [b,a] and [c,b], then F = b -/
lemma wbtw_segment_intersection {a b c F : Plane}
    (h_abc : Wbtw ℝ a b c) (h_bFa : Wbtw ℝ b F a) (h_cFb : Wbtw ℝ c F b) : F = b := by
  have d_abc := Wbtw.dist_add_dist h_abc
  have d_bFa := Wbtw.dist_add_dist h_bFa
  have d_cFb := Wbtw.dist_add_dist h_cFb
  have h_tri : dist a c ≤ dist a F + dist F c := dist_triangle a F c
  have h_Fb_zero : dist F b = 0 := by
    have h1 : dist F a = dist a b - dist F b := by
      have : dist b F + dist F a = dist b a := d_bFa
      rw [dist_comm b F, dist_comm b a] at this
      linarith
    have h2 : dist F c = dist b c - dist F b := by
      have : dist c F + dist F b = dist c b := d_cFb
      rw [dist_comm c F, dist_comm c b] at this
      linarith
    rw [dist_comm a F, h1, h2] at h_tri
    linarith [dist_nonneg (x := F) (y := b)]
  exact dist_eq_zero.mp h_Fb_zero

/-- Key helper: Pythagorean theorem for orthogonal projection -/
lemma pythag_proj {L : AffineSubspace ℝ Plane} {p t : Plane}
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection]
    (ht : t ∈ L) :
    let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
    dist t p ^ 2 = dist t F ^ 2 + dist p F ^ 2 := by
  intro F
  have h := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    (s := L) p ht
  simp only [sq] at h ⊢
  convert h using 1

/-- Key helper: projection distance is strictly less -/
lemma dist_proj_lt {L : AffineSubspace ℝ Plane} {p t : Plane}
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection]
    (ht : t ∈ L) (hp_off : p ∉ L) :
    dist (↑(EuclideanGeometry.orthogonalProjection L p) : Plane) t < dist p t := by
  set F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p) with hF_def
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p
  have h_pF_pos : 0 < dist p F := dist_pos.mpr (fun hpF => hp_off (hpF ▸ hF_mem))
  have h_pythag : dist p t ^ 2 = dist F t ^ 2 + dist p F ^ 2 := by
    have h := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
      (s := L) p ht
    simp only [sq] at h ⊢
    calc dist p t * dist p t = dist t p * dist t p := by rw [dist_comm]
      _ = dist t F * dist t F + dist p F * dist p F := h
      _ = dist F t * dist F t + dist p F * dist p F := by rw [dist_comm t F]
  have h_pt_pos : 0 < dist p t := dist_pos.mpr (fun hpt => hp_off (hpt ▸ ht))
  nlinarith [sq_nonneg (dist F t), sq_pos_of_pos h_pF_pos, sq_pos_of_pos h_pt_pos]

set_option maxHeartbeats 800000 in
/-- Among 3 distinct points on L and p off L, there exists a pair (x, z) with dist(x,z) < dist(p,z).
    This is because by pigeonhole, 2 points are on same side of foot F, and the closer one to F
    gives dist(x,z) ≤ dist(F,z) < dist(p,z) by Pythagorean. -/
lemma exists_pair_close {a b c p : Plane} {L : AffineSubspace ℝ Plane}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hp_off : p ∉ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h_dim : Module.finrank ℝ L.direction ≤ 1)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection] :
    ∃ x z, x ∈ ({a, b, c} : Set Plane) ∧ z ∈ ({a, b, c} : Set Plane) ∧ x ≠ z ∧
      dist x z < dist p z := by
  let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p

  -- Helper for set membership proofs
  have ha_mem : a ∈ ({a, b, c} : Set Plane) := by simp
  have hb_mem : b ∈ ({a, b, c} : Set Plane) := by simp
  have hc_mem : c ∈ ({a, b, c} : Set Plane) := by simp

  -- Key distance inequality: dist(F, t) < dist(p, t) for any t ∈ L
  have h_dist_proj : ∀ t ∈ L, dist F t < dist p t := fun t ht => dist_proj_lt ht hp_off

  -- Case: Is F equal to one of a, b, c?
  by_cases haF : a = F
  · -- a = F: use dist(a, b) < dist(p, b)
    use a, b
    refine ⟨ha_mem, hb_mem, hab, ?_⟩
    rw [haF]
    exact h_dist_proj b hb
  · by_cases hbF : b = F
    · use b, a
      refine ⟨hb_mem, ha_mem, hab.symm, ?_⟩
      rw [hbF]
      exact h_dist_proj a ha
    · by_cases hcF : c = F
      · use c, a
        refine ⟨hc_mem, ha_mem, hac.symm, ?_⟩
        rw [hcF]
        exact h_dist_proj a ha
      · -- None equal F: use Wbtw analysis
        -- {F, a, b, c} are 4 distinct collinear points on L
        -- Among {F, a, b}, one is between the other two
        have h_col_Fab : Collinear ℝ ({F, a, b} : Set Plane) :=
          collinear_of_mem_affineSubspace_finrank_le_one h_dim hF_mem ha hb
        have h_btw_Fab := Collinear.wbtw_or_wbtw_or_wbtw h_col_Fab
        rcases h_btw_Fab with h | h | h
        · -- Wbtw ℝ F a b: a between F and b → dist(a, b) ≤ dist(F, b) < dist(p, b)
          use a, b
          refine ⟨ha_mem, hb_mem, hab, ?_⟩
          have h_ab_le : dist a b ≤ dist F b := by
            have h_sum := Wbtw.dist_add_dist h
            linarith [dist_nonneg (x := F) (y := a)]
          exact lt_of_le_of_lt h_ab_le (h_dist_proj b hb)
        · -- Wbtw ℝ a b F: b between a and F → dist(a, b) ≤ dist(a, F) = dist(F, a) < dist(p, a)
          use b, a
          refine ⟨hb_mem, ha_mem, hab.symm, ?_⟩
          have h_ab_le : dist a b ≤ dist a F := by
            have h_sum := Wbtw.dist_add_dist h
            linarith [dist_nonneg (x := b) (y := F)]
          rw [dist_comm a b, dist_comm a F] at h_ab_le
          exact lt_of_le_of_lt h_ab_le (h_dist_proj a ha)
        · -- Wbtw ℝ b F a: F between b and a → b and a on opposite sides
          -- Check {F, a, c} or {F, b, c}
          have h_col_Fac : Collinear ℝ ({F, a, c} : Set Plane) :=
            collinear_of_mem_affineSubspace_finrank_le_one h_dim hF_mem ha hc
          have h_btw_Fac := Collinear.wbtw_or_wbtw_or_wbtw h_col_Fac
          rcases h_btw_Fac with h' | h' | h'
          · -- Wbtw ℝ F a c: a between F and c
            use a, c
            refine ⟨ha_mem, hc_mem, hac, ?_⟩
            have h_ac_le : dist a c ≤ dist F c := by
              have h_sum := Wbtw.dist_add_dist h'
              linarith [dist_nonneg (x := F) (y := a)]
            exact lt_of_le_of_lt h_ac_le (h_dist_proj c hc)
          · -- Wbtw ℝ a c F: c between a and F
            use c, a
            refine ⟨hc_mem, ha_mem, hac.symm, ?_⟩
            have h_ac_le : dist a c ≤ dist a F := by
              have h_sum := Wbtw.dist_add_dist h'
              linarith [dist_nonneg (x := c) (y := F)]
            rw [dist_comm a c, dist_comm a F] at h_ac_le
            exact lt_of_le_of_lt h_ac_le (h_dist_proj a ha)
          · -- Wbtw ℝ c F a: F between c and a → c and a on opposite sides
            -- Combined with b - F - a: b and a on opposite sides, c and a on opposite sides
            -- So b and c are on the same side of F
            have h_col_Fbc : Collinear ℝ ({F, b, c} : Set Plane) :=
              collinear_of_mem_affineSubspace_finrank_le_one h_dim hF_mem hb hc
            have h_btw_Fbc := Collinear.wbtw_or_wbtw_or_wbtw h_col_Fbc
            rcases h_btw_Fbc with h'' | h'' | h''
            · -- Wbtw ℝ F b c
              use b, c
              refine ⟨hb_mem, hc_mem, hbc, ?_⟩
              have h_bc_le : dist b c ≤ dist F c := by
                have h_sum := Wbtw.dist_add_dist h''
                linarith [dist_nonneg (x := F) (y := b)]
              exact lt_of_le_of_lt h_bc_le (h_dist_proj c hc)
            · -- Wbtw ℝ b c F
              use c, b
              refine ⟨hc_mem, hb_mem, hbc.symm, ?_⟩
              have h_bc_le : dist b c ≤ dist b F := by
                have h_sum := Wbtw.dist_add_dist h''
                linarith [dist_nonneg (x := c) (y := F)]
              rw [dist_comm b c, dist_comm b F] at h_bc_le
              exact lt_of_le_of_lt h_bc_le (h_dist_proj b hb)
            · -- Wbtw ℝ c F b: F between c and b
              -- Now we have: b - F - a, c - F - a, c - F - b
              -- This means: a is on one side, and both b, c are on the other side
              -- So {b, c} are on same side → use Wbtw on {F, b, c} rotated
              -- Actually c - F - b means F ∈ segment [c, b]
              -- Combined with b - F - a (F ∈ segment [b, a]) → a, b, c all through F?
              -- Check {a, b, c} directly
              have h_col_abc : Collinear ℝ ({a, b, c} : Set Plane) :=
                collinear_of_mem_affineSubspace_finrank_le_one h_dim ha hb hc
              have h_btw_abc := Collinear.wbtw_or_wbtw_or_wbtw h_col_abc
              rcases h_btw_abc with h3 | h3 | h3
              · -- Wbtw ℝ a b c: b between a and c
                -- dist(a, b) ≤ dist(a, c), dist(b, c) ≤ dist(a, c)
                -- Try (b, c) with dist(b, c) < dist(p, c)
                -- From c - F - b, we have dist(b, c) ≤ dist(F, c)... wait, that's Wbtw F c b or Wbtw c F b
                -- Wbtw c F b means F ∈ [c, b], so dist(c, b) = dist(c, F) + dist(F, b)
                -- This doesn't give us dist(b, c) ≤ dist(F, c) directly
                -- Let me use a different approach: find the farthest from F among {a, b, c}
                -- Actually from h (b-F-a), h' (c-F-a), h'' (c-F-b):
                -- These give: F ∈ [b,a], F ∈ [c,a], F ∈ [c,b]
                -- If F ∈ [b,a] ∩ [c,a], then F is "between" {b,c} and a
                -- And F ∈ [c,b] means F is also between c and b
                -- This implies F = intersection, which for lines means specific position
                -- The combination might be contradictory. Let me check:
                -- Wbtw b F a + Wbtw c F b should imply something about {a, b, c, F}
                -- On a line, 4 points have a linear order. If Wbtw b F a, order could be b ≤ F ≤ a
                -- If Wbtw c F b, order could be c ≤ F ≤ b
                -- Combined: c ≤ F ≤ b ≤ F ≤ a, which requires F = b. Contradiction with hbF!
                exfalso
                -- Use wbtw_segment_intersection: h3 (Wbtw a b c), h (Wbtw b F a), h'' (Wbtw c F b) → F = b
                have hFb : F = b := wbtw_segment_intersection h3 h h''
                exact hbF hFb.symm
              · -- Wbtw ℝ b c a: c between b and a
                -- h'' : Wbtw c F b (F between c and b)
                -- h3 : Wbtw b c a (c between b and a)
                -- h : Wbtw b F a (F between b and a)
                -- Order on line: b-c-a, F on [c,b] and [b,a]
                -- Since F ∈ [c,b] and F ∈ [b,a], the common point is b unless they overlap
                -- Order b-c-a with F between c,b: could be c-F-b or b-F-c
                -- F between b,a: order b-F-?-a or b-?-F-a
                -- Combined b-c-a, F ∈ [c,b], F ∈ [b,a]: F must be at b or very close
                -- Actually if b-c-a and c-F-b (from h''), then on the segment from b through c to a,
                -- F is between c and b, so F is between b and c in order.
                -- Combined with F between b and a (h): F is between b and c AND between b and a
                -- Since c is between b and a (h3), and F is on [b,c] ⊂ [b,a], F is between b and c
                -- So order: b-F-c-a (F between b and c, c between b and a)
                -- Use pair (c, a): dist(c, a) ≤ dist(F, a) < dist(p, a)
                use c, a
                refine ⟨hc_mem, ha_mem, hac.symm, ?_⟩
                -- From h3 (Wbtw b c a): dist(b, c) + dist(c, a) = dist(b, a)
                -- So dist(c, a) = dist(b, a) - dist(b, c) ≤ dist(b, a)
                -- From h (Wbtw b F a): dist(b, F) + dist(F, a) = dist(b, a)
                -- So dist(F, a) = dist(b, a) - dist(b, F)
                -- From h'' (Wbtw c F b): dist(c, F) + dist(F, b) = dist(c, b)
                -- Order b-F-c-a: dist(c, a) is part of the line from c to a
                -- dist(F, a) = dist(F, c) + dist(c, a) (since F-c-a order)
                -- So dist(c, a) < dist(F, a)
                have d_bca := Wbtw.dist_add_dist h3
                have d_bFa := Wbtw.dist_add_dist h
                have d_cFb := Wbtw.dist_add_dist h''
                have h_ca_lt : dist c a < dist F a := by
                  rw [dist_comm c b] at d_cFb
                  rw [dist_comm b F] at d_bFa
                  have hcF_pos : 0 < dist c F := dist_pos.mpr (fun heq => hcF heq)
                  linarith only [d_bca, d_bFa, d_cFb, hcF_pos, dist_nonneg (x := F) (y := b)]
                exact lt_of_lt_of_le h_ca_lt (le_of_lt (h_dist_proj a ha))
              · -- Wbtw ℝ c a b: a between c and b
                -- h3 : Wbtw c a b (a between c and b)
                -- h'' : Wbtw c F b (F between c and b)
                -- h : Wbtw b F a (F between b and a)
                -- Order c-a-b, F between c and b, F between b and a
                -- F ∈ [c,b] and F ∈ [b,a]. Since a ∈ [c,b] (from c-a-b), [b,a] ⊂ [c,b]
                -- So F ∈ [b,a] means F is between b and a (order a-F-b or b-F-a)
                -- h says Wbtw b F a, so order b-F-a
                -- Combined with c-a-b: the full order is c-a-...-b with F between a and b: c-a-F-b
                -- Use pair (a, c): dist(a, c) < dist(F, c) < dist(p, c)
                use a, c
                refine ⟨ha_mem, hc_mem, hac, ?_⟩
                have d_cab := Wbtw.dist_add_dist h3
                have d_cFb := Wbtw.dist_add_dist h''
                have d_bFa := Wbtw.dist_add_dist h
                have h_ac_lt : dist a c < dist F c := by
                  have haF_pos : 0 < dist a F := dist_pos.mpr (fun heq => haF heq)
                  -- Rewrite distances to align with goal
                  have d1 : dist F b + dist F a = dist a b := by rw [dist_comm b F, dist_comm b a] at d_bFa; exact d_bFa
                  have d2 : dist a c + dist a b = dist c b := by rw [dist_comm c a] at d_cab; exact d_cab
                  have d3 : dist c F + dist F b = dist c b := d_cFb
                  -- Goal: dist a c < dist F c
                  -- We have: dist c F + dist F b = dist c b = dist a c + dist a b
                  -- And: dist F b + dist F a = dist a b
                  -- So: dist c F + dist F b = dist a c + dist F b + dist F a
                  -- Thus: dist c F = dist a c + dist F a
                  -- And dist F c = dist c F, so dist F c = dist a c + dist F a > dist a c
                  rw [dist_comm c F] at d3
                  linarith only [d1, d2, d3, haF_pos, dist_comm a F]
                exact lt_of_lt_of_le h_ac_lt (le_of_lt (h_dist_proj c hc))

/-- Kelly's geometric inequality: given p off line L with 3+ points, some configuration is closer.
    This is the core geometric fact of Kelly's proof of Sylvester-Gallai.

    The proof uses the area formula: for x, z on L with p off L at height h,
    dist(x, line(p,z)) = dist(x,z) * h / dist(p,z).
    For this < h, we need dist(x,z) < dist(p,z), which holds when x is
    between the foot F and z on L. -/
lemma kelly_inequality {p a b c : Plane} {L : AffineSubspace ℝ Plane}
    (hp_off : p ∉ L) (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h_dim : Module.finrank ℝ L.direction ≤ 1) :
    ∃ (x : Plane) (y z : Plane), x ∈ ({a, b, c} : Set Plane) ∧ y ∈ ({a, b, c} : Set Plane) ∧
      z ∈ ({a, b, c} : Set Plane) ∧ x ≠ y ∧ y ≠ z ∧ x ∉ lineThrough p z ∧
      Metric.infDist x (lineThrough p z : Set Plane) < Metric.infDist p L := by
  -- Setup: L is finite-dimensional and has orthogonal projection
  haveI hL_ne : Nonempty L := ⟨⟨a, ha⟩⟩
  haveI hL_dir_fin : FiniteDimensional ℝ L.direction := inferInstance
  haveI hL_has_proj : L.direction.HasOrthogonalProjection := inferInstance

  -- Helper for set membership proofs
  have ha_mem : a ∈ ({a, b, c} : Set Plane) := by simp
  have hb_mem : b ∈ ({a, b, c} : Set Plane) := by simp
  have hc_mem : c ∈ ({a, b, c} : Set Plane) := by simp

  -- h = infDist(p, L) > 0 since p ∉ L
  have h_pos : 0 < Metric.infDist p L := by
    let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
    have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p
    have hpF_eq : dist p F = Metric.infDist p L :=
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist L p
    rw [← hpF_eq]
    exact dist_pos.mpr (fun hpF => hp_off (hpF ▸ hF_mem))

  -- Use exists_pair_close to get x, z with dist(x, z) < dist(p, z)
  obtain ⟨x, z, hx_mem, hz_mem, hxz_ne, hxz_lt_pz⟩ :=
    exists_pair_close ha hb hc hp_off hab hac hbc h_dim

  -- Get the membership facts for x and z
  have hx_L : x ∈ L := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx_mem
    rcases hx_mem with rfl | rfl | rfl <;> assumption
  have hz_L : z ∈ L := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz_mem
    rcases hz_mem with rfl | rfl | rfl <;> assumption

  -- Pick y as a remaining point (any point different from both x and z)
  -- Among {a, b, c}, there are 3 points and we've picked 2, so the third works
  have hy_exists : ∃ y ∈ ({a, b, c} : Set Plane), y ≠ x ∧ y ≠ z := by
    by_cases hxa : x = a
    · by_cases hza : z = a
      · exfalso; exact hxz_ne (hxa.trans hza.symm)
      · by_cases hzb : z = b
        · use c
          refine ⟨hc_mem, ?_, ?_⟩
          · intro hxc; rw [hxa] at hxc; exact hac hxc.symm
          · intro hzc; rw [hzb] at hzc; exact hbc hzc.symm
        · use b
          refine ⟨hb_mem, ?_, ?_⟩
          · intro hxb; rw [hxa] at hxb; exact hab hxb.symm
          · intro hzb'; exact hzb hzb'.symm
    · by_cases hxb : x = b
      · by_cases hzb : z = b
        · exfalso; exact hxz_ne (hxb.trans hzb.symm)
        · by_cases hza : z = a
          · use c
            refine ⟨hc_mem, ?_, ?_⟩
            · intro hxc; rw [hxb] at hxc; exact hbc hxc.symm
            · intro hzc; rw [hza] at hzc; exact hac hzc.symm
          · use a
            refine ⟨ha_mem, ?_, ?_⟩
            · intro hxa'; rw [hxb] at hxa'; exact hab hxa'
            · intro h; exact hza h.symm
      · -- x = c
        have hxc : x = c := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx_mem
          rcases hx_mem with rfl | rfl | rfl
          · exact absurd rfl hxa
          · exact absurd rfl hxb
          · rfl
        by_cases hza : z = a
        · use b
          refine ⟨hb_mem, ?_, ?_⟩
          · intro h'; rw [hxc] at h'; exact hbc h'
          · intro h'; rw [hza] at h'; exact hab h'.symm
        · use a
          refine ⟨ha_mem, ?_, ?_⟩
          · intro h'; rw [hxc] at h'; exact hac h'
          · intro h; exact hza h.symm

  obtain ⟨y, hy_mem, hyx, hyz⟩ := hy_exists

  use x, y, z
  refine ⟨hx_mem, hy_mem, hz_mem, hyx.symm, hyz, ?_, ?_⟩

  · -- x ∉ lineThrough p z
    intro hx_pz
    -- If x ∈ lineThrough p z, then {x, p, z} collinear
    have h_col : Collinear ℝ ({x, p, z} : Set Plane) := collinear_insert_of_mem_affineSpan_pair hx_pz
    -- Since {x, p, z} collinear and x ≠ z, affineSpan {x, z} = affineSpan {x, p, z}
    have h_span_eq : affineSpan ℝ ({x, z} : Set Plane) = affineSpan ℝ ({x, p, z} : Set Plane) :=
      Collinear.affineSpan_eq_of_ne h_col
        (Set.mem_insert x {p, z})
        (Set.mem_insert_of_mem x (Set.mem_insert_of_mem p (Set.mem_singleton z)))
        hxz_ne
    -- p ∈ affineSpan {x, p, z}
    have hp_xpz : p ∈ affineSpan ℝ ({x, p, z} : Set Plane) :=
      subset_affineSpan ℝ _ (Set.mem_insert_of_mem x (Set.mem_insert p {z}))
    -- So p ∈ affineSpan {x, z} = lineThrough x z
    have hp_xz : p ∈ lineThrough x z := by unfold lineThrough; rw [h_span_eq]; exact hp_xpz
    -- But lineThrough x z ≤ L (since x, z ∈ L)
    have h_sub : lineThrough x z ≤ L := affineSpan_eq_of_two_mem hxz_ne hx_L hz_L
    exact hp_off (h_sub hp_xz)

  · -- Metric.infDist x (lineThrough p z) < Metric.infDist p L
    -- Use the area formula: infDist(x, line(p,z)) = dist(x,z) * h / dist(p,z)
    have hp_ne_z : p ≠ z := fun h' => hp_off (h' ▸ hz_L)
    have hpz_pos : 0 < dist p z := dist_pos.mpr hp_ne_z

    -- L has dimension exactly 1 (two distinct points a ≠ b in L give finrank ≥ 1, combined with ≤ 1)
    have h_dim_eq : Module.finrank ℝ L.direction = 1 := by
      apply le_antisymm h_dim
      -- finrank L.direction ≥ 1 because L contains two distinct points a, b
      have h_sub : ({a, b} : Set Plane) ⊆ (L : Set Plane) := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      have h_indep : AffineIndependent ℝ ![a, b] := affineIndependent_of_ne ℝ hab
      have h_range : Set.range ![a, b] = {a, b} := by ext; simp [Set.mem_insert_iff]; tauto
      rw [← h_range] at h_sub
      have h_vs := AffineIndependent.finrank_vectorSpan h_indep (show Fintype.card (Fin 2) = 1 + 1 from rfl)
      rw [h_range] at h_vs
      have h_le : vectorSpan ℝ ({a, b} : Set Plane) ≤ L.direction := by
        rw [AffineSubspace.direction_eq_vectorSpan]
        exact vectorSpan_mono ℝ (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
      calc 1 = Module.finrank ℝ (vectorSpan ℝ ({a, b} : Set Plane)) := h_vs.symm
        _ ≤ Module.finrank ℝ L.direction := Submodule.finrank_mono h_le

    -- Apply the area formula
    have h_area := area_formula_perp_dist hx_L hz_L hp_off hxz_ne h_dim_eq

    -- The formula gives: infDist(x, line(p,z)) = dist(x,z) * h / dist(p,z)
    rw [h_area]

    -- We have dist(x, z) < dist(p, z) from exists_pair_close
    have h_div_lt : dist x z / dist p z < 1 := by
      rw [div_lt_one hpz_pos]
      exact hxz_lt_pz

    calc dist x z * Metric.infDist p L / dist p z
        = (dist x z / dist p z) * Metric.infDist p L := by ring
      _ < 1 * Metric.infDist p L := by
          apply mul_lt_mul_of_pos_right h_div_lt h_pos
      _ = Metric.infDist p L := by ring

/-- Key lemma: if L contains 3+ points of S, we can find a closer configuration -/
lemma exists_closer_if_not_ordinary {S : Finset Plane} {p : Plane} {L : AffineSubspace ℝ Plane}
    (hp : p ∈ S) (hL : L ∈ linesOf S) (hp_off : p ∉ L)
    (h_not_ord : 2 < (S.filter (· ∈ L)).card) :
    ∃ p' L', p' ∈ S ∧ L' ∈ linesOf S ∧ p' ∉ L' ∧
      configDist (p', L') < configDist (p, L) := by
  -- Extract 3 distinct points from S ∩ L
  rw [Finset.two_lt_card] at h_not_ord
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := h_not_ord
  simp only [Finset.mem_filter] at ha hb hc
  obtain ⟨ha_S, ha_L⟩ := ha
  obtain ⟨hb_S, hb_L⟩ := hb
  obtain ⟨hc_S, hc_L⟩ := hc

  haveI : Nonempty L := ⟨⟨a, ha_L⟩⟩

  -- Get dimension of L from the fact it's a lineThrough
  obtain ⟨p₁, p₂, _, _, hp₁p₂, hL_eq⟩ := hL
  have h_dim : Module.finrank ℝ L.direction ≤ 1 := by
    rw [hL_eq]
    exact le_of_eq (finrank_direction_lineThrough hp₁p₂)

  -- Use Kelly's inequality to find the right configuration
  obtain ⟨x, y, z, hx_abc, hy_abc, hz_abc, hxy, hyz, hx_off_pz, h_closer⟩ :=
    kelly_inequality hp_off ha_L hb_L hc_L hab hac hbc h_dim

  -- x is in S (since x ∈ {a,b,c} and all are in S)
  have hx_S : x ∈ S := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx_abc
    rcases hx_abc with rfl | rfl | rfl <;> assumption
  have hz_S : z ∈ S := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz_abc
    rcases hz_abc with rfl | rfl | rfl <;> assumption

  -- p ≠ z since z ∈ L and p ∉ L
  have hpz : p ≠ z := by
    intro hpz
    subst hpz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz_abc
    rcases hz_abc with rfl | rfl | rfl
    · exact hp_off ha_L
    · exact hp_off hb_L
    · exact hp_off hc_L

  use x, lineThrough p z
  refine ⟨hx_S, ⟨p, z, hp, hz_S, hpz, rfl⟩, hx_off_pz, ?_⟩
  unfold configDist
  exact h_closer

/-- Main theorem: Sylvester-Gallai -/
theorem sylvester_gallai (S : Finset Plane) (h_card : 2 < S.card)
    (h_not_collinear : ¬Collinear ℝ (S : Set Plane)) :
    ∃ L : AffineSubspace ℝ Plane, IsOrdinaryLine S L := by
  -- Step 1: Find a non-collinear triple in S
  obtain ⟨p₁, p₂, p₃, hp₁, hp₂, hp₃, h12, h13, h23, h_not_col_triple⟩ :=
    exists_not_collinear_triple h_card h_not_collinear

  -- Step 2: Since {p₁,p₂,p₃} not collinear, p₃ ∉ line(p₁,p₂)
  have hp₃_off : p₃ ∉ lineThrough p₁ p₂ := by
    exact not_collinear_imp_not_mem_affineSpan h_not_col_triple

  -- Step 3: The configuration set is nonempty
  have hconfig_nonempty : (p₃, lineThrough p₁ p₂) ∈ Configurations S := by
    refine ⟨hp₃, ⟨p₁, p₂, hp₁, hp₂, h12, rfl⟩, hp₃_off⟩

  -- Step 4: The configuration set is finite (S is finite, lines are pairs from S)
  have hconfigs_finite : (Configurations S).Finite := by
    -- linesOf S is finite: bounded by |S|²
    have hlines_finite : (linesOf S).Finite := by
      have h : linesOf S ⊆ (fun ab : Plane × Plane => lineThrough ab.1 ab.2) '' ((S : Set Plane) ×ˢ S) := by
        intro L hL
        obtain ⟨a, b, ha, hb, hab, hL_eq⟩ := hL
        exact ⟨(a, b), ⟨ha, hb⟩, hL_eq.symm⟩
      exact Set.Finite.subset (Set.Finite.image _ (Set.Finite.prod (Finset.finite_toSet S)
        (Finset.finite_toSet S))) h
    apply Set.Finite.subset (s := (S : Set Plane) ×ˢ linesOf S)
    · exact Set.Finite.prod (Finset.finite_toSet S) hlines_finite
    · intro ⟨p, L⟩ ⟨hp, hL, _⟩
      exact ⟨hp, hL⟩

  -- Step 5: Pick configuration minimizing distance
  have h_min_exists : ∃ (p : Plane) (L : AffineSubspace ℝ Plane),
      (p, L) ∈ Configurations S ∧
      ∀ (p' : Plane) (L' : AffineSubspace ℝ Plane),
        (p', L') ∈ Configurations S → configDist (p, L) ≤ configDist (p', L') := by
    -- Use finiteness to extract minimum
    have hne : (Configurations S).Nonempty := ⟨_, hconfig_nonempty⟩
    have hne_finset : hconfigs_finite.toFinset.Nonempty := by
      rw [Set.Finite.toFinset_nonempty]
      exact hne
    obtain ⟨⟨pmin, Lmin⟩, hmin_mem, hmin_le⟩ :=
      hconfigs_finite.toFinset.exists_min_image configDist hne_finset
    refine ⟨pmin, Lmin, ?_, ?_⟩
    · rwa [Set.Finite.mem_toFinset] at hmin_mem
    · intro p' L' h
      exact hmin_le _ (by rwa [Set.Finite.mem_toFinset])

  obtain ⟨pmin, Lmin, hmin_config, hmin_prop⟩ := h_min_exists
  obtain ⟨hpmin_S, hLmin_lines, hpmin_off⟩ := hmin_config

  -- Step 6: Show Lmin is ordinary by contradiction
  -- If Lmin has 3+ points, we could find a closer config (contradiction)
  by_contra h_not_ord_any
  push_neg at h_not_ord_any

  -- Get the structure of Lmin from hLmin_lines
  obtain ⟨a, b, ha, hb, hab, hLmin_eq⟩ := hLmin_lines
  have hLmin_eq' : Lmin = lineThrough a b := hLmin_eq

  -- The minimum line must be ordinary
  by_cases h_ord : (S.filter (· ∈ Lmin)).card = 2
  · -- Lmin is ordinary - done!
    exfalso
    apply h_not_ord_any Lmin
    constructor
    · -- IsLine Lmin: it has dimension 1
      rw [hLmin_eq']
      unfold IsLine
      exact finrank_direction_lineThrough hab
    · exact h_ord
  · -- Lmin has ≠ 2 points on it
    -- Since Lmin is a line through 2 points of S, it has ≥ 2 points
    have h_ge_2 : 2 ≤ (S.filter (· ∈ Lmin)).card := by
      have ha_on : a ∈ Lmin := by rw [hLmin_eq']; exact left_mem_affineSpan_pair ℝ a b
      have hb_on : b ∈ Lmin := by rw [hLmin_eq']; exact right_mem_affineSpan_pair ℝ a b
      have ha_filt : a ∈ S.filter (· ∈ Lmin) := Finset.mem_filter.mpr ⟨ha, ha_on⟩
      have hb_filt : b ∈ S.filter (· ∈ Lmin) := Finset.mem_filter.mpr ⟨hb, hb_on⟩
      have h1lt : 1 < (S.filter (· ∈ Lmin)).card := by
        rw [Finset.one_lt_card]
        exact ⟨a, ha_filt, b, hb_filt, hab⟩
      omega
    -- So it has > 2 points (since ≠ 2 and ≥ 2)
    have h_gt_2 : 2 < (S.filter (· ∈ Lmin)).card := by omega
    -- By exists_closer_if_not_ordinary, there's a closer configuration
    have hpmin_S' : pmin ∈ S := hpmin_S
    have hLmin_lines' : Lmin ∈ linesOf S := ⟨a, b, ha, hb, hab, hLmin_eq'⟩
    have hpmin_off' : pmin ∉ Lmin := hpmin_off
    obtain ⟨p', L', hp'S, hL'_lines, hp'_off, h_closer⟩ :=
      exists_closer_if_not_ordinary hpmin_S' hLmin_lines' hpmin_off' h_gt_2
    -- But this contradicts minimality of (pmin, Lmin)
    have h_not_closer := hmin_prop p' L' ⟨hp'S, hL'_lines, hp'_off⟩
    linarith

#check sylvester_gallai
