/-
  Proof of the area formula for perpendicular distances in triangles.
  Uses coordinate-wise expansion for EuclideanSpace ℝ (Fin 2).
-/
import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def lineThrough (p q : Plane) : AffineSubspace ℝ Plane := affineSpan ℝ {p, q}

-- Plane is 2-dimensional
instance plane_finrank_2 : Fact (Module.finrank ℝ Plane = 2) := ⟨finrank_euclideanSpace_fin⟩

-- The 2D "cross product" in terms of coordinates
def cross2D (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

-- Helper: access coordinate i of EuclideanSpace
lemma euclidean_apply (u : Plane) (i : Fin 2) : u i = u.ofLp i := rfl

-- cross2D is antisymmetric
lemma cross2D_swap (u v : Plane) : cross2D v u = -cross2D u v := by
  simp only [cross2D]; ring

-- cross2D u u = 0
lemma cross2D_self (u : Plane) : cross2D u u = 0 := by
  simp only [cross2D]; ring

-- Coordinate expansion for subtraction
lemma sub_ofLp (u v : Plane) (i : Fin 2) : (u - v).ofLp i = u.ofLp i - v.ofLp i := by
  simp only [WithLp.ofLp_sub]
  rfl

-- The Lagrange identity / Pythagorean identity
-- |cross|² + ⟨u,v⟩² = ‖u‖² * ‖v‖²
lemma cross2D_sq_add_inner_sq (u v : Plane) :
    cross2D u v ^ 2 + inner (𝕜 := ℝ) u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  simp only [cross2D]
  -- Expand norm squared
  have hu : ‖u‖ ^ 2 = ∑ i : Fin 2, ‖u.ofLp i‖ ^ 2 := EuclideanSpace.norm_sq_eq u
  have hv : ‖v‖ ^ 2 = ∑ i : Fin 2, ‖v.ofLp i‖ ^ 2 := EuclideanSpace.norm_sq_eq v
  -- Expand inner product
  have huv : inner (𝕜 := ℝ) u v = ∑ i : Fin 2, inner (𝕜 := ℝ) (u.ofLp i) (v.ofLp i) := PiLp.inner_apply u v
  -- For real scalars, inner x y = y * conj x = y * x
  simp only [@RCLike.inner_apply ℝ, conj_trivial, mul_comm] at huv
  simp only [Real.norm_eq_abs, sq_abs] at hu hv
  -- Expand sums over Fin 2
  simp only [Fin.sum_univ_two] at hu hv huv
  rw [hu, hv, huv]
  ring

-- |cross2D u v|² = ‖u‖² * ‖v‖² - ⟨u,v⟩²
lemma cross2D_sq_eq (u v : Plane) :
    cross2D u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - inner (𝕜 := ℝ) u v ^ 2 := by
  have h := cross2D_sq_add_inner_sq u v
  linarith

-- The absolute value form
lemma abs_cross2D_sq_eq (u v : Plane) :
    |cross2D u v| ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - inner (𝕜 := ℝ) u v ^ 2 := by
  rw [sq_abs, cross2D_sq_eq]

-- More directly: cross2D (z-x) (p-x) in terms of cross2D (z-p) (x-p)
lemma cross2D_triangle_eq (p x z : Plane) :
    cross2D (z -ᵥ x) (p -ᵥ x) = -cross2D (z -ᵥ p) (x -ᵥ p) := by
  simp only [cross2D, vsub_eq_sub, euclidean_apply, sub_ofLp]
  ring

-- Absolute values are equal
lemma abs_cross2D_triangle (p x z : Plane) :
    |cross2D (z -ᵥ x) (p -ᵥ x)| = |cross2D (z -ᵥ p) (x -ᵥ p)| := by
  rw [cross2D_triangle_eq, abs_neg]

#check cross2D_sq_add_inner_sq
#check cross2D_sq_eq
#check abs_cross2D_triangle

end
