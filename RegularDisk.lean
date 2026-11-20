import SixthMoment
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Set
noncomputable section
namespace SixthMoment

/-- Rounding a nonnegative angle to the nearest integral multiple of a positive step. -/
private theorem nearest_step {β d : ℝ} (hβ : 0 ≤ β) (hd : 0 < d) :
    ∃ i : ℕ, |(i:ℝ)*d-β| ≤ d/2 := by
  let i := ⌊β/d+1/2⌋₊
  have lo : (i:ℝ) ≤ β/d+1/2 := Nat.floor_le (by positivity)
  have hi : β/d+1/2 < (i:ℝ)+1 := Nat.lt_floor_add_one _
  have h1 := mul_le_mul_of_nonneg_right lo hd.le
  have h2 := mul_lt_mul_of_pos_right hi hd
  rw [add_mul, div_mul_cancel₀ _ hd.ne'] at h1 h2
  exact ⟨i, abs_le.mpr ⟨by linarith, by linarith⟩⟩

private theorem dual_coordinates (f : Plane →L[ℝ] ℝ) (y : Plane) :
    f y = f (1,0)*y.1+f (0,1)*y.2 := by
  have e : y = y.1 • ((1,0):Plane) + y.2 • ((0,1):Plane) := by ext <;> simp
  conv_lhs => rw [e, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

/-- A regular 2m-gon's convex hull contains its closed incircle. -/
theorem regular_incircle_subset {m : ℕ} (hm : 2 ≤ m) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    disk ((ρ*Real.cos (Real.pi/(2*(m:ℝ))))^2) ⊆ regularPolygon m ρ := by
  let d := Real.pi / (m:ℝ)
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hm1 : 1 < (m:ℝ) := by exact_mod_cast (show 1<m by omega)
  have hd : 0 < d := div_pos Real.pi_pos hm0
  have hdlt : d < Real.pi := div_lt_self Real.pi_pos hm1
  have half : Real.pi/(2*(m:ℝ)) = d/2 := by dsimp [d]; ring
  have hc : 0 < Real.cos (d/2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],by linarith⟩
  intro x hx
  change r x ≤ (ρ*Real.cos (Real.pi/(2*(m:ℝ))))^2 at hx
  rw [half] at hx
  by_contra out
  obtain ⟨f,t,hbody,hxsep⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (range (vertex m ρ)))
    (compact_regular (show 0<m by omega) ρ).isClosed out
  let z : ℂ := ⟨f (1,0), f (0,1)⟩
  let β := z.arg+2*Real.pi
  obtain ⟨i,hi⟩ := nearest_step (show 0 ≤ β by
    dsimp [β]; linarith [Complex.neg_pi_lt_arg z,Real.pi_pos]) hd
  have A : ‖z‖*Real.cos β=f (1,0) := by
    simp [β,z]
  have B : ‖z‖*Real.sin β=f (0,1) := by
    simp [β,z]
  let proj (y : Plane) := Real.cos β*y.1+Real.sin β*y.2
  have dual (y : Plane) : f y = ‖z‖*proj y := by
    rw [dual_coordinates, ← A, ← B]; dsimp [proj]; ring
  have unit := Real.cos_sq_add_sin_sq β
  have projSq : (proj x)^2+(Real.sin β*x.1-Real.cos β*x.2)^2 = r x := by
    dsimp [proj, r]; linear_combination (x.1^2+x.2^2)*unit
  have small : proj x ≤ ρ*Real.cos (d/2) := by
    have nonneg := mul_nonneg hρ hc.le
    have bound : (proj x)^2 ≤ (ρ*Real.cos (d/2))^2 := by
      calc (proj x)^2 ≤ (proj x)^2+(Real.sin β*x.1-Real.cos β*x.2)^2 :=
             le_add_of_nonneg_right (sq_nonneg _)
           _ = r x := projSq
           _ ≤ _ := hx
    exact (abs_le.mp ((sq_le_sq.mp bound).trans_eq (abs_of_nonneg nonneg))).2
  have direction := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (show d/2 ≤ Real.pi by
    linarith [Real.pi_pos]) hi
  rw [Real.cos_abs] at direction
  have val : proj (vertex m ρ i) = ρ*Real.cos ((i:ℝ)*d-β) := by
    dsimp [proj,vertex,d]; rw [Real.cos_sub]; ring
  have hle : f x ≤ f (vertex m ρ i) := by
    rw [dual, dual, val]
    exact mul_le_mul_of_nonneg_left (small.trans (mul_le_mul_of_nonneg_left direction hρ))
      (norm_nonneg _)
  have hv : vertex m ρ i ∈ regularPolygon m ρ :=
    subset_convexHull ℝ (range (vertex m ρ)) (mem_range_self i)
  exact (lt_asymm (hle.trans_lt (hbody _ hv))) hxsep

#print axioms regular_incircle_subset
end SixthMoment
