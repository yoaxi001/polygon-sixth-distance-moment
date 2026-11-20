import SixthMoment
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Set MeasureTheory
noncomputable section
namespace SixthMoment

lemma convex_disk (s : ℝ) : Convex ℝ (disk s) := by
  intro x hx y hy a b ha hb hab
  change r (a • x + b • y) ≤ s
  change r x ≤ s at hx
  change r y ≤ s at hy
  have id : a*r x+b*r y-r (a • x + b • y) =
      a*b*((x.1-y.1)^2+(x.2-y.2)^2) := by
    simp only [r,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    linear_combination -(a*x.1^2+a*x.2^2+b*y.1^2+b*y.2^2)*hab
  have h := mul_nonneg (mul_nonneg ha hb) (add_nonneg (sq_nonneg (x.1-y.1)) (sq_nonneg (x.2-y.2)))
  linarith only [id,h, mul_le_mul_of_nonneg_left hx ha,mul_le_mul_of_nonneg_left hy hb,
    show a*s+b*s=s by linear_combination s*hab]

theorem regular_in_outer_disk (m : ℕ) (ρ : ℝ) : regularPolygon m ρ ⊆ disk (ρ^2) := by
  apply convexHull_min _ (convex_disk _)
  rintro _ ⟨i,rfl⟩
  change (ρ * Real.cos _)^2 + (ρ * Real.sin _)^2 ≤ ρ^2
  nlinarith only [show ρ^2 * (Real.cos (i*(Real.pi/m))^2 + Real.sin (i*(Real.pi/m))^2) = ρ^2 by
    rw [Real.cos_sq_add_sin_sq, mul_one]]

lemma convex_polygon {n K} (hp : ConvexPolygonWith n K) : Convex ℝ K := by
  obtain ⟨v,rfl,_⟩ := hp
  exact convex_convexHull ℝ _

lemma unit_volume_positive {K : Set Plane} (unit : avg K (fun _ => 1)=1) : 0 < volume K := by
  apply pos_iff_ne_zero.mpr
  intro h
  simp [avg,Measure.real,h] at unit

/-- If two equal-area regions have equal disk profiles, any centered disk containing the
reference region contains the entire compact convex competitor, including its vertices. -/
theorem outer_disk_of_profile {K R : Set Plane} (kc : IsCompact K) (cv : Convex ℝ K)
    (pos : 0 < volume K) (mass : volume R = volume K) {s : ℝ} (outer : R ⊆ disk s)
    (overlap : volume (R ∩ disk s) = volume (K ∩ disk s)) : K ⊆ disk s := by
  have e : K ∩ disk s = K := eq_of_nested_equal_area
    (kc.isClosed.inter (isClosed_le r_cont continuous_const)) kc cv inter_subset_left pos
    (overlap.symm.trans (by rwa [inter_eq_self_of_subset_left outer]))
  exact fun x hx => (show x ∈ K ∩ disk s from e.symm ▸ hx).2

/-- Equality in the distance inequality confines all vertices to the regular circumdisk,
and transfers every positive centered disk inside the reference to the competitor. -/
theorem disks_of_energy_equality {m : ℕ} (hm : 2≤m) {ρ : ℝ}
    (ra : avg (regularPolygon m ρ) (fun _ => 1)=1) (geom : PolygonDiskComparison m ρ)
    {K : Set Plane} (polygon : ConvexPolygonWith (2*m) K)
    (ks : ∀ x : Plane, -x ∈ K ↔ x ∈ K) (ka : avg K (fun _ => 1)=1)
    (ee : energy (regularPolygon m ρ) = energy K) :
    K ⊆ disk (ρ^2) ∧ ∀ s : ℝ, 0<s → disk s ⊆ regularPolygon m ρ → disk s ⊆ K := by
  have rc := compact_regular (show 0<m by omega) ρ
  have mass : volume (regularPolygon m ρ) = volume K := by
    apply (ENNReal.toReal_eq_toReal rc.measure_lt_top.ne polygon.compact.measure_lt_top.ne).mp
    simpa [avg] using ra.trans ka.symm
  have allDisks := (centrally_symmetric_polygon_sixth_moment hm ra geom polygon ks ka).2 ee
  refine ⟨outer_disk_of_profile polygon.compact (convex_polygon polygon) (unit_volume_positive ka)
    mass (regular_in_outer_disk m ρ) (allDisks _ (sq_nonneg _)), ?_⟩
  have dom (L : Plane →ₗ[ℝ] Plane) (hL : L.det = 1) :=
    geom _ (polygon.linear_image L hL) ((avg_linear_image K L hL (fun _ => 1)).trans ka)
  have me := (regular_polygon_energy hm polygon.compact ks ka ra dom).2 ee
  intro s hs hR
  exact disk_subset_of_open_disk_subset hs polygon.compact.isClosed
    (open_disk_subset_of_equal_moment rc polygon.compact mass (geom K polygon ka)
      (by decide : 3≠0) me hs.le hR)

lemma polar_vertex (x : Plane) {ρ : ℝ} (hρ : 0≤ρ) (hx : x ∈ disk (ρ^2)) :
    ∃ t ∈ Ico (0:ℝ) (2*Real.pi), ∃ d ∈ Icc (0:ℝ) ρ,
      x = (d * Real.cos t,d * Real.sin t) := by
  let z : ℂ := ⟨x.1,x.2⟩
  have hn : ‖z‖ ≤ ρ := by
    change x.1^2 + x.2^2 ≤ ρ^2 at hx
    have e : ‖z‖^2=x.1^2+x.2^2 := by rw [Complex.sq_norm, Complex.normSq_apply]; dsimp [z]; ring
    nlinarith [norm_nonneg z]
  have coords : x=(‖z‖*Real.cos z.arg,‖z‖*Real.sin z.arg) := by
    rw [Complex.norm_mul_cos_arg,Complex.norm_mul_sin_arg]
  by_cases ha : z.arg < 0
  · refine ⟨z.arg+2*Real.pi, ⟨by linarith [Complex.neg_pi_lt_arg z,Real.pi_pos],by linarith⟩,
      ‖z‖,⟨norm_nonneg _,hn⟩,?_⟩
    simpa only [Real.cos_add_two_pi,Real.sin_add_two_pi] using coords
  · exact ⟨z.arg,⟨le_of_not_gt ha,by linarith [Complex.arg_le_pi z,Real.pi_pos]⟩,
      ‖z‖,⟨norm_nonneg _,hn⟩,coords⟩

/-- Equally spaced vertex directions and an upper radius bound put the hull inside a
rotated regular polygon. No equality of individual radii is assumed. -/
theorem hull_subset_of_equal_directions {m : ℕ} (hm : 0<m) {ρ : ℝ} (hρ : 0<ρ)
    (v : Fin (2*m) → Plane) (angle d : Fin (2*m) → ℝ)
    (rad : ∀ i, d i ∈ Icc 0 ρ)
    (coords : ∀ i, v i = (d i * Real.cos (angle i),d i * Real.sin (angle i)))
    {base : ℝ} (σ : Equiv.Perm (Fin (2*m)))
    (hangle : ∀ i, angle (σ i) = base+(i:ℝ)*(2*Real.pi/(2*m:ℕ))) :
    convexHull ℝ (range v) ⊆ rotation (Real.cos base) (Real.sin base) '' regularPolygon m ρ := by
  let L := rotation (Real.cos base) (Real.sin base)
  have cv : Convex ℝ (regularPolygon m ρ) := convex_convexHull _ _
  have cv' : Convex ℝ (L '' regularPolygon m ρ) := cv.linear_image L
  have point (i : ℕ) : vertex m ρ i ∈ regularPolygon m ρ := subset_convexHull _ _ (mem_range_self i)
  have hz : (0:Plane) ∈ regularPolygon m ρ := by
    have h := cv (point 0) ((symmetric_regular hm ρ _).2 (point 0))
      (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)
    simpa using h
  have zero : (0:Plane) ∈ L '' regularPolygon m ρ := ⟨0,hz,L.map_zero⟩
  have step : 2*Real.pi/(2*m:ℕ) = Real.pi/m := by push_cast; ring
  apply convexHull_min _ cv'
  rintro _ ⟨j,rfl⟩
  obtain ⟨i,rfl⟩ := σ.surjective j
  have vmem : L (vertex m ρ i) ∈ L '' regularPolygon m ρ := ⟨_,point _,rfl⟩
  have h := cv'.smul_mem_of_zero_mem zero vmem
      (show d (σ i)/ρ ∈ Icc (0:ℝ) 1 from
        ⟨div_nonneg (rad _).1 hρ.le, (div_le_one hρ).2 (rad _).2⟩)
  have e : v (σ i) = (d (σ i)/ρ) • L (vertex m ρ i) := by
    rw [coords,hangle,step]
    simp only [L, rotation, vertex, Matrix.toLin_finTwoProd_apply, Real.cos_add, Real.sin_add]
    apply Prod.ext <;> dsimp <;> field_simp <;> ring
  exact e ▸ h

theorem eq_rotated_regular_of_subset {m : ℕ} (hm : 0<m) {ρ base : ℝ} {K : Set Plane}
    (kc : IsCompact K) (ka : avg K (fun _ => 1)=1) (ra : avg (regularPolygon m ρ) (fun _ => 1)=1)
    (incl : K ⊆ rotation (Real.cos base) (Real.sin base) '' regularPolygon m ρ) :
    K = rotation (Real.cos base) (Real.sin base) '' regularPolygon m ρ := by
  let L := rotation (Real.cos base) (Real.sin base)
  have det : L.det = 1 := by
    simp [L,rotation,LinearMap.det_toLin,Matrix.det_fin_two]
    nlinarith only [Real.cos_sq_add_sin_sq base]
  have area := (avg_linear_image (regularPolygon m ρ) L det (fun _ => 1)).trans ra
  have compact := (compact_regular hm ρ).image L.continuous_of_finiteDimensional
  have cv : Convex ℝ (regularPolygon m ρ) := convex_convexHull _ _
  apply eq_of_nested_equal_area kc.isClosed compact (cv.linear_image L) incl (unit_volume_positive area)
  apply (ENNReal.toReal_eq_toReal kc.measure_lt_top.ne compact.measure_lt_top.ne).mp
  simpa [avg] using ka.trans area.symm

#print axioms disks_of_energy_equality
#print axioms hull_subset_of_equal_directions
#print axioms eq_rotated_regular_of_subset
end SixthMoment
