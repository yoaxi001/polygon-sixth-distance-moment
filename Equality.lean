import Centering
import DiskEquality
import AngularRigidity
import PolarGaps
import RegularDisk

open Set MeasureTheory
noncomputable section
namespace SixthMoment

theorem centered_equality_iff {m : ℕ} (hm : 2≤m) {ρ : ℝ} (hp : 0<ρ)
    (ra : avg (regularPolygon m ρ) (fun _ => 1)=1) (geom : PolygonDiskComparison m ρ)
    {K : Set Plane} (P : ConvexPolygonWith (2*m) K)
    (sym : ∀ x : Plane, -x ∈ K ↔ x ∈ K) (ka : avg K (fun _ => 1)=1) :
    energy (regularPolygon m ρ) = energy K ↔ ∃ a : ℝ,
      K = rotation (Real.cos a) (Real.sin a) '' regularPolygon m ρ := by
  constructor
  · intro ee
    obtain ⟨outer,inner⟩ := disks_of_energy_equality hm ra geom P sym ka ee
    have kc := P.compact
    obtain ⟨v,hK,_⟩ := P
    have point (i) : v i ∈ K := hK ▸ subset_convexHull _ _ (mem_range_self i)
    choose angle ha d hd coords using fun i => polar_vertex (v i) hp.le (outer (point i))
    have hm' : 2≤(m:ℝ) := by exact_mod_cast hm
    have hlt : Real.pi/(2*(m:ℝ)) < Real.pi/2 := by
      apply (div_lt_iff₀ (by positivity)).2
      nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hm')]
    have hc := Real.cos_pos_of_mem_Ioo (show Real.pi/(2*(m:ℝ)) ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by have : 0 < Real.pi/(2*(m:ℝ)) := by positivity
          linarith [Real.pi_pos],hlt⟩)
    have inc := inner _ (sq_pos_of_pos (mul_pos hp hc)) (regular_incircle_subset hm hp.le)
    have cover := angular_cover_of_inball (show 3≤2*m by omega) hp v angle d coords hd
      (by simpa [← hK, Nat.cast_mul] using inc)
    obtain ⟨base,σ,h⟩ := polar_gaps_regular (show 0<2*m by omega) angle ha cover
    refine ⟨base,eq_rotated_regular_of_subset (by omega) kc ka ra ?_⟩
    rw [hK]
    exact hull_subset_of_equal_directions (by omega) hp v angle d hd coords σ h
  · rintro ⟨a,rfl⟩
    exact (energy_rotate _ (Real.cos_sq_add_sin_sq a)).symm

theorem polygon_sixth_moment_with_equality {m : ℕ} (hm : 2≤m) {ρ : ℝ} (hp : 0<ρ)
    (ra : avg (regularPolygon m ρ) (fun _ => 1)=1) (geom : PolygonDiskComparison m ρ)
    {K : Set Plane} (P : ConvexPolygonWith (2*m) K) (c : Plane)
    (sym : ∀ x : Plane, c+(c-x) ∈ K ↔ x ∈ K) (ka : avg K (fun _ => 1)=1) :
    energy (regularPolygon m ρ) ≤ energy K ∧
    (energy (regularPolygon m ρ) = energy K ↔ ∃ a : ℝ,
      K = translate c (rotation (Real.cos a) (Real.sin a) '' regularPolygon m ρ)) := by
  have p := P.translated (-c)
  have u := (area_translate (-c) K).trans ka
  have sy := symmetric_after_centering sym
  have en : energy (translate (-c) K) = energy K := energy_translate _ _
  exact ⟨((centrally_symmetric_polygon_sixth_moment hm ra geom p sy u).1.trans en.le), by
    constructor
    · intro h
      obtain ⟨a,ha⟩ := (centered_equality_iff hm hp ra geom p sy u).mp (h.trans en.symm)
      exact ⟨a,(translate_back c K).symm.trans (congrArg (translate c) ha)⟩
    · rintro ⟨a,rfl⟩
      exact ((energy_translate _ _).trans (energy_rotate _ (Real.cos_sq_add_sin_sq a))).symm⟩

#print axioms polygon_sixth_moment_with_equality
end SixthMoment
