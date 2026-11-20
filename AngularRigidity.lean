import SixthMoment

open Set
noncomputable section
namespace SixthMoment

/-- A bound on cosines gives a nearby representative modulo a full turn. -/
lemma exists_close_angle_of_cos_le {a t δ : ℝ} (hδ : δ ∈ Icc 0 Real.pi)
    (hc : Real.cos δ ≤ Real.cos (a-t)) :
    ∃ z : ℤ, |a + (z:ℝ)*(2*Real.pi) - t| ≤ δ := by
  have hp : 0 < 2*Real.pi := by positivity
  let d := toIcoMod hp (-Real.pi) (a-t)
  let z := toIcoDiv hp (-Real.pi) (a-t)
  have hm := toIcoMod_mem_Ico hp (-Real.pi) (a-t)
  have hd : -Real.pi ≤ d ∧ d ≤ Real.pi := by
    refine ⟨hm.1, ?_⟩
    change toIcoMod hp (-Real.pi) (a-t) ≤ _
    linarith [hm.2]
  have erep : d + (z:ℝ)*(2*Real.pi) = a-t := by
    simpa only [zsmul_eq_mul] using toIcoMod_add_toIcoDiv_zsmul hp (-Real.pi) (a-t)
  have ec : Real.cos |d| = Real.cos (a-t) := by
    rw [Real.cos_abs, ← erep, Real.cos_add_int_mul_two_pi]
  have habs : |d| ≤ δ :=
    (Real.strictAntiOn_cos.le_iff_le hδ ⟨abs_nonneg d, abs_le.mpr hd⟩).mp (ec.symm ▸ hc)
  refine ⟨-z, ?_⟩
  rwa [show a + ((-z:ℤ):ℝ)*(2*Real.pi)-t = d by push_cast; linarith]

/-- For every direction, the support value of the inball must be attained or exceeded
by at least one vertex. A circumradius bound turns this support estimate into angular coverage. -/
theorem angular_cover_of_inball {n : ℕ} (hn : 3 ≤ n) {ρ : ℝ} (hρ : 0 < ρ)
    (v : Fin n → Plane) (angle radius : Fin n → ℝ)
    (hcoords : ∀ i, v i = (radius i * Real.cos (angle i), radius i * Real.sin (angle i)))
    (hradius : ∀ i, radius i ∈ Icc 0 ρ)
    (inner : disk ((ρ * Real.cos (Real.pi/n))^2) ⊆ convexHull ℝ (range v)) :
    ∀ t : ℝ, ∃ i : Fin n, ∃ z : ℤ, |angle i + (z:ℝ)*(2*Real.pi)-t| ≤ Real.pi/n := by
  intro t
  let δ := Real.pi/n
  have hn' : (2:ℝ)<n := by exact_mod_cast (show 2<n by omega)
  have hδ : 0<δ := div_pos Real.pi_pos (by linarith)
  have hδ' : δ < Real.pi/2 := by
    exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) hn'
  have cp : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδ'⟩
  let h := ρ * Real.cos δ
  let p : Plane := (h * Real.cos t, h * Real.sin t)
  let proj : Plane →ₗ[ℝ] ℝ := Real.cos t • LinearMap.fst ℝ ℝ ℝ +
    Real.sin t • LinearMap.snd ℝ ℝ ℝ
  have projval (x : Plane) : proj x = Real.cos t*x.1 + Real.sin t*x.2 := rfl
  have projP : proj p = h := by
    rw [projval]; dsimp [p]
    linear_combination h * Real.cos_sq_add_sin_sq t
  have inHull : p ∈ convexHull ℝ (range v) := by
    apply inner
    change (h*Real.cos t)^2 + (h*Real.sin t)^2 ≤ h^2
    exact le_of_eq (by linear_combination h^2 * Real.cos_sq_add_sin_sq t)
  have witness : ∃ i, h ≤ proj (v i) := by
    by_contra! H
    have sub : convexHull ℝ (range v) ⊆ {x | proj x < h} := by
      apply convexHull_min _ (convex_halfSpace_lt proj.isLinear h)
      rintro _ ⟨i,rfl⟩; exact H i
    exact (lt_irrefl h) (projP ▸ sub inHull)
  obtain ⟨i,hi⟩ := witness
  have eval : proj (v i) = radius i * Real.cos (angle i - t) := by
    rw [projval, hcoords, Real.cos_sub]; dsimp; ring
  rw [eval] at hi
  have cpos : 0 < Real.cos (angle i-t) := by
    by_contra! hc
    exact (not_lt_of_ge ((mul_nonpos_of_nonneg_of_nonpos (hradius i).1 hc)))
      ((mul_pos hρ cp).trans_le hi)
  have HC := hi.trans (mul_le_mul_of_nonneg_right (hradius i).2 cpos.le)
  refine ⟨i, exists_close_angle_of_cos_le ⟨hδ.le, by linarith [Real.pi_pos]⟩ ?_⟩
  exact (mul_le_mul_left hρ).mp HC

#print axioms angular_cover_of_inball
end SixthMoment
