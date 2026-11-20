import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic

open MeasureTheory Set
noncomputable section
namespace SixthMoment
abbrev Plane := ℝ × ℝ
def avg (K : Set Plane) (f : Plane → ℝ) := ∫ x in K, f x
def r (x : Plane) := x.1^2 + x.2^2
def dot (x y : Plane) := x.1*y.1 + x.2*y.2
def energy (K : Set Plane) := avg K fun x => avg K fun y => r (x-y)^3
def moment (K : Set Plane) (k : ℕ) := avg K fun x => r x ^ k

@[fun_prop] lemma r_cont : Continuous r := by unfold r; fun_prop
lemma avg_add (K : Set Plane) (hK : IsCompact K) (f g : Plane → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    avg K (fun x => f x + g x) = avg K f + avg K g :=
  integral_add (hf.continuousOn.integrableOn_compact hK) (hg.continuousOn.integrableOn_compact hK)
lemma avg_mul (K : Set Plane) (a : ℝ) (f : Plane → ℝ) :
    avg K (fun x => a * f x) = a * avg K f := integral_const_mul _ _
lemma avg_mono (K : Set Plane) (hK : IsCompact K) {f g : Plane → ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ x, f x ≤ g x) : avg K f ≤ avg K g :=
  integral_mono (hf.continuousOn.integrableOn_compact hK) (hg.continuousOn.integrableOn_compact hK) h

/-- Central symmetry of the domain makes reflection preserve its area integral. -/
lemma avg_reflect (K : Set Plane) (sym : ∀ x : Plane, -x ∈ K ↔ x ∈ K) (f : Plane → ℝ) :
    avg K (fun x => f (-x)) = avg K f := by
  have h1 : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume := by
    refine ⟨measurable_neg, ?_⟩
    simpa using Real.map_volume_mul_left (a := (-1:ℝ)) (by norm_num)
  have hp : MeasurePreserving (Neg.neg : Plane → Plane) volume volume := h1.prod h1
  have h := hp.setIntegral_preimage_emb
    (MeasurableEquiv.neg Plane).measurableEmbedding f K
  have pre : Neg.neg ⁻¹' K = K := Set.ext sym
  rwa [pre] at h

def mix (K : Set Plane) := avg K fun x => r x *
  (avg K (fun y => y.1^2) * x.1^2 + 2*avg K (fun y => y.1*y.2)*x.1*x.2 +
    avg K (fun y => y.2^2)*x.2^2)

lemma avg_right (K : Set Plane) (f : Plane → ℝ) (a : ℝ) :
    avg K (fun x => f x * a) = avg K f * a := integral_mul_const _ _

theorem energy_expand (K : Set Plane) (hc : IsCompact K)
    (sym : ∀ x : Plane, -x ∈ K ↔ x ∈ K) (area : avg K (fun _ => 1) = 1) :
    energy K = 2*moment K 3 + 6*moment K 1*moment K 2 + 24*mix K := by
  let evenPart (x y : Plane) := (r x + r y)^3 + 12*(r x+r y)*(dot x y)^2
  have evenInt (x : Plane) : avg K (fun y => r (x-y)^3) = avg K (evenPart x) := by
    have symm := avg_reflect K sym (fun y => r (x-y)^3)
    have h : (fun y => r (x-y)^3 + r (x- -y)^3) = (fun y => 2*evenPart x y) := by
      funext y
      simp [evenPart, r, dot, Prod.fst_sub, Prod.snd_sub]
      ring
    have hh := congrArg (avg K) h
    rw [avg_add K hc _ _ (by fun_prop) (by fun_prop), avg_mul] at hh
    linarith
  let m (f : Plane → ℝ) := avg K f
  let a := m (fun x => x.1^2)
  let b := m (fun x => x.1*x.2)
  let c := m (fun x => x.2^2)
  let u := m (fun x => r x*x.1^2)
  let v := m (fun x => r x*(x.1*x.2))
  let w := m (fun x => r x*x.2^2)
  have ie (x : Plane) : avg K (evenPart x) =
      r x^3 + 3*r x^2*m r + 3*r x*m (fun y => r y^2) + m (fun y => r y^3) +
      12*(r x*x.1^2*a + 2*(r x*(x.1*x.2))*b + r x*x.2^2*c +
          x.1^2*u + 2*(x.1*x.2)*v + x.2^2*w) := by
    have h : evenPart x = (fun y => r x^3 * (1:ℝ) + (3*r x^2)*r y +
       (3*r x)*r y^2 + r y^3 + (12*(r x*x.1^2))*y.1^2 +
       (24*(r x*(x.1*x.2)))*(y.1*y.2) + (12*(r x*x.2^2))*y.2^2 +
       (12*x.1^2)*(r y*y.1^2) + (24*(x.1*x.2))*(r y*(y.1*y.2)) +
       (12*x.2^2)*(r y*y.2^2)) := by funext y; dsimp [evenPart,dot]; ring
    rw [h]
    simp (disch := fun_prop) only [avg_add K hc, avg_mul, area]
    simp only [mul_one]
    dsimp [a,b,c,u,v,w,m]
    ring
  have hm : mix K = a*u + 2*b*v + c*w := by
    unfold mix
    change avg K (fun x => r x*(a*x.1^2 + 2*b*x.1*x.2+c*x.2^2)) = _
    rw [show (fun x : Plane => r x*(a*x.1^2 + 2*b*x.1*x.2+c*x.2^2)) =
        (fun x => a*(r x*x.1^2)+(2*b)*(r x*(x.1*x.2))+c*(r x*x.2^2)) by funext x; ring]
    simp (disch := fun_prop) only [avg_add K hc, avg_mul]
    rfl
  unfold energy
  simp_rw [evenInt, ie]
  rw [hm]
  simp (disch := fun_prop) only [avg_add K hc, avg_mul, avg_right]
  have hconst (t : ℝ) : avg K (fun _ => t) = t := by
    simpa only [mul_one, area] using avg_mul K t (fun _ => 1)
  simp only [hconst, moment, pow_one]
  dsimp [a,b,c,u,v,w,m]
  ring

#print axioms energy_expand
/-- Positive quadratic forms encode radial moments after a linear change of coordinates.
The determinant factor keeps the comparison independent of scale. -/
def form (a b c : ℝ) (x : Plane) := a*x.1^2 + 2*b*x.1*x.2 + c*x.2^2
@[fun_prop] lemma form_cont (a b c : ℝ) : Continuous (form a b c) := by unfold form; fun_prop
def radialBound (K : Set Plane) (k : ℕ) (v : ℝ) : Prop :=
  ∀ a b c : ℝ, 0 < a → 0 < a*c-b^2 →
    (Real.sqrt (a*c-b^2))^k*v ≤ avg K (fun x => form a b c x ^ k)

lemma radial_identity {K k v} (h : radialBound K k v) : v ≤ moment K k := by
  simpa [form, moment, r] using h 1 0 1 (by norm_num) (by norm_num)

lemma quadratic_integral (K : Set Plane) (hc : IsCompact K) (a b c : ℝ) :
    avg K (form a b c) = a*avg K (fun x => x.1^2) +
    2*b*avg K (fun x => x.1*x.2) + c*avg K (fun x => x.2^2) := by
  unfold form
  simp (disch := fun_prop) only [mul_assoc (2*b), avg_add K hc, avg_mul]

/-- Two different positive forms provide the second- and fourth-moment estimates. -/
theorem mixed_bound (K : Set Plane) (hc : IsCompact K) (s₂ s₄ : ℝ)
    (h₂ : radialBound K 1 s₂) (h₄ : radialBound K 2 s₄) (h4pos : 0 ≤ s₄)
    (nondeg : 0 < avg K (fun x => x.1^2)*avg K (fun x => x.2^2) -
                    (avg K (fun x => x.1*x.2))^2) :
    s₂*s₄ ≤ 2*mix K := by
  let a := avg K (fun x => x.1^2)
  let b := avg K (fun x => x.1*x.2)
  let c := avg K (fun x => x.2^2)
  change 0 < a*c-b^2 at nondeg
  have ha : 0 ≤ a := integral_nonneg (fun x => sq_nonneg _)
  have hc0 : 0 ≤ c := integral_nonneg (fun x => sq_nonneg _)
  have hcpos : 0 < c := by
    by_contra! hh
    have : c=0 := le_antisymm hh hc0
    rw [this] at nondeg
    nlinarith [sq_nonneg b]
  let d := Real.sqrt (a*c-b^2)
  have hd : 0<d := Real.sqrt_pos.2 nondeg
  have hd2 : d^2=a*c-b^2 := Real.sq_sqrt nondeg.le
  have he : c*a-(-b)^2=a*c-b^2 := by ring
  have H := h₂ c (-b) a hcpos (he.symm ▸ nondeg)
  simp only [he, pow_one] at H
  rw [quadratic_integral K hc] at H
  change d*s₂ ≤ c*a + 2*(-b)*b+a*c at H
  have dlow : s₂ ≤ 2*d := by
    apply le_of_mul_le_mul_left (a := d) _ hd
    nlinarith only [H,hd2]
  let t := a+c+2*d
  have ht : 0<t := by dsimp [t]; linarith
  have det : (a+d)*(c+d)-b^2=d*t := by dsimp [t]; nlinarith only [hd2]
  have J := h₄ (a+d) b (c+d) (by linarith) (det.symm ▸ mul_pos hd ht)
  rw [det,Real.sq_sqrt (mul_pos hd ht).le] at J
  have cmp : ∀ x : Plane, form (a+d) b (c+d) x ^2 ≤ t*(r x * form a b c x) := by
    intro x
    have e : t*(r x*form a b c x) - form (a+d) b (c+d) x^2 =
        (b*(x.1^2-x.2^2)+(c-a)*x.1*x.2)^2 + (a*c-b^2-d^2)*(r x)^2 := by
      dsimp [t,r,form]; ring
    rw [show a*c-b^2-d^2=0 by linarith, zero_mul, add_zero] at e
    linarith only [e,sq_nonneg (b*(x.1^2-x.2^2)+(c-a)*x.1*x.2)]
  have bound := avg_mono K hc (by fun_prop) (by fun_prop) cmp
  rw [avg_mul] at bound
  change _ ≤ t*mix K at bound
  have dm : d*s₄ ≤ mix K := by
    apply le_of_mul_le_mul_left (a := t) _ ht
    linarith only [show t*(d*s₄) ≤ t*mix K by
      calc t*(d*s₄) = d*t*s₄ := by ring
           _ ≤ _ := J.trans bound]
  linarith only [mul_le_mul_of_nonneg_right dlow h4pos,dm]

#print axioms mixed_bound
lemma determinant_pos {K : Set Plane} (hc : IsCompact K) {v : ℝ}
    (hv : 0 < v) (h : radialBound K 1 v) :
    0 < avg K (fun x => x.1^2)*avg K (fun x => x.2^2) -
      (avg K (fun x => x.1*x.2))^2 := by
  let a := avg K (fun x => x.1^2)
  let b := avg K (fun x => x.1*x.2)
  let c := avg K (fun x => x.2^2)
  change 0 < a*c-b^2
  have H (u t : ℝ) (ht : 0<t) : t*v ≤ a+2*u*b+(u^2+t^2)*c := by
    have e : 1*(u^2+t^2)-u^2=t^2 := by ring
    have h' := h 1 u (u^2+t^2) (by norm_num) (e.symm ▸ sq_pos_of_pos ht)
    simp only [e,pow_one,Real.sqrt_sq ht.le] at h'
    simpa [a,b,c,quadratic_integral K hc] using h'
  have ha : 0 ≤ a := integral_nonneg (fun _ => sq_nonneg _)
  have hc0 : 0 ≤ c := integral_nonneg (fun _ => sq_nonneg _)
  have hcpos : 0 < c := by
    by_contra! hh
    have hz : c=0 := le_antisymm hh hc0
    have hh' := H 0 ((a+1)/v) (div_pos (by linarith) hv)
    rw [hz, div_mul_cancel₀ _ hv.ne'] at hh'
    linarith
  have hh := H (-b/c) (v/(2*c)) (div_pos hv (by positivity))
  have tidy : (v/(2*c))*v - (a+2*(-b/c)*b+((-b/c)^2+(v/(2*c))^2)*c) =
      (v^2-4*(a*c-b^2))/(4*c) := by field_simp; ring
  have hn : (v^2-4*(a*c-b^2))/(4*c) ≤ 0 := tidy ▸ sub_nonpos.mpr hh
  have hp := (div_le_iff₀ (by positivity : 0<4*c)).mp hn
  nlinarith only [hp, sq_pos_of_pos hv]

lemma moment_nonneg (K : Set Plane) (k : ℕ) : 0 ≤ moment K k :=
  integral_nonneg (fun x => pow_nonneg (add_nonneg (sq_nonneg x.1) (sq_nonneg x.2)) _)

/-- Quantitative reduction. It retains the full sixth radial moment surplus. -/
theorem energy_gap (K : Set Plane) (hc : IsCompact K)
    (sym : ∀ x : Plane, -x ∈ K ↔ x ∈ K) (area : avg K (fun _ => 1) = 1)
    {s₂ s₄ : ℝ} (h₂ : radialBound K 1 s₂) (h₄ : radialBound K 2 s₄)
    (h2p : 0<s₂) (h4p : 0≤s₄) :
    2*moment K 3 + 18*s₂*s₄ ≤ energy K := by
  rw [energy_expand K hc sym area]
  have hmix := mixed_bound K hc s₂ s₄ h₂ h₄ h4p (determinant_pos hc h2p h₂)
  have hm := mul_le_mul (radial_identity h₂) (radial_identity h₄) h4p (moment_nonneg K 1)
  linarith only [hm,hmix]

/-- Isotropic means that the second-moment matrix at the origin is scalar. -/
def Isotropic (R : Set Plane) : Prop :=
  avg R (fun x => x.1^2) = avg R (fun x => x.2^2) ∧ avg R (fun x => x.1*x.2) = 0

theorem reference_energy (R : Set Plane) (hc : IsCompact R)
    (sym : ∀ x : Plane, -x ∈ R ↔ x ∈ R) (area : avg R (fun _ => 1) = 1)
    (iso : Isotropic R) :
    energy R = 2*moment R 3 + 18*moment R 1*moment R 2 := by
  rw [energy_expand R hc sym area]
  obtain ⟨hdiag,hcross⟩ := iso
  let c := avg R (fun x => x.2^2)
  have htr : moment R 1 = 2*c := by
    simp (disch := fun_prop) only [moment, pow_one, r, avg_add R hc, hdiag]
    dsimp [c]; ring
  have mixeq : mix R = c*moment R 2 := by
    unfold mix
    rw [hdiag,hcross]
    change avg R (fun x => r x*(c*x.1^2+2*0*x.1*x.2+c*x.2^2)) = _
    rw [show (fun x : Plane => r x*(c*x.1^2+2*0*x.1*x.2+c*x.2^2)) =
          (fun x => c*r x^2) by funext x; dsimp [r]; ring, avg_mul]
    rfl
  rw [mixeq,htr]; ring

/-- The remaining geometric input is expressed by lower bounds on single integrals. -/
theorem energy_comparison {K R : Set Plane} (kc : IsCompact K) (rc : IsCompact R)
    (ks : ∀ x : Plane, -x ∈ K ↔ x ∈ K) (rs : ∀ x : Plane, -x ∈ R ↔ x ∈ R)
    (ka : avg K (fun _ => 1) = 1) (ra : avg R (fun _ => 1) = 1)
    (ri : Isotropic R) (rp : 0 < moment R 1)
    (h₂ : radialBound K 1 (moment R 1)) (h₄ : radialBound K 2 (moment R 2))
    (h₆ : moment R 3 ≤ moment K 3) :
    energy R ≤ energy K ∧ (energy R = energy K → moment R 3 = moment K 3) := by
  have bound := energy_gap K kc ks ka h₂ h₄ rp (moment_nonneg R 2)
  rw [reference_energy R rc rs ra ri]
  constructor
  · linarith
  · intro eq; linarith

#print axioms energy_comparison

/-- A determinant-one linear change preserves the actual area integral on the image. -/
theorem avg_linear_image (K : Set Plane) (L : Plane →ₗ[ℝ] Plane) (hL : L.det = 1)
    (f : Plane → ℝ) : avg (L '' K) f = avg K (fun x => f (L x)) := by
  have hn : L.det ≠ 0 := by rw [hL]; norm_num
  letI : (volume : Measure Plane).IsAddHaarMeasure :=
    inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod volume))
  have hmp : MeasurePreserving L volume volume := by
    refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hn, hL]
    simp
  let e := (L.equivOfDetNeZero hn).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  exact hmp.setIntegral_image_emb e.measurableEmbedding f K

/-- Radial comparison on area-preserving linear images implies every quadratic-form test. -/
theorem radialBound_of_linear_images (K : Set Plane) (k : ℕ) (v : ℝ)
    (h : ∀ L : Plane →ₗ[ℝ] Plane, L.det = 1 → v ≤ moment (L '' K) k) :
    radialBound K k v := by
  intro a b c ha hab
  let d := Real.sqrt (a*c-b^2)
  let t := Real.sqrt (a/d)
  let u := b/(d*t)
  have hd : 0<d := Real.sqrt_pos.2 hab
  have ht : 0<t := Real.sqrt_pos.2 (div_pos ha hd)
  have hd2 : d^2=a*c-b^2 := Real.sq_sqrt hab.le
  have ht2 : t^2=a/d := Real.sq_sqrt (div_pos ha hd).le
  have ha' : d*t^2=a := by rw [ht2]; field_simp
  have hb' : d*t*u=b := by dsimp [u]; field_simp
  have hc' : d*(u^2+(t⁻¹)^2)=c := by
    apply mul_left_cancel₀ (show d*t^2 ≠ 0 by positivity)
    calc (d*t^2)*(d*(u^2+(t⁻¹)^2)) = (d*t*u)^2+d^2 := by field_simp; ring
         _ = _ := by rw [hb', ha', hd2]; ring
  let L := Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ) !![t,u;0,t⁻¹]
  have hL : L.det=1 := by simp [L, LinearMap.det_toLin, Matrix.det_fin_two, ht.ne']
  have hform (x : Plane) : form a b c x = d*r (L x) := by
    simp only [L, Matrix.toLin_finTwoProd_apply, zero_mul, zero_add, form, r]
    linear_combination -x.1^2*ha' - 2*x.1*x.2*hb' - x.2^2*hc'
  have H := h L hL
  unfold moment at H
  rw [avg_linear_image K L hL] at H
  simp_rw [hform, mul_pow, avg_mul]
  exact mul_le_mul_of_nonneg_left H (pow_nonneg hd.le k)

#print axioms radialBound_of_linear_images

def disk (s : ℝ) : Set Plane := {x | r x ≤ s}

lemma disk_measurable (s : ℝ) : MeasurableSet (disk s) :=
  measurableSet_le r_cont.measurable measurable_const

lemma radial_nonneg (x : Plane) : 0 ≤ r x := add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Disk radii are encoded by their squares. -/
def DiskDominates (R K : Set Plane) : Prop :=
  ∀ s : ℝ, 0 ≤ s → volume (K ∩ disk s) ≤ volume (R ∩ disk s)

lemma radial_tail_le {R K : Set Plane} (rc : IsCompact R) (kc : IsCompact K)
    (mass : volume R = volume K) (dom : DiskDominates R K) (k : ℕ) (hk : k ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) :
    volume.restrict R {x | t < r x ^ k} ≤ volume.restrict K {x | t < r x ^ k} := by
  let s := t ^ (k⁻¹ : ℝ)
  have hs : 0 ≤ s := Real.rpow_nonneg ht _
  have hst : s^k=t := Real.rpow_inv_natCast_pow ht hk
  have he : {x : Plane | t < r x ^ k} = (disk s)ᶜ := by
    ext x
    change (t < r x ^ k) ↔ ¬ r x ≤ s
    rw [← hst, pow_lt_pow_iff_left₀ hs (radial_nonneg x) hk, not_le]
  have aux (S : Set Plane) (sc : IsCompact S) :
      volume.restrict S (disk s)ᶜ = volume S - volume (S ∩ disk s) := by
    rw [measure_compl (disk_measurable s), Measure.restrict_apply_univ,
      Measure.restrict_apply (disk_measurable s), inter_comm]
    rw [Measure.restrict_apply (disk_measurable s)]
    exact ne_top_of_le_ne_top sc.measure_lt_top.ne (measure_mono inter_subset_right)
  rw [he, aux R rc, aux K kc, mass]
  exact tsub_le_tsub_left (dom s hs) _

/-- Integration of the tails transfers the disk overlap inequality to all positive even moments. -/
theorem moment_le_of_diskDominates {R K : Set Plane} (rc : IsCompact R) (kc : IsCompact K)
    (mass : volume R = volume K) (dom : DiskDominates R K) (k : ℕ) (hk : k ≠ 0) :
    moment R k ≤ moment K k := by
  let f (x : Plane) := r x ^ k
  have hf : Continuous f := r_cont.pow k
  have fn (x : Plane) : 0 ≤ f x := pow_nonneg (radial_nonneg x) _
  have repr (S : Set Plane) :
      moment S k = (∫⁻ t in Ioi (0:ℝ), volume.restrict S {x | t < f x}).toReal := by
    unfold moment avg
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fn) hf.aestronglyMeasurable,
      lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall fn) hf.aemeasurable]
  rw [repr R, repr K]
  apply ENNReal.toReal_mono
  · rw [← lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall fn) hf.aemeasurable]
    exact (hf.continuousOn.integrableOn_compact kc).lintegral_lt_top.ne
  · apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
    exact radial_tail_le rc kc mass dom k hk t (le_of_lt ht)

lemma first_moment_pos (R : Set Plane) (rc : IsCompact R)
    (area : avg R (fun _ => 1) = 1) : 0 < moment R 1 := by
  have mass : volume.real R = 1 := by simpa [avg] using area
  have pos : 0 < volume R := by
    apply pos_iff_ne_zero.mpr
    intro h
    simp [Measure.real, h] at mass
  have hs : Function.support r ∩ R = R \ {(0 : Plane)} := by
    ext x
    simp only [Function.mem_support, mem_inter_iff, mem_diff, mem_singleton_iff]
    have hz : r x = 0 ↔ x = 0 := by
      constructor
      · intro h
        dsimp [r] at h
        apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;>
          nlinarith [sq_nonneg x.1, sq_nonneg x.2]
      · rintro rfl; norm_num [r]
    tauto
  simp only [moment, pow_one, avg]
  apply (setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall radial_nonneg)
    (r_cont.continuousOn.integrableOn_compact rc)).2
  letI : (volume : Measure Plane).IsAddHaarMeasure :=
    inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod volume))
  rwa [hs, measure_diff_null (measure_singleton (0 : Plane))]

/-- A planar rotation with nonzero sine forces an invariant region's second moment to be scalar. -/
def rotation (p q : ℝ) : Plane →ₗ[ℝ] Plane :=
  Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ) !![p,-q;q,p]

theorem isotropic_of_rotation (R : Set Plane) (rc : IsCompact R) {p q : ℝ}
    (unit : p^2+q^2=1) (hq : q ≠ 0) (inv : rotation p q '' R = R) : Isotropic R := by
  let a := avg R (fun x => x.1^2)
  let b := avg R (fun x => x.1*x.2)
  let c := avg R (fun x => x.2^2)
  have det : (rotation p q).det=1 := by
    simp [rotation,LinearMap.det_toLin,Matrix.det_fin_two]
    nlinarith only [unit]
  have test (f : Plane → ℝ) : avg R f = avg R (fun x => f (rotation p q x)) := by
    simpa only [inv] using avg_linear_image R (rotation p q) det f
  have sqtest := test (fun x => x.1^2)
  have prodtest := test (fun x => x.1*x.2)
  have e1 (x : Plane) : (rotation p q x).1^2 = form (p^2) (-p*q) (q^2) x := by
    simp [rotation,form]; ring
  have e2 (x : Plane) : (rotation p q x).1*(rotation p q x).2 =
      form (p*q) ((p^2-q^2)/2) (-p*q) x := by simp [rotation,form]; ring
  simp only [e1, quadratic_integral R rc] at sqtest
  simp only [e2, quadratic_integral R rc] at prodtest
  change a = p^2*a + 2*(-p*q)*b + q^2*c at sqtest
  change b = (p*q)*a + 2*((p^2-q^2)/2)*b + (-p*q)*c at prodtest
  have E : q*(a-c)+2*p*b=0 := by
    apply mul_left_cancel₀ hq
    linear_combination a*unit + sqtest
  have F : p*(a-c)-2*q*b=0 := by
    apply mul_left_cancel₀ hq
    linear_combination -b*unit - prodtest
  change a = c ∧ b = 0
  constructor
  · linear_combination q*E+p*F-(a-c)*unit
  · linear_combination (p*E-q*F)/2-b*unit

theorem energy_of_disk_comparison {K R : Set Plane} (kc : IsCompact K) (rc : IsCompact R)
    (ks : ∀ x : Plane, -x ∈ K ↔ x ∈ K) (rs : ∀ x : Plane, -x ∈ R ↔ x ∈ R)
    (ka : avg K (fun _ => 1) = 1) (ra : avg R (fun _ => 1) = 1)
    (ri : Isotropic R)
    (dom : ∀ L : Plane →ₗ[ℝ] Plane, L.det = 1 → DiskDominates R (L '' K)) :
    2*(moment K 3 - moment R 3) ≤ energy K - energy R ∧ energy R ≤ energy K := by
  have mass : volume R = volume K := by
    have h : volume.real R = volume.real K := by simpa [avg] using ra.trans ka.symm
    exact (ENNReal.toReal_eq_toReal rc.measure_lt_top.ne kc.measure_lt_top.ne).mp h
  have H (k : ℕ) (hk : k ≠ 0) (L : Plane →ₗ[ℝ] Plane) (hL : L.det = 1) :
      moment R k ≤ moment (L '' K) k := by
    letI : (volume : Measure Plane).IsAddHaarMeasure :=
      inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod volume))
    have he : volume (L '' K) = volume K := by
      rw [Measure.addHaar_image_linearMap, hL]; simp
    exact moment_le_of_diskDominates rc (kc.image L.continuous_of_finiteDimensional)
      (mass.trans he.symm) (dom L hL) k hk
  have h₂ := radialBound_of_linear_images K 1 _ (H 1 one_ne_zero)
  have h₄ := radialBound_of_linear_images K 2 _ (H 2 (by decide))
  have h₆ : moment R 3 ≤ moment K 3 := by
    simpa using H 3 (by decide) LinearMap.id (by simp)
  have gap := energy_gap K kc ks ka h₂ h₄ (first_moment_pos R rc ra) (moment_nonneg R 2)
  rw [reference_energy R rc rs ra ri]
  constructor <;> linarith

#print axioms energy_of_disk_comparison

/-- Vertices of a centered regular polygon with 2m sides and circumradius ρ. -/
def vertex (m : ℕ) (ρ : ℝ) (i : ℕ) : Plane :=
  (ρ * Real.cos ((i:ℝ)*(Real.pi/m)), ρ * Real.sin ((i:ℝ)*(Real.pi/m)))

def regularPolygon (m : ℕ) (ρ : ℝ) : Set Plane := convexHull ℝ (range (vertex m ρ))

lemma vertex_opposite {m : ℕ} (hm : 0<m) (ρ : ℝ) (i : ℕ) :
    vertex m ρ (i+m) = -vertex m ρ i := by
  have hn : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have e : ((i:ℝ)+m)*(Real.pi/m) = i*(Real.pi/m)+Real.pi := by field_simp; ring
  simp [vertex, Nat.cast_add, e, Real.cos_add_pi, Real.sin_add_pi]

lemma vertex_periodic {m : ℕ} (hm : 0<m) (ρ : ℝ) : Function.Periodic (vertex m ρ) (2*m) := by
  intro i
  rw [show i+2*m=i+m+m by omega, vertex_opposite hm, vertex_opposite hm, neg_neg]

lemma compact_regular {m : ℕ} (hm : 0<m) (ρ : ℝ) : IsCompact (regularPolygon m ρ) := by
  apply Set.Finite.isCompact_convexHull
  apply (Set.finite_range (fun i : Fin (2*m) => vertex m ρ i)).subset
  rintro _ ⟨i,rfl⟩
  exact ⟨⟨i%(2*m), Nat.mod_lt _ (by omega)⟩, (vertex_periodic hm ρ).map_mod_nat i⟩

lemma symmetric_regular {m : ℕ} (hm : 0<m) (ρ : ℝ) (x : Plane) :
    -x ∈ regularPolygon m ρ ↔ x ∈ regularPolygon m ρ := by
  let L : Plane →ₗ[ℝ] Plane := -LinearMap.id
  have e : L '' range (vertex m ρ) = range (vertex m ρ) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i+m, vertex_opposite hm ρ i⟩
    · rintro _ ⟨i,rfl⟩
      exact ⟨_,⟨i+m,rfl⟩, by change -vertex m ρ (i+m) = _; rw [vertex_opposite hm, neg_neg]⟩
  have inv : L '' regularPolygon m ρ = regularPolygon m ρ := by
    unfold regularPolygon; rw [L.image_convexHull, e]
  have forward (y : Plane) (hy : y ∈ regularPolygon m ρ) : -y ∈ regularPolygon m ρ := by
    rw [← inv]; exact ⟨y,hy,rfl⟩
  exact ⟨fun h => neg_neg x ▸ forward (-x) h, forward x⟩

lemma isotropic_regular {m : ℕ} (hm : 2≤m) (ρ : ℝ) : Isotropic (regularPolygon m ρ) := by
  let θ := Real.pi/m
  have hm0 : 0<m := by omega
  have θpos : 0<θ := div_pos Real.pi_pos (by exact_mod_cast hm0)
  have θlt : θ<Real.pi := by
    dsimp [θ]
    exact div_lt_self Real.pi_pos (by exact_mod_cast (show 1<m by omega))
  let L := rotation (Real.cos θ) (Real.sin θ)
  have step (i : ℕ) : L (vertex m ρ i) = vertex m ρ (i+1) := by
    simp only [L, rotation, Matrix.toLin_finTwoProd_apply, vertex, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul, Real.cos_add, Real.sin_add, θ]
    apply Prod.ext <;> dsimp <;> ring
  apply isotropic_of_rotation _ (compact_regular hm0 ρ) (Real.cos_sq_add_sin_sq θ)
    (Real.sin_pos_of_pos_of_lt_pi θpos θlt).ne'
  change L '' convexHull ℝ _ = _
  rw [L.image_convexHull]
  apply congrArg (convexHull ℝ)
  apply Set.Subset.antisymm
  · rintro _ ⟨_,⟨i,rfl⟩,rfl⟩; exact ⟨i+1,(step i).symm⟩
  · rintro _ ⟨i,rfl⟩
    refine ⟨_,⟨i+(2*m-1),rfl⟩,?_⟩
    rw [step, show i+(2*m-1)+1=i+2*m by omega, vertex_periodic hm0 ρ i]

/-- Geometric specialization. The disk overlap hypothesis is the published geometric input. -/
theorem regular_polygon_energy {m : ℕ} (hm : 2≤m) {ρ : ℝ} {K : Set Plane}
    (kc : IsCompact K) (ks : ∀ x : Plane, -x ∈ K ↔ x ∈ K)
    (ka : avg K (fun _ => 1) = 1) (ra : avg (regularPolygon m ρ) (fun _ => 1) = 1)
    (overlap : ∀ L : Plane →ₗ[ℝ] Plane, L.det = 1 →
      DiskDominates (regularPolygon m ρ) (L '' K)) :
    energy (regularPolygon m ρ) ≤ energy K ∧
      (energy (regularPolygon m ρ) = energy K →
        moment (regularPolygon m ρ) 3 = moment K 3) := by
  have ⟨gap, bound⟩ := energy_of_disk_comparison kc (compact_regular (by omega) ρ)
    ks (symmetric_regular (by omega) ρ) ka ra (isotropic_regular hm ρ) overlap
  have id_dom : DiskDominates (regularPolygon m ρ) K := by
    simpa using overlap LinearMap.id (by simp)
  have mass : volume (regularPolygon m ρ) = volume K := by
    apply (ENNReal.toReal_eq_toReal (compact_regular (by omega) ρ).measure_lt_top.ne
      kc.measure_lt_top.ne).mp
    simpa [avg] using ra.trans ka.symm
  have mono := moment_le_of_diskDominates (compact_regular (by omega) ρ) kc mass id_dom 3 (by decide)
  exact ⟨bound, fun h => by linarith⟩

#print axioms regular_polygon_energy

/-- Equal positive radial moments under disk dominance determine all exterior tail areas. -/
theorem equal_radial_tails {R K : Set Plane} (rc : IsCompact R) (kc : IsCompact K)
    (mass : volume R = volume K) (dom : DiskDominates R K) {k : ℕ} (hk : k ≠ 0)
    (eq : moment R k = moment K k) (a : ℝ) (ha : 0≤a) :
    volume.restrict R {x | a < r x^k} = volume.restrict K {x | a < r x^k} := by
  let f (x : Plane) := r x^k
  let T (t : ℝ) := {x : Plane | t < f x}
  let A (S : Set Plane) (t : ℝ) := volume.restrict S (T t)
  let I (S : Set Plane) := ∫⁻ t in Ioi (0:ℝ), A S t
  have hf : Continuous f := r_cont.pow k
  have nn (x : Plane) : 0 ≤ f x := pow_nonneg (radial_nonneg x) k
  have repr (S : Set Plane) : I S = ∫⁻ x in S, ENNReal.ofReal (f x) := by
    exact (lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall nn) hf.aemeasurable).symm
  have finite (S : Set Plane) (sc : IsCompact S) : I S ≠ ⊤ := by
    rw [repr]; exact (hf.continuousOn.integrableOn_compact sc).lintegral_lt_top.ne
  have val (S : Set Plane) : (I S).toReal = moment S k := by
    rw [repr]; exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall nn)
      hf.aestronglyMeasurable).symm
  have e : I R = I K := (ENNReal.toReal_eq_toReal (finite R rc) (finite K kc)).mp
    ((val R).trans (eq.trans (val K).symm))
  have mono (S : Set Plane) : Antitone (A S) := fun _ _ h =>
    measure_mono (fun _ hx => lt_of_le_of_lt h hx)
  have ae : A R =ᵐ[volume.restrict (Ioi (0:ℝ))] A K := by
    apply ae_eq_of_ae_le_of_lintegral_le _ (finite R rc) (mono K).measurable.aemeasurable e.ge
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
    exact radial_tail_le rc kc mass dom k hk t (le_of_lt ht)
  have sample (n : ℕ) : ∃ t ∈ Ioo a (a+1/(n+1:ℝ)), A R t = A K t := by
    apply Measure.exists_mem_of_measure_ne_zero_of_ae (μ := (volume : Measure ℝ))
    · simp [Real.volume_Ioo, ENNReal.ofReal_ne_zero_iff]; positivity
    · apply ae_restrict_of_ae_restrict_of_subset _ ae
      exact fun t h => lt_of_le_of_lt ha h.1
  choose u hu heq using sample
  have union : (⋃ n, T (u n)) = T a := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n,hn⟩; exact lt_trans (hu n).1 hn
    · intro hx
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show 0 < f x-a from sub_pos.mpr hx)
      exact ⟨n, (hu n).2.trans (by linarith)⟩
  have directed : Directed (· ⊆ ·) (fun n => T (u n)) := by
    intro i j
    rcases le_total (u i) (u j) with h | h
    · exact ⟨i, Subset.rfl, fun _ hx => lt_of_le_of_lt h hx⟩
    · exact ⟨j, fun _ hx => lt_of_le_of_lt h hx, Subset.rfl⟩
  change volume.restrict R (T a) = volume.restrict K (T a)
  rw [← union, directed.measure_iUnion, directed.measure_iUnion]
  exact iSup_congr heq

theorem equal_disk_overlaps {R K : Set Plane} (rc : IsCompact R) (kc : IsCompact K)
    (mass : volume R = volume K) (dom : DiskDominates R K) {k : ℕ} (hk : k ≠ 0)
    (eq : moment R k = moment K k) (s : ℝ) (hs : 0≤s) :
    volume (R ∩ disk s) = volume (K ∩ disk s) := by
  let T := {x : Plane | s^k < r x^k}
  have comp : Tᶜ = disk s := by
    ext x; change (¬ s^k < r x^k) ↔ r x ≤ s
    rw [not_lt, pow_le_pow_iff_left₀ (radial_nonneg x) hs hk]
  have mt : MeasurableSet T := measurableSet_lt measurable_const (r_cont.pow k).measurable
  have aux (S : Set Plane) (sc : IsCompact S) :
      volume (S ∩ disk s) = volume S - volume.restrict S T := by
    rw [inter_comm, ← Measure.restrict_apply (disk_measurable s), ← comp,
      measure_compl mt, Measure.restrict_apply_univ]
    rw [Measure.restrict_apply mt]
    exact ne_top_of_le_ne_top sc.measure_lt_top.ne (measure_mono inter_subset_right)
  rw [aux R rc, aux K kc, mass, equal_radial_tails rc kc mass dom hk eq _ (pow_nonneg hs k)]

/-- If R contains a centered disk, moment equality forces K to contain its open interior. -/
theorem open_disk_subset_of_equal_moment {R K : Set Plane} (rc : IsCompact R) (kc : IsCompact K)
    (mass : volume R = volume K) (dom : DiskDominates R K) {k : ℕ} (hk : k ≠ 0)
    (eq : moment R k = moment K k) {s : ℝ} (hs : 0≤s) (inside : disk s ⊆ R) :
    {x : Plane | r x < s} ⊆ K := by
  have overlaps := equal_disk_overlaps rc kc mass dom hk eq s hs
  rw [inter_eq_self_of_subset_right inside] at overlaps
  have hn : volume (disk s \ (K ∩ disk s)) = 0 := by
    rw [measure_diff inter_subset_right (kc.measurableSet.inter (disk_measurable s)).nullMeasurableSet
      (ne_top_of_le_ne_top kc.measure_lt_top.ne (measure_mono inter_subset_left)), overlaps, tsub_self]
  let U := {x : Plane | r x < s} \ K
  have null : volume U = 0 := by
    apply measure_mono_null (s := U) _ hn
    intro x hx
    exact ⟨(show r x < s from hx.1).le, fun hi => hx.2 hi.1⟩
  have op : IsOpen U := (isOpen_lt r_cont continuous_const).sdiff kc.isClosed
  intro x hx
  by_contra hxK
  letI : (volume : Measure Plane).IsAddHaarMeasure :=
    inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod volume))
  exact (op.measure_pos volume ⟨x,hx,hxK⟩).ne' null

#print axioms open_disk_subset_of_equal_moment

/-- A convex hull of n labeled extreme vertices. Removing any vertex changes the hull. -/
def ConvexPolygonWith (n : ℕ) (K : Set Plane) : Prop :=
  ∃ v : Fin n → Plane, K = convexHull ℝ (range v) ∧
    ∀ i, v i ∉ convexHull ℝ (v '' {i}ᶜ)

lemma ConvexPolygonWith.compact {n K} (P : ConvexPolygonWith n K) : IsCompact K := by
  obtain ⟨v,rfl,_⟩ := P
  exact (Set.finite_range v).isCompact_convexHull

lemma ConvexPolygonWith.linear_image {n K} (P : ConvexPolygonWith n K)
    (L : Plane →ₗ[ℝ] Plane) (hL : L.det = 1) : ConvexPolygonWith n (L '' K) := by
  obtain ⟨v,rfl,hv⟩ := P
  have hn : L.det ≠ 0 := by rw [hL]; norm_num
  have inj : Function.Injective L := (L.equivOfDetNeZero hn).injective
  refine ⟨L ∘ v, by rw [L.image_convexHull, range_comp], ?_⟩
  intro i h
  change L (v i) ∈ convexHull ℝ ((L ∘ v) '' {i}ᶜ) at h
  have images : (L ∘ v) '' {i}ᶜ = L '' (v '' {i}ᶜ) := (image_image L v _).symm
  rw [images, ← L.image_convexHull] at h
  exact hv i ((inj.mem_set_image).mp h)

/-- The centered disk case of the polygonal Hardy–Littlewood theorem, restricted to convex
polygons of area one. This named proposition is an explicit input, never an axiom. -/
def PolygonDiskComparison (m : ℕ) (ρ : ℝ) : Prop :=
  ∀ S : Set Plane, ConvexPolygonWith (2*m) S → avg S (fun _ => 1) = 1 →
    DiskDominates (regularPolygon m ρ) S

/-- For 2m-sided centrally symmetric convex polygons, the published disk comparison suffices
for energy minimization. Equality forces the complete centered disk-overlap profile to agree. -/
theorem centrally_symmetric_polygon_sixth_moment {m : ℕ} (hm : 2≤m) {ρ : ℝ}
    (ra : avg (regularPolygon m ρ) (fun _ => 1) = 1)
    (geom : PolygonDiskComparison m ρ)
    {K : Set Plane} (polygon : ConvexPolygonWith (2*m) K)
    (ks : ∀ x : Plane, -x ∈ K ↔ x ∈ K) (ka : avg K (fun _ => 1) = 1) :
    energy (regularPolygon m ρ) ≤ energy K ∧
      (energy (regularPolygon m ρ) = energy K → ∀ s : ℝ, 0≤s →
        volume (regularPolygon m ρ ∩ disk s) = volume (K ∩ disk s)) := by
  have dom (L : Plane →ₗ[ℝ] Plane) (hL : L.det = 1) :=
    geom (L '' K) (polygon.linear_image L hL) ((avg_linear_image K L hL (fun _ => 1)).trans ka)
  obtain ⟨lower, equal⟩ := regular_polygon_energy hm polygon.compact ks ka ra dom
  refine ⟨lower, fun he => ?_⟩
  have compact := compact_regular (show 0<m by omega) ρ
  have mass : volume (regularPolygon m ρ) = volume K := by
    apply (ENNReal.toReal_eq_toReal compact.measure_lt_top.ne polygon.compact.measure_lt_top.ne).mp
    simpa [avg] using ra.trans ka.symm
  exact equal_disk_overlaps compact polygon.compact mass (geom K polygon ka) (by decide : 3≠0)
    (equal he)

#print axioms centrally_symmetric_polygon_sixth_moment

open scoped Topology in
theorem disk_subset_of_open_disk_subset {s : ℝ} (hs : 0<s) {K : Set Plane} (kc : IsClosed K)
    (included : {x : Plane | r x < s} ⊆ K) : disk s ⊆ K := by
  intro x hx
  change r x ≤ s at hx
  have lim : Filter.Tendsto (fun t : ℝ => t • x) (𝓝[<] (1:ℝ)) (𝓝 x) := by
    simpa using (continuous_id.smul continuous_const : Continuous (fun t : ℝ => t • x)).continuousAt
      |>.tendsto.mono_left (nhdsWithin_le_nhds (a := (1:ℝ)) (s := Iio 1))
  apply kc.mem_of_tendsto lim
  have pos : ∀ᶠ t in 𝓝[<] (1:ℝ), 0<t := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  filter_upwards [pos, self_mem_nhdsWithin (s := Iio (1:ℝ)) (a := 1)] with t ht hlt
  apply included
  change r (t • x) < s
  have sc : r (t • x) = t^2*r x := by simp [r]; ring
  rw [sc]
  exact (mul_le_mul_of_nonneg_left hx (sq_nonneg t)).trans_lt
    (by have hpow : t^2<1 := by nlinarith [mul_pos ht (sub_pos.mpr (show t<1 from hlt))]
        nlinarith [mul_pos hs (sub_pos.mpr hpow)])

/-- Jensen's bound for the half-gaps between consecutive outward normals, with rigidity. -/
theorem tangent_sum_rigidity {n : ℕ} (hn : 0<n) (angle : Fin n → ℝ)
    (angles : ∀ i, angle i ∈ Ioo 0 (Real.pi/2)) (total : ∑ i, angle i = Real.pi) :
    (n:ℝ)*Real.tan (Real.pi/n) ≤ ∑ i, Real.tan (angle i) ∧
    ((n:ℝ)*Real.tan (Real.pi/n) = ∑ i, Real.tan (angle i) ↔ ∀ i, angle i = Real.pi/n) := by
  have wide {x : ℝ} (hx : x ∈ Ioo 0 (Real.pi/2)) : x ∈ Ioo (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [hx.1, Real.pi_pos],hx.2⟩
  have cv : StrictConvexOn ℝ (Ioo 0 (Real.pi/2)) Real.tan := by
    apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioo _ _) (Real.continuousOn_tan_Ioo.mono
      (fun _ hx => wide hx))
    rw [isOpen_Ioo.interior_eq]
    intro x hx y hy hxy
    rw [Real.deriv_tan, Real.deriv_tan]
    have hcos := Real.strictAntiOn_cos (show x ∈ Icc 0 Real.pi from
      ⟨hx.1.le, by linarith [hx.2, Real.pi_pos]⟩) (show y ∈ Icc 0 Real.pi from
      ⟨hy.1.le, by linarith [hy.2, Real.pi_pos]⟩) hxy
    have cy := Real.cos_pos_of_mem_Ioo (wide hy)
    apply one_div_lt_one_div_of_lt (sq_pos_of_pos cy)
    exact pow_lt_pow_left₀ hcos cy.le (by decide)
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  let w (_ : Fin n) : ℝ := (n:ℝ)⁻¹
  have wp (i : Fin n) (_ : i ∈ Finset.univ) : 0<w i := inv_pos.mpr hn'
  have wt : ∑ i, w i = 1 := by simp [w, hn'.ne']
  have avg_eq (f : Fin n → ℝ) : ∑ i, w i • f i = (∑ i, f i)/(n:ℝ) := by
    simp only [w, smul_eq_mul, ← Finset.mul_sum]; ring
  have h := cv.convexOn.map_sum_le (fun i hi => (wp i hi).le) wt (fun i _ => angles i)
  have e := cv.map_sum_eq_iff wp wt (fun i _ => angles i)
  simp only [avg_eq,total, Finset.mem_univ, forall_true_left] at h e
  constructor
  · simpa only [mul_comm] using (le_div_iff₀ hn').mp h
  · rw [← e, eq_div_iff hn'.ne']; ring_nf

#print axioms tangent_sum_rigidity

/-- Full-dimensional compact convex bodies cannot properly contain a closed subset of equal area. -/
theorem eq_of_nested_equal_area {Q K : Set Plane} (qc : IsClosed Q) (kc : IsCompact K)
    (cv : Convex ℝ K) (inc : Q ⊆ K) (positive : 0 < volume K) (mass : volume Q = volume K) :
    Q = K := by
  letI : (volume : Measure Plane).IsAddHaarMeasure :=
    inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod volume))
  have inner : (interior K).Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    have zero := cv.addHaar_frontier volume
    rw [frontier, kc.isClosed.closure_eq, he, diff_empty] at zero
    exact positive.ne' zero
  have null : volume (K \ Q) = 0 := by
    rw [measure_diff inc qc.measurableSet.nullMeasurableSet (mass.trans_ne kc.measure_lt_top.ne),
      mass, tsub_self]
  have sub : interior K ⊆ Q := by
    intro x hx
    by_contra hn
    exact ((isOpen_interior.sdiff qc).measure_pos volume ⟨x,hx,hn⟩).ne'
      (measure_mono_null (fun _ hy => ⟨interior_subset hy.1, hy.2⟩ : interior K \ Q ⊆ K \ Q) null)
  have h := closure_minimal sub qc
  rw [cv.closure_interior_eq_closure_of_nonempty_interior inner, kc.isClosed.closure_eq] at h
  exact inc.antisymm h

#print axioms eq_of_nested_equal_area

/-- A translation carries both integration variables and preserves the distance energy. -/
theorem energy_translate (K : Set Plane) (v : Plane) :
    energy ((fun x => x+v) '' K) = energy K := by
  let T (x : Plane) := x+v
  have mp : MeasurePreserving T volume volume :=
    (measurePreserving_add_right (volume : Measure ℝ) v.1).prod
      (measurePreserving_add_right (volume : Measure ℝ) v.2)
  have changeVars (f : Plane → ℝ) : avg (T '' K) f = avg K (fun x => f (T x)) :=
    mp.setIntegral_image_emb (MeasurableEquiv.addRight v).measurableEmbedding f K
  change avg (T '' K) (fun x => avg (T '' K) (fun y => r (x-y)^3)) = _
  rw [changeVars]
  apply congrArg (avg K)
  funext x
  rw [changeVars]
  simp only [T, add_sub_add_right_eq_sub]

theorem energy_rotate (K : Set Plane) {p q : ℝ} (unit : p^2+q^2=1) :
    energy (rotation p q '' K) = energy K := by
  let L := rotation p q
  have det : L.det = 1 := by
    simp [L,rotation,LinearMap.det_toLin,Matrix.det_fin_two]
    nlinarith only [unit]
  have normSq (x : Plane) : r (L x) = r x := by
    simp only [L,rotation,Matrix.toLin_finTwoProd_apply,r]
    linear_combination (x.1^2+x.2^2)*unit
  change avg (L '' K) (fun x => avg (L '' K) (fun y => r (x-y)^3)) = _
  rw [avg_linear_image K L det]
  apply congrArg (avg K)
  funext x
  rw [avg_linear_image K L det]
  simp only [← L.map_sub, normSq]

#print axioms energy_rotate
#print axioms energy_translate
end SixthMoment
