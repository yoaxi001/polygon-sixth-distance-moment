import SixthMoment

open Set MeasureTheory
noncomputable section
namespace SixthMoment

def translate (v : Plane) (K : Set Plane) : Set Plane := (fun x => x+v) '' K

lemma mem_translate (v x : Plane) (K : Set Plane) : x ∈ translate v K ↔ x-v ∈ K := by
  constructor
  · rintro ⟨y,hy,rfl⟩; simpa using hy
  · exact fun h => ⟨x-v,h,sub_add_cancel _ _⟩

lemma translate_back (v : Plane) (K : Set Plane) : translate v (translate (-v) K) = K := by
  ext x
  simp only [mem_translate,sub_neg_eq_add,sub_add_cancel]

lemma area_translate (v : Plane) (K : Set Plane) :
    avg (translate v K) (fun _ => 1) = avg K (fun _ => 1) := by
  have mp : MeasurePreserving (fun x : Plane => x+v) volume volume :=
    (measurePreserving_add_right (volume : Measure ℝ) v.1).prod
      (measurePreserving_add_right (volume : Measure ℝ) v.2)
  exact mp.setIntegral_image_emb (MeasurableEquiv.addRight v).measurableEmbedding (fun _ => (1:ℝ)) K

lemma ConvexPolygonWith.translated {n K} (P : ConvexPolygonWith n K)
    (v : Plane) : ConvexPolygonWith n (translate v K) := by
  let e := AffineEquiv.constVAdd ℝ Plane v
  have eqv : (fun x : Plane => x+v) = e := by funext x; exact add_comm x v
  obtain ⟨w,rfl,hw⟩ := P
  unfold translate
  rw [eqv]
  have imageHull (S : Set Plane) : e '' convexHull ℝ S = convexHull ℝ (e '' S) :=
    e.toAffineMap.image_convexHull S
  refine ⟨e ∘ w,by rw [imageHull,range_comp],?_⟩
  intro i h
  have imageV : (e ∘ w) '' {i}ᶜ = e '' (w '' {i}ᶜ) := (image_image e w _).symm
  change e (w i) ∈ convexHull ℝ ((e ∘ w) '' {i}ᶜ) at h
  rw [imageV, ← imageHull] at h
  exact hw i (e.injective.mem_set_image.mp h)

lemma symmetric_after_centering {c : Plane} {K : Set Plane}
    (sym : ∀ x : Plane, c + (c-x) ∈ K ↔ x ∈ K) (x : Plane) :
    -x ∈ translate (-c) K ↔ x ∈ translate (-c) K := by
  simp only [mem_translate, sub_neg_eq_add]
  rw [show -x+c=c+(c-(x+c)) by abel]
  exact sym _

end SixthMoment
