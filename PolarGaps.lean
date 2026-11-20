import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace SixthMoment

/-- If n closed angular arcs of half-width π/n cover the circle, their centers
are equally spaced, in the order given by a permutation of the original indices. -/
theorem polar_gaps_regular {n : ℕ} (hn : 0<n) (angle : Fin n → ℝ)
    (bounds : ∀ i, 0 ≤ angle i ∧ angle i < 2*Real.pi)
    (cover : ∀ t : ℝ, ∃ i : Fin n, ∃ z : ℤ,
      |angle i + (z:ℝ)*(2*Real.pi)-t| ≤ Real.pi/n) :
    ∃ (base : ℝ) (σ : Equiv.Perm (Fin n)),
      ∀ i : Fin n, angle (σ i) = base + (i:ℝ)*(2*Real.pi/n) := by
  let σ := Tuple.sort angle
  let f : Fin n → ℝ := angle ∘ σ
  let first : Fin n := ⟨0, hn⟩
  let base := f first
  let period := 2*Real.pi
  let d := period/n
  have hp : 0<period := mul_pos (by norm_num) Real.pi_pos
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have full : (n:ℝ)*d = period := by dsimp [d]; field_simp
  have sorted : Monotone f := Tuple.monotone_sort angle
  have lo (j : Fin n) : base ≤ f j := sorted (show first ≤ j from Nat.zero_le _)
  have bound (j : Fin n) : 0 ≤ f j ∧ f j < period := bounds (σ j)
  let g (i : ℕ) := if hi : i<n then f ⟨i,hi⟩ else base+period
  have g_at (i : ℕ) (hi : i<n) : g i = f ⟨i,hi⟩ := dif_pos hi
  have g_end : g n = base+period := dif_neg (lt_irrefl _)
  have g_start : g 0 = base := g_at 0 hn

  -- An angular lift lies outside each open gap, including the gap across zero.
  have outside (i : ℕ) (hi : i<n) (j : Fin n) (z : ℤ) :
      f j + (z:ℝ)*period ≤ g i ∨ g (i+1) ≤ f j + (z:ℝ)*period := by
    rw [g_at i hi]
    rcases lt_trichotomy z 0 with hz | rfl | hz
    · left
      have zle : (z:ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
      have hz' := mul_le_mul_of_nonneg_right zle hp.le
      linarith [(bound j).2, (bound ⟨i,hi⟩).1]
    · simp only [Int.cast_zero, zero_mul, add_zero]
      by_cases ji : j.val ≤ i
      · exact Or.inl (sorted (show j ≤ ⟨i,hi⟩ from ji))
      · have next : i+1<n := by omega
        rw [g_at _ next]
        exact Or.inr (sorted (show (⟨i+1,next⟩ : Fin n) ≤ j by change i+1 ≤ j.val; omega))
    · right
      have zge : 1 ≤ (z:ℝ) := by exact_mod_cast (show 1 ≤ z by omega)
      have hz' := mul_le_mul_of_nonneg_right zge hp.le
      by_cases next : i+1<n
      · rw [g_at _ next]; linarith [(bound ⟨i+1,next⟩).2,(bound j).1]
      · rw [show i+1=n by omega, g_end]; linarith [lo j]

  have gap (i : ℕ) (hi : i<n) : g (i+1) ≤ g i + d := by
    obtain ⟨u,z,h⟩ := cover ((g i + g (i+1))/2)
    let j := σ.symm u
    have hj : f j = angle u := by simp [f,j]
    rw [← hj] at h
    have hd : Real.pi/(n:ℝ) = d/2 := by dsimp [d,period]; ring
    rw [hd,abs_le] at h
    rcases outside i hi j z with hz | hz
    · dsimp [period] at hz; linarith [h.1]
    · dsimp [period] at hz; linarith [h.2]

  -- The total length is exactly n times the upper bound, so every increment attains it.
  have descent (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
      g j - (j:ℝ)*d ≤ g i - (i:ℝ)*d := by
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ j h ih =>
      have H := ih (by omega)
      have G := gap j (by omega)
      push_cast
      linarith
  refine ⟨base,σ,?_⟩
  intro i
  have H := descent 0 i.val (Nat.zero_le _) i.isLt.le
  have J := descent i.val n i.isLt.le le_rfl
  rw [g_start, g_at _ i.isLt] at H
  rw [g_end, full, g_at _ i.isLt] at J
  change f i = base + (i:ℝ)*d
  simpa using (show f i = base + (i:ℝ)*d by push_cast at H; linarith)

#print axioms polar_gaps_regular
end SixthMoment
