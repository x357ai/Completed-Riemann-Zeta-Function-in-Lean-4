import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Real MeasureTheory Set Filter
open scoped Topology

namespace Guevremont.XiRectangleBound

noncomputable section

def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) + (s * (s - 1) / 2) * completedRiemannZeta₀ s

def targetRect : Set ℂ :=
  {s : ℂ | (3 / 5 : ℝ) ≤ s.re ∧ s.re ≤ 4 / 5 ∧ (9 / 10 : ℝ) ≤ s.im ∧ s.im ≤ 11 / 10}

lemma poly_norm_le_four_fifths {s : ℂ} (hs : s ∈ targetRect) :
    ‖s * (s - 1) / 2‖ ≤ (4 / 5 : ℝ) := by
  rcases hs with ⟨hre_lo, hre_hi, him_lo, him_hi⟩
  have hnorm_s : ‖s‖ ^ 2 ≤ (37 / 20 : ℝ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have hnorm_s1 : ‖s - 1‖ ^ 2 ≤ (137 / 100 : ℝ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith
  have hprod_sq : ‖s * (s - 1)‖ ^ 2 ≤ (8 / 5 : ℝ) ^ 2 := by
    rw [norm_mul, mul_pow]
    nlinarith [sq_nonneg ‖s‖, sq_nonneg ‖s - 1‖]
  have hprod : ‖s * (s - 1)‖ ≤ (8 / 5 : ℝ) := by
    nlinarith [norm_nonneg (s * (s - 1))]
  rw [norm_div, Complex.norm_ofNat]
  linarith

lemma exp_neg_pi_lt : Real.exp (-Real.pi) ≤ (1 / 16 : ℝ) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have he : (2.7 : ℝ) < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    linarith
  have he3 : (16 : ℝ) ≤ Real.exp 3 := by
    have h1 : Real.exp 3 = (Real.exp 1) ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    nlinarith [sq_nonneg (Real.exp 1)]
  have hle : Real.exp 3 ≤ Real.exp Real.pi := Real.exp_le_exp.mpr hpi.le
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (he3.trans hle)

lemma xi_lower_bound_of_lambda_bound {s : ℂ} (hs : s ∈ targetRect)
    (hΛ : ‖completedRiemannZeta₀ s‖ ≤ (1 / 8 : ℝ)) :
    (2 / 5 : ℝ) ≤ ‖riemannXi s‖ := by
  unfold riemannXi
  have hpoly := poly_norm_le_four_fifths hs
  have hmul : ‖(s * (s - 1) / 2) * completedRiemannZeta₀ s‖ ≤ (1 / 10 : ℝ) := by
    rw [norm_mul]
    nlinarith [norm_nonneg (s * (s - 1) / 2), norm_nonneg (completedRiemannZeta₀ s)]
  have htri : ‖(1 / 2 : ℂ)‖ - ‖(s * (s - 1) / 2) * completedRiemannZeta₀ s‖ ≤
      ‖(1 / 2 : ℂ) + (s * (s - 1) / 2) * completedRiemannZeta₀ s‖ := by
    have h := norm_sub_norm_le (1 / 2 : ℂ) (-((s * (s - 1) / 2) * completedRiemannZeta₀ s))
    simpa [sub_neg_eq_add, norm_neg] using h
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  linarith

lemma sum_exp_sq_le_two_exp {x : ℝ} (hx : 1 ≤ x) :
    ∑' n : ℕ, Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * x) ≤ 2 * Real.exp (-Real.pi * x) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hr_pos : 0 ≤ Real.exp (-Real.pi * x) := (Real.exp_pos _).le
  have hr_lt : Real.exp (-Real.pi * x) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  have hterm : ∀ n : ℕ,
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * x) ≤
        Real.exp (-Real.pi * x) * (Real.exp (-Real.pi * x)) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hpx : 0 < Real.pi * x := mul_pos hpi (by linarith)
    push_cast
    nlinarith
  have hsum : Summable (fun n : ℕ => Real.exp (-Real.pi * x) * (Real.exp (-Real.pi * x)) ^ n) :=
    (summable_geometric_of_lt_one hr_pos hr_lt).mul_left _
  have hsum_sq : Summable (fun n : ℕ => Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * x)) :=
    Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hterm hsum
  calc ∑' n : ℕ, Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * x)
      ≤ ∑' n : ℕ, Real.exp (-Real.pi * x) * (Real.exp (-Real.pi * x)) ^ n :=
        hsum_sq.tsum_le_tsum hterm hsum
    _ = Real.exp (-Real.pi * x) * (1 - Real.exp (-Real.pi * x))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr_pos hr_lt]
    _ ≤ Real.exp (-Real.pi * x) * 2 := by
        apply mul_le_mul_of_nonneg_left _ hr_pos
        have hexp : Real.exp (-Real.pi * x) ≤ (1 / 2 : ℝ) := by
          have h1 : Real.exp (-Real.pi * x) ≤ Real.exp (-Real.pi) :=
            Real.exp_le_exp.mpr (by nlinarith)
          linarith [exp_neg_pi_lt]
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
    _ = 2 * Real.exp (-Real.pi * x) := by ring

lemma integral_exp_neg_pi_Ioi_one :
    ∫ x in Ioi (1 : ℝ), Real.exp (-Real.pi * x) = Real.exp (-Real.pi) / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : ∫ x in Ioi (1 : ℝ), Real.exp (-Real.pi * x) =
      (Real.exp (-Real.pi * 1)) / Real.pi := by
    have hderiv : ∀ x ∈ Ici (1 : ℝ),
        HasDerivAt (fun t => -Real.exp (-Real.pi * t) / Real.pi) (Real.exp (-Real.pi * x)) x := by
      intro x _
      have hd : HasDerivAt (fun t : ℝ => -Real.pi * t) (-Real.pi) x := by
        simpa using (hasDerivAt_id x).const_mul (-Real.pi)
      have he := (Real.hasDerivAt_exp (-Real.pi * x)).comp x hd
      have hneg := he.neg.div_const Real.pi
      simpa [mul_neg, neg_mul, neg_neg, mul_div_cancel_right₀ _ hpi.ne'] using hneg
    have htend : Tendsto (fun t : ℝ => -Real.exp (-Real.pi * t) / Real.pi) atTop (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => Real.exp (-Real.pi * t)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hpi))
      simpa using (h0.neg.div_const Real.pi)
    have hint := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
      (by
        exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hpi) 1))
      htend
    simpa [sub_neg_eq_add, neg_div, neg_neg] using hint
  simpa using h1

end



lemma norm_jacobiTheta_I_mul_sub_one_le {x : ℝ} (hx : 1 ≤ x) :
    ‖jacobiTheta (I * x) - 1‖ ≤ 4 * Real.exp (-Real.pi * x) := by
  have hx_pos : (0 : ℝ) < (I * x).im := by simp; linarith
  have h := norm_jacobiTheta_sub_one_le hx_pos
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_add] at h
  have hexp : Real.exp (-Real.pi * x) ≤ (1 / 2 : ℝ) := by
    have h1 : Real.exp (-Real.pi * x) ≤ Real.exp (-Real.pi) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith [exp_neg_pi_lt]
  have hdiv : 2 / (1 - Real.exp (-Real.pi * x)) ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  exact h.trans (mul_le_mul_of_nonneg_right hdiv (Real.exp_pos _).le)

lemma evenKernel_zero_eq_jacobiTheta (x : ℝ) :
    ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) = jacobiTheta (I * x) := by
  simpa [jacobiTheta, jacobiTheta₂, jacobiTheta₂_term] using HurwitzZeta.evenKernel_def 0 x

lemma cosKernel_zero_eq_jacobiTheta (x : ℝ) :
    ((HurwitzZeta.cosKernel 0 x : ℝ) : ℂ) = jacobiTheta (I * x) := by
  simpa [jacobiTheta, jacobiTheta₂, jacobiTheta₂_term] using HurwitzZeta.cosKernel_def 0 x

lemma norm_f_modif_Ioi_one {x : ℝ} (hx : 1 < x) :
    ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖ ≤ 4 * Real.exp (-Real.pi * x) := by
  have h1 : (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x = jacobiTheta (I * x) - 1 := by
    simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
      Set.indicator_of_mem (Set.mem_Ioi.mpr hx),
      Set.indicator_of_notMem (Set.notMem_Ioo_of_ge hx.le),
      evenKernel_zero_eq_jacobiTheta]
  rw [h1]
  exact norm_jacobiTheta_I_mul_sub_one_le hx.le

lemma norm_g_modif_Ioi_one {x : ℝ} (hx : 1 < x) :
    ‖(HurwitzZeta.hurwitzEvenFEPair 0).g_modif x‖ ≤ 4 * Real.exp (-Real.pi * x) := by
  have h1 : (HurwitzZeta.hurwitzEvenFEPair 0).g_modif x = jacobiTheta (I * x) - 1 := by
    simp [WeakFEPair.g_modif, HurwitzZeta.hurwitzEvenFEPair,
      Set.indicator_of_mem (Set.mem_Ioi.mpr hx),
      Set.indicator_of_notMem (Set.notMem_Ioo_of_ge hx.le),
      cosKernel_zero_eq_jacobiTheta]
  rw [h1]
  exact norm_jacobiTheta_I_mul_sub_one_le hx.le



lemma norm_mellin_Ioi_one_le {s : ℂ} (hs : s ∈ targetRect) :
    ‖∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s / 2 - 1) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖ ≤
      4 * Real.exp (-Real.pi) / Real.pi := by
  rcases hs with ⟨_, hre_hi, _, _⟩
  have hbound : ∀ x ∈ Ioi (1 : ℝ),
      ‖(x : ℂ) ^ (s / 2 - 1) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖ ≤
        4 * Real.exp (-Real.pi * x) := by
    intro x hx
    have hx_pos : (0 : ℝ) < x := by linarith [Set.mem_Ioi.mp hx]
    rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    have hre : (s / 2 - 1).re ≤ 0 := by
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]; linarith
    have hpow : x ^ (s / 2 - 1).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (Set.mem_Ioi.mp hx).le hre
    have hf := norm_f_modif_Ioi_one (Set.mem_Ioi.mp hx)
    nlinarith [norm_nonneg ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif x),
      Real.rpow_nonneg hx_pos.le (s / 2 - 1).re]
  have hint : IntegrableOn (fun x : ℝ => 4 * Real.exp (-Real.pi * x)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr Real.pi_pos) 1).const_mul 4
  calc ‖∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s / 2 - 1) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖
      ≤ ∫ x in Ioi (1 : ℝ), ‖(x : ℂ) ^ (s / 2 - 1) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi (1 : ℝ), 4 * Real.exp (-Real.pi * x) := by
        apply setIntegral_mono_on _ hint measurableSet_Ioi hbound
        let P := HurwitzZeta.hurwitzEvenFEPair 0
        have hm : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s / 2 - 1) • P.f_modif x) (Ioi 0) :=
          (P.isStrongFEPair_toStrongFEPair.hasMellin (s / 2)).1
        exact IntegrableOn.mono_set hm.norm (Set.Ioi_subset_Ioi zero_le_one)
    _ = 4 * Real.exp (-Real.pi) / Real.pi := by
        rw [integral_const_mul, integral_exp_neg_pi_Ioi_one, mul_div_assoc]

lemma norm_mellin_Ioo_zero_one_le {s : ℂ} (hs : s ∈ targetRect) :
    ‖∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (s / 2 - 1) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖ ≤
      4 * Real.exp (-Real.pi) / Real.pi := by
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  have hfold :
      (∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (s / 2 - 1) • P.f_modif x) =
      (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ ((1 - s) / 2 - 1) • P.g_modif t) := by
    have h1 : (∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (s / 2 - 1) • P.f_modif x) =
        mellin ((Ioo (0 : ℝ) 1).indicator P.f_modif) (s / 2) := by
      rw [mellin]
      have heq : (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • (Ioo (0 : ℝ) 1).indicator P.f_modif t) =
          (Ioo (0 : ℝ) 1).indicator (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • P.f_modif t) := by
        ext t; by_cases ht : t ∈ Ioo (0 : ℝ) 1 <;> simp [ht]
      rw [heq, setIntegral_indicator measurableSet_Ioo, Set.Ioi_inter_Ioo, max_self]
    rw [h1, ← neg_neg (s / 2), ← mellin_comp_inv, mellin]
    have h2 : ∀ t ∈ Ioi (0 : ℝ),
        (t : ℂ) ^ (-(s / 2) - 1) • ((Ioo (0 : ℝ) 1).indicator P.f_modif t⁻¹) =
        (Ioi (1 : ℝ)).indicator (fun t => (t : ℂ) ^ ((1 - s) / 2 - 1) • P.g_modif t) t := by
      intro t ht
      have ht_pos : 0 < t := Set.mem_Ioi.mp ht
      by_cases hgt : 1 < t
      · have hinv : t⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr ht_pos, inv_lt_one_of_one_lt₀ hgt⟩
        rw [Set.indicator_of_mem hinv, Set.indicator_of_mem (Set.mem_Ioi.mpr hgt)]
        have hfe := P.hf_modif_FE t ht_pos
        rw [one_div] at hfe
        rw [hfe]
        have hPε : P.ε = 1 := rfl
        have hPk : P.k = (1 / 2 : ℝ) := rfl
        rw [hPε, hPk, one_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
        congr 1
        rw [Complex.ofReal_cpow ht_pos.le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht_pos.ne')]
        congr 1; push_cast; ring
      · have hnot : t⁻¹ ∉ Ioo (0 : ℝ) 1 := by
          intro hmem
          exact hgt (by rw [← inv_inv t]; exact one_lt_inv_iff₀.mpr ⟨hmem.1, hmem.2⟩)
        rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem (Set.notMem_Ioi.mpr (not_lt.mp hgt)), smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi h2, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_left zero_le_one]
  rw [hfold]
  rcases hs with ⟨hre_lo, _, _, _⟩
  have hbound : ∀ t ∈ Ioi (1 : ℝ),
      ‖(t : ℂ) ^ ((1 - s) / 2 - 1) • P.g_modif t‖ ≤ 4 * Real.exp (-Real.pi * t) := by
    intro t ht
    have ht_pos : (0 : ℝ) < t := by linarith [Set.mem_Ioi.mp ht]
    rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
    have hre : ((1 - s) / 2 - 1).re ≤ 0 := by
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]; linarith
    have hpow : t ^ ((1 - s) / 2 - 1).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (Set.mem_Ioi.mp ht).le hre
    have hg := norm_g_modif_Ioi_one (Set.mem_Ioi.mp ht)
    nlinarith [norm_nonneg (P.g_modif t), Real.rpow_nonneg ht_pos.le ((1 - s) / 2 - 1).re]
  have hint : IntegrableOn (fun t : ℝ => 4 * Real.exp (-Real.pi * t)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr Real.pi_pos) 1).const_mul 4
  calc ‖∫ t in Ioi (1 : ℝ), (t : ℂ) ^ ((1 - s) / 2 - 1) • P.g_modif t‖
      ≤ ∫ t in Ioi (1 : ℝ), ‖(t : ℂ) ^ ((1 - s) / 2 - 1) • P.g_modif t‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (1 : ℝ), 4 * Real.exp (-Real.pi * t) := by
        apply setIntegral_mono_on _ hint measurableSet_Ioi hbound
        have hm : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((1 - s) / 2 - 1) • P.symm.f_modif t) (Ioi 0) :=
          (P.symm.isStrongFEPair_toStrongFEPair.hasMellin ((1 - s) / 2)).1
        exact IntegrableOn.mono_set hm.norm (Set.Ioi_subset_Ioi zero_le_one)
    _ = 4 * Real.exp (-Real.pi) / Real.pi := by
        rw [integral_const_mul, integral_exp_neg_pi_Ioi_one, mul_div_assoc]



lemma norm_completedRiemannZeta₀_le {s : ℂ} (hs : s ∈ targetRect) :
    ‖completedRiemannZeta₀ s‖ ≤ 1 / 8 := by
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  have hΛ : completedRiemannZeta₀ s = P.Λ₀ (s / 2) / 2 := rfl
  have hm := P.isStrongFEPair_toStrongFEPair.hasMellin (s / 2)
  have hsplit : P.Λ₀ (s / 2) =
      (∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (s / 2 - 1) • P.f_modif x) +
      (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s / 2 - 1) • P.f_modif x) := by
    have hΛeq : P.Λ₀ (s / 2) = mellin P.f_modif (s / 2) := rfl
    have hm1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s / 2 - 1) • P.f_modif x) (Ioi 0) := hm.1
    rw [hΛeq, mellin, ← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (IntegrableOn.mono_set hm1 Set.Ioc_subset_Ioi_self)
        (IntegrableOn.mono_set hm1 (Set.Ioi_subset_Ioi zero_le_one)),
      setIntegral_congr_set Ioo_ae_eq_Ioc.symm]
  have hnorm0 : ‖completedRiemannZeta₀ s‖ ≤ 4 * Real.exp (-Real.pi) / Real.pi := by
    rw [hΛ, norm_div, Complex.norm_ofNat, hsplit]
    have h1 := norm_mellin_Ioo_zero_one_le hs
    have h2 := norm_mellin_Ioi_one_le hs
    have hadd := norm_add_le
      (∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (s / 2 - 1) • P.f_modif x)
      (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s / 2 - 1) • P.f_modif x)
    linarith
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h13 : (13 : ℝ) ≤ Real.exp 3 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 4
    simp [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hexp : Real.exp (-Real.pi) ≤ 1 / 13 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (h13.trans (Real.exp_le_exp.mpr hpi.le))
  have hdiv : 4 * Real.exp (-Real.pi) / Real.pi ≤ 4 * (1 / 13) / 3 := by gcongr
  linarith

theorem riemannXi_ge_two_fifths_on_targetRect {s : ℂ} (hs : s ∈ targetRect) :
    (2 / 5 : ℝ) ≤ ‖(1 / 2 : ℂ) + s * (s - 1) / 2 * completedRiemannZeta₀ s‖ := by
  rcases hs with ⟨hre_lo, hre_hi, him_lo, him_hi⟩
  have hpoly : ‖s * (s - 1) / 2‖ ≤ 4 / 5 := by
    rw [norm_div, Complex.norm_ofNat]
    have hsq : ‖s * (s - 1)‖ ^ 2 ≤ (8 / 5 : ℝ) ^ 2 := by
      rw [norm_mul, mul_pow, Complex.sq_norm, Complex.sq_norm,
        Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
      have h1 : s.re * s.re + s.im * s.im ≤ 185 / 100 := by nlinarith
      have h2 : (s.re - 1) * (s.re - 1) + s.im * s.im ≤ 137 / 100 := by nlinarith
      have h1_nn : 0 ≤ s.re * s.re + s.im * s.im := by nlinarith
      have h2_nn : 0 ≤ (s.re - 1) * (s.re - 1) + s.im * s.im := by nlinarith
      nlinarith
    have hle : ‖s * (s - 1)‖ ≤ 8 / 5 := by nlinarith [norm_nonneg (s * (s - 1))]
    linarith
  have hζ := norm_completedRiemannZeta₀_le ⟨hre_lo, hre_hi, him_lo, him_hi⟩
  have hprod : ‖s * (s - 1) / 2 * completedRiemannZeta₀ s‖ ≤ 1 / 10 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (s * (s - 1) / 2), norm_nonneg (completedRiemannZeta₀ s)]
  have htri := norm_sub_norm_le (1 / 2 : ℂ) (-(s * (s - 1) / 2 * completedRiemannZeta₀ s))
  rw [sub_neg_eq_add, norm_neg] at htri
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  linarith

#print axioms riemannXi_ge_two_fifths_on_targetRect

end Guevremont.XiRectangleBound
