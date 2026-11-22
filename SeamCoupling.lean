import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Filter Topology

namespace Guevremont.SeamCoupling

noncomputable section

def critPt (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
def horizPt (t₀ σ : ℝ) : ℂ := (σ : ℂ) + (t₀ : ℂ) * I

lemma critPt_eq_horizPt (t₀ : ℝ) : critPt t₀ = horizPt t₀ (1 / 2) := by
  simp [critPt, horizPt]

lemma one_sub_conj_critPt (t : ℝ) : 1 - starRingEnd ℂ (critPt t) = critPt t := by
  apply Complex.ext
  · simp [critPt]; norm_num
  · simp [critPt]

theorem im_eq_zero_on_critical_line (ξ : ℂ → ℂ)
    (h_mirror : ∀ s : ℂ, ξ (1 - starRingEnd ℂ s) = starRingEnd ℂ (ξ s)) (t : ℝ) :
    (ξ (critPt t)).im = 0 := by
  have h := h_mirror (critPt t)
  rw [one_sub_conj_critPt] at h
  have him := congrArg Complex.im h
  simp at him
  linarith

lemma hasDerivAt_critPt (t₀ : ℝ) : HasDerivAt critPt I t₀ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) t₀ := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I t₀ := by
    simpa using h1.mul_const I
  exact h2.const_add (1 / 2 : ℂ)

lemma hasDerivAt_horizPt (t₀ σ₀ : ℝ) : HasDerivAt (horizPt t₀) 1 σ₀ := by
  have h1 : HasDerivAt (fun σ : ℝ => (σ : ℂ)) (1 : ℂ) σ₀ := Complex.ofRealCLM.hasDerivAt
  exact h1.add_const ((t₀ : ℂ) * I)

theorem orthogonal_gradient_transfer {ξ : ℂ → ℂ} {t₀ : ℝ} {d : ℂ}
    (h_diff : HasDerivAt ξ d (critPt t₀))
    (h_mirror : ∀ s : ℂ, ξ (1 - starRingEnd ℂ s) = starRingEnd ℂ (ξ s)) :
    HasDerivAt (fun σ : ℝ => (ξ (horizPt t₀ σ)).re) 0 (1 / 2 : ℝ) ∧
    HasDerivAt (fun σ : ℝ => (ξ (horizPt t₀ σ)).im)
      (-deriv (fun t : ℝ => (ξ (critPt t)).re) t₀) (1 / 2 : ℝ) := by
  have h_vert := h_diff.scomp t₀ (hasDerivAt_critPt t₀)
  simp only [smul_eq_mul] at h_vert
  have h_vert_re : HasDerivAt (fun t : ℝ => (ξ (critPt t)).re) (I * d).re t₀ :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t₀ h_vert
  have h_vert_im : HasDerivAt (fun t : ℝ => (ξ (critPt t)).im) (I * d).im t₀ :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t₀ h_vert
  have h_im_zero : (fun t : ℝ => (ξ (critPt t)).im) = fun _ => (0 : ℝ) := by
    funext t; exact im_eq_zero_on_critical_line ξ h_mirror t
  have h_im_deriv0 : HasDerivAt (fun t : ℝ => (ξ (critPt t)).im) 0 t₀ := by
    rw [h_im_zero]; exact hasDerivAt_const t₀ (0 : ℝ)
  have hd_re : d.re = 0 := by
    have huniq := h_vert_im.unique h_im_deriv0
    simpa [Complex.mul_im] using huniq
  have hd_im : d.im = -deriv (fun t : ℝ => (ξ (critPt t)).re) t₀ := by
    have hder := h_vert_re.deriv
    simp [Complex.mul_re] at hder
    linarith
  have hdiff' : HasDerivAt ξ d (horizPt t₀ (1 / 2)) := by rwa [← critPt_eq_horizPt]
  have h_horiz := hdiff'.scomp (1 / 2 : ℝ) (hasDerivAt_horizPt t₀ (1 / 2))
  simp only [smul_eq_mul, one_mul] at h_horiz
  have h_horiz_re : HasDerivAt (fun σ : ℝ => (ξ (horizPt t₀ σ)).re) d.re (1 / 2 : ℝ) :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt (1 / 2 : ℝ) h_horiz
  have h_horiz_im : HasDerivAt (fun σ : ℝ => (ξ (horizPt t₀ σ)).im) d.im (1 / 2 : ℝ) :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt (1 / 2 : ℝ) h_horiz
  rw [hd_re] at h_horiz_re
  rw [hd_im] at h_horiz_im
  exact ⟨h_horiz_re, h_horiz_im⟩

theorem local_transverse_wobble_bound {ξ : ℂ → ℂ} {t₀ : ℝ} {d : ℂ}
    (h_diff : HasDerivAt ξ d (critPt t₀))
    (h_mirror : ∀ s : ℂ, ξ (1 - starRingEnd ℂ s) = starRingEnd ℂ (ξ s))
    (h_simple : deriv (fun t : ℝ => (ξ (critPt t)).re) t₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ σ : ℝ, |σ - 1 / 2| < δ →
        (1 / 2) * |deriv (fun t : ℝ => (ξ (critPt t)).re) t₀| * |σ - 1 / 2| ≤
          |(ξ (horizPt t₀ σ)).im| := by
  set L : ℝ := -deriv (fun t : ℝ => (ξ (critPt t)).re) t₀
  have hL_ne : L ≠ 0 := neg_ne_zero.mpr h_simple
  have hL_pos : 0 < |L| := abs_pos.mpr hL_ne
  have h_im_deriv : HasDerivAt (fun σ : ℝ => (ξ (horizPt t₀ σ)).im) L (1 / 2 : ℝ) :=
    (orthogonal_gradient_transfer h_diff h_mirror).2
  have h0 : (ξ (horizPt t₀ (1 / 2))).im = 0 := by
    rw [← critPt_eq_horizPt]; exact im_eq_zero_on_critical_line ξ h_mirror t₀
  have ho := (hasDerivAt_iff_isLittleO.mp h_im_deriv).bound (by positivity : 0 < |L| / 2)
  rw [Metric.eventually_nhds_iff] at ho
  rcases ho with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun σ hσ => ?_⟩
  have hdist : dist σ (1 / 2) < δ := by simpa [Real.dist_eq] using hσ
  have hbound := hδ hdist
  rw [h0, sub_zero, smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs] at hbound
  have htri : |(σ - 1 / 2) * L| - |(ξ (horizPt t₀ σ)).im| ≤
      |(ξ (horizPt t₀ σ)).im - (σ - 1 / 2) * L| := by
    simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub ((σ - 1 / 2) * L) (ξ (horizPt t₀ σ)).im
  have hmul : |(σ - 1 / 2) * L| = |L| * |σ - 1 / 2| := by rw [abs_mul, mul_comm]
  have hLabs : |L| = |deriv (fun t : ℝ => (ξ (critPt t)).re) t₀| := abs_neg _
  rw [hLabs] at hbound hmul
  have hhalf : |deriv (fun t : ℝ => (ξ (critPt t)).re) t₀| / 2 * |σ - 1 / 2| =
      (1 / 2) * |deriv (fun t : ℝ => (ξ (critPt t)).re) t₀| * |σ - 1 / 2| := by ring
  linarith

theorem local_off_axis_zero_exclusion {ξ : ℂ → ℂ} {t₀ : ℝ} {d : ℂ}
    (h_diff : HasDerivAt ξ d (critPt t₀))
    (h_mirror : ∀ s : ℂ, ξ (1 - starRingEnd ℂ s) = starRingEnd ℂ (ξ s))
    (h_simple : deriv (fun t : ℝ => (ξ (critPt t)).re) t₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ σ : ℝ, σ ≠ 1 / 2 → |σ - 1 / 2| < δ → ξ (horizPt t₀ σ) ≠ 0 := by
  rcases local_transverse_wobble_bound h_diff h_mirror h_simple with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun σ hne hlt hz => ?_⟩
  have hpos : 0 < (1 / 2) * |deriv (fun t : ℝ => (ξ (critPt t)).re) t₀| * |σ - 1 / 2| := by
    have h1 : 0 < |deriv (fun t : ℝ => (ξ (critPt t)).re) t₀| := abs_pos.mpr h_simple
    have h2 : 0 < |σ - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
    positivity
  have hle := hδ σ hlt
  rw [hz] at hle
  simp at hle
  linarith

def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) + (s * (s - 1) / 2) * completedRiemannZeta₀ s

lemma riemannXi_eq_mul_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    riemannXi s = (s * (s - 1) / 2) * completedRiemannZeta s := by
  rw [completedRiemannZeta_eq, riemannXi]
  have h1' : 1 - s ≠ 0 := sub_ne_zero.mpr h1.symm
  field_simp [h0, h1']
  ring

theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  unfold riemannXi
  have hpoly : Differentiable ℂ (fun s : ℂ => s * (s - 1) / 2) :=
    ((differentiable_id.mul (differentiable_id.sub (differentiable_const 1))).div_const 2)
  exact (differentiable_const (1 / 2 : ℂ)).add (hpoly.mul differentiable_completedZeta₀)

theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

lemma nat_cpow_conj (n : ℕ) {s : ℂ} (hs : s ≠ 0) :
    (n : ℂ) ^ (starRingEnd ℂ s) = starRingEnd ℂ ((n : ℂ) ^ s) := by
  by_cases hn : n = 0
  · subst hn
    have hsc : starRingEnd ℂ s ≠ 0 := by simpa using hs
    simp [Complex.zero_cpow hs, Complex.zero_cpow hsc]
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_conj]
    congr 1
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
    rw [map_mul, hlog, Complex.conj_ofReal]

lemma riemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
  have hsc : 1 < (starRingEnd ℂ s).re := by simpa using hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  rw [zeta_eq_tsum_one_div_nat_cpow hsc, zeta_eq_tsum_one_div_nat_cpow hs, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rw [map_div₀, map_one, nat_cpow_conj n hs0]

lemma gammaR_conj (s : ℂ) :
    (starRingEnd ℂ s).Gammaℝ = starRingEnd ℂ s.Gammaℝ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  congr 1
  · have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [Complex.cpow_def_of_ne_zero hpi, Complex.cpow_def_of_ne_zero hpi, ← Complex.exp_conj]
    congr 1
    rw [map_mul, ← Complex.ofReal_log Real.pi_pos.le, Complex.conj_ofReal]
    simp [map_div₀, map_neg, map_ofNat]
  · have hdiv : starRingEnd ℂ s / 2 = starRingEnd ℂ (s / 2) := by simp [map_div₀, map_ofNat]
    rw [hdiv, Complex.Gamma_conj]

lemma completedRiemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta s) := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have h0c : starRingEnd ℂ s ≠ 0 := by simpa using h0
  have hΓ : s.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΓc : (starRingEnd ℂ s).Gammaℝ ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using (by linarith : (0 : ℝ) < s.re))
  have hΛ : completedRiemannZeta s = riemannZeta s * s.Gammaℝ :=
    ((eq_div_iff hΓ).mp (riemannZeta_def_of_ne_zero h0)).symm
  have hΛc : completedRiemannZeta (starRingEnd ℂ s) =
      riemannZeta (starRingEnd ℂ s) * (starRingEnd ℂ s).Gammaℝ :=
    ((eq_div_iff hΓc).mp (riemannZeta_def_of_ne_zero h0c)).symm
  rw [hΛc, hΛ, map_mul, riemannZeta_conj_of_one_lt_re hs, gammaR_conj]

lemma riemannXi_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (riemannXi s) := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have h0c : starRingEnd ℂ s ≠ 0 := by simpa using h0
  have h1c : starRingEnd ℂ s ≠ 1 := by
    intro h; apply h1; simpa using congrArg (starRingEnd ℂ) h
  rw [riemannXi_eq_mul_completedRiemannZeta h0c h1c,
      riemannXi_eq_mul_completedRiemannZeta h0 h1,
      completedRiemannZeta_conj_of_one_lt_re hs]
  simp [map_div₀, map_mul, map_sub, map_ofNat]

lemma hasDerivAt_conj_conj {f : ℂ → ℂ} {z f' : ℂ}
    (hf : HasDerivAt f f' (starRingEnd ℂ z)) :
    HasDerivAt (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ f') z := by
  rw [hasDerivAt_iff_tendsto] at hf ⊢
  have hmap : Tendsto (starRingEnd ℂ) (𝓝 z) (𝓝 (starRingEnd ℂ z)) :=
    Complex.continuous_conj.continuousAt
  refine (hf.comp hmap).congr fun w => ?_
  simp only [Function.comp_apply, smul_eq_mul]
  have hnorm : ‖starRingEnd ℂ w - starRingEnd ℂ z‖ = ‖w - z‖ := by
    rw [← map_sub, Complex.norm_conj]
  have hnorm2 : ‖f (starRingEnd ℂ w) - f (starRingEnd ℂ z) - (starRingEnd ℂ w - starRingEnd ℂ z) * f'‖ =
      ‖starRingEnd ℂ (f (starRingEnd ℂ w)) - starRingEnd ℂ (f (starRingEnd ℂ z)) -
        (w - z) * starRingEnd ℂ f'‖ := by
    rw [← Complex.norm_conj]
    congr 1
    simp [map_sub, map_mul]
  rw [hnorm, hnorm2]

theorem riemannXi_conj (s : ℂ) :
    riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (riemannXi s) := by
  let g : ℂ → ℂ := fun z => starRingEnd ℂ (riemannXi (starRingEnd ℂ z))
  have hg_diff : Differentiable ℂ g := fun z =>
    (hasDerivAt_conj_conj (differentiable_riemannXi (starRingEnd ℂ z)).hasDerivAt).differentiableAt
  have hf_an : AnalyticOnNhd ℂ riemannXi Set.univ :=
    differentiable_riemannXi.differentiableOn.analyticOnNhd isOpen_univ
  have hg_an : AnalyticOnNhd ℂ g Set.univ :=
    hg_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hev : g =ᶠ[𝓝 (2 : ℂ)] riemannXi := by
    have hopen : IsOpen {z : ℂ | (1 : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {z : ℂ | (1 : ℝ) < z.re} := by norm_num
    filter_upwards [hopen.mem_nhds hmem] with z hz
    dsimp [g]
    rw [riemannXi_conj_of_one_lt_re hz, Complex.conj_conj]
  have heq := hg_an.eqOn_of_preconnected_of_eventuallyEq hf_an isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev (Set.mem_univ s)
  have hres := congrArg (starRingEnd ℂ) heq
  simpa [g] using hres

theorem riemannXi_mirror (s : ℂ) :
    riemannXi (1 - starRingEnd ℂ s) = starRingEnd ℂ (riemannXi s) := by
  rw [riemannXi_one_sub, riemannXi_conj]

theorem riemannXi_eq_zero_iff_riemannZeta_eq_zero {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at h0; norm_num at h0
  have hs1 : s ≠ 1 := by intro h; rw [h] at h1; norm_num at h1
  have hΓ : s.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
  have hpoly : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num)
  have hΛ : completedRiemannZeta s = riemannZeta s * s.Gammaℝ :=
    ((eq_div_iff hΓ).mp (riemannZeta_def_of_ne_zero hs0)).symm
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1, hΛ]
  simp [hpoly, hΓ]

theorem riemannXi_orthogonal_gradient_transfer (t₀ : ℝ) :
    HasDerivAt (fun σ : ℝ => (riemannXi (horizPt t₀ σ)).re) 0 (1 / 2 : ℝ) ∧
    HasDerivAt (fun σ : ℝ => (riemannXi (horizPt t₀ σ)).im)
      (-deriv (fun t : ℝ => (riemannXi (critPt t)).re) t₀) (1 / 2 : ℝ) :=
  orthogonal_gradient_transfer (differentiable_riemannXi (critPt t₀)).hasDerivAt riemannXi_mirror

theorem riemannXi_local_off_axis_zero_exclusion (t₀ : ℝ)
    (h_simple : deriv (fun t : ℝ => (riemannXi (critPt t)).re) t₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ σ : ℝ, σ ≠ 1 / 2 → |σ - 1 / 2| < δ → riemannXi (horizPt t₀ σ) ≠ 0 :=
  local_off_axis_zero_exclusion
    (differentiable_riemannXi (critPt t₀)).hasDerivAt riemannXi_mirror h_simple

theorem riemannZeta_local_off_axis_zero_exclusion (t₀ : ℝ)
    (h_simple : deriv (fun t : ℝ => (riemannXi (critPt t)).re) t₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ σ : ℝ, 0 < σ → σ < 1 → σ ≠ 1 / 2 → |σ - 1 / 2| < δ →
        riemannZeta (horizPt t₀ σ) ≠ 0 := by
  rcases riemannXi_local_off_axis_zero_exclusion t₀ h_simple with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun σ h0 h1 hne hlt hz => ?_⟩
  have hre0 : 0 < (horizPt t₀ σ).re := by simpa [horizPt] using h0
  have hre1 : (horizPt t₀ σ).re < 1 := by simpa [horizPt] using h1
  exact hδ σ hne hlt ((riemannXi_eq_zero_iff_riemannZeta_eq_zero hre0 hre1).mpr hz)

end

#print axioms riemannXi_orthogonal_gradient_transfer
#print axioms riemannXi_local_off_axis_zero_exclusion
#print axioms riemannZeta_local_off_axis_zero_exclusion

end Guevremont.SeamCoupling
