import MyMathProject.Basic
import SeamCoupling
import XiRectangleBound

namespace Guevremont

theorem riemannZeta_ne_zero_on_criticalStripBox_five {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (him : |s.im| ≤ 5) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hxi_zero : Guevremont.SeamCoupling.riemannXi s = 0 :=
    (Guevremont.SeamCoupling.riemannXi_eq_zero_iff_riemannZeta_eq_zero h0 h1).mpr hz
  have hxi_ne : Guevremont.XiRectangleBound.riemannXi s ≠ 0 :=
    Guevremont.XiRectangleBound.riemannXi_ne_zero_on_criticalStripBox_five
      ⟨h0.le, h1.le, him⟩
  exact hxi_ne hxi_zero

#print axioms riemannZeta_ne_zero_on_criticalStripBox_five

end Guevremont
