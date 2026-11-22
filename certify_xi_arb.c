#include <stdio.h>
#include <flint/acb.h>
#include <flint/acb_dirichlet.h>

int main(void) {
    slong prec = 128;
    int N = 64, ok = 1;
    acb_t s_box, xi_box;
    arb_t x0, x1, y0, y1, abs_xi, bound, min_lo;

    acb_init(s_box); acb_init(xi_box);
    arb_init(x0); arb_init(x1); arb_init(y0); arb_init(y1);
    arb_init(abs_xi); arb_init(bound); arb_init(min_lo);

    arb_set_si(bound, 2); arb_div_ui(bound, bound, 5, prec); /* 2/5 = 0.4 */
    arb_set_si(min_lo, 100);

    for (int i = 0; i < N; i++) {
        /* Re(s) in [3/5 + i/(5N), 3/5 + (i+1)/(5N)] */
        arb_set_si(x0, 3 * N + i);     arb_div_ui(x0, x0, 5 * N, prec);
        arb_set_si(x1, 3 * N + i + 1); arb_div_ui(x1, x1, 5 * N, prec);
        arb_union(acb_realref(s_box), x0, x1, prec);

        for (int j = 0; j < N; j++) {
            /* Im(s) in [9/10 + 2j/(10N), 9/10 + 2(j+1)/(10N)] */
            arb_set_si(y0, 9 * N + 2 * j);     arb_div_ui(y0, y0, 10 * N, prec);
            arb_set_si(y1, 9 * N + 2 * j + 2); arb_div_ui(y1, y1, 10 * N, prec);
            arb_union(acb_imagref(s_box), y0, y1, prec);

            acb_dirichlet_xi(xi_box, s_box, prec);
            acb_abs(abs_xi, xi_box, prec);

            if (!arb_gt(abs_xi, bound)) ok = 0;
            arb_min(min_lo, min_lo, abs_xi, prec);
        }
    }

    printf("Grid: %dx%d (%d sub-boxes covering R = [3/5,4/5] x [9/10,11/10])\n", N, N, N*N);
    printf("Rigorous lower enclosure of min |xi(s)| on R: ");
    arb_printn(min_lo, 10, 0); printf("\n");
    printf("Certified |xi(s)| > 2/5 for ALL s in R: %s\n",
           ok ? "TRUE (VERIFIED)" : "FALSE");

    acb_clear(s_box); acb_clear(xi_box);
    arb_clear(x0); arb_clear(x1); arb_clear(y0); arb_clear(y1);
    arb_clear(abs_xi); arb_clear(bound); arb_clear(min_lo);
    return 0;
}
