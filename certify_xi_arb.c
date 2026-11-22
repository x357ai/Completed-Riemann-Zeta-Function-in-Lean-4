/*
 * Copyright 2026 Barry Lee Guevremont
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <flint/acb.h>
#include <flint/acb_dirichlet.h>

int main(void) {
    const slong prec = 128;
    const int N = 64, max_diagnostics = 8;
    int ok = 1, have_min = 0;
    int invalid_boxes = 0, failed_boxes = 0, diagnostics_shown = 0;
    acb_t s_box, xi_box;
    arb_t x0, x1, y0, y1, abs_xi, bound, min_interval;

    acb_init(s_box); acb_init(xi_box);
    arb_init(x0); arb_init(x1); arb_init(y0); arb_init(y1);
    arb_init(abs_xi); arb_init(bound); arb_init(min_interval);

    arb_set_si(bound, 2); arb_div_ui(bound, bound, 5, prec); /* 2/5 = 0.4 */

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
            if (!acb_is_finite(xi_box)) {
                ok = 0;
                invalid_boxes++;
                if (diagnostics_shown < max_diagnostics) {
                    fprintf(stderr, "Box (%d,%d): non-finite xi enclosure; NOT CERTIFIED.\n", i, j);
                    diagnostics_shown++;
                }
                continue;
            }

            acb_abs(abs_xi, xi_box, prec);
            if (!arb_is_finite(abs_xi)) {
                ok = 0;
                invalid_boxes++;
                if (diagnostics_shown < max_diagnostics) {
                    fprintf(stderr, "Box (%d,%d): non-finite modulus enclosure; NOT CERTIFIED.\n", i, j);
                    diagnostics_shown++;
                }
                continue;
            }

            /* A failed comparison is inconclusive, not a disproof of the bound. */
            if (!arb_gt(abs_xi, bound)) {
                ok = 0;
                failed_boxes++;
                if (diagnostics_shown < max_diagnostics) {
                    fprintf(stderr, "Box (%d,%d): modulus enclosure ", i, j);
                    arb_fprintn(stderr, abs_xi, 10, 0);
                    fprintf(stderr, " does not certify > 2/5; NOT CERTIFIED.\n");
                    diagnostics_shown++;
                }
            }

            /* Include every finite enclosure, even if its comparison failed. */
            if (!have_min) {
                arb_set(min_interval, abs_xi);
                have_min = 1;
            } else {
                arb_min(min_interval, min_interval, abs_xi, prec);
            }
        }
    }

    if (invalid_boxes + failed_boxes > diagnostics_shown) {
        fprintf(stderr, "Further uncertified-box diagnostics omitted: %d.\n",
                invalid_boxes + failed_boxes - diagnostics_shown);
    }

    printf("Grid: %dx%d (%d sub-boxes covering R = [3/5,4/5] x [9/10,11/10])\n", N, N, N*N);
    printf("Working precision: %ld bits\n", (long) prec);
    printf("Boxes: %d certified, %d finite but not certified, %d invalid.\n",
           N*N - failed_boxes - invalid_boxes, failed_boxes, invalid_boxes);
    if (have_min && invalid_boxes == 0) {
        /* The printed ball encloses the minimum; its midpoint is not a lower bound. */
        printf("Enclosure of min |xi(s)| on R (midpoint +/- radius): ");
        arb_printn(min_interval, 10, 0); printf("\n");
    } else {
        printf("Enclosure of min |xi(s)| on R: unavailable (incomplete finite evaluation).\n");
    }
    printf("Certified |xi(s)| > 2/5 for ALL s in R: %s\n",
           ok ? "TRUE (VERIFIED)" : "NOT CERTIFIED");

    acb_clear(s_box); acb_clear(xi_box);
    arb_clear(x0); arb_clear(x1); arb_clear(y0); arb_clear(y1);
    arb_clear(abs_xi); arb_clear(bound); arb_clear(min_interval);
    return ok ? 0 : 1;
}
