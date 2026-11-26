#!/usr/bin/env python3
"""Regenerate the certified data of the CMS (22/25) proof.

The pipeline (run from `scripts/cms/`, numpy and scipy needed; sympy for `final_poly.py`):

  1. python3 design2.py 8 8 15,16,17
       LP for the weight: 16 piecewise-linear knots each side, gap of 8 knots, Brun–Titchmarsh
       constant 4, left-Riemann pieces with 8 sub-pieces. Writes design_M8_j8.json (kept here);
       J = 1.1569, so 1/J = 0.8644 < 22/25.
  2. python3 cells.py design_M8_j8.json 0.006 120 6e-5 cells_d.json
       theta-cells on [0, 120] for the step majorant of the per-zero bound.
  3. python3 gen2.py design_M8_j8.json cells_d.json data_d.json
       exact integer data: phi at scale 2^20, Q's Chebyshev coefficients, cell entries
       (scales 2^20, 2^64, 2^40).
  4. python3 emitw.py data_d.json ../../CramerCompute/CMSData 10
     python3 emitagg.py data_d.json ../../CramerCompute/CMSAll.lean 10
       the 708 window modules (11 entries each, sharing boundary entries) and the glue module.
  5. python3 consts.py data_d.json consts_d.json   (the normalised zero-sum constants)
     python3 crude.py                               (the margin model for x >= 10^8)
     python3 final_poly.py                          (the polynomial of Cramer.CMS.final_poly)

The prime chain below 10^8 is generated separately by scripts/cms_chain.py.
"""
import sys
print(__doc__)
sys.exit(0)
