;; -*- lexical-binding: t; -*-

(TeX-add-style-hook
 "submission_may_2026"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("sn-jnl" "pdflatex" "sn-mathphys-num")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("graphicx" "") ("multirow" "") ("amsmath" "") ("amssymb" "") ("amsfonts" "") ("amsthm" "") ("mathrsfs" "") ("appendix" "title") ("xcolor" "") ("textcomp" "") ("manyfoot" "") ("booktabs" "") ("bussproofs" "")))
   (TeX-run-style-hooks
    "latex2e"
    "sn-jnl"
    "sn-jnl10"
    "graphicx"
    "multirow"
    "amsmath"
    "amssymb"
    "amsfonts"
    "amsthm"
    "mathrsfs"
    "appendix"
    "xcolor"
    "textcomp"
    "manyfoot"
    "booktabs"
    "bussproofs")
   (TeX-add-symbols
    "nvdash")
   (LaTeX-add-labels
    "sec:intro"
    "claim1"
    "claim2"
    "eq:1"
    "eq:2"
    "sec:theorem"
    "thm:main"
    "sec:fragment"
    "tab:fragment"
    "rema1"
    "rema2"
    "eq:belnap-paradox"
    "sec:rules"
    "tab:dns"
    "sec:invertible"
    "point_i"
    "point_ii"
    "sec:antidns"
    "sec:contradiction"
    "sec:corollary"
    "cor:claim2"
    "sec:scope-reason"
    "sec:scope"
    "sec:reason"
    "secA1")
   (LaTeX-add-bibliographies
    "paper")
   (LaTeX-add-amsthm-newtheorems
    "theorem"
    "proposition"
    "example"
    "remark"
    "definition"))
 :latex)

