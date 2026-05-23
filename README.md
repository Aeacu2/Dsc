# Dsc: Faster Verified Real Root Isolation with Descartes' Rule of Signs

This repository contains an Isabelle/HOL formalization of real root isolation algorithms based on Descartes' Rule of Signs. Real root isolation is a fundamental subroutine in computer algebra, but most existing formally verified procedures rely on Sturm's theorem. We take an initial step toward efficient verified real root isolation using Descartes' Rule of Signs by verifying a classical bisection procedure (`dsc`) and a Newton-accelerated variant (`newdsc`). 

The verification was completed in Isabelle 2025(March 2025) with AFP 2025, which can be downloaded at https://isabelle.in.tum.de/download_past.html and https://foss.heptapod.net/isa-afp/afp-2025 
We also checked the compatibility with the newest version of Isabelle (2025-2) and its accompanying AFP 2025-2.

## How to Build

Please install Isabelle 2025-2 or Isasbelle 2025 (March 2025) with their corresponding Archives of Formal Proofs configured. 

To check all definitions and proofs, run the following command in the base directory of this repository (where the `ROOT` file is located):

`isabelle build -v -D .`

This can take pretty long. If it times out, please double the timeout in ROOT and try again. 

Alternatively, to only check the termination, soundness, and completeness proofs for `dsc` and `newdsc`, remove `Dsc_Bern`, `Dsc_Exec`, `Dsc_Rat`,  `Dsc_Taylor`, and `Dsc_Int` under `theories` in the ROOT file. Then run the command above. This should be much faster.

To run the experiments, use Poly/ML 5.9.2 (which comes with Isabelle 2025-2) or Poly/ML 5.9.1 (which comes with Isabelle 2025) with the following command:

`poly --use bench_gen.sml --use bench_main.sml`

To save time, it might make sense to remove P3 and M(32, 32) from bench_gen.sml

## High-Level Structure

Files corresponding to the paper sections:
1. **Formalising The Classical Bisection Algorithm:  `Dsc_Bern.thy`, `Dsc_Misc.thy` and `Dsc.thy`** Formalizing the base `dsc` bisection algorithm and relying on the Theorem of Three Circles to guarantee termination.
2. **Formalising Newtonian Acceleration (Completeness proof requires importing the split lemma): `NewDsc.thy`** Formalizing the `newdsc` algorithm, which accelerates convergence to tight clusters of roots by attempting block selection and Newton windows before falling back to bisection. 
3. **Completeness via de Casteljau (Proof of the splitting lemma): `Triangle.thy`, `List_Changes.thy`, and `Bernstein_Split.thy`** Developing a substantial library for the De Casteljau algorithm on Bernstein coefficients to prove the crucial splitting lemma, justifying the discarding of intervals in the Newton-accelerated method.
4. **Code Generation & Benchmarking: `Dsc_Exec.thy`, `Dsc_Rat.thy`, `Dsc_Taylor.thy`, `Dsc_Int.thy`, `Sturm_Isolate.thy`, and `Bench_Export.thy`** Optimizing algorithm efficiency by decomposing the root test and eliminating fractions, then extracting tail-recursive functions and benchmarking them against existing verified Sturm-sequence algorithms using both random and tightly clustered polynomials.

## File Descriptions
* **`Dsc_Bern.thy`**: Proves the equivalence between Li's direct formalization of Descartes' root test and Thompson's formalization using the Bernstein basis.
* **`Dsc_Misc.thy`**: Packages the Theorem of Three Circles to show that the sign variation of a square-free real polynomial eventually becomes 1 or 0, crucial for termination.
* **`Dsc.thy`**: Formalizes the classical bisection algorithm `dsc` as a partial function and proves its termination, soundness, and completeness.
* **`Triangle.thy`**: Formalizes the De Casteljau triangle construction and proves algebraic identities showing how the triangle computes Bernstein coefficients under subdivision.
* **`List_Changes.thy`**: Proves lemmas bounding coefficient sign changes, notably that the number of coefficient sign changes is subadditive with respect to the De Casteljau split.
* **`Bernstein_Split.thy`**: Combining the previous theories to prove the split lemma required for the completeness of `NewDsc`.
* **`NewDsc.thy`**: Formalizes the Newton-accelerated algorithm `newdsc` (including `try_blocks` and `try_newton`) and proves its termination, soundness, and completeness based on the De Casteljau splitting lemma.
* **`Dsc_Exec.thy`**: Defines partial tail-recursive versions of the algorithms (`dsc_exec` and `newdsc_exec`) suitable for code generation, proving their equivalence with the verified functions.
* **`Dsc_Rat.thy`**: Verifies a rational version of the Descartes root test, in preparation for the decomposition.
* **`Dsc_Taylor.thy`**: Decomposes the root test into modular steps, in preparation for eliminating fractions.
* **`Dsc_Int.thy`**: Eliminates fractions from the root test, verifying a fast integer-arithemetic versions (`dsc_int` and `newdsc_int`) of the algorithm.
* **`Sturm_Isolate.thy`**: Extracts the Sturm-based real root isolation function `isolate` developed by Joosten, Thiemann, and Yamada, customized to remove extra steps (like square-free factorization and packaging algebraic numbers) to ensure fair benchmarking.
* **`Bench_Export.thy`**: Exports `isolate`, `dsc_int`, `newdsc_int`, `dsc_exec`, and `newdsc_exec` to executable SML code (`bench_gen.sml`).
* **`bench_main.sml`**: Runs performance comparisons between the Descartes-based algorithms and the Sturm baseline, testing on irreducible polynomials on random and Mignotte-type polynomials. The coefficients for random polynomials tested can be found inside.
* **`Radical.thy`**: Defines and verifies radical operators for real and rational polynomials.
* **`Supplementary_Functions.thy`**: Includes functions that were not as fast as the main executable exports, as well as total functions obtained by wrapping `dsc` and `newdsc` with radical operators.

