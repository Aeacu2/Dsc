# Dsc: Faster Verified Real Root Isolation with Descartes' Rule of Signs

This repository contains an Isabelle/HOL formalization of real root isolation algorithms based on Descartes' Rule of Signs. Real root isolation is a fundamental subroutine in computer algebra, but most existing formally verified procedures rely on Sturm's theorem. We take an initial step toward efficient verified real root isolation using Descartes' Rule of Signs by verifying a classical bisection procedure (`dsc`) and a Newton-accelerated variant (`newdsc`). 

The verification was completed in Isabelle 2025(March 2025), which can be downloaded at https://isabelle.in.tum.de/download_past.html

## How to Build

To check the proofs and generate the PDF proof document for this entry, install Isabelle 2025 with the Archive of Formal Proofs (AFP) configured. 

Run the following command in the base directory of this repository (where the `ROOT` file is located):

`isabelle build -v -D .`

The build took around 0:10:00 elapsed time and 0:45:00 cpu time on an Apple M4 CPU with 16G memory. If a build times out, please try doubling the timeout in ROOT.

To run the experiments, use Poly/ML 5.9.1 (which comes with Isabelle 2025) with the following command:

`poly --use bench_gen.sml --use bench_main.sml`

To save time, it might make sense to remove P3 and M(32, 32) from bench_gen.sml

## High-Level Structure

Files corresponding to the paper sections:
1. **Formalising The Classical Bisection Algorithm: `Dsc_Misc.thy` and `Dsc.thy`** Formalizing the base `dsc` bisection algorithm and relying on the Theorem of Three Circles to guarantee termination.
2. **Formalising Newtonian Acceleration (Completeness proof requires importing the split lemma): `NewDsc.thy`** Formalizing the `newdsc` algorithm, which accelerates convergence to tight clusters of roots by attempting block selection and Newton windows before falling back to bisection. 
3. **Completeness via De Casteljau (Proof of the split lemma): `Triangle.thy`, `List_Changes.thy`, and `Bernstein_Split.thy`** Developing a substantial library for the De Casteljau algorithm on Bernstein coefficients to prove the crucial splitting lemma, justifying the discarding of intervals in the Newton-accelerated method.
4. **Code Generation & Benchmarking: `Dsc_Bern.thy`, `Dsc_Exec.thy`, `Sturm_Isolate.thy`, and `Bench_Export.thy`** Extracting tail-recursive functions and benchmarking them against existing verified Sturm-sequence algorithms using both random and tightly clustered polynomials.

## File Descriptions
* **`Dsc_Misc.thy`**: Packages the Theorem of Three Circles to show that the sign variation of a square-free real polynomial eventually becomes 1 or 0, crucial for termination.
* **`Dsc.thy`**: Formalizes the classical bisection algorithm `dsc` as a partial function and proves its termination, soundness, and completeness.
* **`Triangle.thy`**: Formalizes the De Casteljau triangle construction and proves algebraic identities showing how the triangle computes Bernstein coefficients under subdivision.
* **`List_Changes.thy`**: Proves lemmas bounding coefficient sign changes, notably that the number of coefficient sign changes is subadditive with respect to the De Casteljau split.
* **`Bernstein_Split.thy`**: Combining the previous theories to prove the split lemma required for the completeness of `NewDsc`.
* **`NewDsc.thy`**: Formalizes the Newton-accelerated algorithm `newdsc` (including `try_blocks` and `try_newton`) and proves its termination, soundness, and completeness based on the De Casteljau splitting lemma.
* **`Dsc_Bern.thy`**: Proves the equivalence between Li's direct formalization of Descartes' root test and Thompson's formalization using the Bernstein basis.
* **`Dsc_Exec.thy`**: Defines partial tail-recursive versions of the algorithms (`dsc_exec` and `newdsc_exec`) suitable for code generation, proving their equivalence with the verified functions.
* **`Sturm_Isolate.thy`**: Extracts the Sturm-based real root isolation function `isolate` developed by Thiemann and Yamada, customized to remove extra steps (like square-free factorization and packaging algebraic numbers) to ensure fair benchmarking.
* **`Bench_Export.thy`**: Exports `isolate`, `dsc_exec`, and `newdsc_exec` to executable SML code (`bench_gen.sml`).
* **`bench_main.sml`**: Runs performance comparisons between the Descartes-based algorithms and the Sturm baseline, testing on irreducible polynomials on random and Mignotte-type polynomials. The coefficients for random polynomials tested can be found inside.
* **`Radical.thy`**: Defines and verifies radical operators for real and rational polynomials.
* **`Supplementary_Functions.thy`**: Includes functions that were not as fast as the main executable exports, as well as total functions obtained by wrapping `dsc` and `newdsc` with radical operators.

