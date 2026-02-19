# Dsc
Isabelle/HOL verification of real root isolation algorithms based on Descartes' Rule of Signs. Includes a classical bisection algorithm "dsc" and a Newton-accelerated version "newdsc".

The verification was completed in Isabelle 2025-1, and some proofs might break in different versions.

Dsc_Bern.thy proves the equivalence between the direct formalisation of Descartes' root test by Li and the formalisation using Bernstein basis by Thompson.

Dsc_Misc.thy provides various lemmas preparing for the verification of dsc and newdsc, most importantly a lemma that packages the theorem of three circles to show that the sign variation of a square-free real polynomial eventually becomes 1 or 0 as the algorithm runs.

Dsc.thy formalises dsc as a partial function, proves conditional termination, soundness, and completeness of dsc, based on lemmas proven in Dsc_Misc.thy.

NewDsc.thy proves conditional termination, soundness, and completeness of newdsc, using an additional splitting lemma for Bernstein coefficients, which took the following three .thy files ot prove.

List_Changes.thy proves many lemmas about sign changes in a list. In particular, the number of coefficient sign changes is subadditive with respect to the De Casteljau split.

Triangle.thy formalises the De Casteljau triangle construction and proves basic algebraic identities showing how the triangle computes Bernstein coefficients under subdivision.

Bernstein_Split.thy combines them to prove the splitting lemma required for verifying NewDsc.

Dsc_Exec.thy defines tail-recusive versions of dsc and newdsc for exporting code ("dsc_exec" and "newdsc_exec"). The equivalence between the corresponding functions are proven here.

Sturm_Isolate.thy extracts a real root isolation function "isolate" developed by Thiemann and Yamada in Isabelle, which is the best performing verified real root isolation algorithm we are aware of. To ensure fairness, we customized their algorithm in order to remove extra steps in their original code such as square-free factorization and packaging algebraic numbers. We did not verify our particular customization of their algorithm.

Bench_Export.thy exports the functions isolate, dsc_exec, and newdsc_exec to executable code. The output is bench_gen.sml

bench_main.sml runs experiments comparing the performance of isolate, dsc_exec, and newdsc_exec. Since Thiemann and Yamada's optimized algorithm only works on irreducible polynomials (they do a square factorization otherwise), we only choose irreducible polynomials in the benchmarks. The experiments can be run using Poly/ML 5.9.1 (Comes with Isabelle 2025-1) with the command poly --use bench_gen.sml --use bench_main.sml

Supplementary_Functions.thy includes functions we wrote that were not as fast as dsc_exec and newdsc_exec, as well as total functions obtained by wrapping dsc and newdsc with radical operators (defined and verified in Radical.thy) on polynomials. 
