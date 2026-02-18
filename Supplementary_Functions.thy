theory Supplementary_Functions
  imports 
          Dsc
          NewDsc
          Dsc_Bern
          Radical
begin

lemma Poly_eq_foldr_pCons:
  fixes xs :: "'a::zero list"
  shows "Poly xs = foldr pCons xs (0::'a poly)"
  by (induction xs) simp_all

lemma reciprocal_poly_code [code]:
  "reciprocal_poly pa (p :: 'a::zero poly) =
     foldr pCons (rev (coeffs p @ replicate (pa - degree p) 0)) 0"
  by (simp add: Poly_eq_foldr_pCons reciprocal_poly_def)

lemma dsc_psimps_if_radical:
  fixes R :: "rat poly"
  defines "P \<equiv> (map_poly (of_rat:: rat \<Rightarrow> real) (radical_rat_poly R))"
  assumes P0: "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0:  "p \<noteq> 0"
      and ab:  "a < b"
  shows
    "dsc p a b P =
      (let v = Bernstein_changes p a b P
            in if v = 0 then []
               else if v = 1 then [(a, b)]
                    else let m = (a + b) / 2
                         in (if poly P m = 0 then [(m, m)] else [])
                            @ dsc p a m P @ dsc p m b P)"
proof -
  have R0: "R \<noteq> 0"
  proof
    assume "R = 0"
    then have "P = 0"
      by (simp add: P_def radical_rat_poly_def)
    with P0 show False by simp
  qed

  have sf_rad: "square_free (radical_rat_poly R)"
    using radical_rat_poly_square_free[OF R0] .

  have sfP: "square_free P"
    unfolding P_def
    using square_free_liftR[OF sf_rad] .

  show ?thesis
  proof (rule dsc_psimps_if[of P])
    show "P \<noteq> 0" using P0 .
    show "degree P \<le> p" using deg .
    show "p \<noteq> 0" using p0 .
    show "square_free P" using sfP .
    show "a < b" using ab .
  qed
qed

definition wrap :: "real \<Rightarrow> real \<Rightarrow> rat poly \<Rightarrow> (real \<times> real) list"
where
  "wrap a b R = (let P = (map_poly (of_rat:: rat \<Rightarrow> real) (radical_rat_poly R)) in
    (let p = (degree P) in
     (if (P \<noteq> 0 \<and> (degree P) \<le> p \<and> p \<noteq> 0 \<and> a < b)
       then dsc p a b P 
        else [])))"

lemma wrap_eq_dsc:
  fixes a b :: real and R :: "rat poly"
  defines "P \<equiv> map_poly (of_rat :: rat \<Rightarrow> real) (radical_rat_poly R)"
  assumes P0:  "P \<noteq> 0"
      and deg0:"degree P \<noteq> 0"
      and ab:  "a < b"
  shows "wrap a b R = dsc (degree P) a b P"
    using P0 deg0 ab
    by (simp add: wrap_def P_def)

lemma wrap_simp:  "wrap a b R = (let P = (map_poly (of_rat:: rat \<Rightarrow> real) (radical_rat_poly R)) in
    (let p = (degree P) in
     (if (P \<noteq> 0 \<and> (degree P) \<le> p \<and> p \<noteq> 0 \<and> a < b)
       then (let v = Bernstein_changes p a b P
            in if v = 0 then []
               else if v = 1 then [(a, b)]
                    else let m = (a + b) / 2
                         in (if poly P m = 0 then [(m, m)] else [])
                            @ dsc p a m P @ dsc p m b P)
        else [])))"
  by (smt (verit, ccfv_SIG) dsc_psimps_if_radical wrap_def)

lemma wrap_code[code]:  "wrap a b R = (let P = (map_poly (of_rat:: rat \<Rightarrow> real) (radical_rat_poly R)) in
    (let p = (degree P) in
     (if (P \<noteq> 0 \<and> (degree P) \<le> p \<and> p \<noteq> 0 \<and> a < b)
       then (let v = Bernstein_changes p a b P
            in if v = 0 then []
               else if v = 1 then [(a, b)]
                    else let m = (a + b) / 2
                         in (if poly P m = 0 then [(m, m)] else [])
                            @ wrap a m R @ wrap m b R)
        else [])))"
  by (smt (verit) dsc_psimps_if_radical gt_half_sum less_half_sum wrap_def)

lemma wrap_dsc_dom:
  fixes a b :: real and R :: "rat poly"
  defines "P \<equiv> map_poly (of_rat :: rat \<Rightarrow> real) (radical_rat_poly R)"
  assumes P0:   "P \<noteq> 0"
      and deg0: "degree P \<noteq> 0"
      and ab:   "a < b"
  shows "dsc_dom (degree P, a, b, P)"
proof -
  have R0: "R \<noteq> 0"
  proof
    assume "R = 0"
    then have "P = 0"
      by (simp add: P_def radical_rat_poly_def)
    with P0 show False by simp
  qed

  have sf_rad: "square_free (radical_rat_poly R)"
    using radical_rat_poly_square_free[OF R0] .

  have sfP: "square_free P"
    unfolding P_def
    using square_free_liftR[OF sf_rad] .

  show ?thesis
  proof (rule dsc_terminates_squarefree_real[where P=P and p="degree P" and a=a and b=b])
    show "P \<noteq> 0" using P0 .
    show "degree P \<le> degree P" by simp
    show "degree P \<noteq> 0" using deg0 .
    show "square_free P" using sfP .
    show "a < b" using ab .
  qed
qed

lemma wrap_sound:
  fixes a b :: real and R :: "rat poly"
  defines "P \<equiv> map_poly (of_rat :: rat \<Rightarrow> real) (radical_rat_poly R)"
  assumes P0:   "P \<noteq> 0"
      and deg0: "degree P \<noteq> 0"
      and ab:   "a < b"
  shows "\<forall>I \<in> set (wrap a b R). dsc_pair_ok P I"
proof -
  have dom: "dsc_dom (degree P, a, b, P)"
    using wrap_dsc_dom P0 P_def ab deg0 by blast

  have wrap_dsc: "wrap a b R = dsc (degree P) a b P"
    using wrap_eq_dsc P_def P0 deg0 ab by blast

  have deg: "degree P \<le> degree P" by simp

  show ?thesis
    using dsc_sound[OF dom deg P0 ab]
    by (simp add: wrap_dsc)
qed

lemma wrap_complete:
  fixes a b :: real and R :: "rat poly"
  defines "P \<equiv> map_poly (of_rat :: rat \<Rightarrow> real) (radical_rat_poly R)"
  assumes P0:   "P \<noteq> 0"
      and deg0: "degree P \<noteq> 0"
      and ab:   "a < b"
  shows "\<And>x. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
             (\<exists>I\<in>set (wrap a b R). fst I \<le> x \<and> x \<le> snd I)"
proof -
  have dom: "dsc_dom (degree P, a, b, P)"
    using P0 P_def ab deg0 wrap_dsc_dom by blast

  have wrap_dsc: "wrap a b R = dsc (degree P) a b P"
    using wrap_eq_dsc P_def P0 deg0 ab by blast

  have deg: "degree P \<le> degree P" by simp

  fix x :: real
  assume root: "poly P x = 0" and ax: "a < x" and xb: "x < b"

  have ex_dsc:
    "\<exists>I\<in>set (dsc (degree P) a b P). fst I \<le> x \<and> x \<le> snd I"
    using dsc_complete[OF dom deg P0] root ax xb .

  show "\<exists>I\<in>set (wrap a b R). fst I \<le> x \<and> x \<le> snd I"
    using ex_dsc
    by (simp add: wrap_dsc)
qed


definition wrap_real :: "real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "wrap_real a b R = (let P = (radical_real_poly R) in
    (let p = (degree P) in
     (if (P \<noteq> 0 \<and> (degree P) \<le> p \<and> p \<noteq> 0 \<and> a < b)
       then dsc p a b P 
        else [])))"


lemma wrap_real_eq_dsc:
  fixes a b :: real and R :: "real poly"
  defines "P \<equiv> (radical_real_poly R)"
  assumes P0:  "P \<noteq> 0"
      and deg0:"degree P \<noteq> 0"
      and ab:  "a < b"
  shows "wrap_real a b R = dsc (degree P) a b P"
    using P0 deg0 ab
    by (smt (verit) P_def less_or_eq_imp_le wrap_real_def)

lemma wrap_real_simp:  "wrap_real a b R = (let P =  (radical_real_poly R) in
    (let p = (degree P) in
     (if (P \<noteq> 0 \<and> (degree P) \<le> p \<and> p \<noteq> 0 \<and> a < b)
       then (let v = Bernstein_changes p a b P
            in if v = 0 then []
               else if v = 1 then [(a, b)]
                    else let m = (a + b) / 2
                         in (if poly P m = 0 then [(m, m)] else [])
                            @ dsc p a m P @ dsc p m b P)
        else [])))"
  by (smt (verit) div_by_0 dsc_psimps_if_squarefree_real gcd_eq_0_iff pderiv_0 radical_real_poly_def
      radical_real_poly_square_free wrap_real_def)

lemma wrap_real_code[code]:  "wrap_real a b R = (let P = (radical_real_poly R) in
    (let p = (degree P) in
     (if (P \<noteq> 0 \<and> (degree P) \<le> p \<and> p \<noteq> 0 \<and> a < b)
       then (let v = Bernstein_changes p a b P
            in if v = 0 then []
               else if v = 1 then [(a, b)]
                    else let m = (a + b) / 2
                         in (if poly P m = 0 then [(m, m)] else [])
                            @ wrap_real a m R @ wrap_real m b R)
        else [])))"
  by (smt (verit, best) field_sum_of_halves wrap_real_eq_dsc wrap_real_simp)

lemma wrap_real_dsc_dom:
  fixes a b :: real and R :: "real poly"
  defines "P \<equiv> (radical_real_poly R)"
  assumes P0:   "P \<noteq> 0"
      and deg0: "degree P \<noteq> 0"
      and ab:   "a < b"
  shows "dsc_dom (degree P, a, b, P)"
proof -
  have R0: "R \<noteq> 0"
  proof
    assume "R = 0"
    then have "P = 0"
      by (simp add: P_def radical_real_poly_def)
    with P0 show False by simp
  qed

  show ?thesis
  proof (rule dsc_terminates_squarefree_real[where P=P and p="degree P" and a=a and b=b])
    show "P \<noteq> 0" using P0 .
    show "degree P \<le> degree P" by simp
    show "degree P \<noteq> 0" using deg0 .
    show "square_free P" using P_def R0 radical_real_poly_square_free by presburger
    show "a < b" using ab .
  qed
qed

lemma wrap_real_sound:
  fixes a b :: real and R :: "real poly"
  defines "P \<equiv> (radical_real_poly R)"
  assumes P0:   "P \<noteq> 0"
      and deg0: "degree P \<noteq> 0"
      and ab:   "a < b"
  shows "\<forall>I \<in> set (wrap_real a b R). dsc_pair_ok P I"
proof -
  have dom: "dsc_dom (degree P, a, b, P)"
    using wrap_real_dsc_dom P0 P_def ab deg0 by blast

  have wrap_real_dsc: "wrap_real a b R = dsc (degree P) a b P"
    using wrap_real_eq_dsc P_def P0 deg0 ab by blast

  have deg: "degree P \<le> degree P" by simp

  show ?thesis
    using dsc_sound[OF dom deg P0 ab]
    by (simp add: wrap_real_dsc)
qed

lemma wrap_real_complete:
  fixes a b :: real and R :: "real poly"
  defines "P \<equiv> (radical_real_poly R)"
  assumes P0:   "P \<noteq> 0"
      and deg0: "degree P \<noteq> 0"
      and ab:   "a < b"
  shows "\<And>x. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
             (\<exists>I\<in>set (wrap_real a b R). fst I \<le> x \<and> x \<le> snd I)"
proof -
  have dom: "dsc_dom (degree P, a, b, P)"
    using P0 P_def ab deg0 wrap_real_dsc_dom by blast

  have wrap_real_dsc: "wrap_real a b R = dsc (degree P) a b P"
    using wrap_real_eq_dsc P_def P0 deg0 ab by blast

  have deg: "degree P \<le> degree P" by simp

  fix x :: real
  assume root: "poly P x = 0" and ax: "a < x" and xb: "x < b"

  have ex_dsc:
    "\<exists>I\<in>set (dsc (degree P) a b P). fst I \<le> x \<and> x \<le> snd I"
    using dsc_complete[OF dom deg P0] root ax xb .

  show "\<exists>I\<in>set (wrap_real a b R). fst I \<le> x \<and> x \<le> snd I"
    using ex_dsc
    by (simp add: wrap_real_dsc)
qed

lemma newdsc_psimps_if_radical:
  fixes R :: "rat poly"
  defines "P \<equiv> map_poly (of_rat:: rat \<Rightarrow> real) (radical_rat_poly R)"
  assumes P0: "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0:  "p \<noteq> 0"
      and ab:  "a < b"
      and N2:  "N \<ge> 2"
  shows
    "newdsc p a b N P =
      (let v = Bernstein_changes p a b P in
       if v = 0 then []
       else if v = 1 then [(a, b)]
       else
         (case try_blocks p a b N P v of
            Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
          | None \<Rightarrow>
              (case try_newton p a b N P v of
                 Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
               | None \<Rightarrow>
                   (let m  = (a + b) / 2;
                        N' = Nlin N;
                        mid_root = (if poly P m = 0 then [(m, m)] else [])
                    in mid_root @ newdsc p a m N' P @ newdsc p m b N' P))))"
proof -
  have R0: "R \<noteq> 0"
  proof
    assume "R = 0"
    then have "P = 0"
      by (simp add: P_def radical_rat_poly_def)
    with P0 show False by simp
  qed

  have sf_rad: "square_free (radical_rat_poly R)"
    using radical_rat_poly_square_free[OF R0] .

  have sfP: "square_free P"
    unfolding P_def
    using square_free_liftR[OF sf_rad] .

  show ?thesis
  proof (rule newdsc_psimps_if[of P])
    show "P \<noteq> 0" using P0 .
    show "degree P \<le> p" using deg .
    show "p \<noteq> 0" using p0 .
    show "square_free P" using sfP .
    show "a < b" using ab .
    show "N \<ge> 2" using N2 .
  qed
qed


definition wrap_newdsc :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> rat poly \<Rightarrow> (real \<times> real) list"
where
  "wrap_newdsc a b N R =
     (let P = (map_poly (of_rat:: rat \<Rightarrow> real) (radical_rat_poly R)) in
      (let p = (degree P) in
       (if (P \<noteq> 0 \<and> (degree P) \<le> p \<and> p \<noteq> 0 \<and> a < b \<and> N \<ge> 2)
        then newdsc p a b N P
        else [])))"

lemma wrap_newdsc_eq_newdsc:
  fixes a b :: real and N :: nat and R :: "rat poly"
  defines "P \<equiv> map_poly (of_rat :: rat \<Rightarrow> real) (radical_rat_poly R)"
  assumes P0:  "P \<noteq> 0"
      and deg0:"degree P \<noteq> 0"
      and ab:  "a < b"
      and N2:  "N \<ge> 2"
  shows "wrap_newdsc a b N R = newdsc (degree P) a b N P"
  using P0 deg0 ab N2
  by (simp add: wrap_newdsc_def P_def)

declare [[code drop: wrap_newdsc]]

lemma wrap_newdsc_simp:
  "wrap_newdsc a b N R =
     (let P = map_poly (of_rat::rat \<Rightarrow> real) (radical_rat_poly R) in
      (let p = degree P in
       (if (P \<noteq> 0 \<and> degree P \<le> p \<and> p \<noteq> 0 \<and> a < b \<and> N \<ge> 2)
        then
          (let v = Bernstein_changes p a b P in
           if v = 0 then []
           else if v = 1 then [(a, b)]
           else
             (case try_blocks p a b N P v of
                Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
              | None \<Rightarrow>
                  (case try_newton p a b N P v of
                     Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                   | None \<Rightarrow>
                       (let m = (a + b) / 2;
                            N' = Nlin N;
                            mid_root = (if poly P m = 0 then [(m,m)] else [])
                        in mid_root @ newdsc p a m N' P @ newdsc p m b N' P))))
        else [])))"
  unfolding wrap_newdsc_def
  by (simp add: Let_def newdsc_psimps_if_radical split: if_split option.split)

lemma newdsc_eq_wrap_newdsc:
  fixes a b :: real and N :: nat and R :: "rat poly"
  defines "P \<equiv> map_poly (of_rat :: rat \<Rightarrow> real) (radical_rat_poly R)"
  assumes P0: "P \<noteq> 0"
      and p0: "degree P \<noteq> 0"
      and ab: "a < b"
      and N2: "N \<ge> 2"
  shows "newdsc (degree P) a b N P = wrap_newdsc a b N R"
  using wrap_newdsc_eq_newdsc
  by (metis N2 P0 P_def ab p0)


lemma wrap_newdsc_code[code]:
  "wrap_newdsc a b N R =
     (let P = (map_poly (of_rat:: rat \<Rightarrow> real) (radical_rat_poly R)) in
      (let p = (degree P) in
       (if (P \<noteq> 0 \<and> (degree P) \<le> p \<and> p \<noteq> 0 \<and> a < b \<and> N \<ge> 2)
        then
          (let v = Bernstein_changes p a b P in
           if v = 0 then []
           else if v = 1 then [(a, b)]
           else
             (case try_blocks p a b N P v of
                Some I \<Rightarrow> wrap_newdsc (fst I) (snd I) (Nq N) R
              | None \<Rightarrow>
                  (case try_newton p a b N P v of
                     Some I \<Rightarrow> wrap_newdsc (fst I) (snd I) (Nq N) R
                   | None \<Rightarrow>
                       (let m  = (a + b) / 2;
                            N' = Nlin N;
                            mid_root = (if poly P m = 0 then [(m, m)] else [])
                        in mid_root @ wrap_newdsc a m N' R @ wrap_newdsc m b N' R))))
        else [])))"
proof -
  have W: "wrap_newdsc a b N R =
     (let P = (map_poly (of_rat:: rat \<Rightarrow> real) (radical_rat_poly R)) in
      (let p = (degree P) in
       (if (P \<noteq> 0 \<and> (degree P) \<le> p \<and> p \<noteq> 0 \<and> a < b \<and> N \<ge> 2)
        then
          (let v = Bernstein_changes p a b P in
           if v = 0 then []
           else if v = 1 then [(a, b)]
           else
             (case try_blocks p a b N P v of
                Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
              | None \<Rightarrow>
                  (case try_newton p a b N P v of
                     Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                   | None \<Rightarrow>
                       (let m  = (a + b) / 2;
                            N' = Nlin N;
                            mid_root = (if poly P m = 0 then [(m, m)] else [])
                        in mid_root @ newdsc p a m N' P @ newdsc p m b N' P))))
        else [])))"
    by (rule wrap_newdsc_simp)
  show ?thesis
    apply (subst W)
    apply (simp add: Let_def
             newdsc_eq_wrap_newdsc
             Nq_ge_2 Nlin_ge_2 midpoint_strict
             try_blocks_Some_fst_lt_snd try_newton_Some_fst_lt_snd
           split: if_split option.split)
    using Nlin_ge_2 Nq_ge_2 newdsc_eq_wrap_newdsc try_blocks_Some_fst_lt_snd try_newton_Some_fst_lt_snd
    by force
qed

lemma wrap_newdsc_dom:
  fixes a b :: real and N :: nat and R :: "rat poly"
  defines "P \<equiv> map_poly (of_rat :: rat \<Rightarrow> real) (radical_rat_poly R)"
  assumes P0:   "P \<noteq> 0"
      and deg0: "degree P \<noteq> 0"
      and ab:   "a < b"
      and N2:   "N \<ge> 2"
  shows "newdsc_dom (degree P, a, b, N, P)"
proof -
  have R0: "R \<noteq> 0"
  proof
    assume "R = 0"
    then have "P = 0"
      by (simp add: P_def radical_rat_poly_def)
    with P0 show False by simp
  qed

  have sf_rad: "square_free (radical_rat_poly R)"
    using radical_rat_poly_square_free[OF R0] .

  have sfP: "square_free P"
    unfolding P_def
    using square_free_liftR[OF sf_rad] .

  show ?thesis
  proof (rule newdsc_terminates_squarefree_real[where P=P and p="degree P"])
    show "P \<noteq> 0" using P0 .
    show "degree P \<le> degree P" by simp
    show "degree P \<noteq> 0" using deg0 .
    show "square_free P" using sfP .
    show "a < b" using ab .
    show "N \<ge> 2" using N2 .
  qed
qed

lemma wrap_newdsc_sound:
  fixes a b :: real and N :: nat and R :: "rat poly"
  defines "P \<equiv> map_poly (of_rat :: rat \<Rightarrow> real) (radical_rat_poly R)"
  assumes P0:   "P \<noteq> 0"
      and deg0: "degree P \<noteq> 0"
      and ab:   "a < b"
      and N2:   "N \<ge> 2"
  shows "\<forall>I \<in> set (wrap_newdsc a b N R). dsc_pair_ok P I"
proof -
  have dom: "newdsc_dom (degree P, a, b, N, P)"
    using wrap_newdsc_dom P_def P0 deg0 ab N2 by blast

  have wrap_eq: "wrap_newdsc a b N R = newdsc (degree P) a b N P"
    using wrap_newdsc_eq_newdsc P_def P0 deg0 ab N2 by blast

  have deg: "degree P \<le> degree P" by simp

  show ?thesis
    using newdsc_sound[OF dom deg P0 ab]
    by (simp add: wrap_eq)
qed

lemma wrap_newdsc_complete:
  fixes a b :: real and N :: nat and R :: "rat poly"
  defines "P \<equiv> map_poly (of_rat :: rat \<Rightarrow> real) (radical_rat_poly R)"
  assumes P0:   "P \<noteq> 0"
      and deg0: "degree P \<noteq> 0"
      and ab:   "a < b"
      and N2:   "N \<ge> 2"
  shows "\<And>x. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
             (\<exists>I\<in>set (wrap_newdsc a b N R). fst I \<le> x \<and> x \<le> snd I)"
proof -
  have dom: "newdsc_dom (degree P, a, b, N, P)"
    using wrap_newdsc_dom P_def P0 deg0 ab N2 by blast

  have wrap_eq: "wrap_newdsc a b N R = newdsc (degree P) a b N P"
    using wrap_newdsc_eq_newdsc P_def P0 deg0 ab N2 by blast

  have deg: "degree P \<le> degree P" by simp
  have Npos: "N > 0" using N2 by simp

  fix x :: real
  assume root: "poly P x = 0" and ax: "a < x" and xb: "x < b"

  have ex_newdsc:
    "\<exists>I\<in>set (newdsc (degree P) a b N P). fst I \<le> x \<and> x \<le> snd I"
    using newdsc_complete[OF dom deg P0 Npos] root ax xb .

  show "\<exists>I\<in>set (wrap_newdsc a b N R). fst I \<le> x \<and> x \<le> snd I"
    using ex_newdsc
    by (simp add: wrap_eq)
qed

lemma newdsc_psimps_if_radical_real:
  fixes R :: "real poly"
  defines "P \<equiv> radical_real_poly R"
  assumes P0: "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0:  "p \<noteq> 0"
      and ab:  "a < b"
      and N2:  "N \<ge> 2"
  shows
    "newdsc p a b N P =
      (let v = Bernstein_changes p a b P in
       if v = 0 then []
       else if v = 1 then [(a, b)]
       else
         (case try_blocks p a b N P v of
            Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
          | None \<Rightarrow>
              (case try_newton p a b N P v of
                 Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
               | None \<Rightarrow>
                   (let m  = (a + b) / 2;
                        N' = Nlin N;
                        mid_root = (if poly P m = 0 then [(m, m)] else [])
                    in mid_root @ newdsc p a m N' P @ newdsc p m b N' P))))"
proof -
  have R0: "R \<noteq> 0"
  proof
    assume "R = 0"
    then have "P = 0"
      by (simp add: P_def radical_real_poly_def)
    with P0 show False by simp
  qed

  have sfP: "square_free P"
    using R0 unfolding P_def
    by (simp add: radical_real_poly_square_free)

  show ?thesis
  proof (rule newdsc_psimps_if[of P])
    show "P \<noteq> 0" using P0 .
    show "degree P \<le> p" using deg .
    show "p \<noteq> 0" using p0 .
    show "square_free P" using sfP .
    show "a < b" using ab .
    show "N \<ge> 2" using N2 .
  qed
qed


definition wrap_newdsc_real :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "wrap_newdsc_real a b N R =
     (let P = radical_real_poly R in
      (let p = degree P in
       (if (P \<noteq> 0 \<and> degree P \<le> p \<and> p \<noteq> 0 \<and> a < b \<and> N \<ge> 2)
        then newdsc p a b N P
        else [])))"

lemma wrap_newdsc_real_eq_newdsc:
  fixes a b :: real and N :: nat and R :: "real poly"
  defines "P \<equiv> radical_real_poly R"
  assumes P0:  "P \<noteq> 0"
      and deg0:"degree P \<noteq> 0"
      and ab:  "a < b"
      and N2:  "N \<ge> 2"
  shows "wrap_newdsc_real a b N R = newdsc (degree P) a b N P"
  using P0 deg0 ab N2
  by (smt (verit, best) P_def dual_order.refl wrap_newdsc_real_def)

lemma wrap_newdsc_real_simp:
  "wrap_newdsc_real a b N R =
     (let P = radical_real_poly R in
      (let p = degree P in
       (if (P \<noteq> 0 \<and> degree P \<le> p \<and> p \<noteq> 0 \<and> a < b \<and> N \<ge> 2)
        then
          (let v = Bernstein_changes p a b P in
           if v = 0 then []
           else if v = 1 then [(a, b)]
           else
             (case try_blocks p a b N P v of
                Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
              | None \<Rightarrow>
                  (case try_newton p a b N P v of
                     Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                   | None \<Rightarrow>
                       (let m = (a + b) / 2;
                            N' = Nlin N;
                            mid_root = (if poly P m = 0 then [(m,m)] else [])
                        in mid_root @ newdsc p a m N' P @ newdsc p m b N' P))))
        else [])))"
  unfolding wrap_newdsc_real_def
  by (simp add: Let_def newdsc_psimps_if_radical_real split: if_split option.split)

lemma newdsc_eq_wrap_newdsc_real:
  fixes a b :: real and N :: nat and R :: "real poly"
  defines "P \<equiv> radical_real_poly R"
  assumes P0: "P \<noteq> 0"
      and p0: "degree P \<noteq> 0"
      and ab: "a < b"
      and N2: "N \<ge> 2"
  shows "newdsc (degree P) a b N P = wrap_newdsc_real a b N R"
  using wrap_newdsc_real_eq_newdsc
  by (metis N2 P0 P_def ab p0)

lemma wrap_newdsc_real_code[code]:
  "wrap_newdsc_real a b N R =
     (let P = radical_real_poly R in
      (let p = degree P in
       (if (P \<noteq> 0 \<and> degree P \<le> p \<and> p \<noteq> 0 \<and> a < b \<and> N \<ge> 2)
        then
          (let v = Bernstein_changes p a b P in
           if v = 0 then []
           else if v = 1 then [(a, b)]
           else
             (case try_blocks p a b N P v of
                Some I \<Rightarrow> wrap_newdsc_real (fst I) (snd I) (Nq N) R
              | None \<Rightarrow>
                  (case try_newton p a b N P v of
                     Some I \<Rightarrow> wrap_newdsc_real (fst I) (snd I) (Nq N) R
                   | None \<Rightarrow>
                       (let m  = (a + b) / 2;
                            N' = Nlin N;
                            mid_root = (if poly P m = 0 then [(m, m)] else [])
                        in mid_root @ wrap_newdsc_real a m N' R @ wrap_newdsc_real m b N' R))))
        else [])))"
proof -
  have W:
    "wrap_newdsc_real a b N R =
       (let P = radical_real_poly R in
        (let p = degree P in
         (if (P \<noteq> 0 \<and> degree P \<le> p \<and> p \<noteq> 0 \<and> a < b \<and> N \<ge> 2)
          then
            (let v = Bernstein_changes p a b P in
             if v = 0 then []
             else if v = 1 then [(a, b)]
             else
               (case try_blocks p a b N P v of
                  Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                | None \<Rightarrow>
                    (case try_newton p a b N P v of
                       Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                     | None \<Rightarrow>
                         (let m  = (a + b) / 2;
                              N' = Nlin N;
                              mid_root = (if poly P m = 0 then [(m, m)] else [])
                          in mid_root @ newdsc p a m N' P @ newdsc p m b N' P))))
          else [])))"
    by (rule wrap_newdsc_real_simp)
  show ?thesis
    apply (subst W)
    by (simp add: Let_def
             newdsc_eq_wrap_newdsc_real
             Nq_ge_2 Nlin_ge_2 midpoint_strict
             try_blocks_Some_fst_lt_snd try_newton_Some_fst_lt_snd
           split: if_split option.split)
qed

lemma wrap_newdsc_real_dom:
  fixes a b :: real and N :: nat and R :: "real poly"
  defines "P \<equiv> radical_real_poly R"
  assumes P0:   "P \<noteq> 0"
      and deg0: "degree P \<noteq> 0"
      and ab:   "a < b"
      and N2:   "N \<ge> 2"
  shows "newdsc_dom (degree P, a, b, N, P)"
proof -
  have R0: "R \<noteq> 0"
  proof
    assume "R = 0"
    then have "P = 0"
      by (simp add: P_def radical_real_poly_def)
    with P0 show False by simp
  qed

  have sfP: "square_free P"
    using R0 unfolding P_def
    by (simp add: radical_real_poly_square_free)

  show ?thesis
  proof (rule newdsc_terminates_squarefree_real[where P=P and p="degree P"])
    show "P \<noteq> 0" using P0 .
    show "degree P \<le> degree P" by simp
    show "degree P \<noteq> 0" using deg0 .
    show "square_free P" using sfP .
    show "a < b" using ab .
    show "N \<ge> 2" using N2 .
  qed
qed

lemma wrap_newdsc_real_correct:
  fixes a b :: real and N :: nat and R :: "real poly"
  defines "P \<equiv> radical_real_poly R"
  assumes P0:   "P \<noteq> 0"
      and deg0: "degree P \<noteq> 0"
      and ab:   "a < b"
      and N2:   "N \<ge> 2"
  shows "\<forall>I \<in> set (wrap_newdsc_real a b N R). dsc_pair_ok P I"
proof -
  have dom: "newdsc_dom (degree P, a, b, N, P)"
    using wrap_newdsc_real_dom P_def P0 deg0 ab N2 by blast

  have wrap_eq: "wrap_newdsc_real a b N R = newdsc (degree P) a b N P"
    using wrap_newdsc_real_eq_newdsc P_def P0 deg0 ab N2 by blast

  have deg: "degree P \<le> degree P" by simp

  show ?thesis
    using newdsc_sound[OF dom deg P0 ab]
    by (simp add: wrap_eq)
qed

lemma wrap_newdsc_real_complete:
  fixes a b :: real and N :: nat and R :: "real poly"
  defines "P \<equiv> radical_real_poly R"
  assumes P0:   "P \<noteq> 0"
      and deg0: "degree P \<noteq> 0"
      and ab:   "a < b"
      and N2:   "N \<ge> 2"
  shows "\<And>x. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
             (\<exists>I\<in>set (wrap_newdsc_real a b N R). fst I \<le> x \<and> x \<le> snd I)"
proof -
  have dom: "newdsc_dom (degree P, a, b, N, P)"
    using wrap_newdsc_real_dom P_def P0 deg0 ab N2 by blast

  have wrap_eq: "wrap_newdsc_real a b N R = newdsc (degree P) a b N P"
    using wrap_newdsc_real_eq_newdsc P_def P0 deg0 ab N2 by blast

  have deg: "degree P \<le> degree P" by simp
  have Npos: "N > 0" using N2 by simp

  fix x :: real
  assume root: "poly P x = 0" and ax: "a < x" and xb: "x < b"

  have ex_newdsc:
    "\<exists>I\<in>set (newdsc (degree P) a b N P). fst I \<le> x \<and> x \<le> snd I"
    using newdsc_complete[OF dom deg P0 Npos] root ax xb .

  show "\<exists>I\<in>set (wrap_newdsc_real a b N R). fst I \<le> x \<and> x \<le> snd I"
    using ex_newdsc
    by (simp add: wrap_eq)
qed

partial_function (tailrec) dsc_main ::
  "nat \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list"
where
  [code]:
  "dsc_main p P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b) # todo' \<Rightarrow>
          (let v = Bernstein_changes p a b P in
           if v = 0 then
             dsc_main p P todo' acc
           else if v = 1 then
             dsc_main p P todo' ((a,b) # acc)
           else
             (let m = (a + b) / 2;
                  acc' = (if poly P m = 0 then (m,m) # acc else acc)
              in dsc_main p P ((a,m) # (m,b) # todo') acc')))"


definition dsc_tr :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "dsc_tr p a b P = (dsc_main p P [(a,b)] [])"

lemma dsc_main_sim:
  assumes dom: "dsc_dom (p,a,b,P)"
  shows
    "dsc_main p P ((a,b) # todo) acc =
     dsc_main p P todo (rev (dsc p a b P) @ acc)"
  using dom
proof (induction p a b P arbitrary: todo acc rule: dsc.pinduct)
  case (1 p a b P todo acc)
  let ?v = "Bernstein_changes p a b P"
  show ?case
  proof (cases "?v = 0")
    case v0: True
    have dsc0: "dsc p a b P = []"
      by (simp add: "1.hyps" dsc.psimps v0) 
    show ?thesis
      by (simp add: dsc_main.simps Let_def v0 dsc0)
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have dsc1: "dsc p a b P = [(a,b)]"
        by (simp add: "1.hyps" dsc.psimps v1)
      show ?thesis
        by (simp add: dsc_main.simps Let_def v0 v1 dsc1)
    next
      case v1: False
      define m where "m = (a + b) / 2"
      let ?mid = "(if poly P m = 0 then [(m,m)] else [])"

      have dsc_split:
        "dsc p a b P = ?mid @ dsc p a m P @ dsc p m b P"
        by (smt (verit, ccfv_SIG) "1.hyps" dsc.psimps m_def v0 v1)

      have main_split:
        "dsc_main p P ((a,b) # todo) acc =
         dsc_main p P ((a,m) # (m,b) # todo) (?mid @ acc)"
        by (smt (verit) append_Cons dsc_main.simps list.case(2) m_def self_append_conv2 split_conv v0 v1)

      have stepL:
        "dsc_main p P ((a,m) # (m,b) # todo) (?mid @ acc) =
         dsc_main p P ((m,b) # todo) (rev (dsc p a m P) @ (?mid @ acc))"
        using "1.IH"(1)[of ?v m "((m,b)#todo)" "?mid @ acc"]
        by (simp add: v0 v1 m_def)

      have stepR:
        "dsc_main p P ((m,b) # todo) (rev (dsc p a m P) @ (?mid @ acc)) =
         dsc_main p P todo (rev (dsc p m b P) @ (rev (dsc p a m P) @ (?mid @ acc)))"
        using "1.IH"(2)[of ?v m todo "rev (dsc p a m P) @ (?mid @ acc)"]
        by (simp add: v0 v1 m_def)

      have LHS_rewrite:
        "dsc_main p P ((a,b) # todo) acc =
         dsc_main p P todo (rev (dsc p m b P) @ rev (dsc p a m P) @ ?mid @ acc)"
        using main_split stepL stepR
        by simp

      have RHS_rewrite:
        "dsc_main p P todo (rev (dsc p a b P) @ acc) =
         dsc_main p P todo (rev (dsc p m b P) @ rev (dsc p a m P) @ ?mid @ acc)"
        using dsc_split
        by simp

      show ?thesis
        using LHS_rewrite RHS_rewrite by simp
    qed
  qed
qed


lemma dsc_tr_eq_dsc:
  assumes dom: "dsc_dom (p,a,b,P)"
  shows "rev(dsc_tr p a b P) = dsc p a b P"
  unfolding dsc_tr_def
  using dsc_main_sim[OF dom, of "[]::(real\<times>real) list" "[]"]
  by (simp add: dsc_main.simps)

type_synonym task = "real \<times> real \<times> real list"  (* (a,b, Bernstein_coeffs p a b P) *)

partial_function (tailrec) dsc_main_cache ::
  "nat \<Rightarrow> real poly \<Rightarrow> task list \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list"
where
  [code]:
  "dsc_main_cache p P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b,xs) # todo' \<Rightarrow>
          (let v = int (nat (changes xs)) in
           if v = 0 then
             dsc_main_cache p P todo' acc
           else if v = 1 then
             dsc_main_cache p P todo' ((a,b) # acc)
           else
             (let m = (a + b) / 2;
                  acc' = (if poly P m = 0 then (m,m) # acc else acc);
                  xsL = dc_left (1/2) xs;
                  xsR = dc_right (1/2) xs
              in dsc_main_cache p P ((a,m,xsL) # (m,b,xsR) # todo') acc')))"

definition dsc_tr_cache :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "dsc_tr_cache p a b P =
     (let xs0 = Bernstein_coeffs p a b P
      in (dsc_main_cache p P [(a,b,xs0)] []))"

lemma dsc_main_cache_sim:
  assumes dom: "dsc_dom (p,a,b,P)"
      and deg: "degree P \<le> p"
      and ab:  "a < b"
      and xs_ok: "xs = Bernstein_coeffs p a b P"
  shows
    "dsc_main_cache p P ((a,b,xs) # todo) acc =
     dsc_main_cache p P todo (rev (dsc p a b P) @ acc)"
using dom deg ab xs_ok
proof (induction p a b P arbitrary: todo acc xs rule: dsc.pinduct)
  case (1 p a b P todo acc xs)
  let ?v = "Bernstein_changes p a b P"

  have deg': "degree P \<le> p" and ab': "a < b" and xs_ok': "xs = Bernstein_coeffs p a b P"
    using "1.prems" by blast+

  have v_eq: "int (nat (changes xs)) = ?v"
    using xs_ok' by (simp add: Bernstein_changes_def)

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have dsc0: "dsc p a b P = []"
      by (simp add: "1.hyps" dsc.psimps v0)
    show ?thesis
     using dsc_main_cache.simps Let_def v_eq v0 dsc0 by simp
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have dsc1: "dsc p a b P = [(a,b)]"
        by (simp add: "1.hyps" dsc.psimps v1)
      show ?thesis
        using dsc_main_cache.simps Let_def v_eq v0 v1 dsc1 by simp
    next
      case v1: False
      define m where "m = (a + b) / 2"
      let ?mid = "(if poly P m = 0 then [(m,m)] else [])"
      let ?xsL = "dc_left (1/2) xs"
      let ?xsR = "dc_right (1/2) xs"

      have am: "a < m" and mb: "m < b"
        using ab' by (simp_all add: m_def)

      have dsc_split:
        "dsc p a b P = ?mid @ dsc p a m P @ dsc p m b P"
        by (smt (verit, ccfv_SIG) "1.hyps" dsc.psimps m_def v0 v1)

      have main_split:
        "dsc_main_cache p P ((a,b,xs) # todo) acc =
         dsc_main_cache p P ((a,m,?xsL) # (m,b,?xsR) # todo) (?mid @ acc)"
        using dsc_main_cache.simps Let_def v_eq v0 v1 m_def
        by (smt (verit) append_Cons append_Nil list.simps(5) old.prod.case)

      have xsL_ok: "?xsL = Bernstein_coeffs p a m P"
      proof -
        have "Bernstein_coeffs p a m P = dc_left (1/2) (Bernstein_coeffs p a b P)"
          using Bernstein_coeffs_split_mid(1)[OF ab' deg', folded m_def] .
        thus ?thesis
          using xs_ok' by simp
      qed

      have xsR_ok: "?xsR = Bernstein_coeffs p m b P"
      proof -
        have "Bernstein_coeffs p m b P = dc_right (1/2) (Bernstein_coeffs p a b P)"
          using Bernstein_coeffs_split_mid(2)[OF ab' deg', folded m_def] .
        thus ?thesis
          using xs_ok' by simp
      qed

      have stepL:
        "dsc_main_cache p P ((a,m,?xsL) # (m,b,?xsR) # todo) (?mid @ acc) =
         dsc_main_cache p P ((m,b,?xsR) # todo) (rev (dsc p a m P) @ (?mid @ acc))"
        using "1.IH"(1) v0 v1 m_def deg' am xsL_ok by simp

      have stepR:
        "dsc_main_cache p P ((m,b,?xsR) # todo) (rev (dsc p a m P) @ (?mid @ acc)) =
         dsc_main_cache p P todo (rev (dsc p m b P) @ (rev (dsc p a m P) @ (?mid @ acc)))"
        using "1.IH"(2) v0 v1 m_def deg' mb xsR_ok by simp

      have LHS_rewrite:
        "dsc_main_cache p P ((a,b,xs) # todo) acc =
         dsc_main_cache p P todo (rev (dsc p m b P) @ rev (dsc p a m P) @ ?mid @ acc)"
        using main_split stepL stepR
        by simp

      have RHS_rewrite:
        "dsc_main_cache p P todo (rev (dsc p a b P) @ acc) =
         dsc_main_cache p P todo (rev (dsc p m b P) @ rev (dsc p a m P) @ ?mid @ acc)"
        using dsc_split
        by simp

      show ?thesis
        using LHS_rewrite RHS_rewrite by simp
    qed
  qed
qed

lemma dsc_tr_cache_eq_dsc:
  assumes dom: "dsc_dom (p,a,b,P)"
      and deg: "degree P \<le> p"
      and ab:  "a < b"
  shows "rev (dsc_tr_cache p a b P) = dsc p a b P"
proof -
  have main:
    "dsc_main_cache p P [(a,b, Bernstein_coeffs p a b P)] [] = rev (dsc p a b P)"
    using dsc_main_cache_sim
    by (simp add: ab deg dom dsc_main_cache.simps)
  show ?thesis
    unfolding dsc_tr_cache_def
    using main by simp
qed

partial_function (tailrec) dsc_main_nob ::
  "real poly \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list"
where
  [code]:
  "dsc_main_nob P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b) # todo' \<Rightarrow>
          (let v = descartes_roots_test b a P in
           if v = 0 then
             dsc_main_nob P todo' acc
           else if v = 1 then
             dsc_main_nob P todo' ((a,b) # acc)
           else
             (let m = (a + b) / 2;
                  acc' = (if poly P m = 0 then (m,m) # acc else acc)
              in dsc_main_nob P ((a,m) # (m,b) # todo') acc')))"

definition dsc_nob_tr :: "real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "dsc_nob_tr a b P = (dsc_main_nob P [(a,b)] [])"

lemma dsc_main_nob_sim:
  assumes dom:  "dsc_dom (p,a,b,P)"
      and pdeg: "p = degree P"
  shows
    "dsc_main_nob P ((a,b) # todo) acc =
     dsc_main_nob P todo (rev (dsc p a b P) @ acc)"
  using dom pdeg
proof (induction p a b P arbitrary: todo acc rule: dsc.pinduct)
  case (1 p a b P todo acc)
  let ?v = "Bernstein_changes p a b P"

  have v_eq: "descartes_roots_test b a P = ?v"
    using "1.prems"
    by (simp add: descartes_roots_test_eq_Bernstein_changes)

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have dsc0: "dsc p a b P = []"
      by (simp add: "1.hyps" dsc.psimps v0)
    show ?thesis
      using dsc0 dsc_main_nob.simps v0 v_eq by auto
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have dsc1: "dsc p a b P = [(a,b)]"
        by (simp add: "1.hyps" dsc.psimps v1)
      show ?thesis
        using dsc_main_nob.simps Let_def v0 v1 v_eq dsc1 by auto
    next
      case v1: False
      define m where "m = (a + b) / 2"
      let ?mid = "(if poly P m = 0 then [(m,m)] else [])"

      have dsc_split:
        "dsc p a b P = ?mid @ dsc p a m P @ dsc p m b P"
        by (smt (verit, ccfv_SIG) "1.hyps" dsc.psimps m_def v0 v1)

      have mid_acc_eq:
        "(if poly P m = 0 then (m,m) # acc else acc) = ?mid @ acc"
        by (cases "poly P m = 0"; simp)

      have main_split:
        "dsc_main_nob P ((a,b) # todo) acc =
         dsc_main_nob P ((a,m) # (m,b) # todo) (?mid @ acc)"
      proof -
        have tmp:
          "dsc_main_nob P ((a,b) # todo) acc =
           dsc_main_nob P ((a,m) # (m,b) # todo)
             (if poly P m = 0 then (m,m) # acc else acc)"
          by (smt (verit) dsc_main_nob.simps int_ops(2) list.simps(5) m_def of_nat_eq_0_iff old.prod.case v0 v1
              v_eq)
        show ?thesis
          using tmp
          by (simp add: mid_acc_eq)
      qed

      have stepL:
        "dsc_main_nob P ((a,m) # (m,b) # todo) (?mid @ acc) =
         dsc_main_nob P ((m,b) # todo) (rev (dsc p a m P) @ (?mid @ acc))"
        using "1.IH"(1)[of ?v m "((m,b)#todo)" "?mid @ acc"]
        v0 v1 m_def v_eq "1.prems" by blast

      have stepR:
        "dsc_main_nob P ((m,b) # todo) (rev (dsc p a m P) @ (?mid @ acc)) =
         dsc_main_nob P todo
           (rev (dsc p m b P) @ (rev (dsc p a m P) @ (?mid @ acc)))"
        using "1.IH"(2)[of ?v m todo "rev (dsc p a m P) @ (?mid @ acc)"]
        v0 v1 m_def v_eq "1.prems" by blast

      have LHS_rewrite:
        "dsc_main_nob P ((a,b) # todo) acc =
         dsc_main_nob P todo
           (rev (dsc p m b P) @ rev (dsc p a m P) @ ?mid @ acc)"
        using main_split stepL stepR
        by simp

      have RHS_rewrite:
        "dsc_main_nob P todo (rev (dsc p a b P) @ acc) =
         dsc_main_nob P todo
           (rev (dsc p m b P) @ rev (dsc p a m P) @ ?mid @ acc)"
        using dsc_split
        by simp

      show ?thesis
        using LHS_rewrite RHS_rewrite
        by simp
    qed
  qed
qed


lemma dsc_nob_tr_eq_dsc:
  assumes dom:  "dsc_dom (p,a,b,P)"
      and pdeg: "p = degree P"
  shows "rev (dsc_nob_tr a b P) = dsc p a b P"
proof -
  have tr: "dsc_nob_tr a b P = rev (dsc p a b P)"
    unfolding dsc_nob_tr_def
    using dsc_main_nob_sim[OF dom pdeg, of "[]::(real\<times>real) list" "[]"]
    by (simp add: dsc_main_nob.simps)
  thus ?thesis by simp
qed


partial_function (tailrec) newdsc_main ::
  "nat \<Rightarrow> real poly \<Rightarrow> (real \<times> real \<times> nat) list \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list"
where
  [code]:
  "newdsc_main p P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b,N) # todo' \<Rightarrow>
          (let v = Bernstein_changes p a b P in
           if v = 0 then
             newdsc_main p P todo' acc
           else if v = 1 then
             newdsc_main p P todo' ((a,b) # acc)
           else
             (case try_blocks p a b N P v of
                Some I \<Rightarrow>
                  newdsc_main p P ((fst I, snd I, Nq N) # todo') acc
              | None \<Rightarrow>
                  (case try_newton p a b N P v of
                     Some I \<Rightarrow>
                       newdsc_main p P ((fst I, snd I, Nq N) # todo') acc
                   | None \<Rightarrow>
                       (let m  = (a + b) / 2;
                            N' = Nlin N;
                            acc' = (if poly P m = 0 then (m,m) # acc else acc)
                        in newdsc_main p P ((a,m,N') # (m,b,N') # todo') acc')))))"


definition newdsc_tr ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "newdsc_tr p a b N P = rev (newdsc_main p P [(a,b,N)] [])"


lemma newdsc_main_sim:
  assumes dom: "newdsc_dom (p,a,b,N,P)"
  shows
    "newdsc_main p P ((a,b,N) # todo) acc =
     newdsc_main p P todo (rev (newdsc p a b N P) @ acc)"
  using dom
proof (induction p a b N P arbitrary: todo acc rule: newdsc.pinduct)
  case (1 p a b N P todo acc)
  let ?v = "Bernstein_changes p a b P"

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have nd0: "newdsc p a b N P = []"
      by (simp add: "1.hyps" newdsc.psimps v0)
    show ?thesis
      by (simp add: newdsc_main.simps Let_def v0 nd0)
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have nd1: "newdsc p a b N P = [(a,b)]"
        by (simp add: "1.hyps" newdsc.psimps v1)
      show ?thesis
        by (simp add: newdsc_main.simps Let_def v0 v1 nd1)
    next
      case v1: False
      show ?thesis
      proof (cases "try_blocks p a b N P ?v")
        case (Some I)
        have nd_block:
          "newdsc p a b N P = newdsc p (fst I) (snd I) (Nq N) P"
          by (simp add: "1.hyps" newdsc.psimps v0 v1 Some)

        have main_block:
          "newdsc_main p P ((a,b,N) # todo) acc =
           newdsc_main p P ((fst I, snd I, Nq N) # todo) acc"
          by (simp add: newdsc_main.simps Let_def v0 v1 Some)

        have stepI:
          "newdsc_main p P ((fst I, snd I, Nq N) # todo) acc =
           newdsc_main p P todo (rev (newdsc p (fst I) (snd I) (Nq N) P) @ acc)"
          using "1.IH"(4)
          by (simp add: v0 v1 Some)

        show ?thesis
          using main_block stepI nd_block
          by simp
      next
        case TB0: None
        show ?thesis
        proof (cases "try_newton p a b N P ?v")
          case (Some I)
          have nd_newton:
            "newdsc p a b N P = newdsc p (fst I) (snd I) (Nq N) P"
            by (simp add: "1.hyps" newdsc.psimps v0 v1 TB0 Some)

          have main_newton:
            "newdsc_main p P ((a,b,N) # todo) acc =
             newdsc_main p P ((fst I, snd I, Nq N) # todo) acc"
            by (simp add: newdsc_main.simps Let_def v0 v1 TB0 Some)

          have stepI:
            "newdsc_main p P ((fst I, snd I, Nq N) # todo) acc =
             newdsc_main p P todo (rev (newdsc p (fst I) (snd I) (Nq N) P) @ acc)"
            using "1.IH"(3) Some TB0 v0 v1 by blast

          show ?thesis
            using main_newton stepI nd_newton
            by simp
        next
          case TN0: None
          define m where "m = (a + b) / 2"
          define N' where "N' = Nlin N"
          let ?mid = "(if poly P m = 0 then [(m,m)] else [])"

          have nd_split:
            "newdsc p a b N P = ?mid @ newdsc p a m N' P @ newdsc p m b N' P"
            by (simp add: "1.hyps" newdsc.psimps Let_def v0 v1 TB0 TN0 m_def N'_def)

          have main_split:
            "newdsc_main p P ((a,b,N) # todo) acc =
             newdsc_main p P ((a,m,N') # (m,b,N') # todo) (?mid @ acc)"
            using newdsc_main.simps Let_def v0 v1 TB0 TN0 m_def N'_def 
            by (smt (verit) append.simps(2) list.case(2) option.case(1) self_append_conv2 split_conv)

          have stepL:
            "newdsc_main p P ((a,m,N') # (m,b,N') # todo) (?mid @ acc) =
             newdsc_main p P ((m,b,N') # todo)
               (rev (newdsc p a m N' P) @ (?mid @ acc))"
            using "1.IH"(1)
            by (simp add: v0 v1 TB0 TN0 m_def N'_def)

          have stepR:
            "newdsc_main p P ((m,b,N') # todo) (rev (newdsc p a m N' P) @ (?mid @ acc)) =
             newdsc_main p P todo
               (rev (newdsc p m b N' P) @ (rev (newdsc p a m N' P) @ (?mid @ acc)))"
            using "1.IH"(2)
            by (simp add: v0 v1 TB0 TN0 m_def N'_def)

          have LHS_rewrite:
            "newdsc_main p P ((a,b,N) # todo) acc =
             newdsc_main p P todo
               (rev (newdsc p m b N' P) @ rev (newdsc p a m N' P) @ ?mid @ acc)"
            using main_split stepL stepR
            by simp

          have RHS_rewrite:
            "newdsc_main p P todo (rev (newdsc p a b N P) @ acc) =
             newdsc_main p P todo
               (rev (newdsc p m b N' P) @ rev (newdsc p a m N' P) @ ?mid @ acc)"
            using nd_split
            by simp

          show ?thesis
            using LHS_rewrite RHS_rewrite
            by simp
        qed
      qed
    qed
  qed
qed

lemma newdsc_tr_eq_newdsc:
  assumes dom: "newdsc_dom (p,a,b,N,P)"
  shows "newdsc_tr p a b N P = newdsc p a b N P"
  unfolding newdsc_tr_def
  using newdsc_main_sim[OF dom, of "[]::(real\<times>real\<times>nat) list" "[]::(real\<times>real) list"]
  by (simp add: newdsc_main.simps)

type_synonym taskC = "real \<times> real \<times> nat \<times> real list"
(* (a,b,N,xs), intended invariant: xs = Bernstein_coeffs p a b P *)

definition Bernstein_changes_coeffs :: "real list \<Rightarrow> int" where
  "Bernstein_changes_coeffs xs = int (nat (changes xs))"

lemma Bernstein_changes_coeffs_eq:
  assumes "xs = Bernstein_coeffs p a b P"
  shows   "Bernstein_changes_coeffs xs = Bernstein_changes p a b P"
  using assms
  by (simp add: Bernstein_changes_coeffs_def Bernstein_changes_def)

partial_function (tailrec) newdsc_main_cache ::
  "nat \<Rightarrow> real poly \<Rightarrow> taskC list \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list"
where
  [code]:
  "newdsc_main_cache p P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b,N,xs) # todo' \<Rightarrow>
          (let v = Bernstein_changes_coeffs xs in
           if v = 0 then
             newdsc_main_cache p P todo' acc
           else if v = 1 then
             newdsc_main_cache p P todo' ((a,b) # acc)
           else
             (case try_blocks p a b N P v of
                Some I \<Rightarrow>
                  newdsc_main_cache p P
                    ((fst I, snd I, Nq N, Bernstein_coeffs p (fst I) (snd I) P) # todo') acc
              | None \<Rightarrow>
                  (case try_newton p a b N P v of
                     Some I \<Rightarrow>
                       newdsc_main_cache p P
                         ((fst I, snd I, Nq N, Bernstein_coeffs p (fst I) (snd I) P) # todo') acc
                   | None \<Rightarrow>
                       (let m  = (a + b) / 2;
                            N' = Nlin N;
                            mid = (if poly P m = 0 then [(m,m)] else []);
                            xsL = dc_left (1/2) xs;
                            xsR = dc_right (1/2) xs
                        in newdsc_main_cache p P ((a,m,N',xsL) # (m,b,N',xsR) # todo') (mid @ acc))))))"


definition newdsc_tr_cache ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "newdsc_tr_cache p a b N P =
     rev (newdsc_main_cache p P
            ([(a, b, N, Bernstein_coeffs p a b P)] :: taskC list)
            ([] :: (real \<times> real) list))"


lemma newdsc_main_cache_sim:
  assumes dom:   "newdsc_dom (p,a,b,N,P)"
      and xs_ok: "xs = Bernstein_coeffs p a b P"
      and deg: "degree P \<le> p"
      and ab:  "a < b"
  shows
    "newdsc_main_cache p P ((a,b,N,xs) # todo) acc =
     newdsc_main_cache p P todo (rev (newdsc p a b N P) @ acc)"
  using dom xs_ok ab deg
proof (induction p a b N P arbitrary: todo acc xs rule: newdsc.pinduct)
  case (1 p a b N P todo acc xs)
  let ?v = "Bernstein_changes p a b P"
  have v_eq: "Bernstein_changes_coeffs xs = ?v"
    using Bernstein_changes_coeffs_eq[OF "1.prems"(1)] .
  have deg': "degree P \<le> p" and ab': "a < b"
    using "1.prems" "1.hyps" by blast+

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have nd0: "newdsc p a b N P = []"
      by (simp add: "1.hyps" newdsc.psimps v0)
    show ?thesis
      by (simp add: newdsc_main_cache.simps Let_def v_eq v0 nd0)
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have nd1: "newdsc p a b N P = [(a,b)]"
        by (simp add: "1.hyps" newdsc.psimps v1)
      show ?thesis
        by (simp add: newdsc_main_cache.simps Let_def v_eq v0 v1 nd1)
    next
      case v1: False
      show ?thesis
      proof (cases "try_blocks p a b N P ?v")
        case (Some I)
        have nd_block:
          "newdsc p a b N P = newdsc p (fst I) (snd I) (Nq N) P"
          by (simp add: "1.hyps" newdsc.psimps v0 v1 Some)

        have main_block:
          "newdsc_main_cache p P ((a,b,N,xs) # todo) acc =
           newdsc_main_cache p P
             ((fst I, snd I, Nq N, Bernstein_coeffs p (fst I) (snd I) P) # todo) acc"
          by (simp add: newdsc_main_cache.simps Let_def v_eq v0 v1 Some)

        have stepI:
          "newdsc_main_cache p P
             ((fst I, snd I, Nq N, Bernstein_coeffs p (fst I) (snd I) P) # todo) acc =
           newdsc_main_cache p P todo
             (rev (newdsc p (fst I) (snd I) (Nq N) P) @ acc)"
          using "1.IH" v0 v1 Some 
          by (smt (verit, ccfv_SIG) Bernstein_changes_point ab' deg' div_by_0 divide_pos_pos of_nat_eq_0_iff
              of_nat_le_0_iff option.distinct(1) option.inject split_pairs2 try_blocks_def)

        show ?thesis
          using main_block stepI nd_block
          by simp
      next
        case TB0: None
        show ?thesis
        proof (cases "try_newton p a b N P ?v")
          case (Some I)
          have nd_newton:
            "newdsc p a b N P = newdsc p (fst I) (snd I) (Nq N) P"
            by (simp add: "1.hyps" newdsc.psimps v0 v1 TB0 Some)

          have main_newton:
            "newdsc_main_cache p P ((a,b,N,xs) # todo) acc =
             newdsc_main_cache p P
               ((fst I, snd I, Nq N, Bernstein_coeffs p (fst I) (snd I) P) # todo) acc"
            by (simp add: newdsc_main_cache.simps Let_def v_eq v0 v1 TB0 Some)

          have v_ge2: "?v \<ge> 2"
          using v0 v1
          by (metis Bernstein_changes_def Bernstein_changes_point int_one_le_iff_zero_less not_le_imp_less
              of_nat_le_0_iff one_add_one order_le_less zless_imp_add1_zle)
          
          have Npos: "N > 0"
            proof (rule ccontr)
              assume "\<not> N > 0"
              hence N0: "N = 0" by simp
              have TN_None: "try_newton p a b N P ?v = None"
                unfolding try_newton_def Let_def snap_window_def
                using N0 v_ge2 Bernstein_changes_point
                by (auto split: option.split)
              show False
                using Some TN_None by simp
            qed

          have aux: "snd I - fst I = (b - a) / of_nat N" using Some ab' deg' try_newton_SomeD Npos by auto

          have I_ab: "fst I < snd I"
            using Some ab' deg' aux 
            by (metis Npos diff_gt_0_iff_gt divide_pos_pos of_nat_0_less_iff)

          have stepI:
            "newdsc_main_cache p P
               ((fst I, snd I, Nq N, Bernstein_coeffs p (fst I) (snd I) P) # todo) acc =
             newdsc_main_cache p P todo
               (rev (newdsc p (fst I) (snd I) (Nq N) P) @ acc)"
            using "1.IH"(3) v0 v1 TB0 Some deg' I_ab by blast

          show ?thesis
            using main_newton stepI nd_newton
            by simp
        next
          case TN0: None
          define m where "m = (a + b) / 2"
          define N' where "N' = Nlin N"
          let ?mid = "(if poly P m = 0 then [(m,m)] else [])"
          let ?xsL = "dc_left (1/2) xs"
          let ?xsR = "dc_right (1/2) xs"

          have am: "a < m" and mb: "m < b"
            using ab' by (simp_all add: m_def)

          have t_half: "(m - a) / (b - a) = (1/2::real)"
            using ab' by (simp add: m_def field_simps)

          have xsL_ok:
            "?xsL = Bernstein_coeffs p a m P"
          proof -
            have "Bernstein_coeffs p a m P =
                  dc_left ((m - a) / (b - a)) (Bernstein_coeffs p a b P)"
              using Bernstein_coeffs_split(1) am deg' mb by blast
            thus ?thesis
              using xs_ok t_half "1.prems"(1) by presburger
          qed

          have xsR_ok:
            "?xsR = Bernstein_coeffs p m b P"
          proof -
            have "Bernstein_coeffs p m b P =
                  dc_right ((m - a) / (b - a)) (Bernstein_coeffs p a b P)"
              using Bernstein_coeffs_split(2) am deg' mb by blast
            thus ?thesis
              using xs_ok t_half "1.prems"(1) by presburger
          qed

          have nd_split:
            "newdsc p a b N P = ?mid @ newdsc p a m N' P @ newdsc p m b N' P"
            by (simp add: "1.hyps" newdsc.psimps Let_def v0 v1 TB0 TN0 m_def N'_def)

          have main_split:
            "newdsc_main_cache p P ((a,b,N,xs) # todo) acc =
             newdsc_main_cache p P ((a,m,N',?xsL) # (m,b,N',?xsR) # todo) (?mid @ acc)"
            using newdsc_main_cache.simps Let_def v_eq v0 v1 TB0 TN0 m_def N'_def
            by (smt (verit) append.simps(2) list.case(2) option.case(1) self_append_conv2 split_conv)

          have stepL:
            "newdsc_main_cache p P ((a,m,N',?xsL) # (m,b,N',?xsR) # todo) (?mid @ acc) =
             newdsc_main_cache p P ((m,b,N',?xsR) # todo)
               (rev (newdsc p a m N' P) @ (?mid @ acc))"
            using "1.IH" v0 v1 TB0 TN0 m_def N'_def xsL_ok am deg' by blast

          have stepR:
            "newdsc_main_cache p P ((m,b,N',?xsR) # todo)
               (rev (newdsc p a m N' P) @ (?mid @ acc)) =
             newdsc_main_cache p P todo
               (rev (newdsc p m b N' P) @ (rev (newdsc p a m N' P) @ (?mid @ acc)))"
            using "1.IH" v0 v1 TB0 TN0 m_def N'_def xsR_ok mb deg' by presburger

          have LHS_rewrite:
            "newdsc_main_cache p P ((a,b,N,xs) # todo) acc =
             newdsc_main_cache p P todo
               (rev (newdsc p m b N' P) @ rev (newdsc p a m N' P) @ ?mid @ acc)"
            using main_split stepL stepR
            by simp

          have RHS_rewrite:
            "newdsc_main_cache p P todo (rev (newdsc p a b N P) @ acc) =
             newdsc_main_cache p P todo
               (rev (newdsc p m b N' P) @ rev (newdsc p a m N' P) @ ?mid @ acc)"
            using nd_split
            by simp

          show ?thesis
            using LHS_rewrite RHS_rewrite
            by simp
        qed
      qed
    qed
  qed
qed


lemma newdsc_tr_cache_eq_newdsc:
  assumes dom: "newdsc_dom (p,a,b,N,P)"
      and deg: "degree P \<le> p"
      and ab:  "a < b"
  shows "newdsc_tr_cache p a b N P = newdsc p a b N P"
  unfolding newdsc_tr_cache_def
  using newdsc_main_cache_sim[OF dom, of "Bernstein_coeffs p a b P" "[]::taskC list" "[]::(real\<times>real) list"]
  by (simp add: ab deg newdsc_main_cache.simps)

definition try_blocks_nob ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> int \<Rightarrow> (real \<times> real) option"
where
  "try_blocks_nob a b N P v =
     (let w = b - a;
          B1 = (a, a + w / of_nat N);
          B2 = (b - w / of_nat N, b);
          v1 = descartes_roots_test (snd B1) (fst B1) P;
          v2 = descartes_roots_test (snd B2) (fst B2) P
      in if v1 = v then Some B1 else if v2 = v then Some B2 else None)"

lemma try_block_eq:
  assumes "p = degree P"
  shows "try_blocks_nob a b N P v = try_blocks p a b N P v"
  using assms descartes_roots_test_eq_Bernstein_changes try_blocks_def try_blocks_nob_def
  by presburger

definition try_newton_nob ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> int \<Rightarrow> (real \<times> real) option"
where
  "try_newton_nob a b N P v =
     (let L1 = newton_at v P a; L2 = newton_at v P b in
      case L1 of
        Some lam1 \<Rightarrow>
          (let I1 = snap_window a b N lam1;
               v1 = descartes_roots_test (snd I1) (fst I1) P
           in if v1 = v then Some I1
              else (case L2 of
                      Some lam2 \<Rightarrow>
                        (let I2 = snap_window a b N lam2;
                             v2 = descartes_roots_test (snd I2) (fst I2) P
                         in if v2 = v then Some I2 else None)
                    | None \<Rightarrow> None))
      | None \<Rightarrow>
          (case L2 of
             Some lam2 \<Rightarrow>
               (let I2 = snap_window a b N lam2;
                    v2 = descartes_roots_test (snd I2) (fst I2) P
                in if v2 = v then Some I2 else None)
           | None \<Rightarrow> None))"

lemma try_newton_eq:
  assumes "p = degree P"
  shows "try_newton_nob a b N P v = try_newton p a b N P v"
  using assms descartes_roots_test_eq_Bernstein_changes try_newton_def try_newton_nob_def
  by presburger

partial_function (tailrec) newdsc_main_nob ::
  "real poly \<Rightarrow> (real \<times> real \<times> nat) list \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list"
where
  [code]:
  "newdsc_main_nob P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b,N) # todo' \<Rightarrow>
          (let v = descartes_roots_test b a P in
           if v = 0 then
             newdsc_main_nob P todo' acc
           else if v = 1 then
             newdsc_main_nob P todo' ((a,b) # acc)
           else
             (case try_blocks_nob a b N P v of
                Some I \<Rightarrow>
                  newdsc_main_nob P ((fst I, snd I, Nq N) # todo') acc
              | None \<Rightarrow>
                  (case try_newton_nob a b N P v of
                     Some I \<Rightarrow>
                       newdsc_main_nob P ((fst I, snd I, Nq N) # todo') acc
                   | None \<Rightarrow>
                       (let m  = (a + b) / 2;
                            N' = Nlin N;
                            acc' = (if poly P m = 0 then (m,m) # acc else acc)
                        in newdsc_main_nob P ((a,m,N') # (m,b,N') # todo') acc')))))"

definition newdsc_tr_nob ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "newdsc_tr_nob a b N P = newdsc_main_nob P [(a,b,N)] []"

lemma newdsc_main_nob_sim:
  assumes dom:  "newdsc_dom (p,a,b,N,P)"
      and pdeg: "p = degree P"
  shows
    "newdsc_main_nob P ((a,b,N) # todo) acc =
     newdsc_main_nob P todo (rev (newdsc p a b N P) @ acc)"
  using dom pdeg
proof (induction p a b N P arbitrary: todo acc rule: newdsc.pinduct)
  case (1 p a b N P todo acc)
  let ?v = "Bernstein_changes p a b P"

  have deg_p: "degree P = p"
    using "1.prems" by (simp add: eq_commute)

  have v_eq: "descartes_roots_test b a P = ?v"
    using deg_p by (simp add: descartes_roots_test_eq_Bernstein_changes)

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have nd0: "newdsc p a b N P = []"
      by (simp add: "1.hyps" newdsc.psimps v0)
    show ?thesis
      using nd0 newdsc_main_nob.simps Let_def v0 v_eq by auto
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have nd1: "newdsc p a b N P = [(a,b)]"
        by (simp add: "1.hyps" newdsc.psimps v1)
      show ?thesis
        using nd1 newdsc_main_nob.simps Let_def v0 v1 v_eq by auto
    next
      case v1: False

      show ?thesis
      proof (cases "try_blocks p a b N P ?v")
        case (Some I)
        have nd_block:
          "newdsc p a b N P = newdsc p (fst I) (snd I) (Nq N) P"
          by (simp add: "1.hyps" newdsc.psimps v0 v1 Some)

        have main_block:
          "newdsc_main_nob P ((a,b,N) # todo) acc =
           newdsc_main_nob P ((fst I, snd I, Nq N) # todo) acc"
          using Some newdsc_main_nob.simps Let_def v0 v1 v_eq
                try_block_eq "1.prems" 
          by simp

        have stepI:
          "newdsc_main_nob P ((fst I, snd I, Nq N) # todo) acc =
           newdsc_main_nob P todo (rev (newdsc p (fst I) (snd I) (Nq N) P) @ acc)"
          using "1.IH" v0 v1 Some deg_p by presburger

        show ?thesis
          using main_block stepI nd_block
          by simp
      next
        case TB0: None
        show ?thesis
        proof (cases "try_newton p a b N P ?v")
          case (Some I)
          have nd_newton:
            "newdsc p a b N P = newdsc p (fst I) (snd I) (Nq N) P"
            by (simp add: "1.hyps" newdsc.psimps v0 v1 TB0 Some)

          have main_newton:
            "newdsc_main_nob P ((a,b,N) # todo) acc =
             newdsc_main_nob P ((fst I, snd I, Nq N) # todo) acc"
            using TB0 Some newdsc_main_nob.simps Let_def v0 v1 v_eq
                  try_block_eq try_newton_eq deg_p 
            by force

          have stepI:
            "newdsc_main_nob P ((fst I, snd I, Nq N) # todo) acc =
             newdsc_main_nob P todo (rev (newdsc p (fst I) (snd I) (Nq N) P) @ acc)"
            using "1.IH"(3) v0 v1 TB0 Some deg_p by force

          show ?thesis
            using main_newton stepI nd_newton
            by simp
        next
          case TN0: None
          define m  where "m  = (a + b) / 2"
          define N' where "N' = Nlin N"
          let ?mid = "(if poly P m = 0 then [(m,m)] else [])"

          have nd_split:
            "newdsc p a b N P = ?mid @ newdsc p a m N' P @ newdsc p m b N' P"
            by (simp add: "1.hyps" newdsc.psimps Let_def v0 v1 TB0 TN0 m_def N'_def)

          have mid_acc_eq:
            "(if poly P m = 0 then (m,m) # acc else acc) = ?mid @ acc"
            by (cases "poly P m = 0"; simp)

          have main_split:
            "newdsc_main_nob P ((a,b,N) # todo) acc =
             newdsc_main_nob P ((a,m,N') # (m,b,N') # todo) (?mid @ acc)"
          proof -
            have tmp:
              "newdsc_main_nob P ((a,b,N) # todo) acc =
               newdsc_main_nob P ((a,m,N') # (m,b,N') # todo)
                 (if poly P m = 0 then (m,m) # acc else acc)"
              by (smt (verit) TB0 TN0 newdsc_main_nob.simps Let_def v0 v1 v_eq m_def N'_def
                    try_block_eq try_newton_eq deg_p list.case(2) option.case(1) prod.simps(2))
            show ?thesis
              using tmp by (simp add: mid_acc_eq)
          qed

          have stepL:
            "newdsc_main_nob P ((a,m,N') # (m,b,N') # todo) (?mid @ acc) =
             newdsc_main_nob P ((m,b,N') # todo)
               (rev (newdsc p a m N' P) @ (?mid @ acc))"
            using "1.IH"(1) v0 v1 TB0 TN0 m_def N'_def deg_p 
            by blast

          have stepR:
            "newdsc_main_nob P ((m,b,N') # todo)
               (rev (newdsc p a m N' P) @ (?mid @ acc)) =
             newdsc_main_nob P todo
               (rev (newdsc p m b N' P) @ (rev (newdsc p a m N' P) @ (?mid @ acc)))"
            using "1.IH"(2) v0 v1 TB0 TN0 m_def N'_def deg_p by blast

          have LHS_rewrite:
            "newdsc_main_nob P ((a,b,N) # todo) acc =
             newdsc_main_nob P todo
               (rev (newdsc p m b N' P) @ rev (newdsc p a m N' P) @ ?mid @ acc)"
            using main_split stepL stepR
            by simp

          have RHS_rewrite:
            "newdsc_main_nob P todo (rev (newdsc p a b N P) @ acc) =
             newdsc_main_nob P todo
               (rev (newdsc p m b N' P) @ rev (newdsc p a m N' P) @ ?mid @ acc)"
            using nd_split
            by simp

          show ?thesis
            using LHS_rewrite RHS_rewrite
            by simp
        qed
      qed
    qed
  qed
qed

lemma newdsc_tr_nob_eq_newdsc:
  assumes dom:  "newdsc_dom (p,a,b,N,P)"
      and pdeg: "p = degree P"
  shows "rev (newdsc_tr_nob a b N P) = newdsc p a b N P"
proof -
  have tr: "newdsc_tr_nob a b N P = rev (newdsc p a b N P)"
    unfolding newdsc_tr_nob_def
    using newdsc_main_nob_sim[OF dom pdeg, of "[]::(real\<times>real\<times>nat) list" "[]::(real\<times>real) list"]
    by (simp add: newdsc_main_nob.simps)
  show ?thesis
    using tr by simp
qed



end