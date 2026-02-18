theory Radical
  imports Polynomial_Factorization.Square_Free_Factorization
          Polynomial_Factorization.Gcd_Rat_Poly
          Sturm_Sequences.Misc_Polynomial
begin

lemma poly_prod_list_eq_0_iff:
  fixes fs :: "'a::idom poly list"
  shows "poly (prod_list fs) x = 0 \<longleftrightarrow> (\<exists>f\<in>set fs. poly f x = 0)"
proof (induction fs)
  case Nil
  show ?case by simp
next
  case (Cons f fs)
  have "poly (prod_list (f # fs)) x = 0 \<longleftrightarrow> poly (f * prod_list fs) x = 0"
    by simp
  also have "\<dots> \<longleftrightarrow> (poly f x * poly (prod_list fs) x = 0)"
    by simp
  also have "\<dots> \<longleftrightarrow> (poly f x = 0 \<or> poly (prod_list fs) x = 0)"
    by simp
  also have "\<dots> \<longleftrightarrow> (poly f x = 0 \<or> (\<exists>g\<in>set fs. poly g x = 0))"
    using Cons.IH by simp
  also have "\<dots> \<longleftrightarrow> (\<exists>g\<in>set (f # fs). poly g x = 0)"
    by simp
  finally show ?case .
qed



definition radical_rat_poly :: "rat poly \<Rightarrow> rat poly" where
  "radical_rat_poly p =
     (if p = 0 then 0
      else let (c,bs) = yun_factorization gcd_rat_poly p
           in prod_list (map fst bs))"

lemma radical_rat_poly_square_free:
  assumes "p \<noteq> (0 :: rat poly)"
  shows "square_free (radical_rat_poly p)"
proof -
  obtain c bs where H: "yun_factorization gcd p = (c, bs)"
    by (cases "yun_factorization gcd p") auto

  have sff: "square_free_factorization p (c, bs)"
    using yun_factorization[OF H] by blast

  have sf_prod: "square_free (prod_list (map fst bs))"
    using square_free_factorizationD'[OF sff] by blast

  show ?thesis
    using assms sf_prod H
    by (simp add: radical_rat_poly_def)
qed

lemma radical_rat_poly_same_roots:
  shows "poly (radical_rat_poly p) x = 0 \<longleftrightarrow> poly p x = 0"
proof (cases "p = (0 :: rat poly)")
  case True
  then show ?thesis
    by (simp add: radical_rat_poly_def)
next
  case False

  obtain c bs where H: "yun_factorization gcd p = (c, bs)"
    by (cases "yun_factorization gcd p") auto

  have sff: "square_free_factorization p (c, bs)"
    using yun_factorization[OF H] by blast

  have RootsP:
    "{x. poly p x = 0} = {x. \<exists>a i. (a,i) \<in> set bs \<and> poly a x = 0}"
    using square_free_factorization_root[OF sff False] .

  have rad_eq: "radical_rat_poly p = prod_list (map fst bs)"
    using False H by (simp add: radical_rat_poly_def)

  have RootsRad_pointwise:
    "poly (radical_rat_poly p) x = 0 \<longleftrightarrow> (\<exists>a i. (a,i) \<in> set bs \<and> poly a x = 0)"
  proof -
    have "poly (radical_rat_poly p) x = 0 \<longleftrightarrow> poly (prod_list (map fst bs)) x = 0"
      by (simp add: rad_eq)
    also have "\<dots> \<longleftrightarrow> (\<exists>f\<in>set (map fst bs). poly f x = 0)"
      by (simp add: poly_prod_list_eq_0_iff)
    also have "\<dots> \<longleftrightarrow> (\<exists>a i. (a,i) \<in> set bs \<and> poly a x = 0)"
      by force
    finally show ?thesis .
  qed

  have "poly p x = 0 \<longleftrightarrow> (\<exists>a i. (a,i) \<in> set bs \<and> poly a x = 0)"
    using RootsP by auto

  thus ?thesis
    using RootsRad_pointwise by blast
qed

lemma square_free_liftR:
  assumes"square_free (p::(rat poly))"
  shows "square_free(map_poly (of_rat :: rat \<Rightarrow> real) p)"
  by (simp add: assms field_hom_0'.intro field_hom_0'.square_free_map_poly
      of_rat_hom.field_hom_axioms)

lemma of_rat_sum_atMost:
  fixes g :: "nat \<Rightarrow> rat"
  shows "of_rat (\<Sum>i\<le>n. g i) = (\<Sum>i\<le>n. (of_rat (g i) :: real))"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "of_rat (\<Sum>i\<le>Suc n. g i) = of_rat ((\<Sum>i\<le>n. g i) + g (Suc n))"
    by simp
  also have "... = of_rat (\<Sum>i\<le>n. g i) + (of_rat (g (Suc n)) :: real)"
    using of_rat_add by blast
  also have "... = (\<Sum>i\<le>n. (of_rat (g i) :: real)) + (of_rat (g (Suc n)) :: real)"
    using Suc.IH by simp
  also have "... = (\<Sum>i\<le>Suc n. (of_rat (g i) :: real))"
    by simp
  finally show ?case .
qed

lemma map_poly_mult_of_rat_real:
  fixes p q :: "rat poly"
  shows "map_poly (of_rat :: rat \<Rightarrow> real) (p * q)
       = map_poly (of_rat :: rat \<Rightarrow> real) p * map_poly (of_rat :: rat \<Rightarrow> real) q"
proof -
  have coeff_eq:
    "\<And>n. coeff (map_poly (of_rat :: rat \<Rightarrow> real) (p * q)) n =
         coeff (map_poly (of_rat :: rat \<Rightarrow> real) p * map_poly (of_rat :: rat \<Rightarrow> real) q) n"
  proof-
    fix n
    have LHS:
      "coeff (map_poly (of_rat :: rat \<Rightarrow> real) (p * q)) n
       = of_rat (\<Sum>i\<le>n. coeff p i * coeff q (n - i))"
      by (simp add: coeff_mult)

    have RHS:
      "coeff (map_poly (of_rat :: rat \<Rightarrow> real) p * map_poly (of_rat :: rat \<Rightarrow> real) q) n
       = (\<Sum>i\<le>n. (of_rat (coeff p i) :: real) * (of_rat (coeff q (n - i)) :: real))"
      by (simp add: coeff_mult)

    show
      "coeff (map_poly (of_rat :: rat \<Rightarrow> real) (p * q)) n =
       coeff (map_poly (of_rat :: rat \<Rightarrow> real) p * map_poly (of_rat :: rat \<Rightarrow> real) q) n"
      unfolding LHS RHS
      by (simp add: of_rat_hom.hom_mult of_rat_hom.hom_sum)
  qed

  show ?thesis
    using coeff_eq poly_eqI by blast
qed

lemma map_poly_prod_list_of_rat_real:
  fixes ps :: "rat poly list"
  shows "map_poly (of_rat :: rat \<Rightarrow> real) (prod_list ps)
       = prod_list (map (map_poly (of_rat :: rat \<Rightarrow> real)) ps)"
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case
    by (simp add: map_poly_mult_of_rat_real)
qed

lemma map_poly_pow_of_rat_real:
  fixes p :: "rat poly"
  shows "map_poly (of_rat :: rat \<Rightarrow> real) (p ^ n) =
         (map_poly (of_rat :: rat \<Rightarrow> real) p) ^ n"
  by (induction n) (simp_all add: map_poly_mult_of_rat_real)

lemma map_map_pow:
  "map (map_poly (of_rat :: rat \<Rightarrow> real)) (map (\<lambda>(a,i). a ^ i) bs)
   = map (\<lambda>ai. (map_poly (of_rat :: rat \<Rightarrow> real) (fst ai)) ^ snd ai) bs"
proof (induction bs)
  case Nil
  show ?case by simp
next
  case (Cons ai bs)
  obtain a i where ai: "ai = (a,i)" by (cases ai) auto
  show ?case
    using Cons.IH
    by (simp add: ai map_poly_pow_of_rat_real)
qed

lemma radical_rat_poly_same_roots_real:
  fixes p :: "rat poly" and x :: real
  shows "poly (map_poly (of_rat :: rat \<Rightarrow> real) (radical_rat_poly p)) x = 0 \<longleftrightarrow>
         poly (map_poly (of_rat :: rat \<Rightarrow> real) p) x = 0"
proof (cases "p = (0 :: rat poly)")
  case True
  then show ?thesis by (simp add: radical_rat_poly_def)
next
  case False

  obtain c bs where H: "yun_factorization gcd_rat_poly p = (c, bs)"
    by (cases "yun_factorization gcd_rat_poly p") auto

  have sff: "square_free_factorization p (c, bs)"
    using yun_factorization
    by (metis H gcd_rat_poly)

  have fac: "p = smult c (prod_list (map (\<lambda>(a,i). a ^ i) bs))"
    using square_free_factorization_prod_list[OF sff] .

  have ipos: "\<And>a i. (a,i) \<in> set bs \<Longrightarrow> i > 0"
    using square_free_factorizationD[OF sff] by blast

  have c0: "c \<noteq> 0"
  proof
    assume "c = 0"
    with fac have "p = 0" by simp
    with False show False by simp
  qed

  have rad_eq: "radical_rat_poly p = prod_list (map fst bs)"
    using False H by (simp add: radical_rat_poly_def)

  have roots_rad:
    "poly (map_poly (of_rat :: rat \<Rightarrow> real) (radical_rat_poly p)) x = 0 \<longleftrightarrow>
     (\<exists>a i. (a,i) \<in> set bs \<and> poly (map_poly (of_rat :: rat \<Rightarrow> real) a) x = 0)"
  proof -
    have "poly (map_poly (of_rat :: rat \<Rightarrow> real) (radical_rat_poly p)) x = 0
          \<longleftrightarrow> poly (map_poly (of_rat :: rat \<Rightarrow> real) (prod_list (map fst bs))) x = 0"
      by (simp add: rad_eq)
    also have "\<dots> \<longleftrightarrow> poly (prod_list (map (map_poly (of_rat :: rat \<Rightarrow> real)) (map fst bs))) x = 0"
      by (simp add: map_poly_prod_list_of_rat_real)
    also have "\<dots> \<longleftrightarrow> (\<exists>f\<in>set (map (map_poly (of_rat :: rat \<Rightarrow> real)) (map fst bs)).
                      poly f x = 0)"
      by (simp add: poly_prod_list_eq_0_iff)
    also have "\<dots> \<longleftrightarrow> (\<exists>a i. (a,i) \<in> set bs \<and> poly (map_poly (of_rat :: rat \<Rightarrow> real) a) x = 0)"
      by force
    finally show ?thesis .
  qed

  have roots_p:
    "poly (map_poly (of_rat :: rat \<Rightarrow> real) p) x = 0 \<longleftrightarrow>
     (\<exists>a i. (a,i) \<in> set bs \<and> poly (map_poly (of_rat :: rat \<Rightarrow> real) a) x = 0)"
  proof -
    let ?fs = "map (\<lambda>ai. (map_poly (of_rat :: rat \<Rightarrow> real) (fst ai)) ^ snd ai) bs"

    have map_p:
      "map_poly (of_rat :: rat \<Rightarrow> real) p =
       smult (of_rat c) (prod_list ?fs)"
    proof -
      have "map_poly (of_rat :: rat \<Rightarrow> real) p =
            map_poly (of_rat :: rat \<Rightarrow> real)
              (smult c (prod_list (map (\<lambda>(a,i). a ^ i) bs)))"
        by (simp add: fac)
      also have "\<dots> =
        smult (of_rat c)
          (map_poly (of_rat :: rat \<Rightarrow> real) (prod_list (map (\<lambda>(a,i). a ^ i) bs)))"
      using of_rat_hom.map_poly_hom_smult by blast
      also have "\<dots> =
        smult (of_rat c)
          (prod_list (map (map_poly (of_rat :: rat \<Rightarrow> real)) (map (\<lambda>(a,i). a ^ i) bs)))"
        by (simp add: map_poly_prod_list_of_rat_real)
      also have "\<dots> = smult (of_rat c) (prod_list ?fs)"
        using map_map_pow by presburger
      finally show ?thesis .
    qed

    have pow_factor0:
      "poly (prod_list ?fs) x = 0 \<longleftrightarrow>
       (\<exists>a i. (a,i) \<in> set bs \<and> poly (map_poly (of_rat :: rat \<Rightarrow> real) a) x = 0)"
    proof -
      have "poly (prod_list ?fs) x = 0 \<longleftrightarrow> (\<exists>f\<in>set ?fs. poly f x = 0)"
        by (simp add: poly_prod_list_eq_0_iff)
      also have "\<dots> \<longleftrightarrow> (\<exists>a i. (a,i) \<in> set bs \<and> poly ((map_poly (of_rat :: rat \<Rightarrow> real) a) ^ i) x = 0)"
        by force
      also have "\<dots> \<longleftrightarrow> (\<exists>a i. (a,i) \<in> set bs \<and> poly (map_poly (of_rat :: rat \<Rightarrow> real) a) x = 0)"
      proof
        assume "\<exists>a i. (a,i) \<in> set bs \<and> poly ((map_poly (of_rat :: rat \<Rightarrow> real) a) ^ i) x = 0"
        then obtain a i where ai: "(a,i) \<in> set bs"
          and rt: "poly ((map_poly (of_rat :: rat \<Rightarrow> real) a) ^ i) x = 0" by blast
        have "i > 0" using ipos[OF ai] .
        then have "poly ((map_poly (of_rat :: rat \<Rightarrow> real) a) ^ i) x = 0 \<longleftrightarrow>
                   poly (map_poly (of_rat :: rat \<Rightarrow> real) a) x = 0"
          using poly_power_zero_iff by blast
        with rt ai show "\<exists>a i. (a,i) \<in> set bs \<and> poly (map_poly (of_rat :: rat \<Rightarrow> real) a) x = 0"
          by blast
      next
        assume "\<exists>a i. (a,i) \<in> set bs \<and> poly (map_poly (of_rat :: rat \<Rightarrow> real) a) x = 0"
        then obtain a i where ai: "(a,i) \<in> set bs"
          and rt: "poly (map_poly (of_rat :: rat \<Rightarrow> real) a) x = 0" by blast
        have "i > 0" using ipos[OF ai] .
        then have "poly ((map_poly (of_rat :: rat \<Rightarrow> real) a) ^ i) x = 0"
          by (simp add: rt)
        with ai show "\<exists>a i. (a,i) \<in> set bs \<and> poly ((map_poly (of_rat :: rat \<Rightarrow> real) a) ^ i) x = 0"
          by blast
      qed
      finally show ?thesis .
    qed

    have "poly (map_poly (of_rat :: rat \<Rightarrow> real) p) x = 0
          \<longleftrightarrow> poly (smult (of_rat c) (prod_list ?fs)) x = 0"
      by (simp add: map_p)
    also have "\<dots> \<longleftrightarrow> poly (prod_list ?fs) x = 0"
      using c0 by simp
    also have "\<dots> \<longleftrightarrow> (\<exists>a i. (a,i) \<in> set bs \<and> poly (map_poly (of_rat :: rat \<Rightarrow> real) a) x = 0)"
      using pow_factor0 by simp
    finally show ?thesis .
  qed

  show ?thesis
    using roots_rad roots_p by blast
qed

definition radical_real_poly :: "real poly => real poly" where
  "radical_real_poly p =  p div (gcd p (pderiv p))"

lemma radical_real_poly_square_free:
  assumes "p \<noteq> (0 :: real poly)"
  shows "square_free (radical_real_poly p)"
  by (simp add: assms poly_div_gcd_squarefree(1) radical_real_poly_def separable_def
      separable_imp_square_free)

lemma radical_real_poly_rsquarefree:
  assumes "p \<noteq> (0 :: real poly)"
  shows "rsquarefree (radical_real_poly p)"
  by (simp add: assms radical_real_poly_square_free square_free_rsquarefree)

lemma radical_real_poly_same_roots:
  fixes p :: "real poly" and x :: real
  shows "(poly (radical_real_poly p) x = 0) \<longleftrightarrow> (poly p x = 0)"
proof (cases "p = (0 :: real poly)")
  case True
  then show ?thesis by (simp add: radical_real_poly_def)
next
  case False
  have "poly (radical_real_poly p) x = 0  \<longleftrightarrow> poly (p div (gcd p (pderiv p))) x = 0"
    by (simp add: radical_real_poly_def)
  also have "...  \<longleftrightarrow> poly p x = 0"
    using poly_div_gcd_squarefree[of p] by fastforce
  finally show ?thesis .
qed

end



