theory Dsc
  imports
    Dsc_Misc
begin

function (domintros) dsc :: "nat ⇒ real ⇒ real ⇒ real poly ⇒ (real × real) list"
  where
  "dsc p a b P =
    (let v = Bernstein_changes p a b P in
     if v = 0 then []
     else if v = 1 then [(a, b)]
     else
       (let m = (a + b) / 2 in
          (if poly P m = 0 then [(m, m)] else []) @
          dsc p a m P @
          dsc p m b P))"
  by pat_completeness auto

term dsc_dom

find_theorems dsc_dom

thm dsc.pelims

lemma dsc_domI_general:
  fixes δ :: real and p :: nat and P :: "real poly"
  assumes δ_pos: "δ > 0"
    and small: "⋀a b. a < b ⟹ b - a ≤ δ ⟹ Bernstein_changes p a b P ≤ 1"
  shows "⋀a b. a < b ⟹ dsc_dom (p, a, b, P)"
proof -
  define μ where "μ = (λa b. mu δ a b)"
  let ?Prop = "λn::nat. ∀a b. μ a b < n ⟶ a < b ⟶ dsc_dom (p, a, b, P)"

  have step: "⋀n. (⋀m. m < n ⟹ ?Prop m) ⟹ ?Prop n"
  proof -
    fix n
    assume IH: "⋀m. m < n ⟹ ?Prop m"
    show "?Prop n"
    proof (intro allI impI)
      fix a b :: real
      assume mu_lt_n: "μ a b < n"
        and ab: "a < b"
      show "dsc_dom (p, a, b, P)"
      proof -
        let ?v = "Bernstein_changes p a b P"
        show ?thesis
        proof (cases "?v = 0 ∨ ?v = 1")
          case True
          then show ?thesis
            by (auto intro: dsc.domintros)
        next
          case False
          have v_ge2: "2 ≤ ?v"
            using False Bernstein_changes_def
            by fastforce
          have δ_lt_width: "δ < b - a"
          proof (rule ccontr)
            assume "¬ δ < b - a"
            then have width_le_δ: "b - a ≤ δ"
              by linarith
            then have v_le1: "Bernstein_changes p a b P ≤ 1"
              using ab small
              by presburger
            from v_ge2 v_le1 show False
              by linarith
          qed

          define m where "m = (a + b) / 2"
          have am: "a < m"
            and mb: "m < b"
            using ab
            by (simp_all add: m_def)

          have mu_left_strict: "μ a m < μ a b"
            by (simp add: μ_def δ_pos δ_lt_width ab m_def mu_halve_strict(1))

          have mu_right_strict: "μ m b < μ a b"
            by (simp add: μ_def δ_pos δ_lt_width ab m_def mu_halve_strict(2))

          have IH_at_mu: "?Prop (μ a b)"
            using IH mu_lt_n
            by simp

          have dom_left: "dsc_dom (p, a, m, P)"
            using IH_at_mu mu_left_strict am
            by blast

          have dom_right: "dsc_dom (p, m, b, P)"
            using IH_at_mu mu_right_strict mb
            by blast

          show ?thesis
            using dom_left dom_right m_def dsc.domintros by blast            
        qed
      qed
    qed
  qed

  have all_Prop: "⋀n. ?Prop n"
    by (rule less_induct, rule step)

  show "⋀a b. a < b ⟹ dsc_dom (p, a, b, P)"
    using all_Prop by blast
qed



lemma dsc_terminates_squarefree_real:
  fixes P :: "real poly"
  assumes P0: "P ≠ 0"
      and deg: "degree P ≤ p"
      and p0: "p ≠ 0"
      and sf: "square_free P"
  shows "⋀a b. a < b ⟹ dsc_dom (p,a,b,P)"
proof -
  have δ_pos: "delta_P P > 0"
    using P0 delta_P_pos by blast

  have small:
    "⋀a b. a < b ⟹ b - a ≤ delta_P P ⟹ Bernstein_changes p a b P ≤ 1"
  using Bernstein_changes_small_interval_le_1 P0 deg p0 sf rsquarefree_lift
  by blast

  show "⋀a b. a < b ⟹ dsc_dom (p,a,b,P)"
    using dsc_domI_general[OF δ_pos small] .
qed

lemma dsc_sound:
  assumes dom: "dsc_dom (p,a,b,P)"
      and deg: "degree P ≤ p"
      and P0:  "P ≠ 0"
      and ab:  "a < b"
  shows "∀I ∈ set (dsc p a b P). dsc_pair_ok P I"
using dom deg P0 ab
proof (induction p a b P rule: dsc.pinduct)
  case (1 p a b P)

  have dsc_eq:
    "dsc p a b P =
       (let v = Bernstein_changes p a b P in
        if v = 0 then []
        else if v = 1 then [(a,b)]
        else
          (let m = (a + b) / 2 in
             (if poly P m = 0 then [(m,m)] else []) @
             dsc p a m P @
             dsc p m b P))"
    using "1.hyps" dsc.psimps by blast

  show ?case
  proof -
    from 1 have ab: "a < b" and P0': "P ≠ 0"
      apply blast 
      by (simp add: "1.prems"(2))
    from 1 have deg': "degree P ≤ p"
      by blast

    show ?thesis
    proof (subst dsc_eq, simp only: Let_def Ball_def)
      let ?v = "Bernstein_changes p a b P"

      have H0:
        "∀I∈ set (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
                   (let m = (a + b) / 2 in
                      (if poly P m = 0 then [(m, m)] else []) @
                      dsc p a m P @ dsc p m b P)).
           dsc_pair_ok P I"
      proof (cases "?v = 0")
        case True
        then show ?thesis by simp
      next
        case v0: False
        show ?thesis
        proof (cases "?v = 1")
          case True
          hence v1: "Bernstein_changes p a b P = 1"
            by simp
          have "roots_in P a b = 1"
            using Bernstein_changes_1_one_root[OF deg' P0' ab v1] .
          hence "dsc_pair_ok P (a,b)"
            by (simp add: dsc_pair_ok_def roots_in_def ab)
          with v0 True show ?thesis
            by simp
        next
          case v_ge2: False
          hence v2: "?v ≥ 2"
            using v0
            by (smt (verit) Bernstein_changes_def int_nat_eq)
          let ?m = "(a + b) / 2"
          have am: "a < ?m" and mb: "?m < b"
            using ab by simp_all

          have IH_left:
            "∀I∈set (dsc p a ?m P). dsc_pair_ok P I"
            using "1.IH"(1) deg' v0 v_ge2 P0' am by blast

          have IH_right:
            "∀I∈set (dsc p ?m b P). dsc_pair_ok P I"
            using "1.IH"(2) deg' v0 v_ge2 P0' mb by blast
          
          show ?thesis
          proof (simp add: v0 v_ge2 Let_def, intro ballI impI)
            fix I
            assume Ain:
              "I ∈ {x. x = (?m, ?m) ∧ poly P ?m = 0} ∪
                   (set (dsc p a ?m P) ∪ set (dsc p ?m b P))"
            then have disj:
              "I = (?m,?m) ∧ poly P ?m = 0
               ∨ I ∈ set (dsc p a ?m P)
               ∨ I ∈ set (dsc p ?m b P)"
              by auto
            from disj show "dsc_pair_ok P I"
            proof
              assume "I = (?m,?m) ∧ poly P ?m = 0"
              then show "dsc_pair_ok P I"
                by (simp add: dsc_pair_ok_def)
            next
              assume alt:
                "I ∈ set (dsc p a ?m P) ∨ I ∈ set (dsc p ?m b P)"
              from alt show "dsc_pair_ok P I"
              proof
                assume "I ∈ set (dsc p a ?m P)"
                then show "dsc_pair_ok P I"
                  using IH_left by blast
              next
                assume "I ∈ set (dsc p ?m b P)"
                then show "dsc_pair_ok P I"
                  using IH_right by blast
              qed
            qed
          qed
        qed
      qed

      have H:
        "∀I∈set (if Bernstein_changes p a b P = 0 then []
                 else if Bernstein_changes p a b P = 1 then [(a, b)]
                      else (if poly P ((a + b) / 2) = 0
                            then [((a + b) / 2, (a + b) / 2)]
                            else []) @
                           dsc p a ((a + b) / 2) P @
                           dsc p ((a + b) / 2) b P).
           dsc_pair_ok P I"
        using H0
        by (simp add: Let_def)

      show
        "∀x. x ∈ set (if Bernstein_changes p a b P = 0 then []
                      else if Bernstein_changes p a b P = 1 then [(a, b)]
                           else (if poly P ((a + b) / 2) = 0
                                 then [((a + b) / 2, (a + b) / 2)]
                                 else []) @
                                dsc p a ((a + b) / 2) P @
                                dsc p ((a + b) / 2) b P) ⟶
             dsc_pair_ok P x"
        using H by blast
    qed
  qed
qed



thm dsc.psimps

lemma dsc_psimps_if_squarefree_real:
  fixes P :: "real poly"
  assumes P0: "P ≠ 0"
      and deg: "degree P ≤ p"
      and p0:  "p ≠ 0"
      and sf: "square_free P"
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
  have dom: "dsc_dom (p, a, b, P)"
    using dsc_terminates_squarefree_real ab P0 deg p0 sf by blast
  show ?thesis
    using dsc.psimps[OF dom]
    by simp
qed



lemma dsc_complete:
  assumes dom: "dsc_dom (p,a,b,P)"
      and deg: "degree P ≤ p"
      and P0:  "P ≠ 0"
  shows "⋀x. poly P x = 0 ⟹ a < x ⟹ x < b ⟹
             (∃I∈set (dsc p a b P). fst I ≤ x ∧ x ≤ snd I)"
using dom deg P0
proof (induction p a b P rule: dsc.pinduct)
  case (1 p a b P)
  have dsc_eq:
    "dsc p a b P =
       (let v = Bernstein_changes p a b P in
        if v = 0 then []
        else if v = 1 then [(a,b)]
        else
          (let m = (a + b) / 2 in
             (if poly P m = 0 then [(m,m)] else []) @
             dsc p a m P @
             dsc p m b P))"
    using "1.hyps" dsc.psimps by blast

  show ?case
  proof -
    from 1 have deg': "degree P ≤ p"
      by simp

    have H:
      "⋀x::real. poly P x = 0 ⟹ a < x ⟹ x < b ⟹
             (∃I∈set (dsc p a b P). fst I ≤ x ∧ x ≤ snd I)"
    proof -
      fix x :: real
      assume root: "poly P x = 0"
         and ax:   "a < x"
         and xb:   "x < b"

      have ab: "a < b"
        using ax xb by linarith
      have P0': "P ≠ 0"
        using P0 "1.prems"(5) by blast

      let ?v = "Bernstein_changes p a b P"

      have v_nonzero: "?v ≠ 0"
        using Bernstein_changes_pos_of_root[OF deg' P0' ab root ax xb] .

      have Ex0:
        "∃I∈set (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
                        (let m = (a + b) / 2 in
                           (if poly P m = 0 then [(m, m)] else []) @
                           dsc p a m P @ dsc p m b P)).
                 fst I ≤ x ∧ x ≤ snd I"
      proof (cases "?v = 1")
        case True
        hence v1: "?v = 1" by simp
        have cover: "fst (a,b) ≤ x ∧ x ≤ snd (a,b)"
          using ax xb by simp
        moreover have mem:
          "(a,b) ∈ set (if ?v = 0 then [] else if ?v = 1 then [(a,b)] else
                        (let m = (a + b) / 2 in
                           (if poly P m = 0 then [(m,m)] else []) @
                           dsc p a m P @ dsc p m b P))"
          using v1 v_nonzero by simp
        ultimately show ?thesis
          by blast
      next
        case v_ne1: False
        hence v_ge2: "?v ≥ 2"
          using v_nonzero
          by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)

        let ?m = "(a + b) / 2"
        have am: "a < ?m" and mb: "?m < b"
          using ab by simp_all

        have IH_left:
          "⋀x. poly P x = 0 ⟹ a < x ⟹ x < ?m ⟹
               (∃I∈set (dsc p a ?m P). fst I ≤ x ∧ x ≤ snd I)"
          using "1.IH"(1) deg' v_ne1 v_nonzero P0' by blast

        have IH_right:
          "⋀x. poly P x = 0 ⟹ ?m < x ⟹ x < b ⟹
               (∃I∈set (dsc p ?m b P). fst I ≤ x ∧ x ≤ snd I)"
          using "1.IH"(2) deg' v_ne1 v_nonzero P0' by blast

        show ?thesis
        proof (cases "x = ?m")
          case mid: True
          then have "poly P ?m = 0"
            using root by blast
          then have mem_root:
            "(?m,?m) ∈ set (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
                             (let m = (a + b) / 2 in
                                (if poly P m = 0 then [(m, m)] else []) @
                                dsc p a m P @
                                dsc p m b P))"
            using v_nonzero v_ne1 by (simp add: Let_def mid)
          moreover have cover_root:
            "fst (?m,?m) ≤ x ∧ x ≤ snd (?m,?m)"
            using mid by simp
          ultimately show ?thesis
            by blast
        next
          case mid_ne: False
          then have x_split: "x < ?m ∨ ?m < x"
            using ax xb by linarith

          show ?thesis
          proof (cases "x < ?m")
            case x_left: True
            then have ax': "a < x" and xm': "x < ?m"
              using ax by simp_all
            have ex_left:
              "∃I∈set (dsc p a ?m P). fst I ≤ x ∧ x ≤ snd I"
              using IH_left root ax' xm' by blast
            then obtain I where I_in: "I ∈ set (dsc p a ?m P)"
                             and I_cov: "fst I ≤ x ∧ x ≤ snd I"
              by blast
            have mem_top:
              "I ∈ set (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
                         (let m = (a + b) / 2 in
                            (if poly P m = 0 then [(m, m)] else []) @
                            dsc p a m P @ dsc p m b P))"
              using v_nonzero v_ne1 I_in
              by (simp add: Let_def)
            from mem_top I_cov show ?thesis
              by blast
          next
            case not_left: False
            with x_split have x_right: "?m < x" by simp
            have mx': "?m < x" using x_right .
            have ex_right:
              "∃I∈set (dsc p ?m b P). fst I ≤ x ∧ x ≤ snd I"
              using IH_right root mx' xb by blast
            then obtain I where I_in: "I ∈ set (dsc p ?m b P)"
                             and I_cov: "fst I ≤ x ∧ x ≤ snd I"
              by blast
            have mem_top:
              "I ∈ set (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
                         (let m = (a + b) / 2 in
                            (if poly P m = 0 then [(m, m)] else []) @
                            dsc p a m P @ dsc p m b P))"
              using v_nonzero v_ne1 I_in
              by (simp add: Let_def)
            from mem_top I_cov show ?thesis
              by blast
          qed
        qed
      qed

      have Ex:
        "∃I∈set (if Bernstein_changes p a b P = 0 then []
                 else if Bernstein_changes p a b P = 1 then [(a, b)]
                      else let m = (a + b) / 2
                           in (if poly P m = 0 then [(m, m)] else []) @
                              dsc p a m P @ dsc p m b P).
           fst I ≤ x ∧ x ≤ snd I"
        using Ex0 by simp

      have Ex_dsc:
        "∃I∈set (dsc p a b P). fst I ≤ x ∧ x ≤ snd I"
        using Ex
        by (simp add: dsc_eq Let_def)

      show "∃I∈set (dsc p a b P). fst I ≤ x ∧ x ≤ snd I"
        using Ex_dsc by simp
    qed

    show ?thesis
      using "1.prems"(1,2,3) H by blast

  qed
qed

lemma dsc_psimps_if:
  fixes P :: "real poly"
  assumes P0: "P ≠ 0"
      and deg: "degree P ≤ p"
      and p0:  "p ≠ 0"
      and sf: "square_free P"
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
  have dom: "dsc_dom (p, a, b, P)"
    using dsc_terminates_squarefree_real ab P0 deg p0 sf by blast
  show ?thesis
    using dsc.psimps[OF dom]
    using P0 ab by argo
qed

end
