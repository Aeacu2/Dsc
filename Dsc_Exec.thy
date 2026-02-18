theory Dsc_Exec
  imports Dsc
          Dsc_Bern
          NewDsc
          Algebraic_Numbers.Algebraic_Numbers_External_Code
begin

partial_function (tailrec) dsc_main_exec ::
  "real poly \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list"
where
  [code]:
  "dsc_main_exec P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b) # todo' \<Rightarrow>
          (let v = descartes_roots_test_sc a b P in
           if v = 0 then
             dsc_main_exec P todo' acc
           else if v = 1 then
             dsc_main_exec P todo' ((a,b) # acc)
           else
             (let m = (a + b) / 2;
                  acc' = (if poly P m = 0 then (m,m) # acc else acc)
              in dsc_main_exec P ((a,m) # (m,b) # todo') acc')))"

definition dsc_exec :: "real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "dsc_exec a b P = (dsc_main_exec P [(a,b)] [])"

lemma dsc_main_exec_sim:
  assumes dom:  "dsc_dom (p,a,b,P)"
      and pdeg: "p = degree P"
  shows
    "dsc_main_exec P ((a,b) # todo) acc =
     dsc_main_exec P todo (rev (dsc p a b P) @ acc)"
  using dom pdeg
proof (induction p a b P arbitrary: todo acc rule: dsc.pinduct)
  case (1 p a b P todo acc)
  let ?v = "Bernstein_changes p a b P"

  have v_eq: "descartes_roots_test_sc a b P = ?v"
    using "1.prems"
    by (simp add: descartes_roots_test_sc_eq_Bernstein_changes)

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have dsc0: "dsc p a b P = []"
      by (simp add: "1.hyps" dsc.psimps v0)
    show ?thesis
      using dsc0 dsc_main_exec.simps v0 v_eq by auto
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have dsc1: "dsc p a b P = [(a,b)]"
        by (simp add: "1.hyps" dsc.psimps v1)
      show ?thesis
        using dsc_main_exec.simps Let_def v0 v1 v_eq dsc1 by auto
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
        "dsc_main_exec P ((a,b) # todo) acc =
         dsc_main_exec P ((a,m) # (m,b) # todo) (?mid @ acc)"
      proof -
        have tmp:
          "dsc_main_exec P ((a,b) # todo) acc =
           dsc_main_exec P ((a,m) # (m,b) # todo)
             (if poly P m = 0 then (m,m) # acc else acc)"
          by (smt (verit) dsc_main_exec.simps int_ops(2) list.simps(5) m_def of_nat_eq_0_iff old.prod.case v0 v1
              v_eq)
        show ?thesis
          using tmp
          by (simp add: mid_acc_eq)
      qed

      have stepL:
        "dsc_main_exec P ((a,m) # (m,b) # todo) (?mid @ acc) =
         dsc_main_exec P ((m,b) # todo) (rev (dsc p a m P) @ (?mid @ acc))"
        using "1.IH"(1)[of ?v m "((m,b)#todo)" "?mid @ acc"]
        v0 v1 m_def v_eq "1.prems" by blast

      have stepR:
        "dsc_main_exec P ((m,b) # todo) (rev (dsc p a m P) @ (?mid @ acc)) =
         dsc_main_exec P todo
           (rev (dsc p m b P) @ (rev (dsc p a m P) @ (?mid @ acc)))"
        using "1.IH"(2)[of ?v m todo "rev (dsc p a m P) @ (?mid @ acc)"]
        v0 v1 m_def v_eq "1.prems" by blast

      have LHS_rewrite:
        "dsc_main_exec P ((a,b) # todo) acc =
         dsc_main_exec P todo
           (rev (dsc p m b P) @ rev (dsc p a m P) @ ?mid @ acc)"
        using main_split stepL stepR
        by simp

      have RHS_rewrite:
        "dsc_main_exec P todo (rev (dsc p a b P) @ acc) =
         dsc_main_exec P todo
           (rev (dsc p m b P) @ rev (dsc p a m P) @ ?mid @ acc)"
        using dsc_split
        by simp

      show ?thesis
        using LHS_rewrite RHS_rewrite
        by simp
    qed
  qed
qed

lemma dsc_exec_eq_dsc:
  assumes dom:  "dsc_dom (p,a,b,P)"
      and pdeg: "p = degree P"
  shows "rev (dsc_exec a b P) = dsc p a b P"
proof -
  have tr: "dsc_exec a b P = rev (dsc p a b P)"
    unfolding dsc_exec_def
    using dsc_main_exec_sim[OF dom pdeg, of "[]::(real\<times>real) list" "[]"]
    by (simp add: dsc_main_exec.simps)
  thus ?thesis by simp
qed


definition try_blocks_sc ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> int \<Rightarrow> (real \<times> real) option"
where
  "try_blocks_sc a b N P v =
     (let w = b - a;
          B1 = (a, a + w / of_nat N);
          B2 = (b - w / of_nat N, b);
          v1 = descartes_roots_test_sc (fst B1) (snd B1) P;
          v2 = descartes_roots_test_sc (fst B2) (snd B2) P
      in if v1 = v then Some B1 else if v2 = v then Some B2 else None)"

lemma try_block_sc_eq:
  assumes "p = degree P"
  shows "try_blocks_sc a b N P v = try_blocks p a b N P v"
  using assms descartes_roots_test_sc_eq_Bernstein_changes try_blocks_def
    try_blocks_sc_def by presburger

definition try_newton_sc ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> int \<Rightarrow> (real \<times> real) option"
where
  "try_newton_sc a b N P v =
     (let L1 = newton_at v P a; L2 = newton_at v P b in
      case L1 of
        Some lam1 \<Rightarrow>
          (let I1 = snap_window a b N lam1;
               v1 = descartes_roots_test_sc (fst I1) (snd I1) P
           in if v1 = v then Some I1
              else (case L2 of
                      Some lam2 \<Rightarrow>
                        (let I2 = snap_window a b N lam2;
                             v2 = descartes_roots_test_sc (fst I2) (snd I2) P
                         in if v2 = v then Some I2 else None)
                    | None \<Rightarrow> None))
      | None \<Rightarrow>
          (case L2 of
             Some lam2 \<Rightarrow>
               (let I2 = snap_window a b N lam2;
                    v2 = descartes_roots_test_sc (fst I2) (snd I2)  P
                in if v2 = v then Some I2 else None)
           | None \<Rightarrow> None))"

lemma try_newton_sc_eq:
  assumes "p = degree P"
  shows "try_newton_sc a b N P v = try_newton p a b N P v"
  using assms descartes_roots_test_sc_eq_Bernstein_changes try_newton_def try_newton_sc_def
  by presburger

partial_function (tailrec) newdsc_main_exec ::
  "real poly \<Rightarrow> (real \<times> real \<times> nat) list \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list"
where
  [code]:
  "newdsc_main_exec P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b,N) # todo' \<Rightarrow>
          (let v = descartes_roots_test_sc a b P in
           if v = 0 then
             newdsc_main_exec P todo' acc
           else if v = 1 then
             newdsc_main_exec P todo' ((a,b) # acc)
           else
             (case try_blocks_sc a b N P v of
                Some I \<Rightarrow>
                  newdsc_main_exec P ((fst I, snd I, Nq N) # todo') acc
              | None \<Rightarrow>
                  (case try_newton_sc a b N P v of
                     Some I \<Rightarrow>
                       newdsc_main_exec P ((fst I, snd I, Nq N) # todo') acc
                   | None \<Rightarrow>
                       (let m  = (a + b) / 2;
                            N' = Nlin N;
                            acc' = (if poly P m = 0 then (m,m) # acc else acc)
                        in newdsc_main_exec P ((a,m,N') # (m,b,N') # todo') acc')))))"

definition newdsc_exec ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "newdsc_exec a b N P = newdsc_main_exec P [(a,b,N)] []"

lemma newdsc_main_exec_sim:
  assumes dom:  "newdsc_dom (p,a,b,N,P)"
      and pdeg: "p = degree P"
  shows
    "newdsc_main_exec P ((a,b,N) # todo) acc =
     newdsc_main_exec P todo (rev (newdsc p a b N P) @ acc)"
  using dom pdeg
proof (induction p a b N P arbitrary: todo acc rule: newdsc.pinduct)
  case (1 p a b N P todo acc)
  let ?v = "Bernstein_changes p a b P"

  have deg_p: "degree P = p"
    using "1.prems" by (simp add: eq_commute)

  have v_eq: "descartes_roots_test_sc a b P = ?v"
    using deg_p by (simp add: descartes_roots_test_sc_eq_Bernstein_changes)

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have nd0: "newdsc p a b N P = []"
      by (simp add: "1.hyps" newdsc.psimps v0)
    show ?thesis
      using nd0 newdsc_main_exec.simps Let_def v0 v_eq by auto
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have nd1: "newdsc p a b N P = [(a,b)]"
        by (simp add: "1.hyps" newdsc.psimps v1)
      show ?thesis
        using nd1 newdsc_main_exec.simps Let_def v0 v1 v_eq by auto
    next
      case v1: False

      show ?thesis
      proof (cases "try_blocks p a b N P ?v")
        case (Some I)
        have nd_block:
          "newdsc p a b N P = newdsc p (fst I) (snd I) (Nq N) P"
          by (simp add: "1.hyps" newdsc.psimps v0 v1 Some)

        have main_block:
          "newdsc_main_exec P ((a,b,N) # todo) acc =
           newdsc_main_exec P ((fst I, snd I, Nq N) # todo) acc"
          using Some newdsc_main_exec.simps Let_def v0 v1 v_eq
                try_block_sc_eq "1.prems" 
          by simp

        have stepI:
          "newdsc_main_exec P ((fst I, snd I, Nq N) # todo) acc =
           newdsc_main_exec P todo (rev (newdsc p (fst I) (snd I) (Nq N) P) @ acc)"
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
            "newdsc_main_exec P ((a,b,N) # todo) acc =
             newdsc_main_exec P ((fst I, snd I, Nq N) # todo) acc"
            using TB0 Some newdsc_main_exec.simps Let_def v0 v1 v_eq
                  try_block_sc_eq try_newton_sc_eq deg_p 
            by force

          have stepI:
            "newdsc_main_exec P ((fst I, snd I, Nq N) # todo) acc =
             newdsc_main_exec P todo (rev (newdsc p (fst I) (snd I) (Nq N) P) @ acc)"
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
            "newdsc_main_exec P ((a,b,N) # todo) acc =
             newdsc_main_exec P ((a,m,N') # (m,b,N') # todo) (?mid @ acc)"
          proof -
            have tmp:
              "newdsc_main_exec P ((a,b,N) # todo) acc =
               newdsc_main_exec P ((a,m,N') # (m,b,N') # todo)
                 (if poly P m = 0 then (m,m) # acc else acc)"
              by (smt (verit) TB0 TN0 newdsc_main_exec.simps Let_def v0 v1 v_eq m_def N'_def
                    try_block_sc_eq try_newton_sc_eq deg_p list.case(2) option.case(1) prod.simps(2))
            show ?thesis
              using tmp by (simp add: mid_acc_eq)
          qed

          have stepL:
            "newdsc_main_exec P ((a,m,N') # (m,b,N') # todo) (?mid @ acc) =
             newdsc_main_exec P ((m,b,N') # todo)
               (rev (newdsc p a m N' P) @ (?mid @ acc))"
            using "1.IH"(1) v0 v1 TB0 TN0 m_def N'_def deg_p 
            by blast

          have stepR:
            "newdsc_main_exec P ((m,b,N') # todo)
               (rev (newdsc p a m N' P) @ (?mid @ acc)) =
             newdsc_main_exec P todo
               (rev (newdsc p m b N' P) @ (rev (newdsc p a m N' P) @ (?mid @ acc)))"
            using "1.IH"(2) v0 v1 TB0 TN0 m_def N'_def deg_p by blast

          have LHS_rewrite:
            "newdsc_main_exec P ((a,b,N) # todo) acc =
             newdsc_main_exec P todo
               (rev (newdsc p m b N' P) @ rev (newdsc p a m N' P) @ ?mid @ acc)"
            using main_split stepL stepR
            by simp

          have RHS_rewrite:
            "newdsc_main_exec P todo (rev (newdsc p a b N P) @ acc) =
             newdsc_main_exec P todo
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

lemma newdsc_exec_eq_newdsc:
  assumes dom:  "newdsc_dom (p,a,b,N,P)"
      and pdeg: "p = degree P"
  shows "rev (newdsc_exec a b N P) = newdsc p a b N P"
proof -
  have tr: "newdsc_exec a b N P = rev (newdsc p a b N P)"
    unfolding newdsc_exec_def
    using newdsc_main_exec_sim[OF dom pdeg, of "[]::(real\<times>real\<times>nat) list" "[]::(real\<times>real) list"]
    by (simp add: newdsc_main_exec.simps)
  show ?thesis
    using tr by simp
qed


end