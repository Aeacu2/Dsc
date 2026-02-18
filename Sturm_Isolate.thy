theory Sturm_Isolate
  imports Algebraic_Numbers.Real_Roots
begin

partial_function (tailrec) isolate_of_2_main ::
  "int poly \<Rightarrow> root_info \<Rightarrow> (rat \<Rightarrow> rat \<Rightarrow> nat) \<Rightarrow>
    (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list"
where
  [code]:
  "isolate_of_2_main p ri cr todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (l,r) # todo' \<Rightarrow>
          (let c = cr l r in
           if c = 0 then
             isolate_of_2_main p ri cr todo' acc
           else if c = 1 then
             isolate_of_2_main p ri cr todo' ((l,r) # acc)
           else
             (let m = (l + r) / 2
              in isolate_of_2_main p ri cr ((m,r) # (l,m) # todo') acc)))"

definition isolate :: "rat \<Rightarrow> rat \<Rightarrow> int poly \<Rightarrow>  (rat \<times> rat) list" where
  "isolate l r p =
        (let ri = root_info p;
             cr = root_info.l_r ri
         in isolate_of_2_main p ri cr [(l,r)] [])"

end
