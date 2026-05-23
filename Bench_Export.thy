theory Bench_Export
  imports Dsc_Int Sturm_Isolate HOL.Code_Numeral Dsc_Exec
begin

definition mk_nat :: "Code_Numeral.integer \<Rightarrow> nat" where
  "mk_nat = nat_of_integer"

definition mk_int :: "Code_Numeral.integer \<Rightarrow> int" where
  "mk_int = Code_Numeral.int_of_integer"

definition mk_rat :: "Code_Numeral.integer \<Rightarrow> Code_Numeral.integer \<Rightarrow> rat" where
  "mk_rat n d = Rat.Fract (mk_int n) (mk_int d)" 

definition mk_real :: "Code_Numeral.integer \<Rightarrow> real" where
  "mk_real k = of_int (mk_int k)"

definition poly_int :: "Code_Numeral.integer list \<Rightarrow> int poly" where
  "poly_int ks = poly_of_list (map mk_int ks)"

definition poly_real :: "Code_Numeral.integer list \<Rightarrow> real poly" where
  "poly_real ks = poly_of_list (map (of_int \<circ> mk_int) ks)"

definition poly_rat :: "Code_Numeral.integer list \<Rightarrow> rat poly" where
  "poly_rat ks = poly_of_list (map (\<lambda>k. Rat.Fract (Code_Numeral.int_of_integer k) 1) ks)"

export_code
  mk_int mk_nat mk_rat mk_real poly_int poly_real poly_rat
  degree dsc_int newdsc_int dsc_exec newdsc_exec isolate
in SML module_name Bench_Gen file "bench_gen.sml"

end


