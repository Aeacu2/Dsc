(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val shiftl : Word32.word -> IntInf.int -> Word32.word
  val shiftr : Word32.word -> IntInf.int -> Word32.word
  val shiftr_signed : Word32.word -> IntInf.int -> Word32.word
  val test_bit : Word32.word -> IntInf.int -> bool
end = struct

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)

(* Test that words can handle numbers between 0 and 63 *)
val _ = if 6 <= Word.wordSize then () else raise (Fail ("wordSize less than 6"));

structure Uint64 : sig
  eqtype uint64;
  val zero : uint64;
  val one : uint64;
  val fromInt : IntInf.int -> uint64;
  val toInt : uint64 -> IntInf.int;
  val toLarge : uint64 -> LargeWord.word;
  val fromLarge : LargeWord.word -> uint64
  val plus : uint64 -> uint64 -> uint64;
  val minus : uint64 -> uint64 -> uint64;
  val times : uint64 -> uint64 -> uint64;
  val divide : uint64 -> uint64 -> uint64;
  val modulus : uint64 -> uint64 -> uint64;
  val negate : uint64 -> uint64;
  val less_eq : uint64 -> uint64 -> bool;
  val less : uint64 -> uint64 -> bool;
  val notb : uint64 -> uint64;
  val andb : uint64 -> uint64 -> uint64;
  val orb : uint64 -> uint64 -> uint64;
  val xorb : uint64 -> uint64 -> uint64;
  val shiftl : uint64 -> IntInf.int -> uint64;
  val shiftr : uint64 -> IntInf.int -> uint64;
  val shiftr_signed : uint64 -> IntInf.int -> uint64;
  val test_bit : uint64 -> IntInf.int -> bool;
end = struct

type uint64 = IntInf.int;

val mask = 0xFFFFFFFFFFFFFFFF : IntInf.int;

val zero = 0 : IntInf.int;

val one = 1 : IntInf.int;

fun fromInt x = IntInf.andb(x, mask);

fun toInt x = x

fun toLarge x = LargeWord.fromLargeInt (IntInf.toLarge x);

fun fromLarge x = IntInf.fromLarge (LargeWord.toLargeInt x);

fun plus x y = IntInf.andb(IntInf.+(x, y), mask);

fun minus x y = IntInf.andb(IntInf.-(x, y), mask);

fun negate x = IntInf.andb(IntInf.~(x), mask);

fun times x y = IntInf.andb(IntInf.*(x, y), mask);

fun divide x y = IntInf.div(x, y);

fun modulus x y = IntInf.mod(x, y);

fun less_eq x y = IntInf.<=(x, y);

fun less x y = IntInf.<(x, y);

fun notb x = IntInf.andb(IntInf.notb(x), mask);

fun orb x y = IntInf.orb(x, y);

fun andb x y = IntInf.andb(x, y);

fun xorb x y = IntInf.xorb(x, y);

val maxWord = IntInf.pow (2, Word.wordSize);

fun shiftl x n = 
  if n < maxWord then IntInf.andb(IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n)), mask)
  else 0;

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else 0;

val msb_mask = 0x8000000000000000 : IntInf.int;

fun shiftr_signed x i =
  if IntInf.andb(x, msb_mask) = 0 then shiftr x i
  else if i >= 64 then 0xFFFFFFFFFFFFFFFF
  else let
    val x' = shiftr x i
    val m' = IntInf.andb(IntInf.<<(mask, Word.max(0w64 - Word.fromLargeInt (IntInf.toLarge i), 0w0)), mask)
  in IntInf.orb(x', m') end;

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else false;

end



structure Bit_Shifts : sig
  type int = IntInf.int
  val push : int -> int -> int
  val drop : int -> int -> int
  val word_max_index : Word.word (*only for validation*)
end = struct

open IntInf;

fun fold _ [] y = y
  | fold f (x :: xs) y = fold f xs (f x y);

fun replicate n x = (if n <= 0 then [] else x :: replicate (n - 1) x);

val max_index = pow (fromInt 2, Int.- (Word.wordSize, 3)) - fromInt 1; (*experimentally determined*)

val word_of_int = Word.fromLargeInt o toLarge;

val word_max_index = word_of_int max_index;

fun words_of_int k = case divMod (k, max_index)
  of (b, s) => word_of_int s :: (replicate b word_max_index);

fun push' i k = << (k, i);

fun drop' i k = ~>> (k, i);

(* The implementations are formally total, though indices >~ max_index will produce heavy computation load *)

fun push i = fold push' (words_of_int (abs i));

fun drop i = fold drop' (words_of_int (abs i));

end;

structure Bench_Gen : sig
  type int
  type 'a zero
  type nat
  type rat
  type 'a poly
  type real
  val degree : 'a zero -> 'a poly -> nat
  type root_info
  val dsc_exec : real -> real -> real poly -> (real * real) list
  val mk_int : IntInf.int -> int
  val mk_nat : IntInf.int -> nat
  val mk_rat : IntInf.int -> IntInf.int -> rat
  val mk_real : IntInf.int -> real
  val newdsc_exec : real -> real -> nat -> real poly -> (real * real) list
  val poly_int : IntInf.int list -> int poly
  val poly_rat : IntInf.int list -> rat poly
  val isolate : rat -> rat -> int poly -> (rat * rat) list
  val poly_real : IntInf.int list -> real poly
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun times_inta k l =
  Int_of_integer (IntInf.* (integer_of_int k, integer_of_int l));

val zero_inta : int = Int_of_integer (0 : IntInf.int);

datatype num = One | Bit0 of num | Bit1 of num;

val one_inta : int = Int_of_integer (1 : IntInf.int);

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k) then IntInf.divMod ( k, l )
                  else let
                         val (r, s) = IntInf.divMod ( (IntInf.~ k), l );
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod ( (IntInf.~ k), (IntInf.~ l) )
                           else let
                                  val (r, s) =
                                    IntInf.divMod ( k, (IntInf.~ l) );
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

fun gcd_integer k l =
  IntInf.abs
    (if ((l : IntInf.int) = (0 : IntInf.int)) then k
      else gcd_integer l (modulo_integer (IntInf.abs k) (IntInf.abs l)));

fun lcm_integer a b =
  divide_integer (IntInf.* (IntInf.abs a, IntInf.abs b)) (gcd_integer a b);

fun lcm_inta (Int_of_integer x) (Int_of_integer y) =
  Int_of_integer (lcm_integer x y);

fun gcd_intc (Int_of_integer x) (Int_of_integer y) =
  Int_of_integer (gcd_integer x y);

datatype color = R | B;

datatype ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;

datatype ordera = Eq | Lt | Gt;

type 'a ccompare = {ccompare : ('a -> 'a -> ordera) option};
val ccompare = #ccompare : 'a ccompare -> ('a -> 'a -> ordera) option;

datatype ('b, 'a) mapping_rbt = Mapping_RBT of ('b, 'a) rbt;

type 'a ceq = {ceq : ('a -> 'a -> bool) option};
val ceq = #ceq : 'a ceq -> ('a -> 'a -> bool) option;

datatype 'a set_dlist = Abs_dlist of 'a list;

datatype 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
  RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
  Complement of 'a set;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

type 'a gcda =
  {one_gcd : 'a one, zero_gcd : 'a zero, dvd_gcd : 'a dvd,
    gcda : 'a -> 'a -> 'a, lcma : 'a -> 'a -> 'a};
val one_gcd = #one_gcd : 'a gcda -> 'a one;
val zero_gcd = #zero_gcd : 'a gcda -> 'a zero;
val dvd_gcd = #dvd_gcd : 'a gcda -> 'a dvd;
val gcda = #gcda : 'a gcda -> 'a -> 'a -> 'a;
val lcma = #lcma : 'a gcda -> 'a -> 'a -> 'a;

type 'a gcd = {gcd_Gcd : 'a gcda, gcd : 'a set -> 'a, lcm : 'a set -> 'a};
val gcd_Gcd = #gcd_Gcd : 'a gcd -> 'a gcda;
val gcd = #gcd : 'a gcd -> 'a set -> 'a;
val lcm = #lcm : 'a gcd -> 'a set -> 'a;

fun dummy_Lcm A_ x = lcm A_ x;

fun dummy_Gcd _ = raise Fail "Code_Abort_Gcd.dummy_Gcd";

fun gcd_intb x = dummy_Gcd x;

val zero_int = {zero = zero_inta} : int zero;

val one_int = {one = one_inta} : int one;

val times_int = {times = times_inta} : int times;

val dvd_int = {times_dvd = times_int} : int dvd;

val gcd_inta =
  {one_gcd = one_int, zero_gcd = zero_int, dvd_gcd = dvd_int, gcda = gcd_intc,
    lcma = lcm_inta}
  : int gcda;

fun gcd_int () = {gcd_Gcd = gcd_inta, gcd = gcd_intb, lcm = lcm_int} : int gcd
and lcm_int x = dummy_Lcm (gcd_int ()) x;
val gcd_int = gcd_int ();

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

fun uminus_inta k = Int_of_integer (IntInf.~ (integer_of_int k));

fun minus_inta k l =
  Int_of_integer (IntInf.- (integer_of_int k, integer_of_int l));

fun plus_inta k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

type 'a uminus = {uminus : 'a -> 'a};
val uminus = #uminus : 'a uminus -> 'a -> 'a;

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add,
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add,
    minus_cancel_ab_semigroup_add : 'a minus};
val ab_semigroup_add_cancel_ab_semigroup_add =
  #ab_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add =
  #cancel_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;
val minus_cancel_ab_semigroup_add = #minus_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a minus;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add,
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add =
  #cancel_ab_semigroup_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add =
  #comm_monoid_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a comm_monoid_add;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add,
    semiring_0_semiring_0_cancel : 'a semiring_0};
val cancel_comm_monoid_add_semiring_0_cancel =
  #cancel_comm_monoid_add_semiring_0_cancel :
  'a semiring_0_cancel -> 'a cancel_comm_monoid_add;
val semiring_0_semiring_0_cancel = #semiring_0_semiring_0_cancel :
  'a semiring_0_cancel -> 'a semiring_0;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};
val semigroup_mult_ab_semigroup_mult = #semigroup_mult_ab_semigroup_mult :
  'a ab_semigroup_mult -> 'a semigroup_mult;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult,
    semiring_comm_semiring : 'a semiring};
val ab_semigroup_mult_comm_semiring = #ab_semigroup_mult_comm_semiring :
  'a comm_semiring -> 'a ab_semigroup_mult;
val semiring_comm_semiring = #semiring_comm_semiring :
  'a comm_semiring -> 'a semiring;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring,
    semiring_0_comm_semiring_0 : 'a semiring_0};
val comm_semiring_comm_semiring_0 = #comm_semiring_comm_semiring_0 :
  'a comm_semiring_0 -> 'a comm_semiring;
val semiring_0_comm_semiring_0 = #semiring_0_comm_semiring_0 :
  'a comm_semiring_0 -> 'a semiring_0;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0,
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};
val comm_semiring_0_comm_semiring_0_cancel =
  #comm_semiring_0_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a comm_semiring_0;
val semiring_0_cancel_comm_semiring_0_cancel =
  #semiring_0_cancel_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a semiring_0_cancel;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel,
    semiring_1_semiring_1_cancel : 'a semiring_1};
val semiring_0_cancel_semiring_1_cancel = #semiring_0_cancel_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_0_cancel;
val semiring_1_semiring_1_cancel = #semiring_1_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_1;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult,
    monoid_mult_comm_monoid_mult : 'a monoid_mult,
    dvd_comm_monoid_mult : 'a dvd};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a monoid_mult;
val dvd_comm_monoid_mult = #dvd_comm_monoid_mult :
  'a comm_monoid_mult -> 'a dvd;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult,
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0,
    semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_semiring_0;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 :
  'a comm_semiring_1 -> 'a semiring_1;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel,
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1,
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};
val comm_semiring_0_cancel_comm_semiring_1_cancel =
  #comm_semiring_0_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_0_cancel;
val comm_semiring_1_comm_semiring_1_cancel =
  #comm_semiring_1_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_1;
val semiring_1_cancel_comm_semiring_1_cancel =
  #semiring_1_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a semiring_1_cancel;

type 'a comm_semiring_1_cancel_crossproduct =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct :
     'a comm_semiring_1_cancel};
val comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
  #comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct :
  'a comm_semiring_1_cancel_crossproduct -> 'a comm_semiring_1_cancel;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};
val semiring_0_semiring_no_zero_divisors = #semiring_0_semiring_no_zero_divisors
  : 'a semiring_no_zero_divisors -> 'a semiring_0;

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};
val semiring_1_semiring_1_no_zero_divisors =
  #semiring_1_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_1;
val semiring_no_zero_divisors_semiring_1_no_zero_divisors =
  #semiring_no_zero_divisors_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_no_zero_divisors;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};
val semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
  #semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
  'a semiring_no_zero_divisors_cancel -> 'a semiring_no_zero_divisors;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add,
    minus_group_add : 'a minus, monoid_add_group_add : 'a monoid_add,
    uminus_group_add : 'a uminus};
val cancel_semigroup_add_group_add = #cancel_semigroup_add_group_add :
  'a group_add -> 'a cancel_semigroup_add;
val minus_group_add = #minus_group_add : 'a group_add -> 'a minus;
val monoid_add_group_add = #monoid_add_group_add :
  'a group_add -> 'a monoid_add;
val uminus_group_add = #uminus_group_add : 'a group_add -> 'a uminus;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add,
    group_add_ab_group_add : 'a group_add};
val cancel_comm_monoid_add_ab_group_add = #cancel_comm_monoid_add_ab_group_add :
  'a ab_group_add -> 'a cancel_comm_monoid_add;
val group_add_ab_group_add = #group_add_ab_group_add :
  'a ab_group_add -> 'a group_add;

type 'a ring =
  {ab_group_add_ring : 'a ab_group_add,
    semiring_0_cancel_ring : 'a semiring_0_cancel};
val ab_group_add_ring = #ab_group_add_ring : 'a ring -> 'a ab_group_add;
val semiring_0_cancel_ring = #semiring_0_cancel_ring :
  'a ring -> 'a semiring_0_cancel;

type 'a ring_no_zero_divisors =
  {ring_ring_no_zero_divisors : 'a ring,
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors :
      'a semiring_no_zero_divisors_cancel};
val ring_ring_no_zero_divisors = #ring_ring_no_zero_divisors :
  'a ring_no_zero_divisors -> 'a ring;
val semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
  #semiring_no_zero_divisors_cancel_ring_no_zero_divisors :
  'a ring_no_zero_divisors -> 'a semiring_no_zero_divisors_cancel;

type 'a neg_numeral =
  {group_add_neg_numeral : 'a group_add, numeral_neg_numeral : 'a numeral};
val group_add_neg_numeral = #group_add_neg_numeral :
  'a neg_numeral -> 'a group_add;
val numeral_neg_numeral = #numeral_neg_numeral : 'a neg_numeral -> 'a numeral;

type 'a ring_1 =
  {neg_numeral_ring_1 : 'a neg_numeral, ring_ring_1 : 'a ring,
    semiring_1_cancel_ring_1 : 'a semiring_1_cancel};
val neg_numeral_ring_1 = #neg_numeral_ring_1 : 'a ring_1 -> 'a neg_numeral;
val ring_ring_1 = #ring_ring_1 : 'a ring_1 -> 'a ring;
val semiring_1_cancel_ring_1 = #semiring_1_cancel_ring_1 :
  'a ring_1 -> 'a semiring_1_cancel;

type 'a ring_1_no_zero_divisors =
  {ring_1_ring_1_no_zero_divisors : 'a ring_1,
    ring_no_zero_divisors_ring_1_no_zero_divisors : 'a ring_no_zero_divisors,
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors :
      'a semiring_1_no_zero_divisors};
val ring_1_ring_1_no_zero_divisors = #ring_1_ring_1_no_zero_divisors :
  'a ring_1_no_zero_divisors -> 'a ring_1;
val ring_no_zero_divisors_ring_1_no_zero_divisors =
  #ring_no_zero_divisors_ring_1_no_zero_divisors :
  'a ring_1_no_zero_divisors -> 'a ring_no_zero_divisors;
val semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
  #semiring_1_no_zero_divisors_ring_1_no_zero_divisors :
  'a ring_1_no_zero_divisors -> 'a semiring_1_no_zero_divisors;

type 'a comm_ring =
  {comm_semiring_0_cancel_comm_ring : 'a comm_semiring_0_cancel,
    ring_comm_ring : 'a ring};
val comm_semiring_0_cancel_comm_ring = #comm_semiring_0_cancel_comm_ring :
  'a comm_ring -> 'a comm_semiring_0_cancel;
val ring_comm_ring = #ring_comm_ring : 'a comm_ring -> 'a ring;

type 'a comm_ring_1 =
  {comm_ring_comm_ring_1 : 'a comm_ring,
    comm_semiring_1_cancel_comm_ring_1 : 'a comm_semiring_1_cancel,
    ring_1_comm_ring_1 : 'a ring_1};
val comm_ring_comm_ring_1 = #comm_ring_comm_ring_1 :
  'a comm_ring_1 -> 'a comm_ring;
val comm_semiring_1_cancel_comm_ring_1 = #comm_semiring_1_cancel_comm_ring_1 :
  'a comm_ring_1 -> 'a comm_semiring_1_cancel;
val ring_1_comm_ring_1 = #ring_1_comm_ring_1 : 'a comm_ring_1 -> 'a ring_1;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel,
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};
val comm_semiring_1_cancel_semidom = #comm_semiring_1_cancel_semidom :
  'a semidom -> 'a comm_semiring_1_cancel;
val semiring_1_no_zero_divisors_semidom = #semiring_1_no_zero_divisors_semidom :
  'a semidom -> 'a semiring_1_no_zero_divisors;

type 'a idom =
  {comm_ring_1_idom : 'a comm_ring_1,
    ring_1_no_zero_divisors_idom : 'a ring_1_no_zero_divisors,
    semidom_idom : 'a semidom,
    comm_semiring_1_cancel_crossproduct_idom :
      'a comm_semiring_1_cancel_crossproduct};
val comm_ring_1_idom = #comm_ring_1_idom : 'a idom -> 'a comm_ring_1;
val ring_1_no_zero_divisors_idom = #ring_1_no_zero_divisors_idom :
  'a idom -> 'a ring_1_no_zero_divisors;
val semidom_idom = #semidom_idom : 'a idom -> 'a semidom;
val comm_semiring_1_cancel_crossproduct_idom =
  #comm_semiring_1_cancel_crossproduct_idom :
  'a idom -> 'a comm_semiring_1_cancel_crossproduct;

val plus_int = {plus = plus_inta} : int plus;

val semigroup_add_int = {plus_semigroup_add = plus_int} : int semigroup_add;

val cancel_semigroup_add_int =
  {semigroup_add_cancel_semigroup_add = semigroup_add_int} :
  int cancel_semigroup_add;

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int}
  : int ab_semigroup_add;

val minus_int = {minus = minus_inta} : int minus;

val cancel_ab_semigroup_add_int =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int,
    minus_cancel_ab_semigroup_add = minus_int}
  : int cancel_ab_semigroup_add;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  int monoid_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : int comm_monoid_add;

val cancel_comm_monoid_add_int =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_int,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
  : int cancel_comm_monoid_add;

val mult_zero_int = {times_mult_zero = times_int, zero_mult_zero = zero_int} :
  int mult_zero;

val semigroup_mult_int = {times_semigroup_mult = times_int} :
  int semigroup_mult;

val semiring_int =
  {ab_semigroup_add_semiring = ab_semigroup_add_int,
    semigroup_mult_semiring = semigroup_mult_int}
  : int semiring;

val semiring_0_int =
  {comm_monoid_add_semiring_0 = comm_monoid_add_int,
    mult_zero_semiring_0 = mult_zero_int, semiring_semiring_0 = semiring_int}
  : int semiring_0;

val semiring_0_cancel_int =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int,
    semiring_0_semiring_0_cancel = semiring_0_int}
  : int semiring_0_cancel;

val ab_semigroup_mult_int =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
  int ab_semigroup_mult;

val comm_semiring_int =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int,
    semiring_comm_semiring = semiring_int}
  : int comm_semiring;

val comm_semiring_0_int =
  {comm_semiring_comm_semiring_0 = comm_semiring_int,
    semiring_0_comm_semiring_0 = semiring_0_int}
  : int comm_semiring_0;

val comm_semiring_0_cancel_int =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int}
  : int comm_semiring_0_cancel;

val power_int = {one_power = one_int, times_power = times_int} : int power;

val monoid_mult_int =
  {semigroup_mult_monoid_mult = semigroup_mult_int,
    power_monoid_mult = power_int}
  : int monoid_mult;

val numeral_int =
  {one_numeral = one_int, semigroup_add_numeral = semigroup_add_int} :
  int numeral;

val semiring_numeral_int =
  {monoid_mult_semiring_numeral = monoid_mult_int,
    numeral_semiring_numeral = numeral_int,
    semiring_semiring_numeral = semiring_int}
  : int semiring_numeral;

val zero_neq_one_int =
  {one_zero_neq_one = one_int, zero_zero_neq_one = zero_int} : int zero_neq_one;

val semiring_1_int =
  {semiring_numeral_semiring_1 = semiring_numeral_int,
    semiring_0_semiring_1 = semiring_0_int,
    zero_neq_one_semiring_1 = zero_neq_one_int}
  : int semiring_1;

val semiring_1_cancel_int =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int,
    semiring_1_semiring_1_cancel = semiring_1_int}
  : int semiring_1_cancel;

val comm_monoid_mult_int =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int,
    monoid_mult_comm_monoid_mult = monoid_mult_int,
    dvd_comm_monoid_mult = dvd_int}
  : int comm_monoid_mult;

val comm_semiring_1_int =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_int,
    semiring_1_comm_semiring_1 = semiring_1_int}
  : int comm_semiring_1;

val comm_semiring_1_cancel_int =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int}
  : int comm_semiring_1_cancel;

val comm_semiring_1_cancel_crossproduct_int =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
     comm_semiring_1_cancel_int}
  : int comm_semiring_1_cancel_crossproduct;

val semiring_no_zero_divisors_int =
  {semiring_0_semiring_no_zero_divisors = semiring_0_int} :
  int semiring_no_zero_divisors;

val semiring_1_no_zero_divisors_int =
  {semiring_1_semiring_1_no_zero_divisors = semiring_1_int,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_int}
  : int semiring_1_no_zero_divisors;

val semiring_no_zero_divisors_cancel_int =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_int}
  : int semiring_no_zero_divisors_cancel;

val uminus_int = {uminus = uminus_inta} : int uminus;

val group_add_int =
  {cancel_semigroup_add_group_add = cancel_semigroup_add_int,
    minus_group_add = minus_int, monoid_add_group_add = monoid_add_int,
    uminus_group_add = uminus_int}
  : int group_add;

val ab_group_add_int =
  {cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int,
    group_add_ab_group_add = group_add_int}
  : int ab_group_add;

val ring_int =
  {ab_group_add_ring = ab_group_add_int,
    semiring_0_cancel_ring = semiring_0_cancel_int}
  : int ring;

val ring_no_zero_divisors_int =
  {ring_ring_no_zero_divisors = ring_int,
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
      semiring_no_zero_divisors_cancel_int}
  : int ring_no_zero_divisors;

val neg_numeral_int =
  {group_add_neg_numeral = group_add_int, numeral_neg_numeral = numeral_int} :
  int neg_numeral;

val ring_1_int =
  {neg_numeral_ring_1 = neg_numeral_int, ring_ring_1 = ring_int,
    semiring_1_cancel_ring_1 = semiring_1_cancel_int}
  : int ring_1;

val ring_1_no_zero_divisors_int =
  {ring_1_ring_1_no_zero_divisors = ring_1_int,
    ring_no_zero_divisors_ring_1_no_zero_divisors = ring_no_zero_divisors_int,
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
      semiring_1_no_zero_divisors_int}
  : int ring_1_no_zero_divisors;

val comm_ring_int =
  {comm_semiring_0_cancel_comm_ring = comm_semiring_0_cancel_int,
    ring_comm_ring = ring_int}
  : int comm_ring;

val comm_ring_1_int =
  {comm_ring_comm_ring_1 = comm_ring_int,
    comm_semiring_1_cancel_comm_ring_1 = comm_semiring_1_cancel_int,
    ring_1_comm_ring_1 = ring_1_int}
  : int comm_ring_1;

val semidom_int =
  {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_int,
    semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_int}
  : int semidom;

val idom_int =
  {comm_ring_1_idom = comm_ring_1_int,
    ring_1_no_zero_divisors_idom = ring_1_no_zero_divisors_int,
    semidom_idom = semidom_int,
    comm_semiring_1_cancel_crossproduct_idom =
      comm_semiring_1_cancel_crossproduct_int}
  : int idom;

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun abs_int i = (if less_int i zero_inta then uminus_inta i else i);

fun normalize_int x = abs_int x;

fun sgn_int i =
  (if equal_inta i zero_inta then zero_inta
    else (if less_int zero_inta i then one_inta else uminus_inta one_inta));

fun unit_factor_inta x = sgn_int x;

type 'a divide = {divide : 'a -> 'a -> 'a};
val divide = #divide : 'a divide -> 'a -> 'a -> 'a;

type 'a divide_trivial =
  {one_divide_trivial : 'a one, zero_divide_trivial : 'a zero,
    divide_divide_trivial : 'a divide};
val one_divide_trivial = #one_divide_trivial : 'a divide_trivial -> 'a one;
val zero_divide_trivial = #zero_divide_trivial : 'a divide_trivial -> 'a zero;
val divide_divide_trivial = #divide_divide_trivial :
  'a divide_trivial -> 'a divide;

type 'a semidom_divide =
  {divide_trivial_semidom_divide : 'a divide_trivial,
    semidom_semidom_divide : 'a semidom,
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};
val divide_trivial_semidom_divide = #divide_trivial_semidom_divide :
  'a semidom_divide -> 'a divide_trivial;
val semidom_semidom_divide = #semidom_semidom_divide :
  'a semidom_divide -> 'a semidom;
val semiring_no_zero_divisors_cancel_semidom_divide =
  #semiring_no_zero_divisors_cancel_semidom_divide :
  'a semidom_divide -> 'a semiring_no_zero_divisors_cancel;

type 'a unit_factor = {unit_factor : 'a -> 'a};
val unit_factor = #unit_factor : 'a unit_factor -> 'a -> 'a;

type 'a semidom_divide_unit_factor =
  {semidom_divide_semidom_divide_unit_factor : 'a semidom_divide,
    unit_factor_semidom_divide_unit_factor : 'a unit_factor};
val semidom_divide_semidom_divide_unit_factor =
  #semidom_divide_semidom_divide_unit_factor :
  'a semidom_divide_unit_factor -> 'a semidom_divide;
val unit_factor_semidom_divide_unit_factor =
  #unit_factor_semidom_divide_unit_factor :
  'a semidom_divide_unit_factor -> 'a unit_factor;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};
val semidom_divide_algebraic_semidom = #semidom_divide_algebraic_semidom :
  'a algebraic_semidom -> 'a semidom_divide;

type 'a normalization_semidom =
  {algebraic_semidom_normalization_semidom : 'a algebraic_semidom,
    semidom_divide_unit_factor_normalization_semidom :
      'a semidom_divide_unit_factor,
    normalizea : 'a -> 'a};
val algebraic_semidom_normalization_semidom =
  #algebraic_semidom_normalization_semidom :
  'a normalization_semidom -> 'a algebraic_semidom;
val semidom_divide_unit_factor_normalization_semidom =
  #semidom_divide_unit_factor_normalization_semidom :
  'a normalization_semidom -> 'a semidom_divide_unit_factor;
val normalizea = #normalizea : 'a normalization_semidom -> 'a -> 'a;

fun divide_inta k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

type 'a comm_monoid_gcd =
  {gcd_comm_monoid_gcd : 'a gcda,
    comm_semiring_1_comm_monoid_gcd : 'a comm_semiring_1};
val gcd_comm_monoid_gcd = #gcd_comm_monoid_gcd : 'a comm_monoid_gcd -> 'a gcda;
val comm_semiring_1_comm_monoid_gcd = #comm_semiring_1_comm_monoid_gcd :
  'a comm_monoid_gcd -> 'a comm_semiring_1;

type 'a idom_gcd =
  {idom_idom_gcd : 'a idom, comm_monoid_gcd_idom_gcd : 'a comm_monoid_gcd};
val idom_idom_gcd = #idom_idom_gcd : 'a idom_gcd -> 'a idom;
val comm_monoid_gcd_idom_gcd = #comm_monoid_gcd_idom_gcd :
  'a idom_gcd -> 'a comm_monoid_gcd;

type 'a semiring_gcd =
  {normalization_semidom_semiring_gcd : 'a normalization_semidom,
    comm_monoid_gcd_semiring_gcd : 'a comm_monoid_gcd};
val normalization_semidom_semiring_gcd = #normalization_semidom_semiring_gcd :
  'a semiring_gcd -> 'a normalization_semidom;
val comm_monoid_gcd_semiring_gcd = #comm_monoid_gcd_semiring_gcd :
  'a semiring_gcd -> 'a comm_monoid_gcd;

type 'a ring_gcd =
  {semiring_gcd_ring_gcd : 'a semiring_gcd, idom_gcd_ring_gcd : 'a idom_gcd};
val semiring_gcd_ring_gcd = #semiring_gcd_ring_gcd :
  'a ring_gcd -> 'a semiring_gcd;
val idom_gcd_ring_gcd = #idom_gcd_ring_gcd : 'a ring_gcd -> 'a idom_gcd;

val comm_monoid_gcd_int =
  {gcd_comm_monoid_gcd = gcd_inta,
    comm_semiring_1_comm_monoid_gcd = comm_semiring_1_int}
  : int comm_monoid_gcd;

val idom_gcd_int =
  {idom_idom_gcd = idom_int, comm_monoid_gcd_idom_gcd = comm_monoid_gcd_int} :
  int idom_gcd;

val divide_int = {divide = divide_inta} : int divide;

val divide_trivial_int =
  {one_divide_trivial = one_int, zero_divide_trivial = zero_int,
    divide_divide_trivial = divide_int}
  : int divide_trivial;

val semidom_divide_int =
  {divide_trivial_semidom_divide = divide_trivial_int,
    semidom_semidom_divide = semidom_int,
    semiring_no_zero_divisors_cancel_semidom_divide =
      semiring_no_zero_divisors_cancel_int}
  : int semidom_divide;

val unit_factor_int = {unit_factor = unit_factor_inta} : int unit_factor;

val semidom_divide_unit_factor_int =
  {semidom_divide_semidom_divide_unit_factor = semidom_divide_int,
    unit_factor_semidom_divide_unit_factor = unit_factor_int}
  : int semidom_divide_unit_factor;

val algebraic_semidom_int =
  {semidom_divide_algebraic_semidom = semidom_divide_int} :
  int algebraic_semidom;

val normalization_semidom_int =
  {algebraic_semidom_normalization_semidom = algebraic_semidom_int,
    semidom_divide_unit_factor_normalization_semidom =
      semidom_divide_unit_factor_int,
    normalizea = normalize_int}
  : int normalization_semidom;

val semiring_gcd_int =
  {normalization_semidom_semiring_gcd = normalization_semidom_int,
    comm_monoid_gcd_semiring_gcd = comm_monoid_gcd_int}
  : int semiring_gcd;

val ring_gcd_int =
  {semiring_gcd_ring_gcd = semiring_gcd_int, idom_gcd_ring_gcd = idom_gcd_int} :
  int ring_gcd;

fun modulo_inta k l =
  Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));

type 'a modulo =
  {divide_modulo : 'a divide, dvd_modulo : 'a dvd, modulo : 'a -> 'a -> 'a};
val divide_modulo = #divide_modulo : 'a modulo -> 'a divide;
val dvd_modulo = #dvd_modulo : 'a modulo -> 'a dvd;
val modulo = #modulo : 'a modulo -> 'a -> 'a -> 'a;

val modulo_int =
  {divide_modulo = divide_int, dvd_modulo = dvd_int, modulo = modulo_inta} :
  int modulo;

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_int = {less_eq = less_eq_int, less = less_int} : int ord;

type 'a semiring_Gcd =
  {gcd_semiring_Gcd : 'a gcd, semiring_gcd_semiring_Gcd : 'a semiring_gcd};
val gcd_semiring_Gcd = #gcd_semiring_Gcd : 'a semiring_Gcd -> 'a gcd;
val semiring_gcd_semiring_Gcd = #semiring_gcd_semiring_Gcd :
  'a semiring_Gcd -> 'a semiring_gcd;

val semiring_Gcd_int =
  {gcd_semiring_Gcd = gcd_int, semiring_gcd_semiring_Gcd = semiring_gcd_int} :
  int semiring_Gcd;

type 'a idom_divide =
  {idom_idom_divide : 'a idom, semidom_divide_idom_divide : 'a semidom_divide};
val idom_idom_divide = #idom_idom_divide : 'a idom_divide -> 'a idom;
val semidom_divide_idom_divide = #semidom_divide_idom_divide :
  'a idom_divide -> 'a semidom_divide;

val idom_divide_int =
  {idom_idom_divide = idom_int, semidom_divide_idom_divide = semidom_divide_int}
  : int idom_divide;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel,
    modulo_semiring_modulo : 'a modulo};
val comm_semiring_1_cancel_semiring_modulo =
  #comm_semiring_1_cancel_semiring_modulo :
  'a semiring_modulo -> 'a comm_semiring_1_cancel;
val modulo_semiring_modulo = #modulo_semiring_modulo :
  'a semiring_modulo -> 'a modulo;

type 'a semiring_modulo_trivial =
  {divide_trivial_semiring_modulo_trivial : 'a divide_trivial,
    semiring_modulo_semiring_modulo_trivial : 'a semiring_modulo};
val divide_trivial_semiring_modulo_trivial =
  #divide_trivial_semiring_modulo_trivial :
  'a semiring_modulo_trivial -> 'a divide_trivial;
val semiring_modulo_semiring_modulo_trivial =
  #semiring_modulo_semiring_modulo_trivial :
  'a semiring_modulo_trivial -> 'a semiring_modulo;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom,
    semiring_modulo_trivial_semidom_modulo : 'a semiring_modulo_trivial};
val algebraic_semidom_semidom_modulo = #algebraic_semidom_semidom_modulo :
  'a semidom_modulo -> 'a algebraic_semidom;
val semiring_modulo_trivial_semidom_modulo =
  #semiring_modulo_trivial_semidom_modulo :
  'a semidom_modulo -> 'a semiring_modulo_trivial;

type 'a idom_modulo =
  {idom_divide_idom_modulo : 'a idom_divide,
    semidom_modulo_idom_modulo : 'a semidom_modulo};
val idom_divide_idom_modulo = #idom_divide_idom_modulo :
  'a idom_modulo -> 'a idom_divide;
val semidom_modulo_idom_modulo = #semidom_modulo_idom_modulo :
  'a idom_modulo -> 'a semidom_modulo;

val semiring_modulo_int =
  {comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_int,
    modulo_semiring_modulo = modulo_int}
  : int semiring_modulo;

val semiring_modulo_trivial_int =
  {divide_trivial_semiring_modulo_trivial = divide_trivial_int,
    semiring_modulo_semiring_modulo_trivial = semiring_modulo_int}
  : int semiring_modulo_trivial;

val semidom_modulo_int =
  {algebraic_semidom_semidom_modulo = algebraic_semidom_int,
    semiring_modulo_trivial_semidom_modulo = semiring_modulo_trivial_int}
  : int semidom_modulo;

val idom_modulo_int =
  {idom_divide_idom_modulo = idom_divide_int,
    semidom_modulo_idom_modulo = semidom_modulo_int}
  : int idom_modulo;

fun max A_ a b = (if less_eq A_ a b then b else a);

datatype nat = Nat of IntInf.int;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun nat x = (nat_of_integer o integer_of_int) x;

fun euclidean_size_int x = (nat o abs_int) x;

type 'a euclidean_semiring =
  {semidom_modulo_euclidean_semiring : 'a semidom_modulo,
    euclidean_size : 'a -> nat};
val semidom_modulo_euclidean_semiring = #semidom_modulo_euclidean_semiring :
  'a euclidean_semiring -> 'a semidom_modulo;
val euclidean_size = #euclidean_size : 'a euclidean_semiring -> 'a -> nat;

type 'a euclidean_ring =
  {euclidean_semiring_euclidean_ring : 'a euclidean_semiring,
    idom_modulo_euclidean_ring : 'a idom_modulo};
val euclidean_semiring_euclidean_ring = #euclidean_semiring_euclidean_ring :
  'a euclidean_ring -> 'a euclidean_semiring;
val idom_modulo_euclidean_ring = #idom_modulo_euclidean_ring :
  'a euclidean_ring -> 'a idom_modulo;

val euclidean_semiring_int =
  {semidom_modulo_euclidean_semiring = semidom_modulo_int,
    euclidean_size = euclidean_size_int}
  : int euclidean_semiring;

val euclidean_ring_int =
  {euclidean_semiring_euclidean_ring = euclidean_semiring_int,
    idom_modulo_euclidean_ring = idom_modulo_int}
  : int euclidean_ring;

type 'a normalization_semidom_multiplicative =
  {normalization_semidom_normalization_semidom_multiplicative :
     'a normalization_semidom};
val normalization_semidom_normalization_semidom_multiplicative =
  #normalization_semidom_normalization_semidom_multiplicative :
  'a normalization_semidom_multiplicative -> 'a normalization_semidom;

type 'a semiring_gcd_mult_normalize =
  {semiring_gcd_semiring_gcd_mult_normalize : 'a semiring_gcd,
    normalization_semidom_multiplicative_semiring_gcd_mult_normalize :
      'a normalization_semidom_multiplicative};
val semiring_gcd_semiring_gcd_mult_normalize =
  #semiring_gcd_semiring_gcd_mult_normalize :
  'a semiring_gcd_mult_normalize -> 'a semiring_gcd;
val normalization_semidom_multiplicative_semiring_gcd_mult_normalize =
  #normalization_semidom_multiplicative_semiring_gcd_mult_normalize :
  'a semiring_gcd_mult_normalize -> 'a normalization_semidom_multiplicative;

val normalization_semidom_multiplicative_int =
  {normalization_semidom_normalization_semidom_multiplicative =
     normalization_semidom_int}
  : int normalization_semidom_multiplicative;

val semiring_gcd_mult_normalize_int =
  {semiring_gcd_semiring_gcd_mult_normalize = semiring_gcd_int,
    normalization_semidom_multiplicative_semiring_gcd_mult_normalize =
      normalization_semidom_multiplicative_int}
  : int semiring_gcd_mult_normalize;

type 'a factorial_semiring =
  {normalization_semidom_factorial_semiring : 'a normalization_semidom};
val normalization_semidom_factorial_semiring =
  #normalization_semidom_factorial_semiring :
  'a factorial_semiring -> 'a normalization_semidom;

type 'a factorial_semiring_gcd =
  {factorial_semiring_factorial_semiring_gcd : 'a factorial_semiring,
    semiring_Gcd_factorial_semiring_gcd : 'a semiring_Gcd};
val factorial_semiring_factorial_semiring_gcd =
  #factorial_semiring_factorial_semiring_gcd :
  'a factorial_semiring_gcd -> 'a factorial_semiring;
val semiring_Gcd_factorial_semiring_gcd = #semiring_Gcd_factorial_semiring_gcd :
  'a factorial_semiring_gcd -> 'a semiring_Gcd;

type 'a factorial_ring_gcd =
  {factorial_semiring_gcd_factorial_ring_gcd : 'a factorial_semiring_gcd,
    ring_gcd_factorial_ring_gcd : 'a ring_gcd,
    idom_divide_factorial_ring_gcd : 'a idom_divide};
val factorial_semiring_gcd_factorial_ring_gcd =
  #factorial_semiring_gcd_factorial_ring_gcd :
  'a factorial_ring_gcd -> 'a factorial_semiring_gcd;
val ring_gcd_factorial_ring_gcd = #ring_gcd_factorial_ring_gcd :
  'a factorial_ring_gcd -> 'a ring_gcd;
val idom_divide_factorial_ring_gcd = #idom_divide_factorial_ring_gcd :
  'a factorial_ring_gcd -> 'a idom_divide;

val factorial_semiring_int =
  {normalization_semidom_factorial_semiring = normalization_semidom_int} :
  int factorial_semiring;

val factorial_semiring_gcd_int =
  {factorial_semiring_factorial_semiring_gcd = factorial_semiring_int,
    semiring_Gcd_factorial_semiring_gcd = semiring_Gcd_int}
  : int factorial_semiring_gcd;

val factorial_ring_gcd_int =
  {factorial_semiring_gcd_factorial_ring_gcd = factorial_semiring_gcd_int,
    ring_gcd_factorial_ring_gcd = ring_gcd_int,
    idom_divide_factorial_ring_gcd = idom_divide_int}
  : int factorial_ring_gcd;

type 'a normalization_euclidean_semiring =
  {euclidean_semiring_normalization_euclidean_semiring : 'a euclidean_semiring,
    factorial_semiring_normalization_euclidean_semiring :
      'a factorial_semiring};
val euclidean_semiring_normalization_euclidean_semiring =
  #euclidean_semiring_normalization_euclidean_semiring :
  'a normalization_euclidean_semiring -> 'a euclidean_semiring;
val factorial_semiring_normalization_euclidean_semiring =
  #factorial_semiring_normalization_euclidean_semiring :
  'a normalization_euclidean_semiring -> 'a factorial_semiring;

type 'a euclidean_semiring_gcd =
  {normalization_euclidean_semiring_euclidean_semiring_gcd :
     'a normalization_euclidean_semiring,
    factorial_semiring_gcd_euclidean_semiring_gcd : 'a factorial_semiring_gcd};
val normalization_euclidean_semiring_euclidean_semiring_gcd =
  #normalization_euclidean_semiring_euclidean_semiring_gcd :
  'a euclidean_semiring_gcd -> 'a normalization_euclidean_semiring;
val factorial_semiring_gcd_euclidean_semiring_gcd =
  #factorial_semiring_gcd_euclidean_semiring_gcd :
  'a euclidean_semiring_gcd -> 'a factorial_semiring_gcd;

type 'a euclidean_ring_gcd =
  {euclidean_semiring_gcd_euclidean_ring_gcd : 'a euclidean_semiring_gcd,
    euclidean_ring_euclidean_ring_gcd : 'a euclidean_ring,
    factorial_ring_gcd_euclidean_ring_gcd : 'a factorial_ring_gcd};
val euclidean_semiring_gcd_euclidean_ring_gcd =
  #euclidean_semiring_gcd_euclidean_ring_gcd :
  'a euclidean_ring_gcd -> 'a euclidean_semiring_gcd;
val euclidean_ring_euclidean_ring_gcd = #euclidean_ring_euclidean_ring_gcd :
  'a euclidean_ring_gcd -> 'a euclidean_ring;
val factorial_ring_gcd_euclidean_ring_gcd =
  #factorial_ring_gcd_euclidean_ring_gcd :
  'a euclidean_ring_gcd -> 'a factorial_ring_gcd;

val normalization_euclidean_semiring_int =
  {euclidean_semiring_normalization_euclidean_semiring = euclidean_semiring_int,
    factorial_semiring_normalization_euclidean_semiring =
      factorial_semiring_int}
  : int normalization_euclidean_semiring;

val euclidean_semiring_gcd_int =
  {normalization_euclidean_semiring_euclidean_semiring_gcd =
     normalization_euclidean_semiring_int,
    factorial_semiring_gcd_euclidean_semiring_gcd = factorial_semiring_gcd_int}
  : int euclidean_semiring_gcd;

val euclidean_ring_gcd_int =
  {euclidean_semiring_gcd_euclidean_ring_gcd = euclidean_semiring_gcd_int,
    euclidean_ring_euclidean_ring_gcd = euclidean_ring_int,
    factorial_ring_gcd_euclidean_ring_gcd = factorial_ring_gcd_int}
  : int euclidean_ring_gcd;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat equal;

fun times_nata m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

val times_nat = {times = times_nata} : nat times;

val dvd_nat = {times_dvd = times_nat} : nat dvd;

val one_nata : nat = Nat (1 : IntInf.int);

val one_nat = {one = one_nata} : nat one;

fun plus_nata m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nata : nat = Nat (0 : IntInf.int);

val zero_nat = {zero = zero_nata} : nat zero;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

fun minus_nata m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

val minus_nat = {minus = minus_nata} : nat minus;

fun divide_nata m n =
  Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

val divide_nat = {divide = divide_nata} : nat divide;

fun modulo_nata m n =
  Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

val modulo_nat =
  {divide_modulo = divide_nat, dvd_modulo = dvd_nat, modulo = modulo_nata} :
  nat modulo;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

val ab_semigroup_add_nat = {semigroup_add_ab_semigroup_add = semigroup_add_nat}
  : nat ab_semigroup_add;

val monoid_add_nat =
  {semigroup_add_monoid_add = semigroup_add_nat, zero_monoid_add = zero_nat} :
  nat monoid_add;

val comm_monoid_add_nat =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat,
    monoid_add_comm_monoid_add = monoid_add_nat}
  : nat comm_monoid_add;

val mult_zero_nat = {times_mult_zero = times_nat, zero_mult_zero = zero_nat} :
  nat mult_zero;

val semigroup_mult_nat = {times_semigroup_mult = times_nat} :
  nat semigroup_mult;

val semiring_nat =
  {ab_semigroup_add_semiring = ab_semigroup_add_nat,
    semigroup_mult_semiring = semigroup_mult_nat}
  : nat semiring;

val semiring_0_nat =
  {comm_monoid_add_semiring_0 = comm_monoid_add_nat,
    mult_zero_semiring_0 = mult_zero_nat, semiring_semiring_0 = semiring_nat}
  : nat semiring_0;

val semiring_no_zero_divisors_nat =
  {semiring_0_semiring_no_zero_divisors = semiring_0_nat} :
  nat semiring_no_zero_divisors;

val monoid_mult_nat =
  {semigroup_mult_monoid_mult = semigroup_mult_nat,
    power_monoid_mult = power_nat}
  : nat monoid_mult;

val semiring_numeral_nat =
  {monoid_mult_semiring_numeral = monoid_mult_nat,
    numeral_semiring_numeral = numeral_nat,
    semiring_semiring_numeral = semiring_nat}
  : nat semiring_numeral;

val zero_neq_one_nat =
  {one_zero_neq_one = one_nat, zero_zero_neq_one = zero_nat} : nat zero_neq_one;

val semiring_1_nat =
  {semiring_numeral_semiring_1 = semiring_numeral_nat,
    semiring_0_semiring_1 = semiring_0_nat,
    zero_neq_one_semiring_1 = zero_neq_one_nat}
  : nat semiring_1;

val semiring_1_no_zero_divisors_nat =
  {semiring_1_semiring_1_no_zero_divisors = semiring_1_nat,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_nat}
  : nat semiring_1_no_zero_divisors;

val cancel_semigroup_add_nat =
  {semigroup_add_cancel_semigroup_add = semigroup_add_nat} :
  nat cancel_semigroup_add;

val cancel_ab_semigroup_add_nat =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_nat,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_nat,
    minus_cancel_ab_semigroup_add = minus_nat}
  : nat cancel_ab_semigroup_add;

val cancel_comm_monoid_add_nat =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_nat,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_nat}
  : nat cancel_comm_monoid_add;

val semiring_0_cancel_nat =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_nat,
    semiring_0_semiring_0_cancel = semiring_0_nat}
  : nat semiring_0_cancel;

val ab_semigroup_mult_nat =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_nat} :
  nat ab_semigroup_mult;

val comm_semiring_nat =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_nat,
    semiring_comm_semiring = semiring_nat}
  : nat comm_semiring;

val comm_semiring_0_nat =
  {comm_semiring_comm_semiring_0 = comm_semiring_nat,
    semiring_0_comm_semiring_0 = semiring_0_nat}
  : nat comm_semiring_0;

val comm_semiring_0_cancel_nat =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_nat,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_nat}
  : nat comm_semiring_0_cancel;

val semiring_1_cancel_nat =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_nat,
    semiring_1_semiring_1_cancel = semiring_1_nat}
  : nat semiring_1_cancel;

val comm_monoid_mult_nat =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_nat,
    monoid_mult_comm_monoid_mult = monoid_mult_nat,
    dvd_comm_monoid_mult = dvd_nat}
  : nat comm_monoid_mult;

val comm_semiring_1_nat =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_nat,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_nat,
    semiring_1_comm_semiring_1 = semiring_1_nat}
  : nat comm_semiring_1;

val comm_semiring_1_cancel_nat =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_nat,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_nat,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_nat}
  : nat comm_semiring_1_cancel;

val semidom_nat =
  {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_nat,
    semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_nat}
  : nat semidom;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

type 'a semiring_char_0 = {semiring_1_semiring_char_0 : 'a semiring_1};
val semiring_1_semiring_char_0 = #semiring_1_semiring_char_0 :
  'a semiring_char_0 -> 'a semiring_1;

val semiring_char_0_nat = {semiring_1_semiring_char_0 = semiring_1_nat} :
  nat semiring_char_0;

val divide_trivial_nat =
  {one_divide_trivial = one_nat, zero_divide_trivial = zero_nat,
    divide_divide_trivial = divide_nat}
  : nat divide_trivial;

val semiring_no_zero_divisors_cancel_nat =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_nat}
  : nat semiring_no_zero_divisors_cancel;

val semidom_divide_nat =
  {divide_trivial_semidom_divide = divide_trivial_nat,
    semidom_semidom_divide = semidom_nat,
    semiring_no_zero_divisors_cancel_semidom_divide =
      semiring_no_zero_divisors_cancel_nat}
  : nat semidom_divide;

val semiring_modulo_nat =
  {comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_nat,
    modulo_semiring_modulo = modulo_nat}
  : nat semiring_modulo;

val semiring_modulo_trivial_nat =
  {divide_trivial_semiring_modulo_trivial = divide_trivial_nat,
    semiring_modulo_semiring_modulo_trivial = semiring_modulo_nat}
  : nat semiring_modulo_trivial;

val algebraic_semidom_nat =
  {semidom_divide_algebraic_semidom = semidom_divide_nat} :
  nat algebraic_semidom;

val semidom_modulo_nat =
  {algebraic_semidom_semidom_modulo = algebraic_semidom_nat,
    semiring_modulo_trivial_semidom_modulo = semiring_modulo_trivial_nat}
  : nat semidom_modulo;

fun eq A_ a b = equal A_ a b;

fun equal_prod A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

datatype rat = Frct of (int * int);

fun quotient_of (Frct x) = x;

fun equal_rata a b =
  equal_prod equal_int equal_int (quotient_of a) (quotient_of b);

val equal_rat = {equal = equal_rata} : rat equal;

fun normalize p =
  (if less_int zero_inta (snd p)
    then let
           val a = gcd_intc (fst p) (snd p);
         in
           (divide_inta (fst p) a, divide_inta (snd p) a)
         end
    else (if equal_inta (snd p) zero_inta then (zero_inta, one_inta)
           else let
                  val a = uminus_inta (gcd_intc (fst p) (snd p));
                in
                  (divide_inta (fst p) a, divide_inta (snd p) a)
                end));

fun times_rata p q = Frct let
                            val (a, c) = quotient_of p;
                            val (b, d) = quotient_of q;
                          in
                            normalize (times_inta a b, times_inta c d)
                          end;

val times_rat = {times = times_rata} : rat times;

val dvd_rat = {times_dvd = times_rat} : rat dvd;

fun abs_rata p = Frct let
                        val (a, b) = quotient_of p;
                      in
                        (abs_int a, b)
                      end;

type 'a abs = {abs : 'a -> 'a};
val abs = #abs : 'a abs -> 'a -> 'a;

val abs_rat = {abs = abs_rata} : rat abs;

val one_rata : rat = Frct (one_inta, one_inta);

val one_rat = {one = one_rata} : rat one;

fun sgn_rata p = Frct (sgn_int (fst (quotient_of p)), one_inta);

type 'a sgn = {sgn : 'a -> 'a};
val sgn = #sgn : 'a sgn -> 'a -> 'a;

val sgn_rat = {sgn = sgn_rata} : rat sgn;

fun uminus_rata p = Frct let
                           val (a, b) = quotient_of p;
                         in
                           (uminus_inta a, b)
                         end;

fun minus_rata p q =
  Frct let
         val (a, c) = quotient_of p;
         val (b, d) = quotient_of q;
       in
         normalize
           (minus_inta (times_inta a d) (times_inta b c), times_inta c d)
       end;

val zero_rata : rat = Frct (zero_inta, one_inta);

fun plus_rata p q =
  Frct let
         val (a, c) = quotient_of p;
         val (b, d) = quotient_of q;
       in
         normalize (plus_inta (times_inta a d) (times_inta b c), times_inta c d)
       end;

val plus_rat = {plus = plus_rata} : rat plus;

val semigroup_add_rat = {plus_semigroup_add = plus_rat} : rat semigroup_add;

val cancel_semigroup_add_rat =
  {semigroup_add_cancel_semigroup_add = semigroup_add_rat} :
  rat cancel_semigroup_add;

val ab_semigroup_add_rat = {semigroup_add_ab_semigroup_add = semigroup_add_rat}
  : rat ab_semigroup_add;

val minus_rat = {minus = minus_rata} : rat minus;

val cancel_ab_semigroup_add_rat =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_rat,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_rat,
    minus_cancel_ab_semigroup_add = minus_rat}
  : rat cancel_ab_semigroup_add;

val zero_rat = {zero = zero_rata} : rat zero;

val monoid_add_rat =
  {semigroup_add_monoid_add = semigroup_add_rat, zero_monoid_add = zero_rat} :
  rat monoid_add;

val comm_monoid_add_rat =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_rat,
    monoid_add_comm_monoid_add = monoid_add_rat}
  : rat comm_monoid_add;

val cancel_comm_monoid_add_rat =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_rat,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_rat}
  : rat cancel_comm_monoid_add;

val mult_zero_rat = {times_mult_zero = times_rat, zero_mult_zero = zero_rat} :
  rat mult_zero;

val semigroup_mult_rat = {times_semigroup_mult = times_rat} :
  rat semigroup_mult;

val semiring_rat =
  {ab_semigroup_add_semiring = ab_semigroup_add_rat,
    semigroup_mult_semiring = semigroup_mult_rat}
  : rat semiring;

val semiring_0_rat =
  {comm_monoid_add_semiring_0 = comm_monoid_add_rat,
    mult_zero_semiring_0 = mult_zero_rat, semiring_semiring_0 = semiring_rat}
  : rat semiring_0;

val semiring_0_cancel_rat =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_rat,
    semiring_0_semiring_0_cancel = semiring_0_rat}
  : rat semiring_0_cancel;

val ab_semigroup_mult_rat =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_rat} :
  rat ab_semigroup_mult;

val comm_semiring_rat =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_rat,
    semiring_comm_semiring = semiring_rat}
  : rat comm_semiring;

val comm_semiring_0_rat =
  {comm_semiring_comm_semiring_0 = comm_semiring_rat,
    semiring_0_comm_semiring_0 = semiring_0_rat}
  : rat comm_semiring_0;

val comm_semiring_0_cancel_rat =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_rat,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_rat}
  : rat comm_semiring_0_cancel;

val power_rat = {one_power = one_rat, times_power = times_rat} : rat power;

val monoid_mult_rat =
  {semigroup_mult_monoid_mult = semigroup_mult_rat,
    power_monoid_mult = power_rat}
  : rat monoid_mult;

val numeral_rat =
  {one_numeral = one_rat, semigroup_add_numeral = semigroup_add_rat} :
  rat numeral;

val semiring_numeral_rat =
  {monoid_mult_semiring_numeral = monoid_mult_rat,
    numeral_semiring_numeral = numeral_rat,
    semiring_semiring_numeral = semiring_rat}
  : rat semiring_numeral;

val zero_neq_one_rat =
  {one_zero_neq_one = one_rat, zero_zero_neq_one = zero_rat} : rat zero_neq_one;

val semiring_1_rat =
  {semiring_numeral_semiring_1 = semiring_numeral_rat,
    semiring_0_semiring_1 = semiring_0_rat,
    zero_neq_one_semiring_1 = zero_neq_one_rat}
  : rat semiring_1;

val semiring_1_cancel_rat =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_rat,
    semiring_1_semiring_1_cancel = semiring_1_rat}
  : rat semiring_1_cancel;

val comm_monoid_mult_rat =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_rat,
    monoid_mult_comm_monoid_mult = monoid_mult_rat,
    dvd_comm_monoid_mult = dvd_rat}
  : rat comm_monoid_mult;

val comm_semiring_1_rat =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_rat,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_rat,
    semiring_1_comm_semiring_1 = semiring_1_rat}
  : rat comm_semiring_1;

val comm_semiring_1_cancel_rat =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_rat,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_rat,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_rat}
  : rat comm_semiring_1_cancel;

val comm_semiring_1_cancel_crossproduct_rat =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
     comm_semiring_1_cancel_rat}
  : rat comm_semiring_1_cancel_crossproduct;

val semiring_no_zero_divisors_rat =
  {semiring_0_semiring_no_zero_divisors = semiring_0_rat} :
  rat semiring_no_zero_divisors;

val semiring_1_no_zero_divisors_rat =
  {semiring_1_semiring_1_no_zero_divisors = semiring_1_rat,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_rat}
  : rat semiring_1_no_zero_divisors;

val semiring_no_zero_divisors_cancel_rat =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_rat}
  : rat semiring_no_zero_divisors_cancel;

val uminus_rat = {uminus = uminus_rata} : rat uminus;

val group_add_rat =
  {cancel_semigroup_add_group_add = cancel_semigroup_add_rat,
    minus_group_add = minus_rat, monoid_add_group_add = monoid_add_rat,
    uminus_group_add = uminus_rat}
  : rat group_add;

val ab_group_add_rat =
  {cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_rat,
    group_add_ab_group_add = group_add_rat}
  : rat ab_group_add;

val ring_rat =
  {ab_group_add_ring = ab_group_add_rat,
    semiring_0_cancel_ring = semiring_0_cancel_rat}
  : rat ring;

val ring_no_zero_divisors_rat =
  {ring_ring_no_zero_divisors = ring_rat,
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
      semiring_no_zero_divisors_cancel_rat}
  : rat ring_no_zero_divisors;

val neg_numeral_rat =
  {group_add_neg_numeral = group_add_rat, numeral_neg_numeral = numeral_rat} :
  rat neg_numeral;

val ring_1_rat =
  {neg_numeral_ring_1 = neg_numeral_rat, ring_ring_1 = ring_rat,
    semiring_1_cancel_ring_1 = semiring_1_cancel_rat}
  : rat ring_1;

val ring_1_no_zero_divisors_rat =
  {ring_1_ring_1_no_zero_divisors = ring_1_rat,
    ring_no_zero_divisors_ring_1_no_zero_divisors = ring_no_zero_divisors_rat,
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
      semiring_1_no_zero_divisors_rat}
  : rat ring_1_no_zero_divisors;

val comm_ring_rat =
  {comm_semiring_0_cancel_comm_ring = comm_semiring_0_cancel_rat,
    ring_comm_ring = ring_rat}
  : rat comm_ring;

val comm_ring_1_rat =
  {comm_ring_comm_ring_1 = comm_ring_rat,
    comm_semiring_1_cancel_comm_ring_1 = comm_semiring_1_cancel_rat,
    ring_1_comm_ring_1 = ring_1_rat}
  : rat comm_ring_1;

val semidom_rat =
  {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_rat,
    semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_rat}
  : rat semidom;

val idom_rat =
  {comm_ring_1_idom = comm_ring_1_rat,
    ring_1_no_zero_divisors_idom = ring_1_no_zero_divisors_rat,
    semidom_idom = semidom_rat,
    comm_semiring_1_cancel_crossproduct_idom =
      comm_semiring_1_cancel_crossproduct_rat}
  : rat idom;

fun inverse_rata p =
  Frct let
         val (a, b) = quotient_of p;
       in
         (if equal_inta a zero_inta then (zero_inta, one_inta)
           else (times_inta (sgn_int a) b, abs_int a))
       end;

fun divide_rata p q = Frct let
                             val (a, c) = quotient_of p;
                             val (b, d) = quotient_of q;
                           in
                             normalize (times_inta a d, times_inta c b)
                           end;

type 'a inverse = {divide_inverse : 'a divide, inverse : 'a -> 'a};
val divide_inverse = #divide_inverse : 'a inverse -> 'a divide;
val inverse = #inverse : 'a inverse -> 'a -> 'a;

type 'a ufd = {idom_ufd : 'a idom};
val idom_ufd = #idom_ufd : 'a ufd -> 'a idom;

type 'a division_ring =
  {inverse_division_ring : 'a inverse,
    divide_trivial_division_ring : 'a divide_trivial,
    ring_1_no_zero_divisors_division_ring : 'a ring_1_no_zero_divisors};
val inverse_division_ring = #inverse_division_ring :
  'a division_ring -> 'a inverse;
val divide_trivial_division_ring = #divide_trivial_division_ring :
  'a division_ring -> 'a divide_trivial;
val ring_1_no_zero_divisors_division_ring =
  #ring_1_no_zero_divisors_division_ring :
  'a division_ring -> 'a ring_1_no_zero_divisors;

type 'a field =
  {division_ring_field : 'a division_ring, idom_divide_field : 'a idom_divide,
    ufd_field : 'a ufd};
val division_ring_field = #division_ring_field : 'a field -> 'a division_ring;
val idom_divide_field = #idom_divide_field : 'a field -> 'a idom_divide;
val ufd_field = #ufd_field : 'a field -> 'a ufd;

val ufd_rat = {idom_ufd = idom_rat} : rat ufd;

val divide_rat = {divide = divide_rata} : rat divide;

val divide_trivial_rat =
  {one_divide_trivial = one_rat, zero_divide_trivial = zero_rat,
    divide_divide_trivial = divide_rat}
  : rat divide_trivial;

val inverse_rat = {divide_inverse = divide_rat, inverse = inverse_rata} :
  rat inverse;

val division_ring_rat =
  {inverse_division_ring = inverse_rat,
    divide_trivial_division_ring = divide_trivial_rat,
    ring_1_no_zero_divisors_division_ring = ring_1_no_zero_divisors_rat}
  : rat division_ring;

val semidom_divide_rat =
  {divide_trivial_semidom_divide = divide_trivial_rat,
    semidom_semidom_divide = semidom_rat,
    semiring_no_zero_divisors_cancel_semidom_divide =
      semiring_no_zero_divisors_cancel_rat}
  : rat semidom_divide;

val idom_divide_rat =
  {idom_idom_divide = idom_rat, semidom_divide_idom_divide = semidom_divide_rat}
  : rat idom_divide;

val field_rat =
  {division_ring_field = division_ring_rat, idom_divide_field = idom_divide_rat,
    ufd_field = ufd_rat}
  : rat field;

fun less_eq_rat p q = let
                        val (a, c) = quotient_of p;
                        val (b, d) = quotient_of q;
                      in
                        less_eq_int (times_inta a d) (times_inta c b)
                      end;

fun less_rat p q = let
                     val (a, c) = quotient_of p;
                     val (b, d) = quotient_of q;
                   in
                     less_int (times_inta a d) (times_inta c b)
                   end;

type 'a abs_if =
  {abs_abs_if : 'a abs, minus_abs_if : 'a minus, uminus_abs_if : 'a uminus,
    zero_abs_if : 'a zero, ord_abs_if : 'a ord};
val abs_abs_if = #abs_abs_if : 'a abs_if -> 'a abs;
val minus_abs_if = #minus_abs_if : 'a abs_if -> 'a minus;
val uminus_abs_if = #uminus_abs_if : 'a abs_if -> 'a uminus;
val zero_abs_if = #zero_abs_if : 'a abs_if -> 'a zero;
val ord_abs_if = #ord_abs_if : 'a abs_if -> 'a ord;

val ord_rat = {less_eq = less_eq_rat, less = less_rat} : rat ord;

val abs_if_rat =
  {abs_abs_if = abs_rat, minus_abs_if = minus_rat, uminus_abs_if = uminus_rat,
    zero_abs_if = zero_rat, ord_abs_if = ord_rat}
  : rat abs_if;

type 'a ring_char_0 =
  {semiring_char_0_ring_char_0 : 'a semiring_char_0,
    ring_1_ring_char_0 : 'a ring_1};
val semiring_char_0_ring_char_0 = #semiring_char_0_ring_char_0 :
  'a ring_char_0 -> 'a semiring_char_0;
val ring_1_ring_char_0 = #ring_1_ring_char_0 : 'a ring_char_0 -> 'a ring_1;

val semiring_char_0_rat = {semiring_1_semiring_char_0 = semiring_1_rat} :
  rat semiring_char_0;

val ring_char_0_rat =
  {semiring_char_0_ring_char_0 = semiring_char_0_rat,
    ring_1_ring_char_0 = ring_1_rat}
  : rat ring_char_0;

val preorder_rat = {ord_preorder = ord_rat} : rat preorder;

val order_rat = {preorder_order = preorder_rat} : rat order;

type 'a no_bot = {order_no_bot : 'a order};
val order_no_bot = #order_no_bot : 'a no_bot -> 'a order;

val no_bot_rat = {order_no_bot = order_rat} : rat no_bot;

type 'a no_top = {order_no_top : 'a order};
val order_no_top = #order_no_top : 'a no_top -> 'a order;

val no_top_rat = {order_no_top = order_rat} : rat no_top;

val linorder_rat = {order_linorder = order_rat} : rat linorder;

type 'a idom_abs_sgn =
  {abs_idom_abs_sgn : 'a abs, sgn_idom_abs_sgn : 'a sgn,
    idom_idom_abs_sgn : 'a idom};
val abs_idom_abs_sgn = #abs_idom_abs_sgn : 'a idom_abs_sgn -> 'a abs;
val sgn_idom_abs_sgn = #sgn_idom_abs_sgn : 'a idom_abs_sgn -> 'a sgn;
val idom_idom_abs_sgn = #idom_idom_abs_sgn : 'a idom_abs_sgn -> 'a idom;

val idom_abs_sgn_rat =
  {abs_idom_abs_sgn = abs_rat, sgn_idom_abs_sgn = sgn_rat,
    idom_idom_abs_sgn = idom_rat}
  : rat idom_abs_sgn;

type 'a ordered_ab_semigroup_add =
  {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add,
    order_ordered_ab_semigroup_add : 'a order};
val ab_semigroup_add_ordered_ab_semigroup_add =
  #ab_semigroup_add_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a ab_semigroup_add;
val order_ordered_ab_semigroup_add = #order_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a order;

type 'a strict_ordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add};
val ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
  #ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
  'a strict_ordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_cancel_ab_semigroup_add =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
     'a cancel_ab_semigroup_add,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
      'a strict_ordered_ab_semigroup_add};
val cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
  #cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
  'a ordered_cancel_ab_semigroup_add -> 'a cancel_ab_semigroup_add;
val strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
  #strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
  'a ordered_cancel_ab_semigroup_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_comm_monoid_add =
  {comm_monoid_add_ordered_comm_monoid_add : 'a comm_monoid_add,
    ordered_ab_semigroup_add_ordered_comm_monoid_add :
      'a ordered_ab_semigroup_add};
val comm_monoid_add_ordered_comm_monoid_add =
  #comm_monoid_add_ordered_comm_monoid_add :
  'a ordered_comm_monoid_add -> 'a comm_monoid_add;
val ordered_ab_semigroup_add_ordered_comm_monoid_add =
  #ordered_ab_semigroup_add_ordered_comm_monoid_add :
  'a ordered_comm_monoid_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_semiring =
  {ordered_comm_monoid_add_ordered_semiring : 'a ordered_comm_monoid_add,
    semiring_ordered_semiring : 'a semiring};
val ordered_comm_monoid_add_ordered_semiring =
  #ordered_comm_monoid_add_ordered_semiring :
  'a ordered_semiring -> 'a ordered_comm_monoid_add;
val semiring_ordered_semiring = #semiring_ordered_semiring :
  'a ordered_semiring -> 'a semiring;

type 'a ordered_semiring_0 =
  {ordered_semiring_ordered_semiring_0 : 'a ordered_semiring,
    semiring_0_ordered_semiring_0 : 'a semiring_0};
val ordered_semiring_ordered_semiring_0 = #ordered_semiring_ordered_semiring_0 :
  'a ordered_semiring_0 -> 'a ordered_semiring;
val semiring_0_ordered_semiring_0 = #semiring_0_ordered_semiring_0 :
  'a ordered_semiring_0 -> 'a semiring_0;

type 'a ordered_cancel_semiring =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_semiring :
     'a ordered_cancel_ab_semigroup_add,
    ordered_semiring_0_ordered_cancel_semiring : 'a ordered_semiring_0,
    semiring_0_cancel_ordered_cancel_semiring : 'a semiring_0_cancel};
val ordered_cancel_ab_semigroup_add_ordered_cancel_semiring =
  #ordered_cancel_ab_semigroup_add_ordered_cancel_semiring :
  'a ordered_cancel_semiring -> 'a ordered_cancel_ab_semigroup_add;
val ordered_semiring_0_ordered_cancel_semiring =
  #ordered_semiring_0_ordered_cancel_semiring :
  'a ordered_cancel_semiring -> 'a ordered_semiring_0;
val semiring_0_cancel_ordered_cancel_semiring =
  #semiring_0_cancel_ordered_cancel_semiring :
  'a ordered_cancel_semiring -> 'a semiring_0_cancel;

type 'a ordered_ab_semigroup_add_imp_le =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
     'a ordered_cancel_ab_semigroup_add};
val ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
  #ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
  'a ordered_ab_semigroup_add_imp_le -> 'a ordered_cancel_ab_semigroup_add;

type 'a strict_ordered_comm_monoid_add =
  {comm_monoid_add_strict_ordered_comm_monoid_add : 'a comm_monoid_add,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
      'a strict_ordered_ab_semigroup_add};
val comm_monoid_add_strict_ordered_comm_monoid_add =
  #comm_monoid_add_strict_ordered_comm_monoid_add :
  'a strict_ordered_comm_monoid_add -> 'a comm_monoid_add;
val strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
  #strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
  'a strict_ordered_comm_monoid_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_cancel_comm_monoid_add =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
     'a ordered_cancel_ab_semigroup_add,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a ordered_comm_monoid_add,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a strict_ordered_comm_monoid_add};
val ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
  #ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a ordered_cancel_ab_semigroup_add;
val ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
  #ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a ordered_comm_monoid_add;
val strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
  #strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a strict_ordered_comm_monoid_add;

type 'a ordered_ab_semigroup_monoid_add_imp_le =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
     'a cancel_comm_monoid_add,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_ab_semigroup_add_imp_le,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_cancel_comm_monoid_add};
val cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
  #cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le -> 'a cancel_comm_monoid_add;
val ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
  #ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le ->
    'a ordered_ab_semigroup_add_imp_le;
val ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
  #ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le ->
    'a ordered_cancel_comm_monoid_add;

type 'a ordered_ab_group_add =
  {ab_group_add_ordered_ab_group_add : 'a ab_group_add,
    ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add :
      'a ordered_ab_semigroup_monoid_add_imp_le};
val ab_group_add_ordered_ab_group_add = #ab_group_add_ordered_ab_group_add :
  'a ordered_ab_group_add -> 'a ab_group_add;
val ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add =
  #ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add :
  'a ordered_ab_group_add -> 'a ordered_ab_semigroup_monoid_add_imp_le;

type 'a ordered_ring =
  {ordered_ab_group_add_ordered_ring : 'a ordered_ab_group_add,
    ordered_cancel_semiring_ordered_ring : 'a ordered_cancel_semiring,
    ring_ordered_ring : 'a ring};
val ordered_ab_group_add_ordered_ring = #ordered_ab_group_add_ordered_ring :
  'a ordered_ring -> 'a ordered_ab_group_add;
val ordered_cancel_semiring_ordered_ring = #ordered_cancel_semiring_ordered_ring
  : 'a ordered_ring -> 'a ordered_cancel_semiring;
val ring_ordered_ring = #ring_ordered_ring : 'a ordered_ring -> 'a ring;

val ordered_ab_semigroup_add_rat =
  {ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_rat,
    order_ordered_ab_semigroup_add = order_rat}
  : rat ordered_ab_semigroup_add;

val strict_ordered_ab_semigroup_add_rat =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
     ordered_ab_semigroup_add_rat}
  : rat strict_ordered_ab_semigroup_add;

val ordered_cancel_ab_semigroup_add_rat =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
     cancel_ab_semigroup_add_rat,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
      strict_ordered_ab_semigroup_add_rat}
  : rat ordered_cancel_ab_semigroup_add;

val ordered_comm_monoid_add_rat =
  {comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_rat,
    ordered_ab_semigroup_add_ordered_comm_monoid_add =
      ordered_ab_semigroup_add_rat}
  : rat ordered_comm_monoid_add;

val ordered_semiring_rat =
  {ordered_comm_monoid_add_ordered_semiring = ordered_comm_monoid_add_rat,
    semiring_ordered_semiring = semiring_rat}
  : rat ordered_semiring;

val ordered_semiring_0_rat =
  {ordered_semiring_ordered_semiring_0 = ordered_semiring_rat,
    semiring_0_ordered_semiring_0 = semiring_0_rat}
  : rat ordered_semiring_0;

val ordered_cancel_semiring_rat =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_semiring =
     ordered_cancel_ab_semigroup_add_rat,
    ordered_semiring_0_ordered_cancel_semiring = ordered_semiring_0_rat,
    semiring_0_cancel_ordered_cancel_semiring = semiring_0_cancel_rat}
  : rat ordered_cancel_semiring;

val ordered_ab_semigroup_add_imp_le_rat =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
     ordered_cancel_ab_semigroup_add_rat}
  : rat ordered_ab_semigroup_add_imp_le;

val strict_ordered_comm_monoid_add_rat =
  {comm_monoid_add_strict_ordered_comm_monoid_add = comm_monoid_add_rat,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
      strict_ordered_ab_semigroup_add_rat}
  : rat strict_ordered_comm_monoid_add;

val ordered_cancel_comm_monoid_add_rat =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
     ordered_cancel_ab_semigroup_add_rat,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      ordered_comm_monoid_add_rat,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      strict_ordered_comm_monoid_add_rat}
  : rat ordered_cancel_comm_monoid_add;

val ordered_ab_semigroup_monoid_add_imp_le_rat =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
     cancel_comm_monoid_add_rat,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_ab_semigroup_add_imp_le_rat,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_cancel_comm_monoid_add_rat}
  : rat ordered_ab_semigroup_monoid_add_imp_le;

val ordered_ab_group_add_rat =
  {ab_group_add_ordered_ab_group_add = ab_group_add_rat,
    ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add =
      ordered_ab_semigroup_monoid_add_imp_le_rat}
  : rat ordered_ab_group_add;

val ordered_ring_rat =
  {ordered_ab_group_add_ordered_ring = ordered_ab_group_add_rat,
    ordered_cancel_semiring_ordered_ring = ordered_cancel_semiring_rat,
    ring_ordered_ring = ring_rat}
  : rat ordered_ring;

type 'a field_char_0 =
  {field_field_char_0 : 'a field, ring_char_0_field_char_0 : 'a ring_char_0};
val field_field_char_0 = #field_field_char_0 : 'a field_char_0 -> 'a field;
val ring_char_0_field_char_0 = #ring_char_0_field_char_0 :
  'a field_char_0 -> 'a ring_char_0;

val field_char_0_rat =
  {field_field_char_0 = field_rat, ring_char_0_field_char_0 = ring_char_0_rat} :
  rat field_char_0;

type 'a zero_less_one =
  {order_zero_less_one : 'a order,
    zero_neq_one_zero_less_one : 'a zero_neq_one};
val order_zero_less_one = #order_zero_less_one : 'a zero_less_one -> 'a order;
val zero_neq_one_zero_less_one = #zero_neq_one_zero_less_one :
  'a zero_less_one -> 'a zero_neq_one;

val zero_less_one_rat =
  {order_zero_less_one = order_rat,
    zero_neq_one_zero_less_one = zero_neq_one_rat}
  : rat zero_less_one;

type 'a field_abs_sgn =
  {field_field_abs_sgn : 'a field,
    idom_abs_sgn_field_abs_sgn : 'a idom_abs_sgn};
val field_field_abs_sgn = #field_field_abs_sgn : 'a field_abs_sgn -> 'a field;
val idom_abs_sgn_field_abs_sgn = #idom_abs_sgn_field_abs_sgn :
  'a field_abs_sgn -> 'a idom_abs_sgn;

val field_abs_sgn_rat =
  {field_field_abs_sgn = field_rat,
    idom_abs_sgn_field_abs_sgn = idom_abs_sgn_rat}
  : rat field_abs_sgn;

type 'a dense_order = {order_dense_order : 'a order};
val order_dense_order = #order_dense_order : 'a dense_order -> 'a order;

val dense_order_rat = {order_dense_order = order_rat} : rat dense_order;

type 'a linordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add,
    linorder_linordered_ab_semigroup_add : 'a linorder};
val ordered_ab_semigroup_add_linordered_ab_semigroup_add =
  #ordered_ab_semigroup_add_linordered_ab_semigroup_add :
  'a linordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;
val linorder_linordered_ab_semigroup_add = #linorder_linordered_ab_semigroup_add
  : 'a linordered_ab_semigroup_add -> 'a linorder;

type 'a linordered_cancel_ab_semigroup_add =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
     'a linordered_ab_semigroup_add,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
      'a ordered_ab_semigroup_add_imp_le};
val linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
  #linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
  'a linordered_cancel_ab_semigroup_add -> 'a linordered_ab_semigroup_add;
val ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
  #ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
  'a linordered_cancel_ab_semigroup_add -> 'a ordered_ab_semigroup_add_imp_le;

type 'a linordered_semiring =
  {linordered_cancel_ab_semigroup_add_linordered_semiring :
     'a linordered_cancel_ab_semigroup_add,
    ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring :
      'a ordered_ab_semigroup_monoid_add_imp_le,
    ordered_cancel_semiring_linordered_semiring : 'a ordered_cancel_semiring};
val linordered_cancel_ab_semigroup_add_linordered_semiring =
  #linordered_cancel_ab_semigroup_add_linordered_semiring :
  'a linordered_semiring -> 'a linordered_cancel_ab_semigroup_add;
val ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring =
  #ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring :
  'a linordered_semiring -> 'a ordered_ab_semigroup_monoid_add_imp_le;
val ordered_cancel_semiring_linordered_semiring =
  #ordered_cancel_semiring_linordered_semiring :
  'a linordered_semiring -> 'a ordered_cancel_semiring;

type 'a linordered_semiring_strict =
  {linordered_semiring_linordered_semiring_strict : 'a linordered_semiring};
val linordered_semiring_linordered_semiring_strict =
  #linordered_semiring_linordered_semiring_strict :
  'a linordered_semiring_strict -> 'a linordered_semiring;

type 'a linordered_semiring_1 =
  {linordered_semiring_linordered_semiring_1 : 'a linordered_semiring,
    semiring_1_linordered_semiring_1 : 'a semiring_1,
    zero_less_one_linordered_semiring_1 : 'a zero_less_one};
val linordered_semiring_linordered_semiring_1 =
  #linordered_semiring_linordered_semiring_1 :
  'a linordered_semiring_1 -> 'a linordered_semiring;
val semiring_1_linordered_semiring_1 = #semiring_1_linordered_semiring_1 :
  'a linordered_semiring_1 -> 'a semiring_1;
val zero_less_one_linordered_semiring_1 = #zero_less_one_linordered_semiring_1 :
  'a linordered_semiring_1 -> 'a zero_less_one;

type 'a linordered_semiring_1_strict =
  {linordered_semiring_1_linordered_semiring_1_strict :
     'a linordered_semiring_1,
    linordered_semiring_strict_linordered_semiring_1_strict :
      'a linordered_semiring_strict};
val linordered_semiring_1_linordered_semiring_1_strict =
  #linordered_semiring_1_linordered_semiring_1_strict :
  'a linordered_semiring_1_strict -> 'a linordered_semiring_1;
val linordered_semiring_strict_linordered_semiring_1_strict =
  #linordered_semiring_strict_linordered_semiring_1_strict :
  'a linordered_semiring_1_strict -> 'a linordered_semiring_strict;

type 'a ordered_ab_group_add_abs =
  {abs_ordered_ab_group_add_abs : 'a abs,
    ordered_ab_group_add_ordered_ab_group_add_abs : 'a ordered_ab_group_add};
val abs_ordered_ab_group_add_abs = #abs_ordered_ab_group_add_abs :
  'a ordered_ab_group_add_abs -> 'a abs;
val ordered_ab_group_add_ordered_ab_group_add_abs =
  #ordered_ab_group_add_ordered_ab_group_add_abs :
  'a ordered_ab_group_add_abs -> 'a ordered_ab_group_add;

type 'a linordered_ab_group_add =
  {linordered_cancel_ab_semigroup_add_linordered_ab_group_add :
     'a linordered_cancel_ab_semigroup_add,
    ordered_ab_group_add_linordered_ab_group_add : 'a ordered_ab_group_add};
val linordered_cancel_ab_semigroup_add_linordered_ab_group_add =
  #linordered_cancel_ab_semigroup_add_linordered_ab_group_add :
  'a linordered_ab_group_add -> 'a linordered_cancel_ab_semigroup_add;
val ordered_ab_group_add_linordered_ab_group_add =
  #ordered_ab_group_add_linordered_ab_group_add :
  'a linordered_ab_group_add -> 'a ordered_ab_group_add;

type 'a linordered_ring =
  {linordered_ab_group_add_linordered_ring : 'a linordered_ab_group_add,
    ordered_ab_group_add_abs_linordered_ring : 'a ordered_ab_group_add_abs,
    abs_if_linordered_ring : 'a abs_if,
    linordered_semiring_linordered_ring : 'a linordered_semiring,
    ordered_ring_linordered_ring : 'a ordered_ring};
val linordered_ab_group_add_linordered_ring =
  #linordered_ab_group_add_linordered_ring :
  'a linordered_ring -> 'a linordered_ab_group_add;
val ordered_ab_group_add_abs_linordered_ring =
  #ordered_ab_group_add_abs_linordered_ring :
  'a linordered_ring -> 'a ordered_ab_group_add_abs;
val abs_if_linordered_ring = #abs_if_linordered_ring :
  'a linordered_ring -> 'a abs_if;
val linordered_semiring_linordered_ring = #linordered_semiring_linordered_ring :
  'a linordered_ring -> 'a linordered_semiring;
val ordered_ring_linordered_ring = #ordered_ring_linordered_ring :
  'a linordered_ring -> 'a ordered_ring;

type 'a linordered_ring_strict =
  {linordered_ring_linordered_ring_strict : 'a linordered_ring,
    linordered_semiring_strict_linordered_ring_strict :
      'a linordered_semiring_strict,
    ring_no_zero_divisors_linordered_ring_strict : 'a ring_no_zero_divisors};
val linordered_ring_linordered_ring_strict =
  #linordered_ring_linordered_ring_strict :
  'a linordered_ring_strict -> 'a linordered_ring;
val linordered_semiring_strict_linordered_ring_strict =
  #linordered_semiring_strict_linordered_ring_strict :
  'a linordered_ring_strict -> 'a linordered_semiring_strict;
val ring_no_zero_divisors_linordered_ring_strict =
  #ring_no_zero_divisors_linordered_ring_strict :
  'a linordered_ring_strict -> 'a ring_no_zero_divisors;

type 'a ordered_comm_semiring =
  {comm_semiring_0_ordered_comm_semiring : 'a comm_semiring_0,
    ordered_semiring_ordered_comm_semiring : 'a ordered_semiring};
val comm_semiring_0_ordered_comm_semiring =
  #comm_semiring_0_ordered_comm_semiring :
  'a ordered_comm_semiring -> 'a comm_semiring_0;
val ordered_semiring_ordered_comm_semiring =
  #ordered_semiring_ordered_comm_semiring :
  'a ordered_comm_semiring -> 'a ordered_semiring;

type 'a ordered_cancel_comm_semiring =
  {comm_semiring_0_cancel_ordered_cancel_comm_semiring :
     'a comm_semiring_0_cancel,
    ordered_cancel_semiring_ordered_cancel_comm_semiring :
      'a ordered_cancel_semiring,
    ordered_comm_semiring_ordered_cancel_comm_semiring :
      'a ordered_comm_semiring};
val comm_semiring_0_cancel_ordered_cancel_comm_semiring =
  #comm_semiring_0_cancel_ordered_cancel_comm_semiring :
  'a ordered_cancel_comm_semiring -> 'a comm_semiring_0_cancel;
val ordered_cancel_semiring_ordered_cancel_comm_semiring =
  #ordered_cancel_semiring_ordered_cancel_comm_semiring :
  'a ordered_cancel_comm_semiring -> 'a ordered_cancel_semiring;
val ordered_comm_semiring_ordered_cancel_comm_semiring =
  #ordered_comm_semiring_ordered_cancel_comm_semiring :
  'a ordered_cancel_comm_semiring -> 'a ordered_comm_semiring;

type 'a linordered_comm_semiring_strict =
  {linordered_semiring_strict_linordered_comm_semiring_strict :
     'a linordered_semiring_strict,
    ordered_cancel_comm_semiring_linordered_comm_semiring_strict :
      'a ordered_cancel_comm_semiring};
val linordered_semiring_strict_linordered_comm_semiring_strict =
  #linordered_semiring_strict_linordered_comm_semiring_strict :
  'a linordered_comm_semiring_strict -> 'a linordered_semiring_strict;
val ordered_cancel_comm_semiring_linordered_comm_semiring_strict =
  #ordered_cancel_comm_semiring_linordered_comm_semiring_strict :
  'a linordered_comm_semiring_strict -> 'a ordered_cancel_comm_semiring;

type 'a linordered_nonzero_semiring =
  {semiring_char_0_linordered_nonzero_semiring : 'a semiring_char_0,
    linorder_linordered_nonzero_semiring : 'a linorder,
    comm_semiring_1_linordered_nonzero_semiring : 'a comm_semiring_1,
    ordered_comm_semiring_linordered_nonzero_semiring :
      'a ordered_comm_semiring,
    zero_less_one_linordered_nonzero_semiring : 'a zero_less_one};
val semiring_char_0_linordered_nonzero_semiring =
  #semiring_char_0_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a semiring_char_0;
val linorder_linordered_nonzero_semiring = #linorder_linordered_nonzero_semiring
  : 'a linordered_nonzero_semiring -> 'a linorder;
val comm_semiring_1_linordered_nonzero_semiring =
  #comm_semiring_1_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a comm_semiring_1;
val ordered_comm_semiring_linordered_nonzero_semiring =
  #ordered_comm_semiring_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a ordered_comm_semiring;
val zero_less_one_linordered_nonzero_semiring =
  #zero_less_one_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a zero_less_one;

type 'a linordered_semidom =
  {linordered_comm_semiring_strict_linordered_semidom :
     'a linordered_comm_semiring_strict,
    linordered_nonzero_semiring_linordered_semidom :
      'a linordered_nonzero_semiring,
    semidom_linordered_semidom : 'a semidom};
val linordered_comm_semiring_strict_linordered_semidom =
  #linordered_comm_semiring_strict_linordered_semidom :
  'a linordered_semidom -> 'a linordered_comm_semiring_strict;
val linordered_nonzero_semiring_linordered_semidom =
  #linordered_nonzero_semiring_linordered_semidom :
  'a linordered_semidom -> 'a linordered_nonzero_semiring;
val semidom_linordered_semidom = #semidom_linordered_semidom :
  'a linordered_semidom -> 'a semidom;

type 'a ordered_comm_ring =
  {comm_ring_ordered_comm_ring : 'a comm_ring,
    ordered_cancel_comm_semiring_ordered_comm_ring :
      'a ordered_cancel_comm_semiring,
    ordered_ring_ordered_comm_ring : 'a ordered_ring};
val comm_ring_ordered_comm_ring = #comm_ring_ordered_comm_ring :
  'a ordered_comm_ring -> 'a comm_ring;
val ordered_cancel_comm_semiring_ordered_comm_ring =
  #ordered_cancel_comm_semiring_ordered_comm_ring :
  'a ordered_comm_ring -> 'a ordered_cancel_comm_semiring;
val ordered_ring_ordered_comm_ring = #ordered_ring_ordered_comm_ring :
  'a ordered_comm_ring -> 'a ordered_ring;

type 'a ordered_ring_abs =
  {ordered_ab_group_add_abs_ordered_ring_abs : 'a ordered_ab_group_add_abs,
    ordered_ring_ordered_ring_abs : 'a ordered_ring};
val ordered_ab_group_add_abs_ordered_ring_abs =
  #ordered_ab_group_add_abs_ordered_ring_abs :
  'a ordered_ring_abs -> 'a ordered_ab_group_add_abs;
val ordered_ring_ordered_ring_abs = #ordered_ring_ordered_ring_abs :
  'a ordered_ring_abs -> 'a ordered_ring;

type 'a linordered_idom =
  {ring_char_0_linordered_idom : 'a ring_char_0,
    idom_abs_sgn_linordered_idom : 'a idom_abs_sgn,
    linordered_ring_strict_linordered_idom : 'a linordered_ring_strict,
    linordered_semidom_linordered_idom : 'a linordered_semidom,
    linordered_semiring_1_strict_linordered_idom :
      'a linordered_semiring_1_strict,
    ordered_comm_ring_linordered_idom : 'a ordered_comm_ring,
    ordered_ring_abs_linordered_idom : 'a ordered_ring_abs};
val ring_char_0_linordered_idom = #ring_char_0_linordered_idom :
  'a linordered_idom -> 'a ring_char_0;
val idom_abs_sgn_linordered_idom = #idom_abs_sgn_linordered_idom :
  'a linordered_idom -> 'a idom_abs_sgn;
val linordered_ring_strict_linordered_idom =
  #linordered_ring_strict_linordered_idom :
  'a linordered_idom -> 'a linordered_ring_strict;
val linordered_semidom_linordered_idom = #linordered_semidom_linordered_idom :
  'a linordered_idom -> 'a linordered_semidom;
val linordered_semiring_1_strict_linordered_idom =
  #linordered_semiring_1_strict_linordered_idom :
  'a linordered_idom -> 'a linordered_semiring_1_strict;
val ordered_comm_ring_linordered_idom = #ordered_comm_ring_linordered_idom :
  'a linordered_idom -> 'a ordered_comm_ring;
val ordered_ring_abs_linordered_idom = #ordered_ring_abs_linordered_idom :
  'a linordered_idom -> 'a ordered_ring_abs;

val linordered_ab_semigroup_add_rat =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add =
     ordered_ab_semigroup_add_rat,
    linorder_linordered_ab_semigroup_add = linorder_rat}
  : rat linordered_ab_semigroup_add;

val linordered_cancel_ab_semigroup_add_rat =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
     linordered_ab_semigroup_add_rat,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
      ordered_ab_semigroup_add_imp_le_rat}
  : rat linordered_cancel_ab_semigroup_add;

val linordered_semiring_rat =
  {linordered_cancel_ab_semigroup_add_linordered_semiring =
     linordered_cancel_ab_semigroup_add_rat,
    ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring =
      ordered_ab_semigroup_monoid_add_imp_le_rat,
    ordered_cancel_semiring_linordered_semiring = ordered_cancel_semiring_rat}
  : rat linordered_semiring;

val linordered_semiring_strict_rat =
  {linordered_semiring_linordered_semiring_strict = linordered_semiring_rat} :
  rat linordered_semiring_strict;

val linordered_semiring_1_rat =
  {linordered_semiring_linordered_semiring_1 = linordered_semiring_rat,
    semiring_1_linordered_semiring_1 = semiring_1_rat,
    zero_less_one_linordered_semiring_1 = zero_less_one_rat}
  : rat linordered_semiring_1;

val linordered_semiring_1_strict_rat =
  {linordered_semiring_1_linordered_semiring_1_strict =
     linordered_semiring_1_rat,
    linordered_semiring_strict_linordered_semiring_1_strict =
      linordered_semiring_strict_rat}
  : rat linordered_semiring_1_strict;

val ordered_ab_group_add_abs_rat =
  {abs_ordered_ab_group_add_abs = abs_rat,
    ordered_ab_group_add_ordered_ab_group_add_abs = ordered_ab_group_add_rat}
  : rat ordered_ab_group_add_abs;

val linordered_ab_group_add_rat =
  {linordered_cancel_ab_semigroup_add_linordered_ab_group_add =
     linordered_cancel_ab_semigroup_add_rat,
    ordered_ab_group_add_linordered_ab_group_add = ordered_ab_group_add_rat}
  : rat linordered_ab_group_add;

val linordered_ring_rat =
  {linordered_ab_group_add_linordered_ring = linordered_ab_group_add_rat,
    ordered_ab_group_add_abs_linordered_ring = ordered_ab_group_add_abs_rat,
    abs_if_linordered_ring = abs_if_rat,
    linordered_semiring_linordered_ring = linordered_semiring_rat,
    ordered_ring_linordered_ring = ordered_ring_rat}
  : rat linordered_ring;

val linordered_ring_strict_rat =
  {linordered_ring_linordered_ring_strict = linordered_ring_rat,
    linordered_semiring_strict_linordered_ring_strict =
      linordered_semiring_strict_rat,
    ring_no_zero_divisors_linordered_ring_strict = ring_no_zero_divisors_rat}
  : rat linordered_ring_strict;

val ordered_comm_semiring_rat =
  {comm_semiring_0_ordered_comm_semiring = comm_semiring_0_rat,
    ordered_semiring_ordered_comm_semiring = ordered_semiring_rat}
  : rat ordered_comm_semiring;

val ordered_cancel_comm_semiring_rat =
  {comm_semiring_0_cancel_ordered_cancel_comm_semiring =
     comm_semiring_0_cancel_rat,
    ordered_cancel_semiring_ordered_cancel_comm_semiring =
      ordered_cancel_semiring_rat,
    ordered_comm_semiring_ordered_cancel_comm_semiring =
      ordered_comm_semiring_rat}
  : rat ordered_cancel_comm_semiring;

val linordered_comm_semiring_strict_rat =
  {linordered_semiring_strict_linordered_comm_semiring_strict =
     linordered_semiring_strict_rat,
    ordered_cancel_comm_semiring_linordered_comm_semiring_strict =
      ordered_cancel_comm_semiring_rat}
  : rat linordered_comm_semiring_strict;

val linordered_nonzero_semiring_rat =
  {semiring_char_0_linordered_nonzero_semiring = semiring_char_0_rat,
    linorder_linordered_nonzero_semiring = linorder_rat,
    comm_semiring_1_linordered_nonzero_semiring = comm_semiring_1_rat,
    ordered_comm_semiring_linordered_nonzero_semiring =
      ordered_comm_semiring_rat,
    zero_less_one_linordered_nonzero_semiring = zero_less_one_rat}
  : rat linordered_nonzero_semiring;

val linordered_semidom_rat =
  {linordered_comm_semiring_strict_linordered_semidom =
     linordered_comm_semiring_strict_rat,
    linordered_nonzero_semiring_linordered_semidom =
      linordered_nonzero_semiring_rat,
    semidom_linordered_semidom = semidom_rat}
  : rat linordered_semidom;

val ordered_comm_ring_rat =
  {comm_ring_ordered_comm_ring = comm_ring_rat,
    ordered_cancel_comm_semiring_ordered_comm_ring =
      ordered_cancel_comm_semiring_rat,
    ordered_ring_ordered_comm_ring = ordered_ring_rat}
  : rat ordered_comm_ring;

val ordered_ring_abs_rat =
  {ordered_ab_group_add_abs_ordered_ring_abs = ordered_ab_group_add_abs_rat,
    ordered_ring_ordered_ring_abs = ordered_ring_rat}
  : rat ordered_ring_abs;

val linordered_idom_rat =
  {ring_char_0_linordered_idom = ring_char_0_rat,
    idom_abs_sgn_linordered_idom = idom_abs_sgn_rat,
    linordered_ring_strict_linordered_idom = linordered_ring_strict_rat,
    linordered_semidom_linordered_idom = linordered_semidom_rat,
    linordered_semiring_1_strict_linordered_idom =
      linordered_semiring_1_strict_rat,
    ordered_comm_ring_linordered_idom = ordered_comm_ring_rat,
    ordered_ring_abs_linordered_idom = ordered_ring_abs_rat}
  : rat linordered_idom;

type 'a non_strict_order = {ord_non_strict_order : 'a ord};
val ord_non_strict_order = #ord_non_strict_order :
  'a non_strict_order -> 'a ord;

type 'a ordered_ab_semigroup =
  {ab_semigroup_add_ordered_ab_semigroup : 'a ab_semigroup_add,
    monoid_add_ordered_ab_semigroup : 'a monoid_add,
    non_strict_order_ordered_ab_semigroup : 'a non_strict_order};
val ab_semigroup_add_ordered_ab_semigroup =
  #ab_semigroup_add_ordered_ab_semigroup :
  'a ordered_ab_semigroup -> 'a ab_semigroup_add;
val monoid_add_ordered_ab_semigroup = #monoid_add_ordered_ab_semigroup :
  'a ordered_ab_semigroup -> 'a monoid_add;
val non_strict_order_ordered_ab_semigroup =
  #non_strict_order_ordered_ab_semigroup :
  'a ordered_ab_semigroup -> 'a non_strict_order;

type 'a ordered_semiring_0a =
  {semiring_0_ordered_semiring_0a : 'a semiring_0,
    ordered_ab_semigroup_ordered_semiring_0 : 'a ordered_ab_semigroup};
val semiring_0_ordered_semiring_0a = #semiring_0_ordered_semiring_0a :
  'a ordered_semiring_0a -> 'a semiring_0;
val ordered_ab_semigroup_ordered_semiring_0 =
  #ordered_ab_semigroup_ordered_semiring_0 :
  'a ordered_semiring_0a -> 'a ordered_ab_semigroup;

type 'a ordered_semiring_1 =
  {semiring_1_ordered_semiring_1 : 'a semiring_1,
    ordered_semiring_0_ordered_semiring_1 : 'a ordered_semiring_0a};
val semiring_1_ordered_semiring_1 = #semiring_1_ordered_semiring_1 :
  'a ordered_semiring_1 -> 'a semiring_1;
val ordered_semiring_0_ordered_semiring_1 =
  #ordered_semiring_0_ordered_semiring_1 :
  'a ordered_semiring_1 -> 'a ordered_semiring_0a;

type 'a poly_carrier =
  {comm_semiring_1_poly_carrier : 'a comm_semiring_1,
    ordered_semiring_1_poly_carrier : 'a ordered_semiring_1};
val comm_semiring_1_poly_carrier = #comm_semiring_1_poly_carrier :
  'a poly_carrier -> 'a comm_semiring_1;
val ordered_semiring_1_poly_carrier = #ordered_semiring_1_poly_carrier :
  'a poly_carrier -> 'a ordered_semiring_1;

val non_strict_order_rat = {ord_non_strict_order = ord_rat} :
  rat non_strict_order;

val ordered_ab_semigroup_rat =
  {ab_semigroup_add_ordered_ab_semigroup = ab_semigroup_add_rat,
    monoid_add_ordered_ab_semigroup = monoid_add_rat,
    non_strict_order_ordered_ab_semigroup = non_strict_order_rat}
  : rat ordered_ab_semigroup;

val ordered_semiring_0_rata =
  {semiring_0_ordered_semiring_0a = semiring_0_rat,
    ordered_ab_semigroup_ordered_semiring_0 = ordered_ab_semigroup_rat}
  : rat ordered_semiring_0a;

val ordered_semiring_1_rat =
  {semiring_1_ordered_semiring_1 = semiring_1_rat,
    ordered_semiring_0_ordered_semiring_1 = ordered_semiring_0_rata}
  : rat ordered_semiring_1;

val poly_carrier_rat =
  {comm_semiring_1_poly_carrier = comm_semiring_1_rat,
    ordered_semiring_1_poly_carrier = ordered_semiring_1_rat}
  : rat poly_carrier;

type 'a dense_linorder =
  {dense_order_dense_linorder : 'a dense_order,
    linorder_dense_linorder : 'a linorder};
val dense_order_dense_linorder = #dense_order_dense_linorder :
  'a dense_linorder -> 'a dense_order;
val linorder_dense_linorder = #linorder_dense_linorder :
  'a dense_linorder -> 'a linorder;

type 'a unbounded_dense_linorder =
  {dense_linorder_unbounded_dense_linorder : 'a dense_linorder,
    no_bot_unbounded_dense_linorder : 'a no_bot,
    no_top_unbounded_dense_linorder : 'a no_top};
val dense_linorder_unbounded_dense_linorder =
  #dense_linorder_unbounded_dense_linorder :
  'a unbounded_dense_linorder -> 'a dense_linorder;
val no_bot_unbounded_dense_linorder = #no_bot_unbounded_dense_linorder :
  'a unbounded_dense_linorder -> 'a no_bot;
val no_top_unbounded_dense_linorder = #no_top_unbounded_dense_linorder :
  'a unbounded_dense_linorder -> 'a no_top;

type 'a linordered_field =
  {field_abs_sgn_linordered_field : 'a field_abs_sgn,
    field_char_0_linordered_field : 'a field_char_0,
    unbounded_dense_linorder_linordered_field : 'a unbounded_dense_linorder,
    linordered_idom_linordered_field : 'a linordered_idom};
val field_abs_sgn_linordered_field = #field_abs_sgn_linordered_field :
  'a linordered_field -> 'a field_abs_sgn;
val field_char_0_linordered_field = #field_char_0_linordered_field :
  'a linordered_field -> 'a field_char_0;
val unbounded_dense_linorder_linordered_field =
  #unbounded_dense_linorder_linordered_field :
  'a linordered_field -> 'a unbounded_dense_linorder;
val linordered_idom_linordered_field = #linordered_idom_linordered_field :
  'a linordered_field -> 'a linordered_idom;

val dense_linorder_rat =
  {dense_order_dense_linorder = dense_order_rat,
    linorder_dense_linorder = linorder_rat}
  : rat dense_linorder;

val unbounded_dense_linorder_rat =
  {dense_linorder_unbounded_dense_linorder = dense_linorder_rat,
    no_bot_unbounded_dense_linorder = no_bot_rat,
    no_top_unbounded_dense_linorder = no_top_rat}
  : rat unbounded_dense_linorder;

val linordered_field_rat =
  {field_abs_sgn_linordered_field = field_abs_sgn_rat,
    field_char_0_linordered_field = field_char_0_rat,
    unbounded_dense_linorder_linordered_field = unbounded_dense_linorder_rat,
    linordered_idom_linordered_field = linordered_idom_rat}
  : rat linordered_field;

type 'a archimedean_field =
  {linordered_field_archimedean_field : 'a linordered_field};
val linordered_field_archimedean_field = #linordered_field_archimedean_field :
  'a archimedean_field -> 'a linordered_field;

type 'a large_ordered_semiring_1 =
  {poly_carrier_large_ordered_semiring_1 : 'a poly_carrier};
val poly_carrier_large_ordered_semiring_1 =
  #poly_carrier_large_ordered_semiring_1 :
  'a large_ordered_semiring_1 -> 'a poly_carrier;

type 'a floor_ceiling =
  {archimedean_field_floor_ceiling : 'a archimedean_field,
    large_ordered_semiring_1_floor_ceiling : 'a large_ordered_semiring_1,
    floor : 'a -> int};
val archimedean_field_floor_ceiling = #archimedean_field_floor_ceiling :
  'a floor_ceiling -> 'a archimedean_field;
val large_ordered_semiring_1_floor_ceiling =
  #large_ordered_semiring_1_floor_ceiling :
  'a floor_ceiling -> 'a large_ordered_semiring_1;
val floor = #floor : 'a floor_ceiling -> 'a -> int;

fun floor_rat p = let
                    val (a, b) = quotient_of p;
                  in
                    divide_inta a b
                  end;

val archimedean_field_rat =
  {linordered_field_archimedean_field = linordered_field_rat} :
  rat archimedean_field;

val large_ordered_semiring_1_rat =
  {poly_carrier_large_ordered_semiring_1 = poly_carrier_rat} :
  rat large_ordered_semiring_1;

val floor_ceiling_rat =
  {archimedean_field_floor_ceiling = archimedean_field_rat,
    large_ordered_semiring_1_floor_ceiling = large_ordered_semiring_1_rat,
    floor = floor_rat}
  : rat floor_ceiling;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype 'a poly = Poly of 'a list;

datatype real_alg_2 = Rational of rat |
  Irrational of nat * (int poly * (rat * rat));

datatype real_alg_3 = Real_Alg_Invariant of real_alg_2;

datatype real_alg = Real_Alg_Quotient of real_alg_3;

fun rep_real_alg_3 (Real_Alg_Invariant x) = x;

fun coeffs A_ (Poly x) = x;

fun equal_polya (A1_, A2_) p q = equal_lista A2_ (coeffs A1_ p) (coeffs A1_ q);

fun equal_2 (Rational r) (Rational q) = equal_rata r q
  | equal_2 (Irrational (n, (p, uu))) (Irrational (m, (q, uv))) =
    equal_polya (zero_int, equal_int) p q andalso equal_nata n m
  | equal_2 (Rational r) (Irrational (uw, yy)) = false
  | equal_2 (Irrational (ux, xx)) (Rational q) = false;

fun equal_3 xa xc = equal_2 (rep_real_alg_3 xa) (rep_real_alg_3 xc);

fun equal_real_alg (Real_Alg_Quotient xc) (Real_Alg_Quotient xa) =
  equal_3 xc xa;

datatype real = Real_of of real_alg;

fun equal_reala (Real_of x) (Real_of y) = equal_real_alg x y;

val equal_real = {equal = equal_reala} : real equal;

fun map_prod f g (a, b) = (f a, g b);

fun divmod_nat m n =
  let
    val k = integer_of_nat m;
    val l = integer_of_nat n;
  in
    map_prod nat_of_integer nat_of_integer
      (if ((k : IntInf.int) = (0 : IntInf.int))
        then ((0 : IntInf.int), (0 : IntInf.int))
        else (if ((l : IntInf.int) = (0 : IntInf.int))
               then ((0 : IntInf.int), k) else IntInf.divMod ( k, l )))
  end;

fun binary_power A_ x n =
  (if equal_nata n zero_nata then one ((one_power o power_monoid_mult) A_)
    else let
           val (d, r) = divmod_nat n (nat_of_integer (2 : IntInf.int));
           val reca =
             binary_power A_ (times ((times_power o power_monoid_mult) A_) x x)
               d;
         in
           (if equal_nata r zero_nata then reca
             else times ((times_power o power_monoid_mult) A_) reca x)
         end);

fun suc n = plus_nata n one_nata;

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun size_list x = gen_length zero_nata x;

fun dropWhile p [] = []
  | dropWhile p (x :: xs) = (if p x then dropWhile p xs else x :: xs);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun strip_while p = rev o dropWhile p o rev;

fun poly_of_list (A1_, A2_) asa =
  Poly (strip_while
         (eq A2_ (zero ((zero_monoid_add o monoid_add_comm_monoid_add) A1_)))
         asa);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip xs [] = []
  | zip [] ys = [];

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun poly_mult_rat_main (A1_, A2_) n d f =
  let
    val fs =
      coeffs
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_semidom o semidom_idom)
          A2_)
        f;
    val k = size_list fs;
  in
    poly_of_list
      ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
         semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
         comm_semiring_1_cancel_semidom o semidom_idom)
         A2_,
        A1_)
      (map (fn (fi, i) =>
             times ((times_dvd o dvd_comm_monoid_mult o
                      comm_monoid_mult_comm_semiring_1 o
                      comm_semiring_1_comm_semiring_1_cancel o
                      comm_semiring_1_cancel_semidom o semidom_idom)
                     A2_)
               (times
                 ((times_dvd o dvd_comm_monoid_mult o
                    comm_monoid_mult_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_semidom o semidom_idom)
                   A2_)
                 fi (binary_power
                      ((monoid_mult_semiring_numeral o
                         semiring_numeral_semiring_1 o
                         semiring_1_comm_semiring_1 o
                         comm_semiring_1_comm_semiring_1_cancel o
                         comm_semiring_1_cancel_semidom o semidom_idom)
                        A2_)
                      d i))
               (binary_power
                 ((monoid_mult_semiring_numeral o semiring_numeral_semiring_1 o
                    semiring_1_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_semidom o semidom_idom)
                   A2_)
                 n (minus_nata k (suc i))))
        (zip fs (upt zero_nata k)))
  end;

fun poly_mult_rat r p = let
                          val (n, d) = quotient_of r;
                        in
                          poly_mult_rat_main (equal_int, idom_int) n d p
                        end;

fun map_poly B_ (A1_, A2_) f p =
  Poly (strip_while (eq A2_ (zero A1_)) (map f (coeffs B_ p)));

fun sdiv_poly (A1_, A2_) p a =
  map_poly
    ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
       semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
       comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide)
      A2_)
    ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
       semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
       comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide)
       A2_,
      A1_)
    (fn c =>
      divide
        ((divide_divide_trivial o divide_trivial_semidom_divide o
           semidom_divide_idom_divide)
          A2_)
        c a)
    p;

fun nth (x :: xs) n =
  (if equal_nata n zero_nata then x else nth xs (minus_nata n one_nata));

fun nth_default dflt xs n =
  (if less_nat n (size_list xs) then nth xs n else dflt);

fun coeff A_ p = nth_default (zero A_) (coeffs A_ p);

fun id x = (fn xa => xa) x;

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun fold_coeffs A_ f p = foldr f (coeffs A_ p);

fun content A_ p =
  fold_coeffs
    ((zero_gcd o gcd_comm_monoid_gcd o comm_monoid_gcd_semiring_gcd) A_)
    (gcda ((gcd_comm_monoid_gcd o comm_monoid_gcd_semiring_gcd) A_)) p
    (zero ((zero_gcd o gcd_comm_monoid_gcd o comm_monoid_gcd_semiring_gcd) A_));

fun degree A_ p = minus_nata (size_list (coeffs A_ p)) one_nata;

fun cf_pos_poly f =
  let
    val c = content semiring_gcd_int f;
    val a = times_inta (sgn_int (coeff zero_int f (degree zero_int f))) c;
  in
    sdiv_poly (equal_int, idom_divide_int) f a
  end;

fun of_int a = Frct (a, one_inta);

fun tighten_poly_bounds p l r sr =
  let
    val m =
      divide_rata (plus_rata l r) (of_int (Int_of_integer (2 : IntInf.int)));
    val sm =
      sgn_rata
        (fold_coeffs zero_int
          (fn a => fn b => plus_rata (of_int a) (times_rata m b)) p zero_rata);
  in
    (if equal_rata sm sr then (l, (m, sm)) else (m, (r, sr)))
  end;

fun tighten_poly_bounds_epsilon p x l r sr =
  (if less_eq_rat (minus_rata r l) x then (l, (r, sr))
    else let
           val (la, (a, b)) = tighten_poly_bounds p l r sr;
         in
           tighten_poly_bounds_epsilon p x la a b
         end);

fun tighten_poly_bounds_for_x p x l r sr =
  (if less_rat x l orelse less_rat r x then (l, (r, sr))
    else let
           val (la, (a, b)) = tighten_poly_bounds p l r sr;
         in
           tighten_poly_bounds_for_x p x la a b
         end);

fun normalize_bounds_1_main eps rai =
  let
    val (p, (l, r)) = rai;
    val (la, (ra, sr)) =
      tighten_poly_bounds_epsilon p eps l r
        (sgn_rata
          (fold_coeffs zero_int
            (fn a => fn b => plus_rata (of_int a) (times_rata r b)) p
            zero_rata));
    val fr = of_int (floor_rat ra);
    val (lb, (rb, _)) = tighten_poly_bounds_for_x p fr la ra sr;
  in
    (p, (lb, rb))
  end;

fun fract a b = Frct (normalize (a, b));

val real_alg_precision : rat = fract one_inta (Int_of_integer (2 : IntInf.int));

fun normalize_bounds_1 x = normalize_bounds_1_main real_alg_precision x;

fun poly_real_alg_1 (p, (uu, uv)) = p;

datatype root_info = Root_Info of (rat -> rat -> nat) * (rat -> nat);

fun number_root (Root_Info (x1, x2)) = x2;

fun dvd (A1_, A2_) a b =
  eq A1_
    (modulo
      ((modulo_semiring_modulo o semiring_modulo_semiring_modulo_trivial o
         semiring_modulo_trivial_semidom_modulo)
        A2_)
      b a)
    (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_comm_semiring_1 o
             comm_semiring_1_comm_semiring_1_cancel o
             comm_semiring_1_cancel_semidom o semidom_semidom_divide o
             semidom_divide_algebraic_semidom o
             algebraic_semidom_semidom_modulo)
            A2_));

fun poly_neg_number_rootat p =
  (if dvd (equal_nat, semidom_modulo_nat) (nat_of_integer (2 : IntInf.int))
        (degree zero_rat p)
    then sgn_rata (coeff zero_rat p (degree zero_rat p))
    else uminus_rata (sgn_rata (coeff zero_rat p (degree zero_rat p))));

fun remdups_adj A_ [] = []
  | remdups_adj A_ [x] = [x]
  | remdups_adj A_ (x :: y :: xs) =
    (if eq A_ x y then remdups_adj A_ (x :: xs)
      else x :: remdups_adj A_ (y :: xs));

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun sign_changes_neg_number_rootat ps =
  minus_nata
    (size_list
      (remdups_adj equal_rat
        (filter (fn x => not (equal_rata x zero_rata))
          (map poly_neg_number_rootat ps))))
    one_nata;

fun horner_sum B_ f a xs =
  foldr (fn x => fn b =>
          plus ((plus_semigroup_add o semigroup_add_monoid_add o
                  monoid_add_comm_monoid_add o comm_monoid_add_semiring_0 o
                  semiring_0_comm_semiring_0)
                 B_)
            (f x)
            (times
              ((times_mult_zero o mult_zero_semiring_0 o
                 semiring_0_comm_semiring_0)
                B_)
              a b))
    xs (zero ((zero_mult_zero o mult_zero_semiring_0 o
                semiring_0_comm_semiring_0)
               B_));

fun poly A_ p a =
  horner_sum A_ id a
    (coeffs
      ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_comm_semiring_0) A_)
      p);

fun sign_changes_rat ps x =
  minus_nata
    (size_list
      (remdups_adj equal_rat
        (filter (fn xa => not (equal_rata xa zero_rata))
          (map (fn p => sgn_rata (poly comm_semiring_0_rat p x)) ps))))
    one_nata;

fun uminus_polya A_ p =
  Poly (map (uminus ((uminus_group_add o group_add_ab_group_add) A_))
         (coeffs
           ((zero_monoid_add o monoid_add_group_add o group_add_ab_group_add)
             A_)
           p));

fun minus_poly_rev_list A_ (x :: xs) (y :: ys) =
  minus (minus_group_add A_) x y :: minus_poly_rev_list A_ xs ys
  | minus_poly_rev_list A_ xs [] = xs
  | minus_poly_rev_list A_ [] (y :: ys) = [];

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun hd (x21 :: x22) = x21;

fun mod_poly_one_main_list (A1_, A2_) r d n =
  (if equal_nata n zero_nata then r
    else let
           val a = hd r;
           val rr =
             tl (if eq A1_ a
                      (zero ((zero_mult_zero o mult_zero_semiring_0 o
                               semiring_0_semiring_1 o
                               semiring_1_comm_semiring_1 o
                               comm_semiring_1_comm_semiring_1_cancel o
                               comm_semiring_1_cancel_comm_ring_1)
                              A2_))
                  then r
                  else minus_poly_rev_list
                         ((group_add_neg_numeral o neg_numeral_ring_1 o
                            ring_1_comm_ring_1)
                           A2_)
                         r (map (times
                                  ((times_dvd o dvd_comm_monoid_mult o
                                     comm_monoid_mult_comm_semiring_1 o
                                     comm_semiring_1_comm_semiring_1_cancel o
                                     comm_semiring_1_cancel_comm_ring_1)
                                    A2_)
                                  a)
                             d));
         in
           mod_poly_one_main_list (A1_, A2_) rr d (minus_nata n one_nata)
         end);

fun null [] = true
  | null (x :: xs) = false;

fun last (x :: xs) = (if null xs then x else last xs);

fun modulo_poly (A1_, A2_) f g =
  let
    val cg =
      coeffs
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide o
           idom_divide_field)
          A1_)
        g;
  in
    (if null cg then f
      else let
             val cf =
               coeffs
                 ((zero_mult_zero o mult_zero_semiring_0 o
                    semiring_0_semiring_1 o semiring_1_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_semidom o semidom_idom o
                    idom_idom_divide o idom_divide_field)
                   A1_)
                 f;
             val ilc =
               inverse ((inverse_division_ring o division_ring_field) A1_)
                 (last cg);
             val ch =
               map (times
                     ((times_dvd o dvd_comm_monoid_mult o
                        comm_monoid_mult_comm_semiring_1 o
                        comm_semiring_1_comm_semiring_1_cancel o
                        comm_semiring_1_cancel_semidom o semidom_idom o
                        idom_idom_divide o idom_divide_field)
                       A1_)
                     ilc)
                 cg;
             val r =
               mod_poly_one_main_list
                 (A2_, (comm_ring_1_idom o idom_idom_divide o idom_divide_field)
                         A1_)
                 (rev cf) (rev ch)
                 (minus_nata (plus_nata one_nata (size_list cf))
                   (size_list cg));
           in
             poly_of_list
               ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
                  semiring_1_comm_semiring_1 o
                  comm_semiring_1_comm_semiring_1_cancel o
                  comm_semiring_1_cancel_semidom o semidom_idom o
                  idom_idom_divide o idom_divide_field)
                  A1_,
                 A2_)
               (rev r)
           end)
  end;

fun sturm_aux_rat p q =
  (if equal_nata (degree zero_rat q) zero_nata then [p, q]
    else p :: sturm_aux_rat q
                (uminus_polya ab_group_add_rat
                  (modulo_poly (field_rat, equal_rat) p q)));

fun cCons (A1_, A2_) x xs =
  (if null xs andalso eq A2_ x (zero A1_) then [] else x :: xs);

fun pderiv_coeffs_code (A1_, A2_, A3_) f (x :: xs) =
  cCons ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1)
           A2_,
          A1_)
    (times
      ((times_dvd o dvd_comm_monoid_mult o comm_monoid_mult_comm_semiring_1)
        A2_)
      f x)
    (pderiv_coeffs_code (A1_, A2_, A3_)
      (plus ((plus_semigroup_add o semigroup_add_numeral o
               numeral_semiring_numeral o semiring_numeral_semiring_1 o
               semiring_1_comm_semiring_1)
              A2_)
        f (one ((one_numeral o numeral_semiring_numeral o
                  semiring_numeral_semiring_1 o semiring_1_comm_semiring_1)
                 A2_)))
      xs)
  | pderiv_coeffs_code (A1_, A2_, A3_) f [] = [];

fun pderiv_coeffs (A1_, A2_, A3_) xs =
  pderiv_coeffs_code (A1_, A2_, A3_)
    (one ((one_numeral o numeral_semiring_numeral o
            semiring_numeral_semiring_1 o semiring_1_comm_semiring_1)
           A2_))
    (tl xs);

fun pderiv (A1_, A2_, A3_) p =
  Poly (pderiv_coeffs (A1_, A2_, A3_)
         (coeffs
           ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
              semiring_1_comm_semiring_1)
             A2_)
           p));

fun sturm_rat p =
  sturm_aux_rat p
    (pderiv (equal_rat, comm_semiring_1_rat, semiring_no_zero_divisors_rat) p);

fun root_info p =
  (if equal_nata (degree zero_int p) one_nata
    then let
           val x =
             fract (uminus_inta
                     (case coeffs zero_int p of [] => zero_inta | x :: _ => x))
               (coeff zero_int p one_nata);
         in
           Root_Info
             ((fn l => fn r =>
                (if less_eq_rat l x andalso less_eq_rat x r then one_nata
                  else zero_nata)),
               (fn b => (if less_eq_rat x b then one_nata else zero_nata)))
         end
    else let
           val rp = map_poly zero_int (zero_rat, equal_rat) of_int p;
           val ps = sturm_rat rp;
         in
           Root_Info
             ((fn a => fn b =>
                minus_nata (sign_changes_rat ps a) (sign_changes_rat ps b)),
               (fn a =>
                 minus_nata (sign_changes_neg_number_rootat ps)
                   (sign_changes_rat ps a)))
         end);

fun real_alg_2 rai =
  let
    val p = poly_real_alg_1 rai;
  in
    (if equal_nata (degree zero_int p) one_nata
      then Rational
             (fract
               (uminus_inta
                 (case coeffs zero_int p of [] => zero_inta | x :: _ => x))
               (coeff zero_int p one_nata))
      else let
             val (pa, (l, r)) = normalize_bounds_1 rai;
           in
             Irrational (number_root (root_info p) r, (pa, (l, r)))
           end)
  end;

fun mult_rat_1_pos r1 (p2, (l2, r2)) =
  real_alg_2
    (cf_pos_poly (poly_mult_rat r1 p2), (times_rata l2 r1, times_rata r2 r1));

fun abs_int_poly p =
  (if less_int (coeff zero_int p (degree zero_int p)) zero_inta
    then uminus_polya ab_group_add_int p else p);

fun zero_polya A_ = Poly [];

fun pCons (A1_, A2_) a p = Poly (cCons (A1_, A2_) a (coeffs A1_ p));

fun poly_uminus_inner (A1_, A2_) [] =
  zero_polya
    ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
       semiring_1_semiring_1_cancel o semiring_1_cancel_ring_1)
      A2_)
  | poly_uminus_inner (A1_, A2_) [a] =
    pCons ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_semiring_1_cancel o semiring_1_cancel_ring_1)
             A2_,
            A1_)
      a (zero_polya
          ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_semiring_1_cancel o semiring_1_cancel_ring_1)
            A2_))
  | poly_uminus_inner (A1_, A2_) (a :: b :: cs) =
    pCons ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_semiring_1_cancel o semiring_1_cancel_ring_1)
             A2_,
            A1_)
      a (pCons
          ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_semiring_1_cancel o semiring_1_cancel_ring_1)
             A2_,
            A1_)
          (uminus
            ((uminus_group_add o group_add_neg_numeral o neg_numeral_ring_1)
              A2_)
            b)
          (poly_uminus_inner (A1_, A2_) cs));

fun poly_uminus (A1_, A2_) p =
  poly_uminus_inner (A1_, A2_)
    (coeffs
      ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
         semiring_1_semiring_1_cancel o semiring_1_cancel_ring_1)
        A2_)
      p);

fun uminus_1 (p, (l, r)) =
  (abs_int_poly (poly_uminus (equal_int, ring_1_int) p),
    (uminus_rata r, uminus_rata l));

fun uminus_2 (Rational r) = Rational (uminus_rata r)
  | uminus_2 (Irrational (n, x)) = real_alg_2 (uminus_1 x);

fun mult_rat_1 x y =
  (if less_rat x zero_rata then uminus_2 (mult_rat_1_pos (uminus_rata x) y)
    else (if equal_rata x zero_rata then Rational zero_rata
           else mult_rat_1_pos x y));

fun l_r (Root_Info (x1, x2)) = x1;

fun select_correct_factor_main bnd_update bnd_get bnd todo old l r n =
  (case todo
    of [] =>
      (if equal_nata n one_nata then (hd old, (l, r))
        else let
               val bnda = bnd_update bnd;
               val (la, ra) = bnd_get bnda;
             in
               select_correct_factor_main bnd_update bnd_get bnda old [] la ra
                 zero_nata
             end)
    | (p, ri) :: todoa =>
      let
        val m = l_r ri l r;
      in
        (if equal_nata m zero_nata
          then select_correct_factor_main bnd_update bnd_get bnd todoa old l r n
          else select_correct_factor_main bnd_update bnd_get bnd todoa
                 ((p, ri) :: old) l r (plus_nata n m))
      end);

fun select_correct_factor bnd_update bnd_get init polys =
  let
    val (l, r) = bnd_get init;
  in
    select_correct_factor_main bnd_update bnd_get init polys [] l r zero_nata
  end;

datatype int_poly_factorization_algorithm =
  Abs_int_poly_factorization_algorithm of (int poly -> int poly list);

datatype 'a arith_ops_record =
  Arith_Ops_Record of
    'a * 'a * ('a -> 'a -> 'a) * ('a -> 'a -> 'a) * ('a -> 'a -> 'a) *
      ('a -> 'a) * ('a -> 'a -> 'a) * ('a -> 'a) * ('a -> 'a -> 'a) *
      ('a -> 'a) * ('a -> 'a) * (int -> 'a) * ('a -> int) * ('a -> bool);

fun onea
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x2;

val karatsuba_lower_bound : nat = nat_of_integer (7 : IntInf.int);

fun zeroa
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x1;

fun poly_of_list_i A_ ops = strip_while (eq A_ (zeroa ops));

fun uminusa
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x6;

fun minusa
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x5;

fun coeffs_minus_i ops (x :: xs) (y :: ys) =
  minusa ops x y :: coeffs_minus_i ops xs ys
  | coeffs_minus_i ops xs [] = xs
  | coeffs_minus_i ops [] (v :: va) = map (uminusa ops) (v :: va);

fun replicate n x =
  (if equal_nata n zero_nata then []
    else x :: replicate (minus_nata n one_nata) x);

fun monom_mult_i ops n xs =
  (if null xs then xs else replicate n (zeroa ops) @ xs);

fun cCons_i A_ ops x xs =
  (if null xs andalso eq A_ x (zeroa ops) then [] else x :: xs);

fun minus_poly_i A_ ops (x :: xs) (y :: ys) =
  cCons_i A_ ops (minusa ops x y) (minus_poly_i A_ ops xs ys)
  | minus_poly_i A_ ops xs [] = xs
  | minus_poly_i A_ ops [] (v :: va) = map (uminusa ops) (v :: va);

fun plusa
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x3;

fun plus_poly_i A_ ops (x :: xs) (y :: ys) =
  cCons_i A_ ops (plusa ops x y) (plus_poly_i A_ ops xs ys)
  | plus_poly_i A_ ops xs [] = xs
  | plus_poly_i A_ ops [] (v :: va) = v :: va;

fun split_at n (x :: xs) =
  (if equal_nata n zero_nata then ([], x :: xs)
    else let
           val (bef, a) = split_at (minus_nata n one_nata) xs;
         in
           (x :: bef, a)
         end)
  | split_at n [] = ([], []);

fun timesa
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x4;

fun smult_i A_ ops a pp =
  (if eq A_ a (zeroa ops) then []
    else strip_while (eq A_ (zeroa ops)) (map (timesa ops a) pp));

fun karatsuba_main_i A_ ops f n g m =
  (if less_eq_nat n karatsuba_lower_bound orelse
        less_eq_nat m karatsuba_lower_bound
    then let
           val ff = poly_of_list_i A_ ops f;
         in
           foldr (fn a => fn p =>
                   plus_poly_i A_ ops (smult_i A_ ops a ff)
                     (cCons_i A_ ops (zeroa ops) p))
             g []
         end
    else let
           val n2 = divide_nata n (nat_of_integer (2 : IntInf.int));
         in
           (if less_nat n2 m
             then let
                    val (f0, f1) = split_at n2 f;
                    val (g0, g1) = split_at n2 g;
                    val p1 =
                      karatsuba_main_i A_ ops f1 (minus_nata n n2) g1
                        (minus_nata m n2);
                    val p2 =
                      karatsuba_main_i A_ ops (coeffs_minus_i ops f1 f0) n2
                        (coeffs_minus_i ops g1 g0) n2;
                    val p3 = karatsuba_main_i A_ ops f0 n2 g0 n2;
                  in
                    plus_poly_i A_ ops (monom_mult_i ops (plus_nata n2 n2) p1)
                      (plus_poly_i A_ ops
                        (monom_mult_i ops n2
                          (plus_poly_i A_ ops (minus_poly_i A_ ops p1 p2) p3))
                        p3)
                  end
             else let
                    val (f0, f1) = split_at n2 f;
                    val p1 = karatsuba_main_i A_ ops f1 (minus_nata n n2) g m;
                    val a = karatsuba_main_i A_ ops f0 n2 g m;
                  in
                    plus_poly_i A_ ops (monom_mult_i ops n2 p1) a
                  end)
         end);

fun times_poly_i A_ ops f g =
  let
    val n = size_list f;
    val m = size_list g;
  in
    (if less_eq_nat n karatsuba_lower_bound orelse
          less_eq_nat m karatsuba_lower_bound
      then (if less_eq_nat n m
             then foldr (fn a => fn p =>
                          plus_poly_i A_ ops (smult_i A_ ops a g)
                            (cCons_i A_ ops (zeroa ops) p))
                    f []
             else foldr (fn a => fn p =>
                          plus_poly_i A_ ops (smult_i A_ ops a f)
                            (cCons_i A_ ops (zeroa ops) p))
                    g [])
      else (if less_eq_nat n m then karatsuba_main_i A_ ops g m f n
             else karatsuba_main_i A_ ops f n g m))
  end;

fun power_poly_f_mod_i A_ ff_ops modulus a n =
  (if equal_nata n zero_nata then modulus [onea ff_ops]
    else let
           val (d, r) = divmod_nat n (nat_of_integer (2 : IntInf.int));
           val reca =
             power_poly_f_mod_i A_ ff_ops modulus
               (modulus (times_poly_i A_ ff_ops a a)) d;
         in
           (if equal_nata r zero_nata then reca
             else modulus (times_poly_i A_ ff_ops reca a))
         end);

fun inversea
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x8;

fun minus_poly_rev_list_i ops (x :: xs) (y :: ys) =
  minusa ops x y :: minus_poly_rev_list_i ops xs ys
  | minus_poly_rev_list_i ops xs [] = xs
  | minus_poly_rev_list_i ops [] (y :: ys) = [];

fun mod_poly_one_main_i A_ ops r d n =
  (if equal_nata n zero_nata then r
    else let
           val a = hd r;
           val rr =
             tl (if eq A_ a (zeroa ops) then r
                  else minus_poly_rev_list_i ops r (map (timesa ops a) d));
         in
           mod_poly_one_main_i A_ ops rr d (minus_nata n one_nata)
         end);

fun mod_field_poly_i A_ ops cf cg =
  (if null cg then cf
    else let
           val ilc = inversea ops (last cg);
           val ch = map (timesa ops ilc) cg;
           val r =
             mod_poly_one_main_i A_ ops (rev cf) (rev ch)
               (minus_nata (plus_nata one_nata (size_list cf)) (size_list cg));
         in
           poly_of_list_i A_ ops (rev r)
         end);

fun divmod_poly_one_main_i A_ ops q r d n =
  (if equal_nata n zero_nata then (q, r)
    else let
           val a = hd r;
           val qqq = cCons_i A_ ops a q;
           val rr =
             tl (if eq A_ a (zeroa ops) then r
                  else minus_poly_rev_list_i ops r (map (timesa ops a) d));
         in
           divmod_poly_one_main_i A_ ops qqq rr d (minus_nata n one_nata)
         end);

fun div_field_poly_i A_ ops cf cg =
  (if null cg then []
    else let
           val ilc = inversea ops (last cg);
           val ch = map (timesa ops ilc) cg;
           val q =
             fst (divmod_poly_one_main_i A_ ops [] (rev cf) (rev ch)
                   (minus_nata (plus_nata one_nata (size_list cf))
                     (size_list cg)));
         in
           poly_of_list_i A_ ops (map (timesa ops ilc) q)
         end);

fun normalizeb
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x10;

fun moduloa
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x9;

fun gcd_eucl_i A_ ops a b =
  (if eq A_ b (zeroa ops) then normalizeb ops a
    else gcd_eucl_i A_ ops b (moduloa ops a b));

fun of_intb
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x12;

fun unit_factora
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x11;

fun lead_coeff_i ops pp = (case pp of [] => zeroa ops | _ :: _ => last pp);

fun unit_factor_poly_i A_ ops xs =
  cCons_i A_ ops (unit_factora ops (lead_coeff_i ops xs)) [];

fun normalize_poly_i A_ ops xs =
  smult_i A_ ops (inversea ops (unit_factora ops (lead_coeff_i ops xs))) xs;

fun dp
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x14;

fun no_leading p xs = (if not (null xs) then not (p (hd xs)) else true);

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun is_poly A_ ops xs =
  list_all (dp ops) xs andalso no_leading (eq A_ (zeroa ops)) (rev xs);

fun poly_ops A_ ops =
  Arith_Ops_Record
    ([], [onea ops], plus_poly_i A_ ops, times_poly_i A_ ops,
      minus_poly_i A_ ops, map (uminusa ops), div_field_poly_i A_ ops,
      (fn _ => []), mod_field_poly_i A_ ops, normalize_poly_i A_ ops,
      unit_factor_poly_i A_ ops,
      (fn i => (if equal_inta i zero_inta then [] else [of_intb ops i])),
      (fn _ => zero_inta), is_poly A_ ops);

fun gcd_poly_i A_ ops = gcd_eucl_i (equal_list A_) (poly_ops A_ ops);

fun degree_i pp = minus_nata (size_list pp) one_nata;

fun dist_degree_factorize_main_i A_ p ff_ops ze on dv v w d res =
  (if equal_lista A_ v [on] then res
    else (if less_nat dv (plus_nata d d) then (dv, v) :: res
           else let
                  val wa =
                    power_poly_f_mod_i A_ ff_ops
                      (fn f => mod_field_poly_i A_ ff_ops f v) w (nat p);
                  val da = suc d;
                  val gd =
                    gcd_poly_i A_ ff_ops (minus_poly_i A_ ff_ops wa [ze, on]) v;
                in
                  (if equal_lista A_ gd [on]
                    then dist_degree_factorize_main_i A_ p ff_ops ze on dv v wa
                           da res
                    else let
                           val va = div_field_poly_i A_ ff_ops v gd;
                         in
                           dist_degree_factorize_main_i A_ p ff_ops ze on
                             (degree_i va) va (mod_field_poly_i A_ ff_ops wa va)
                             da ((da, gd) :: res)
                         end)
                end));

fun distinct_degree_factorization_i A_ p ff_ops f =
  let
    val ze = zeroa ff_ops;
    val on = onea ff_ops;
  in
    (if equal_nata (degree_i f) one_nata then [(one_nata, f)]
      else dist_degree_factorize_main_i A_ p ff_ops ze on (degree_i f) f
             [ze, on] zero_nata [])
  end;

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun partition p [] = ([], [])
  | partition p (x :: xs) = let
                              val (yes, no) = partition p xs;
                            in
                              (if p x then (x :: yes, no) else (yes, x :: no))
                            end;

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun berlekamp_factorization_main_i A_ p ff_ops ze on d divs (v :: vs) n =
  (if equal_lista A_ v [on]
    then berlekamp_factorization_main_i A_ p ff_ops ze on d divs vs n
    else (if equal_nata (size_list divs) n then divs
           else let
                  val of_int = of_intb ff_ops;
                  val facts =
                    filter (fn w => not (equal_lista A_ w [on]))
                      (maps (fn u =>
                              map (fn s =>
                                    gcd_poly_i A_ ff_ops u
                                      (minus_poly_i A_ ff_ops v
(if equal_nata s zero_nata then [] else [of_int (int_of_nat s)])))
                                (upt zero_nata (nat p)))
                        divs);
                  val (lin, nonlin) =
                    partition (fn q => equal_nata (degree_i q) d) facts;
                in
                  lin @ berlekamp_factorization_main_i A_ p ff_ops ze on d
                          nonlin vs (minus_nata n (size_list lin))
                end))
  | berlekamp_factorization_main_i A_ p ff_ops ze on d divs [] n = divs;

fun power_polys_i A_ ff_ops mul_p u curr_p i =
  (if equal_nata i zero_nata then []
    else curr_p ::
           power_polys_i A_ ff_ops mul_p u
             (mod_field_poly_i A_ ff_ops (times_poly_i A_ ff_ops curr_p mul_p)
               u)
             (minus_nata i one_nata));

datatype 'a x_a_mat_impl_option_x_x_x_a_iarray_iarray_nat_prod_nat_prod_option =
  Abs_x_a_mat_impl_option_x_x_x_a_iarray_iarray_nat_prod_nat_prod_option of
    (nat * (nat * ('a Vector.vector) Vector.vector)) option;

fun rep_x_a_mat_impl_option_x_x_x_a_iarray_iarray_nat_prod_nat_prod_option
  (Abs_x_a_mat_impl_option_x_x_x_a_iarray_iarray_nat_prod_nat_prod_option x) =
  x;

datatype 'a mat_impl =
  Abs_mat_impl of (nat * (nat * ('a Vector.vector) Vector.vector));

fun rep_mat_impl (Abs_mat_impl x) = x;

fun sel21 xa =
  Abs_mat_impl
    (case rep_x_a_mat_impl_option_x_x_x_a_iarray_iarray_nat_prod_nat_prod_option
            xa
      of NONE => rep_mat_impl (raise Fail "undefined") | SOME x2 => x2);

fun dis1 xa =
  (case rep_x_a_mat_impl_option_x_x_x_a_iarray_iarray_nat_prod_nat_prod_option
          xa
    of NONE => true | SOME _ => false);

fun rep_isom x = (if dis1 x then NONE else SOME (sel21 x));

fun mat_of_rows_list_impl_aux xb xc =
  Abs_x_a_mat_impl_option_x_x_x_a_iarray_iarray_nat_prod_nat_prod_option
    (if list_all (fn r => equal_nata (size_list r) xb) xc
      then SOME (size_list xc, (xb, Vector.fromList (map Vector.fromList xc)))
      else NONE);

fun mat_of_rows_list_impl x1 x2 = rep_isom (mat_of_rows_list_impl_aux x1 x2);

datatype 'a mat = Mat_impl of 'a mat_impl;

datatype 'a vec_impl = Abs_vec_impl of (nat * 'a Vector.vector);

fun rep_vec_impl (Abs_vec_impl x) = x;

fun sub asa n = Vector.sub (asa, integer_of_nat n);

fun vec_index_impl xa = let
                          val (_, a) = rep_vec_impl xa;
                        in
                          sub a
                        end;

datatype 'a vec = Vec_impl of 'a vec_impl;

fun vec_index (Vec_impl v) i = vec_index_impl v i;

fun of_fun f n = Vector.tabulate (integer_of_nat n, f o nat_of_integer);

fun mat_of_fun xc xd xe =
  Abs_mat_impl (xc, (xd, of_fun (fn i => of_fun (fn j => xe (i, j)) xd) xc));

fun mat nr nc f = Mat_impl (mat_of_fun nr nc f);

fun mat_of_rows n rs =
  mat (size_list rs) n (fn (i, a) => vec_index (nth rs i) a);

fun vec_of_fun xb xc = Abs_vec_impl (xb, of_fun xc xb);

fun vec n f = Vec_impl (vec_of_fun n f);

fun mat_of_rows_list nc vs =
  (case mat_of_rows_list_impl nc vs
    of NONE => mat_of_rows nc (map (fn v => vec nc (nth v)) vs)
    | SOME a => Mat_impl a);

fun berlekamp_mat_i A_ p ff_ops u =
  let
    val n = degree_i u;
    val ze = zeroa ff_ops;
    val on = onea ff_ops;
    val mul_p =
      power_poly_f_mod_i A_ ff_ops (fn v => mod_field_poly_i A_ ff_ops v u)
        [ze, on] (nat p);
    val xks = power_polys_i A_ ff_ops mul_p u [on] n;
  in
    mat_of_rows_list n
      (map (fn cs => cs @ replicate (minus_nata n (size_list cs)) ze) xks)
  end;

fun eliminate_entries_i2 A_ xc xe xg xh xi xj =
  Abs_mat_impl
    (let
       val (nr, (nc, a)) = rep_mat_impl xi;
     in
       (fn i =>
         (nr, (nc, let
                     val ai = Vector.sub (a, i);
                   in
                     Vector.tabulate
                       (integer_of_nat nr,
                         (fn ia =>
                           let
                             val aia = Vector.sub (a, ia);
                           in
                             (if ((ia : IntInf.int) = i) then aia
                               else let
                                      val vi_j = xh ia;
                                    in
                                      (if eq A_ vi_j xc then aia
else Vector.tabulate
       (integer_of_nat nc,
         (fn j => xe (Vector.sub (aia, j)) (xg vi_j (Vector.sub (ai, j))))))
                                    end)
                           end))
                   end)))
     end
      xj);

fun dim_row_impl xa = fst (rep_mat_impl xa);

fun eliminate_entries_gen_zero A_ mm tt z v (Mat_impl m) i j =
  (if less_nat i (dim_row_impl m)
    then Mat_impl (eliminate_entries_i2 A_ z mm tt v m (integer_of_nat i))
    else (raise Fail "index out of range in eliminate_entries")
           (fn _ => eliminate_entries_gen_zero A_ mm tt z v (Mat_impl m) i j));

fun eliminate_entries_i A_ ops =
  eliminate_entries_gen_zero A_ (minusa ops) (timesa ops) (zeroa ops);

fun list_update [] i y = []
  | list_update (x :: xs) i y =
    (if equal_nata i zero_nata then y :: xs
      else x :: list_update xs (minus_nata i one_nata) y);

fun length asa = nat_of_integer (Vector.length asa);

fun list_of asa = map (sub asa) (upt zero_nata (length asa));

fun mat_swaprows_impl xc xd xe =
  Abs_mat_impl
    let
      val (nr, (nc, a)) = rep_mat_impl xe;
    in
      (if less_nat xc nr andalso less_nat xd nr
        then let
               val ai = sub a xc;
               val aj = sub a xd;
               val arows = list_of a;
               val aa =
                 Vector.fromList (list_update (list_update arows xc aj) xd ai);
             in
               (nr, (nc, aa))
             end
        else (nr, (nc, a)))
    end;

fun mat_swaprows k l (Mat_impl a) =
  let
    val nr = dim_row_impl a;
  in
    (if less_nat l nr andalso less_nat k nr
      then Mat_impl (mat_swaprows_impl k l a)
      else (raise Fail "index out of bounds in mat_swaprows")
             (fn _ => mat_swaprows k l (Mat_impl a)))
  end;

fun mat_multrow_gen_impl xc xd xe xf =
  Abs_mat_impl let
                 val (nr, (nc, a)) = rep_mat_impl xf;
                 val ak = sub a xd;
                 val arows = list_of a;
                 val aka = Vector.fromList (map (xc xe) (list_of ak));
                 val aa = Vector.fromList (list_update arows xd aka);
               in
                 (nr, (nc, aa))
               end;

fun mat_multrow_gen mul k aa (Mat_impl a) =
  Mat_impl (mat_multrow_gen_impl mul k aa a);

fun multrow_i ops = mat_multrow_gen (timesa ops);

fun index_mat_impl xa =
  let
    val (nr, (_, m)) = rep_mat_impl xa;
  in
    (fn (i, j) =>
      (if less_nat i nr then sub (sub m i) j
        else sub (Vector.fromList (nth [] (minus_nata i nr))) j))
  end;

fun index_mat (Mat_impl m) ij = index_mat_impl m ij;

fun gauss_jordan_main_i A_ ops nr nc a i j =
  (if less_nat i nr andalso less_nat j nc
    then let
           val aij = index_mat a (i, j);
         in
           (if eq A_ aij (zeroa ops)
             then (case maps (fn ia =>
                               (if not (eq A_ (index_mat a (ia, j)) (zeroa ops))
                                 then [ia] else []))
                          (upt (suc i) nr)
                    of [] => gauss_jordan_main_i A_ ops nr nc a i (suc j)
                    | ia :: _ =>
                      gauss_jordan_main_i A_ ops nr nc (mat_swaprows i ia a) i
                        j)
             else (if eq A_ aij (onea ops)
                    then let
                           val v =
                             (fn ia => index_mat a (nat_of_integer ia, j));
                         in
                           gauss_jordan_main_i A_ ops nr nc
                             (eliminate_entries_i A_ ops v a i j) (suc i)
                             (suc j)
                         end
                    else let
                           val iaij = inversea ops aij;
                           val aa = multrow_i ops i iaij a;
                           val v =
                             (fn ia => index_mat aa (nat_of_integer ia, j));
                         in
                           gauss_jordan_main_i A_ ops nr nc
                             (eliminate_entries_i A_ ops v aa i j) (suc i)
                             (suc j)
                         end))
         end
    else a);

fun dim_row (Mat_impl m) = dim_row_impl m;

fun dim_col_impl xa = fst (snd (rep_mat_impl xa));

fun dim_col (Mat_impl m) = dim_col_impl m;

fun gauss_jordan_single_i A_ ops a =
  gauss_jordan_main_i A_ ops (dim_row a) (dim_col a) a zero_nata zero_nata;

fun transpose_mat a =
  mat (dim_col a) (dim_row a) (fn (i, j) => index_mat a (j, i));

fun berlekamp_resulting_mat_i A_ p ff_ops u =
  let
    val q = berlekamp_mat_i A_ p ff_ops u;
    val n = dim_row q;
    val qi =
      mat n n
        (fn (i, j) =>
          (if equal_nata i j
            then minusa ff_ops (index_mat q (i, j)) (onea ff_ops)
            else index_mat q (i, j)));
  in
    gauss_jordan_single_i A_ ff_ops (transpose_mat qi)
  end;

fun pivot_positions_main_gen A_ zero a nr nc i j =
  (if less_nat i nr
    then (if less_nat j nc
           then (if eq A_ (index_mat a (i, j)) zero
                  then pivot_positions_main_gen A_ zero a nr nc i (suc j)
                  else (i, j) ::
                         pivot_positions_main_gen A_ zero a nr nc (suc i)
                           (suc j))
           else [])
    else []);

fun pivot_positions_gen A_ zer a =
  pivot_positions_main_gen A_ zer a (dim_row a) (dim_col a) zero_nata zero_nata;

fun swap p = (snd p, fst p);

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

fun non_pivot_base_gen uminus zero one a pivots =
  let
    val _ = dim_row a;
    val nc = dim_col a;
    val invers = map_of equal_nat (map swap pivots);
  in
    (fn qj =>
      vec nc
        (fn i =>
          (if equal_nata i qj then one
            else (case invers i of NONE => zero
                   | SOME j => uminus (index_mat a (j, qj))))))
  end;

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun find_base_vectors_gen A_ uminus zero one a =
  let
    val pp = pivot_positions_gen A_ zero a;
    val b =
      filter (fn j => not (member equal_nat (map snd pp) j))
        (upt zero_nata (dim_col a));
  in
    map (non_pivot_base_gen uminus zero one a pp) b
  end;

fun find_base_vectors_i A_ ops a =
  find_base_vectors_gen A_ (uminusa ops) (zeroa ops) (onea ops) a;

fun list_of_vec_impl xa = let
                            val (_, a) = rep_vec_impl xa;
                          in
                            list_of a
                          end;

fun list_of_vec (Vec_impl v) = list_of_vec_impl v;

fun berlekamp_basis_i A_ p ff_ops u =
  map (poly_of_list_i A_ ff_ops o list_of_vec)
    (find_base_vectors_i A_ ff_ops (berlekamp_resulting_mat_i A_ p ff_ops u));

fun berlekamp_monic_factorization_i A_ p ff_ops d f =
  let
    val vs = berlekamp_basis_i A_ p ff_ops f;
  in
    berlekamp_factorization_main_i A_ p ff_ops (zeroa ff_ops) (onea ff_ops) d
      [f] vs (size_list vs)
  end;

fun finite_field_factorization_i A_ p ff_ops f =
  (if equal_nata (degree_i f) zero_nata then (lead_coeff_i ff_ops f, [])
    else let
           val a = lead_coeff_i ff_ops f;
           val u = smult_i A_ ff_ops (inversea ff_ops a) f;
           val gs =
             (if false then distinct_degree_factorization_i A_ p ff_ops u
               else [(one_nata, u)]);
           val (irr, hs) =
             partition (fn (i, fa) => equal_nata (degree_i fa) i) gs;
         in
           (a, map snd irr @
                 maps (fn (aa, b) =>
                        berlekamp_monic_factorization_i A_ p ff_ops aa b)
                   hs)
         end);

fun to_int
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x13;

fun to_int_poly_i ops f =
  poly_of_list (comm_monoid_add_int, equal_int) (map (to_int ops) f);

fun of_int_poly_i ops f = map (of_intb ops) (coeffs zero_int f);

fun m m x = modulo_inta x m;

fun mp ma = map_poly zero_int (zero_int, equal_int) (m ma);

fun finite_field_factorization_main A_ p f_ops f =
  let
    val (c, fs) =
      finite_field_factorization_i A_ p f_ops (of_int_poly_i f_ops (mp p f));
  in
    (to_int f_ops c, map (to_int_poly_i f_ops) fs)
  end;

fun drop_bit_integer n k = Bit_Shifts.drop (integer_of_nat n) k;

fun mult_p_integer p x y = modulo_integer (IntInf.* (x, y)) p;

fun power_p_integer p x n =
  (if IntInf.<= (n, (0 : IntInf.int)) then (1 : IntInf.int)
    else let
           val reca =
             power_p_integer p (mult_p_integer p x x)
               (drop_bit_integer one_nata n);
         in
           (if (((IntInf.andb (n,
                   (1 : IntInf.int))) : IntInf.int) = (0 : IntInf.int))
             then reca else mult_p_integer p reca x)
         end);

fun inverse_p_integer p x =
  (if ((x : IntInf.int) = (0 : IntInf.int)) then (0 : IntInf.int)
    else power_p_integer p x (IntInf.- (p, (2 : IntInf.int))));

fun uminus_p_integer p x =
  (if ((x : IntInf.int) = (0 : IntInf.int)) then (0 : IntInf.int)
    else IntInf.- (p, x));

fun divide_p_integer p x y = mult_p_integer p x (inverse_p_integer p y);

fun minus_p_integer p x y =
  (if IntInf.<= (y, x) then IntInf.- (x, y) else IntInf.- (IntInf.+ (x, p), y));

fun plus_p_integer p x y = let
                             val z = IntInf.+ (x, y);
                           in
                             (if IntInf.<= (p, z) then IntInf.- (z, p) else z)
                           end;

fun finite_field_ops_integer p =
  Arith_Ops_Record
    ((0 : IntInf.int), (1 : IntInf.int), plus_p_integer p, mult_p_integer p,
      minus_p_integer p, uminus_p_integer p, divide_p_integer p,
      inverse_p_integer p,
      (fn x => fn y =>
        (if ((y : IntInf.int) = (0 : IntInf.int)) then x
          else (0 : IntInf.int))),
      (fn x =>
        (if ((x : IntInf.int) = (0 : IntInf.int)) then (0 : IntInf.int)
          else (1 : IntInf.int))),
      (fn x => x), integer_of_int, Int_of_integer,
      (fn x => IntInf.<= ((0 : IntInf.int), x) andalso IntInf.< (x, p)));

fun modulo_uint64 x y =
  (if ((y : Uint64.uint64) = Uint64.zero) then x else Uint64.modulus x y);

fun mult_p64 p x y = modulo_uint64 (Uint64.times x y) p;

fun power_p64 p x n =
  (if ((n : Uint64.uint64) = Uint64.zero) then Uint64.one
    else let
           val reca =
             power_p64 p (mult_p64 p x x) (Uint64.shiftr n (1 : IntInf.int));
         in
           (if (((Uint64.andb n Uint64.one) : Uint64.uint64) = Uint64.zero)
             then reca else mult_p64 p reca x)
         end);

fun inverse_p64 p x =
  (if ((x : Uint64.uint64) = Uint64.zero) then Uint64.zero
    else power_p64 p x (Uint64.minus p (Uint64.fromInt (2 : IntInf.int))));

fun uminus_p64 p x =
  (if ((x : Uint64.uint64) = Uint64.zero) then Uint64.zero
    else Uint64.minus p x);

fun divide_p64 p x y = mult_p64 p x (inverse_p64 p y);

fun minus_p64 p x y =
  (if Uint64.less_eq y x then Uint64.minus x y
    else Uint64.minus (Uint64.plus x p) y);

fun plus_p64 p x y = let
                       val z = Uint64.plus x y;
                     in
                       (if Uint64.less_eq p z then Uint64.minus z p else z)
                     end;

fun uint64_of_int i = Uint64.fromInt (integer_of_int i);

fun int_of_uint64 x = Int_of_integer (Uint64.toInt x);

fun finite_field_ops64 p =
  Arith_Ops_Record
    (Uint64.zero, Uint64.one, plus_p64 p, mult_p64 p, minus_p64 p, uminus_p64 p,
      divide_p64 p, inverse_p64 p,
      (fn x => fn y =>
        (if ((y : Uint64.uint64) = Uint64.zero) then x else Uint64.zero)),
      (fn x =>
        (if ((x : Uint64.uint64) = Uint64.zero) then Uint64.zero
          else Uint64.one)),
      (fn x => x), uint64_of_int, int_of_uint64,
      (fn x => Uint64.less_eq Uint64.zero x andalso Uint64.less x p));

fun modulo_uint32 x y =
  (if ((y : Word32.word) = (Word32.fromInt 0)) then x else Word32.mod (x, y));

fun mult_p32 p x y = modulo_uint32 (Word32.* (x, y)) p;

fun power_p32 p x n =
  (if ((n : Word32.word) = (Word32.fromInt 0)) then (Word32.fromInt 1)
    else let
           val reca =
             power_p32 p (mult_p32 p x x) (Uint32.shiftr n (1 : IntInf.int));
         in
           (if (((Word32.andb (n,
                   (Word32.fromInt 1))) : Word32.word) = (Word32.fromInt 0))
             then reca else mult_p32 p reca x)
         end);

fun inverse_p32 p x =
  (if ((x : Word32.word) = (Word32.fromInt 0)) then (Word32.fromInt 0)
    else power_p32 p x
           (Word32.- (p, Word32.fromLargeInt (IntInf.toLarge (2 : IntInf.int)))));

fun uminus_p32 p x =
  (if ((x : Word32.word) = (Word32.fromInt 0)) then (Word32.fromInt 0)
    else Word32.- (p, x));

fun divide_p32 p x y = mult_p32 p x (inverse_p32 p y);

fun minus_p32 p x y =
  (if Word32.<= (y, x) then Word32.- (x, y) else Word32.- (Word32.+ (x, p), y));

fun plus_p32 p x y = let
                       val z = Word32.+ (x, y);
                     in
                       (if Word32.<= (p, z) then Word32.- (z, p) else z)
                     end;

fun uint32_of_int i = Word32.fromLargeInt (IntInf.toLarge (integer_of_int i));

fun int_of_uint32 x =
  Int_of_integer (IntInf.fromLarge (Word32.toLargeInt x) : IntInf.int);

fun finite_field_ops32 p =
  Arith_Ops_Record
    ((Word32.fromInt 0), (Word32.fromInt 1), plus_p32 p, mult_p32 p,
      minus_p32 p, uminus_p32 p, divide_p32 p, inverse_p32 p,
      (fn x => fn y =>
        (if ((y : Word32.word) = (Word32.fromInt 0)) then x
          else (Word32.fromInt 0))),
      (fn x =>
        (if ((x : Word32.word) = (Word32.fromInt 0)) then (Word32.fromInt 0)
          else (Word32.fromInt 1))),
      (fn x => x), uint32_of_int, int_of_uint32,
      (fn x => Word32.<= ((Word32.fromInt 0), x) andalso Word32.< (x, p)));

val equal_integer = {equal = (fn a => fn b => ((a : IntInf.int) = b))} :
  IntInf.int equal;

val equal_uint64 = {equal = (fn a => fn b => ((a : Uint64.uint64) = b))} :
  Uint64.uint64 equal;

val equal_uint32 = {equal = (fn a => fn b => ((a : Word32.word) = b))} :
  Word32.word equal;

fun finite_field_factorization_int p =
  (if less_eq_int p (Int_of_integer (65535 : IntInf.int))
    then finite_field_factorization_main equal_uint32 p
           (finite_field_ops32 (uint32_of_int p))
    else (if less_eq_int p (Int_of_integer (4294967295 : IntInf.int))
           then finite_field_factorization_main equal_uint64 p
                  (finite_field_ops64 (uint64_of_int p))
           else finite_field_factorization_main equal_integer p
                  (finite_field_ops_integer (integer_of_int p))));

datatype ('a, 'b, 'c) subseqs_foldr_impl =
  Sublists_Foldr_Impl of
    ('b -> 'a list -> nat -> 'b list * 'c) * ('c -> 'b list * 'c);

fun subseqs_foldr (Sublists_Foldr_Impl (x1, x2)) = x1;

fun next_subseqs_foldr (Sublists_Foldr_Impl (x1, x2)) = x2;

fun divide_poly_main_list (A1_, A2_) lc q r d n =
  (if equal_nata n zero_nata then q
    else let
           val cr = hd r;
         in
           (if eq A1_ cr
                 (zero ((zero_mult_zero o mult_zero_semiring_0 o
                          semiring_0_semiring_1 o semiring_1_comm_semiring_1 o
                          comm_semiring_1_comm_semiring_1_cancel o
                          comm_semiring_1_cancel_semidom o semidom_idom o
                          idom_idom_divide)
                         A2_))
             then divide_poly_main_list (A1_, A2_) lc
                    (cCons
                      ((zero_mult_zero o mult_zero_semiring_0 o
                         semiring_0_semiring_1 o semiring_1_comm_semiring_1 o
                         comm_semiring_1_comm_semiring_1_cancel o
                         comm_semiring_1_cancel_semidom o semidom_idom o
                         idom_idom_divide)
                         A2_,
                        A1_)
                      cr q)
                    (tl r) d (minus_nata n one_nata)
             else let
                    val a =
                      divide
                        ((divide_divide_trivial o
                           divide_trivial_semidom_divide o
                           semidom_divide_idom_divide)
                          A2_)
                        cr lc;
                    val qq =
                      cCons ((zero_mult_zero o mult_zero_semiring_0 o
                               semiring_0_semiring_1 o
                               semiring_1_comm_semiring_1 o
                               comm_semiring_1_comm_semiring_1_cancel o
                               comm_semiring_1_cancel_semidom o semidom_idom o
                               idom_idom_divide)
                               A2_,
                              A1_)
                        a q;
                    val rr =
                      minus_poly_rev_list
                        ((group_add_neg_numeral o neg_numeral_ring_1 o
                           ring_1_comm_ring_1 o comm_ring_1_idom o
                           idom_idom_divide)
                          A2_)
                        r (map (times
                                 ((times_dvd o dvd_comm_monoid_mult o
                                    comm_monoid_mult_comm_semiring_1 o
                                    comm_semiring_1_comm_semiring_1_cancel o
                                    comm_semiring_1_cancel_semidom o
                                    semidom_idom o idom_idom_divide)
                                   A2_)
                                 a)
                            d);
                  in
                    (if eq A1_ (hd rr)
                          (zero ((zero_mult_zero o mult_zero_semiring_0 o
                                   semiring_0_semiring_1 o
                                   semiring_1_comm_semiring_1 o
                                   comm_semiring_1_comm_semiring_1_cancel o
                                   comm_semiring_1_cancel_semidom o
                                   semidom_idom o idom_idom_divide)
                                  A2_))
                      then divide_poly_main_list (A1_, A2_) lc qq (tl rr) d
                             (minus_nata n one_nata)
                      else [])
                  end)
         end);

fun divide_poly_list (A1_, A2_) f g =
  let
    val cg =
      coeffs
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide)
          A2_)
        g;
  in
    (if null cg then g
      else let
             val cf =
               coeffs
                 ((zero_mult_zero o mult_zero_semiring_0 o
                    semiring_0_semiring_1 o semiring_1_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_semidom o semidom_idom o
                    idom_idom_divide)
                   A2_)
                 f;
             val cgr = rev cg;
           in
             poly_of_list
               ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
                  semiring_1_comm_semiring_1 o
                  comm_semiring_1_comm_semiring_1_cancel o
                  comm_semiring_1_cancel_semidom o semidom_idom o
                  idom_idom_divide)
                  A2_,
                 A1_)
               (divide_poly_main_list (A1_, A2_) (hd cgr) [] (rev cf) cgr
                 (minus_nata (plus_nata one_nata (size_list cf))
                   (size_list cg)))
           end)
  end;

fun divide_polya (A1_, A2_) f g = divide_poly_list (A1_, A2_) f g;

fun plus_coeffs (A1_, A2_) xs [] = xs
  | plus_coeffs (A1_, A2_) [] (v :: va) = v :: va
  | plus_coeffs (A1_, A2_) (x :: xs) (y :: ys) =
    cCons ((zero_monoid_add o monoid_add_comm_monoid_add) A1_, A2_)
      (plus ((plus_semigroup_add o semigroup_add_monoid_add o
               monoid_add_comm_monoid_add)
              A1_)
        x y)
      (plus_coeffs (A1_, A2_) xs ys);

fun plus_polya (A1_, A2_) p q =
  Poly (plus_coeffs (A1_, A2_)
         (coeffs ((zero_monoid_add o monoid_add_comm_monoid_add) A1_) p)
         (coeffs ((zero_monoid_add o monoid_add_comm_monoid_add) A1_) q));

fun minus_polya (A1_, A2_) p q =
  plus_polya
    ((comm_monoid_add_cancel_comm_monoid_add o
       cancel_comm_monoid_add_ab_group_add)
       A1_,
      A2_)
    p (uminus_polya A1_ q);

fun coeffs_minus A_ (x :: xs) (y :: ys) =
  minus ((minus_group_add o group_add_ab_group_add) A_) x y ::
    coeffs_minus A_ xs ys
  | coeffs_minus A_ xs [] = xs
  | coeffs_minus A_ [] (v :: va) =
    map (uminus ((uminus_group_add o group_add_ab_group_add) A_)) (v :: va);

fun monom_mult A_ n f =
  Poly let
         val xs =
           coeffs
             ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
                semiring_1_comm_semiring_1)
               A_)
             f;
       in
         (if null xs then xs
           else replicate n
                  (zero ((zero_mult_zero o mult_zero_semiring_0 o
                           semiring_0_semiring_1 o semiring_1_comm_semiring_1)
                          A_)) @
                  xs)
       end;

fun smult (A1_, A2_, A3_) a p =
  Poly (if eq A1_ a
             (zero ((zero_mult_zero o mult_zero_semiring_0 o
                      semiring_0_comm_semiring_0)
                     A2_))
         then []
         else map (times
                    ((times_mult_zero o mult_zero_semiring_0 o
                       semiring_0_comm_semiring_0)
                      A2_)
                    a)
                (coeffs
                  ((zero_mult_zero o mult_zero_semiring_0 o
                     semiring_0_comm_semiring_0)
                    A2_)
                  p));

fun karatsuba_main (A1_, A2_, A3_) f n g m =
  (if less_eq_nat n karatsuba_lower_bound orelse
        less_eq_nat m karatsuba_lower_bound
    then let
           val ff =
             poly_of_list
               ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
                  semiring_1_comm_semiring_1 o
                  comm_semiring_1_comm_semiring_1_cancel o
                  comm_semiring_1_cancel_comm_ring_1)
                  A2_,
                 A1_)
               f;
         in
           foldr (fn a => fn p =>
                   plus_polya
                     ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
                        semiring_1_comm_semiring_1 o
                        comm_semiring_1_comm_semiring_1_cancel o
                        comm_semiring_1_cancel_comm_ring_1)
                        A2_,
                       A1_)
                     (smult
                       (A1_, (comm_semiring_0_comm_semiring_1 o
                               comm_semiring_1_comm_semiring_1_cancel o
                               comm_semiring_1_cancel_comm_ring_1)
                               A2_,
                         A3_)
                       a ff)
                     (pCons
                       ((zero_mult_zero o mult_zero_semiring_0 o
                          semiring_0_semiring_1 o semiring_1_comm_semiring_1 o
                          comm_semiring_1_comm_semiring_1_cancel o
                          comm_semiring_1_cancel_comm_ring_1)
                          A2_,
                         A1_)
                       (zero ((zero_mult_zero o mult_zero_semiring_0 o
                                semiring_0_semiring_1 o
                                semiring_1_comm_semiring_1 o
                                comm_semiring_1_comm_semiring_1_cancel o
                                comm_semiring_1_cancel_comm_ring_1)
                               A2_))
                       p))
             g (zero_polya
                 ((zero_mult_zero o mult_zero_semiring_0 o
                    semiring_0_semiring_1 o semiring_1_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_comm_ring_1)
                   A2_))
         end
    else let
           val n2 = divide_nata n (nat_of_integer (2 : IntInf.int));
         in
           (if less_nat n2 m
             then let
                    val (f0, f1) = split_at n2 f;
                    val (g0, g1) = split_at n2 g;
                    val p1 =
                      karatsuba_main (A1_, A2_, A3_) f1 (minus_nata n n2) g1
                        (minus_nata m n2);
                    val p2 =
                      karatsuba_main (A1_, A2_, A3_)
                        (coeffs_minus
                          ((ab_group_add_ring o ring_ring_1 o
                             ring_1_comm_ring_1)
                            A2_)
                          f1 f0)
                        n2 (coeffs_minus
                             ((ab_group_add_ring o ring_ring_1 o
                                ring_1_comm_ring_1)
                               A2_)
                             g1 g0)
                        n2;
                    val p3 = karatsuba_main (A1_, A2_, A3_) f0 n2 g0 n2;
                  in
                    plus_polya
                      ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
                         semiring_1_comm_semiring_1 o
                         comm_semiring_1_comm_semiring_1_cancel o
                         comm_semiring_1_cancel_comm_ring_1)
                         A2_,
                        A1_)
                      (monom_mult
                        ((comm_semiring_1_comm_semiring_1_cancel o
                           comm_semiring_1_cancel_comm_ring_1)
                          A2_)
                        (plus_nata n2 n2) p1)
                      (plus_polya
                        ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
                           semiring_1_comm_semiring_1 o
                           comm_semiring_1_comm_semiring_1_cancel o
                           comm_semiring_1_cancel_comm_ring_1)
                           A2_,
                          A1_)
                        (monom_mult
                          ((comm_semiring_1_comm_semiring_1_cancel o
                             comm_semiring_1_cancel_comm_ring_1)
                            A2_)
                          n2 (plus_polya
                               ((comm_monoid_add_semiring_0 o
                                  semiring_0_semiring_1 o
                                  semiring_1_comm_semiring_1 o
                                  comm_semiring_1_comm_semiring_1_cancel o
                                  comm_semiring_1_cancel_comm_ring_1)
                                  A2_,
                                 A1_)
                               (minus_polya
                                 ((ab_group_add_ring o ring_ring_1 o
                                    ring_1_comm_ring_1)
                                    A2_,
                                   A1_)
                                 p1 p2)
                               p3))
                        p3)
                  end
             else let
                    val (f0, f1) = split_at n2 f;
                    val p1 =
                      karatsuba_main (A1_, A2_, A3_) f1 (minus_nata n n2) g m;
                    val a = karatsuba_main (A1_, A2_, A3_) f0 n2 g m;
                  in
                    plus_polya
                      ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
                         semiring_1_comm_semiring_1 o
                         comm_semiring_1_comm_semiring_1_cancel o
                         comm_semiring_1_cancel_comm_ring_1)
                         A2_,
                        A1_)
                      (monom_mult
                        ((comm_semiring_1_comm_semiring_1_cancel o
                           comm_semiring_1_cancel_comm_ring_1)
                          A2_)
                        n2 p1)
                      a
                  end)
         end);

fun karatsuba_mult_poly (A1_, A2_, A3_) f g =
  let
    val ff =
      coeffs
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_comm_ring_1)
          A2_)
        f;
    val gg =
      coeffs
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_comm_ring_1)
          A2_)
        g;
    val n = size_list ff;
    val m = size_list gg;
  in
    (if less_eq_nat n karatsuba_lower_bound orelse
          less_eq_nat m karatsuba_lower_bound
      then (if less_eq_nat n m
             then foldr (fn a => fn p =>
                          plus_polya
                            ((comm_monoid_add_semiring_0 o
                               semiring_0_semiring_1 o
                               semiring_1_comm_semiring_1 o
                               comm_semiring_1_comm_semiring_1_cancel o
                               comm_semiring_1_cancel_comm_ring_1)
                               A2_,
                              A1_)
                            (smult
                              (A1_, (comm_semiring_0_comm_semiring_1 o
                                      comm_semiring_1_comm_semiring_1_cancel o
                                      comm_semiring_1_cancel_comm_ring_1)
                                      A2_,
                                A3_)
                              a g)
                            (pCons
                              ((zero_mult_zero o mult_zero_semiring_0 o
                                 semiring_0_semiring_1 o
                                 semiring_1_comm_semiring_1 o
                                 comm_semiring_1_comm_semiring_1_cancel o
                                 comm_semiring_1_cancel_comm_ring_1)
                                 A2_,
                                A1_)
                              (zero ((zero_mult_zero o mult_zero_semiring_0 o
                                       semiring_0_semiring_1 o
                                       semiring_1_comm_semiring_1 o
                                       comm_semiring_1_comm_semiring_1_cancel o
                                       comm_semiring_1_cancel_comm_ring_1)
                                      A2_))
                              p))
                    ff (zero_polya
                         ((zero_mult_zero o mult_zero_semiring_0 o
                            semiring_0_semiring_1 o semiring_1_comm_semiring_1 o
                            comm_semiring_1_comm_semiring_1_cancel o
                            comm_semiring_1_cancel_comm_ring_1)
                           A2_))
             else foldr (fn a => fn p =>
                          plus_polya
                            ((comm_monoid_add_semiring_0 o
                               semiring_0_semiring_1 o
                               semiring_1_comm_semiring_1 o
                               comm_semiring_1_comm_semiring_1_cancel o
                               comm_semiring_1_cancel_comm_ring_1)
                               A2_,
                              A1_)
                            (smult
                              (A1_, (comm_semiring_0_comm_semiring_1 o
                                      comm_semiring_1_comm_semiring_1_cancel o
                                      comm_semiring_1_cancel_comm_ring_1)
                                      A2_,
                                A3_)
                              a f)
                            (pCons
                              ((zero_mult_zero o mult_zero_semiring_0 o
                                 semiring_0_semiring_1 o
                                 semiring_1_comm_semiring_1 o
                                 comm_semiring_1_comm_semiring_1_cancel o
                                 comm_semiring_1_cancel_comm_ring_1)
                                 A2_,
                                A1_)
                              (zero ((zero_mult_zero o mult_zero_semiring_0 o
                                       semiring_0_semiring_1 o
                                       semiring_1_comm_semiring_1 o
                                       comm_semiring_1_comm_semiring_1_cancel o
                                       comm_semiring_1_cancel_comm_ring_1)
                                      A2_))
                              p))
                    gg (zero_polya
                         ((zero_mult_zero o mult_zero_semiring_0 o
                            semiring_0_semiring_1 o semiring_1_comm_semiring_1 o
                            comm_semiring_1_comm_semiring_1_cancel o
                            comm_semiring_1_cancel_comm_ring_1)
                           A2_)))
      else (if less_eq_nat n m then karatsuba_main (A1_, A2_, A3_) gg m ff n
             else karatsuba_main (A1_, A2_, A3_) ff n gg m))
  end;

fun one_polya A_ =
  Poly [one ((one_numeral o numeral_semiring_numeral o
               semiring_numeral_semiring_1 o semiring_1_comm_semiring_1)
              A_)];

fun prod_list_m m [] = one_polya comm_semiring_1_int
  | prod_list_m m (f :: fs) =
    mp m (karatsuba_mult_poly
           (equal_int, comm_ring_1_int, semiring_no_zero_divisors_int) f
           (prod_list_m m fs));

fun inv_M2 m m2 = (fn x => (if less_eq_int x m2 then x else minus_inta x m));

fun primitive_part (A1_, A2_) p =
  map_poly ((zero_gcd o gcd_comm_monoid_gcd o comm_monoid_gcd_semiring_gcd) A1_)
    ((zero_gcd o gcd_comm_monoid_gcd o comm_monoid_gcd_semiring_gcd) A1_, A2_)
    (fn x =>
      divide
        ((divide_divide_trivial o divide_trivial_semidom_divide o
           semidom_divide_algebraic_semidom o
           algebraic_semidom_normalization_semidom o
           normalization_semidom_semiring_gcd)
          A1_)
        x (content A1_ p))
    p;

fun divmod_int m n =
  map_prod Int_of_integer Int_of_integer
    (divmod_integer (integer_of_int m) (integer_of_int n));

fun div_mod_int_poly p q =
  (if equal_polya (zero_int, equal_int) q (zero_polya zero_int) then NONE
    else let
           val n = degree zero_int q;
           val _ = coeff zero_int q n;
         in
           fold_coeffs zero_int
             (fn a => fn b =>
               (case b of NONE => NONE
                 | SOME (s, r) =>
                   let
                     val ar = pCons (zero_int, equal_int) a r;
                     val (ba, m) =
                       divmod_int (coeff zero_int ar (degree zero_int q))
                         (coeff zero_int q (degree zero_int q));
                   in
                     (if equal_inta m zero_inta
                       then SOME (pCons (zero_int, equal_int) ba s,
                                   minus_polya (ab_group_add_int, equal_int) ar
                                     (smult
                                       (equal_int, comm_semiring_0_int,
 semiring_no_zero_divisors_int)
                                       ba q))
                       else NONE)
                   end))
             p (SOME (zero_polya zero_int, zero_polya zero_int))
         end);

fun div_int_poly p q =
  (case div_mod_int_poly p q of NONE => NONE
    | SOME (d, m) =>
      (if equal_polya (zero_int, equal_int) m (zero_polya zero_int) then SOME d
        else NONE));

fun is_none (SOME x) = false
  | is_none NONE = true;

fun dvd_int_poly q p =
  (if equal_polya (zero_int, equal_int) q (zero_polya zero_int)
    then equal_polya (zero_int, equal_int) p (zero_polya zero_int)
    else not (is_none (div_int_poly p q)));

fun remove1 A_ x [] = []
  | remove1 A_ x (y :: xs) = (if eq A_ x y then xs else y :: remove1 A_ x xs);

fun equal_poly (A1_, A2_) = {equal = equal_polya (A1_, A2_)} : 'a poly equal;

fun reconstruction m sl_impl m2 state u luu lu d r vs res cands =
  (case cands
    of [] =>
      let
        val da = suc d;
      in
        (if less_nat r (plus_nata da da) then u :: res
          else let
                 val (candsa, statea) = next_subseqs_foldr sl_impl state;
               in
                 reconstruction m sl_impl m2 statea u luu lu da r vs res candsa
               end)
      end
    | (lv, ws) :: candsa =>
      let
        val lva = inv_M2 m m2 lv;
      in
        (if dvd (equal_int, semidom_modulo_int) lva
              (case coeffs zero_int luu of [] => zero_inta | x :: _ => x)
          then let
                 val vb =
                   map_poly zero_int (zero_int, equal_int) (inv_M2 m m2)
                     (mp m (smult
                             (equal_int, comm_semiring_0_int,
                               semiring_no_zero_divisors_int)
                             lu (prod_list_m m ws)));
               in
                 (if dvd_int_poly vb luu
                   then let
                          val pp_vb =
                            primitive_part (semiring_gcd_int, equal_int) vb;
                          val ua =
                            divide_polya (equal_int, idom_divide_int) u pp_vb;
                          val ra = minus_nata r (size_list ws);
                          val resa = pp_vb :: res;
                        in
                          (if less_nat ra (plus_nata d d) then ua :: resa
                            else let
                                   val lua =
                                     coeff zero_int ua (degree zero_int ua);
                                   val vsa =
                                     fold (remove1
    (equal_poly (zero_int, equal_int)))
                                       ws vs;
                                   val (candsb, statea) =
                                     subseqs_foldr sl_impl (lua, []) vsa d;
                                 in
                                   reconstruction m sl_impl m2 statea ua
                                     (smult
                                       (equal_int, comm_semiring_0_int,
 semiring_no_zero_divisors_int)
                                       lua ua)
                                     lua d ra vsa resa candsb
                                 end)
                        end
                   else reconstruction m sl_impl m2 state u luu lu d r vs res
                          candsa)
               end
          else reconstruction m sl_impl m2 state u luu lu d r vs res candsa)
      end);

fun zassenhaus_reconstruction_generic sl_impl vs p n f =
  let
    val lf = coeff zero_int f (degree zero_int f);
    val pn = binary_power monoid_mult_int p n;
    val (_, state) = subseqs_foldr sl_impl (lf, []) vs zero_nata;
  in
    reconstruction pn sl_impl (divide_inta pn (Int_of_integer (2 : IntInf.int)))
      state f
      (smult (equal_int, comm_semiring_0_int, semiring_no_zero_divisors_int) lf
        f)
      lf zero_nata (size_list vs) vs [] []
  end;

fun next_subseqs1 f head tail ret0 ret1 ((i, v) :: prevs) =
  next_subseqs2 f head tail (f head v :: ret0) ret1 prevs v (upt zero_nata i)
  | next_subseqs1 f head tail ret0 ret1 [] = (ret0, (head, (tail, ret1)))
and next_subseqs2 f head tail ret0 ret1 prevs v (j :: js) =
  let
    val va = f (sub tail j) v;
  in
    next_subseqs2 f head tail (va :: ret0) ((j, va) :: ret1) prevs v js
  end
  | next_subseqs2 f head tail ret0 ret1 prevs v [] =
    next_subseqs1 f head tail ret0 ret1 prevs;

fun next_subseqs f (head, (tail, prevs)) =
  next_subseqs1 f head tail [] [] prevs;

fun create_subseqs f base elements n =
  (if equal_nata n zero_nata
    then (if null elements
           then ([base], ((raise Fail "undefined"), (Vector.fromList [], [])))
           else let
                  val head = hd elements;
                  val tail = Vector.fromList (tl elements);
                in
                  ([base], (head, (tail, [(length tail, base)])))
                end)
    else next_subseqs f
           (snd (create_subseqs f base elements (minus_nata n one_nata))));

fun impl f = Sublists_Foldr_Impl (create_subseqs f, next_subseqs f);

fun mul_const m p c =
  modulo_inta
    (times_inta (case coeffs zero_int p of [] => zero_inta | x :: _ => x) c) m;

fun zassenhaus_reconstruction vs p n f =
  let
    val mul = mul_const (binary_power monoid_mult_int p n);
    val sl_impl = impl (fn x => map_prod (mul x) (fn a => x :: a));
  in
    zassenhaus_reconstruction_generic sl_impl vs p n f
  end;

fun find_exponent_main p pm m bnd =
  (if less_int bnd pm then m
    else find_exponent_main p (times_inta pm p) (suc m) bnd);

fun find_exponent p bnd = find_exponent_main p p one_nata bnd;

fun coprime (A1_, A2_) a b =
  eq A2_ (gcda ((gcd_comm_monoid_gcd o comm_monoid_gcd_semiring_gcd) A1_) a b)
    (one ((one_gcd o gcd_comm_monoid_gcd o comm_monoid_gcd_semiring_gcd) A1_));

fun coprimea (A1_, A2_) = coprime (A1_, A2_);

fun pderiv_main_i A_ ops f (x :: xs) =
  cCons_i A_ ops (timesa ops f x)
    (pderiv_main_i A_ ops (plusa ops f (onea ops)) xs)
  | pderiv_main_i A_ ops f [] = [];

fun pderiv_i A_ ops xs = pderiv_main_i A_ ops (onea ops) (tl xs);

fun separable_i A_ ops xs =
  equal_lista A_ (gcd_poly_i A_ ops xs (pderiv_i A_ ops xs)) [onea ops];

fun separable_impl_main A_ p ff_ops f =
  separable_i A_ ff_ops (of_int_poly_i ff_ops (mp p f));

fun separable_impl p =
  (if less_eq_int p (Int_of_integer (65535 : IntInf.int))
    then separable_impl_main equal_uint32 p
           (finite_field_ops32 (uint32_of_int p))
    else (if less_eq_int p (Int_of_integer (4294967295 : IntInf.int))
           then separable_impl_main equal_uint64 p
                  (finite_field_ops64 (uint64_of_int p))
           else separable_impl_main equal_integer p
                  (finite_field_ops_integer (integer_of_int p))));

val primes_1000 : nat list =
  [nat_of_integer (2 : IntInf.int), nat_of_integer (3 : IntInf.int),
    nat_of_integer (5 : IntInf.int), nat_of_integer (7 : IntInf.int),
    nat_of_integer (11 : IntInf.int), nat_of_integer (13 : IntInf.int),
    nat_of_integer (17 : IntInf.int), nat_of_integer (19 : IntInf.int),
    nat_of_integer (23 : IntInf.int), nat_of_integer (29 : IntInf.int),
    nat_of_integer (31 : IntInf.int), nat_of_integer (37 : IntInf.int),
    nat_of_integer (41 : IntInf.int), nat_of_integer (43 : IntInf.int),
    nat_of_integer (47 : IntInf.int), nat_of_integer (53 : IntInf.int),
    nat_of_integer (59 : IntInf.int), nat_of_integer (61 : IntInf.int),
    nat_of_integer (67 : IntInf.int), nat_of_integer (71 : IntInf.int),
    nat_of_integer (73 : IntInf.int), nat_of_integer (79 : IntInf.int),
    nat_of_integer (83 : IntInf.int), nat_of_integer (89 : IntInf.int),
    nat_of_integer (97 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (103 : IntInf.int), nat_of_integer (107 : IntInf.int),
    nat_of_integer (109 : IntInf.int), nat_of_integer (113 : IntInf.int),
    nat_of_integer (127 : IntInf.int), nat_of_integer (131 : IntInf.int),
    nat_of_integer (137 : IntInf.int), nat_of_integer (139 : IntInf.int),
    nat_of_integer (149 : IntInf.int), nat_of_integer (151 : IntInf.int),
    nat_of_integer (157 : IntInf.int), nat_of_integer (163 : IntInf.int),
    nat_of_integer (167 : IntInf.int), nat_of_integer (173 : IntInf.int),
    nat_of_integer (179 : IntInf.int), nat_of_integer (181 : IntInf.int),
    nat_of_integer (191 : IntInf.int), nat_of_integer (193 : IntInf.int),
    nat_of_integer (197 : IntInf.int), nat_of_integer (199 : IntInf.int),
    nat_of_integer (211 : IntInf.int), nat_of_integer (223 : IntInf.int),
    nat_of_integer (227 : IntInf.int), nat_of_integer (229 : IntInf.int),
    nat_of_integer (233 : IntInf.int), nat_of_integer (239 : IntInf.int),
    nat_of_integer (241 : IntInf.int), nat_of_integer (251 : IntInf.int),
    nat_of_integer (257 : IntInf.int), nat_of_integer (263 : IntInf.int),
    nat_of_integer (269 : IntInf.int), nat_of_integer (271 : IntInf.int),
    nat_of_integer (277 : IntInf.int), nat_of_integer (281 : IntInf.int),
    nat_of_integer (283 : IntInf.int), nat_of_integer (293 : IntInf.int),
    nat_of_integer (307 : IntInf.int), nat_of_integer (311 : IntInf.int),
    nat_of_integer (313 : IntInf.int), nat_of_integer (317 : IntInf.int),
    nat_of_integer (331 : IntInf.int), nat_of_integer (337 : IntInf.int),
    nat_of_integer (347 : IntInf.int), nat_of_integer (349 : IntInf.int),
    nat_of_integer (353 : IntInf.int), nat_of_integer (359 : IntInf.int),
    nat_of_integer (367 : IntInf.int), nat_of_integer (373 : IntInf.int),
    nat_of_integer (379 : IntInf.int), nat_of_integer (383 : IntInf.int),
    nat_of_integer (389 : IntInf.int), nat_of_integer (397 : IntInf.int),
    nat_of_integer (401 : IntInf.int), nat_of_integer (409 : IntInf.int),
    nat_of_integer (419 : IntInf.int), nat_of_integer (421 : IntInf.int),
    nat_of_integer (431 : IntInf.int), nat_of_integer (433 : IntInf.int),
    nat_of_integer (439 : IntInf.int), nat_of_integer (443 : IntInf.int),
    nat_of_integer (449 : IntInf.int), nat_of_integer (457 : IntInf.int),
    nat_of_integer (461 : IntInf.int), nat_of_integer (463 : IntInf.int),
    nat_of_integer (467 : IntInf.int), nat_of_integer (479 : IntInf.int),
    nat_of_integer (487 : IntInf.int), nat_of_integer (491 : IntInf.int),
    nat_of_integer (499 : IntInf.int), nat_of_integer (503 : IntInf.int),
    nat_of_integer (509 : IntInf.int), nat_of_integer (521 : IntInf.int),
    nat_of_integer (523 : IntInf.int), nat_of_integer (541 : IntInf.int),
    nat_of_integer (547 : IntInf.int), nat_of_integer (557 : IntInf.int),
    nat_of_integer (563 : IntInf.int), nat_of_integer (569 : IntInf.int),
    nat_of_integer (571 : IntInf.int), nat_of_integer (577 : IntInf.int),
    nat_of_integer (587 : IntInf.int), nat_of_integer (593 : IntInf.int),
    nat_of_integer (599 : IntInf.int), nat_of_integer (601 : IntInf.int),
    nat_of_integer (607 : IntInf.int), nat_of_integer (613 : IntInf.int),
    nat_of_integer (617 : IntInf.int), nat_of_integer (619 : IntInf.int),
    nat_of_integer (631 : IntInf.int), nat_of_integer (641 : IntInf.int),
    nat_of_integer (643 : IntInf.int), nat_of_integer (647 : IntInf.int),
    nat_of_integer (653 : IntInf.int), nat_of_integer (659 : IntInf.int),
    nat_of_integer (661 : IntInf.int), nat_of_integer (673 : IntInf.int),
    nat_of_integer (677 : IntInf.int), nat_of_integer (683 : IntInf.int),
    nat_of_integer (691 : IntInf.int), nat_of_integer (701 : IntInf.int),
    nat_of_integer (709 : IntInf.int), nat_of_integer (719 : IntInf.int),
    nat_of_integer (727 : IntInf.int), nat_of_integer (733 : IntInf.int),
    nat_of_integer (739 : IntInf.int), nat_of_integer (743 : IntInf.int),
    nat_of_integer (751 : IntInf.int), nat_of_integer (757 : IntInf.int),
    nat_of_integer (761 : IntInf.int), nat_of_integer (769 : IntInf.int),
    nat_of_integer (773 : IntInf.int), nat_of_integer (787 : IntInf.int),
    nat_of_integer (797 : IntInf.int), nat_of_integer (809 : IntInf.int),
    nat_of_integer (811 : IntInf.int), nat_of_integer (821 : IntInf.int),
    nat_of_integer (823 : IntInf.int), nat_of_integer (827 : IntInf.int),
    nat_of_integer (829 : IntInf.int), nat_of_integer (839 : IntInf.int),
    nat_of_integer (853 : IntInf.int), nat_of_integer (857 : IntInf.int),
    nat_of_integer (859 : IntInf.int), nat_of_integer (863 : IntInf.int),
    nat_of_integer (877 : IntInf.int), nat_of_integer (881 : IntInf.int),
    nat_of_integer (883 : IntInf.int), nat_of_integer (887 : IntInf.int),
    nat_of_integer (907 : IntInf.int), nat_of_integer (911 : IntInf.int),
    nat_of_integer (919 : IntInf.int), nat_of_integer (929 : IntInf.int),
    nat_of_integer (937 : IntInf.int), nat_of_integer (941 : IntInf.int),
    nat_of_integer (947 : IntInf.int), nat_of_integer (953 : IntInf.int),
    nat_of_integer (967 : IntInf.int), nat_of_integer (971 : IntInf.int),
    nat_of_integer (977 : IntInf.int), nat_of_integer (983 : IntInf.int),
    nat_of_integer (991 : IntInf.int), nat_of_integer (997 : IntInf.int)];

fun next_candidates n =
  (if equal_nata n zero_nata
    then (nat_of_integer (1001 : IntInf.int), primes_1000)
    else (plus_nata n (nat_of_integer (30 : IntInf.int)),
           [n, plus_nata n (nat_of_integer (2 : IntInf.int)),
             plus_nata n (nat_of_integer (6 : IntInf.int)),
             plus_nata n (nat_of_integer (8 : IntInf.int)),
             plus_nata n (nat_of_integer (12 : IntInf.int)),
             plus_nata n (nat_of_integer (18 : IntInf.int)),
             plus_nata n (nat_of_integer (20 : IntInf.int)),
             plus_nata n (nat_of_integer (26 : IntInf.int))]));

fun all_interval_nat p i j =
  less_eq_nat j i orelse p i andalso all_interval_nat p (suc i) j;

fun prime_nat p =
  less_nat one_nata p andalso
    all_interval_nat (fn n => not (dvd (equal_nat, semidom_modulo_nat) n p))
      (suc one_nata) p;

fun next_primes n =
  (if equal_nata n zero_nata then next_candidates zero_nata
    else let
           val (m, ps) = next_candidates n;
         in
           (m, filter prime_nat ps)
         end);

fun find_prime_main f np ps =
  (case ps of [] => let
                      val (a, b) = next_primes np;
                    in
                      find_prime_main f a b
                    end
    | p :: psa => (if f p then p else find_prime_main f np psa));

fun find_prime f = find_prime_main f zero_nata [];

fun suitable_prime_bz f =
  let
    val lc = coeff zero_int f (degree zero_int f);
  in
    int_of_nat
      (find_prime
        (fn n =>
          let
            val p = int_of_nat n;
          in
            coprimea (semiring_gcd_int, equal_int) lc p andalso
              separable_impl p f
          end))
  end;

datatype 'a factor_tree = Factor_Leaf of 'a * int poly |
  Factor_Node of 'a * 'a factor_tree * 'a factor_tree;

fun factor_node_info (Factor_Leaf (i, x)) = i
  | factor_node_info (Factor_Node (i, l, r)) = i;

fun product_factor_tree p (Factor_Leaf (i, x)) = Factor_Leaf (x, x)
  | product_factor_tree p (Factor_Node (i, l, r)) =
    let
      val la = product_factor_tree p l;
      val ra = product_factor_tree p r;
      val f = factor_node_info la;
      val g = factor_node_info ra;
      val fg =
        mp p (karatsuba_mult_poly
               (equal_int, comm_ring_1_int, semiring_no_zero_divisors_int) f g);
    in
      Factor_Node (fg, la, ra)
    end;

fun dividea
  (Arith_Ops_Record
    (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14))
  = x7;

fun euclid_ext_aux_i A_ ops sa s ta t ra r =
  (if eq A_ r (zeroa ops)
    then let
           val c = dividea ops (onea ops) (unit_factora ops ra);
         in
           ((timesa ops sa c, timesa ops ta c), normalizeb ops ra)
         end
    else let
           val q = dividea ops ra r;
         in
           euclid_ext_aux_i A_ ops s (minusa ops sa (timesa ops q s)) t
             (minusa ops ta (timesa ops q t)) r (moduloa ops ra r)
         end);

fun euclid_ext_poly_i A_ ops =
  euclid_ext_aux_i (equal_list A_) (poly_ops A_ ops) (onea (poly_ops A_ ops))
    (zeroa (poly_ops A_ ops)) (zeroa (poly_ops A_ ops))
    (onea (poly_ops A_ ops));

fun bezout_coefficients_i A_ ff_ops f g = fst (euclid_ext_poly_i A_ ff_ops f g);

fun euclid_ext_poly_mod_main A_ p ff_ops f g =
  let
    val (a, b) =
      bezout_coefficients_i A_ ff_ops (of_int_poly_i ff_ops f)
        (of_int_poly_i ff_ops g);
  in
    (to_int_poly_i ff_ops a, to_int_poly_i ff_ops b)
  end;

fun euclid_ext_poly_dynamic p =
  (if less_eq_int p (Int_of_integer (65535 : IntInf.int))
    then euclid_ext_poly_mod_main equal_uint32 p
           (finite_field_ops32 (uint32_of_int p))
    else (if less_eq_int p (Int_of_integer (4294967295 : IntInf.int))
           then euclid_ext_poly_mod_main equal_uint64 p
                  (finite_field_ops64 (uint64_of_int p))
           else euclid_ext_poly_mod_main equal_integer p
                  (finite_field_ops_integer (integer_of_int p))));

fun pdivmod_monic_i A_ ops cf cg =
  let
    val (q, r) =
      divmod_poly_one_main_i A_ ops [] (rev cf) (rev cg)
        (minus_nata (plus_nata one_nata (size_list cf)) (size_list cg));
  in
    (poly_of_list_i A_ ops q, poly_of_list_i A_ ops (rev r))
  end;

fun dupe_monic_i A_ ops d h s t u =
  let
    val (q, a) = pdivmod_monic_i A_ ops (times_poly_i A_ ops t u) d;
  in
    (plus_poly_i A_ ops (times_poly_i A_ ops s u) (times_poly_i A_ ops h q), a)
  end;

fun dupe_monic_i_int A_ ops d h s t =
  let
    val da = of_int_poly_i ops d;
    val ha = of_int_poly_i ops h;
    val sa = of_int_poly_i ops s;
    val ta = of_int_poly_i ops t;
  in
    (fn u =>
      let
        val (db, hb) = dupe_monic_i A_ ops da ha sa ta (of_int_poly_i ops u);
      in
        (to_int_poly_i ops db, to_int_poly_i ops hb)
      end)
  end;

fun dupe_monic_dynamic p =
  (if less_eq_int p (Int_of_integer (65535 : IntInf.int))
    then dupe_monic_i_int equal_uint32 (finite_field_ops32 (uint32_of_int p))
    else (if less_eq_int p (Int_of_integer (4294967295 : IntInf.int))
           then dupe_monic_i_int equal_uint64
                  (finite_field_ops64 (uint64_of_int p))
           else dupe_monic_i_int equal_integer
                  (finite_field_ops_integer (integer_of_int p))));

fun simple_quadratic_hensel_step c q s t d h =
  let
    val u =
      mp q (sdiv_poly (equal_int, idom_divide_int)
             (minus_polya (ab_group_add_int, equal_int) c
               (karatsuba_mult_poly
                 (equal_int, comm_ring_1_int, semiring_no_zero_divisors_int) d
                 h))
             q);
    val (a, b) = dupe_monic_dynamic q d h s t u;
    val da =
      plus_polya (comm_monoid_add_int, equal_int) d
        (smult (equal_int, comm_semiring_0_int, semiring_no_zero_divisors_int) q
          b);
    val aa =
      plus_polya (comm_monoid_add_int, equal_int) h
        (smult (equal_int, comm_semiring_0_int, semiring_no_zero_divisors_int) q
          a);
  in
    (da, aa)
  end;

fun quadratic_hensel_step c q s t d h =
  let
    val dupe = dupe_monic_dynamic q d h s t;
    val u =
      mp q (sdiv_poly (equal_int, idom_divide_int)
             (minus_polya (ab_group_add_int, equal_int) c
               (karatsuba_mult_poly
                 (equal_int, comm_ring_1_int, semiring_no_zero_divisors_int) d
                 h))
             q);
    val (a, b) = dupe u;
    val da =
      plus_polya (comm_monoid_add_int, equal_int) d
        (smult (equal_int, comm_semiring_0_int, semiring_no_zero_divisors_int) q
          b);
    val ha =
      plus_polya (comm_monoid_add_int, equal_int) h
        (smult (equal_int, comm_semiring_0_int, semiring_no_zero_divisors_int) q
          a);
    val ua =
      mp q (sdiv_poly (equal_int, idom_divide_int)
             (minus_polya (ab_group_add_int, equal_int)
               (plus_polya (comm_monoid_add_int, equal_int)
                 (karatsuba_mult_poly
                   (equal_int, comm_ring_1_int, semiring_no_zero_divisors_int) s
                   da)
                 (karatsuba_mult_poly
                   (equal_int, comm_ring_1_int, semiring_no_zero_divisors_int) t
                   ha))
               (one_polya comm_semiring_1_int))
             q);
    val (aa, ba) = dupe ua;
    val qa = times_inta q q;
    val sa =
      mp qa (minus_polya (ab_group_add_int, equal_int) s
              (smult
                (equal_int, comm_semiring_0_int, semiring_no_zero_divisors_int)
                q aa));
    val ta =
      mp qa (minus_polya (ab_group_add_int, equal_int) t
              (smult
                (equal_int, comm_semiring_0_int, semiring_no_zero_divisors_int)
                q ba));
  in
    (sa, (ta, (da, ha)))
  end;

fun quadratic_hensel_loop c p s1 t1 d1 h1 j =
  (if less_eq_nat j one_nata then (p, (s1, (t1, (d1, h1))))
    else (if dvd (equal_nat, semidom_modulo_nat)
               (nat_of_integer (2 : IntInf.int)) j
           then let
                  val (q, (s, (t, (d, h)))) =
                    quadratic_hensel_loop c p s1 t1 d1 h1
                      (divide_nata j (nat_of_integer (2 : IntInf.int)));
                  val qq = times_inta q q;
                  val (sa, (ta, (da, ha))) = quadratic_hensel_step c q s t d h;
                in
                  (qq, (sa, (ta, (da, ha))))
                end
           else let
                  val (q, (s, (t, (d, h)))) =
                    quadratic_hensel_loop c p s1 t1 d1 h1
                      (plus_nata
                        (divide_nata j (nat_of_integer (2 : IntInf.int)))
                        one_nata);
                  val (sa, (ta, (da, ha))) = quadratic_hensel_step c q s t d h;
                  val qq = times_inta q q;
                  val pj = divide_inta qq p;
                  val down = mp pj;
                in
                  (pj, (down sa, (down ta, (down da, down ha))))
                end));

fun quadratic_hensel_main c p s1 t1 d1 h1 j =
  (if less_eq_nat j one_nata then (d1, h1)
    else (if dvd (equal_nat, semidom_modulo_nat)
               (nat_of_integer (2 : IntInf.int)) j
           then let
                  val (q, (s, (t, (a, b)))) =
                    quadratic_hensel_loop c p s1 t1 d1 h1
                      (divide_nata j (nat_of_integer (2 : IntInf.int)));
                in
                  simple_quadratic_hensel_step c q s t a b
                end
           else let
                  val (q, (s, (t, (d, h)))) =
                    quadratic_hensel_loop c p s1 t1 d1 h1
                      (plus_nata
                        (divide_nata j (nat_of_integer (2 : IntInf.int)))
                        one_nata);
                  val (da, ha) = simple_quadratic_hensel_step c q s t d h;
                  val down = mp (divide_inta (times_inta q q) p);
                in
                  (down da, down ha)
                end));

fun quadratic_hensel_binary p n c d h =
  let
    val (s, t) = euclid_ext_poly_dynamic p d h;
  in
    quadratic_hensel_main c p s t d h n
  end;

fun hensel_lifting_main p n u (Factor_Leaf (uu, uv)) = [u]
  | hensel_lifting_main p n u (Factor_Node (uw, l, r)) =
    let
      val v = factor_node_info l;
      val w = factor_node_info r;
      val (va, wa) = quadratic_hensel_binary p n u v w;
    in
      hensel_lifting_main p n va l @ hensel_lifting_main p n wa r
    end;

fun partition_factors_main s [] = ([], [])
  | partition_factors_main s ((f, d) :: xs) =
    (if less_eq_nat d s
      then let
             val (l, a) = partition_factors_main (minus_nata s d) xs;
           in
             ((f, d) :: l, a)
           end
      else let
             val (l, r) = partition_factors_main d xs;
           in
             (l, (f, d) :: r)
           end);

fun sum_list A_ xs =
  foldr (plus ((plus_semigroup_add o semigroup_add_monoid_add) A_)) xs
    (zero (zero_monoid_add A_));

fun partition_factors xs =
  let
    val n =
      divide_nata (sum_list monoid_add_nat (map snd xs))
        (nat_of_integer (2 : IntInf.int));
  in
    (case partition_factors_main n xs of ([], []) => ([], [])
      | ([], [x]) => ([], [x]) | ([], x :: y :: ys) => ([x], y :: ys)
      | ([x], b) => ([x], b) | (x :: y :: ys, []) => ([x], y :: ys)
      | (x :: y :: ys, ad :: listb) => (x :: y :: ys, ad :: listb))
  end;

fun create_factor_tree_balanced xs =
  (if less_eq_nat (size_list xs) one_nata then Factor_Leaf ((), fst (hd xs))
    else let
           val (l, r) = partition_factors xs;
         in
           Factor_Node
             ((), create_factor_tree_balanced l, create_factor_tree_balanced r)
         end);

fun sequences B_ key (a :: b :: xs) =
  (if less ((ord_preorder o preorder_order o order_linorder) B_) (key b) (key a)
    then desc B_ key b [a] xs else asc B_ key b (fn ba => a :: ba) xs)
  | sequences B_ key [x] = [[x]]
  | sequences B_ key [] = []
and asc B_ key a asa (b :: bs) =
  (if less_eq ((ord_preorder o preorder_order o order_linorder) B_) (key a)
        (key b)
    then asc B_ key b (fn ys => asa (a :: ys)) bs
    else asa [a] :: sequences B_ key (b :: bs))
  | asc B_ key a asa [] = [asa [a]]
and desc B_ key a asa (b :: bs) =
  (if less ((ord_preorder o preorder_order o order_linorder) B_) (key b) (key a)
    then desc B_ key b (a :: asa) bs
    else (a :: asa) :: sequences B_ key (b :: bs))
  | desc B_ key a asa [] = [a :: asa];

fun merge B_ key (a :: asa) (b :: bs) =
  (if less ((ord_preorder o preorder_order o order_linorder) B_) (key b) (key a)
    then b :: merge B_ key (a :: asa) bs else a :: merge B_ key asa (b :: bs))
  | merge B_ key [] bs = bs
  | merge B_ key (v :: va) [] = v :: va;

fun merge_pairs B_ key (a :: b :: xs) =
  merge B_ key a b :: merge_pairs B_ key xs
  | merge_pairs B_ key [] = []
  | merge_pairs B_ key [v] = [v];

fun merge_all B_ key [] = []
  | merge_all B_ key [x] = x
  | merge_all B_ key (v :: vb :: vc) =
    merge_all B_ key (merge_pairs B_ key (v :: vb :: vc));

fun msort_key B_ key xs = merge_all B_ key (sequences B_ key xs);

fun sort_key B_ key = msort_key B_ key;

fun create_factor_tree xs = let
                              val ys = map (fn f => (f, degree zero_int f)) xs;
                              val a = rev (sort_key linorder_nat snd ys);
                            in
                              create_factor_tree_balanced a
                            end;

fun hensel_lifting_monic p n u vs =
  (if null vs then []
    else let
           val pn = binary_power monoid_mult_int p n;
           val c = mp pn u;
           val a = product_factor_tree p (create_factor_tree vs);
         in
           hensel_lifting_main p n c a
         end);

fun euclid_ext_aux (A1_, A2_) sa s ta t ra r =
  (if eq A2_ r
        (zero ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                 semiring_Gcd_factorial_semiring_gcd o
                 factorial_semiring_gcd_factorial_ring_gcd o
                 factorial_ring_gcd_euclidean_ring_gcd)
                A1_))
    then let
           val c =
             divide
               ((divide_modulo o modulo_semiring_modulo o
                  semiring_modulo_semiring_modulo_trivial o
                  semiring_modulo_trivial_semidom_modulo o
                  semidom_modulo_idom_modulo o idom_modulo_euclidean_ring o
                  euclidean_ring_euclidean_ring_gcd)
                 A1_)
               (one ((one_gcd o gcd_Gcd o gcd_semiring_Gcd o
                       semiring_Gcd_factorial_semiring_gcd o
                       factorial_semiring_gcd_factorial_ring_gcd o
                       factorial_ring_gcd_euclidean_ring_gcd)
                      A1_))
               (unit_factor
                 ((unit_factor_semidom_divide_unit_factor o
                    semidom_divide_unit_factor_normalization_semidom o
                    normalization_semidom_semiring_gcd o semiring_gcd_ring_gcd o
                    ring_gcd_factorial_ring_gcd o
                    factorial_ring_gcd_euclidean_ring_gcd)
                   A1_)
                 ra);
         in
           ((times ((times_dvd o dvd_gcd o gcd_Gcd o gcd_semiring_Gcd o
                      semiring_Gcd_factorial_semiring_gcd o
                      factorial_semiring_gcd_factorial_ring_gcd o
                      factorial_ring_gcd_euclidean_ring_gcd)
                     A1_)
               sa c,
              times ((times_dvd o dvd_gcd o gcd_Gcd o gcd_semiring_Gcd o
                       semiring_Gcd_factorial_semiring_gcd o
                       factorial_semiring_gcd_factorial_ring_gcd o
                       factorial_ring_gcd_euclidean_ring_gcd)
                      A1_)
                ta c),
             normalizea
               ((normalization_semidom_semiring_gcd o semiring_gcd_ring_gcd o
                  ring_gcd_factorial_ring_gcd o
                  factorial_ring_gcd_euclidean_ring_gcd)
                 A1_)
               ra)
         end
    else let
           val q =
             divide
               ((divide_modulo o modulo_semiring_modulo o
                  semiring_modulo_semiring_modulo_trivial o
                  semiring_modulo_trivial_semidom_modulo o
                  semidom_modulo_idom_modulo o idom_modulo_euclidean_ring o
                  euclidean_ring_euclidean_ring_gcd)
                 A1_)
               ra r;
         in
           euclid_ext_aux (A1_, A2_) s
             (minus
               ((minus_group_add o group_add_neg_numeral o neg_numeral_ring_1 o
                  ring_1_comm_ring_1 o comm_ring_1_idom o idom_idom_divide o
                  idom_divide_idom_modulo o idom_modulo_euclidean_ring o
                  euclidean_ring_euclidean_ring_gcd)
                 A1_)
               sa (times
                    ((times_dvd o dvd_gcd o gcd_Gcd o gcd_semiring_Gcd o
                       semiring_Gcd_factorial_semiring_gcd o
                       factorial_semiring_gcd_factorial_ring_gcd o
                       factorial_ring_gcd_euclidean_ring_gcd)
                      A1_)
                    q s))
             t (minus
                 ((minus_group_add o group_add_neg_numeral o
                    neg_numeral_ring_1 o ring_1_comm_ring_1 o comm_ring_1_idom o
                    idom_idom_divide o idom_divide_idom_modulo o
                    idom_modulo_euclidean_ring o
                    euclidean_ring_euclidean_ring_gcd)
                   A1_)
                 ta (times
                      ((times_dvd o dvd_gcd o gcd_Gcd o gcd_semiring_Gcd o
                         semiring_Gcd_factorial_semiring_gcd o
                         factorial_semiring_gcd_factorial_ring_gcd o
                         factorial_ring_gcd_euclidean_ring_gcd)
                        A1_)
                      q t))
             r (modulo
                 ((modulo_semiring_modulo o
                    semiring_modulo_semiring_modulo_trivial o
                    semiring_modulo_trivial_semidom_modulo o
                    semidom_modulo_idom_modulo o idom_modulo_euclidean_ring o
                    euclidean_ring_euclidean_ring_gcd)
                   A1_)
                 ra r)
         end);

fun bezout_coefficients (A1_, A2_) a b =
  fst (euclid_ext_aux (A1_, A2_)
        (one ((one_gcd o gcd_Gcd o gcd_semiring_Gcd o
                semiring_Gcd_factorial_semiring_gcd o
                factorial_semiring_gcd_factorial_ring_gcd o
                factorial_ring_gcd_euclidean_ring_gcd)
               A1_))
        (zero ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                 semiring_Gcd_factorial_semiring_gcd o
                 factorial_semiring_gcd_factorial_ring_gcd o
                 factorial_ring_gcd_euclidean_ring_gcd)
                A1_))
        (zero ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                 semiring_Gcd_factorial_semiring_gcd o
                 factorial_semiring_gcd_factorial_ring_gcd o
                 factorial_ring_gcd_euclidean_ring_gcd)
                A1_))
        (one ((one_gcd o gcd_Gcd o gcd_semiring_Gcd o
                semiring_Gcd_factorial_semiring_gcd o
                factorial_semiring_gcd_factorial_ring_gcd o
                factorial_ring_gcd_euclidean_ring_gcd)
               A1_))
        a b);

fun inverse_mod x m =
  fst (bezout_coefficients (euclidean_ring_gcd_int, equal_int) x m);

fun hensel_lifting p n f gs =
  let
    val lc = coeff zero_int f (degree zero_int f);
    val ilc = inverse_mod lc (binary_power monoid_mult_int p n);
    val g =
      smult (equal_int, comm_semiring_0_int, semiring_no_zero_divisors_int) ilc
        f;
  in
    hensel_lifting_monic p n g gs
  end;

fun root_int_maina pm ipm ip x n =
  let
    val xpm = binary_power monoid_mult_int x pm;
    val xp = times_inta xpm x;
  in
    (if less_eq_int xp n then (x, equal_inta xp n)
      else root_int_maina pm ipm ip
             (divide_inta (plus_inta (divide_inta n xpm) (times_inta x ipm)) ip)
             n)
  end;

fun numeral A_ (Bit1 n) =
  let
    val m = numeral A_ n;
  in
    plus ((plus_semigroup_add o semigroup_add_numeral) A_)
      (plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m)
      (one (one_numeral A_))
  end
  | numeral A_ (Bit0 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m
    end
  | numeral A_ One = one (one_numeral A_);

fun of_nat A_ n =
  (if equal_nata n zero_nata
    then zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1)
                A_)
    else let
           val (m, q) = divmod_nat n (nat_of_integer (2 : IntInf.int));
           val ma =
             times ((times_power o power_monoid_mult o
                      monoid_mult_semiring_numeral o
                      semiring_numeral_semiring_1)
                     A_)
               (numeral
                 ((numeral_semiring_numeral o semiring_numeral_semiring_1) A_)
                 (Bit0 One))
               (of_nat A_ m);
         in
           (if equal_nata q zero_nata then ma
             else plus ((plus_semigroup_add o semigroup_add_numeral o
                          numeral_semiring_numeral o
                          semiring_numeral_semiring_1)
                         A_)
                    ma (one ((one_numeral o numeral_semiring_numeral o
                               semiring_numeral_semiring_1)
                              A_)))
         end);

fun ceiling A_ x =
  uminus_inta
    (floor A_
      (uminus
        ((uminus_abs_if o abs_if_linordered_ring o
           linordered_ring_linordered_ring_strict o
           linordered_ring_strict_linordered_idom o
           linordered_idom_linordered_field o
           linordered_field_archimedean_field o archimedean_field_floor_ceiling)
          A_)
        x));

datatype proper_base = Abs_proper_base of int;

fun into_base xa =
  Abs_proper_base
    (if less_eq_int (Int_of_integer (2 : IntInf.int)) xa then xa
      else Int_of_integer (2 : IntInf.int));

fun rep_proper_base (Abs_proper_base x) = x;

fun square_base xa =
  Abs_proper_base (times_inta (rep_proper_base xa) (rep_proper_base xa));

fun get_base x = rep_proper_base x;

fun log_main b x =
  (if less_int x (get_base b) then (zero_nata, one_inta)
    else let
           val (z, bz) = log_main (square_base b) x;
           val l = times_nata (nat_of_integer (2 : IntInf.int)) z;
           val bz1 = times_inta bz (get_base b);
         in
           (if less_int x bz1 then (l, bz) else (suc l, bz1))
         end);

fun log_ceiling b x = let
                        val (y, by) = log_main (into_base b) x;
                      in
                        (if equal_inta x by then y else suc y)
                      end;

fun start_value n p =
  binary_power monoid_mult_int (Int_of_integer (2 : IntInf.int))
    (nat (ceiling floor_ceiling_rat
           (divide_rata
             (of_nat semiring_1_rat
               (log_ceiling (Int_of_integer (2 : IntInf.int)) n))
             (of_nat semiring_1_rat p))));

fun root_int_main p n =
  (if equal_nata p zero_nata then (one_inta, equal_inta n one_inta)
    else let
           val pm = minus_nata p one_nata;
         in
           root_int_maina pm (int_of_nat pm) (int_of_nat p) (start_value n p) n
         end);

fun root_int_ceiling_pos p x =
  (if equal_nata p zero_nata then zero_inta
    else (case root_int_main p x of (y, true) => y
           | (y, false) => plus_inta y one_inta));

fun root_int_floor_pos p x =
  (if equal_nata p zero_nata then zero_inta else fst (root_int_main p x));

fun root_int_floor p x =
  (if less_eq_int zero_inta x then root_int_floor_pos p x
    else uminus_inta (root_int_ceiling_pos p (uminus_inta x)));

fun mahler_landau_graeffe_approximation kk dd f =
  let
    val no =
      sum_list monoid_add_int
        (map (fn a => times_inta a a) (coeffs zero_int f));
  in
    root_int_floor kk (times_inta (int_of_nat dd) no)
  end;

fun alternate (x :: y :: ys) = let
                                 val (evn, od) = alternate ys;
                               in
                                 (x :: evn, y :: od)
                               end
  | alternate [] = ([], [])
  | alternate [v] = ([v], []);

fun poly_even_odd (A1_, A2_) f =
  let
    val (evn, od) =
      alternate
        (coeffs
          ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_comm_semiring_1 o
             comm_semiring_1_comm_semiring_1_cancel o
             comm_semiring_1_cancel_comm_ring_1)
            A2_)
          f);
  in
    (poly_of_list
       ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
          semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
          comm_semiring_1_cancel_comm_ring_1)
          A2_,
         A1_)
       evn,
      poly_of_list
        ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_comm_ring_1)
           A2_,
          A1_)
        od)
  end;

fun graeffe_one_step (A1_, A2_) c f =
  let
    val (g, h) = poly_even_odd (A1_, comm_ring_1_idom A2_) f;
  in
    smult (A1_, (comm_semiring_0_comm_semiring_1 o
                  comm_semiring_1_comm_semiring_1_cancel o
                  comm_semiring_1_cancel_semidom o semidom_idom)
                  A2_,
            (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
              semiring_1_no_zero_divisors_semidom o semidom_idom)
              A2_)
      c (minus_polya
          ((ab_group_add_ring o ring_ring_1 o ring_1_comm_ring_1 o
             comm_ring_1_idom)
             A2_,
            A1_)
          (karatsuba_mult_poly
            (A1_, comm_ring_1_idom A2_,
              (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
                semiring_1_no_zero_divisors_semidom o semidom_idom)
                A2_)
            g g)
          (karatsuba_mult_poly
            (A1_, comm_ring_1_idom A2_,
              (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
                semiring_1_no_zero_divisors_semidom o semidom_idom)
                A2_)
            (monom_mult
              ((comm_semiring_1_comm_semiring_1_cancel o
                 comm_semiring_1_cancel_semidom o semidom_idom)
                A2_)
              one_nata h)
            h))
  end;

fun min A_ a b = (if less_eq A_ a b then a else b);

fun mahler_approximation_main bnd dd c g mm k kk =
  let
    val mmm = mahler_landau_graeffe_approximation kk dd g;
    val new_mm = (if equal_nata k zero_nata then mmm else min ord_int mm mmm);
  in
    (if less_eq_nat bnd k then new_mm
      else mahler_approximation_main bnd (times_nata dd dd) c
             (graeffe_one_step (equal_int, idom_int) c g) new_mm (suc k)
             (times_nata (nat_of_integer (2 : IntInf.int)) kk))
  end;

fun mahler_approximation bnd d f =
  mahler_approximation_main bnd (times_nata d d)
    (binary_power monoid_mult_int (uminus_inta one_inta) (degree zero_int f)) f
    (uminus_inta one_inta) zero_nata (nat_of_integer (2 : IntInf.int));

fun fold_atLeastAtMost_nat f a b acc =
  (if less_nat b a then acc
    else fold_atLeastAtMost_nat f (plus_nata a one_nata) b (f a acc));

fun fact A_ n =
  of_nat (semiring_1_semiring_char_0 A_)
    (fold_atLeastAtMost_nat times_nata (nat_of_integer (2 : IntInf.int)) n
      one_nata);

fun binomial n k =
  (if less_eq_nat k n
    then divide_nata (fact semiring_char_0_nat n)
           (times_nata (fact semiring_char_0_nat k)
             (fact semiring_char_0_nat (minus_nata n k)))
    else zero_nata);

fun mignotte_bound f d =
  let
    val da = minus_nata d one_nata;
    val d2 = divide_nata da (nat_of_integer (2 : IntInf.int));
    val binom = binomial da d2;
  in
    plus_inta (mahler_approximation (nat_of_integer (2 : IntInf.int)) binom f)
      (times_inta (int_of_nat binom)
        (abs_int (coeff zero_int f (degree zero_int f))))
  end;

fun factor_bound x = mignotte_bound x;

fun drop n [] = []
  | drop n (x :: xs) =
    (if equal_nata n zero_nata then x :: xs
      else drop (minus_nata n one_nata) xs);

fun max_factor_degree degs =
  let
    val ds = sort_key linorder_nat (fn x => x) degs;
  in
    sum_list monoid_add_nat
      (drop (divide_nata (size_list ds) (nat_of_integer (2 : IntInf.int))) ds)
  end;

fun degree_bound A_ vs = max_factor_degree (map (degree A_) vs);

fun berlekamp_zassenhaus_factorization f =
  let
    val p = suitable_prime_bz f;
    val (_, fs) = finite_field_factorization_int p f;
    val max_deg = degree_bound zero_int fs;
    val bnd =
      times_inta
        (times_inta (Int_of_integer (2 : IntInf.int))
          (abs_int (coeff zero_int f (degree zero_int f))))
        (factor_bound f max_deg);
    val k = find_exponent p bnd;
    val vs = hensel_lifting p k f fs;
  in
    zassenhaus_reconstruction vs p k f
  end;

val berlekamp_zassenhaus_factorization_algorithm :
  int_poly_factorization_algorithm
  = Abs_int_poly_factorization_algorithm berlekamp_zassenhaus_factorization;

fun yun_factorization_main (A1_, A2_) gcd bn cn i sqr =
  (if eq (equal_poly
           ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
              semiring_Gcd_factorial_semiring_gcd o
              factorial_semiring_gcd_factorial_ring_gcd)
              A1_,
             A2_))
        bn (one_polya
             ((comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_semidom o semidom_idom o
                idom_idom_divide o idom_divide_factorial_ring_gcd)
               A1_))
    then sqr
    else let
           val dn =
             minus_polya
               ((ab_group_add_ring o ring_ring_1 o ring_1_comm_ring_1 o
                  comm_ring_1_idom o idom_idom_divide o
                  idom_divide_factorial_ring_gcd)
                  A1_,
                 A2_)
               cn (pderiv
                    (A2_, (comm_semiring_1_comm_semiring_1_cancel o
                            comm_semiring_1_cancel_semidom o semidom_idom o
                            idom_idom_divide o idom_divide_factorial_ring_gcd)
                            A1_,
                      (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
                        semiring_1_no_zero_divisors_semidom o semidom_idom o
                        idom_idom_divide o idom_divide_factorial_ring_gcd)
                        A1_)
                    bn);
           val an = gcd bn dn;
         in
           yun_factorization_main (A1_, A2_) gcd
             (divide_polya (A2_, idom_divide_factorial_ring_gcd A1_) bn an)
             (divide_polya (A2_, idom_divide_factorial_ring_gcd A1_) dn an)
             (suc i) ((an, suc i) :: sqr)
         end);

fun yun_monic_factorization (A1_, A2_) gcd p =
  let
    val pp =
      pderiv
        (A2_, (comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_semidom o semidom_idom o
                idom_idom_divide o idom_divide_factorial_ring_gcd)
                A1_,
          (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
            semiring_1_no_zero_divisors_semidom o semidom_idom o
            idom_idom_divide o idom_divide_factorial_ring_gcd)
            A1_)
        p;
    val u = gcd p pp;
    val b0 = divide_polya (A2_, idom_divide_factorial_ring_gcd A1_) p u;
    val c0 = divide_polya (A2_, idom_divide_factorial_ring_gcd A1_) pp u;
  in
    filter
      (fn (a, _) =>
        not (eq (equal_poly
                  ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                     semiring_Gcd_factorial_semiring_gcd o
                     factorial_semiring_gcd_factorial_ring_gcd)
                     A1_,
                    A2_))
              a (one_polya
                  ((comm_semiring_1_comm_semiring_1_cancel o
                     comm_semiring_1_cancel_semidom o semidom_idom o
                     idom_idom_divide o idom_divide_factorial_ring_gcd)
                    A1_))))
      (yun_factorization_main (A1_, A2_) gcd b0 c0 zero_nata [])
  end;

fun find uu [] = NONE
  | find p (x :: xs) = (if p x then SOME x else find p xs);

fun square_free_heuristic f =
  let
    val lc = coeff zero_int f (degree zero_int f);
  in
    find (fn p =>
           coprimea (semiring_gcd_int, equal_int) lc p andalso
             separable_impl p f)
      [Int_of_integer (2 : IntInf.int), Int_of_integer (3 : IntInf.int),
        Int_of_integer (5 : IntInf.int), Int_of_integer (7 : IntInf.int),
        Int_of_integer (11 : IntInf.int), Int_of_integer (13 : IntInf.int),
        Int_of_integer (17 : IntInf.int), Int_of_integer (19 : IntInf.int),
        Int_of_integer (23 : IntInf.int)]
  end;

fun normalize_poly (A1_, A2_, A3_) p =
  divide_polya (A1_, A2_) p
    (pCons
      ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
         semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
         comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide)
         A2_,
        A1_)
      (unit_factor (unit_factor_semidom_divide_unit_factor A3_)
        (coeff
          ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_comm_semiring_1 o
             comm_semiring_1_comm_semiring_1_cancel o
             comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide)
            A2_)
          p (degree
              ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
                 semiring_1_comm_semiring_1 o
                 comm_semiring_1_comm_semiring_1_cancel o
                 comm_semiring_1_cancel_semidom o semidom_idom o
                 idom_idom_divide)
                A2_)
              p)))
      (zero_polya
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide)
          A2_)));

fun coprime_approx_main A_ p ff_ops f g =
  equal_lista A_
    (gcd_poly_i A_ ff_ops (of_int_poly_i ff_ops (mp p f))
      (of_int_poly_i ff_ops (mp p g)))
    [onea ff_ops];

val gcd_primes64 : int list =
  [Int_of_integer (383 : IntInf.int), Int_of_integer (21984191 : IntInf.int),
    Int_of_integer (50329901 : IntInf.int),
    Int_of_integer (80329901 : IntInf.int),
    Int_of_integer (219849193 : IntInf.int)];

fun coprime_heuristic f g =
  let
    val lcf = coeff zero_int f (degree zero_int f);
    val lcg = coeff zero_int g (degree zero_int g);
  in
    not (is_none
          (find (fn p =>
                  (coprimea (semiring_gcd_int, equal_int) lcf p orelse
                    coprimea (semiring_gcd_int, equal_int) lcg p) andalso
                    coprime_approx_main equal_uint64 p
                      (finite_field_ops64 (uint64_of_int p)) f g)
            gcd_primes64))
  end;

fun pseudo_mod_main_list (A1_, A2_) lc r d n =
  (if equal_nata n zero_nata then r
    else let
           val rr =
             map (times
                   ((times_dvd o dvd_comm_monoid_mult o
                      comm_monoid_mult_comm_semiring_1 o
                      comm_semiring_1_comm_semiring_1_cancel o
                      comm_semiring_1_cancel_comm_ring_1)
                     A2_)
                   lc)
               r;
           val a = hd r;
           val rrr =
             tl (if eq A1_ a
                      (zero ((zero_mult_zero o mult_zero_semiring_0 o
                               semiring_0_semiring_1 o
                               semiring_1_comm_semiring_1 o
                               comm_semiring_1_comm_semiring_1_cancel o
                               comm_semiring_1_cancel_comm_ring_1)
                              A2_))
                  then rr
                  else minus_poly_rev_list
                         ((group_add_neg_numeral o neg_numeral_ring_1 o
                            ring_1_comm_ring_1)
                           A2_)
                         rr (map (times
                                   ((times_dvd o dvd_comm_monoid_mult o
                                      comm_monoid_mult_comm_semiring_1 o
                                      comm_semiring_1_comm_semiring_1_cancel o
                                      comm_semiring_1_cancel_comm_ring_1)
                                     A2_)
                                   a)
                              d));
         in
           pseudo_mod_main_list (A1_, A2_) lc rrr d (minus_nata n one_nata)
         end);

fun pseudo_mod_list (A1_, A2_) p q =
  (if null q then p
    else let
           val rq = rev q;
           val a =
             pseudo_mod_main_list (A1_, A2_) (hd rq) (rev p) rq
               (minus_nata (plus_nata one_nata (size_list p)) (size_list q));
         in
           rev a
         end);

fun pseudo_mod (A1_, A2_, A3_) f g =
  poly_of_list
    ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
       semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
       comm_semiring_1_cancel_comm_ring_1)
       A2_,
      A1_)
    (pseudo_mod_list (A1_, A2_)
      (coeffs
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_comm_ring_1)
          A2_)
        f)
      (coeffs
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_comm_ring_1)
          A2_)
        g));

fun is_zero A_ p = null (coeffs A_ p);

fun gcd_poly_code_aux (A1_, A2_) p q =
  (if is_zero
        ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
           semiring_Gcd_factorial_semiring_gcd o
           factorial_semiring_gcd_factorial_ring_gcd)
          A1_)
        q
    then normalize_poly
           (A2_, idom_divide_factorial_ring_gcd A1_,
             (semidom_divide_unit_factor_normalization_semidom o
               normalization_semidom_semiring_gcd o semiring_gcd_ring_gcd o
               ring_gcd_factorial_ring_gcd)
               A1_)
           p
    else gcd_poly_code_aux (A1_, A2_) q
           (primitive_part
             ((semiring_gcd_ring_gcd o ring_gcd_factorial_ring_gcd) A1_, A2_)
             (pseudo_mod
               (A2_, (comm_ring_1_idom o idom_idom_divide o
                       idom_divide_factorial_ring_gcd)
                       A1_,
                 (semiring_1_no_zero_divisors_semidom o semidom_idom o
                   idom_idom_divide o idom_divide_factorial_ring_gcd)
                   A1_)
               p q)));

fun gcd_int_poly f g =
  (if equal_polya (zero_int, equal_int) f (zero_polya zero_int)
    then normalize_poly
           (equal_int, idom_divide_int, semidom_divide_unit_factor_int) g
    else (if equal_polya (zero_int, equal_int) g (zero_polya zero_int)
           then normalize_poly
                  (equal_int, idom_divide_int, semidom_divide_unit_factor_int) f
           else let
                  val cf = content semiring_gcd_int f;
                  val cg = content semiring_gcd_int g;
                  val ct = gcd_intc cf cg;
                  val ff =
                    map_poly zero_int (zero_int, equal_int)
                      (fn x => divide_inta x cf) f;
                  val gg =
                    map_poly zero_int (zero_int, equal_int)
                      (fn x => divide_inta x cg) g;
                in
                  (if coprime_heuristic ff gg
                    then pCons (zero_int, equal_int) ct (zero_polya zero_int)
                    else smult (equal_int, comm_semiring_0_int,
                                 semiring_no_zero_divisors_int)
                           ct (gcd_poly_code_aux
                                (factorial_ring_gcd_int, equal_int) ff gg))
                end));

fun square_free_factorization_int_main f =
  (case square_free_heuristic f
    of NONE =>
      yun_monic_factorization (factorial_ring_gcd_int, equal_int) gcd_int_poly f
    | SOME _ => [(f, one_nata)]);

fun square_free_factorization_inta f =
  (if equal_nata (degree zero_int f) zero_nata
    then (coeff zero_int f (degree zero_int f), [])
    else let
           val c = content semiring_gcd_int f;
           val d =
             times_inta (sgn_int (coeff zero_int f (degree zero_int f))) c;
           val g = sdiv_poly (equal_int, idom_divide_int) f d;
         in
           (d, square_free_factorization_int_main g)
         end);

fun takeWhile p [] = []
  | takeWhile p (x :: xs) = (if p x then x :: takeWhile p xs else []);

fun x_split (A1_, A2_) f =
  let
    val fs = coeffs ((zero_mult_zero o mult_zero_semiring_0) A2_) f;
    val zs =
      takeWhile (eq A1_ (zero ((zero_mult_zero o mult_zero_semiring_0) A2_)))
        fs;
  in
    (case zs of [] => (zero_nata, f)
      | _ :: _ =>
        (size_list zs,
          poly_of_list (comm_monoid_add_semiring_0 A2_, A1_)
            (dropWhile
              (eq A1_ (zero ((zero_mult_zero o mult_zero_semiring_0) A2_)))
              fs)))
  end;

fun monom (A1_, A2_) a n =
  Poly (if eq A2_ a (zero A1_) then [] else replicate n (zero A1_) @ [a]);

fun square_free_factorization_int f =
  let
    val (n, g) = x_split (equal_int, semiring_0_int) f;
    val (d, fs) = square_free_factorization_inta g;
  in
    (if equal_nata n zero_nata then (d, fs)
      else (d, (monom (zero_int, equal_int) one_inta one_nata, n) :: fs))
  end;

fun rep_int_poly_factorization_algorithm
  (Abs_int_poly_factorization_algorithm x) = x;

fun int_poly_factorization_algorithm x = rep_int_poly_factorization_algorithm x;

fun reflect_poly (A1_, A2_) p =
  Poly (rev (dropWhile (eq A2_ (zero A1_)) (coeffs A1_ p)));

fun main_int_poly_factorization alg f =
  let
    val df = degree zero_int f;
  in
    (if equal_nata df one_nata then [f]
      else (if less_int
                 (abs_int
                   (case coeffs zero_int f of [] => zero_inta | x :: _ => x))
                 (abs_int (coeff zero_int f df))
             then map (reflect_poly (zero_int, equal_int))
                    (int_poly_factorization_algorithm alg
                      (reflect_poly (zero_int, equal_int) f))
             else int_poly_factorization_algorithm alg f))
  end;

fun internal_int_poly_factorization alg f =
  let
    val (a, gis) = square_free_factorization_int f;
  in
    (a, maps (fn (g, i) =>
               map (fn fa => (fa, i)) (main_int_poly_factorization alg g))
          gis)
  end;

fun factorize_int_last_nz_poly alg f =
  let
    val df = degree zero_int f;
  in
    (if equal_nata df zero_nata
      then ((case coeffs zero_int f of [] => zero_inta | x :: _ => x), [])
      else (if equal_nata df one_nata
             then (content semiring_gcd_int f,
                    [(primitive_part (semiring_gcd_int, equal_int) f,
                       one_nata)])
             else internal_int_poly_factorization alg f))
  end;

fun factorize_int_poly_generic alg f =
  let
    val (n, g) = x_split (equal_int, semiring_0_int) f;
  in
    (if equal_polya (zero_int, equal_int) g (zero_polya zero_int)
      then (zero_inta, [])
      else let
             val (a, fs) = factorize_int_last_nz_poly alg g;
           in
             (if equal_nata n zero_nata then (a, fs)
               else (a, (monom (zero_int, equal_int) one_inta one_nata, n) ::
                          fs))
           end)
  end;

fun factors_of_int_poly p =
  map (abs_int_poly o fst)
    (snd (factorize_int_poly_generic
           berlekamp_zassenhaus_factorization_algorithm p));

fun real_alg_2a ri p l r =
  (if equal_nata (degree zero_int p) one_nata
    then Rational
           (fract
             (uminus_inta
               (case coeffs zero_int p of [] => zero_inta | x :: _ => x))
             (coeff zero_int p one_nata))
    else let
           val (pa, (la, ra)) =
             normalize_bounds_1
               let
                 val (la, (ra, _)) =
                   tighten_poly_bounds_for_x p zero_rata l r
                     (sgn_rata
                       (fold_coeffs zero_int
                         (fn a => fn b => plus_rata (of_int a) (times_rata r b))
                         p zero_rata));
               in
                 (p, (la, ra))
               end;
         in
           Irrational (number_root ri ra, (pa, (la, ra)))
         end);

fun select_correct_factor_int_poly bnd_update bnd_get init p =
  let
    val qs = factors_of_int_poly p;
    val polys = map (fn q => (q, root_info q)) qs;
    val (a, b) = select_correct_factor bnd_update bnd_get init polys;
  in
    let
      val (q, ri) = a;
    in
      (fn (aa, ba) => real_alg_2a ri q aa ba)
    end
      b
  end;

fun tighten_poly_bounds_binary cr1 cr2 ((l1, (r1, sr1)), (l2, (r2, sr2))) =
  (tighten_poly_bounds cr1 l1 r1 sr1, tighten_poly_bounds cr2 l2 r2 sr2);

fun zero_poly A_ = {zero = zero_polya A_} : 'a poly zero;

fun poly_lift (A1_, A2_) =
  map_poly A1_ (zero_poly A1_, equal_poly (A1_, A2_))
    (fn a => pCons (A1_, A2_) a (zero_polya A1_));

fun plus_poly (A1_, A2_) = {plus = plus_polya (A1_, A2_)} : 'a poly plus;

fun semigroup_add_poly (A1_, A2_) = {plus_semigroup_add = plus_poly (A1_, A2_)}
  : 'a poly semigroup_add;

fun ab_semigroup_add_poly (A1_, A2_) =
  {semigroup_add_ab_semigroup_add = semigroup_add_poly (A1_, A2_)} :
  'a poly ab_semigroup_add;

fun monoid_add_poly (A1_, A2_) =
  {semigroup_add_monoid_add = semigroup_add_poly (A1_, A2_),
    zero_monoid_add =
      zero_poly ((zero_monoid_add o monoid_add_comm_monoid_add) A1_)}
  : 'a poly monoid_add;

fun comm_monoid_add_poly (A1_, A2_) =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_poly (A1_, A2_),
    monoid_add_comm_monoid_add = monoid_add_poly (A1_, A2_)}
  : 'a poly comm_monoid_add;

fun poly_x_mult_y (A1_, A2_) p =
  let
    val cs = coeffs ((zero_monoid_add o monoid_add_comm_monoid_add) A1_) p;
  in
    poly_of_list
      (comm_monoid_add_poly (A1_, A2_),
        equal_poly ((zero_monoid_add o monoid_add_comm_monoid_add) A1_, A2_))
      (map (fn (i, ai) =>
             monom ((zero_monoid_add o monoid_add_comm_monoid_add) A1_, A2_) ai
               i)
        (zip (upt zero_nata (size_list cs)) cs))
  end;

fun dichotomous_Lazard A_ x y n =
  (if less_eq_nat n one_nata
    then (if equal_nata n one_nata then x
           else one ((one_numeral o numeral_neg_numeral o neg_numeral_ring_1 o
                       ring_1_comm_ring_1 o comm_ring_1_idom o idom_idom_divide)
                      A_))
    else let
           val (d, r) = divmod_nat n (nat_of_integer (2 : IntInf.int));
           val reca = dichotomous_Lazard A_ x y d;
           val recsq =
             divide
               ((divide_divide_trivial o divide_trivial_semidom_divide o
                  semidom_divide_idom_divide)
                 A_)
               (times
                 ((times_dvd o dvd_comm_monoid_mult o
                    comm_monoid_mult_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_semidom o semidom_idom o
                    idom_idom_divide)
                   A_)
                 reca reca)
               y;
         in
           (if equal_nata r zero_nata then recsq
             else divide
                    ((divide_divide_trivial o divide_trivial_semidom_divide o
                       semidom_divide_idom_divide)
                      A_)
                    (times
                      ((times_dvd o dvd_comm_monoid_mult o
                         comm_monoid_mult_comm_semiring_1 o
                         comm_semiring_1_comm_semiring_1_cancel o
                         comm_semiring_1_cancel_semidom o semidom_idom o
                         idom_idom_divide)
                        A_)
                      recsq x)
                    y)
         end);

fun resultant_impl_rec_Lazard (A1_, A2_) gi_1 gi ni_1 d1_1 hi_2 =
  let
    val ni =
      degree
        ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
           semiring_Gcd_factorial_semiring_gcd o
           factorial_semiring_gcd_factorial_ring_gcd)
          A1_)
        gi;
    val pmod =
      pseudo_mod
        (A2_, (comm_ring_1_idom o idom_idom_divide o
                idom_divide_factorial_ring_gcd)
                A1_,
          (semiring_1_no_zero_divisors_semidom o semidom_idom o
            idom_idom_divide o idom_divide_factorial_ring_gcd)
            A1_)
        gi_1 gi;
  in
    (if is_zero
          ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
             semiring_Gcd_factorial_semiring_gcd o
             factorial_semiring_gcd_factorial_ring_gcd)
            A1_)
          pmod
      then (if equal_nata ni zero_nata
             then let
                    val d1 = minus_nata ni_1 ni;
                    val gia =
                      coeff ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                               semiring_Gcd_factorial_semiring_gcd o
                               factorial_semiring_gcd_factorial_ring_gcd)
                              A1_)
                        gi (degree
                             ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                                semiring_Gcd_factorial_semiring_gcd o
                                factorial_semiring_gcd_factorial_ring_gcd)
                               A1_)
                             gi);
                  in
                    (if equal_nata d1 one_nata then gia
                      else let
                             val gi_1a =
                               coeff ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
semiring_Gcd_factorial_semiring_gcd o factorial_semiring_gcd_factorial_ring_gcd)
                                       A1_)
                                 gi_1
                                 (degree
                                   ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                                      semiring_Gcd_factorial_semiring_gcd o
                                      factorial_semiring_gcd_factorial_ring_gcd)
                                     A1_)
                                   gi_1);
                             val hi_1 =
                               (if equal_nata d1_1 one_nata then gi_1a
                                 else dichotomous_Lazard
(idom_divide_factorial_ring_gcd A1_) gi_1a hi_2 d1_1);
                           in
                             dichotomous_Lazard
                               (idom_divide_factorial_ring_gcd A1_) gia hi_1 d1
                           end)
                  end
             else zero ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                          semiring_Gcd_factorial_semiring_gcd o
                          factorial_semiring_gcd_factorial_ring_gcd)
                         A1_))
      else let
             val d1 = minus_nata ni_1 ni;
             val gi_1a =
               coeff ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                        semiring_Gcd_factorial_semiring_gcd o
                        factorial_semiring_gcd_factorial_ring_gcd)
                       A1_)
                 gi_1
                 (degree
                   ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                      semiring_Gcd_factorial_semiring_gcd o
                      factorial_semiring_gcd_factorial_ring_gcd)
                     A1_)
                   gi_1);
             val hi_1 =
               (if equal_nata d1_1 one_nata then gi_1a
                 else dichotomous_Lazard (idom_divide_factorial_ring_gcd A1_)
                        gi_1a hi_2 d1_1);
             val divisor =
               (if equal_nata d1 one_nata
                 then times ((times_dvd o dvd_gcd o gcd_Gcd o gcd_semiring_Gcd o
                               semiring_Gcd_factorial_semiring_gcd o
                               factorial_semiring_gcd_factorial_ring_gcd)
                              A1_)
                        gi_1a hi_1
                 else (if dvd (equal_nat, semidom_modulo_nat)
                            (nat_of_integer (2 : IntInf.int)) d1
                        then times ((times_dvd o dvd_gcd o gcd_Gcd o
                                      gcd_semiring_Gcd o
                                      semiring_Gcd_factorial_semiring_gcd o
                                      factorial_semiring_gcd_factorial_ring_gcd)
                                     A1_)
                               (uminus
                                 ((uminus_group_add o group_add_neg_numeral o
                                    neg_numeral_ring_1 o ring_1_comm_ring_1 o
                                    comm_ring_1_idom o idom_idom_divide o
                                    idom_divide_factorial_ring_gcd)
                                   A1_)
                                 gi_1a)
                               (binary_power
                                 ((monoid_mult_semiring_numeral o
                                    semiring_numeral_semiring_1 o
                                    semiring_1_comm_semiring_1 o
                                    comm_semiring_1_comm_semiring_1_cancel o
                                    comm_semiring_1_cancel_semidom o
                                    semidom_idom o idom_idom_divide o
                                    idom_divide_factorial_ring_gcd)
                                   A1_)
                                 hi_1 d1)
                        else times ((times_dvd o dvd_gcd o gcd_Gcd o
                                      gcd_semiring_Gcd o
                                      semiring_Gcd_factorial_semiring_gcd o
                                      factorial_semiring_gcd_factorial_ring_gcd)
                                     A1_)
                               gi_1a
                               (binary_power
                                 ((monoid_mult_semiring_numeral o
                                    semiring_numeral_semiring_1 o
                                    semiring_1_comm_semiring_1 o
                                    comm_semiring_1_comm_semiring_1_cancel o
                                    comm_semiring_1_cancel_semidom o
                                    semidom_idom o idom_idom_divide o
                                    idom_divide_factorial_ring_gcd)
                                   A1_)
                                 hi_1 d1)));
             val gi_p1 =
               sdiv_poly (A2_, idom_divide_factorial_ring_gcd A1_) pmod divisor;
           in
             resultant_impl_rec_Lazard (A1_, A2_) gi gi_p1 ni d1 hi_1
           end)
  end;

fun resultant_impl_start_Lazard (A1_, A2_) g1 g2 =
  let
    val pmod =
      pseudo_mod
        (A2_, (comm_ring_1_idom o idom_idom_divide o
                idom_divide_factorial_ring_gcd)
                A1_,
          (semiring_1_no_zero_divisors_semidom o semidom_idom o
            idom_idom_divide o idom_divide_factorial_ring_gcd)
            A1_)
        g1 g2;
    val n2 =
      degree
        ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
           semiring_Gcd_factorial_semiring_gcd o
           factorial_semiring_gcd_factorial_ring_gcd)
          A1_)
        g2;
    val n1 =
      degree
        ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
           semiring_Gcd_factorial_semiring_gcd o
           factorial_semiring_gcd_factorial_ring_gcd)
          A1_)
        g1;
    val g2a =
      coeff ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
               semiring_Gcd_factorial_semiring_gcd o
               factorial_semiring_gcd_factorial_ring_gcd)
              A1_)
        g2 (degree
             ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                semiring_Gcd_factorial_semiring_gcd o
                factorial_semiring_gcd_factorial_ring_gcd)
               A1_)
             g2);
    val d1 = minus_nata n1 n2;
  in
    (if is_zero
          ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
             semiring_Gcd_factorial_semiring_gcd o
             factorial_semiring_gcd_factorial_ring_gcd)
            A1_)
          pmod
      then (if equal_nata n2 zero_nata
             then (if equal_nata d1 zero_nata
                    then one ((one_gcd o gcd_Gcd o gcd_semiring_Gcd o
                                semiring_Gcd_factorial_semiring_gcd o
                                factorial_semiring_gcd_factorial_ring_gcd)
                               A1_)
                    else (if equal_nata d1 one_nata then g2a
                           else binary_power
                                  ((monoid_mult_semiring_numeral o
                                     semiring_numeral_semiring_1 o
                                     semiring_1_comm_semiring_1 o
                                     comm_semiring_1_comm_semiring_1_cancel o
                                     comm_semiring_1_cancel_semidom o
                                     semidom_idom o idom_idom_divide o
                                     idom_divide_factorial_ring_gcd)
                                    A1_)
                                  g2a d1))
             else zero ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                          semiring_Gcd_factorial_semiring_gcd o
                          factorial_semiring_gcd_factorial_ring_gcd)
                         A1_))
      else let
             val g3 =
               (if dvd (equal_nat, semidom_modulo_nat)
                     (nat_of_integer (2 : IntInf.int)) d1
                 then uminus_polya
                        ((ab_group_add_ring o ring_ring_1 o ring_1_comm_ring_1 o
                           comm_ring_1_idom o idom_idom_divide o
                           idom_divide_factorial_ring_gcd)
                          A1_)
                        pmod
                 else pmod);
             val n3 =
               degree
                 ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                    semiring_Gcd_factorial_semiring_gcd o
                    factorial_semiring_gcd_factorial_ring_gcd)
                   A1_)
                 g3;
             val pmoda =
               pseudo_mod
                 (A2_, (comm_ring_1_idom o idom_idom_divide o
                         idom_divide_factorial_ring_gcd)
                         A1_,
                   (semiring_1_no_zero_divisors_semidom o semidom_idom o
                     idom_idom_divide o idom_divide_factorial_ring_gcd)
                     A1_)
                 g2 g3;
           in
             (if is_zero
                   ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                      semiring_Gcd_factorial_semiring_gcd o
                      factorial_semiring_gcd_factorial_ring_gcd)
                     A1_)
                   pmoda
               then (if equal_nata n3 zero_nata
                      then let
                             val d2 = minus_nata n2 n3;
                             val g3a =
                               coeff ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
semiring_Gcd_factorial_semiring_gcd o factorial_semiring_gcd_factorial_ring_gcd)
                                       A1_)
                                 g3 (degree
                                      ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
 semiring_Gcd_factorial_semiring_gcd o
 factorial_semiring_gcd_factorial_ring_gcd)
A1_)
                                      g3);
                           in
                             (if equal_nata d2 one_nata then g3a
                               else dichotomous_Lazard
                                      (idom_divide_factorial_ring_gcd A1_) g3a
                                      (if equal_nata d1 one_nata then g2a
else binary_power
       ((monoid_mult_semiring_numeral o semiring_numeral_semiring_1 o
          semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
          comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide o
          idom_divide_factorial_ring_gcd)
         A1_)
       g2a d1)
                                      d2)
                           end
                      else zero ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                                   semiring_Gcd_factorial_semiring_gcd o
                                   factorial_semiring_gcd_factorial_ring_gcd)
                                  A1_))
               else let
                      val h2 =
                        (if equal_nata d1 one_nata then g2a
                          else binary_power
                                 ((monoid_mult_semiring_numeral o
                                    semiring_numeral_semiring_1 o
                                    semiring_1_comm_semiring_1 o
                                    comm_semiring_1_comm_semiring_1_cancel o
                                    comm_semiring_1_cancel_semidom o
                                    semidom_idom o idom_idom_divide o
                                    idom_divide_factorial_ring_gcd)
                                   A1_)
                                 g2a d1);
                      val d2 = minus_nata n2 n3;
                      val divisor =
                        (if equal_nata d2 one_nata
                          then times ((times_dvd o dvd_gcd o gcd_Gcd o
gcd_semiring_Gcd o semiring_Gcd_factorial_semiring_gcd o
factorial_semiring_gcd_factorial_ring_gcd)
                                       A1_)
                                 g2a h2
                          else (if dvd (equal_nat, semidom_modulo_nat)
                                     (nat_of_integer (2 : IntInf.int)) d2
                                 then times
((times_dvd o dvd_gcd o gcd_Gcd o gcd_semiring_Gcd o
   semiring_Gcd_factorial_semiring_gcd o
   factorial_semiring_gcd_factorial_ring_gcd)
  A1_)
(uminus
  ((uminus_group_add o group_add_neg_numeral o neg_numeral_ring_1 o
     ring_1_comm_ring_1 o comm_ring_1_idom o idom_idom_divide o
     idom_divide_factorial_ring_gcd)
    A1_)
  g2a)
(binary_power
  ((monoid_mult_semiring_numeral o semiring_numeral_semiring_1 o
     semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
     comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide o
     idom_divide_factorial_ring_gcd)
    A1_)
  h2 d2)
                                 else times
((times_dvd o dvd_gcd o gcd_Gcd o gcd_semiring_Gcd o
   semiring_Gcd_factorial_semiring_gcd o
   factorial_semiring_gcd_factorial_ring_gcd)
  A1_)
g2a (binary_power
      ((monoid_mult_semiring_numeral o semiring_numeral_semiring_1 o
         semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
         comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide o
         idom_divide_factorial_ring_gcd)
        A1_)
      h2 d2)));
                      val g4 =
                        sdiv_poly (A2_, idom_divide_factorial_ring_gcd A1_)
                          pmoda divisor;
                    in
                      resultant_impl_rec_Lazard (A1_, A2_) g3 g4 n3 d2 h2
                    end)
           end)
  end;

fun resultant_impl_main_Lazard (A1_, A2_) g1 g2 =
  (if is_zero
        ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
           semiring_Gcd_factorial_semiring_gcd o
           factorial_semiring_gcd_factorial_ring_gcd)
          A1_)
        g2
    then (if equal_nata
               (degree
                 ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                    semiring_Gcd_factorial_semiring_gcd o
                    factorial_semiring_gcd_factorial_ring_gcd)
                   A1_)
                 g1)
               zero_nata
           then one ((one_gcd o gcd_Gcd o gcd_semiring_Gcd o
                       semiring_Gcd_factorial_semiring_gcd o
                       factorial_semiring_gcd_factorial_ring_gcd)
                      A1_)
           else zero ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                        semiring_Gcd_factorial_semiring_gcd o
                        factorial_semiring_gcd_factorial_ring_gcd)
                       A1_))
    else resultant_impl_start_Lazard (A1_, A2_) g1 g2);

fun resultant_impl_Lazard (A1_, A2_) f g =
  (if less_eq_nat
        (size_list
          (coeffs
            ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
               semiring_Gcd_factorial_semiring_gcd o
               factorial_semiring_gcd_factorial_ring_gcd)
              A1_)
            g))
        (size_list
          (coeffs
            ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
               semiring_Gcd_factorial_semiring_gcd o
               factorial_semiring_gcd_factorial_ring_gcd)
              A1_)
            f))
    then resultant_impl_main_Lazard (A1_, A2_) f g
    else let
           val res = resultant_impl_main_Lazard (A1_, A2_) g f;
         in
           (if dvd (equal_nat, semidom_modulo_nat)
                 (nat_of_integer (2 : IntInf.int))
                 (degree
                   ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                      semiring_Gcd_factorial_semiring_gcd o
                      factorial_semiring_gcd_factorial_ring_gcd)
                     A1_)
                   f) orelse
                 dvd (equal_nat, semidom_modulo_nat)
                   (nat_of_integer (2 : IntInf.int))
                   (degree
                     ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                        semiring_Gcd_factorial_semiring_gcd o
                        factorial_semiring_gcd_factorial_ring_gcd)
                       A1_)
                     g)
             then res
             else uminus
                    ((uminus_group_add o group_add_neg_numeral o
                       neg_numeral_ring_1 o ring_1_comm_ring_1 o
                       comm_ring_1_idom o idom_idom_divide o
                       idom_divide_factorial_ring_gcd)
                      A1_)
                    res)
         end);

fun resultant (A1_, A2_) = resultant_impl_Lazard (A1_, A2_);

fun unit_factor_polya (A1_, A2_, A3_) p =
  pCons ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide)
           A2_,
          A1_)
    (unit_factor (unit_factor_semidom_divide_unit_factor A3_)
      (coeff
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide)
          A2_)
        p (degree
            ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
               semiring_1_comm_semiring_1 o
               comm_semiring_1_comm_semiring_1_cancel o
               comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide)
              A2_)
            p)))
    (zero_polya
      ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
         semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
         comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide)
        A2_));

fun gcd_poly_code (A1_, A2_) p q =
  (if is_zero
        ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
           semiring_Gcd_factorial_semiring_gcd o
           factorial_semiring_gcd_factorial_ring_gcd)
          A1_)
        p
    then normalize_poly
           (A2_, idom_divide_factorial_ring_gcd A1_,
             (semidom_divide_unit_factor_normalization_semidom o
               normalization_semidom_semiring_gcd o semiring_gcd_ring_gcd o
               ring_gcd_factorial_ring_gcd)
               A1_)
           q
    else (if is_zero
               ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                  semiring_Gcd_factorial_semiring_gcd o
                  factorial_semiring_gcd_factorial_ring_gcd)
                 A1_)
               q
           then normalize_poly
                  (A2_, idom_divide_factorial_ring_gcd A1_,
                    (semidom_divide_unit_factor_normalization_semidom o
                      normalization_semidom_semiring_gcd o
                      semiring_gcd_ring_gcd o ring_gcd_factorial_ring_gcd)
                      A1_)
                  p
           else let
                  val c1 =
                    content
                      ((semiring_gcd_ring_gcd o ring_gcd_factorial_ring_gcd)
                        A1_)
                      p;
                  val c2 =
                    content
                      ((semiring_gcd_ring_gcd o ring_gcd_factorial_ring_gcd)
                        A1_)
                      q;
                  val pa =
                    map_poly
                      ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                         semiring_Gcd_factorial_semiring_gcd o
                         factorial_semiring_gcd_factorial_ring_gcd)
                        A1_)
                      ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                         semiring_Gcd_factorial_semiring_gcd o
                         factorial_semiring_gcd_factorial_ring_gcd)
                         A1_,
                        A2_)
                      (fn x =>
                        divide
                          ((divide_divide_trivial o
                             divide_trivial_semidom_divide o
                             semidom_divide_idom_divide o
                             idom_divide_factorial_ring_gcd)
                            A1_)
                          x c1)
                      p;
                  val qa =
                    map_poly
                      ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                         semiring_Gcd_factorial_semiring_gcd o
                         factorial_semiring_gcd_factorial_ring_gcd)
                        A1_)
                      ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
                         semiring_Gcd_factorial_semiring_gcd o
                         factorial_semiring_gcd_factorial_ring_gcd)
                         A1_,
                        A2_)
                      (fn x =>
                        divide
                          ((divide_divide_trivial o
                             divide_trivial_semidom_divide o
                             semidom_divide_idom_divide o
                             idom_divide_factorial_ring_gcd)
                            A1_)
                          x c2)
                      q;
                in
                  smult (A2_, (comm_semiring_0_comm_semiring_1 o
                                comm_semiring_1_comm_semiring_1_cancel o
                                comm_semiring_1_cancel_semidom o semidom_idom o
                                idom_idom_divide o
                                idom_divide_factorial_ring_gcd)
                                A1_,
                          (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
                            semiring_1_no_zero_divisors_semidom o semidom_idom o
                            idom_idom_divide o idom_divide_factorial_ring_gcd)
                            A1_)
                    (gcda ((gcd_Gcd o gcd_semiring_Gcd o
                             semiring_Gcd_factorial_semiring_gcd o
                             factorial_semiring_gcd_factorial_ring_gcd)
                            A1_)
                      c1 c2)
                    (gcd_poly_code_aux (A1_, A2_) pa qa)
                end));

fun gcd_polyc (A1_, A2_, A3_) p q = gcd_poly_code (A1_, A3_) p q;

fun lcm_polya (A1_, A2_, A3_) p q =
  normalize_poly
    (A3_, idom_divide_factorial_ring_gcd A1_,
      (semidom_divide_unit_factor_normalization_semidom o
        normalization_semidom_semiring_gcd o semiring_gcd_ring_gcd o
        ring_gcd_factorial_ring_gcd)
        A1_)
    (divide_polya (A3_, idom_divide_factorial_ring_gcd A1_)
      (karatsuba_mult_poly
        (A3_, (comm_ring_1_idom o idom_idom_divide o
                idom_divide_factorial_ring_gcd)
                A1_,
          (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
            semiring_1_no_zero_divisors_semidom o semidom_idom o
            idom_idom_divide o idom_divide_factorial_ring_gcd)
            A1_)
        p q)
      (gcd_polyc (A1_, A2_, A3_) p q));

fun gcd_polyb (A1_, A2_) x = dummy_Gcd x;

fun times_polya (A1_, A2_, A3_) p q =
  fold_coeffs
    ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_comm_semiring_0) A2_)
    (fn a => fn pa =>
      plus_polya
        ((comm_monoid_add_semiring_0 o semiring_0_comm_semiring_0) A2_, A1_)
        (smult (A1_, A2_, A3_) a q)
        (pCons
          ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_comm_semiring_0)
             A2_,
            A1_)
          (zero ((zero_mult_zero o mult_zero_semiring_0 o
                   semiring_0_comm_semiring_0)
                  A2_))
          pa))
    p (zero_polya
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_comm_semiring_0)
          A2_));

fun one_poly A_ = {one = one_polya A_} : 'a poly one;

fun times_poly (A1_, A2_, A3_) = {times = times_polya (A1_, A2_, A3_)} :
  'a poly times;

fun dvd_poly (A1_, A2_, A3_) =
  {times_dvd = times_poly (A1_, comm_semiring_0_comm_semiring_1 A2_, A3_)} :
  'a poly dvd;

fun gcd_polya (A1_, A2_, A3_) =
  {one_gcd =
     one_poly
       ((comm_semiring_1_comm_semiring_1_cancel o
          comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide o
          idom_divide_factorial_ring_gcd)
         A1_),
    zero_gcd =
      zero_poly
        ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
           semiring_Gcd_factorial_semiring_gcd o
           factorial_semiring_gcd_factorial_ring_gcd)
          A1_),
    dvd_gcd =
      dvd_poly
        (A3_, (comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_semidom o semidom_idom o
                idom_idom_divide o idom_divide_factorial_ring_gcd)
                A1_,
          (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
            semiring_1_no_zero_divisors_semidom o semidom_idom o
            idom_idom_divide o idom_divide_factorial_ring_gcd)
            A1_),
    gcda = gcd_polyc (A1_, A2_, A3_), lcma = lcm_polya (A1_, A2_, A3_)}
  : 'a poly gcda;

fun lcm_poly (A1_, A2_, A3_) x = dummy_Lcm (gcd_poly (A1_, A2_, A3_)) x
and gcd_poly (A1_, A2_, A3_) =
  {gcd_Gcd = gcd_polya (A1_, A2_, A3_), gcd = gcd_polyb (A1_, A2_),
    lcm = lcm_poly (A1_, A2_, A3_)}
  : 'a poly gcd;

fun mult_zero_poly (A1_, A2_, A3_) =
  {times_mult_zero = times_poly (A1_, A2_, A3_),
    zero_mult_zero =
      zero_poly
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_comm_semiring_0)
          A2_)}
  : 'a poly mult_zero;

fun semigroup_mult_poly (A1_, A2_, A3_) =
  {times_semigroup_mult = times_poly (A1_, A2_, A3_)} : 'a poly semigroup_mult;

fun semiring_poly (A1_, A2_, A3_) =
  {ab_semigroup_add_semiring =
     ab_semigroup_add_poly
       ((comm_monoid_add_semiring_0 o semiring_0_comm_semiring_0) A2_, A1_),
    semigroup_mult_semiring = semigroup_mult_poly (A1_, A2_, A3_)}
  : 'a poly semiring;

fun semiring_0_poly (A1_, A2_, A3_) =
  {comm_monoid_add_semiring_0 =
     comm_monoid_add_poly
       ((comm_monoid_add_semiring_0 o semiring_0_comm_semiring_0) A2_, A1_),
    mult_zero_semiring_0 = mult_zero_poly (A1_, A2_, A3_),
    semiring_semiring_0 = semiring_poly (A1_, A2_, A3_)}
  : 'a poly semiring_0;

fun semiring_no_zero_divisors_poly (A1_, A2_, A3_) =
  {semiring_0_semiring_no_zero_divisors = semiring_0_poly (A1_, A2_, A3_)} :
  'a poly semiring_no_zero_divisors;

fun semiring_no_zero_divisors_cancel_poly (A1_, A2_) =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_poly
       (A1_, (comm_semiring_0_comm_semiring_1 o
               comm_semiring_1_comm_semiring_1_cancel o
               comm_semiring_1_cancel_semidom o semidom_idom)
               A2_,
         (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
           semiring_1_no_zero_divisors_semidom o semidom_idom)
           A2_)}
  : 'a poly semiring_no_zero_divisors_cancel;

fun divide_poly (A1_, A2_) = {divide = divide_polya (A1_, A2_)} :
  'a poly divide;

fun divide_trivial_poly (A1_, A2_) =
  {one_divide_trivial =
     one_poly
       ((comm_semiring_1_comm_semiring_1_cancel o
          comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide)
         A2_),
    zero_divide_trivial =
      zero_poly
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide)
          A2_),
    divide_divide_trivial = divide_poly (A1_, A2_)}
  : 'a poly divide_trivial;

fun power_poly (A1_, A2_, A3_) =
  {one_power = one_poly A2_,
    times_power = times_poly (A1_, comm_semiring_0_comm_semiring_1 A2_, A3_)}
  : 'a poly power;

fun monoid_mult_poly (A1_, A2_, A3_) =
  {semigroup_mult_monoid_mult =
     semigroup_mult_poly (A1_, comm_semiring_0_comm_semiring_1 A2_, A3_),
    power_monoid_mult = power_poly (A1_, A2_, A3_)}
  : 'a poly monoid_mult;

fun numeral_poly (A1_, A2_) =
  {one_numeral = one_poly A2_,
    semigroup_add_numeral =
      semigroup_add_poly
        ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1)
           A2_,
          A1_)}
  : 'a poly numeral;

fun semiring_numeral_poly (A1_, A2_, A3_) =
  {monoid_mult_semiring_numeral = monoid_mult_poly (A1_, A2_, A3_),
    numeral_semiring_numeral = numeral_poly (A1_, A2_),
    semiring_semiring_numeral =
      semiring_poly (A1_, comm_semiring_0_comm_semiring_1 A2_, A3_)}
  : 'a poly semiring_numeral;

fun zero_neq_one_poly A_ =
  {one_zero_neq_one = one_poly A_,
    zero_zero_neq_one =
      zero_poly
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1)
          A_)}
  : 'a poly zero_neq_one;

fun semiring_1_poly (A1_, A2_, A3_) =
  {semiring_numeral_semiring_1 = semiring_numeral_poly (A1_, A2_, A3_),
    semiring_0_semiring_1 =
      semiring_0_poly (A1_, comm_semiring_0_comm_semiring_1 A2_, A3_),
    zero_neq_one_semiring_1 = zero_neq_one_poly A2_}
  : 'a poly semiring_1;

fun semiring_1_no_zero_divisors_poly (A1_, A2_, A3_) =
  {semiring_1_semiring_1_no_zero_divisors =
     semiring_1_poly
       (A1_, A2_, semiring_no_zero_divisors_semiring_1_no_zero_divisors A3_),
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_poly
        (A1_, comm_semiring_0_comm_semiring_1 A2_,
          semiring_no_zero_divisors_semiring_1_no_zero_divisors A3_)}
  : 'a poly semiring_1_no_zero_divisors;

fun cancel_semigroup_add_poly (A1_, A2_) =
  {semigroup_add_cancel_semigroup_add =
     semigroup_add_poly (comm_monoid_add_cancel_comm_monoid_add A1_, A2_)}
  : 'a poly cancel_semigroup_add;

fun minus_poly (A1_, A2_) = {minus = minus_polya (A1_, A2_)} : 'a poly minus;

fun cancel_ab_semigroup_add_poly (A1_, A2_) =
  {ab_semigroup_add_cancel_ab_semigroup_add =
     ab_semigroup_add_poly
       ((comm_monoid_add_cancel_comm_monoid_add o
          cancel_comm_monoid_add_ab_group_add)
          A1_,
         A2_),
    cancel_semigroup_add_cancel_ab_semigroup_add =
      cancel_semigroup_add_poly (cancel_comm_monoid_add_ab_group_add A1_, A2_),
    minus_cancel_ab_semigroup_add = minus_poly (A1_, A2_)}
  : 'a poly cancel_ab_semigroup_add;

fun cancel_comm_monoid_add_poly (A1_, A2_) =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add =
     cancel_ab_semigroup_add_poly (A1_, A2_),
    comm_monoid_add_cancel_comm_monoid_add =
      comm_monoid_add_poly
        ((comm_monoid_add_cancel_comm_monoid_add o
           cancel_comm_monoid_add_ab_group_add)
           A1_,
          A2_)}
  : 'a poly cancel_comm_monoid_add;

fun semiring_0_cancel_poly (A1_, A2_, A3_, A4_) =
  {cancel_comm_monoid_add_semiring_0_cancel =
     cancel_comm_monoid_add_poly (A1_, A2_),
    semiring_0_semiring_0_cancel =
      semiring_0_poly (A2_, comm_semiring_0_comm_semiring_0_cancel A3_, A4_)}
  : 'a poly semiring_0_cancel;

fun ab_semigroup_mult_poly (A1_, A2_, A3_) =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_poly (A1_, A2_, A3_)} :
  'a poly ab_semigroup_mult;

fun comm_semiring_poly (A1_, A2_, A3_) =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_poly (A1_, A2_, A3_),
    semiring_comm_semiring = semiring_poly (A1_, A2_, A3_)}
  : 'a poly comm_semiring;

fun comm_semiring_0_poly (A1_, A2_, A3_) =
  {comm_semiring_comm_semiring_0 = comm_semiring_poly (A1_, A2_, A3_),
    semiring_0_comm_semiring_0 = semiring_0_poly (A1_, A2_, A3_)}
  : 'a poly comm_semiring_0;

fun comm_semiring_0_cancel_poly (A1_, A2_, A3_, A4_) =
  {comm_semiring_0_comm_semiring_0_cancel =
     comm_semiring_0_poly
       (A2_, comm_semiring_0_comm_semiring_0_cancel A3_, A4_),
    semiring_0_cancel_comm_semiring_0_cancel =
      semiring_0_cancel_poly (A1_, A2_, A3_, A4_)}
  : 'a poly comm_semiring_0_cancel;

fun semiring_1_cancel_poly (A1_, A2_, A3_) =
  {semiring_0_cancel_semiring_1_cancel =
     semiring_0_cancel_poly
       ((ab_group_add_ring o ring_ring_1 o ring_1_comm_ring_1) A2_, A1_,
         (comm_semiring_0_cancel_comm_ring o comm_ring_comm_ring_1) A2_, A3_),
    semiring_1_semiring_1_cancel =
      semiring_1_poly
        (A1_, (comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_comm_ring_1)
                A2_,
          A3_)}
  : 'a poly semiring_1_cancel;

fun comm_monoid_mult_poly (A1_, A2_, A3_) =
  {ab_semigroup_mult_comm_monoid_mult =
     ab_semigroup_mult_poly (A1_, comm_semiring_0_comm_semiring_1 A2_, A3_),
    monoid_mult_comm_monoid_mult = monoid_mult_poly (A1_, A2_, A3_),
    dvd_comm_monoid_mult = dvd_poly (A1_, A2_, A3_)}
  : 'a poly comm_monoid_mult;

fun comm_semiring_1_poly (A1_, A2_, A3_) =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_poly (A1_, A2_, A3_),
    comm_semiring_0_comm_semiring_1 =
      comm_semiring_0_poly (A1_, comm_semiring_0_comm_semiring_1 A2_, A3_),
    semiring_1_comm_semiring_1 = semiring_1_poly (A1_, A2_, A3_)}
  : 'a poly comm_semiring_1;

fun comm_semiring_1_cancel_poly (A1_, A2_, A3_) =
  {comm_semiring_0_cancel_comm_semiring_1_cancel =
     comm_semiring_0_cancel_poly
       ((ab_group_add_ring o ring_ring_1 o ring_1_comm_ring_1) A2_, A1_,
         (comm_semiring_0_cancel_comm_ring o comm_ring_comm_ring_1) A2_, A3_),
    comm_semiring_1_comm_semiring_1_cancel =
      comm_semiring_1_poly
        (A1_, (comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_comm_ring_1)
                A2_,
          A3_),
    semiring_1_cancel_comm_semiring_1_cancel =
      semiring_1_cancel_poly (A1_, A2_, A3_)}
  : 'a poly comm_semiring_1_cancel;

fun semidom_poly (A1_, A2_) =
  {comm_semiring_1_cancel_semidom =
     comm_semiring_1_cancel_poly
       (A1_, comm_ring_1_idom A2_,
         (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
           semiring_1_no_zero_divisors_semidom o semidom_idom)
           A2_),
    semiring_1_no_zero_divisors_semidom =
      semiring_1_no_zero_divisors_poly
        (A1_, (comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_semidom o semidom_idom)
                A2_,
          (semiring_1_no_zero_divisors_semidom o semidom_idom) A2_)}
  : 'a poly semidom;

fun semidom_divide_poly (A1_, A2_) =
  {divide_trivial_semidom_divide = divide_trivial_poly (A1_, A2_),
    semidom_semidom_divide = semidom_poly (A1_, idom_idom_divide A2_),
    semiring_no_zero_divisors_cancel_semidom_divide =
      semiring_no_zero_divisors_cancel_poly (A1_, idom_idom_divide A2_)}
  : 'a poly semidom_divide;

fun unit_factor_poly (A1_, A2_, A3_) =
  {unit_factor = unit_factor_polya (A1_, A2_, A3_)} : 'a poly unit_factor;

fun semidom_divide_unit_factor_poly (A1_, A2_, A3_) =
  {semidom_divide_semidom_divide_unit_factor = semidom_divide_poly (A1_, A2_),
    unit_factor_semidom_divide_unit_factor = unit_factor_poly (A1_, A2_, A3_)}
  : 'a poly semidom_divide_unit_factor;

fun algebraic_semidom_poly (A1_, A2_) =
  {semidom_divide_algebraic_semidom = semidom_divide_poly (A1_, A2_)} :
  'a poly algebraic_semidom;

fun normalization_semidom_poly (A1_, A2_, A3_) =
  {algebraic_semidom_normalization_semidom = algebraic_semidom_poly (A1_, A2_),
    semidom_divide_unit_factor_normalization_semidom =
      semidom_divide_unit_factor_poly (A1_, A2_, A3_),
    normalizea = normalize_poly (A1_, A2_, A3_)}
  : 'a poly normalization_semidom;

fun factorial_semiring_poly (A1_, A2_, A3_) =
  {normalization_semidom_factorial_semiring =
     normalization_semidom_poly
       (A3_, idom_divide_factorial_ring_gcd A1_,
         (semidom_divide_unit_factor_normalization_semidom o
           normalization_semidom_semiring_gcd o semiring_gcd_ring_gcd o
           ring_gcd_factorial_ring_gcd)
           A1_)}
  : 'a poly factorial_semiring;

fun comm_monoid_gcd_poly (A1_, A2_, A3_) =
  {gcd_comm_monoid_gcd = gcd_polya (A1_, A2_, A3_),
    comm_semiring_1_comm_monoid_gcd =
      comm_semiring_1_poly
        (A3_, (comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_semidom o semidom_idom o
                idom_idom_divide o idom_divide_factorial_ring_gcd)
                A1_,
          (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
            semiring_1_no_zero_divisors_semidom o semidom_idom o
            idom_idom_divide o idom_divide_factorial_ring_gcd)
            A1_)}
  : 'a poly comm_monoid_gcd;

fun semiring_gcd_poly (A1_, A2_, A3_) =
  {normalization_semidom_semiring_gcd =
     normalization_semidom_poly
       (A3_, idom_divide_factorial_ring_gcd A1_,
         (semidom_divide_unit_factor_normalization_semidom o
           normalization_semidom_semiring_gcd o semiring_gcd_ring_gcd o
           ring_gcd_factorial_ring_gcd)
           A1_),
    comm_monoid_gcd_semiring_gcd = comm_monoid_gcd_poly (A1_, A2_, A3_)}
  : 'a poly semiring_gcd;

fun semiring_Gcd_poly (A1_, A2_, A3_) =
  {gcd_semiring_Gcd = gcd_poly (A1_, A2_, A3_),
    semiring_gcd_semiring_Gcd = semiring_gcd_poly (A1_, A2_, A3_)}
  : 'a poly semiring_Gcd;

fun factorial_semiring_gcd_poly (A1_, A2_, A3_) =
  {factorial_semiring_factorial_semiring_gcd =
     factorial_semiring_poly (A1_, A2_, A3_),
    semiring_Gcd_factorial_semiring_gcd = semiring_Gcd_poly (A1_, A2_, A3_)}
  : 'a poly factorial_semiring_gcd;

fun comm_semiring_1_cancel_crossproduct_poly (A1_, A2_) =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
     comm_semiring_1_cancel_poly
       (A1_, comm_ring_1_idom A2_,
         (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
           semiring_1_no_zero_divisors_semidom o semidom_idom)
           A2_)}
  : 'a poly comm_semiring_1_cancel_crossproduct;

fun uminus_poly A_ = {uminus = uminus_polya A_} : 'a poly uminus;

fun group_add_poly (A1_, A2_) =
  {cancel_semigroup_add_group_add =
     cancel_semigroup_add_poly (cancel_comm_monoid_add_ab_group_add A1_, A2_),
    minus_group_add = minus_poly (A1_, A2_),
    monoid_add_group_add =
      monoid_add_poly
        ((comm_monoid_add_cancel_comm_monoid_add o
           cancel_comm_monoid_add_ab_group_add)
           A1_,
          A2_),
    uminus_group_add = uminus_poly A1_}
  : 'a poly group_add;

fun ab_group_add_poly (A1_, A2_) =
  {cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_poly (A1_, A2_),
    group_add_ab_group_add = group_add_poly (A1_, A2_)}
  : 'a poly ab_group_add;

fun ring_poly (A1_, A2_, A3_) =
  {ab_group_add_ring =
     ab_group_add_poly ((ab_group_add_ring o ring_comm_ring) A2_, A1_),
    semiring_0_cancel_ring =
      semiring_0_cancel_poly
        ((ab_group_add_ring o ring_comm_ring) A2_, A1_,
          comm_semiring_0_cancel_comm_ring A2_, A3_)}
  : 'a poly ring;

fun ring_no_zero_divisors_poly (A1_, A2_) =
  {ring_ring_no_zero_divisors =
     ring_poly
       (A1_, (comm_ring_comm_ring_1 o comm_ring_1_idom) A2_,
         (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
           semiring_1_no_zero_divisors_semidom o semidom_idom)
           A2_),
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
      semiring_no_zero_divisors_cancel_poly (A1_, A2_)}
  : 'a poly ring_no_zero_divisors;

fun neg_numeral_poly (A1_, A2_) =
  {group_add_neg_numeral =
     group_add_poly
       ((ab_group_add_ring o ring_ring_1 o ring_1_comm_ring_1) A2_, A1_),
    numeral_neg_numeral =
      numeral_poly
        (A1_, (comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_comm_ring_1)
                A2_)}
  : 'a poly neg_numeral;

fun ring_1_poly (A1_, A2_, A3_) =
  {neg_numeral_ring_1 = neg_numeral_poly (A1_, A2_),
    ring_ring_1 = ring_poly (A1_, comm_ring_comm_ring_1 A2_, A3_),
    semiring_1_cancel_ring_1 = semiring_1_cancel_poly (A1_, A2_, A3_)}
  : 'a poly ring_1;

fun ring_1_no_zero_divisors_poly (A1_, A2_) =
  {ring_1_ring_1_no_zero_divisors =
     ring_1_poly
       (A1_, comm_ring_1_idom A2_,
         (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
           semiring_1_no_zero_divisors_semidom o semidom_idom)
           A2_),
    ring_no_zero_divisors_ring_1_no_zero_divisors =
      ring_no_zero_divisors_poly (A1_, A2_),
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
      semiring_1_no_zero_divisors_poly
        (A1_, (comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_semidom o semidom_idom)
                A2_,
          (semiring_1_no_zero_divisors_semidom o semidom_idom) A2_)}
  : 'a poly ring_1_no_zero_divisors;

fun comm_ring_poly (A1_, A2_, A3_) =
  {comm_semiring_0_cancel_comm_ring =
     comm_semiring_0_cancel_poly
       ((ab_group_add_ring o ring_comm_ring) A2_, A1_,
         comm_semiring_0_cancel_comm_ring A2_, A3_),
    ring_comm_ring = ring_poly (A1_, A2_, A3_)}
  : 'a poly comm_ring;

fun comm_ring_1_poly (A1_, A2_, A3_) =
  {comm_ring_comm_ring_1 = comm_ring_poly (A1_, comm_ring_comm_ring_1 A2_, A3_),
    comm_semiring_1_cancel_comm_ring_1 =
      comm_semiring_1_cancel_poly (A1_, A2_, A3_),
    ring_1_comm_ring_1 = ring_1_poly (A1_, A2_, A3_)}
  : 'a poly comm_ring_1;

fun idom_poly (A1_, A2_) =
  {comm_ring_1_idom =
     comm_ring_1_poly
       (A1_, comm_ring_1_idom A2_,
         (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
           semiring_1_no_zero_divisors_semidom o semidom_idom)
           A2_),
    ring_1_no_zero_divisors_idom = ring_1_no_zero_divisors_poly (A1_, A2_),
    semidom_idom = semidom_poly (A1_, A2_),
    comm_semiring_1_cancel_crossproduct_idom =
      comm_semiring_1_cancel_crossproduct_poly (A1_, A2_)}
  : 'a poly idom;

fun idom_divide_poly (A1_, A2_) =
  {idom_idom_divide = idom_poly (A1_, idom_idom_divide A2_),
    semidom_divide_idom_divide = semidom_divide_poly (A1_, A2_)}
  : 'a poly idom_divide;

fun idom_gcd_poly (A1_, A2_, A3_) =
  {idom_idom_gcd =
     idom_poly (A3_, (idom_idom_divide o idom_divide_factorial_ring_gcd) A1_),
    comm_monoid_gcd_idom_gcd = comm_monoid_gcd_poly (A1_, A2_, A3_)}
  : 'a poly idom_gcd;

fun ring_gcd_poly (A1_, A2_, A3_) =
  {semiring_gcd_ring_gcd = semiring_gcd_poly (A1_, A2_, A3_),
    idom_gcd_ring_gcd = idom_gcd_poly (A1_, A2_, A3_)}
  : 'a poly ring_gcd;

fun factorial_ring_gcd_poly (A1_, A2_, A3_) =
  {factorial_semiring_gcd_factorial_ring_gcd =
     factorial_semiring_gcd_poly (A1_, A2_, A3_),
    ring_gcd_factorial_ring_gcd = ring_gcd_poly (A1_, A2_, A3_),
    idom_divide_factorial_ring_gcd =
      idom_divide_poly (A3_, idom_divide_factorial_ring_gcd A1_)}
  : 'a poly factorial_ring_gcd;

fun poly_div (A1_, A2_, A3_) p q =
  resultant
    (factorial_ring_gcd_poly (A1_, A2_, A3_),
      equal_poly
        ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
           semiring_Gcd_factorial_semiring_gcd o
           factorial_semiring_gcd_factorial_ring_gcd)
           A1_,
          A3_))
    (poly_x_mult_y
      ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
         semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
         comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide o
         idom_divide_factorial_ring_gcd)
         A1_,
        A3_)
      p)
    (poly_lift
      ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
         semiring_Gcd_factorial_semiring_gcd o
         factorial_semiring_gcd_factorial_ring_gcd)
         A1_,
        A3_)
      q);

fun poly_mult (A1_, A2_, A3_) p q =
  poly_div (A1_, A2_, A3_) p
    (reflect_poly
      ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
         semiring_Gcd_factorial_semiring_gcd o
         factorial_semiring_gcd_factorial_ring_gcd)
         A1_,
        A3_)
      q);

fun mult_1_pos (p1, (l1, r1)) (p2, (l2, r2)) =
  select_correct_factor_int_poly (tighten_poly_bounds_binary p1 p2)
    (fn (a, b) =>
      let
        val (l1a, (r1a, _)) = a;
      in
        (fn (l2a, (r2a, _)) => (times_rata l1a l2a, times_rata r1a r2a))
      end
        b)
    ((l1, (r1, sgn_rata
                 (fold_coeffs zero_int
                   (fn a => fn b => plus_rata (of_int a) (times_rata r1 b)) p1
                   zero_rata))),
      (l2, (r2, sgn_rata
                  (fold_coeffs zero_int
                    (fn a => fn b => plus_rata (of_int a) (times_rata r2 b)) p2
                    zero_rata))))
    (poly_mult
      (factorial_ring_gcd_int, semiring_gcd_mult_normalize_int, equal_int) p1
      p2);

fun mult_1 x y =
  let
    val ((_, (_, r1)), (_, (_, r2))) = (x, y);
  in
    (if less_rat zero_rata r1
      then (if less_rat zero_rata r2 then mult_1_pos x y
             else uminus_2 (mult_1_pos x (uminus_1 y)))
      else (if less_rat zero_rata r2 then uminus_2 (mult_1_pos (uminus_1 x) y)
             else mult_1_pos (uminus_1 x) (uminus_1 y)))
  end;

fun mult_2 (Rational r) (Rational q) = Rational (times_rata r q)
  | mult_2 (Rational r) (Irrational (n, y)) = mult_rat_1 r y
  | mult_2 (Irrational (n, x)) (Rational q) = mult_rat_1 q x
  | mult_2 (Irrational (n, x)) (Irrational (m, y)) = mult_1 x y;

fun mult_3 xb xc =
  Real_Alg_Invariant (mult_2 (rep_real_alg_3 xb) (rep_real_alg_3 xc));

fun times_real_alg (Real_Alg_Quotient xa) (Real_Alg_Quotient x) =
  Real_Alg_Quotient (mult_3 xa x);

fun times_reala (Real_of x) (Real_of y) = Real_of (times_real_alg x y);

val times_real = {times = times_reala} : real times;

val dvd_real = {times_dvd = times_real} : real dvd;

fun of_rat_3 xa = Real_Alg_Invariant (Rational xa);

fun of_rat_real_alg x = Real_Alg_Quotient (of_rat_3 x);

val one_real_alg : real_alg = of_rat_real_alg one_rata;

val one_reala : real = Real_of one_real_alg;

val one_real = {one = one_reala} : real one;

fun rai_ub (uu, (uv, r)) = r;

fun sgn_1 x = sgn_rata (rai_ub x);

fun sgn_2 (Rational r) = sgn_rata r
  | sgn_2 (Irrational (n, rai)) = sgn_1 rai;

fun sgn_3 xa = sgn_2 (rep_real_alg_3 xa);

fun sgn_real_alg_rat (Real_Alg_Quotient xa) = sgn_3 xa;

fun sgn_real_alg x = of_rat_real_alg (sgn_real_alg_rat x);

fun sgn_reala (Real_of x) = Real_of (sgn_real_alg x);

val sgn_real = {sgn = sgn_reala} : real sgn;

fun uminus_3 xa = Real_Alg_Invariant (uminus_2 (rep_real_alg_3 xa));

fun uminus_real_alg (Real_Alg_Quotient x) = Real_Alg_Quotient (uminus_3 x);

fun uminus_reala (Real_of x) = Real_of (uminus_real_alg x);

fun pcompose (A1_, A2_, A3_) p q =
  fold_coeffs
    ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_comm_semiring_0) A2_)
    (fn a => fn c =>
      plus_polya
        ((comm_monoid_add_semiring_0 o semiring_0_comm_semiring_0) A2_, A1_)
        (pCons
          ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_comm_semiring_0)
             A2_,
            A1_)
          a (zero_polya
              ((zero_mult_zero o mult_zero_semiring_0 o
                 semiring_0_comm_semiring_0)
                A2_)))
        (times_polya (A1_, A2_, A3_) q c))
    p (zero_polya
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_comm_semiring_0)
          A2_));

fun poly_add_rat r p =
  let
    val (n, d) = quotient_of r;
    val pa =
      let
        val fs = coeffs zero_int p;
        val k = size_list fs;
      in
        poly_of_list (comm_monoid_add_int, equal_int)
          (map (fn (fi, i) =>
                 times_inta fi
                   (binary_power monoid_mult_int d (minus_nata k (suc i))))
            (zip fs (upt zero_nata k)))
      end;
    val pb =
      pcompose (equal_int, comm_semiring_0_int, semiring_no_zero_divisors_int)
        pa (pCons (zero_int, equal_int) (uminus_inta n)
             (pCons (zero_int, equal_int) d (zero_polya zero_int)));
  in
    pb
  end;

fun add_rat_1 r1 (p2, (l2, r2)) =
  let
    val p = cf_pos_poly (poly_add_rat r1 p2);
    val (l, (r, _)) =
      tighten_poly_bounds_for_x p zero_rata (plus_rata l2 r1) (plus_rata r2 r1)
        (sgn_rata
          (fold_coeffs zero_int
            (fn a => fn b =>
              plus_rata (of_int a) (times_rata (plus_rata r2 r1) b))
            p zero_rata));
  in
    (p, (l, r))
  end;

fun x_y (A1_, A2_, A3_) =
  pCons (zero_poly
           ((zero_monoid_add o monoid_add_group_add o group_add_ab_group_add)
             A1_),
          equal_poly
            ((zero_monoid_add o monoid_add_group_add o group_add_ab_group_add)
               A1_,
              A2_))
    (pCons
      ((zero_monoid_add o monoid_add_group_add o group_add_ab_group_add) A1_,
        A2_)
      (zero ((zero_monoid_add o monoid_add_group_add o group_add_ab_group_add)
              A1_))
      (pCons
        ((zero_monoid_add o monoid_add_group_add o group_add_ab_group_add) A1_,
          A2_)
        (one ((one_numeral o numeral_semiring_numeral o
                semiring_numeral_semiring_1 o semiring_1_comm_semiring_1)
               A3_))
        (zero_polya
          ((zero_monoid_add o monoid_add_group_add o group_add_ab_group_add)
            A1_))))
    (pCons
      (zero_poly
         ((zero_monoid_add o monoid_add_group_add o group_add_ab_group_add)
           A1_),
        equal_poly
          ((zero_monoid_add o monoid_add_group_add o group_add_ab_group_add)
             A1_,
            A2_))
      (uminus_polya A1_ (one_polya A3_))
      (zero_polya
        (zero_poly
          ((zero_monoid_add o monoid_add_group_add o group_add_ab_group_add)
            A1_))));

fun poly_x_minus_y (A1_, A2_, A3_, A4_) p =
  pcompose
    (equal_poly
       ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_comm_semiring_0 o
          comm_semiring_0_comm_semiring_1)
          A3_,
         A2_),
      comm_semiring_0_poly (A2_, comm_semiring_0_comm_semiring_1 A3_, A4_),
      semiring_no_zero_divisors_poly
        (A2_, comm_semiring_0_comm_semiring_1 A3_, A4_))
    (poly_lift
      ((zero_monoid_add o monoid_add_group_add o group_add_ab_group_add) A1_,
        A2_)
      p)
    (x_y (A1_, A2_, A3_));

fun poly_add (A1_, A2_, A3_) p q =
  resultant
    (factorial_ring_gcd_poly (A1_, A2_, A3_),
      equal_poly
        ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
           semiring_Gcd_factorial_semiring_gcd o
           factorial_semiring_gcd_factorial_ring_gcd)
           A1_,
          A3_))
    (poly_x_minus_y
      ((ab_group_add_ring o ring_ring_1 o ring_1_comm_ring_1 o
         comm_ring_1_idom o idom_idom_divide o idom_divide_factorial_ring_gcd)
         A1_,
        A3_,
        (comm_semiring_1_comm_semiring_1_cancel o
          comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide o
          idom_divide_factorial_ring_gcd)
          A1_,
        (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
          semiring_1_no_zero_divisors_semidom o semidom_idom o
          idom_idom_divide o idom_divide_factorial_ring_gcd)
          A1_)
      p)
    (poly_lift
      ((zero_gcd o gcd_Gcd o gcd_semiring_Gcd o
         semiring_Gcd_factorial_semiring_gcd o
         factorial_semiring_gcd_factorial_ring_gcd)
         A1_,
        A3_)
      q);

fun add_1 (p1, (l1, r1)) (p2, (l2, r2)) =
  select_correct_factor_int_poly (tighten_poly_bounds_binary p1 p2)
    (fn (a, b) =>
      let
        val (l1a, (r1a, _)) = a;
      in
        (fn (l2a, (r2a, _)) => (plus_rata l1a l2a, plus_rata r1a r2a))
      end
        b)
    ((l1, (r1, sgn_rata
                 (fold_coeffs zero_int
                   (fn a => fn b => plus_rata (of_int a) (times_rata r1 b)) p1
                   zero_rata))),
      (l2, (r2, sgn_rata
                  (fold_coeffs zero_int
                    (fn a => fn b => plus_rata (of_int a) (times_rata r2 b)) p2
                    zero_rata))))
    (poly_add
      (factorial_ring_gcd_int, semiring_gcd_mult_normalize_int, equal_int) p1
      p2);

fun add_2 (Rational r) (Rational q) = Rational (plus_rata r q)
  | add_2 (Rational r) (Irrational (n, x)) = Irrational (n, add_rat_1 r x)
  | add_2 (Irrational (n, x)) (Rational q) = Irrational (n, add_rat_1 q x)
  | add_2 (Irrational (n, x)) (Irrational (m, y)) = add_1 x y;

fun add_3 xb xc =
  Real_Alg_Invariant (add_2 (rep_real_alg_3 xb) (rep_real_alg_3 xc));

fun plus_real_alg (Real_Alg_Quotient xa) (Real_Alg_Quotient x) =
  Real_Alg_Quotient (add_3 xa x);

fun minus_real_alg x y = plus_real_alg x (uminus_real_alg y);

fun minus_reala (Real_of x) (Real_of y) = Real_of (minus_real_alg x y);

val zero_real_alg : real_alg = of_rat_real_alg zero_rata;

val zero_reala : real = Real_of zero_real_alg;

fun plus_reala (Real_of x) (Real_of y) = Real_of (plus_real_alg x y);

val plus_real = {plus = plus_reala} : real plus;

val semigroup_add_real = {plus_semigroup_add = plus_real} : real semigroup_add;

val cancel_semigroup_add_real =
  {semigroup_add_cancel_semigroup_add = semigroup_add_real} :
  real cancel_semigroup_add;

val ab_semigroup_add_real =
  {semigroup_add_ab_semigroup_add = semigroup_add_real} : real ab_semigroup_add;

val minus_real = {minus = minus_reala} : real minus;

val cancel_ab_semigroup_add_real =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_real,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_real,
    minus_cancel_ab_semigroup_add = minus_real}
  : real cancel_ab_semigroup_add;

val zero_real = {zero = zero_reala} : real zero;

val monoid_add_real =
  {semigroup_add_monoid_add = semigroup_add_real, zero_monoid_add = zero_real} :
  real monoid_add;

val comm_monoid_add_real =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_real,
    monoid_add_comm_monoid_add = monoid_add_real}
  : real comm_monoid_add;

val cancel_comm_monoid_add_real =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add =
     cancel_ab_semigroup_add_real,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_real}
  : real cancel_comm_monoid_add;

val mult_zero_real = {times_mult_zero = times_real, zero_mult_zero = zero_real}
  : real mult_zero;

val semigroup_mult_real = {times_semigroup_mult = times_real} :
  real semigroup_mult;

val semiring_real =
  {ab_semigroup_add_semiring = ab_semigroup_add_real,
    semigroup_mult_semiring = semigroup_mult_real}
  : real semiring;

val semiring_0_real =
  {comm_monoid_add_semiring_0 = comm_monoid_add_real,
    mult_zero_semiring_0 = mult_zero_real, semiring_semiring_0 = semiring_real}
  : real semiring_0;

val semiring_0_cancel_real =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_real,
    semiring_0_semiring_0_cancel = semiring_0_real}
  : real semiring_0_cancel;

val ab_semigroup_mult_real =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_real} :
  real ab_semigroup_mult;

val comm_semiring_real =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_real,
    semiring_comm_semiring = semiring_real}
  : real comm_semiring;

val comm_semiring_0_real =
  {comm_semiring_comm_semiring_0 = comm_semiring_real,
    semiring_0_comm_semiring_0 = semiring_0_real}
  : real comm_semiring_0;

val comm_semiring_0_cancel_real =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_real,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_real}
  : real comm_semiring_0_cancel;

val power_real = {one_power = one_real, times_power = times_real} : real power;

val monoid_mult_real =
  {semigroup_mult_monoid_mult = semigroup_mult_real,
    power_monoid_mult = power_real}
  : real monoid_mult;

val numeral_real =
  {one_numeral = one_real, semigroup_add_numeral = semigroup_add_real} :
  real numeral;

val semiring_numeral_real =
  {monoid_mult_semiring_numeral = monoid_mult_real,
    numeral_semiring_numeral = numeral_real,
    semiring_semiring_numeral = semiring_real}
  : real semiring_numeral;

val zero_neq_one_real =
  {one_zero_neq_one = one_real, zero_zero_neq_one = zero_real} :
  real zero_neq_one;

val semiring_1_real =
  {semiring_numeral_semiring_1 = semiring_numeral_real,
    semiring_0_semiring_1 = semiring_0_real,
    zero_neq_one_semiring_1 = zero_neq_one_real}
  : real semiring_1;

val semiring_1_cancel_real =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_real,
    semiring_1_semiring_1_cancel = semiring_1_real}
  : real semiring_1_cancel;

val comm_monoid_mult_real =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_real,
    monoid_mult_comm_monoid_mult = monoid_mult_real,
    dvd_comm_monoid_mult = dvd_real}
  : real comm_monoid_mult;

val comm_semiring_1_real =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_real,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_real,
    semiring_1_comm_semiring_1 = semiring_1_real}
  : real comm_semiring_1;

val comm_semiring_1_cancel_real =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_real,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_real,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_real}
  : real comm_semiring_1_cancel;

val comm_semiring_1_cancel_crossproduct_real =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
     comm_semiring_1_cancel_real}
  : real comm_semiring_1_cancel_crossproduct;

val semiring_no_zero_divisors_real =
  {semiring_0_semiring_no_zero_divisors = semiring_0_real} :
  real semiring_no_zero_divisors;

val semiring_1_no_zero_divisors_real =
  {semiring_1_semiring_1_no_zero_divisors = semiring_1_real,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_real}
  : real semiring_1_no_zero_divisors;

val semiring_no_zero_divisors_cancel_real =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_real}
  : real semiring_no_zero_divisors_cancel;

val uminus_real = {uminus = uminus_reala} : real uminus;

val group_add_real =
  {cancel_semigroup_add_group_add = cancel_semigroup_add_real,
    minus_group_add = minus_real, monoid_add_group_add = monoid_add_real,
    uminus_group_add = uminus_real}
  : real group_add;

val ab_group_add_real =
  {cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_real,
    group_add_ab_group_add = group_add_real}
  : real ab_group_add;

val ring_real =
  {ab_group_add_ring = ab_group_add_real,
    semiring_0_cancel_ring = semiring_0_cancel_real}
  : real ring;

val ring_no_zero_divisors_real =
  {ring_ring_no_zero_divisors = ring_real,
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
      semiring_no_zero_divisors_cancel_real}
  : real ring_no_zero_divisors;

val neg_numeral_real =
  {group_add_neg_numeral = group_add_real, numeral_neg_numeral = numeral_real} :
  real neg_numeral;

val ring_1_real =
  {neg_numeral_ring_1 = neg_numeral_real, ring_ring_1 = ring_real,
    semiring_1_cancel_ring_1 = semiring_1_cancel_real}
  : real ring_1;

val ring_1_no_zero_divisors_real =
  {ring_1_ring_1_no_zero_divisors = ring_1_real,
    ring_no_zero_divisors_ring_1_no_zero_divisors = ring_no_zero_divisors_real,
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
      semiring_1_no_zero_divisors_real}
  : real ring_1_no_zero_divisors;

val comm_ring_real =
  {comm_semiring_0_cancel_comm_ring = comm_semiring_0_cancel_real,
    ring_comm_ring = ring_real}
  : real comm_ring;

val comm_ring_1_real =
  {comm_ring_comm_ring_1 = comm_ring_real,
    comm_semiring_1_cancel_comm_ring_1 = comm_semiring_1_cancel_real,
    ring_1_comm_ring_1 = ring_1_real}
  : real comm_ring_1;

val semidom_real =
  {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_real,
    semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_real}
  : real semidom;

val idom_real =
  {comm_ring_1_idom = comm_ring_1_real,
    ring_1_no_zero_divisors_idom = ring_1_no_zero_divisors_real,
    semidom_idom = semidom_real,
    comm_semiring_1_cancel_crossproduct_idom =
      comm_semiring_1_cancel_crossproduct_real}
  : real idom;

fun inverse_1 (p, (l, r)) =
  real_alg_2
    (abs_int_poly (reflect_poly (zero_int, equal_int) p),
      (inverse_rata r, inverse_rata l));

fun inverse_2 (Rational r) = Rational (inverse_rata r)
  | inverse_2 (Irrational (n, x)) = inverse_1 x;

fun inverse_3 xa = Real_Alg_Invariant (inverse_2 (rep_real_alg_3 xa));

fun inverse_real_alg (Real_Alg_Quotient x) = Real_Alg_Quotient (inverse_3 x);

fun inverse_reala (Real_of x) = Real_of (inverse_real_alg x);

fun divide_real_alg x y = times_real_alg x (inverse_real_alg y);

fun divide_reala (Real_of x) (Real_of y) = Real_of (divide_real_alg x y);

val ufd_real = {idom_ufd = idom_real} : real ufd;

val divide_real = {divide = divide_reala} : real divide;

val divide_trivial_real =
  {one_divide_trivial = one_real, zero_divide_trivial = zero_real,
    divide_divide_trivial = divide_real}
  : real divide_trivial;

val inverse_real = {divide_inverse = divide_real, inverse = inverse_reala} :
  real inverse;

val division_ring_real =
  {inverse_division_ring = inverse_real,
    divide_trivial_division_ring = divide_trivial_real,
    ring_1_no_zero_divisors_division_ring = ring_1_no_zero_divisors_real}
  : real division_ring;

val semidom_divide_real =
  {divide_trivial_semidom_divide = divide_trivial_real,
    semidom_semidom_divide = semidom_real,
    semiring_no_zero_divisors_cancel_semidom_divide =
      semiring_no_zero_divisors_cancel_real}
  : real semidom_divide;

val idom_divide_real =
  {idom_idom_divide = idom_real,
    semidom_divide_idom_divide = semidom_divide_real}
  : real idom_divide;

val field_real =
  {division_ring_field = division_ring_real,
    idom_divide_field = idom_divide_real, ufd_field = ufd_real}
  : real field;

fun nq n = times_nata n n;

fun floor_1 (p, (l, r)) =
  let
    val (la, (ra, sr)) =
      tighten_poly_bounds_epsilon p
        (divide_rata one_rata (of_int (Int_of_integer (2 : IntInf.int)))) l r
        (sgn_rata
          (fold_coeffs zero_int
            (fn a => fn b => plus_rata (of_int a) (times_rata r b)) p
            zero_rata));
    val fr = floor_rat ra;
    val fl = floor_rat la;
    val fra = of_int fr;
  in
    (if equal_inta fr fl then fr
      else let
             val (lb, (_, _)) = tighten_poly_bounds_for_x p fra la ra sr;
           in
             (if less_rat fra lb then fr else fl)
           end)
  end;

fun floor_2 (Rational r) = floor_rat r
  | floor_2 (Irrational (n, rai)) = floor_1 rai;

fun floor_3 xa = floor_2 (rep_real_alg_3 xa);

fun floor_real_alg (Real_Alg_Quotient xa) = floor_3 xa;

fun floor_real (Real_of x) = floor_real_alg x;

fun poly_rata x =
  let
    val (n, d) = quotient_of x;
  in
    pCons (zero_int, equal_int) (uminus_inta n)
      (pCons (zero_int, equal_int) d (zero_polya zero_int))
  end;

fun of_rat_1 x = (poly_rata x, (x, x));

fun real_alg_1 (Rational r) = of_rat_1 r
  | real_alg_1 (Irrational (n, rai)) = rai;

fun root_rat_floor p x =
  let
    val (a, b) = quotient_of x;
  in
    divide_inta
      (root_int_floor p
        (times_inta a (binary_power monoid_mult_int b (minus_nata p one_nata))))
      b
  end;

fun root_rat_ceiling p x = uminus_inta (root_rat_floor p (uminus_rata x));

fun initial_upper_bound n r = of_int (root_rat_ceiling n r);

fun initial_lower_bound n l =
  (if less_eq_rat l one_rata then l else of_int (root_rat_floor n l));

fun tighten_bound_root n cmpx (l, r) =
  let
    val m =
      divide_rata (plus_rata l r) (of_int (Int_of_integer (2 : IntInf.int)));
    val ma = binary_power monoid_mult_rat m n;
  in
    (case cmpx ma of Eq => (m, m) | Lt => (m, r) | Gt => (l, m))
  end;

fun poly_nth_root (A1_, A2_) n p =
  pcompose
    (A1_, (comm_semiring_0_comm_semiring_1 o
            comm_semiring_1_comm_semiring_1_cancel o
            comm_semiring_1_cancel_semidom o semidom_idom)
            A2_,
      (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
        semiring_1_no_zero_divisors_semidom o semidom_idom)
        A2_)
    p (monom
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_semidom o semidom_idom)
           A2_,
          A1_)
        (one ((one_numeral o numeral_neg_numeral o neg_numeral_ring_1 o
                ring_1_comm_ring_1 o comm_ring_1_idom)
               A2_))
        n);

fun comparator_of (A1_, A2_) x y =
  (if less ((ord_preorder o preorder_order o order_linorder) A2_) x y then Lt
    else (if eq A1_ x y then Eq else Gt));

fun compare_rat x = comparator_of (equal_rat, linorder_rat) x;

fun compare_rat_1 x (p, (l, r)) =
  (if less_rat x l then Lt
    else (if less_rat r x then Gt
           else (if equal_rata
                      (sgn_rata
                        (fold_coeffs zero_int
                          (fn a => fn b =>
                            plus_rata (of_int a) (times_rata x b))
                          p zero_rata))
                      (sgn_rata
                        (fold_coeffs zero_int
                          (fn a => fn b =>
                            plus_rata (of_int a) (times_rata r b))
                          p zero_rata))
                  then Gt else Lt)));

fun compare_1_rat rai =
  let
    val p = poly_real_alg_1 rai;
  in
    (if equal_nata (degree zero_int p) one_nata
      then let
             val x =
               fract (uminus_inta
                       (case coeffs zero_int p of [] => zero_inta
                         | x :: _ => x))
                 (coeff zero_int p one_nata);
           in
             (fn y => compare_rat y x)
           end
      else (fn y => compare_rat_1 y rai))
  end;

fun root_pos_1 n (p, (l, r)) =
  select_correct_factor_int_poly
    (tighten_bound_root n (compare_1_rat (p, (l, r)))) (fn x => x)
    (initial_lower_bound n l, initial_upper_bound n r)
    (poly_nth_root (equal_int, idom_int) n p);

fun root_1 n (p, (l, r)) =
  (if equal_nata n zero_nata orelse equal_rata r zero_rata
    then Rational zero_rata
    else (if less_rat zero_rata r then root_pos_1 n (p, (l, r))
           else uminus_2 (root_pos_1 n (uminus_1 (p, (l, r))))));

fun root_2 n x = root_1 n (real_alg_1 x);

fun root_3 xb xc = Real_Alg_Invariant (root_2 xb (rep_real_alg_3 xc));

fun root_real_alg xa (Real_Alg_Quotient x) = Real_Alg_Quotient (root_3 xa x);

fun root n (Real_of x) = Real_of (root_real_alg n x);

fun sqrt x = root (nat_of_integer (2 : IntInf.int)) x;

fun nlin n =
  max ord_nat (nat_of_integer (4 : IntInf.int))
    (nat (floor_real (sqrt (of_nat semiring_1_real n))));

fun ratreal x = (Real_of o of_rat_real_alg) x;

fun fcompose (A1_, A2_) p q r =
  fst (fold_coeffs
        ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
           semiring_1_comm_semiring_1 o comm_semiring_1_comm_semiring_1_cancel o
           comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide o
           idom_divide_field)
          A1_)
        (fn a => fn (c, d) =>
          (plus_polya
             ((comm_monoid_add_semiring_0 o semiring_0_semiring_1 o
                semiring_1_comm_semiring_1 o
                comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_semidom o semidom_idom o
                idom_idom_divide o idom_divide_field)
                A1_,
               A2_)
             (karatsuba_mult_poly
               (A2_, (comm_ring_1_idom o idom_idom_divide o idom_divide_field)
                       A1_,
                 (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
                   semiring_1_no_zero_divisors_semidom o semidom_idom o
                   idom_idom_divide o idom_divide_field)
                   A1_)
               d (pCons
                   ((zero_mult_zero o mult_zero_semiring_0 o
                      semiring_0_semiring_1 o semiring_1_comm_semiring_1 o
                      comm_semiring_1_comm_semiring_1_cancel o
                      comm_semiring_1_cancel_semidom o semidom_idom o
                      idom_idom_divide o idom_divide_field)
                      A1_,
                     A2_)
                   a (zero_polya
                       ((zero_mult_zero o mult_zero_semiring_0 o
                          semiring_0_semiring_1 o semiring_1_comm_semiring_1 o
                          comm_semiring_1_comm_semiring_1_cancel o
                          comm_semiring_1_cancel_semidom o semidom_idom o
                          idom_idom_divide o idom_divide_field)
                         A1_))))
             (karatsuba_mult_poly
               (A2_, (comm_ring_1_idom o idom_idom_divide o idom_divide_field)
                       A1_,
                 (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
                   semiring_1_no_zero_divisors_semidom o semidom_idom o
                   idom_idom_divide o idom_divide_field)
                   A1_)
               q c),
            karatsuba_mult_poly
              (A2_, (comm_ring_1_idom o idom_idom_divide o idom_divide_field)
                      A1_,
                (semiring_no_zero_divisors_semiring_1_no_zero_divisors o
                  semiring_1_no_zero_divisors_semidom o semidom_idom o
                  idom_idom_divide o idom_divide_field)
                  A1_)
              r d))
        p (zero_polya
             ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
                semiring_1_comm_semiring_1 o
                comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_semidom o semidom_idom o
                idom_idom_divide o idom_divide_field)
               A1_),
            one_polya
              ((comm_semiring_1_comm_semiring_1_cancel o
                 comm_semiring_1_cancel_semidom o semidom_idom o
                 idom_idom_divide o idom_divide_field)
                A1_)));

fun newton_at v p t =
  let
    val fp =
      poly comm_semiring_0_real
        (pderiv
          (equal_real, comm_semiring_1_real, semiring_no_zero_divisors_real) p)
        t;
    val f = poly comm_semiring_0_real p t;
  in
    (if equal_reala fp zero_reala then NONE
      else SOME (minus_reala t
                  (divide_reala (times_reala (ratreal (of_int v)) f) fp)))
  end;

fun sign_changes (A1_, A2_, A3_) xs =
  minus_nata
    (size_list
      (remdups_adj A3_
        (filter (fn x => not (eq A3_ x (zero A2_))) (map (sgn A1_) xs))))
    one_nata;

fun descartes_roots_test_sc a b p =
  sign_changes (sgn_real, zero_real, equal_real)
    (coeffs zero_real
      (fcompose (field_real, equal_real) p
        (pCons (zero_real, equal_real) a
          (pCons (zero_real, equal_real) b (zero_polya zero_real)))
        (pCons (zero_real, equal_real) one_reala
          (pCons (zero_real, equal_real) one_reala (zero_polya zero_real)))));

fun dsc_main_exec p todo acc =
  (case todo of [] => acc
    | (a, b) :: todoa =>
      let
        val v = descartes_roots_test_sc a b p;
      in
        (if equal_nata v zero_nata then dsc_main_exec p todoa acc
          else (if equal_nata v one_nata
                 then dsc_main_exec p todoa ((a, b) :: acc)
                 else let
                        val m =
                          divide_reala (plus_reala a b)
                            (ratreal
                              (of_int (Int_of_integer (2 : IntInf.int))));
                        val c =
                          (if equal_reala (poly comm_semiring_0_real p m)
                                zero_reala
                            then (m, m) :: acc else acc);
                      in
                        dsc_main_exec p ((a, m) :: (m, b) :: todoa) c
                      end))
      end);

fun dsc_exec a b p = dsc_main_exec p [(a, b)] [];

fun snap_window a b n lam =
  let
    val w = minus_reala b a;
    val s = times_nata (nat_of_integer (4 : IntInf.int)) n;
    val step = divide_reala w (of_nat semiring_1_real s);
    val k0 =
      floor_real
        (times_reala (of_nat semiring_1_real s)
          (divide_reala (minus_reala lam a) w));
    val k =
      max ord_int (Int_of_integer (2 : IntInf.int))
        (min ord_int
          (minus_inta (int_of_nat s) (Int_of_integer (2 : IntInf.int))) k0);
    val kn = nat k;
  in
    (plus_reala a
       (times_reala
         (of_nat semiring_1_real
           (minus_nata kn (nat_of_integer (2 : IntInf.int))))
         step),
      plus_reala a
        (times_reala
          (of_nat semiring_1_real
            (plus_nata kn (nat_of_integer (2 : IntInf.int))))
          step))
  end;

fun mk_int x = Int_of_integer x;

fun mk_nat x = nat_of_integer x;

fun mk_rat n d = fract (mk_int n) (mk_int d);

fun mk_real k = ratreal (of_int (mk_int k));

fun try_newton_sc a b n p v =
  let
    val l1 = newton_at v p a;
    val l2 = newton_at v p b;
  in
    (case l1
      of NONE =>
        (case l2 of NONE => NONE
          | SOME lam2 =>
            let
              val i2 = snap_window a b n lam2;
              val x = descartes_roots_test_sc (fst i2) (snd i2) p;
            in
              (if equal_inta (int_of_nat x) v then SOME i2 else NONE)
            end)
      | SOME lam1 =>
        let
          val i1 = snap_window a b n lam1;
          val x = descartes_roots_test_sc (fst i1) (snd i1) p;
        in
          (if equal_inta (int_of_nat x) v then SOME i1
            else (case l2 of NONE => NONE
                   | SOME lam2 =>
                     let
                       val i2 = snap_window a b n lam2;
                       val xa = descartes_roots_test_sc (fst i2) (snd i2) p;
                     in
                       (if equal_inta (int_of_nat xa) v then SOME i2 else NONE)
                     end))
        end)
  end;

fun try_blocks_sc a b n p v =
  let
    val w = minus_reala b a;
    val b1 = (a, plus_reala a (divide_reala w (of_nat semiring_1_real n)));
    val b2 = (minus_reala b (divide_reala w (of_nat semiring_1_real n)), b);
    val x = descartes_roots_test_sc (fst b1) (snd b1) p;
    val xa = descartes_roots_test_sc (fst b2) (snd b2) p;
  in
    (if equal_inta (int_of_nat x) v then SOME b1
      else (if equal_inta (int_of_nat xa) v then SOME b2 else NONE))
  end;

fun newdsc_main_exec p todo acc =
  (case todo of [] => acc
    | (a, (b, n)) :: todoa =>
      let
        val x = descartes_roots_test_sc a b p;
      in
        (if equal_inta (int_of_nat x) zero_inta
          then newdsc_main_exec p todoa acc
          else (if equal_inta (int_of_nat x) one_inta
                 then newdsc_main_exec p todoa ((a, b) :: acc)
                 else (case try_blocks_sc a b n p (int_of_nat x)
                        of NONE =>
                          (case try_newton_sc a b n p (int_of_nat x)
                            of NONE =>
                              let
                                val m =
                                  divide_reala (plus_reala a b)
                                    (ratreal
                                      (of_int
(Int_of_integer (2 : IntInf.int))));
                                val na = nlin n;
                                val c =
                                  (if equal_reala
(poly comm_semiring_0_real p m) zero_reala
                                    then (m, m) :: acc else acc);
                              in
                                newdsc_main_exec p
                                  ((a, (m, na)) :: (m, (b, na)) :: todoa) c
                              end
                            | SOME i =>
                              newdsc_main_exec p
                                ((fst i, (snd i, nq n)) :: todoa) acc)
                        | SOME i =>
                          newdsc_main_exec p ((fst i, (snd i, nq n)) :: todoa)
                            acc)))
      end);

fun newdsc_exec a b n p = newdsc_main_exec p [(a, (b, n))] [];

fun poly_int ks = poly_of_list (comm_monoid_add_int, equal_int) (map mk_int ks);

fun poly_rat ks =
  poly_of_list (comm_monoid_add_rat, equal_rat)
    (map (fn k => fract (Int_of_integer k) one_inta) ks);

fun isolate_of_2_main p ri cr todo acc =
  (case todo of [] => acc
    | (l, r) :: todoa =>
      let
        val c = cr l r;
      in
        (if equal_nata c zero_nata then isolate_of_2_main p ri cr todoa acc
          else (if equal_nata c one_nata
                 then isolate_of_2_main p ri cr todoa ((l, r) :: acc)
                 else let
                        val m =
                          divide_rata (plus_rata l r)
                            (of_int (Int_of_integer (2 : IntInf.int)));
                      in
                        isolate_of_2_main p ri cr ((m, r) :: (l, m) :: todoa)
                          acc
                      end))
      end);

fun isolate l r p = let
                      val ri = root_info p;
                      val cr = l_r ri;
                    in
                      isolate_of_2_main p ri cr [(l, r)] []
                    end;

fun of_inta A_ k =
  (if equal_inta k zero_inta
    then zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
                 semiring_1_semiring_1_cancel o semiring_1_cancel_ring_1)
                A_)
    else (if less_int k zero_inta
           then uminus
                  ((uminus_group_add o group_add_neg_numeral o
                     neg_numeral_ring_1)
                    A_)
                  (of_inta A_ (uminus_inta k))
           else let
                  val l =
                    times ((times_power o power_monoid_mult o
                             monoid_mult_semiring_numeral o
                             semiring_numeral_semiring_1 o
                             semiring_1_semiring_1_cancel o
                             semiring_1_cancel_ring_1)
                            A_)
                      (numeral ((numeral_neg_numeral o neg_numeral_ring_1) A_)
                        (Bit0 One))
                      (of_inta A_
                        (divide_inta k (Int_of_integer (2 : IntInf.int))));
                  val j = modulo_inta k (Int_of_integer (2 : IntInf.int));
                in
                  (if equal_inta j zero_inta then l
                    else plus ((plus_semigroup_add o semigroup_add_numeral o
                                 numeral_neg_numeral o neg_numeral_ring_1)
                                A_)
                           l (one ((one_numeral o numeral_neg_numeral o
                                     neg_numeral_ring_1)
                                    A_)))
                end));

fun poly_real ks =
  poly_of_list (comm_monoid_add_real, equal_real)
    (map (of_inta ring_1_real o mk_int) ks);

end; (*struct Bench_Gen*)
