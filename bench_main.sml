structure B = Bench_Gen

(* ============================================================
   timing helpers
   ============================================================ *)

val sink : int ref = ref 0

fun ms (t: Time.time) : real =
  Real.fromLargeInt (Time.toMilliseconds t)

fun time_it (name: string) (th: unit -> int) : unit =
  let
    val rt = Timer.startRealTimer()
    val ct = Timer.startCPUTimer()
    val k  = th()
    val wall = Timer.checkRealTimer rt
    val {usr, sys} = Timer.checkCPUTimer ct
    val _ = sink := (!sink + k)
  in
    print (String.concat [
      name, ",",
      Real.toString (ms wall), ",",
      Real.toString (ms usr), ",",
      Real.toString (ms sys), ",",
      Int.toString (!sink), "\n"
    ])
  end

fun repeatN (n: int) (f: unit -> int) : int =
  let
    fun go (0, acc) = acc
      | go (k, acc) = go (k-1, acc + f())
  in
    go (n, 0)
  end

(* ============================================================
   IntInf polynomial arithmetic on coeff lists (constant term first)
   ============================================================ *)

fun iabs (x: IntInf.int) = if x < 0 then ~x else x

fun trim (cs: IntInf.int list) : IntInf.int list =
  let
    fun dropz [] = []
      | dropz (0::xs) = dropz xs
      | dropz xs = xs
    val revd = dropz (List.rev cs)
  in
    List.rev revd
  end

fun addPoly (as_: IntInf.int list) (bs: IntInf.int list) : IntInf.int list =
  let
    fun go (xs, ys) =
      case (xs, ys) of
          ([], ys') => ys'
        | (xs', []) => xs'
        | (x::xs', y::ys') => (x+y) :: go (xs', ys')
  in
    trim (go (as_, bs))
  end

fun subPoly (as_: IntInf.int list) (bs: IntInf.int list) : IntInf.int list =
  let
    fun go (xs, ys) =
      case (xs, ys) of
          ([], ys') => List.map (fn y => ~y) ys'
        | (xs', []) => xs'
        | (x::xs', y::ys') => (x-y) :: go (xs', ys')
  in
    trim (go (as_, bs))
  end

fun smult (c: IntInf.int) (cs: IntInf.int list) : IntInf.int list =
  if c = 0 then [0] else trim (List.map (fn x => c*x) cs)

(* --- FIXED mulPoly: uses vectors, no weird patterns --- *)
fun mulPoly (as_: IntInf.int list) (bs: IntInf.int list) : IntInf.int list =
  let
    val a = trim as_
    val b = trim bs
  in
    if a = [0] orelse b = [0] then [0]
    else
      let
        val la = List.length a
        val lb = List.length b
        val av = Vector.fromList a
        val bv = Vector.fromList b

        fun coeff (k:int) : IntInf.int =
          let
            val i0 = Int.max (0, k - (lb - 1))
            val i1 = Int.min (la - 1, k)
            fun loop (i:int, acc:IntInf.int) =
              if i > i1 then acc
              else loop (i+1, acc + Vector.sub(av, i) * Vector.sub(bv, k - i))
          in
            loop (i0, 0)
          end
      in
        trim (List.tabulate (la + lb - 1, coeff))
      end
  end

fun powPoly (p: IntInf.int list) (e: int) : IntInf.int list =
  if e < 0 then raise Fail "powPoly: negative exponent"
  else if e = 0 then [1]
  else
    let
      fun loop (k:int, acc:IntInf.int list, base:IntInf.int list) =
        if k = 0 then acc
        else if k mod 2 = 1 then loop (k div 2, mulPoly acc base, mulPoly base base)
        else loop (k div 2, acc, mulPoly base base)
    in
      loop (e, [1], trim p)
    end

(* Cauchy bound: |x| <= 1 + ceil(max_{i<deg} |a_i| / |a_deg|) *)
fun cauchy_bound (cs: IntInf.int list) : IntInf.int =
  let
    val ts = trim cs
    val deg = List.length ts - 1
    val lead = List.nth (ts, deg) handle _ => 0
    val alead = iabs lead
    fun maxabs [] m = m
      | maxabs (x::xs) m =
          let val ax = iabs x
          in maxabs xs (if ax > m then ax else m) end
    val maxRest =
      if deg <= 0 then 0
      else maxabs (List.take (ts, deg)) 0
    fun ceil_div (a: IntInf.int) (b: IntInf.int) : IntInf.int =
      if b <= 0 then raise Fail "ceil_div: nonpositive b"
      else if a = 0 then 0
      else (a + b - 1) div b
    val frac = if alead = 0 then maxRest else ceil_div maxRest alead
  in
    1 + frac
  end

fun pow2 (k:int) : IntInf.int =
  IntInf.<< (1, Word.fromInt k)

(* ============================================================
   Families: Mignotte (hard for Sturm, good for Newton–Descartes)
   ============================================================ *)

(* p(x) = x^n - 2(ax - 1)^2 = x^n - 2a^2 x^2 + 4a x - 2
   Coeff list is constant term first.
   For n>=3 and a even, Eisenstein with prime 2 => irreducible over Z[x]. *)
fun mignotte (n:int, tau:int) : IntInf.int list =
  if n < 3 then raise Fail "mignotte: need n >= 3"
  else if tau < 1 then raise Fail "mignotte: need tau >= 1 (a even)"
  else
    let
      val a  : IntInf.int = pow2 tau
      val a2 : IntInf.int = a * a
      val c0 : IntInf.int = ~2                      (* -2 *)
      val c1 : IntInf.int = 4 * a                   (* 4a *)
      val c2 : IntInf.int = ~(2 * a2)               (* -2a^2 *)
    in
      trim (List.tabulate (n+1, fn i =>
        if i = 0 then c0
        else if i = 1 then c1
        else if i = 2 then c2
        else if i = n then 1
        else 0))
    end

(* Variant: p(x) = x^n - 2(a x^k - 1)^2
   = x^n - 2a^2 x^{2k} + 4a x^k - 2.
   Still Eisenstein at 2 if tau>=1. Require n > 2k so deg is n. *)
fun mignotteK (n:int, k:int, tau:int) : IntInf.int list =
  if n < 3 then raise Fail "mignotteK: need n >= 3"
  else if k < 1 then raise Fail "mignotteK: need k >= 1"
  else if n <= 2*k then raise Fail "mignotteK: need n > 2*k"
  else if tau < 1 then raise Fail "mignotteK: need tau >= 1 (a even)"
  else
    let
      val a  : IntInf.int = pow2 tau
      val a2 : IntInf.int = a * a
      val c0 : IntInf.int = ~2                      (* -2 *)
      val ck : IntInf.int = 4 * a                   (* 4a at x^k *)
      val c2k: IntInf.int = ~(2 * a2)               (* -2a^2 at x^{2k} *)
    in
      trim (List.tabulate (n+1, fn i =>
        if i = 0 then c0
        else if i = k then ck
        else if i = 2*k then c2k
        else if i = n then 1
        else 0))
    end

(* ============================================================
   Family: 2 real roots, Sturm-expensive, Eisenstein(2) irreducible
   p(x) = x^(2n) + Σ_{i=1..n-1} 2(2^tau + i) x^(2i) - 2
   Coeff list constant term first.
   Preconditions: n >= 2, tau >= 1.
   Result has exactly two real roots (±r).
   ============================================================ *)

fun twoRootEisenstein (n:int, tau:int) : IntInf.int list =
  if n < 2 then raise Fail "twoRootEisenstein: need n >= 2"
  else if tau < 1 then raise Fail "twoRootEisenstein: need tau >= 1 (Eisenstein at 2)"
  else
    let
      val deg = 2*n
      val base : IntInf.int = pow2 tau  (* 2^tau *)

      fun coeff (j:int) : IntInf.int =
        if j = 0 then ~2
        else if j = deg then 1
        else if j mod 2 = 0 then
          let
            val i = j div 2
          in
            if 1 <= i andalso i <= n-1 then
              let
                val ci = base + IntInf.fromInt i  (* 2^tau + i *)
              in
                2 * ci
              end
            else 0
          end
        else 0
    in
      trim (List.tabulate (deg + 1, coeff))
    end

(* ============================================================
   Robust fraction -> integer coefficient conversion
   ============================================================ *)

fun igcd (a:IntInf.int) (b:IntInf.int) =
  let
    fun go (x,y) = if y = 0 then x else go (y, IntInf.mod(x,y))
    val a' = if a < 0 then ~a else a
    val b' = if b < 0 then ~b else b
  in
    go (a', b')
  end

fun ilcm (a:IntInf.int) (b:IntInf.int) =
  if a = 0 orelse b = 0 then 0
  else (a div (igcd a b)) * b

(* each coefficient is (num, den) with den > 0 *)
fun clear_denoms (qs : (IntInf.int * IntInf.int) list) : IntInf.int list =
  let
    val denLCM = foldl (fn ((_,d), acc) => ilcm acc d) 1 qs
    fun scale (n,d) = n * (denLCM div d)
  in
    trim (map scale qs)
  end

val P1_fracs =
  [ (~85,68), (70,5), (88,79), (29,75), (80,51), (~66,52), (9,71),
    (~14,61), (~27,64), (~100,83), (1,53), (~23,85), (83,98), (48,16),
    (~89,25), (~100,5), (36,28), (1,1), (43,99), (~29,32), (74,97),
    (9,5), (20,70), (~89,27), (~33,48), (16,33), (84,63), (96,89),
    (22,69), (95,97) ]

val P1_coeffs : IntInf.int list = clear_denoms P1_fracs

val P2_coeffs : IntInf.int list =
  [ ~34, ~28, 5, ~39, 83, ~89, ~49, 94, ~66, 18, 75, 84, ~98, ~68, 12,
    46, ~43, 98, 24, ~30, 10, ~88, 54, 79, ~29, 12, ~55, ~46, ~18, 50 ]

val P3_fracs =
  [ (9,30), (~65,82), (~94,68), (9,33), (~56,83), (~22,35), (73,31), (69,2),
    (~58,43), (71,22), (~75,44), (2,49), (24,40), (33,62), (~17,2), (~39,82),
    (~55,43), (~26,47), (46,4), (~48,26), (35,83), (~50,100), (~60,65), (66,36),
    (~43,76), (30,24), (18,28), (~96,51), (49,42), (~41,89), (81,90), (~65,57),
    (~70,64), (~50,26), (91,40), (52,68), (~91,99), (~79,59), (15,93), (~56,42),
    (~20,59), (50,62), (~27,77), (28,53), (~36,75) ]

val P3_coeffs : IntInf.int list = clear_denoms P3_fracs

val P4_coeffs : IntInf.int list =
  [ ~20, ~6, ~50, ~95, 35, ~64, 77, ~56, 18, ~94, ~74, ~69, ~62, ~93, ~4,
    ~41, ~47, ~48, ~95, ~41, 29, 76, 70, ~67, ~91, ~93, ~55, ~34, ~67, ~61,
    ~8, 32, 8, ~33, ~27, ~8, 88, 53, ~28, ~66, ~72, ~46, 15, ~19, 29 ]


(* ============================================================
   Test cases
   ============================================================ *)

type testcase = {name: string, coeffs: IntInf.int list}

val cases : testcase list =
  [
    { name = "pdf_P1", coeffs = P1_coeffs },
    { name = "pdf_P2", coeffs = P2_coeffs },
    { name = "pdf_P4", coeffs = P4_coeffs },
    { name = "pdf_P3", coeffs = P3_coeffs },
    { name = "mignotte_n16_tau32",   coeffs = mignotte (16, 32)  },
    { name = "mignotte_n32_tau16",   coeffs = mignotte (32, 16)  },
    { name = "mignotte_n32_tau32",   coeffs = mignotte (32, 32)  },
    { name = "mignotte_n8_tau128",   coeffs = mignotte (8, 128)  }
  ]






(* ============================================================
   Run
   ============================================================ *)

val iters : int = 1
val two : B.nat = B.mk_nat 2

val zero_real : B.real B.zero = {zero = B.mk_real 0}

fun run_case ({name, coeffs}: testcase) : unit =
  let
    val coeffs' = trim coeffs
    val deg = List.length coeffs' - 1

    val bound : IntInf.int = cauchy_bound coeffs'

    val p_int  : B.int B.poly  = B.poly_int coeffs'
    val p_rat  : B.rat B.poly  = B.poly_rat coeffs'
    val p_real : B.real B.poly = B.poly_real coeffs'

    val a_rat  : B.rat  = B.mk_rat (~bound) 1
    val b_rat  : B.rat  = B.mk_rat bound 1
    val a_real : B.real = B.mk_real (~bound)
    val b_real : B.real = B.mk_real bound

    (* dsc_tr_cache needs p = degree P *)
    val degP : B.nat = B.degree zero_real p_real
  in
    print (String.concat [
      "--- case ", name,
      " (deg=", Int.toString deg,
      ", bound=", IntInf.toString bound,
      ") ---\n"
    ]);

    print "starting isolate...\n";
    time_it (name ^ "_isolate") (fn () =>
      repeatN iters (fn () =>
        List.length (B.isolate a_rat b_rat p_int)));

    print "starting dsc_tr_sc...\n";
    time_it (name ^ "_dsc_exec") (fn () =>
      repeatN iters (fn () =>
        List.length (B.dsc_exec a_real b_real p_real)));
    
    print "starting newdsc_exec...\n";
    time_it (name ^ "_newdsc_exec") (fn () =>
      repeatN iters (fn () =>
        List.length (B.newdsc_exec a_real b_real two p_real)));

    ()
  end

val _ =
  ( print "name,wall_ms,usr_ms,sys_ms,checksum\n"
  ; List.app run_case cases
  )
