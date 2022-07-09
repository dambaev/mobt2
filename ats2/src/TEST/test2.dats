#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
//#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
staload UN="prelude/SATS/unsafe.sats"


fun from( n: int, step: int): stream_vt( int) = $ldelay( stream_vt_cons( n, from( n+step, step)))
fun from1( n: int, step: int):<!laz> stream( int) = $delay( stream_cons( n, from1( n+step, step)))

fun
  sieve
  ( ns: stream_vt( int)
  ): stream_vt( int) = $ldelay
  (
    let
      val ns_con = !ns
      val-@stream_vt_cons(n0, ns1) = ns_con
      val n0_val = n0
      val ns1_val = ns1
      val () = ns1 := sieve( stream_vt_filter_cloptr<int>( ns1_val, lam x=> x mod n0_val > 0))
      prval () = fold@(ns_con)
    in
     ns_con
    end
  ,
    ~ns
  )


fun
  {a:t0p}
  stream_vt_take_while
  ( xs: stream_vt( INV(a))
  , pred: (&a) -<cloptr1> bool
  ):<cloptr1>
  stream_vt( a) = auxmain( xs, pred) where
{
  fun
  auxmain
  ( xs: stream_vt(a)
  , pred: (&a) -<cloptr1> bool
  ) : stream_vt(a) = $ldelay
  (
    auxmain_con(xs, pred)
  ,
    ( ~xs
    ; cloptr_free($UN.castvwtp0{cloptr0}(pred))
    )
  )
  and
  auxmain_con
  ( xs: stream_vt(a)
  , pred: (&a) -<cloptr1> bool
  ) : stream_vt_con(a) =
  (
  let
    val xs_con = !xs
  in
  case+ xs_con of
  | ~stream_vt_nil() =>
    let
      val () = cloptr_free ($UN.castvwtp0{cloptr0}(pred))
    in
      stream_vt_nil()
    end
  | @stream_vt_cons(x0, xs1) =>
    let
      val test = pred(x0)
    in
      if test
        then xs_con where {
          val () = xs1 := auxmain(xs1, pred)
          val () = fold@{a}(xs_con)
        }
        else stream_vt_nil() where {
          val () = stream_vt_free( xs1)
          val () = free@{a}(xs_con)
          val () = cloptr_free ($UN.castvwtp0{cloptr0}(pred))
        }
    end
  end
  )
}

fun
  {a:t0p}
  stream_take_while
  ( xs: stream( INV(a))
  , pred: (a) -<cloref1> bool
  ):<cloref1>
  stream( a) = auxmain( xs, pred) where
{
  fun
  auxmain
  ( xs: stream(a)
  , pred: (a) -<cloref1> bool
  ) : stream(a) = $delay
  (
    auxmain_con(xs, pred)
  )
  and
  auxmain_con
  ( xs: stream(a)
  , pred: (a) -<cloref1> bool
  ) : stream_con(a) =
  (
  let
    val xs_con = !xs
  in
  case+ xs_con of
  | stream_nil() =>
    let
    in
      stream_nil()
    end
  | stream_cons(x0, xs1) =>
    let
      val test = pred(x0)
    in
      if test
        then stream_cons( x0, $delay (auxmain_con(xs1, pred)))
        else stream_nil()
    end
  end
  )
}

fn isPrime( x:int, primes: !stream(int)): bool = loop( primes) where {
  fun
    loop
    ( xs: !stream(int)
    ): bool =
  let
    val xs_con = !xs
  in
    case+ xs_con of
    | stream_nil() => true
    | stream_cons( x0, xs1) =>
      let
        val x0pow2 = g0int_npow( x0, 2)
      in
        if x0pow2 > x
        then true
        else
          if (x mod x0) = 0
          then false
          else loop( xs1)
      end
  end
}

/*
fn isPrime( primes: !stream_vt(int), x: int): bool = result where {
  fun
    loop
    ( xs: !stream_vt(int)
    ): bool =
  let
    val xs_con = !xs
  in
    case+ xs_con of
    | ~stream_vt_nil() => true where {
      val () = xs := $ldelay( stream_vt_nil())
    }
    | @stream_vt_cons( x0, xs1) =>
      let
        val x0pow2 = g0int_npow( x0, 2)
      in
        if x0pow2 > x
        then true where {
          val () = xs1 := $ldelay( xs_con)
          val () = fold@(xs_con)
        }
        else
          if (x mod x0) = 0
          then false
          else loop( xs1)
      end
  end
  val result = loop( primes)
}
*/

//val rec primes: stream(int) = $delay (stream_cons( 2, $delay (stream_cons( 3, stream_filter_fun<int>( from1( 5, 2), lam x =<fun> $effmask{1} isPrime(primes, x))))))

fn primes(): stream(int) = result where {
  fun
    loop
    ( from: int
    , step: int
    , primes: !stream(int)
    ): stream_con(int) =
  if isPrime( from, primes)
  then stream_cons( from, $delay( loop( from + step, step, primes))) where {
  }
  else loop( from + step, step, primes)
  val rec result = $delay (stream_cons( 2, $delay (stream_cons( 3, $delay( loop( 5, 2, result))))))
}

implement main0() = () where {
  val pow2_24 = g0int_npow( 2, 24)
  val primes = sieve( $ldelay( stream_vt_cons( 2, $ldelay( stream_vt_cons( 3, from( 5,2))))))
  val thePrimes = stream_vt_take_while( primes, lam x => x <= pow2_24 )
  val () = println!( stream_vt_length( thePrimes))
}
