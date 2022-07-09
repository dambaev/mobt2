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

/*
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
*/

/*
fn
  isPrime
  ( primes: stream_vt(int)
  , x: int
  ):
  (stream_vt(int), bool) = (primes, result) where {
  fun
    loop
    ( xs: stream_vt(int)
    , result: &bool? >> bool
    ): stream_vt_con(int) =
  let
    val xs_con = !xs
  in
    case+ xs_con of
    | ~stream_vt_nil() => stream_vt_nil() where {
      val () = result := true
    }
    | @stream_vt_cons( x0, xs1) =>
      let
        val x0pow2 = g0int_npow( x0, 2)
      in
        if x0pow2 > x
        then xs_con where {
          val () = result := false
          val () = xs1 := xs1
          prval () = fold@(xs_con)
        }
        else
          if (x mod x0) = 0
          then xs_con where {
            val () = result := false
            prval () = fold@(xs_con)
          }
          else xs_con where {
            val () = xs1 := loop( xs1, result)
            prval () = fold@(xs_con)
          }
      end
  end
  var result: bool?
  val primes = loop( primes, result)
}
*/

fun
  isPrime
  ( xs: stream_vt( int)
  , x: int
  ):<cloptr1>
  ( stream_vt( int)
  , bool
  ) = ( primes1, result) where
{
  val () = println!("isPrime")
  var primes1: ptr
  fun
  auxmain_con
  ( xs: stream_vt(int)
  , x: int
  , primes: &ptr? >> stream_vt(int)
  ) : bool =
  (
  let
    val () = println!("auxmain_con")
  in
  case+ !xs of
  | ~stream_vt_nil() => true where {
      val () = primes := $ldelay stream_vt_nil()
    }
  | ~stream_vt_cons(x0, xs1) => auxmain_con( xs1, x, hole) where {
    var tmp: ptr
    val () = tmp := stream_vt_cons( x0, _)
    val+stream_vt_cons( _, hole) = tmp
    val () = primes := $ldelay tmp
    prval _ = $showtype tmp
  }
    /*
    let
      val () = println!("isPrime: ", x0)
      val x0pow2 = g0int_npow( x0, 2)
    in
      if x0pow2 > x
      then true where {
          val () = primes := xs_con
      }
      else
        if (x mod x0) = 0
        then false where {
          val () = primes := xs_con
        }
        else auxmain_con(xs1, x, hole) where {
          val () = primes := $ldelay xs_con
          val+stream_vt_cons(_, hole) = !primes
        }
    end
    */
  end
  )
  val result = auxmain_con( xs, x, primes1)
  val () = println!( "isPrime: end")
}
fn primes(): stream_vt(int) = $ldelay (loop( 5,2, $ldelay (stream_vt_cons( 2, $ldelay (stream_vt_cons( 3, $ldelay( stream_vt_nil()))))))) where {
  fun
    loop
    ( from: int
    , step: int
    , primes: stream_vt(int)
    ): stream_vt_con(int) =
  let
    val () = println!("primes: ", from)
    val (primes, is_prime) = isPrime( primes, from)
    val () = println!("primes: ", is_prime)
  in
    if is_prime
    then loop( from + step, step, added) where {
      val added = stream_vt_append( primes, $ldelay( stream_vt_cons( from, $ldelay( stream_vt_nil()))))
    }
    else loop( from + step, step, primes)
  end
}

implement main0() = () where {
  val pow2_24 = 100; // g0int_npow( 2, 24)
  val primes = primes()
  val thePrimes = stream_vt_take_while( primes, lam x => x <= pow2_24 )
  val () = println!( stream_vt_length( thePrimes))
}
