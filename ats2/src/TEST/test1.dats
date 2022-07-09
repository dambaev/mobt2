#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
staload UN="prelude/SATS/unsafe.sats"

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
  val thePrimes = stream_take_while( primes(), lam x =<cloref1> x <= pow2_24 )
  val () = println!( stream_length( thePrimes))
}
