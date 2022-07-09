#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
staload UN="prelude/SATS/unsafe.sats"

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
  then stream_cons( from, $delay( loop( from + step, step, primes)))
  else loop( from + step, step, primes)
  val rec result = $delay (stream_cons( 2, $delay (stream_cons( 3, $delay( loop( 5, 2, result))))))
}

implement main0() = () where {
  val pow2_24 = g0int_npow( 2, 24)
  val primes = stream_t2vt( primes())
  val thePrimes = stream_vt_take_while( primes, lam x => x <= pow2_24 )
  val () = println!( stream_vt_length( thePrimes))
}
