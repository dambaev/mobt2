#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
staload "{$LIBS}/result/src/SATS/result.sats"
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

fn
  isPrime
  {n:nat}
  ( x:int
  , primes: &list_vt(int, n) >> result_vtb( ret, list_vt(int, n+1), list_vt(int, n))
  ):
  #[ret:bool]
  bool(ret) =
let
  fun
    loop
    {n:nat}
    ( x: int
    , xs: !list_vt(int, n)
    ):
    #[ret:bool]
    bool(ret) =
  case+ xs of
  | list_vt_nil() => true
  | list_vt_cons( x0, xs1) =>
    let
      val x0pow2 = g0int_npow( x0, 2)
    in
      if x0pow2 > x
      then true
      else
        if (x mod x0) = 0
        then false
        else loop( x, xs1)
    end
  val result = loop( x, primes)
in
  if result
  then result where {
    val () = primes := list_vt_extend( primes, x)
    prval () = result_vt_success( primes)
  }
  else result where {
    prval () = result_vt_failure( primes)
  }
end

fn primes(): stream_vt(int) = $ldelay( stream_vt_cons( 2, auxmain( 3, 2, list_vt_cons( 2, list_vt_nil())))) where {
  fun
    auxmain
    {n:nat}
    ( from: int
    , step: int
    , evaluatedPrimes: list_vt(int,n)
    ): stream_vt(int) = $ldelay
  ( auxmain_con( from, step, evaluatedPrimes)
  , list_vt_free evaluatedPrimes
  )
  and
    auxmain_con
    {n:nat}
    ( from: int
    , step: int
    , evaluatedPrimes: list_vt(int,n)
    ): stream_vt_con(int) =
  let
    var vprimes = evaluatedPrimes
    val is_prime = isPrime( from, vprimes)
  in
    if is_prime
    then stream_vt_cons( from, auxmain( from + step, step, vprimes)) where {
      prval () = result_vt_unsuccess( vprimes)
    }
    else auxmain_con( from+step, step, vprimes) where {
      prval () = result_vt_unfailure( vprimes)
    }
  end
}

implement main0() = () where {
  val pow2_24 = 1000000; //g0int_npow( 2, 24)
  val primes = primes()
  val thePrimes = stream_vt_take_while( primes, lam x => x <= pow2_24 )
  val () = println!( stream_vt_length( thePrimes))
}
