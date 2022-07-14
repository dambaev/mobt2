#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
staload "{$LIBS}/result/src/SATS/result.sats"
staload "libats/SATS/dynarray.sats"
staload DA="libats/SATS/dynarray.sats"
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
  | stream_vt_nil() =>
    let
      val () = cloptr_free ($UN.castvwtp0{cloptr0}(pred))
    in
      xs_con
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
  ( x:int
  , primes: &dynarray(int)
  ):
  bool =
let
  var result : bool?
  var primes_sz: size_t?
  val ( pf, fpf | ptr ) = $DA.dynarray_get_array( primes, primes_sz)
  val () = result := true
  val _ = array_foreach_env<int><bool>( !ptr, primes_sz, result) where {
    implement array_foreach$cont<int><bool>( x0, env) = env && x0pow2 <= x where {
      val x0pow2 = g0int_npow( x0, 2)
    }
    implement array_foreach$fwork<int><bool>( x0, env) =
      if x mod x0 = 0
      then {
        val () = env := false
      }
  }
  prval () = fpf pf
in
  if result
  then true where {
    val () = $DA.dynarray_insert_atend_exn<int>(primes, x)
  }
  else false
end

fn primes(): stream_vt(int) = result where {
  val initial = $DA.dynarray_make_nil<int>(i2sz 1024)
  val () = $DA.dynarray_insert_atend_exn<int>( initial, 2)
  fun
    auxmain
    ( from: int
    , step: int
    , evaluatedPrimes: dynarray(int)
    ): stream_vt(int) = $ldelay
  ( auxmain_con( from, step, evaluatedPrimes)
  , dynarray_free evaluatedPrimes
  )
  and
    auxmain_con
    ( from: int
    , step: int
    , evaluatedPrimes: dynarray(int)
    ): stream_vt_con(int) =
  let
    var vprimes = evaluatedPrimes
    val is_prime = isPrime( from, vprimes)
  in
    if is_prime
    then stream_vt_cons( from, auxmain( from + step, step, vprimes))
    else auxmain_con( from+step, step, vprimes)
  end
  val result = $ldelay( stream_vt_cons( 2, auxmain( 3, 2, initial)), dynarray_free initial)
}

implement main0() = () where {
  val pow2_24 = g0int_npow( 2, 24)
  val primes = primes()
  val thePrimes = stream_vt_take_while( primes, lam x => x <= pow2_24 )
  val () = println!( stream_vt_length( thePrimes))
}
