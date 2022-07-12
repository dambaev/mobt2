#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
staload "{$LIBS}/result/src/SATS/result.sats"
staload "libats/SATS/qlist.sats"
staload LIBATS="libats/SATS/qlist.sats"
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
  {n:nat}
  ( x:int
  , primes: &qlist(int, n) >> result_vtb( ret, qlist(int, n+1), qlist(int, n))
  ):
  #[ret:bool]
  bool(ret) =
let
  var result : bool?
  val () = result := true
  val () = $LIBATS.qlist_foreach_env<int><bool>( primes, result) where {
    implement qlist_foreach$cont<int><bool>( x0, env) = env && x0pow2 <= x where {
      val x0pow2 = g0int_npow( x0, 2)
    }
    implement qlist_foreach$fwork<int><bool>( x0, env) =
      if x mod x0 = 0
      then {
        val () = env := false
      }
  }
in
  if result
  then true where {
    val () = qlist_insert<int>(primes, x)
    prval () = result_vt_success( primes)
  }
  else false where {
    prval () = result_vt_failure( primes)
  }
end

fn primes(): stream_vt(int) = result where {
  val initial = qlist_make_nil{int}()
  val () = qlist_insert<int>( initial, 2)
  fn
    qlist_free
    {n:nat}
    ( xs: qlist(int,n)
    ): void = {
    fun
      qlist_consume
      {n:nat}
      .<n>.
      ( xs: !qlist( int, n) >> qlist(int, 0)
      , sz: int n
      ): void =
    if sz = 0
    then ()
    else qlist_consume( xs, sz-1) where {
      val value = qlist_takeout( xs)
    }
    val sz = qlist_length( xs)
    val () = qlist_consume( xs, sz)
    val () = qlist_free_nil(xs)
  }
  fun
    auxmain
    {n:nat}
    ( from: int
    , step: int
    , evaluatedPrimes: qlist(int,n)
    ): stream_vt(int) = $ldelay
  ( auxmain_con( from, step, evaluatedPrimes)
  , qlist_free evaluatedPrimes
  )
  and
    auxmain_con
    {n:nat}
    ( from: int
    , step: int
    , evaluatedPrimes: qlist(int,n)
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
  val result = $ldelay( stream_vt_cons( 2, auxmain( 3, 2, initial)), qlist_free initial)
}

implement main0() = () where {
  val pow2_24 = g0int_npow( 2, 24)
  val primes = primes()
  val thePrimes = stream_vt_take_while( primes, lam x => x <= pow2_24 )
  val () = println!( stream_vt_length( thePrimes))
}
