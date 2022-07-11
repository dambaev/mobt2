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

fn
  isPrime
  {n:nat}
  ( x:int
  , primes: !list_vt(int, n)
  ):
  bool =
let
  fun
    loop
    {n:nat}
    ( x: int
    , cnt: int
    , xs: !list_vt(int, n)
    ):
    #[ret:bool]
    (bool(ret), int) =
  case+ xs of
  | list_vt_nil() => (true, cnt) where {
  }
  | list_vt_cons( x0, xs1) =>
    let
      val x0pow2 = g0int_npow( x0, 2)
    in
      if x0pow2 > x
      then (true, cnt)
      else
        if (x mod x0) = 0
        then (false, cnt)
        else loop( x, cnt+1, xs1)
    end
  val (result, cnt) = loop( x, 0, primes)
in
  result
end

fn primes(): stream_vt(int) = result where {
  var tail: list_vt(int, 0)?
  val () = tail := list_vt_nil()
  var initial: list_vt(int,1)
  val () = initial := (list_vt_cons( 2, tail):list_vt(int,1))
  val numbers = $ldelay (stream_vt_cons( 2, $ldelay (stream_vt_cons( 3, from( 5, 2))))) where {
    fun from( start: int, step: int): stream_vt(int) = $ldelay( stream_vt_cons( start, from( start+step, step)))
  }
  fun
    auxmain
    {n:nat}
    ( xs: stream_vt( int)
    , evaluatedPrimes: list_vt(int,n)
    , tail: &ptr? >> List_vt(int)
    ): stream_vt(int) = $ldelay
  ( let
      prval _ = $showtype view@ tail
    in
      auxmain_con( xs, evaluatedPrimes, tail)
    end
  , {
    val () = ~xs
    val () = list_vt_free evaluatedPrimes
    val _ = tail
  }
  )
  and
    auxmain_con
    {n:nat}
    ( xs: stream_vt(int)
    , evaluatedPrimes: list_vt(int,n)
    , tail: &ptr? >> List_vt(int)
    ): stream_vt_con(int) =
  let
    val xs_con = !xs
  in
    case+ xs_con of
    | stream_vt_nil() => xs_con where {
      val () = list_vt_free evaluatedPrimes
    }
    | @stream_vt_cons( x0, xs1) =>
    let
      var vprimes = evaluatedPrimes
      val is_prime = isPrime( x0, vprimes)
    in
      if is_prime
      then xs_con where {
        var newtail: ptr
        val ~list_vt_nil() = tail
        val () = tail := list_vt_cons( x0, newtail)
        val () = xs1 := auxmain( xs1, vprimes, newtail)
        prval _ = fold@( xs_con)
      }
      else auxmain_con( xs1, vprimes, tail) where {
        val xs1 = xs1
        val () = free@ xs_con
      }
    end
  end
  val result = auxmain( numbers, initial, tail )
}

implement main0() = () where {
  val pow2_24 = 10000; // g0int_npow( 2, 24)
  val primes = primes()
  val thePrimes = stream_vt_take_while( primes, lam x => x <= pow2_24 )
  val () = println!( stream_vt_length( thePrimes))
}
