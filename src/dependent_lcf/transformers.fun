structure Identity :> MONAD where type 'a m = 'a = 
struct
  type 'a m = 'a
  fun ret a = a
  fun map f = f
  fun bind (m, f) = f m
end

structure Result :>
sig
  datatype 'a result = 
     OK of 'a
   | ERR of exn

  include MONAD where type 'a m = 'a result
  val mapErr : (exn -> exn) -> 'a result -> 'a result
end = 
struct
  datatype 'a result = 
     OK of 'a
   | ERR of exn

  type 'a m = 'a result

  val ret = OK
  
  fun map f = 
    fn OK a => OK (f a)
     | ERR exn => ERR exn

  fun bind (m, k) =
    case m of 
       OK a => k a
     | ERR exn => ERR exn

  fun mapErr f =
    fn OK a => OK a
     | ERR exn => ERR (f exn)
end

functor ErrorT (M : MONAD) :>
sig
  datatype result = datatype Result.result
  include MONAD where type 'a m = 'a result M.m
  val lift : 'a M.m -> 'a m
  val throw : exn -> 'a m
  val mapErr : (exn -> exn) -> 'a m -> 'a m
  val or : 'a m * 'a m -> 'a m
end = 
struct
  structure R = Result
  datatype result = datatype R.result
  type 'a m = 'a result M.m

  fun lift (a : 'a M.m) = M.map OK a
  fun throw exn = M.ret (ERR exn)
  fun mapErr f = M.map (R.mapErr f)
  fun or (m1, m2) = M.bind (m1, fn OK a => M.ret (OK a) | ERR exn => m2)
  fun ret a = M.ret (OK a)
  fun map f = M.map (Result.map f)
  fun bind (m, k) = M.bind (m, fn OK a => k a | ERR exn => M.ret (ERR exn))
end

functor ReaderT (type r structure M : MONAD) :>
sig
  include MONAD where type 'a m = r -> 'a M.m
  val lift : 'a M.m -> 'a m
  val mapR : (r -> r) -> 'a m -> 'a m
end =
struct
  type 'a m = r -> 'a M.m
  fun lift m _ = m
  fun mapR f m = m o f
  fun ret a = lift (M.ret a)
  fun map f m = M.map f o m
  fun bind (m, f) r = M.bind (m r, fn a => f a r)
end

functor Reader (type r) = ReaderT (type r = r structure M = Identity)

functor ListT (M : MONAD) :>
sig
  include MONAD
  val lift : 'a M.m -> 'a m
  val concat : 'a m * 'a m -> 'a m
  val emp : unit -> 'a m
  val cons : 'a * 'a m -> 'a m
  val uncons : 'a m -> ('a * 'a m) option M.m
end = 
struct
  fun @@ (f, x) = f x
  infix @@

  datatype ('a, 's) step = 
      YIELD of 'a * 's Susp.susp
    | SKIP of 's Susp.susp
    | DONE

  datatype 'a m = ROLL of ('a, 'a m) step M.m

  fun emp () = ROLL @@ M.ret DONE

  fun lift (m : 'a M.m) : 'a m =
    ROLL @@ M.map (fn a => YIELD (a, Susp.delay (fn _ => ROLL @@ M.ret DONE))) m

  fun stepMap (f : ('a, 'a m) step -> ('b, 'b m) step) : 'a m -> 'b m = 
    fn ROLL m =>
      ROLL (M.map f m)

  fun ret (a : 'a) : 'a m =
    lift @@ M.ret a

  fun suspMap (f : 'a -> 'b) (s : 'a Susp.susp) : 'b Susp.susp = 
    Susp.delay (fn _ => 
      f (Susp.force s))

  fun map f =
    stepMap
      (fn YIELD (a, s) => YIELD (f a, suspMap (map f) s)
        | SKIP s => SKIP (suspMap (map f) s)
        | DONE => DONE)

  fun consSusp (a : 'a, xs : 'a m Susp.susp) : 'a m =
    ROLL (M.ret (YIELD (a, xs)))

  fun cons (a : 'a, xs : 'a m) : 'a m = 
    consSusp (a, Susp.delay (fn _ => xs))

  fun concat (m : 'a m, n : 'a m) =
    stepMap
      (fn YIELD (a, s) => YIELD (a, suspMap (fn m' => concat (m', n)) s)
        | SKIP s => SKIP (suspMap (fn m' => concat (m', n)) s)
        | DONE => SKIP (Susp.delay (fn _ => n)))
      m

  fun bind (m, f) = 
    stepMap
      (fn YIELD (a, s) => SKIP (suspMap (fn n => concat (f a, bind (n, f))) s)
        | SKIP s => SKIP (suspMap (fn n => bind (n, f)) s)
        | DONE => DONE)
      m

  fun uncons (ROLL m) = 
    let
      val f = 
        fn YIELD (a, s) => M.ret @@ SOME (a, Susp.force s)
         | SKIP s => uncons (Susp.force s)
         | DONE => M.ret NONE
    in
      M.bind (m, f)
    end
end
