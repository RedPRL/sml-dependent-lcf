signature LCF_TACTIC_MONAD = 
sig
  include MONAD

  type env (* local state *)
  type w (* log *)

  val run : env -> 'a m * ('a -> bool) -> 'a

  val throw : exn -> 'a m
  val par : 'a m * 'a m -> 'a m
  val or : 'a m * 'a m -> 'a m

  val getEnv : env m
  val mapEnv : (env -> env) -> 'a m -> 'a m
  val mapErr : (exn -> exn) -> 'a m -> 'a m

  val trace : w -> unit m
  val listen : 'a m -> ('a * w) m
end