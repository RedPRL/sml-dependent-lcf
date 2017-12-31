signature MONAD =
sig
  type 'a m
  val ret : 'a -> 'a m
  val map : ('a -> 'b) -> 'a m -> 'b m
  val bind : 'a m * ('a -> 'b m) -> 'b m
end