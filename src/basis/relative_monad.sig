(* Monads Need Not Be Endofunctors: http://www.cs.nott.ac.uk/~psztxa/publ/Relative_Monads.pdf *)
signature RELATIVE_MONAD =
sig
  structure J : FUNCTOR (* leaves *)
  type 'x t (* trees *)

  (* the unit of the relative monad creates a leaf node *)
  val unit : 'x J.t -> 'x t

  (* the Kleisli extension of the relative monad substitutes
   * new subtrees for each leaf node. *)
  val extend : ('x J.t -> 'y t) -> 'x t -> 'y t
end
