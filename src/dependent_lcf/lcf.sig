signature LCF =
sig
  structure L : LCF_LANGUAGE
  structure Tl : TELESCOPE where type Label.t = L.var

  datatype 'a state = |> of 'a Tl.telescope * L.term

  type 'a isjdg =
     {sort : 'a -> L.sort,
      subst : L.env -> 'a -> 'a}

  val map : ('a -> 'b) -> 'a state -> 'b state
  val ret : 'a isjdg -> 'a -> 'a state
  val mul : 'a isjdg -> 'a state state -> 'a state

  type 'a tactic = 'a -> 'a state
  type 'a multitactic = 'a state tactic
end
