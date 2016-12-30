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
end

signature LCF_JUDGMENT =
sig
  type jdg
  type sort
  type env

  val sort : jdg -> sort
  val subst : env -> jdg -> jdg
  val eq : jdg * jdg -> bool
  val toString : jdg -> string
end
