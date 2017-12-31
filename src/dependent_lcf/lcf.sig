signature LCF =
sig
  structure L : LCF_LANGUAGE
  structure Tl : TELESCOPE where type Label.t = L.var

  datatype 'a info = ::@ of string list * 'a

  val newInfo : 'a -> 'a info
  val mapInfo : ('a -> 'b) -> 'a info -> 'b info
  val projInfo : 'a info -> 'a
  
  datatype 'a state = |> of 'a info Tl.telescope * L.term

  type 'a isjdg =
     {sort : 'a -> L.sort,
      subst : L.env -> 'a -> 'a,
      ren : L.ren -> 'a -> 'a}

  val map : ('a -> 'b) -> 'a state -> 'b state
  val ret : 'a isjdg -> 'a -> 'a state
  val mul : 'a isjdg -> 'a state state -> 'a state
end

signature LCF_JUDGMENT =
sig
  type jdg
  type sort
  type env
  type ren

  val sort : jdg -> sort
  val subst : env -> jdg -> jdg
  val ren : ren -> jdg -> jdg
  val eq : jdg * jdg -> bool
end
