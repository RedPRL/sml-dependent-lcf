signature LCF_TRACE = 
sig
  type t
  val empty : t
  val append : t * t -> t
end

signature LCF_INFO = 
sig
  type 'a t
  val ret : 'a -> 'a t
  val run : 'a t -> 'a
  val map : ('a -> 'b) -> 'a t -> 'b t
  val bind : 'a t * ('a -> 'b t) -> 'b t
  val replace : 'b -> 'a t -> 'b t
end

signature LCF =
sig
  structure L : LCF_LANGUAGE
  structure Tl : TELESCOPE where type Label.t = L.var
  structure I : LCF_INFO

  datatype 'a state = |> of 'a I.t Tl.telescope * L.term

  type 'a isjdg =
     {sort : 'a -> L.sort,
      subst : L.env -> 'a -> 'a,
      ren : L.ren -> 'a -> 'a}

  val map : ('a -> 'b) -> 'a state -> 'b state
  val ret : 'a isjdg -> 'a -> 'a state
  val mul : 'a isjdg -> 'a state state -> 'a state
end

signature PLAIN_LCF = 
  LCF where type 'a I.t = 'a

signature TRACED_LCF = 
sig
  type trace
  datatype 'a traced = ::@ of trace * 'a
  include LCF where type 'a I.t = 'a traced
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
