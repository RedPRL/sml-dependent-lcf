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

signature LCF_UTIL =
sig
  include LCF

  structure J : LCF_JUDGMENT where type sort = L.sort and type env = L.term L.Ctx.dict

  type jdg = J.jdg
  val isjdg : jdg isjdg

  type 'a tactic = 'a -> 'a state
  type 'a multitactic = 'a state tactic

  val all : jdg tactic -> jdg multitactic
  val each : jdg tactic list -> jdg multitactic
  val only : int * jdg tactic -> jdg multitactic

  val seq : jdg tactic * jdg multitactic -> jdg tactic
  val then_ : jdg tactic * jdg tactic -> jdg tactic
  val thenl : jdg tactic * jdg tactic list -> jdg tactic
  val thenf : jdg tactic * (int * jdg tactic) -> jdg tactic

  val idn : jdg tactic
  val orelse_ : jdg tactic * jdg tactic -> jdg tactic
  val try : jdg tactic -> jdg tactic

  exception Progress
  val progress : jdg tactic -> jdg tactic
  val mprogress : jdg multitactic -> jdg multitactic

  exception Complete
  val complete : jdg tactic -> jdg tactic
end
