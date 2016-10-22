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

  val isjdg : J.jdg isjdg

  type 'a tactic = 'a -> 'a state
  type 'a multitactic = 'a state tactic

  val all : J.jdg tactic -> J.jdg multitactic
  val each : J.jdg tactic list -> J.jdg multitactic
  val only : int * J.jdg tactic -> J.jdg multitactic

  val seq : J.jdg tactic * J.jdg multitactic -> J.jdg tactic
  val then_ : J.jdg tactic * J.jdg tactic -> J.jdg tactic
  val thenl : J.jdg tactic * J.jdg tactic list -> J.jdg tactic
  val thenf : J.jdg tactic * (int * J.jdg tactic) -> J.jdg tactic

  val idn : J.jdg tactic
  val orelse_ : J.jdg tactic * J.jdg tactic -> J.jdg tactic
  val try : J.jdg tactic -> J.jdg tactic

  exception Progress
  val progress : J.jdg tactic -> J.jdg tactic

  exception Complete
  val complete : J.jdg tactic -> J.jdg tactic
end
