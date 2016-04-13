(* We extend a model of Nominal LCF to interpret tactics and multitactics. *)
signature NOMINAL_LCF_SEMANTICS =
sig
  include NOMINAL_LCF_MODEL

  val tactic : Syn.sign * env -> Syn.tactic -> tactic
  val multitactic : Syn.sign * env -> Syn.multitactic -> multitactic
end
