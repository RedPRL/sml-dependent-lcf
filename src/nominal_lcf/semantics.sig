(* We extend a model of Nominal LCF to interpret multitactics and statements. *)
signature NOMINAL_LCF_SEMANTICS =
sig
  include NOMINAL_LCF_MODEL

  val tactic : (Syn.tactic, tactic) interp
  val multitactic : (Syn.multitactic, multitactic) interp
  val statement : (Syn.statement, tactic) interp
end
