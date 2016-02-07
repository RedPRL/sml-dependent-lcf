signature MULTITACTICALS =
sig
  structure Lcf : DEPENDENT_LCF

  type multitactic = Lcf.judgment Lcf.state -> Lcf.judgment Lcf.state

  val ID : Lcf.tactic
  val ALL : Lcf.tactic -> multitactic
  val EACHX : Lcf.tactic Lcf.ctx -> multitactic
  val EACH : Lcf.tactic list -> multitactic
  val FOCUS : int -> Lcf.tactic -> multitactic
end
