signature TACTICALS =
sig
  structure Lcf : LCF

  val ID : Lcf.tactic
  val THEN : Lcf.tactic * Lcf.tactic -> Lcf.tactic
  val THENX : Lcf.tactic * Lcf.tactic Lcf.ctx -> Lcf.tactic
  val THENL : Lcf.tactic * Lcf.tactic list -> Lcf.tactic
  val THENF : Lcf.tactic * int * Lcf.tactic -> Lcf.tactic
  val ORELSE : Lcf.tactic * Lcf.tactic -> Lcf.tactic
  val TRY : Lcf.tactic -> Lcf.tactic
end
