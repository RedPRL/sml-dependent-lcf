signature LCF_UTIL =
sig
  include LCF

  val unit : judgment -> judgment state

  val extend : tactic -> multitactic
  val labeledExtend : (metavariable -> tactic) -> multitactic

  val contract : multitactic -> tactic
end
