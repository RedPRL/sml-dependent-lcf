signature LCF =
sig
  type 'a ctx
  type judgment
  type evidence

  type environment = evidence ctx
  type validation = environment -> evidence

  type 'a state = 'a ctx * validation
  type tactic = judgment -> judgment state

  val stateToString : judgment state -> string
end

signature DEPENDENT_LCF =
sig
  structure J : ABT_JUDGMENT
  structure T : TELESCOPE
    where type Label.t = J.metavariable

  include LCF
    where type judgment = J.judgment
    where type evidence = J.evidence
    where type 'a ctx = 'a T.telescope
end


