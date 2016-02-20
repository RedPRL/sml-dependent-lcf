signature LCF =
sig
  type 'a ctx

  (* A logical theory is defined by specifying a collection of [judgment]s,
   * and a collection of formal rules for proving these judgments. The
   * formal rules are then related to the semantic assertion conditions
   * of the judgments by the synthesis of [evidence]. *)
  type judgment
  type evidence

  (* An [environment] is a substitution of evidence for subgoals. *)
  type environment = evidence ctx

  (* [validation]s are hypothetical evidence. *)
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

  (* Substitute new trees for the leaves of a proof tree; morally, this
   * operation arises from the fact that ['a state] is a monad on the
   * category of types that classify judgments. *)
  val subst
    : (J.metavariable -> judgment -> judgment state)
    -> judgment state
    -> judgment state
end

