signature JUDGMENT =
sig
  type judgment
  type evidence

  (* metavariables range over evidence *)
  type metavariable

  val judgmentToString : judgment -> string
  val evidenceToString : evidence -> string

  (* Substitute evidence for a metavariable in a judgment *)
  val substEvidence
    : evidence * metavariable
    -> judgment
    -> judgment
end
