signature JUDGMENT =
sig
  type judgment
  type evidence

  (* metavariables range over evidence *)
  type metavariable

  (* valences classify metavariables *)
  type valence

  val judgmentToString : judgment -> string
  val evidenceToString : evidence -> string

  (* the valence of the evidence of the judgment; categorical judgments
   * tend to take evidence of trivial valence, but generic and parametric
   * judgments will induce non-trivial valences for their evidence.*)
  val evidenceValence : judgment -> valence

  (* Substitute evidence for a metavariable in a judgment *)
  val substJudgment
    : metavariable * evidence
    -> judgment
    -> judgment
end

signature ABT_JUDGMENT =
sig
  structure Tm : ABT
  include JUDGMENT
    where type evidence = Tm.abs
    where type valence = Tm.valence
    where type metavariable = Tm.Metavariable.t
end

