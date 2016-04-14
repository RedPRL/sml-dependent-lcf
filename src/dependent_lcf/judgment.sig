signature ABT_JUDGMENT =
sig
  structure Tm : ABT
  type valence = Tm.valence

  include JUDGMENT
    where type evidence = Tm.abs
    where type metavariable = Tm.Metavariable.t

  (* the valence of the evidence of the judgment; categorical judgments
   * tend to take evidence of trivial valence, but generic and parametric
   * judgments will induce non-trivial valences for their evidence.*)
  val evidenceValence : judgment -> valence

  val judgmentMetactx : judgment -> Tm.metactx
  val substEvidenceEnv : evidence Tm.MetaCtx.dict -> judgment -> judgment
  val unifyJudgment : judgment * judgment -> Tm.Unify.renaming option
end

