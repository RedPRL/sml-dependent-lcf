signature HOLE_KIT =
sig
  structure J : ABT_JUDGMENT
  structure T : TELESCOPE
    where type Label.t = J.metavariable
end

signature HOLE_UTIL =
sig
  include HOLE_KIT
  val makeHole : J.metavariable * J.valence -> J.evidence
  val openEnv : J.judgment T.telescope -> J.evidence J.Tm.Metavar.Ctx.dict
end
