(* Dependent LCF arises from endowing the evidence of judgments with
 * a valence and a substitution action. *)
signature DEPENDENT_LCF =
sig
  structure J : ABT_JUDGMENT
  structure T : TELESCOPE
    where type Label.t = J.metavariable

  datatype 'a judgable =
    JUDGABLE of
      {judgment : 'a,
       evidenceValence : J.valence,
       subst : J.evidence J.Tm.MetaCtx.dict -> 'a judgable}

  include LCF
    where type judgment = J.judgment
    where type evidence = J.evidence
    where type 'a Ctx.ctx = 'a T.telescope
    where type Ctx.metavariable = J.metavariable
    where type 'a Judgable.t = 'a judgable
end

