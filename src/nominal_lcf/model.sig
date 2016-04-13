(* A model of Nominal LCF consists in a tactic metalanguage, a spread of
 * sequences of atoms, and an interpretation of primitive tactics into the
 * metalanguage language. *)
signature NOMINAL_LCF_MODEL =
sig
  (* We will construct a model for a Nominal LCF theory [Syn]. *)
  structure Syn : NOMINAL_LCF_SYNTAX

  (* A model begins with a tactic metalanguage [Lcf]. *)
  structure Lcf : DEPENDENT_LCF

  (* The nominal character of the semantics is dealt with using a Brouwerian
   * spread, a space whose points are free choice sequences. A free choice
   * sequence is a stream of constructible objects which are chosen not by a
   * computable function, but by interaction with a subject (i.e. a user). *)
  structure Spr : SPREAD

  (* A "nominal" object is a functional which _continuously_ transforms a free
   * choice sequence into a result. *)
  type 'a nominal = Syn.atom Spr.point -> 'a

  type tactic = Lcf.tactic nominal
  type multitactic = Lcf.multitactic nominal

  (* An environment assigns a tactic to each variable. *)
  type env = tactic Syn.VarCtx.dict

  (* An interpretation takes a signature and an environment, and
   * translates syntax into semantics. *)
  type ('syn, 'sem) interp
    = Syn.sign * env
    -> 'syn
    -> 'sem

  val tacticR
    : (Syn.statement, tactic) interp
    -> (Syn.tactic, tactic) interp
end

