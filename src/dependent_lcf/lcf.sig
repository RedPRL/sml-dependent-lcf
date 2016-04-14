signature LCF_CONTEXT =
sig
  type 'a ctx
  type metavariable

  val mapWithKeys : (metavariable * 'a -> 'b) -> 'a ctx -> 'b ctx
end

signature LCF =
sig
  structure Ctx : LCF_CONTEXT
  type 'a ctx = 'a Ctx.ctx
  type metavariable = Ctx.metavariable

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
  type multitactic = judgment state -> judgment state

  val stateToString : judgment state -> string

  structure Judgable :
  sig
    include FUNCTOR

    (* A natural transformation [Const(judgment) -> t] *)
    val into : judgment -> judgment t

    (* A natural transformation [t -> id] *)
    val out : 'a t -> 'a
  end

  structure State : FUNCTOR
    where type 'a t = 'a state

  (* The relative monad structure provides for the construction
   * leaf nodes in a proof tree, and also the substitution of
   * a new subtree for a leaf node. *)
  structure Monad : RELATIVE_MONAD
    where type 'a J.t = 'a Judgable.t
    where type 'a t = 'a Judgable.t State.t

end

signature LCF_UTIL =
sig
  include LCF

  val unit : judgment -> judgment state

  val extend : tactic -> multitactic
  val labeledExtend : (metavariable -> tactic) -> multitactic

  val contract : multitactic -> tactic
end

(* Classic LCF arises from letting [Judgable] be the identity functor;
 * in this case, the relative monad is just a standard monad. *)
signature CLASSIC_LCF = LCF
  where type 'a Judgable.t = 'a
  where type 'a Ctx.ctx = 'a list
  where type Ctx.metavariable = int

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

