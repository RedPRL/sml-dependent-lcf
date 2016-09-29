signature LCF =
sig
  structure Ctx : LCF_CONTEXT
  structure Env : LCF_CONTEXT
  sharing type Ctx.metavariable = Env.metavariable

  type 'a ctx = 'a Ctx.ctx
  type 'a env = 'a Env.ctx
  type metavariable = Ctx.metavariable

  (* A logical theory is defined by specifying a collection of [judgment]s,
   * and a collection of formal rules for proving these judgments. The
   * formal rules are then related to the semantic assertion conditions
   * of the judgments by the synthesis of [evidence]. *)
  type judgment
  type evidence

  (* An [environment] is a substitution of evidence for subgoals. *)
  type environment = evidence env

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

(* Classic LCF arises from letting [Judgable] be the identity functor;
 * in this case, the relative monad is just a standard monad. *)
signature CLASSIC_LCF = LCF
  where type 'a Judgable.t = 'a
  where type 'a Ctx.ctx = 'a list
  where type Ctx.metavariable = int

