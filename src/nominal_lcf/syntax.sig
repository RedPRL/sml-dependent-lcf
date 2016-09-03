structure NominalLcfView =
struct
  datatype ('mtac, 'tac, 'rule, 'var, 'atom) tactic_view =
      SEQ of ('atom list * 'mtac) list
    | ORELSE of 'tac * 'tac
    | REC of 'var * 'tac
    | PROGRESS of 'tac
    | RULE of 'rule
    | VAR of 'var

  datatype 'tac multitactic_view =
      ALL of 'tac
    | EACH of 'tac list
    | FOCUS of int * 'tac
end

signature NOMINAL_LCF_SYNTAX =
sig
  type atom
  type variable

  (* A [rule] is an atomic tactic, a leaf node of a proof. *)
  type rule

  (* A [tactic] operates on a single judgment. *)
  type tactic

  (* A [multitactic] operates on a full proof-state. *)
  type multitactic

  (* The notion of a signature may differ depending on the refinement theory.
   * Signatures might contain declarations, definitional extensions, etc.; the
   * Nominal LCF theory is completely agnostic on this count. *)
  type sign

  structure VarCtx : DICT
    where type key = variable

  val tactic : sign -> tactic -> (multitactic, tactic, rule, variable, atom) NominalLcfView.tactic_view
  val multitactic : sign -> multitactic -> tactic NominalLcfView.multitactic_view
end

