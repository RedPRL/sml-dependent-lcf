structure NominalLcfView =
struct
  datatype ('mtac, 'tac, 'rule) tactic_view =
      RULE of 'rule
    | MTAC of 'mtac

  datatype ('mtac, 'tac, 'var, 'atom) multitactic_view =
      ALL of 'tac
    | EACH of 'tac list
    | FOCUS of int * 'tac
    | REPEAT of 'mtac
    | PROGRESS of 'mtac
    | ORELSE of 'mtac * 'mtac
    | REC of 'var * 'mtac
    | VAR of 'var
    | SEQ of 'atom list * 'mtac * 'mtac
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

  val tactic : sign -> tactic -> (multitactic, tactic, rule) NominalLcfView.tactic_view
  val multitactic : sign -> multitactic -> (multitactic, tactic, variable, atom) NominalLcfView.multitactic_view
end

