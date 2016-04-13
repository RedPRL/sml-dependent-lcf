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

  structure Tactic :
  sig
    type 'a binding = atom list * 'a

    datatype view =
        SEQ of multitactic binding list
      | ORELSE of tactic * tactic
      | REC of variable * tactic
      | PROGRESS of tactic
      | RULE of rule
      | VAR of variable

    val out : sign -> tactic -> view
  end

  structure Multitactic :
  sig
    datatype view =
        ALL of tactic
      | EACH of tactic list
      | FOCUS of int * tactic

    val out : sign -> multitactic -> view
  end
end

