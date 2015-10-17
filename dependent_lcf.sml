signature DLCF_KIT =
sig
  type name
  type term
  type judgment

  val substJudgment : name * term -> judgment -> judgment

  structure Telescope : TELESCOPE where type Label.t = name
  structure Term : ABT where type t = term and type Variable.t = name
end

signature DLCF =
sig
  include DLCF_KIT

  type subgoals = judgment Telescope.telescope

  type tactic = judgment -> term * subgoals

  val THEN : tactic * tactic -> tactic
  val ORELSE : tactic * tactic -> tactic
  val ID : tactic
  val TRY : tactic -> tactic

  val COMPLETE : tactic -> tactic
  exception RemainingSubgoals of subgoals
  exception UnsolvedMetavariables of name list
end

functor DLcf (Kit : DLCF_KIT) : DLCF =
struct
  open Kit

  type subgoals = judgment Telescope.telescope

  type tactic = judgment -> term * subgoals
  structure Term = AbtUtil (Term)

  fun THEN (t1, t2) J =
    let
      open Telescope.ConsView

      (*
      * -----------------------------nil
      *    E -| <> ==[t]==> E -| <>
      *
      *    Jα ||- t => Eα -| Ψα
      *    [Eα/α]E -| [Eα/α]Φ \ α ==[t]==> E' -| Φ'
      * ----------------------------------------------cons
      *    E -| α:Jα,Φ ==[t]==> E' -| Ψα <+> Φ'
      *
      *    J ||- t1 => E -| Φ
      *    E -| Φ ==[t2]==> E' -| Φ'
      * ------------------------------------THEN
      *    J ||- t1;t2 => E' -| Φ'
      *)
      fun go (e, Phi) =
        case out Phi of
             Empty => (e, Phi)
           | Cons (x, Jx, Phi) =>
               let
                 val (ex, Psix) = t2 Jx
                 val Phi' = Telescope.map Phi (substJudgment (x, ex))

                 val (e', Phi'') = go (Term.subst ex x e, Phi')
               in
                 (e', Telescope.append (Psix, Phi''))
               end

    in
      go (t1 J)
    end

  fun ID J =
    let
      val q = Term.Variable.new ()
      val Psi = Telescope.snoc Telescope.empty (q, J)
    in
      (Term.`` q, Psi)
    end

  fun ORELSE (t1, t2) J =
    t1 J handle _ => t2 J

  fun TRY t = ORELSE (t, ID)

  exception RemainingSubgoals of subgoals
  exception UnsolvedMetavariables of name list

  local
    open Telescope.SnocView
    fun assertClosed e =
      case Term.freeVariables e of
           [] => ()
         | xs => raise UnsolvedMetavariables xs
    fun assertEmpty Psi =
      case out Psi of
           Empty => ()
         | _ => raise RemainingSubgoals Psi
  in
    fun COMPLETE t J =
      let
        val (e, Psi) = t J
        val _ = assertEmpty Psi
        val _ = assertClosed e
      in
        (e, Telescope.empty)
      end
  end
end

