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
      open Telescope.SnocView

      fun foldStates T (R as (e, Psi))=
        case out T of
             Empty => R
           | Snoc (T', x, (e', Psi')) =>
               let
                 val e'' = Term.subst e' x e
                 val Psi'' = Telescope.append (Psi', Telescope.remove Psi x)
                 val Psi''' = Telescope.map Psi'' (substJudgment (x, e'))
               in
                 foldStates T' (e'', Psi''')
               end

      val (e, Psi) = t1 J
    in
      foldStates (Telescope.map Psi t2) (e, Psi)
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

