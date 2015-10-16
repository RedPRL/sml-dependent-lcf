signature TERM =
sig
  type term
  type name
  type subst = name * term
  val subst : subst -> term -> term
  val freeVariables : term -> name list
end

signature REFINER_KIT =
sig
  type name
  type term
  type judgment = term
  type sort

  structure Telescope : TELESCOPE where type Label.t = name
  structure Term : TERM where type term = term and type name = name
end

signature REFINER =
sig
  include REFINER_KIT

  type subgoals = judgment Telescope.telescope

  type tactic = judgment -> term * subgoals

  val THEN : tactic * tactic -> tactic

  val COMPLETE : tactic -> tactic
  exception RemainingSubgoals of subgoals
  exception UnsolvedMetavariables of name list
end

functor Refiner
  (structure Kit : REFINER_KIT where type sort = unit) : REFINER =
struct
  open Kit

  type subgoals = judgment Telescope.telescope

  local
    open Telescope.SnocView
  in
    fun telescopeAppend (T, T') =
      case out T of
           Empty => T'
         | Snoc (_, x, _) => Telescope.interposeAfter T (x, T')
  end

  type tactic = judgment -> term * subgoals

  fun THEN (t1, t2) J =
    let
      open Telescope.SnocView

      val (e, Psi) = t1 J

      (* build up a telescope of proof states by applying t2 to every subgoal of t1 *)
      fun unfoldStates T =
        case out T of
             Empty => Telescope.empty
           | Snoc (T', x, Jx) =>
               Telescope.snoc
                (unfoldStates T')
                (x, t2 Jx)

      (* fold the telescope of proof states into a single proof state *)
      fun foldStates T (R as (e, Psi)) =
        case out T of
             Empty => R
           | Snoc (T, x, (e', Psi')) =>
             let
               val x2e = (x, e')
               val e'' = Term.subst x2e e'
               val Psi'' =
                 Telescope.map
                   (telescopeAppend (Psi, Psi'))
                   (fn m => Term.subst x2e m)
             in
               foldStates T (e'', Psi'')
             end
    in
      foldStates (unfoldStates Psi) (e, Psi)
    end

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

