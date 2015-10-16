signature CONTEXT =
sig
  type name
  type 'a context

  val empty : 'a context
  val insert : 'a context * name * 'a -> 'a context
  val append : 'a context * 'a context -> 'a context
  val eq : ''a context * ''a context -> bool
end

signature SUBST =
sig
  structure Context : CONTEXT

  type term
  type subst

  val id : subst
  val subst : Context.name * term -> subst
  val seq : subst * subst -> subst

  val union : subst * subst -> subst
  exception UNION

  val apply : term * subst -> term

  val infer : 'a Context.context * subst -> 'a Context.context
end

signature SUBST_UTIL =
sig
  include SUBST

  val check : subst * ''a Context.context * ''a Context.context -> bool
end

functor SubstUtil (S : SUBST) : SUBST_UTIL =
struct
  open S

  fun check (rho, G, D) =
    Context.eq (D, infer (G, rho))
end

signature REFINER_KIT =
sig
  type name
  type term
  type judgment
  type sort

  structure Context : CONTEXT where type name = name
  structure Telescope : TELESCOPE where type Label.t = name
  structure Subst : SUBST where Context = Context and type term = term
end

signature REFINER =
sig
  include REFINER_KIT

  type metavars = sort Context.context
  type subgoals = judgment Telescope.telescope
  type subst = Subst.subst

  type tactic = metavars * judgment -> subst * term * subgoals

  val THEN : tactic * tactic -> tactic
  val SUBST : tactic * subst -> tactic
end

functor Refiner
  (structure Kit : REFINER_KIT where type sort = unit
   sharing type Kit.judgment = Kit.term) : REFINER =
struct
  open Kit

  type metavars = sort Context.context
  type subgoals = judgment Telescope.telescope
  type subst = Subst.subst

  local
    open Telescope.SnocView
  in
    fun telescopeAppend (T, T') =
      case out T of
           Empty => T'
         | Snoc (_, x, _) => Telescope.interposeAfter T (x, T')

    fun subgoalsToMetavars T =
      case out T of
           Empty => Context.empty
         | Snoc (T', x, A) => Context.insert (subgoalsToMetavars T', x, ())
  end

  type tactic = metavars * judgment -> subst * term * subgoals

  fun THEN (t1, t2) (X, J) =
    let
      open Telescope.SnocView

      val (rho, e, Psi) = t1 (X, J)
      val Y = Subst.infer (X, rho)

      (* build up a telescope of proof states by applying t2 to every subgoal of t1 *)
      fun unfoldStates T =
        case out T of
             Empty => Telescope.empty
           | Snoc (T', x, Jx) =>
               Telescope.snoc
                (unfoldStates T')
                (x, t2 (Context.append (Y, subgoalsToMetavars T'), Jx))

      (* fold the telescope of proof states into a single proof state *)
      fun foldStates T (R as (rho, e, Psi)) =
        case out T of
             Empty => R
           | Snoc (T, x, (rho', e', Psi')) =>
             let
               val rho'' = Subst.union (rho, rho')
               val x2e = Subst.subst (x, e')
               val e'' = Subst.apply (e, x2e)
               val Psi'' =
                 Telescope.map
                   (telescopeAppend (Psi, Psi'))
                   (fn m => Subst.apply (m, x2e))
             in
               foldStates T (rho'', e'', Psi'')
             end
    in
      foldStates (unfoldStates Psi) (rho, e, Psi)
    end

  fun SUBST (t, rho) goal =
    let
      val (rho', e, psi) = t goal
    in
      (Subst.seq (rho', rho), e, psi)
    end

end

