signature DLCF_KIT =
sig
  structure Term : ABT

  type judgment
  val judgmentToString : judgment -> string

  (* the valence of the evidence of the judgment; categorical judgments
   * tend to take evidence of trivial valence, but generic and parametric
   * judgments will induce non-trivial valences for their evidence.*)
  val evidenceValence : judgment -> Term.valence

  (* Substitute an abstraction for a hole in the statement of a judgment. *)
  val substJudgment
    : Term.metavariable * Term.abs
    -> judgment
    -> judgment

  structure Telescope : TELESCOPE
    where type Label.t = Term.metavariable
end

signature DLCF =
sig
  include DLCF_KIT

  type 'a ctx = 'a Telescope.telescope
  type environment = Term.abs Telescope.telescope
  type validation = environment -> Term.abs
  type 'a state = 'a ctx * validation
  type tactic = judgment -> judgment state

  val stateToString : judgment state -> string

  val ID : tactic
  val THEN : tactic * tactic -> tactic
  val THENX : tactic * tactic ctx -> tactic
  val THENL : tactic * tactic list -> tactic
  val ORELSE : tactic * tactic -> tactic
  val TRY : tactic -> tactic

  (* val COMPLETE : tactic -> tactic *)
  exception RemainingSubgoals of judgment ctx
  exception UnsolvedMetavariables of Term.metavariable list
end

functor DepLcf (Kit : DLCF_KIT) : DLCF =
struct
  open Kit

  structure T = Telescope and Tm = Term
  structure Spine = Tm.Operator.Arity.Valence.Spine
  structure ShowTm = DebugShowAbt (Tm)

  structure Meta = Tm.Metavariable
  type 'a ctx = 'a T.telescope
  type environment = Term.abs T.telescope
  type validation = environment -> Term.abs
  type 'a state = 'a ctx * validation
  type tactic = judgment -> judgment state

  exception RemainingSubgoals of judgment ctx
  exception UnsolvedMetavariables of Term.metavariable list

  local
    val i = ref 0
  in
    fun newMeta () =
      (i := !i + 1;
       Meta.named ("?" ^ Int.toString (!i)))
  end

  fun ID jdg =
    let
      val v = newMeta ()
      val theta = T.snoc T.empty (v, jdg)
    in
      (theta, fn rho =>
         T.lookup rho v)
    end

  structure MetaCtxUtil = ContextUtil (structure Ctx = Tm.MetaCtx and Elem = Tm.Operator.Arity.Valence)

  fun makeHole (v : Tm.metavariable, vl : Tm.valence) : Tm.abs =
    let
      open Tm infix \ $#
      val ((sigmas, taus), tau) = vl
      val theta =
        MetaCtxUtil.extend
          Tm.MetaCtx.empty
          (v, vl)
      val syms = Spine.map (fn _ => Symbol.named "?") sigmas
      val vars = Spine.map (fn _ => Variable.named "?") taus
      val varTms =
        Spine.Pair.mapEq
          (fn (x,tau) => check theta (`x, tau))
          (vars, taus)
      val tm = check theta (v $# (syms, varTms), tau)
    in
      checkb theta ((syms, vars) \ tm, vl)
    end

  fun openEnv psi =
    let
      open T.ConsView
      fun go Empty rho = rho
        | go (Cons (x, jdg, phi)) rho =
            go (out phi)
              (T.snoc rho (x, makeHole (x, evidenceValence jdg)))
    in
      go (out psi) T.empty
    end

  fun absToString ev =
    let
      val (Tm.\ (_, m), _) = Tm.inferb ev
    in
      ShowTm.toString m
    end

  fun stateToString (psi, vld) =
    T.toString judgmentToString psi
      ^ "\n----------------------------------------------------\n"
      ^ absToString (vld (openEnv psi))

  datatype hole = hole
  fun ?hole = raise Match

  fun subst (t : Term.metavariable -> judgment -> judgment state) (st : judgment state) : judgment state =
    let
      open T.ConsView
      fun go (psi, vld) =
        case out psi of
             Empty => (psi, vld)
           | Cons (x, jdgx, psi) =>
               let
                 val (psix, vldx) = t x jdgx
                 fun vld' rho = vld (T.snoc rho (x, vldx rho))
                 val psi' = T.map psi (substJudgment (x, vldx (openEnv psix)))
                 val (psi'', vld'') = go (psi', vld')
               in
                 (T.append (psix, psi''), vld'')
               end
    in
      go st
    end

  fun uncurry f (x,y) =
    f x y

  fun THEN (t1, t2) =
    subst (fn _ => t2) o t1

  fun THENX (t, ts) =
    subst (T.lookup ts) o t

  fun THENL (t, ts) = fn jdg =>
    let
      val st as (psi, _) = t jdg
      open T.ConsView
      fun go (Empty, []) r = r
        | go (Cons (x,a,tel), (t :: ts)) r = go (out tel, ts) (T.snoc r (x, t))
        | go _ _ = raise Fail "Incorrect length"
      val ts' = go (out psi, ts) T.empty
    in
      THENX (fn _ => st, ts') jdg
    end

  fun ORELSE (t1, t2) jdg =
    t1 jdg handle _ => t2 jdg

  fun TRY t = ORELSE (t, ID)
end
