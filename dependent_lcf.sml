signature JUDGMENT =
sig
  structure Term : ABT

  type judgment
  type evidence = Term.abs
  val judgmentToString : judgment -> string
  val evidenceToString : evidence -> string

  (* the valence of the evidence of the judgment; categorical judgments
   * tend to take evidence of trivial valence, but generic and parametric
   * judgments will induce non-trivial valences for their evidence.*)
  val evidenceValence : judgment -> Term.valence

  (* Substitute an abstraction for a hole in the statement of a judgment. *)
  val substJudgment
    : Term.metavariable * Term.abs
    -> judgment
    -> judgment
end

signature LCF =
sig
  type 'a ctx
  type judgment
  type evidence

  type environment = evidence ctx
  type validation = environment -> evidence

  type 'a state = 'a ctx * validation
  type tactic = judgment -> judgment state

  val stateToString : judgment state -> string
end

signature DEPENDENT_LCF =
sig
  structure J : JUDGMENT
  structure T : TELESCOPE
  sharing type T.Label.t = J.Term.Metavariable.t

  include LCF
    where type judgment = J.judgment
    where type evidence = J.evidence
    where type 'a ctx = 'a T.telescope
end

signature HOLE_UTIL =
sig
  structure J : JUDGMENT
  structure T : TELESCOPE
  sharing type J.Term.Metavariable.t = T.Label.t

  val makeHole : J.Term.metavariable * J.Term.valence -> J.evidence
  val openEnv : J.judgment T.telescope -> J.evidence T.telescope
end

functor HoleUtil
  (structure J : JUDGMENT and T : TELESCOPE
   sharing type J.Term.Metavariable.t = T.Label.t) : HOLE_UTIL =
struct
  structure J = J and T = T and Tm = J.Term
  structure Spine = Tm.Operator.Arity.Valence.Spine
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
      val varTerms =
        Spine.Pair.mapEq
          (fn (x,tau) => check theta (`x, tau))
          (vars, taus)
      val tm = check theta (v $# (syms, varTerms), tau)
    in
      checkb theta ((syms, vars) \ tm, vl)
    end

  fun openEnv psi =
    let
      open T.ConsView
      fun go Empty rho = rho
        | go (Cons (x, jdg, phi)) rho =
            go (out phi)
              (T.snoc rho (x, makeHole (x, J.evidenceValence jdg)))
    in
      go (out psi) T.empty
    end
end

functor DependentLcf (J : JUDGMENT) : DEPENDENT_LCF =
struct
  structure J = J and Spine = J.Term.Operator.Arity.Valence.Spine
  open J

  structure Lbl =
  struct
    open Term.Metavariable
    fun prime x = named (toString x ^ "'")
  end

  structure T = Telescope (Lbl)
  type 'a ctx = 'a T.telescope

  type environment = evidence ctx
  type validation = environment -> evidence

  type 'a state = 'a ctx * validation
  type tactic = judgment -> judgment state

  structure HoleUtil = HoleUtil (structure J = J and T = T)

  fun stateToString (psi, vld) =
    T.toString judgmentToString psi
      ^ "\n----------------------------------------------------\n"
      ^ evidenceToString (vld (HoleUtil.openEnv psi))
end


signature TACTICALS =
sig
  structure Lcf : LCF

  val ID : Lcf.tactic
  val THEN : Lcf.tactic * Lcf.tactic -> Lcf.tactic
  val THENX : Lcf.tactic * Lcf.tactic Lcf.ctx -> Lcf.tactic
  val THENL : Lcf.tactic * Lcf.tactic list -> Lcf.tactic
  val ORELSE : Lcf.tactic * Lcf.tactic -> Lcf.tactic
  val TRY : Lcf.tactic -> Lcf.tactic
end

functor Tacticals (Lcf : DEPENDENT_LCF) : TACTICALS =
struct
  open Lcf
  structure Lcf = Lcf and Tm = J.Term
  structure Meta = Tm.Metavariable and Spine = Tm.Operator.Arity.Valence.Spine
  structure HoleUtil = HoleUtil (structure J = J and T = T)
  structure ShowTm = DebugShowAbt (Tm)

  local
    val i = ref 0
  in
    fun newMeta () =
      (i := !i + 1;
       Meta.named ("?" ^ Int.toString (!i)))
  end

  fun subst (t : Tm.metavariable -> judgment -> judgment state) (st : judgment state) : judgment state =
    let
      open T.ConsView
      fun go (psi, vld) =
        case out psi of
             Empty => (psi, vld)
           | Cons (x, jdgx, psi) =>
               let
                 val (psix, vldx) = t x jdgx
                 fun vld' rho = vld (T.snoc rho (x, vldx rho))
                 val psi' = T.map psi (J.substJudgment (x, vldx (HoleUtil.openEnv psix)))
                 val (psi'', vld'') = go (psi', vld')
               in
                 (T.append (psix, psi''), vld'')
               end
    in
      go st
    end

  fun ID jdg =
    let
      val v = newMeta ()
      val theta = T.snoc T.empty (v, jdg)
    in
      (theta, fn rho =>
         T.lookup rho v)
    end

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

