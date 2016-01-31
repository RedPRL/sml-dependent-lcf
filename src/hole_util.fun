functor HoleUtil (Kit : HOLE_KIT) : HOLE_UTIL =
struct
  open Kit Kit.J
  structure Spine = Tm.Operator.Arity.Valence.Spine
  structure MetaCtxUtil = ContextUtil (structure Ctx = Tm.MetaCtx and Elem = Tm.Operator.Arity.Valence)

  fun makeHole (v : J.metavariable, vl : J.valence) : Tm.abs =
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
              (T.snoc rho (x, makeHole (x, evidenceValence jdg)))
    in
      go (out psi) T.empty
    end
end


