functor HoleUtil (Kit : HOLE_KIT) : HOLE_UTIL =
struct
  open Kit Kit.J
  structure Spine = Tm.Operator.Arity.Valence.Spine

  structure VarCtx = Tm.Variable.Ctx and SymCtx = Tm.Symbol.Ctx
  structure MetaCtxUtil = ContextUtil (structure Ctx = Tm.Metavariable.Ctx and Elem = Tm.Operator.Arity.Valence)

  (* TODO: use Variable.fresh *)
  fun makeHole (v : J.metavariable, vl : J.valence) : Tm.abs =
    let
      open Tm infix \ $#
      val ((sigmas, taus), tau) = vl
      val syms = Spine.map (fn sigma => (Symbol.named "?", sigma)) sigmas
      val vars = Spine.map (fn _ => Variable.named "?") taus
      val varTerms =
        Spine.Pair.mapEq
          (fn (x,tau) => check (`x, tau))
          (vars, taus)
      val tm = check (v $# (syms, varTerms), tau)
    in
      checkb ((Spine.map #1 syms, vars) \ tm, vl)
    end

  fun openEnv psi =
    let
      open T.ConsView
      fun go EMPTY rho = rho
        | go (CONS (x, jdg, phi)) rho =
            go (out phi) (T.snoc rho x (makeHole (x, evidenceValence jdg)))
    in
      go (out psi) T.empty
    end
end


