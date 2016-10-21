functor FreshSymbols (S : ABT_SYMBOL) =
struct
  fun freshSyms ss =
    let
      fun go ctx [] = []
        | go ctx (s :: ss) =
            let
              val u = S.fresh ctx "?"
            in
              (u, s) :: go (S.Ctx.insert ctx u ()) ss
            end
    in
      go S.Ctx.empty ss
    end

end

functor HoleUtil (Kit : HOLE_KIT) : HOLE_UTIL =
struct
  open Kit Kit.J
  structure Spine = Tm.O.Ar.Vl.Sp

  structure VarCtx = Tm.Var.Ctx and SymCtx = Tm.Sym.Ctx and MetaCtx = Tm.Metavar.Ctx
  structure FreshSyms = FreshSymbols (Tm.Sym) and FreshVars = FreshSymbols (Tm.Var)

  fun makeHole (v : J.metavariable, vl : J.valence) : Tm.abs =
    let
      open Tm infix \ $#
      val ((sigmas, taus), tau) = vl
      val syms = FreshSyms.freshSyms sigmas
      val params = List.map (fn (a, sigma) => (O.P.ret a, sigma)) syms
      val vars = FreshVars.freshSyms taus
      val varTerms = List.map (fn (x,tau) => check (`x, tau)) vars
      val tm = check (v $# (params, varTerms), tau)
    in
      checkb ((List.map #1 syms, List.map #1 vars) \ tm, vl)
    end

  fun openEnv psi =
    let
      open T.ConsView
      fun go EMPTY rho = rho
        | go (CONS (x, jdg, phi)) rho =
            go (out phi) (MetaCtx.insert rho x (makeHole (x, evidenceValence jdg)))
    in
      go (out psi) MetaCtx.empty
    end
end
