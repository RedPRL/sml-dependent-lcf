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

  structure VarCtx = Tm.Var.Ctx and SymCtx = Tm.Sym.Ctx
  structure MetaCtxUtil = ContextUtil (structure Ctx = Tm.Metavar.Ctx and Elem = Tm.O.Ar.Vl)
  structure FreshSyms = FreshSymbols (Tm.Sym) and FreshVars = FreshSymbols (Tm.Var)

  fun makeHole (v : J.metavariable, vl : J.valence) : Tm.abs =
    let
      open Tm infix \ $#
      val ((sigmas, taus), tau) = vl
      val syms = FreshSyms.freshSyms sigmas
      val vars = FreshVars.freshSyms taus
      val varTerms = List.map (fn (x,tau) => check (`x, tau)) vars
      val tm = check (v $# (syms, varTerms), tau)
    in
      checkb ((List.map #1 syms, List.map #1 vars) \ tm, vl)
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
