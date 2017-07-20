functor FreshSymbols (S : ABT_SYMBOL) =
struct
  fun freshSyms ss =
    let
      fun go i ctx [] = []
        | go i ctx (s :: ss) =
            let
              val u = S.fresh ctx ("?" ^ Int.toString i)
            in
              (u, s) :: go (i + 1) (S.Ctx.insert ctx u ()) ss
            end
    in
      go 0 S.Ctx.empty ss
    end
end

signature LCF_ABT_LANGUAGE =
sig
  structure Abt : ABT
  include LCF_LANGUAGE
    where type sort = Abt.valence
    where type Var.t = Abt.Metavar.t
    where type 'a Ctx.dict = 'a Abt.Metavar.Ctx.dict
    where type term = Abt.abs
end

functor LcfAbtLanguage (Abt : ABT) : LCF_ABT_LANGUAGE =
struct
  structure Abt = Abt
  structure Var = Abt.Metavar
  structure Ctx = Abt.Metavar.Ctx
  type sort = Abt.valence
  type var = Var.t
  type term = Abt.abs
  type ctx = sort Ctx.dict
  type env = term Ctx.dict

  local
    val counter = ref 0
  in
    fun fresh () =
      (counter := !counter + 1;
      Var.named (Int.toString (!counter)))
  end

  local
    structure FreshSyms = FreshSymbols (Abt.Sym) and FreshVars = FreshSymbols (Abt.Var)
  in
    fun var v vl =
      let
        open Abt infix \ $#
        val ((sigmas, taus), tau) = vl
        val syms = FreshSyms.freshSyms sigmas
        val params = List.map (fn (a, sigma) => (O.P.ret a, sigma)) syms
        val vars = FreshVars.freshSyms taus
        val varTerms = List.map (fn (x,tau) => check (`x, tau)) vars
        val tm = check (v $# (params, varTerms), tau)
      in
        checkb ((List.map #1 syms, List.map #1 vars) \ tm, vl)
      end
  end

  val subst = Abt.mapAbs o Abt.substMetaenv
  val eq = Abt.eqAbs
end
