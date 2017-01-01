signature LCF_GENERIC =
sig
  structure Abt : ABT
  datatype 'a generic = || of ((Abt.symbol * Abt.psort) list * (Abt.variable * Abt.sort) list) * 'a
  include LCF where type 'a Eff.t = 'a generic
end

signature LCF_BINDING_JUDGMENT = 
sig
  type symenv
  type varenv

  include LCF_JUDGMENT

  val substSymenv : symenv -> jdg -> jdg
  val substVarenv : varenv -> jdg -> jdg
end

signature LCF_GENERIC_UTIL_KIT =
sig
  structure Lcf : LCF_GENERIC
  structure J : LCF_BINDING_JUDGMENT
    where type sort = Lcf.L.sort
    where type env = Lcf.L.term Lcf.L.Ctx.dict
    where type symenv = Lcf.Abt.symenv
    where type varenv = Lcf.Abt.varenv
end

functor LcfGenericUtil (Kit : LCF_GENERIC_UTIL_KIT) : LCF_UTIL =
struct
  local
    local
      open Kit Kit.Lcf Kit.Lcf.Abt infix ||
    in
      fun effEq ((us1, xs1) || jdg1, (us2, xs2) || jdg2) =
        let
          val (srho1, srho2) =
            ListPair.foldl 
              (fn ((u1, _), (u2, _), (r1, r2)) => let val u = O.P.ret (Sym.named "u") in (Sym.Ctx.insert r1 u1 u, Sym.Ctx.insert r2 u2 u) end)
              (Sym.Ctx.empty, Sym.Ctx.empty)
              (us1, us2)
          val (vrho1, vrho2) =
            ListPair.foldl 
              (fn ((x1, tau), (x2, _), (r1, r2)) => let val x = check (` (Var.named "x"), tau) in (Var.Ctx.insert r1 x1 x, Var.Ctx.insert r2 x2 x) end)
              (Var.Ctx.empty, Var.Ctx.empty)
              (xs1, xs2)
          val jdg1 = J.substVarenv vrho1 (J.substSymenv srho1 jdg1)
          val jdg2 = J.substVarenv vrho2 (J.substSymenv srho2 jdg2)
        in
          J.eq (jdg1, jdg2)
        end
    end
    structure Util = LcfUtil (open Kit val effEq = effEq)
  in
    open Util
  end
end

functor LcfGeneric (L : LCF_ABT_LANGUAGE) : LCF_GENERIC =
struct
  structure L = L and Tl = Telescope (L.Var) and Abt = L.Abt

  datatype 'a generic = || of ((Abt.symbol * Abt.psort) list * (Abt.variable * Abt.sort) list) * 'a
  type 'a eff = 'a generic
  datatype 'a state = |> of 'a eff Tl.telescope * L.term

  type 'a isjdg =
     {sort : 'a -> L.sort,
      subst : L.env -> 'a -> 'a}

  fun @@ (f, x) = f x
  infix @@ |> ||

  structure Eff : MONAD =
  struct
    type 'a t = 'a generic
    fun ret x = ([],[]) || x
    fun bind f ((us', xs') || m) =
      let
        val (us, xs) || m' = f m
      in
        (us' @ us, xs' @ xs) || m'
      end
  end

  structure G = struct structure F = MonadApplicative (Eff) open F Eff end

  fun liftJdg {sort, subst} =
    {sort = 
      (fn (us, xs) || m => 
         let 
           val ((sigmas, taus), tau) = sort m
           val (sigmas', taus') = (List.map #2 us, List.map #2 xs)
         in
           ((sigmas' @ sigmas, taus' @ taus), tau)
         end),
     subst = (fn env => G.map (subst env))}

  fun map f (psi |> m) =
    Tl.map (G.map f) psi |> m

  fun ret isjdg jdg =
    let
      val x = L.fresh ()
      val jdg' = G.ret jdg
      val {sort,...} = liftJdg isjdg
    in
      Tl.singleton x jdg' |> L.var x (sort jdg')
    end

  structure Print = DebugShowAbt (L.Abt)

  local
    open L.Abt Tl.ConsView infix \ $#
    structure Tl = TelescopeUtil (Tl)

    fun substTele (isjdg : 'a isjdg) env (psi : 'a eff telescope) = 
      Tl.map (G.map (#subst isjdg env)) psi

    fun substState isjdg env (psi |> m) : 'a state =
      substTele isjdg env psi |> L.subst env m

    fun prependState psi' (psi |> abs) =
      Tl.append psi' psi |> abs

    fun prependBindings (symBindings, varBindings) abs = 
      let
        val (us', sigmas') = ListPair.unzip symBindings
        val (xs', taus') = ListPair.unzip varBindings
        val ((us, xs) \ m, ((sigmas, taus), tau)) = inferb abs
        val binder = (us' @ us, xs' @ xs) \ m
        val valence = ((sigmas' @ sigmas, taus' @ taus), tau)
      in
        checkb (binder, valence)
      end

    fun ::= (x, abs) = Metavar.Ctx.insert Metavar.Ctx.empty x abs
    infix ::=

    fun makeRebindingEnv (isjdg : 'a isjdg) bindings (psi : 'a telescope) =
      let
        val (symBindings, varBindings) = bindings
        val (us', sigmas') = ListPair.unzip symBindings
        val (xs', taus') = ListPair.unzip varBindings
      in
        Tl.foldl 
          (fn (x, jdg, env) => 
             let
               val ((sigmas, taus), tau) = #sort isjdg jdg
               val us = List.map (fn _ => Sym.named "u") sigmas
               val xs = List.map (fn _ => Var.named "x") taus
               (*check order of application here*)
               val ps = ListPair.map (fn (u, sigma) => (O.P.ret u, sigma)) (us' @ us, sigmas' @ sigmas)
               val ms = ListPair.map (fn (x, tau) => check (`x, tau)) (xs' @ xs, taus' @ taus)
               val meta = check (x $# (ps, ms), tau)
               val binder = (us, xs) \ meta
               val abs = checkb (binder, ((sigmas, taus), tau))
             in
               Metavar.Ctx.insert env x abs
             end)
          Metavar.Ctx.empty
          psi
      end
  in
    fun 'a mul isjdg (ppsi |> abs) = 
      case out ppsi of 
         EMPTY => Tl.empty |> abs
       | CONS (x, bindings || (psix |> absx), ppsi') =>
           let
             val envx = makeRebindingEnv (liftJdg isjdg) bindings psix
             val absx' = prependBindings bindings @@ mapAbs (substMetaenv envx) absx
             val psix' = Tl.map (Eff.bind (fn jdg => bindings || #subst isjdg envx jdg)) psix

             val state' = 
               Tl.map (G.map (substState isjdg (x ::= absx'))) ppsi'
                 |> L.subst (x ::= absx') abs
           in
             prependState psix' @@ mul isjdg state'
           end
  end

end