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

  infix |> ||

  structure Eff : MONAD =
  struct
    type 'a t = 'a generic
    fun ret x = ([],[]) || x
    fun bind f ((us, xs) || m) =
      let
        val (us', xs') || m' = f m
      in
        (us @ us', xs @ xs') || m'
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
           ((sigmas @ sigmas', taus @ taus'), tau)
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
    fun substState {subst, sort} env (psi |> m) : 'a state =
      Tl.map (G.map (subst env)) psi |> L.subst env m

    fun printVars lbl xs = print (lbl ^ ": [" ^ ListSpine.pretty Var.toString ", " xs ^ "]\n")
  in
    fun 'a mul isjdg (ppsi |> abs) = 
      case out ppsi of 
         EMPTY => Tl.empty |> abs
       | CONS (x, stx : 'a state eff, ppsi') =>
           let
             val bs || ((psix : 'a eff telescope) |> absx) = stx
             val psix' = Tl.map (Eff.bind (fn x => bs || x)) psix

             val ((usx, xsx) \ mx, ((sigmas, taus), tau)) = inferb absx
             val (us', sigmas') = ListPair.unzip (#1 bs)
             val (xs', taus') = ListPair.unzip (#2 bs)

             val envx = 
               Tl.foldl 
                 (fn (y, yjdg, r) => 
                    let
                      val vl as ((ysigmas, ytaus), tau) = #sort (liftJdg isjdg) yjdg
                      val us = List.map (fn _ => Sym.named "u") ysigmas
                      val xs = List.map (fn _ => Var.named "x") ytaus
                      val ps = ListPair.map (fn (u, sigma) => (O.P.ret u, sigma)) (us' @ us, sigmas' @ ysigmas)
                      val ms = ListPair.map (fn (x, tau) => check (`x, tau)) (xs' @ xs, taus' @ ytaus)
                    in
                      Metavar.Ctx.insert r y (checkb ((us, xs) \ check (y $# (ps, ms), tau), vl))
                   end)
                 Metavar.Ctx.empty
                 psix

             val vlx = ((sigmas' @ sigmas, taus' @ taus), tau)
             val absx' = checkb ((us' @ usx, xs' @ xsx) \ substMetaenv envx mx, vlx)
             val env = Metavar.Ctx.insert Metavar.Ctx.empty x absx'
             val psi |> m' = substState isjdg env (mul isjdg (ppsi' |> abs))
           in
             Tl.append psix' psi |> m'
           end
  end

end