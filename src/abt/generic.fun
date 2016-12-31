signature LCF_GENERIC =
sig
  type ovar
  type osym
  type vsort
  type psort
  datatype 'a generic = || of ((osym * psort) list * (ovar * vsort) list) * 'a
  include LCF where type 'a Eff.t = 'a generic
end

functor LcfGeneric (L : LCF_ABT_LANGUAGE) : LCF_GENERIC =
struct
  structure L = L and Tl = Telescope (L.Var)

  type ovar = L.Abt.variable
  type osym = L.Abt.symbol
  type vsort = L.Abt.sort
  type psort = L.Abt.psort

  datatype 'a generic = || of ((osym * psort) list * (ovar * vsort) list) * 'a
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

  fun commuteEff (isjdg : 'a isjdg) (bs || ((psi : 'a eff Tl.telescope) |> abs)) : 'a eff state = 
    let
      open L.Abt infix \ $#
      val isjdg' = liftJdg isjdg
      val psi' : 'a eff eff Tl.telescope = Tl.map (fn a => bs || a) psi
      val env = 
        Tl.foldl
          (fn (x, bs' || jdg, r : L.env) => 
             let
               val ((sigmas, taus), tau) = #sort isjdg' (bs' || jdg)
               val us = List.map (fn _ => Sym.named "u") sigmas
               val xs = List.map (fn _ => Var.named "x") taus
               val (us', sigmas') = ListPair.unzip (#1 bs)
               val (xs', taus') = ListPair.unzip (#2 bs)
               val vl' = ((sigmas' @ sigmas, taus' @ taus), tau)
               val ps = ListPair.map (fn (u, sigma) => (O.P.ret u, sigma)) (us' @ us, sigmas' @ sigmas)
               val ms = ListPair.map (fn (x, tau) => check (`x, tau)) (xs' @ xs, taus' @ taus)
               val abs = checkb ((us' @ us, xs' @ xs) \ check (x $# (ps, ms), tau), vl')
             in
               Metavar.Ctx.insert r x abs
             end) 
          Metavar.Ctx.empty
          psi

      val (sbs, vbs) = bs
      val (slen, vlen) = (List.length sbs, List.length vbs)
      val ((us, xs) \ m, ((sigmas, taus), tau)) = inferb abs
      val (us', xs') = (List.drop (us, slen), List.drop (xs, vlen))
      val (sigmas', taus') = (List.drop (sigmas, slen), List.drop (taus, vlen))
      val m' = substMetaenv env m
      val abs' = checkb ((us', xs') \ m', ((sigmas', taus'), tau))
    in
      psi' |> abs'
    end
  
  fun 'a mul isjdg =
    let
      open Tl.ConsView
      val isjdg' as {sort,subst} = liftJdg isjdg
      fun go (psi : 'a eff telescope, m : L.term, env : L.env, ppsi : 'a eff state telescope) =
        case out ppsi of
           EMPTY => psi |> L.subst env m
         | CONS (x : L.var, (psix : 'a eff eff telescope) |> (mx : L.term), ppsi' : 'a eff state telescope) =>
             let
               val psix' : 'a eff telescope = Tl.map (subst env o G.bind (fn x => x)) psix
               val psi' = Tl.append psi psix'
               val env' = L.Ctx.insert env x mx
             in
               go (psi', m, env', ppsi')
             end
    in
      fn ((psi : 'a state eff telescope) |> m) => 
        go (Tl.empty, m, L.Ctx.empty, Tl.map (commuteEff isjdg) psi)
    end

end