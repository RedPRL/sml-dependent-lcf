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

  local
    open L.Abt Tl.ConsView infix \ $$ $#
    fun substState (isjdg : 'a isjdg) env (psi |> m) : 'a state =
      Tl.map (G.map (#subst isjdg env)) psi |> L.subst env m
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

             val mx' = 
               Tl.foldl 
                 (fn (y : L.var, jdg : 'a eff, r) =>
                   let
                     val vl as ((psorts, vsorts), tau) = #sort (liftJdg isjdg) jdg
                     val us = List.map (fn _ => Sym.named "u") psorts
                     val xs = List.map (fn _ => Var.named "x") vsorts

                     val ps = ListPair.map (fn (u, sigma) => (O.P.ret u, sigma)) (us' @ us, sigmas' @ psorts)
                     val ms = ListPair.map (fn (x, tau) => check (`x, tau)) (xs' @ xs, taus' @ vsorts)

                     val binder = (us, xs) \ check (y $# (ps, ms), tau)
                     val abs = checkb (binder, vl)
                   in
                     substMetavar (abs, y) r
                   end) 
                 mx 
                 psix
             
             val bndx' = (us' @ usx, xs' @ xsx) \ mx'
             val absx' = checkb (bndx', ((sigmas' @ sigmas, taus' @ taus), tau))
             val env = Metavar.Ctx.insert Metavar.Ctx.empty x absx'
             val psi |> m' = substState isjdg env (mul isjdg (ppsi' |> abs))
           in
             Tl.append psix' psi |> m'
           end
  end

end