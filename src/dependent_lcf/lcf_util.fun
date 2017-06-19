signature LCF_UTIL_KIT_PURE =
sig
  structure Lcf : LCF
  structure J : LCF_JUDGMENT
    where type sort = Lcf.L.sort
    where type env = Lcf.L.term Lcf.L.Ctx.dict
end

signature LCF_UTIL_KIT =
sig
  include LCF_UTIL_KIT_PURE
  val effEq : J.jdg Lcf.eff * J.jdg Lcf.eff -> bool
end


functor LcfUtil (Kit : LCF_UTIL_KIT) : LCF_UTIL =
struct
  open Kit Kit.Lcf
  structure Eff = 
  struct
    structure F = MonadApplicative (Eff)
    open Eff F
  end

  infix |>

  type jdg = J.jdg
  type 'a tactic = 'a -> 'a state
  type 'a multitactic = 'a state tactic

  val isjdg : jdg isjdg =
    {sort = J.sort,
     subst = J.subst}

  val idn =
    ret isjdg

  fun 'a all (t : 'a -> 'a state) (psi |> vl) =
    Tl.map (Eff.map t) psi |> vl

  fun each (ts : jdg tactic list) (psi |> vl) =
    let
      open Tl.ConsView
      fun go (r : jdg state eff telescope) =
        fn (_, EMPTY) => r
         | (t :: ts, CONS (x, jdg : jdg eff, psi)) =>
             go (Tl.snoc r x (Eff.map t jdg)) (ts, out psi)
         | ([], CONS (x, jdg, psi)) => 
             go (Tl.snoc r x (Eff.map idn jdg)) ([], out psi)
    in
      go Tl.empty (ts, out psi) |> vl
    end

  fun only (i, t) =
    let
      val ts = List.tabulate (i + 1, fn j => if i = j then t else idn)
    in
      each ts
    end

  fun eachSeq (ts : jdg tactic list) (psi |> vl) =
    let
      open Tl.ConsView
      fun go rho (r : jdg state eff telescope) =
        fn (_, EMPTY) => r
         | (t :: ts, CONS (x, jdg : jdg eff, psi)) =>
             let
               val etjdg = Eff.map (t o J.subst rho) jdg
               val psix |> vlx = Eff.run etjdg
               val rho' = L.Ctx.insert rho x vlx
             in
               go rho' (Tl.snoc r x etjdg) (ts, out psi)
             end
         | ([], CONS (x, jdg, psi)) => 
             go rho (Tl.snoc r x (Eff.map idn jdg)) ([], out psi)
    in
      go L.Ctx.empty Tl.empty (ts, out psi) |> vl
    end

  fun allSeq (t : jdg tactic) (psi |> vl) =
    let
      open Tl.ConsView
      fun go rho (r : jdg state eff telescope) =
        fn EMPTY => r
         | CONS (x, jdg : jdg eff, psi) =>
             let
               val etjdg = Eff.map (t o J.subst rho) jdg
               val psix |> vlx = Eff.run etjdg
               val rho' = L.Ctx.insert rho x vlx
             in
               go rho' (Tl.snoc r x etjdg) (out psi)
             end
    in
      go L.Ctx.empty Tl.empty (out psi) |> vl
    end

  fun allSeq t (psi |> vl) = 
    eachSeq (Tl.foldr (fn (_,_,ts) => t :: ts) [] psi) (psi |> vl)

  fun seq (t, m) =
    mul isjdg o m o t

  exception Progress
  exception Complete

  fun then_ (t1, t2) =
    seq (t1, all t2)

  fun thenl (t, ts) =
    seq (t, each ts)


  fun thenf (t, (i, t')) =
    seq (t, only (i, t'))


  fun orelse_ (t1, t2) jdg =
    t1 jdg handle _ => t2 jdg

  fun morelse (mt1, mt2) st =
    mt1 st handle _ => mt2 st

  fun try t =
    orelse_ (t, idn)

  local
    open Tl.ConsView
    val {sort, subst} = liftJdg isjdg
    fun unifySubtelescopeAux (env1, env2) (psi1, psi2) =
      case (out psi1, out psi2) of
         (EMPTY, _) => SOME (env1, env2)
       | (CONS (x1, jdg1, psi1'), CONS (x2, jdg2, psi2')) =>
            if effEq (subst env1 jdg1, subst env2 jdg2) then
              let
                val y = L.fresh ()
                val ytm = L.var y (sort jdg1)
                val env1y = L.Ctx.insert env1 x1 ytm
                val env2y = L.Ctx.insert env2 x2 ytm
              in
                unifySubtelescopeAux (env1y, env2y) (psi1', psi2')
              end
            else
              unifySubtelescopeAux (env1, env2) (psi1, psi2')
       | _ => NONE
  in
    val unifySubtelescope = unifySubtelescopeAux (L.Ctx.empty, L.Ctx.empty)
  end

  val isSubtelescope =
    Option.isSome o unifySubtelescope

  exception Progress
  exception Complete

  fun progress t (jdg : jdg) =
    let
      val st as (psi |> vl) = t jdg
      val psi' = Tl.singleton (L.fresh ()) (Eff.ret jdg)
    in
      case unifySubtelescope (psi', psi) of
         SOME _ => raise Progress
       | NONE => st
    end

  fun mprogress mt (st as (psi |> _)) =
    let
      val sst = mt st
      val psi' |> _ = mul isjdg sst
    in
      case unifySubtelescope (psi, psi') of
         SOME _ => raise Progress
       | NONE => sst
    end

  fun complete t jdg =
    let
      val st as (psi |> _) = t jdg
    in
      if Tl.isEmpty psi then
        st
      else
        raise Complete
    end
end

functor LcfUtilPure (Kit : LCF_UTIL_KIT_PURE where type 'a Lcf.Eff.t = 'a) = 
  LcfUtil (struct open Kit val effEq = J.eq end)