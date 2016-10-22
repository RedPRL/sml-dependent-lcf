functor Lcf (L : LCF_LANGUAGE) : LCF =
struct
  structure L = L and Tl = Telescope (L.Var)

  datatype 'a state = |> of 'a Tl.telescope * L.term

  type 'a isjdg =
     {sort : 'a -> L.sort,
      subst : L.env -> 'a -> 'a}

  infix |>

  fun map f (psi |> m) =
    Tl.map f psi |> m

  fun ret {sort, subst} jdg =
    let
      val x = L.fresh ()
    in
      Tl.singleton x jdg |> L.var x (sort jdg)
    end

  fun mul {sort, subst} =
    let
      open Tl.ConsView

      fun go (psi, m, env, ppsi) =
        case out ppsi of
           EMPTY => psi |> L.subst env m
         | CONS (x, psix |> mx, ppsi') =>
             let
               val psix' = Tl.map (subst env) psix
               val psi' = Tl.append psi psix'
               val env' = L.Ctx.insert env x mx
             in
               go (psi', m, env', ppsi')
             end
    in
      fn (psi |> m) =>
        go (Tl.empty, m, L.Ctx.empty, psi)
    end

  type 'a tactic = 'a -> 'a state
  type 'a multitactic = 'a state tactic
end

signature LCF_UTIL_KIT =
sig
  structure Lcf : LCF
  structure J : LCF_JUDGMENT
    where type sort = Lcf.L.sort
    where type env = Lcf.L.term Lcf.L.Ctx.dict
end

functor LcfUtil (Kit : LCF_UTIL_KIT) : LCF_UTIL =
struct
  open Kit Kit.Lcf

  infix |>

  type 'a tactic = 'a -> 'a state
  type 'a multitactic = 'a state tactic

  val isjdg : J.jdg isjdg =
    {sort = J.sort,
     subst = J.subst}

  val idn =
    ret isjdg

  fun all t (psi |> vl) =
    Tl.map t psi |> vl

  fun each ts (psi |> vl) =
    let
      open Tl.ConsView
      fun go r =
        fn (_, EMPTY) => r
         | (t :: ts, CONS (x, jdg, psi)) =>
             go (Tl.snoc r x (t jdg)) (ts, out psi)
         | ([], CONS (x, jdg, psi)) =>
             go (Tl.snoc r x (idn jdg)) ([], out psi)
    in
      go Tl.empty (ts, out psi) |> vl
    end

  fun only (i, t) =
    let
      val ts = List.tabulate (i + 1, fn j => if i = j then t else idn)
    in
      each ts
    end

  fun seq (t, m) =
    mul isjdg o m o t

  fun then_ (t1, t2) =
    seq (t1, all t2)

  fun thenl (t, ts) =
    seq (t, each ts)

  fun thenf (t, (i, t')) =
    seq (t, only (i, t'))


  fun orelse_ (t1, t2) jdg =
    t1 jdg handle _ => t2 jdg

  fun try t =
    orelse_ (t, idn)

  local
    open Tl.ConsView
    fun unifySubtelescopeAux (env1, env2) (psi1, psi2) =
      case (out psi1, out psi2) of
         (EMPTY, _) => SOME (env1, env2)
       | (CONS (x1, jdg1, psi1'), CONS (x2, jdg2, psi2')) =>
            if J.eq (J.subst env1 jdg1, J.subst env2 jdg2) then
              let
                val y = L.fresh ()
                val ytm = L.var y (J.sort jdg1)
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

  exception Progress
  exception Complete

  fun progress t jdg =
    let
      val st as (psi |> vl) = t jdg
      val psi' = Tl.singleton (L.fresh ()) jdg
    in
      case unifySubtelescope (psi', psi) of
         SOME _ => raise Progress
       | NONE => st
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
