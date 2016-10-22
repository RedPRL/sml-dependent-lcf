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

functor LCF_UTIL (Kit : LCF_UTIL_KIT) : LCF_UTIL =
struct
  open Kit Kit.Lcf

  infix |>

  type 'a tactic = 'a -> 'a state
  type 'a multitactic = 'a state tactic

  val isjdg : J.jdg isjdg =
    {sort = J.sort,
     subst = J.subst}

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
             go (Tl.snoc r x (ret isjdg jdg)) ([], out psi)
    in
      go Tl.empty (ts, out psi) |> vl
    end

  fun only (i, t) =
    let
      val ts = List.tabulate (i + 1, fn j => if i = j then t else ret isjdg)
    in
      each ts
    end

  fun seq (t, m) =
    mul isjdg o m o t

  fun then' (t1, t2) =
    seq (t1, all t2)

  fun thenl (t, ts) =
    seq (t, each ts)

  fun thenf (t, (i, t')) =
    seq (t, only (i, t'))
end
