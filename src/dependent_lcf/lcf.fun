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

      fun go (psi, cl as L.CLO (m, env), ppsi) =
        case out ppsi of
           EMPTY => psi |> L.force cl
         | CONS (x, psix |> mx, ppsi') =>
             let
               val psix' = Tl.map (subst env) psix
               val psi' = Tl.append psi psix'
               val env' = L.Ctx.insert env x (L.CLO (mx, env))
             in
               go (psi', L.CLO (m, env'), ppsi')
             end
    in
      fn (psi |> m) =>
        go (Tl.empty, L.CLO (m, L.Ctx.empty), psi)
    end

  type 'a tactic = 'a -> 'a state
  type 'a multitactic = 'a state tactic
end
