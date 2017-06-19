functor Lcf (L : LCF_LANGUAGE) : LCF =
struct
  structure L = L and Tl = Telescope (L.Var)
  structure Eff = 
  struct 
    open IdMonad
    fun run x = x
  end

  type 'a eff = 'a
  datatype 'a state = |> of 'a eff Tl.telescope * L.term

  type 'a isjdg =
     {sort : 'a -> L.sort,
      subst : L.env -> 'a -> 'a}

  infix |>

  fun liftJdg isjdg = isjdg
  
  fun map f (psi |> m) =
    Tl.map f psi |> m

  fun ret {sort, subst} jdg =
    let
      val x = L.fresh ()
    in
      Tl.singleton x jdg |> L.var x (sort jdg)
    end

  fun 'a mul {sort, subst} =
    let
      open Tl.ConsView

      fun go (psi : 'a telescope, m : L.term, env : L.env, ppsi : 'a state telescope) =
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
end