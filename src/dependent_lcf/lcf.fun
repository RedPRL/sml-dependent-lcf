functor Lcf (L : LCF_LANGUAGE) : LCF =
struct
  structure L = L and Tl = Telescope (L.Var)

  datatype 'a info = ::@ of string list * 'a
  datatype 'a state = |> of 'a info Tl.telescope * L.term

  infix 2 ::@ 
  infix 3 |>

  fun newInfo a = 
    [] ::@ a

  fun mapInfo f (i ::@ a) = 
    i ::@ f a

  fun projInfo (_ ::@ a) = 
    a
    
  type 'a isjdg =
     {sort : 'a -> L.sort,
      subst : L.env -> 'a -> 'a,
      ren : L.ren -> 'a -> 'a}

  
  fun liftJdg isjdg = isjdg
  
  fun map f (psi |> m) =
    Tl.map (mapInfo f) psi |> m

  fun ret {sort, subst, ren} (a : 'a) =
    let
      val x = L.fresh ()
    in
      Tl.singleton x (newInfo a) |> L.var x (sort a)
    end

  fun 'a mul {sort, subst, ren} =
    let
      open Tl.ConsView

      fun go (psi : 'a info telescope, m : L.term, env : L.env, ppsi : 'a state info telescope) =
        case out ppsi of
           EMPTY => psi |> L.subst env m
         | CONS (x, i ::@ (psix : 'a info telescope) |> mx, ppsi') =>
             let
               val psix' = Tl.map (fn i' ::@ jdg => i @ i' ::@ subst env jdg) psix
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