functor TracedLcf (structure L : LCF_LANGUAGE and Tr : LCF_TRACE) : LCF =
struct
  structure L = L and Tl = Telescope (L.Var) and Tr = Tr

  datatype 'a traced = ::@ of Tr.t * 'a
  datatype 'a state = |> of 'a traced Tl.telescope * L.term

  infix 2 ::@ 
  infix 3 |>

  type 'a isjdg =
     {sort : 'a -> L.sort,
      subst : L.env -> 'a -> 'a,
      ren : L.ren -> 'a -> 'a}

  fun liftJdg isjdg = isjdg
  
  fun map f (psi |> m) =
    Tl.map (fn (log ::@ x) => log ::@ f x) psi |> m

  fun ret {sort, subst, ren} (a : 'a) =
    let
      val x = L.fresh ()
    in
      Tl.singleton x (Tr.empty ::@ a) |> L.var x (sort a)
    end

  fun 'a mul {sort, subst, ren} =
    let
      open Tl.ConsView

      fun go (psi : 'a traced telescope, m : L.term, env : L.env, ppsi : 'a state traced telescope) =
        case out ppsi of
           EMPTY => psi |> L.subst env m
         | CONS (x, i ::@ (psix : 'a traced telescope) |> mx, ppsi') =>
             let
               val psix' = Tl.map (fn i' ::@ jdg => Tr.append (i, i') ::@ subst env jdg) psix
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

functor LcfListTrace (type e) : LCF_TRACE = 
struct
  type t = e list
  val empty = []
  val append = op@
end

structure LcfBlankTrace :> LCF_TRACE = 
struct
  type t = unit
  val empty = ()
  fun append _ = ()
end

functor Lcf (L : LCF_LANGUAGE) : LCF = TracedLcf (structure L = L and Tr = LcfBlankTrace)