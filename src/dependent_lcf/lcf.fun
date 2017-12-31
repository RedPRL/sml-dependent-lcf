functor Lcf (structure L : LCF_LANGUAGE and I : LCF_INFO) : LCF =
struct
  structure L = L and Tl = Telescope (L.Var) and I = I
  datatype 'a state = |> of 'a I.t Tl.telescope * L.term

  infix 3 |>

  type 'a isjdg =
     {sort : 'a -> L.sort,
      subst : L.env -> 'a -> 'a,
      ren : L.ren -> 'a -> 'a}

  fun liftJdg isjdg = isjdg
  
  fun map f (psi |> m) =
    Tl.map (I.map f) psi |> m

  fun ret {sort, subst, ren} (a : 'a) =
    let
      val x = L.fresh ()
    in
      Tl.singleton x (I.ret a) |> L.var x (sort a)
    end

  fun 'a mul {sort, subst, ren} =
    let
      open Tl.ConsView

      fun go (psi : 'a I.t telescope, m : L.term, env : L.env, ppsi : 'a state I.t telescope) =
        case out ppsi of
           EMPTY => psi |> L.subst env m
         | CONS (x, stx, ppsi') =>
             let
               val psix |> mx = I.run stx
               val psix' = Tl.map (fn jdg => I.bind (stx, fn _ => I.map (subst env) jdg)) psix
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

functor LcfTraceInfo (Tr : LCF_TRACE) : 
sig
  datatype 'a traced = ::@ of Tr.t * 'a
  include LCF_INFO where type 'a t = 'a traced
end = 
struct
  datatype 'a traced = ::@ of Tr.t * 'a
  type 'a t = 'a traced

  infix ::@

  fun ret a = 
    Tr.empty ::@ a

  fun run (_ ::@ a) = 
    a

  fun map f (t ::@ a) = 
    t ::@ f a

  fun replace a (t ::@ _) = 
    t ::@ a

  fun bind (t ::@ a, k) = 
    let
      val t' ::@ b = k a
    in
      Tr.append (t, t') ::@ b
    end
end

structure LcfIdentityInfo : LCF_INFO = 
struct
  type 'a t = 'a
  fun ret a = a
  fun run a = a
  fun map f = f
  fun bind (a, k) = k a
  fun replace a _ = a
end

functor PlainLcf (L : LCF_LANGUAGE) : PLAIN_LCF = Lcf (structure L = L and I = LcfIdentityInfo)

functor TracedLcf (structure L : LCF_LANGUAGE and Tr : LCF_TRACE) : TRACED_LCF = 
struct
  local
    structure TrI = LcfTraceInfo (Tr)
    structure X = Lcf (structure L = L and I = TrI)
  in
    open X
    type trace = Tr.t
    datatype traced = datatype TrI.traced
  end
end
