(* backtracking *)
functor LcfUtilBt (Kit : LCF_UTIL_KIT) : LCF_UTIL =
struct
  open Kit Kit.Lcf

  infix |>



  exception todo
  fun ?e = raise e

  fun @@ (f, x) = f x
  infixr @@


  datatype 'a result = 
     OK of 'a
   | ERR of exn

  structure BT = 
  struct
    type 'a m = 'a result Logic.t
    fun map (f : 'a -> 'b) (m : 'a m) = Logic.map (fn OK a => OK (f a) | ERR exn => ERR exn) m
    fun ret (a : 'a) : 'a m = Logic.return (OK a)
    fun bind (m, f) = Logic.>>- (m, fn OK a => f a | ERR exn => Logic.return (ERR exn))
    fun throw exn = Logic.return (ERR exn)
  end

  type 'a m = 'a BT.m

  val >>- = BT.bind
  infix >>-

  type jdg = J.jdg
  type 'a rule = 'a -> 'a state
  type 'a tactic = 'a -> 'a state m
  type 'a multitactic = 'a state tactic

  fun wrap (t : 'a tactic) : 'a tactic = fn jdg =>
    t jdg handle exn => Logic.return (ERR exn)

  fun rule r jdg = 
    Logic.return (OK (r jdg) handle exn => ERR exn)

  val isjdg : jdg isjdg =
    {sort = J.sort,
     subst = J.subst,
     ren = J.ren}


  val idn : jdg tactic = BT.ret o ret isjdg

  fun each (ts : jdg tactic list) (psi |> vl) : jdg state state m =
    let
      open Tl.ConsView
      fun go (r : jdg state telescope) =
        fn (_, EMPTY) => BT.ret r
         | (t :: ts, CONS (x, jdg : jdg, psi)) =>
             wrap t jdg >>- (fn tjdg => go (Tl.snoc r x tjdg) (ts, out psi))
         | ([], CONS (x, jdg, psi)) => 
             go (Tl.snoc r x (ret isjdg jdg)) ([], out psi)
    in
      BT.map (fn psi => psi |> vl) @@ go Tl.empty (ts, out psi)
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
      fun go rho (r : jdg state telescope) =
        fn (_, EMPTY) => BT.ret r
         | (t :: ts, CONS (x, jdg : jdg, psi)) =>
            wrap t (J.subst rho jdg) >>-
              (fn tjdg as (psix |> vlx) =>
              let
                val rho' = L.Ctx.insert rho x vlx
              in
                go rho' (Tl.snoc r x tjdg) (ts, out psi)
              end)
         | ([], CONS (x, jdg, psi)) => 
            go rho (Tl.snoc r x (ret isjdg jdg)) ([], out psi)
    in
      BT.map (fn psi => psi |> vl) @@ go L.Ctx.empty Tl.empty (ts, out psi)
    end

  fun all t (psi |> vl) = 
    each (Tl.foldr (fn (_,_,ts) => t :: ts) [] psi) (psi |> vl)

  fun allSeq t (psi |> vl) = 
    eachSeq (Tl.foldr (fn (_,_,ts) => t :: ts) [] psi) (psi |> vl)

  fun seq (t : jdg tactic, m : jdg multitactic) (jdg : jdg) =
    BT.map m (t jdg)
      >>- BT.map (mul isjdg)

  exception Progress
  exception Complete

  fun then_ (t1, t2) =
    seq (t1, all t2)

  fun thenl (t, ts) =
    seq (t, each ts)

  fun thenf (t, (i, t')) =
    seq (t, only (i, t'))

  fun orelse_ (t1, t2) jdg =
    Logic.merge (t1 jdg) (t2 jdg)

  fun morelse (mt1, mt2) st =
    Logic.merge (mt1 st) (mt2 st)

  fun try t =
    orelse_ (t, idn)

  local
    open Tl.ConsView
    fun unifySubtelescopeAux (env1, env2) (psi1, psi2) =
      case (out psi1, out psi2) of
         (EMPTY, _) => SOME (env1, env2)
       | (CONS (x1, jdg1, psi1'), CONS (x2, jdg2, psi2')) =>
            if J.eq (J.ren env1 jdg1, J.ren env2 jdg2) then
              let
                val y = L.fresh ()
                val env1y = L.Ctx.insert env1 x1 y
                val env2y = L.Ctx.insert env2 x2 y
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
    t jdg >>- (fn st as (psi |> vl) =>
      let
        val psi' = Tl.singleton (L.fresh ()) jdg
      in
        case unifySubtelescope (psi', psi) of
           SOME _ => BT.throw Progress
         | NONE => BT.ret st
      end)

  fun mprogress mt (st as (psi |> _)) =
    mt st >>- (fn sst =>
      let
        val psi' |> _ = mul isjdg sst
      in
        case unifySubtelescope (psi, psi') of
           SOME _ => BT.throw Progress
         | NONE => BT.ret sst
      end)

  fun complete t jdg =
    wrap t jdg >>- (fn st as (psi |> _) => 
      if Tl.isEmpty psi then
        BT.ret st
      else
        BT.throw Complete)
end