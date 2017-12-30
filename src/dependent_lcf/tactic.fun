signature LCF_TACTIC_KIT =
sig
  structure Lcf : LCF
  structure J : LCF_JUDGMENT
    where type sort = Lcf.L.sort
    where type env = Lcf.L.term Lcf.L.Ctx.dict
    where type ren = Lcf.L.var Lcf.L.Ctx.dict
end

functor LcfMonad (type env) :>
sig
  include LCF_TACTIC_MONAD where type env = env
  exception Refine of exn list
end = 
struct
  type env = env

  fun @@ (f, x) = f x
  infix @@

  exception Refine of exn list
  structure L = ListT (Identity)
  structure E = ErrorT (L)
  structure M = ReaderT (type r = env structure M = E)

  open M

  exception todo
  fun ?e = raise e

  local
    fun runAux p exns m =
      case L.uncons m of 
         SOME (Result.OK a, n) => if p a then a else runAux p exns n
       | SOME (Result.ERR exn, n) => runAux p (exn :: exns) n
       | NONE => raise Refine exns
  in
    fun run (env : env) (m, p) =
      runAux p [] (m env)
  end

  fun mapEnv (f : env -> env) : 'a m -> 'a m =
    fn m => fn env => 
      m (f env)

  fun getEnv env = 
    E.ret env
  
 fun throw exn env =
   E.throw exn

 fun mapErr f m env =
   E.mapErr f (m env)

 fun orAux env (m1, m2) = 
   case L.uncons m1 of 
      SOME (Result.OK a, _) => m1
    | SOME (Result.ERR exn, n1) => orAux env (n1, m2)
    | _ => m2 env

 fun or (m1 : 'a m, m2 : 'a m) : 'a m =
   fn env => 
     orAux env (m1 env, m2)
   
  fun par (m1, m2) env =
    L.concat (m1 env, m2 env)
end

structure LcfMonad = LcfMonad (type env = unit)

functor LcfTactic
  (include LCF_TACTIC_KIT
   structure M : LCF_TACTIC_MONAD) : LCF_TACTIC =
struct
  open Lcf
  structure R = Reader (type r = M.env) and M = M and J = J

  infix |>

  type jdg = J.jdg

  type 'a rule = 'a -> 'a state R.m
  type 'a tactic = 'a -> 'a state M.m
  type 'a multitactic = 'a state tactic

  val isjdg : jdg isjdg =
    {sort = J.sort,
     subst = J.subst,
     ren = J.ren}

  fun @@ (f, x) = f x
  infix @@

  fun wrap (t : 'a tactic) : 'a tactic = fn jdg =>
    t jdg handle exn => M.throw exn

  fun rule r jdg =
    M.bind (M.getEnv, fn env =>
      M.ret (r jdg env)
      handle exn => M.throw exn)

  fun mapEnv f tac jdg =
    M.mapEnv f (tac jdg)

  val idn = M.ret o ret isjdg

  fun matchGoal f jdg = 
    f jdg jdg

  (* This may be a bad idea ! *)
  fun >>= (m, f) = M.bind (m, f)
  infix >>=

  fun each (ts : jdg tactic list) (psi |> vl) : jdg state state M.m =
    let
      open Tl.ConsView
      fun go (r : jdg state telescope) =
        fn (_, EMPTY) => M.ret r
         | (t :: ts, CONS (x, jdg : jdg, psi)) =>
             wrap t jdg >>= (fn tjdg => go (Tl.snoc r x tjdg) (ts, out psi))
         | ([], CONS (x, jdg, psi)) => 
             go (Tl.snoc r x (ret isjdg jdg)) ([], out psi)
    in
      go Tl.empty (ts, out psi) >>= (fn psi => M.ret (psi |> vl))
    end


  fun eachSeq (ts : jdg tactic list) (psi |> vl) =
    let
      open Tl.ConsView
      fun go rho (r : jdg state telescope) =
        fn (_, EMPTY) => M.ret r
         | (t :: ts, CONS (x, jdg : jdg, psi)) =>
            wrap t (J.subst rho jdg) >>=
              (fn tjdg as (psix |> vlx) =>
               let
                 val rho' = L.Ctx.insert rho x vlx
               in
                 go rho' (Tl.snoc r x tjdg) (ts, out psi)
               end)
         | ([], CONS (x, jdg, psi)) => 
            go rho (Tl.snoc r x (ret isjdg jdg)) ([], out psi)
    in
      go L.Ctx.empty Tl.empty (ts, out psi) >>= (fn psi => M.ret (psi |> vl))
    end

  fun only (i, t) =
    let
      val ts = List.tabulate (i + 1, fn j => if i = j then t else idn)
    in
      each ts
    end

  fun allSeq t (psi |> vl) =
    eachSeq (Tl.foldr (fn (_,_,ts) => t :: ts) [] psi) (psi |> vl)

  fun all t (psi |> vl) =
    each (Tl.foldr (fn (_,_,ts) => t :: ts) [] psi) (psi |> vl)

  fun seq (t: jdg tactic, m : jdg multitactic) jdg =
    wrap t jdg >>= M.map (mul isjdg) o m

  exception Progress
  exception Complete

  fun then_ (t1, t2) =
    seq (t1, allSeq t2)

  fun thenl (t, ts) =
    seq (t, eachSeq ts)

  fun thenf (t, (i, t')) =
    seq (t, only (i, t'))

  fun orelse_ (t1, t2) jdg =
    M.or (wrap t1 jdg, wrap t2 jdg)

  fun par (t1, t2) jdg =
    M.par (wrap t1 jdg, wrap t2 jdg)

  fun morelse (mt1, mt2) st =
    M.or (wrap mt1 st, wrap mt2 st)

  fun mpar (mt1, mt2) st =
    M.par (wrap mt1 st, wrap mt2 st)

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
    t jdg >>= (fn st as (psi |> vl) =>
      let
        val psi' = Tl.singleton (L.fresh ()) jdg
      in
        case unifySubtelescope (psi', psi) of
           SOME _ => M.throw Progress
         | NONE => M.ret st
      end)

  fun mprogress mt (st as (psi |> _)) =
    mt st >>= (fn sst =>
      let
        val psi' |> _ = mul isjdg sst
      in
        case unifySubtelescope (psi, psi') of
           SOME _ => M.throw Progress
         | NONE => M.ret sst
      end)

  fun complete t jdg =
    wrap t jdg >>= (fn st as (psi |> _) => 
      if Tl.isEmpty psi then
        M.ret st
      else
        M.throw Complete)
end