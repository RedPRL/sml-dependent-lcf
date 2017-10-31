signature LCF_TACTIC_KIT =
sig
  structure Lcf : LCF
  structure J : LCF_JUDGMENT
    where type sort = Lcf.L.sort
    where type env = Lcf.L.term Lcf.L.Ctx.dict
    where type ren = Lcf.L.var Lcf.L.Ctx.dict
end

structure LcfMonad :
sig
  include LCF_TACTIC_MONAD
  exception Refine of exn list
end = 
struct
  fun @@ (f, x) = f x
  infix @@

  (* type name = string *)
  exception Refine of exn list

  (* structure R = Reader (type r = name list) *)
  structure L = ListT (Identity)
  structure M = ErrorT (L)

  open M

  local
    fun runAux p exns m =
      case L.uncons m of
         SOME (OK a, n) => if p a then a else runAux p exns n
       | SOME (ERR exn, n) => runAux p (exn :: exns) n
       | NONE => raise Refine exns
  in
    fun run (m, p) =
      runAux p [] m
  end

  fun shortcircuit (m : 'a m, p, f : 'a -> 'b m) =
    let
      val h = 
        case L.uncons m of
           SOME (OK a, n) => if p a then f a else L.concat (f a, shortcircuit (n, p, f))
         | SOME (ERR exn, n) => L.cons (ERR exn, shortcircuit (n, p, f))
         | NONE => L.emp ()
    in
      h 
    end

  (* fun getEnv h = 
    M.bind (M.lift (L.lift h), fn x => x) *)

 fun or (m1 : 'a m, m2 : 'a m) =
    case L.uncons m1 of 
        SOME (OK a, _) => m1
      | SOME (ERR exn, n1) => or (n1, m2)
      | _ => m2

  val par : 'a m * 'a m -> 'a m = L.concat
end

functor LcfTactic (include LCF_TACTIC_KIT structure M : LCF_TACTIC_MONAD) : LCF_TACTIC =
struct
  open Lcf
  structure M = M and J = J

  infix |>

  type jdg = J.jdg

  type 'a rule = 'a -> 'a state
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
    M.ret (r jdg)
    handle exn => M.throw exn

  val idn = M.ret o ret isjdg

  fun matchGoal f jdg = 
    f jdg jdg

  fun >>-* (m, f) = 
    M.shortcircuit (m, fn psi |> _ => Tl.isEmpty psi, f)

  infix >>-*

  fun each (ts : jdg tactic list) (psi |> vl) : jdg state state M.m =
    let
      open Tl.ConsView
      fun go (r : jdg state telescope) =
        fn (_, EMPTY) => M.ret r
         | (t :: ts, CONS (x, jdg : jdg, psi)) =>
             wrap t jdg >>-* (fn tjdg => go (Tl.snoc r x tjdg) (ts, out psi))
         | ([], CONS (x, jdg, psi)) => 
             go (Tl.snoc r x (ret isjdg jdg)) ([], out psi)
    in
      M.shortcircuit (go Tl.empty (ts, out psi), Tl.isEmpty, fn psi => M.ret (psi |> vl))
    end


  fun eachSeq (ts : jdg tactic list) (psi |> vl) =
    let
      open Tl.ConsView
      fun go rho (r : jdg state telescope) =
        fn (_, EMPTY) => M.ret r
         | (t :: ts, CONS (x, jdg : jdg, psi)) =>
            wrap t (J.subst rho jdg) >>-*
              (fn tjdg as (psix |> vlx) =>
               let
                 val rho' = L.Ctx.insert rho x vlx
               in
                 go rho' (Tl.snoc r x tjdg) (ts, out psi)
               end)
         | ([], CONS (x, jdg, psi)) => 
            go rho (Tl.snoc r x (ret isjdg jdg)) ([], out psi)
    in
      M.shortcircuit (go L.Ctx.empty Tl.empty (ts, out psi), Tl.isEmpty, fn psi => M.ret (psi |> vl))
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
    wrap t jdg >>-* M.map (mul isjdg) o m

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
    t jdg >>-* (fn st as (psi |> vl) =>
      let
        val psi' = Tl.singleton (L.fresh ()) jdg
      in
        case unifySubtelescope (psi', psi) of
           SOME _ => M.throw Progress
         | NONE => M.ret st
      end)

  fun mprogress mt (st as (psi |> _)) =
    mt st >>-* (fn sst =>
      let
        val psi' |> _ = mul isjdg sst
      in
        case unifySubtelescope (psi, psi') of
           SOME _ => M.throw Progress
         | NONE => M.ret sst
      end)

  fun complete t jdg =
    wrap t jdg >>-* (fn st as (psi |> _) => 
      if Tl.isEmpty psi then
        M.ret st
      else
        M.throw Complete)
end