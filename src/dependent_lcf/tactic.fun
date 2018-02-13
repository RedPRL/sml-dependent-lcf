signature LCF_TACTIC_KIT =
sig
  structure Lcf : LCF
  structure J : LCF_JUDGMENT
    where type sort = Lcf.L.sort
    where type env = Lcf.L.term Lcf.L.Ctx.dict
    where type ren = Lcf.L.var Lcf.L.Ctx.dict
end

structure LcfMonadBT :
sig
  include LCF_TACTIC_MONAD
  exception Refine of exn list
end = 
struct
  datatype 'a result = 
     OK of 'a
   | ERR of exn

  type 'a m = 'a result Logic.t

  exception Refine of exn list

  local
    fun runAux p exns m = 
      case Logic.uncons m of 
         SOME (OK r, t) => if p r then r else runAux p exns t
       | SOME (ERR exn, t) => runAux p (exn :: exns) t
       | NONE => raise Refine exns
  in
    fun run (m, p) = runAux p [] m
  end

  fun throw exn = Logic.return (ERR exn)
  fun par (m1, m2) = Logic.merge m1 m2
  fun or (m1, m2) = 
    case Logic.uncons m1 of
       SOME (OK a, _) => m1
     | SOME (ERR _, m1') => or (m1', m2)
     | NONE => m2

  fun map (f : 'a -> 'b) (m : 'a m) = Logic.map (fn OK a => OK (f a) | ERR exn => ERR exn) m
  fun mapErr f = Logic.map (fn OK a => OK a | ERR exn => ERR (f exn))
  fun ret (a : 'a) : 'a m = Logic.return (OK a)
  fun bind (m, f) = Logic.>>- (m, fn OK a => f a | ERR exn => Logic.return (ERR exn))
  fun mul mm = bind (mm, fn x => x)
  fun shortcircuit (m, p, f) = 
    Logic.shortcircuit
      (m, fn OK x => p x | ERR _ => false, fn OK a => f a | ERR exn => Logic.return (ERR exn))
end

functor LcfTactic (include LCF_TACTIC_KIT structure M : LCF_TACTIC_MONAD) : LCF_TACTIC =
struct
  open Lcf
  structure M = M and J = J

  infix 2 ::@
  infix 3 |>

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

  fun >>-* (m : 'a state M.m, k : 'a state -> 'b M.m) : 'b M.m = 
    M.shortcircuit (m, fn psi |> _ => Tl.isEmpty psi, k)

  infix >>-*

  fun each (ts : jdg tactic list) (psi |> vl) : jdg state state M.m =
    let
      open Tl.ConsView
      fun go (r : jdg state I.t telescope) =
        fn (_, EMPTY) => M.ret r
         | (t :: ts, CONS (x, jdg, psi)) =>
             wrap t (I.run jdg) >>-* (fn tjdg =>
               go (Tl.snoc r x (I.replace tjdg jdg)) (ts, out psi))
         | ([], CONS (x, jdg, psi)) => 
             go (Tl.snoc r x (I.map (ret isjdg) jdg)) ([], out psi)
    in
      M.shortcircuit (go Tl.empty (ts, out psi), Tl.isEmpty, fn psi => M.ret (psi |> vl))
    end


  fun eachSeq (ts : jdg tactic list) (psi |> vl) =
    let
      open Tl.ConsView
      fun go rho (r : jdg state I.t telescope) =
        fn (_, EMPTY) => M.ret r
         | (t :: ts, CONS (x, jdg, psi)) =>
            wrap t (J.subst rho (I.run jdg)) >>-*
              (fn tjdg as (psix |> vlx) =>
               let
                 val rho' = L.Ctx.insert rho x vlx
               in
                 go rho' (Tl.snoc r x (I.replace tjdg jdg)) (ts, out psi)
               end)
         | ([], CONS (x, jdg, psi)) => 
            go rho (Tl.snoc r x (I.map (ret isjdg) jdg)) ([], out psi)
    in
      M.shortcircuit (go L.Ctx.empty Tl.empty (ts, out psi), Tl.isEmpty, fn psi => M.ret (psi |> vl))
    end

  fun tabulate (f : int -> jdg tactic) (psi |> vl) =
    let
      val len = Tl.foldl (fn (_, _, n) => n + 1) 0 psi
    in
      eachSeq (List.tabulate (len, f)) (psi |> vl)
    end

  fun eachSeqWithDefault (ts, tdef) =
    tabulate (fn i => List.nth (ts, i) handle _ => tdef)

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
    M.par(wrap t1 jdg, wrap t2 jdg)

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
            if J.eq (J.ren env1 (I.run jdg1), J.ren env2 (I.run jdg2)) then
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
        open Tl.ConsView
        val psi' = Tl.singleton (L.fresh ()) (I.ret jdg)
      in
        case out psi of
           CONS (_, jdg', rest) => 
             if J.eq (jdg, I.run jdg') then
               M.throw Progress
             else
               M.ret st
         | _ => M.ret st
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