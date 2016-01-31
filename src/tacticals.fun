functor Tacticals (Lcf : DEPENDENT_LCF) : TACTICALS =
struct
  open Lcf Lcf.J
  structure Lcf = Lcf
  structure HoleUtil = HoleUtil (structure J = J and T = T)

  local
    val i = ref 0
  in
    fun newMeta () =
      (i := !i + 1;
       J.Tm.Metavariable.named ("?" ^ Int.toString (!i)))
  end

  fun subst (t : metavariable -> judgment -> judgment state) (st : judgment state) : judgment state =
    let
      open T.ConsView
      fun go (psi, vld) =
        case out psi of
             Empty => (psi, vld)
           | Cons (x, jdgx, psi) =>
               let
                 val (psix, vldx) = t x jdgx
                 fun vld' rho = vld (T.snoc rho (x, vldx rho))
                 val psi' = T.map psi (J.substJudgment (x, vldx (HoleUtil.openEnv psix)))
                 val (psi'', vld'') = go (psi', vld')
               in
                 (T.append (psix, psi''), vld'')
               end
    in
      go st
    end

  fun ID jdg =
    let
      val v = newMeta ()
      val theta = T.snoc T.empty (v, jdg)
    in
      (theta, fn rho =>
         T.lookup rho v)
    end

  fun THEN (t1, t2) =
    subst (fn _ => t2) o t1

  fun THENX (t, ts) =
    subst (T.lookup ts) o t

  fun THENL (t, ts) = fn jdg =>
    let
      val st as (psi, _) = t jdg
      open T.ConsView
      fun go (Empty, []) r = r
        | go (Cons (x,a,tel), (t :: ts)) r = go (out tel, ts) (T.snoc r (x, t))
        | go _ _ = raise Fail "Incorrect length"
      val ts' = go (out psi, ts) T.empty
    in
      THENX (fn _ => st, ts') jdg
    end

  fun THENF (t1, i, t2) = fn jdg =>
    let
      val st as (psi, _) = t1 jdg
      open T.ConsView
      fun go r =
        fn (Empty, j) => r
         | (Cons (x,_,tel), j) => go (T.snoc r (x, if i = j then t2 else ID)) (out tel, i + 1)
      val ts = go T.empty (out psi, 0)
    in
      THENX (fn _ => st, ts) jdg
    end

  fun ORELSE (t1, t2) jdg =
    t1 jdg handle _ => t2 jdg

  fun TRY t = ORELSE (t, ID)
end

