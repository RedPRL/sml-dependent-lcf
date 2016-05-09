functor Tacticals (Lcf : DEPENDENT_LCF) : TACTICALS =
struct
  open Lcf Lcf.J
  structure Lcf = Lcf
  structure HoleUtil = HoleUtil (structure J = J and T = T)

  structure Multi = Multitacticals (Lcf)
  structure LcfUtil = LcfUtil (Lcf)

  fun ID jdg =
    LcfUtil.unit jdg

  fun THEN (t1, t2) =
    Multi.ALL t2 o t1

  fun THENX (t, ts) =
    Multi.EACHX ts o t

  fun THENL (t, ts) =
    Multi.EACH ts o t

  fun THENL' (t, ts) =
    Multi.EACH' ts o t

  fun THENF (t1, i, t2) =
    Multi.FOCUS i t2 o t1

  fun ORELSE (t1, t2) jdg =
    t1 jdg handle _ => t2 jdg

  fun TRY t = ORELSE (t, ID)

  structure UnificationKit =
  struct
    structure MetaCtx = Tm.Metavariable.Ctx and VarCtx = Tm.Variable.Ctx and SymCtx = Tm.Symbol.Ctx

    structure T = T and Ren = MetaCtx
    type term = judgment

    fun variableRenamingIsVacuous rho =
      VarCtx.foldl
        (fn (k, v, b) => b andalso Tm.Variable.eq (k, v))
        true
        rho

    fun symbolRenamingIsVacuous rho =
      SymCtx.foldl
        (fn (k, v, b) => b andalso Tm.Symbol.eq (k, v))
        true
        rho

    fun >>= (SOME x, f) = f x
      | >>= (NONE, f) = NONE
    infix >>=

    fun unifyTerm (m, n) : Tm.metavariable Ren.dict option =
      unifyJudgment (m, n) >>= (fn (mrho, srho, vrho) =>
        if symbolRenamingIsVacuous srho andalso variableRenamingIsVacuous vrho then
          SOME mrho
        else
          NONE)

    fun rename rho jdg : term =
      let
        val psi = judgmentMetactx jdg
        val env =
          MetaCtx.foldl
            (fn (k, x, acc) =>
              case MetaCtx.find psi x of
                  NONE => acc
                | SOME vl => MetaCtx.insert acc x (HoleUtil.makeHole (x, vl)))
            MetaCtx.empty
            rho
      in
        substEvidenceEnv env jdg
      end
  end

  structure UnifyTelescope = UnifyTelescope (UnificationKit)

  fun PROGRESS t jdg =
    let
      val st as (psi, _) = t jdg
      val x = Tm.Metavariable.named "%PROGRESS-probe-var"
    in
      case UnifyTelescope.unifySubOpt (T.snoc T.empty x jdg, psi) of
           NONE => st
         | SOME _ => raise Fail "Failed to make progress"
    end
end
