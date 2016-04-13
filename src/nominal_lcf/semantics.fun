functor NominalLcfSemantics (M : NOMINAL_LCF_MODEL) : NOMINAL_LCF_SEMANTICS =
struct
  open M
  structure MT = Multitacticals (Lcf)

  fun extendTactic (tac : tactic) : multitactic =
    MT.ALL o tac

  fun contractMultitactic (mtac : multitactic) : tactic =
    fn alpha => fn jdg =>
      let
        val x = Lcf.J.Tm.Metavariable.named "?x"
        val psi = Lcf.T.snoc Lcf.T.empty x jdg
      in
        mtac alpha (psi, fn rho => Lcf.T.lookup rho x)
      end

  fun composeMultitactics mtacs =
    List.foldr
      (fn ((us : Syn.atom Spr.neigh, mtac : multitactic), rest) => fn alpha => fn st =>
        let
          val beta = Spr.prepend us alpha
          val (beta', modulus) = Spr.probe (Spr.prepend us beta)
          val st' = mtac beta' st
        in
          rest (Spr.bite (!modulus) beta) st'
        end)
      (fn _ => fn st => st)
      mtacs

  local
    open Syn
  in
    fun statement (sign, rho) stmt =
      case Stmt.out sign stmt of
           Stmt.SEQ bindings =>
             let
               fun multitacBinding (us, mtac) =
                 (us, multitactic (sign, rho) mtac)
             in
               contractMultitactic (composeMultitactics (List.map multitacBinding bindings))
             end
         | Stmt.TAC tac =>
             tactic (sign, rho) tac
         | Stmt.VAR x =>
             Syn.VarCtx.lookup rho x

    and tactic (sign, rho) =
      tacticR statement (sign, rho)

    and multitactic (sign, rho) mtac =
      case Multi.out sign mtac of
           Multi.ALL stmt =>
             MT.ALL o statement (sign, rho) stmt
         | Multi.EACH stmts =>
             let
               val ts = List.map (statement (sign, rho)) stmts
             in
               fn alpha =>
                 MT.EACH' (List.map (fn t => t alpha) ts)
             end
         | Multi.FOCUS (i, stmt) =>
             MT.FOCUS i o statement (sign, rho) stmt
  end
end
