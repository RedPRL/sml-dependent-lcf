functor NominalLcfSemantics (M : NOMINAL_LCF_MODEL) : NOMINAL_LCF_SEMANTICS =
struct
  open M
  structure Lcf = LcfUtil (MT.Lcf)

  fun contractMultitactic (mtac : multitactic) : tactic =
    Lcf.contract o mtac

  fun composeMultitactics mtacs =
    List.foldr
      (fn ((us : Syn.atom Spr.neigh, mtac : multitactic), rest) => fn alpha => fn st =>
        let
          val beta = Spr.prepend us alpha
          val (beta', modulus) = Spr.probe (Spr.prepend us beta)
          val st' = mtac beta' st
          val l = Int.max (0, !modulus - List.length us)
        in
          rest (Spr.bite l alpha) st'
        end)
      (fn _ => fn st => st)
      mtacs

  local
    open Syn
  in

    fun Rec f alpha jdg =
      f (Rec f) alpha jdg

    (* [Σ |=[ρ] tac ==> T] *)
    fun tactic (sign, rho) tac =
      case Tactic.out sign tac of
           Tactic.SEQ bindings =>
             let
               fun multitacBinding (us, mtac) =
                 (us, multitactic (sign, rho) mtac)
             in
               contractMultitactic (composeMultitactics (List.map multitacBinding bindings))
             end
         | Tactic.ORELSE (tac1, tac2) =>
             let
               val t1 = tactic (sign, rho) tac1
               val t2 = tactic (sign, rho) tac2
             in
               fn alpha => fn jdg =>
                 t1 alpha jdg
                   handle _ => t2 alpha jdg
             end
         | Tactic.REC (x, tac) =>
             Rec (fn t => tactic (sign, Syn.VarCtx.insert rho x t) tac)
         | Tactic.PROGRESS tac =>
             T.PROGRESS o tactic (sign, rho) tac
         | Tactic.RULE rl => rule (sign, rho) rl
         | Tactic.VAR x => Syn.VarCtx.lookup rho x

    (* [Σ |=[ρ] mtac ==> M] *)
    and multitactic (sign, rho) mtac =
      case Multitactic.out sign mtac of
           Multitactic.ALL tac =>
             MT.ALL o tactic (sign, rho) tac
         | Multitactic.EACH tacs =>
             let
               val ts = List.map (tactic (sign, rho)) tacs
             in
               fn alpha =>
                 MT.EACH' (List.map (fn t => t alpha) ts)
             end
         | Multitactic.FOCUS (i, tac) =>
             MT.FOCUS i o tactic (sign, rho) tac
  end
end
