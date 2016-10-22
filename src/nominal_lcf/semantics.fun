functor NominalLcfSemantics (M : NOMINAL_LCF_MODEL) : NOMINAL_LCF_SEMANTICS =
struct
  open M

  fun composeMultitactics mtacs =
    List.foldr
      (fn ((us : Syn.atom Spr.neigh, mtac : multitactic), rest) => fn alpha => fn st =>
        let
          val beta = Spr.prepend us alpha
          val (beta', modulus) = Spr.probe (Spr.prepend us beta)
          val st' = mtac beta' st
          val l = Int.max (0, !modulus - List.length us)
        in
          rest (Spr.bite l alpha) (Lcf.mul Lcf.isjdg st')
        end)
      (fn _ => fn st => st)
      mtacs

  local
    open NominalLcfView
  in

    fun Rec f alpha jdg =
      f (Rec f) alpha jdg

    (* [Σ |=[ρ] tac ==> T] *)
    fun tactic (sign, rho) tac =
      case Syn.tactic sign tac of
           SEQ bindings =>
             let
               fun multitacBinding (us, mtac) =
                 (us, multitactic (sign, rho) mtac)
             in
               fn alpha =>
                 composeMultitactics (List.map multitacBinding bindings) alpha
                   o Lcf.idn
             end
         | ORELSE (tac1, tac2) =>
             let
               val t1 = tactic (sign, rho) tac1
               val t2 = tactic (sign, rho) tac2
             in
               fn alpha => fn jdg =>
                 t1 alpha jdg
                   handle _ => t2 alpha jdg
             end
         | REC (x, tac) =>
             Rec (fn t => tactic (sign, Syn.VarCtx.insert rho x t) tac)
         | PROGRESS tac =>
             Lcf.progress o tactic (sign, rho) tac
         | RULE rl => rule (sign, rho) rl
         | VAR x => Syn.VarCtx.lookup rho x

    (* [Σ |=[ρ] mtac ==> M] *)
    and multitactic (sign, rho) mtac =
      case Syn.multitactic sign mtac of
           ALL tac =>
             Lcf.all o tactic (sign, rho) tac
         | EACH tacs =>
             let
               val ts = List.map (tactic (sign, rho)) tacs
             in
               fn alpha =>
                 Lcf.each (List.map (fn t => t alpha) ts)
             end
         | FOCUS (i, tac) =>
             (fn t => Lcf.only (i, t)) o tactic (sign, rho) tac
  end
end
