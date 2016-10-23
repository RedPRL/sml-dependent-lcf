functor NominalLcfSemantics (M : NOMINAL_LCF_MODEL) : NOMINAL_LCF_SEMANTICS =
struct
  open M

  fun seq (mt1, us, mt2) alpha st =
    let
      val beta = Spr.prepend us alpha
      val (beta', modulus) = Spr.probe (Spr.prepend us beta)
      val st' = mt1 beta' st
      val l = Int.max (0, !modulus - List.length us)
    in
      mt2 (Spr.bite l alpha) (Lcf.mul Lcf.isjdg st')
    end


  local
    open NominalLcfView
  in

    fun Rec f alpha =
      f (Rec f) alpha

    (* [Σ |=[ρ] tac ==> T] *)
    fun tactic (sign, rho) tac =
      case Syn.tactic sign tac of
           RULE rl => rule (sign, rho) rl
         | MTAC mtac => (fn alpha => Lcf.mul Lcf.isjdg o multitactic (sign, rho) mtac alpha o Lcf.idn)

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
         | REC (x, mtac) =>
             Rec (fn mt => multitactic (sign, Syn.VarCtx.insert rho x mt) mtac)
         | PROGRESS mtac' =>
             Lcf.mprogress o multitactic (sign, rho) mtac'
         | VAR x => Syn.VarCtx.lookup rho x
         | SEQ (us, mt1, mt2) =>
            seq (multitactic (sign, rho) mt1, us, multitactic (sign, rho) mt2)
         | ORELSE (mt1, mt2) =>
             let
               val mt1 = multitactic (sign, rho) mt1
               val mt2 = multitactic (sign, rho) mt2
             in
               fn alpha =>
                 Lcf.morelse (mt1 alpha, mt2 alpha)
             end
  end
end
