functor DependentLcf (Kit : ABT_JUDGMENT) : DEPENDENT_LCF =
struct
  open Kit
  structure J = Kit and Spine = Tm.Operator.Arity.Valence.Spine
  structure Metavariable = Tm.Metavariable

  structure Lbl = Tm.Metavariable

  structure T = Telescope (Lbl)
  type 'a ctx = 'a T.telescope

  type environment = evidence ctx
  type validation = environment -> evidence

  type 'a state = 'a ctx * validation
  type tactic = judgment -> judgment state
  type multitactic = judgment state -> judgment state

  structure HoleUtil = HoleUtil (structure Tm = Tm and J = J and T = T)

  structure TShow = ShowTelescope (structure T = T val labelToString = Lbl.toString)

  fun stateToString (psi, vld) =
    TShow.toString judgmentToString psi
      ^ "\n----------------------------------------------------\n"
      ^ evidenceToString (vld (HoleUtil.openEnv psi))

  local
    val i = ref 0
  in
    fun newMeta () =
      (i := !i + 1;
       J.Tm.Metavariable.named ("?" ^ Int.toString (!i)))
  end

  fun return jdg =
    let
      val v = newMeta ()
      val theta = T.snoc T.empty v jdg
    in
      (theta, fn rho =>
         T.lookup rho v)
    end

  fun subst (t : metavariable -> judgment -> judgment state) =
    let
      open T.ConsView
      fun go (psi, vld) =
        case out psi of
             EMPTY => (psi, vld)
           | CONS (x, jdgx, psi) =>
               let
                 val (psix, vldx) = t x jdgx
                 fun vld' rho = vld (T.snoc rho x (vldx rho))
                 val psi' = T.map (J.substEvidence (vldx (HoleUtil.openEnv psix), x)) psi
                 val (psi'', vld'') = go (psi', vld')
               in
                 (T.append (psix, psi''), vld'')
               end
    in
      go
    end

end

