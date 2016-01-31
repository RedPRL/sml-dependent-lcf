functor DependentLcf (Kit : ABT_JUDGMENT) : DEPENDENT_LCF =
struct
  open Kit
  structure J = Kit and Spine = Tm.Operator.Arity.Valence.Spine
  structure Metavariable = Tm.Metavariable

  structure Lbl =
  struct
    open Tm.Metavariable
    fun prime x = named (toString x ^ "'")
  end

  structure T = Telescope (Lbl)
  type 'a ctx = 'a T.telescope

  type environment = evidence ctx
  type validation = environment -> evidence

  type 'a state = 'a ctx * validation
  type tactic = judgment -> judgment state

  structure HoleUtil = HoleUtil (structure Tm = Tm and J = J and T = T)

  fun stateToString (psi, vld) =
    T.toString judgmentToString psi
      ^ "\n----------------------------------------------------\n"
      ^ evidenceToString (vld (HoleUtil.openEnv psi))
end

