functor LcfUtil (Lcf : LCF) : LCF_UTIL =
struct
  open Lcf

  fun labelState (psi, vld) : (metavariable * judgment) Monad.t =
    let
      val psi' =
        Ctx.mapWithKeys
          (fn (x, a) => Judgable.map (fn a' => (x, a')) (Judgable.into a))
          psi
    in
      (psi', vld)
    end

  fun uncurry f (x, y) =
    f x y

  val unit =
    State.map Judgable.out
      o Monad.unit
      o Judgable.into

  fun extend (t : tactic) : multitactic =
    State.map Judgable.out
      o Monad.extend (State.map Judgable.into o t o Judgable.out)
      o State.map Judgable.into

  fun labeledExtend (t : metavariable -> tactic) : multitactic =
    State.map Judgable.out
      o Monad.extend (State.map Judgable.into o uncurry t o Judgable.out)
      o labelState

  fun contract (mt : multitactic) : tactic =
    mt o unit
end

