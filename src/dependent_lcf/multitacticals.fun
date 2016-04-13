functor Multitacticals (Lcf : DEPENDENT_LCF) : MULTITACTICALS =
struct
  structure Lcf = Lcf
  open Lcf

  type multitactic = judgment state -> judgment state

  fun ID jdg =
    return jdg

  fun ALL t =
    subst (fn _ => t)

  fun EACHX ts =
    subst (T.lookup ts)

  fun EACH ts (psi, vld) =
    let
      open T.ConsView
      fun go (EMPTY, []) r = r
        | go (CONS (x,a,tel), (t :: ts)) r = go (out tel, ts) (T.snoc r x t)
        | go _ _ = raise Fail "Incorrect length"
      val ts' = go (out psi, ts) T.empty
    in
      EACHX ts' (psi, vld)
    end

  fun EACH' ts (psi, vld) =
    let
      open T.ConsView
      fun go (EMPTY, _) r = r
        | go (CONS (x,a,tel), ts) r =
            go (out tel, List.tl ts handle _ => []) (T.snoc r x (List.hd ts handle _ => ID))
      val ts' = go (out psi, ts) T.empty
    in
      EACHX ts' (psi, vld)
    end

  fun FOCUS i t (psi, vld) =
    let
      open T.ConsView
      fun go r =
        fn (EMPTY, j) => r
         | (CONS (x,_,tel), j) => go (T.snoc r x (if i = j then t else ID)) (out tel, j + 1)
      val ts = go T.empty (out psi, 0)
    in
      EACHX ts (psi, vld)
    end

end
