functor DependentLcf (Kit : ABT_JUDGMENT) : DEPENDENT_LCF =
struct
  open Kit
  structure J = Kit and Spine = Tm.O.Ar.Vl.Sp
  structure Lbl = Tm.Metavar

  structure T = Telescope (Lbl)
  type 'a ctx = 'a T.telescope

  structure Ctx =
  struct
    type 'a ctx = 'a ctx
    type metavariable = metavariable

    fun mapWithKeys f =
      let
        open T.ConsView
        val rec go =
          fn EMPTY => T.empty
           | CONS (x, a, psi) =>
               T.cons x (f (x, a)) (go (out psi))
      in
        go o out
      end
  end

  type environment = evidence ctx
  type validation = environment -> evidence

  type 'a state = 'a ctx * validation
  type tactic = judgment -> judgment state
  type multitactic = judgment state -> judgment state

  structure HoleUtil = HoleUtil (structure Tm = Tm and J = J and T = T)
  structure TShow = ShowTelescope (T)

  fun stateToString (psi, vld) =
    TShow.toString judgmentToString psi
      ^ "\n----------------------------------------------------\n"
      ^ evidenceToString (vld (HoleUtil.openEnv psi))

  local
    val i = ref 0
  in
    fun newMeta () =
      (i := !i + 1;
       Lbl.named ("?" ^ Int.toString (!i)))
  end

  fun unit jdg =
    let
      val v = newMeta ()
      val theta = T.snoc T.empty v jdg
    in
      (theta, fn rho =>
         T.lookup rho v)
    end

  datatype 'a judgable =
    JUDGABLE of
      {judgment : 'a,
       evidenceValence : valence,
       subst : Tm.metaenv -> 'a judgable}

  structure Judgable =
  struct
    type 'a t = 'a judgable

    fun map (f : 'a -> 'b) (JUDGABLE {judgment, evidenceValence, subst}) =
      JUDGABLE
        {judgment = f judgment,
         evidenceValence = evidenceValence,
         subst = map f o subst}

    fun into jdg =
      JUDGABLE
        {judgment = jdg,
         evidenceValence = evidenceValence jdg,
         subst = fn rho => into (substEvidenceEnv rho jdg)}

    fun out (JUDGABLE {judgment,...}) =
      judgment
  end

  structure State =
  struct
    type 'a t = 'a state
    fun map f (psi, vld) =
      (T.map f psi, vld)
  end

  structure Monad =
  struct
    structure J = Judgable
    type 'x t = 'x J.t State.t

    val unit =
      unit

    fun openEnv (psi : 'a J.t ctx) : environment =
      let
        open T.ConsView
        fun go rho =
          fn EMPTY => rho
           | CONS (x, JUDGABLE {evidenceValence,...}, phi) =>
               go (T.snoc rho x (HoleUtil.makeHole (x, evidenceValence))) (out phi)
      in
        go T.empty (out psi)
      end

    fun // (JUDGABLE {subst,...}, rho) =
      subst rho

    infix //

    fun extend (k : 'a J.t -> 'b t) : 'a t -> 'b t =
      let
        open T.ConsView

        (* At each stage, [env] contains a substitution for all the metavariables in the *original*
         * proof state which have been processed so far. Each [x] is substituted by the result of applying
         * [k] to the judgment [jdgx]. *)
        fun go env (psi, vld) =
          case out psi of
               EMPTY => (T.empty, vld)
             | CONS (x, jdgx, psi) =>
                 let
                   (* 1. Rewrite the focused judgment [jdgx] under the ambient environment, and apply [k] to it to get the subgoals and validation for [jdgx].
                    * 2. Extend the ambient environment by replacing the metavariable [x] with the validation [vldx].
                    * 3. Recurse along the tail of our proof state with the new environment. *)
                   val (psix, vldx) = k (jdgx // env)
                   val env' = Lbl.Ctx.insert env x (vldx (openEnv psix))
                   val (psi', vld') = go env' (psi, vld)
                 in
                   (T.append psix psi', vld' o (fn rho => T.snoc rho x (vldx rho)))
                 end
      in
        go Tm.Metavar.Ctx.empty
      end
  end
end
