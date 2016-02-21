structure Sort : SORT =
struct
  type t = unit
  val eq = op=
  fun toString () = "exp"
end

structure Valence = Valence (structure Sort = Sort and Spine = ListSpine)
structure Arity = Arity (Valence)

structure O =
struct
  structure Arity = Arity

  datatype 'i t =
      UNIT
    | SIGMA
    | AX
    | PAIR
    | FOO (* a dummy proposition to demonstrate dependency *)

  fun eq _ =
    fn (UNIT, UNIT) => true
     | (SIGMA, SIGMA) => true
     | (AX, AX) => true
     | (PAIR, PAIR) => true
     | (FOO, FOO) => true
     | _ => false

  fun arity UNIT = ([], ())
    | arity SIGMA = ([(([],[]),()), (([], [()]), ())], ())
    | arity AX = ([], ())
    | arity PAIR = ([(([],[]),()), (([], []), ())], ())
    | arity FOO = ([(([],[]),()), (([], []), ())], ())

  fun map _ =
    fn UNIT => UNIT
     | SIGMA => SIGMA
     | AX => AX
     | PAIR => PAIR
     | FOO => FOO

  fun support _ = []

  fun toString _ UNIT = "Unit"
    | toString _ SIGMA = "Σ"
    | toString _ AX = "Ax"
    | toString _ PAIR = "Pair"
    | toString _ FOO = "Foo"
end

structure Term = SimpleAbt (O)
structure ShowTm = DebugShowAbt (Term)

structure Judgment =
struct
  structure Tm = Term
  open Tm

  datatype judgment = TRUE of Term.abt
  fun judgmentToString (TRUE p) =
    ShowTm.toString p ^ " true"

  fun evidenceValence _ =
    (([], []), ())

  type evidence = abs
  fun evidenceToString e =
    let
      infix \
      val _ \ m = outb e
    in
      ShowTm.toString m
    end

  fun substEvidence rho (TRUE p) =
    TRUE (metasubst rho p)
end

structure Lcf = DependentLcf (Judgment)
structure Tacticals = Tacticals (Lcf)

signature REFINER =
sig
  val UnitIntro : Lcf.tactic
  val SigmaIntro : Lcf.tactic
  val FooIntro : Lcf.tactic
end

structure Refiner :> REFINER =
struct
  open Judgment Term
  infix $ $# \

  structure T = Lcf.T and V = Term.Metavariable

  local
    structure Notation = TelescopeNotation (T)
  in
    open Notation
    infix >:
  end

  structure MC =
  struct
    open MetaCtx
    structure Util = ContextUtil (structure Ctx = MetaCtx and Elem = Valence)
    open Util
  end

  fun teleToMctx (tele : judgment T.telescope) =
    let
      open T.ConsView
      fun go EMPTY theta = theta
        | go (CONS (l, jdg, psi)) theta =
            go (out psi) (MC.extend theta (l, evidenceValence jdg))
    in
      go (out tele) MC.empty
    end


  local
    val i = ref 0
  in
    fun newMeta str =
      (i := !i + 1;
       V.named (str ^ Int.toString (!i)))
  end

  fun UnitIntro (TRUE P) =
    let
      val O.UNIT $ [] = out P
      val ax = check' (O.AX $ [], ())
    in
      (T.empty, (fn rho => abtToAbs ax))
    end

  fun SigmaIntro (TRUE P) =
    let
      val O.SIGMA $ [_ \ A, (_, [x]) \ B] = out P
      val a = newMeta "?a"
      val b = newMeta "?b"
      val psi1 = T.empty >: (a, TRUE A)
      val theta1 = teleToMctx psi1
      val Ba = subst (check theta1 (a $# ([],[]), ()), x) B
      val psi = psi1 >: (b, TRUE Ba)
      val theta = teleToMctx psi
    in
      (psi, (fn rho =>
        let
          val a' = outb (T.lookup rho a)
          val b' = outb (T.lookup rho b)
          val pair = O.PAIR $ [a', b']
        in
          abtToAbs (check theta (pair, ()))
        end))
    end

  fun FooIntro (TRUE P) =
    let
      val O.FOO $ [_ \ A, _] = out P
      val a = newMeta "?a"
      val psi = T.empty >: (a, TRUE A)
      val theta = teleToMctx psi
      val ax = check theta (O.AX $ [], ())
    in
      (psi, (fn rho =>
        T.lookup rho a))
    end

end

structure Example =
struct
  open Refiner Judgment
  open Lcf Tacticals Term
  structure ShowTm = PlainShowAbt (Term)
  structure ShowTel = ShowTelescope (structure T = T val labelToString = Term.Metavariable.toString)
  infix 5 $ \ THEN ORELSE

  val x = Variable.named "x"

  val subgoalsToString =
    ShowTel.toString (fn (TRUE p) => ShowTm.toString p ^ " true")

  fun run goal (tac : tactic) =
    let
      val state = tac goal
    in
      print ("\n\n" ^ Lcf.stateToString state ^ "\n\n")
    end

  val mkUnit = check' (O.UNIT $ [], ())
  fun mkSigma x a b = check' (O.SIGMA $ [([],[]) \ a, ([],[x]) \ b], ())
  fun mkFoo a b = check' (O.FOO $ [([],[]) \ a, ([],[]) \ b], ())

  val x = Variable.named "x"
  val y = Variable.named "y"

  val goal =
    mkSigma y
      (mkSigma x mkUnit mkUnit)
      (mkFoo mkUnit (check' (`y, ())))

  (* to interact with the refiner, try commenting out some of the following lines *)
  val script =
    SigmaIntro
      THEN TRY SigmaIntro
      THEN TRY UnitIntro
      THEN FooIntro
      THEN UnitIntro

  val _ = run (TRUE goal) script
end

