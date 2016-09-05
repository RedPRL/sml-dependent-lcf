structure Sort : ABT_SORT =
struct
  type t = unit
  val eq = op=
  fun toString () = "exp"
end

structure Vl = AbtValence (structure S = Sort and PS = AbtEmptySort and Sp = ListSpine)
structure Ar = AbtArity (Vl)

structure L =
struct
  structure Ar = Ar
  structure P = AbtParameterTerm (AbtEmptyParameter (AbtEmptySort))

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

structure Term = SimpleAbt (L)
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
    TRUE (substMetavar rho p)

  fun substEvidenceEnv rho (TRUE p) =
    TRUE (substMetaenv rho p)

  fun judgmentMetactx (TRUE p) =
    metactx p

  fun unifyJudgment (TRUE p, TRUE q) =
    Unify.unifyOpt (p, q)
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

  structure T = Lcf.T and V = Term.Metavar

  local
    structure Notation = TelescopeNotation (T)
  in
    open Notation
    infix >:
  end

  structure MC =
  struct
    open Metavar.Ctx
    structure Util = ContextUtil (structure Ctx = Metavar.Ctx and Elem = Vl)
    open Util
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
      val L.UNIT $ [] = out P
      val ax = check (L.AX $ [], ())
    in
      (T.empty, (fn rho => abtToAbs ax))
    end

  fun SigmaIntro (TRUE P) =
    let
      val L.SIGMA $ [_ \ A, (_, [x]) \ B] = out P
      val a = newMeta "?a"
      val b = newMeta "?b"
      val psi1 = T.empty >: (a, TRUE A)
      val Ba = substVar (check (a $# ([],[]), ()), x) B
      val psi = psi1 >: (b, TRUE Ba)
    in
      (psi, (fn rho =>
        let
          val a' = outb (T.lookup rho a)
          val b' = outb (T.lookup rho b)
          val pair = L.PAIR $ [a', b']
        in
          abtToAbs (check (pair, ()))
        end))
    end

  fun FooIntro (TRUE P) =
    let
      val L.FOO $ [_ \ A, _] = out P
      val a = newMeta "?a"
      val psi = T.empty >: (a, TRUE A)
      val ax = check (L.AX $ [], ())
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
  structure ShowTel = ShowTelescope (structure T = T val labelToString = Term.Metavar.toString)
  infix 5 $ \ THEN ORELSE

  val x = Var.named "x"

  val subgoalsToString =
    ShowTel.toString (fn (TRUE p) => ShowTm.toString p ^ " true")

  fun run goal (tac : tactic) =
    let
      val state = tac goal
    in
      print ("\n\n" ^ Lcf.stateToString state ^ "\n\n")
    end

  val mkUnit = check (L.UNIT $ [], ())
  fun mkSigma x a b = check (L.SIGMA $ [([],[]) \ a, ([],[x]) \ b], ())
  fun mkFoo a b = check (L.FOO $ [([],[]) \ a, ([],[]) \ b], ())

  val x = Var.named "x"
  val y = Var.named "y"

  val goal =
    mkSigma y
      (mkSigma x mkUnit mkUnit)
      (mkFoo mkUnit (check (`y, ())))

  (* to interact with the refiner, try commenting out some of the following lines *)
  val script =
    SigmaIntro
      THEN TRY SigmaIntro
      THEN TRY UnitIntro
      THEN FooIntro
      THEN UnitIntro

  val _ = run (TRUE goal) script
end
