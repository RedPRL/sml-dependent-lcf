structure Sort =
struct
  type t = unit
  val eq : t * t -> bool = op=
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
    | PI
    | AX
    | PAIR
    | LAM
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
    | arity PI = ([(([],[]),()), (([], [()]), ())], ())
    | arity AX = ([], ())
    | arity PAIR = ([(([],[]),()), (([], []), ())], ())
    | arity LAM = ([(([],[()]), ())], ())
    | arity FOO = ([(([],[]),()), (([], []), ())], ())

  fun map _ =
    fn UNIT => UNIT
     | SIGMA => SIGMA
     | PI => PI
     | AX => AX
     | PAIR => PAIR
     | LAM => LAM
     | FOO => FOO

  fun support _ = []

  fun toString _ UNIT = "Unit"
    | toString _ SIGMA = "Σ"
    | toString _ PI = "Π"
    | toString _ AX = "Ax"
    | toString _ PAIR = "Pair"
    | toString _ LAM = "λ"
    | toString _ FOO = "Foo"
end

structure Term = SimpleAbt (L)
structure ShowTm = DebugShowAbt (Term)

structure Language = LcfAbtLanguage (Term)
structure Generic = LcfGeneric (Language)

structure Judgment =
struct
  structure Tm = Term

  type sort = Language.sort
  type env = Language.env
  type symenv = Tm.symenv
  type varenv = Tm.varenv
  datatype jdg = TRUE of Tm.abt

  fun toString (TRUE p) =
    ShowTm.toString p ^ " true"

  fun sort _ =
    (([], []), ())

  fun map f (TRUE m) = TRUE (f m)
  fun eq (TRUE m, TRUE n) = Tm.eq (m, n)
  fun subst env = map (Tm.substMetaenv env)
  val substSymenv = map o Tm.substSymenv
  val substVarenv = map o Tm.substVarenv
end

structure Lcf = 
struct
  local
    structure Generic = LcfGeneric (Language)
    structure Util = LcfGenericUtil (structure Lcf = Generic and J = Judgment)
  in
    open Generic Util
  end
end


signature REFINER =
sig
  val UnitIntro : Lcf.jdg Lcf.tactic
  val SigmaIntro : Lcf.jdg Lcf.tactic
  val PiIntro : Lcf.jdg Lcf.tactic
  val FooIntro : Lcf.jdg Lcf.tactic
end

structure Refiner :> REFINER =
struct
  open Judgment Term
  infix $ $$ $# \
  structure Tl = Lcf.Tl and V = Term.Metavar

  val |> = Lcf.|>
  infix |>

  val || = Lcf.||
  infix ||

  local structure Notation = TelescopeNotation (Tl) in open Notation infix >: end

  local
    val i = ref 0
    fun newMeta () =
      (i := !i + 1;
       V.named (Int.toString (!i)))
  in
    fun makeGoal jdg =
      let
        val x = newMeta ()
      in
        ((x, ([],[]) || jdg), fn ps => fn ms => check (x $# (ps, ms), ()))
      end

    fun makeGoal' (us, xs) jdg =
      let
        val x = newMeta ()
      in
        ((x, (us, xs) || jdg), fn ps => fn ms => (check (x $# (ps, ms), ())))
      end
  end

  fun UnitIntro (TRUE P) =
    let
      val L.UNIT $ [] = out P
      val ax = L.AX $$ []
    in
      Tl.empty |> abtToAbs ax
    end

  fun SigmaIntro (TRUE P) =
    let
      val L.SIGMA $ [_ \ A, (_, [x]) \ B] = out P
      val (goalA, holeA) = makeGoal (TRUE A)
      val (goalB, holeB) = makeGoal (TRUE (substVar (holeA [] [], x) B))
      val pair = L.PAIR $$ [([],[]) \ holeA [] [], ([],[]) \ holeB [] []]
    in
      Tl.empty >: goalA >: goalB
        |> abtToAbs pair
    end
  
  fun PiIntro (TRUE P) = 
    let
      val L.PI $ [_ \ A, (_, [x]) \ B] = out P
      val (goal, hole) = makeGoal' ([], [(x, ())]) (TRUE B)
      val lam = L.LAM $$ [([],[x]) \ hole [] [check (`x, ())]]
    in
      Tl.empty >: goal |> abtToAbs lam
    end

  fun FooIntro (TRUE P) =
    let
      val L.FOO $ [_ \ A, _] = out P
      val (goalA, holeA) = makeGoal (TRUE A)
    in
      Tl.empty >: goalA |> abtToAbs (holeA [] [])
    end
end

structure Example =
struct
  open L Refiner Judgment
  open Lcf Term
  structure ShowTm = PlainShowAbt (Term)
  structure ShowTel = TelescopeUtil (Tl)
  infix 5 $ \ then_ orelse_

  val x = Var.named "x"

  fun run goal (tac : jdg tactic) =
    let
      val Lcf.|> (psi : jdg generic Tl.telescope, vld) = tac goal
      val (us, xs) \ m = outb vld
    in
      print "\n\n";
      print (ShowTel.toString (fn Lcf.|| (_, jdg) => J.toString jdg) psi);
      print "\n--------------------------------\n";
      print (ShowTm.toString m);
      print "\n\n"
    end

  val mkUnit = check (UNIT $ [], ())
  fun mkSigma x a b = check (SIGMA $ [([],[]) \ a, ([],[x]) \ b], ())
  fun mkPi x a b = check (PI $ [([],[]) \ a, ([],[x]) \ b], ())
  fun mkFoo a b = check (FOO $ [([],[]) \ a, ([],[]) \ b], ())

  val x = Var.named "x"
  val y = Var.named "y"
  val z = Var.named "z"

  val goal =
    mkSigma y
      (mkSigma x mkUnit mkUnit)
      (mkPi z (mkFoo mkUnit (check (`y, ()))) (mkFoo mkUnit (check (`z, ()))))

  (* to interact with the refiner, try commenting out some of the following lines *)
  val script =
    SigmaIntro
      then_ try SigmaIntro
      then_ try UnitIntro
      then_ PiIntro
      then_ FooIntro
      then_ UnitIntro

  val _ = run (TRUE goal) script
end
