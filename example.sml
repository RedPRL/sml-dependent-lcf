structure Sort : ABT_SORT =
struct
  type t = unit
  val eq : t * t -> bool = op=
  fun toString () = "exp"
end

structure Vl = AbtValence (structure S = Sort)
structure Ar = AbtArity (Vl)

structure L =
struct
  structure Ar = Ar

  datatype t =
      UNIT
    | SIGMA
    | AX
    | PAIR
    | FOO (* a dummy proposition to demonstrate dependency *)

  val eq = op=

  fun arity UNIT = ([], ())
    | arity SIGMA = ([([],()), ([()], ())], ())
    | arity AX = ([], ())
    | arity PAIR = ([([],()), ([], ())], ())
    | arity FOO = ([([],()), ([], ())], ())

  fun toString UNIT = "Unit"
    | toString SIGMA = "Σ"
    | toString AX = "Ax"
    | toString PAIR = "Pair"
    | toString FOO = "Foo"
end

structure Term = SimpleAbt (L)
structure ShowTm = DebugShowAbt (Term)

structure Language = LcfAbtLanguage (Term)

structure Judgment =
struct
  structure Tm = Term

  type sort = Language.sort
  type env = Language.env
  type ren = Language.ren

  datatype jdg = TRUE of Tm.abt

  fun toString (TRUE p) =
    ShowTm.toString p ^ " true"

  fun sort _ =
    ([], ())

  fun eq (TRUE m, TRUE n) = Tm.eq (m, n)
  fun subst env (TRUE m) = TRUE (Tm.substMetaenv env m)
  fun ren env (TRUE m) = TRUE (Tm.renameMetavars env m)
end

structure Lcf = LcfTactic (structure Lcf = Lcf (Language) and J = Judgment and M = LcfMonadBT)


signature REFINER =
sig
  val UnitIntro : Lcf.jdg Lcf.rule
  val SigmaIntro : Lcf.jdg Lcf.rule
  val FooIntro : Lcf.jdg Lcf.rule
end

structure Refiner :> REFINER =
struct
  open Judgment Term
  infix $ $$ $# \
  structure Tl = Lcf.Tl and V = Term.Metavar

  val |> = Lcf.|>
  infix |>

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
        ((x, jdg), fn ms => check (x $# ms, ()))
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
      val L.SIGMA $ [_ \ A, [x] \ B] = out P
      val (goalA, holeA) = makeGoal (TRUE A)
      val (goalB, holeB) = makeGoal (TRUE (substVar (holeA [], x) B))
      val pair = L.PAIR $$ [[] \ holeA [], [] \ holeB []]
    in
      Tl.empty >: goalA >: goalB
        |> abtToAbs pair
    end

  fun FooIntro (TRUE P) =
    let
      val L.FOO $ [_ \ A, _] = out P
      val (goalA, holeA) = makeGoal (TRUE A)
    in
      Tl.empty >: goalA |> abtToAbs (holeA [])
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

  val subgoalsToString =
    ShowTel.toString (fn (TRUE p) => ShowTm.toString p ^ " true")

  fun run goal (tac : jdg tactic) =
    let
      val Lcf.|> (psi, vld) = Lcf.M.run (tac goal, fn _ => true)
      val xs \ m = outb vld
    in
      print "\n\n";
      print (ShowTel.toString Judgment.toString psi);
      print "\n--------------------------------\n";
      print (ShowTm.toString m);
      print "\n\n"
    end

  val mkUnit = check (UNIT $ [], ())
  fun mkSigma x a b = check (SIGMA $ [[] \ a, [x] \ b], ())
  fun mkFoo a b = check (FOO $ [[] \ a, [] \ b], ())

  val x = Var.named "x"
  val y = Var.named "y"

  val goal =
    mkSigma y
      (mkSigma x mkUnit mkUnit)
      (mkFoo mkUnit (check (`y, ())))

  (* to interact with the refiner, try commenting out some of the following lines *)
  val script =
    Lcf.rule SigmaIntro
      then_ try (Lcf.rule SigmaIntro)
      then_ try (Lcf.rule UnitIntro)
      then_ Lcf.rule FooIntro
      then_ Lcf.rule UnitIntro

  val _ = run (TRUE goal) script
end
