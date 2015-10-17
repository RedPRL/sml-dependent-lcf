structure O =
struct
  datatype t =
      UNIT
    | SIGMA
    | AX
    | PAIR
    | CONST (* a dummy proposition to demonstrate dependency *)

  val eq : t * t -> bool = op=

  fun arity UNIT = Vector.fromList []
    | arity SIGMA = Vector.fromList [0,1]
    | arity AX = Vector.fromList []
    | arity PAIR = Vector.fromList [0,0]
    | arity CONST = Vector.fromList [0,0]

  fun toString UNIT = "Unit"
    | toString SIGMA = "Σ"
    | toString AX = "Ax"
    | toString PAIR = "Pair"
    | toString CONST = "Const"
end

structure V = Variable ()

structure Term = Abt (structure Operator = O and Variable = V)

structure Kit =
struct
  type name = V.t
  type term = Term.t
  datatype judgment = TRUE of term

  structure Telescope = Telescope (V)
  structure Term = AbtUtil (Term)
  fun substJudgment (x, e) (TRUE p) =
    TRUE (Term.subst e x p)
end

structure Lcf = DLcf (Kit)

signature REFINER =
sig
  val UnitIntro : Lcf.tactic
  val SigmaIntro : Lcf.tactic
  val ConstIntro : Lcf.tactic
end

structure Refiner :> REFINER =
struct
  open Kit
  open Term
  infix $$ $ //

  fun >: (T, p) = Telescope.snoc T p
  infix >:

  fun UnitIntro (TRUE P) =
    let
      val O.UNIT $ #[] = out P
    in
      (O.AX $$ #[], Telescope.empty)
    end

  fun SigmaIntro (TRUE P) =
    let
      val O.SIGMA $ #[A, xB] = out P
      val a = Variable.new ()
      val b = Variable.new ()
      val Psi =
        Telescope.empty
          >: (a, TRUE A)
          >: (b, TRUE (xB // ``a))
    in
      (O.PAIR $$ #[``a, ``b], Psi)
    end

  fun ConstIntro (TRUE P) =
    let
      val O.CONST $ #[A, _] = out P
      val a = Variable.new ()
      val Psi = Telescope.empty >: (a, TRUE A)
    in
      (``a, Psi)
    end
end

structure Example =
struct
  open Refiner Kit
  open Lcf
  structure Term = AbtUtil (Term)
  open Term
  infix 5 $$ $ // THEN ORELSE
  infixr 4 \\

  val x = Variable.named "x"

  val subgoalsToString =
    Telescope.toString (fn (TRUE p) => Term.toString p ^ " true")

  fun run goal tac =
    let
      val (e, Psi) = tac goal
    in
      print (Term.toString e ^ "\n\n" ^ subgoalsToString Psi ^ "\n\n")
    end

  val mkUnit = O.UNIT $$ #[]
  val x = Variable.named "x"
  val y = Variable.named "y"

  val goal =
    O.SIGMA $$
      #[O.SIGMA $$ #[mkUnit, x \\ mkUnit],
        y \\ O.CONST $$ #[mkUnit, ``y]]

  (* to interact with the refiner, try commenting out some of the following lines *)
  val script =
    SigmaIntro
      THEN TRY SigmaIntro
      THEN TRY UnitIntro
      THEN ConstIntro
      THEN UnitIntro

  val _ = run (TRUE goal) script
end

