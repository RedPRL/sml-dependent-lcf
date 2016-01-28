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
    | CONST (* a dummy proposition to demonstrate dependency *)

  fun eq _ =
    fn (UNIT, UNIT) => true
     | (SIGMA, SIGMA) => true
     | (AX, AX) => true
     | (PAIR, PAIR) => true
     | (CONST, CONST) => true
     | _ => false

  fun arity UNIT = ([], ())
    | arity SIGMA = ([(([],[]),()), (([], [()]), ())], ())
    | arity AX = ([], ())
    | arity PAIR = ([(([],[]),()), (([], []), ())], ())
    | arity CONST = ([(([],[]),()), (([], []), ())], ())

  fun map _ =
    fn UNIT => UNIT
     | SIGMA => SIGMA
     | AX => AX
     | PAIR => PAIR
     | CONST => CONST

  fun support _ = []

  fun toString _ UNIT = "Unit"
    | toString _ SIGMA = "Σ"
    | toString _ AX = "Ax"
    | toString _ PAIR = "Pair"
    | toString _ CONST = "Const"
end

structure V = Symbol ()
structure Lbl =
struct
  open V
  fun prime x = named (toString x ^ "'")
end

structure MC = Metacontext (structure Metavariable = V and Valence = Valence)
structure Term = Abt (structure Operator = O and Variable = V and Symbol = V and Metavariable = V and Metacontext = MC)

structure Kit : DLCF_KIT =
struct
  structure Term = Term and Telescope = Telescope (Lbl)
  datatype judgment = TRUE of Term.abt
  fun evidenceValence _ = (([], []), ())
  fun substJudgment (x, e) (TRUE p) =
    TRUE (Term.metasubst (e,x) p)
end
structure Lcf = DepLcf (Kit)

signature REFINER =
sig
  val UnitIntro : Lcf.tactic
  val SigmaIntro : Lcf.tactic
  val ConstIntro : Lcf.tactic
end

(*

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

*)
