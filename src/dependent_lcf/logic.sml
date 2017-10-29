structure Logic :> LOGIC =
struct
    datatype 'a t
      = CONS of 'a * 'a t
      | PAUSE of unit -> 'a t
      | NIL

    val empty = NIL
    val delay = PAUSE

    fun uncons s =
      case s of
          NIL => NONE
        | CONS (a, t) => SOME (a, t)
        | PAUSE p => uncons (p ())

    exception Empty
    fun observe 0 s = []
      | observe i s =
      case uncons s of
          NONE => raise Empty
        | SOME (a, s') => a :: observe (i - 1) s'

    fun toList s =
      case s of
          NIL => []
        | CONS (a, s') => a :: toList s'
        | PAUSE p => toList (p ())

    fun map f s =
      case s of
          NIL => NIL
        | CONS (a, t) => CONS (f a, map f t)
        | PAUSE p => PAUSE (fn () => map f (p ()))

    fun merge l r =
      case l of
          NIL => r
        | CONS (a, l') => CONS (a, merge l' r)
        | PAUSE p => PAUSE (fn () => merge r (p ()))

    fun return a = CONS (a, NIL)
    fun >>- (s, f) =
      case s of
          NIL => NIL
        | CONS (a, s') => merge (f a) (>>- (s', f))
        | PAUSE p => PAUSE (fn () => >>- (p (), f))
    infixr 1 >>-

    fun >>= (s, f) =
        let
          fun concat ss =
              case ss of
                  NIL => NIL
                | PAUSE p => PAUSE (fn () => concat (p ()))
                | CONS (NIL, ss') => concat ss'
                | CONS (CONS (a, s), ss') => CONS (a, concat (CONS (s, ss')))
                | CONS (PAUSE p, ss') =>
                  PAUSE (fn () => concat (CONS (p (), ss')))
        in
          concat (map f s)
        end

    fun unfold f b =
      case f b of
          NONE => NIL
        | SOME (a, b') =>
          CONS (a, PAUSE (fn () => unfold f b'))

    fun fromList xs =
      List.foldl (fn (a, b) => merge a b)
                 NIL
                 (List.map return xs)

    fun ifte i t e =
        case uncons i of
            NONE => e
          | SOME (a, b) => CONS (a, b) >>- t

    fun once s =
      case uncons s of
          NONE => NIL
        | SOME (a, _) => return a
end