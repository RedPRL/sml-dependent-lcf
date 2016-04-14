functor RelativeMonadFunctor (M : RELATIVE_MONAD) : FUNCTOR =
struct
  open M

  fun map f =
    extend (unit o J.map f)
end
