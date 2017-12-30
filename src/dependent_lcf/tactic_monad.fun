
functor LcfTacticMonad (type env) :>
sig
  include LCF_TACTIC_MONAD where type env = env
  exception Refine of exn list
end = 
struct
  type env = env

  fun @@ (f, x) = f x
  infix @@

  exception Refine of exn list
  structure L = ListT (Identity)
  structure E = ErrorT (L)
  structure M = ReaderT (type r = env structure M = E)

  open M

  exception todo
  fun ?e = raise e

  local
    fun runAux p exns m =
      case L.uncons m of 
         SOME (Result.OK a, n) => if p a then a else runAux p exns n
       | SOME (Result.ERR exn, n) => runAux p (exn :: exns) n
       | NONE => raise Refine exns
  in
    fun run (env : env) (m, p) =
      runAux p [] (m env)
  end

  fun mapEnv (f : env -> env) : 'a m -> 'a m =
    fn m => fn env => 
      m (f env)

  fun getEnv env = 
    E.ret env
  
 fun throw exn env =
   E.throw exn

 fun mapErr f m env =
   E.mapErr f (m env)

 fun orAux env (m1, m2) = 
   case L.uncons m1 of 
      SOME (Result.OK a, _) => m1
    | SOME (Result.ERR exn, n1) => orAux env (n1, m2)
    | _ => m2 env

 fun or (m1 : 'a m, m2 : 'a m) : 'a m =
   fn env => 
     orAux env (m1 env, m2)
   
  fun par (m1, m2) env =
    L.concat (m1 env, m2 env)
end

structure LcfTacticMonad = LcfTacticMonad (type env = unit)
