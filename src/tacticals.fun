functor Tacticals (Lcf : DEPENDENT_LCF) : TACTICALS =
struct
  open Lcf Lcf.J
  structure Lcf = Lcf
  structure HoleUtil = HoleUtil (structure J = J and T = T)

  structure Multi = Multitacticals (Lcf)

  val ID = Multi.ID

  fun THEN (t1, t2) =
    Multi.ALL t2 o t1

  fun THENX (t, ts) =
    Multi.EACHX ts o t

  fun THENL (t, ts) =
    Multi.EACH ts o t

  fun THENF (t1, i, t2) =
    Multi.FOCUS i t2 o t1

  fun ORELSE (t1, t2) jdg =
    t1 jdg handle _ => t2 jdg

  fun TRY t = ORELSE (t, ID)
end

