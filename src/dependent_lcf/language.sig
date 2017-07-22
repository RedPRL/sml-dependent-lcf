signature LCF_VAR =
sig
  include ORDERED
  val toString : t -> string
end

signature LCF_LANGUAGE =
sig
  structure Var : LCF_VAR
  structure Ctx : DICT
  sharing type Var.t = Ctx.key

  type sort
  type term
  type var = Var.t
  type ctx = sort Ctx.dict
  type env = term Ctx.dict
  type ren = var Ctx.dict

  val fresh : unit -> var
  val var : var -> sort -> term
  val subst : env -> term -> term
  val ren : ren -> term -> term
  val eq : term * term -> bool
end
