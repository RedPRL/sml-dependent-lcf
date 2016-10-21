signature LCF_LANGUAGE =
sig
  structure Var : ORDERED
  structure Ctx : DICT
  sharing type Var.t = Ctx.key

  type sort
  type term
  type var = Var.t
  type ctx = sort Ctx.dict

  datatype clo = CLO of term * clo Ctx.dict
  type env = clo Ctx.dict

  val fresh : unit -> var
  val var : var -> sort -> term
  val force : clo -> term
end
