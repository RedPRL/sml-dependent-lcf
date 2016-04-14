signature LCF_CONTEXT =
sig
  type 'a ctx
  type metavariable

  val mapWithKeys : (metavariable * 'a -> 'b) -> 'a ctx -> 'b ctx
end
