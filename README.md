This repository contains a collection of very modular libraries for building
tactic-based refiners in the LCF tradition.

### Dependent LCF: modernized refinement proof

Dependent LCF is a modernization of the old LCF tactic system, to deal with
dependent refinement properly. A proof state is a telescope of judgments, where
each judgment binds a metavariable in the rest of the telescope, together with
a term that takes its free metavariables from the telescope.

The telescope corresponds to the list of subgoals in LCF, and the open term
corresponds to the "validation" in LCF. Whereas in Classic LCF, the validation
was a computational function from evidence to evidence, here it is a piece of
evidence with free variables; this design choice is forced by the categorical
semantics for Dependent LCF, and suggests that the computational character of
validations in Classic LCF is a design which does not generalize cleanly.

### Instructions

```
git submodule update --init --recursive
rlwrap sml
> CM.make "development.cm";
```
