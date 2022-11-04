### Documentation

* [ ] Document `!.` and `^`, `/` extract modes
* [ ] More structured documentation à la readthedocs?

### Syntax

* [x] Insist keywords are followed by a space (`casew{}` vs. `case w {}`)
* [x] Annotating max locations (cf. (<!>) in Parse)
* [ ] User-friendly syntaxes
* [ ] Industrial-strength parsing
* [x] Source location information
* [x] Let binders
* [x] as-patterns
* [x] irrefutable patterns in binders
* [x] literate markdown
* [ ] literate LaTeX

### Features

* [ ] Module system
* [ ] Concurrent runtime
* [ ] Construct error messages from unfinished runs
* [ ] Deadlock detection
* [x] Coverage checker for `case`
* [x] Standalone stacks (attached to strings, not judgements)
* [ ] Unification modulo computation
* [ ] Guarding execution until validation
   + [ ] Unique names for subactors
   + [ ] block terms on names
   + [ ] Blocking wrapper evaporates when named thing is `Done`
+ [x] PRINTF argument for model-based normalisation

### VM

* [ ] VM performance
   + [ ] Profiling
   + [ ] Bookkeep parts of the tree that are not stuck on new metas
   + [ ] Record more precise "Date" information (e.g. sets of blocking meta)
   + [x] 'Done' status for winning branches
   + [x] 'Fail' status for dead branches
* [ ] Add "stuckon" tracing option for pattern-matching machinery
* [ ] Add "match" tracing option
* [ ] Compile matches to case trees
* [ ] Record metas that got us stuck

### Judgement Contracts

* [ ] Syntax have an associated Semantics (what's canonical)
* [ ] Judgement take inputs / subjects / outputs
   + [ ] Subject should be syntatic
   + [ ] Inputs / outputs should be in the semantics of the given syntax
   + [ ] child subjects are structural components of parent subjects
   + [x] if a subject pattern variable is transmitted, it is the subject of some child
   + [ ] Each syntax has a designated judgement with that syntax as subject (the justifier / gatekeeper / guarantor)
* [ ] Distinction between subjects and citizens (interpreted values of subjects)
   + [ ] make separate environments for subjects and citizens
   + [ ] guarding subjects-as-citizens
   + [ ] meaning of guarded subjects is given by citizens (silently)
* [ ] Contracts (constraints on inputs, guarantees on outputs)
  + [ ] each ? and ! must have a contract how it was/will be a $
  + [ ] define a standard model that we match against in ? and synthesise in !
  + [ ] there are other explicit models (e.g. a Kripke one for NBE)

### CLI

* [ ] Hide extract mode under a CLI option

### LaTeX

* [x] Colours for input and output
* [ ] Allow Latex injection in the source file
* [ ] Proper escaping of things latex don't like

### Examples

* [x] STLC with clever lists
* [ ] Tests for extract mode
* [x] List induction

### Refactoring

* [x] Add range information to Variable
* [ ] More structured type of names
* [ ] Make sure LaTeX output is valid LaTeX
* [x] `data Actor (ph :: Phase)`?
* [ ] Define `ElaborationMonad m =>` & cleanup sclause
* [ ] Drop run-length encoding subst in favour of relevant subst
* [ ] Match monad for Matching (Env in a state)
* [ ] `keyword` pretty printing should use the data type of keywords
* [ ] `class Declarable a where { declare :: a -> Context -> Context }`
      instead of declareObjVar, declareChannel, declareXXX

### Pretty

* [ ] Try alternative libraries

### Cleanup

* [ ] Fix all the incomplete patterns errors
