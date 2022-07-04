### Documentation

* [ ] Document `!.` and `^`, `/` extract modes
* [ ] More structured documentation à la readthedocs?

### Syntax

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
* [ ] VM performance
   + [ ] Profiling
   + [ ] Bookkeep parts of the tree that are not stuck on new metas
   + [ ] Record more precise "Date" information (e.g. sets of blocking meta)
* [ ] Concurrent runtime
* [ ] Construct error messages from unfinished runs
* [ ] Deadlock detection
* [x] Coverage checker for `case`
* [x] Standalone stacks (attached to strings, not judgements)
* [ ] Unification modulo computation

### Judgement Contracts

* [ ] Syntax have an associated Semantics (what's canonical)
* [ ] Judgement take inputs / subjects / outputs
   + [ ] Subject should be syntatic
   + [ ] Inputs / outputs should be in the semantics of the given syntax
   + [ ] child subjects are structural components of parent subjects
   + [ ] if a subject pattern variable is transmitted, it is the subject of some child
   * [ ] Each syntax has a designated judgement with that syntax as subject (the justifier / gatekeeper)
* [ ] Contracts (constraints on inputs, guarantees on outputs)

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

### Pretty

* [ ] Try alternative libraries

### Cleanup

* [ ] Fix all the incomplete patterns errors
