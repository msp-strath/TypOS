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

### Features

* [ ] Module system
* [ ] VM performance
   + [ ] Profiling
   + [ ] Bookkeep parts of the tree that are not stuck on new metas
   + [ ] Record more precise "Date" information (e.g. sets of blocking meta)
* [ ] Concurrent runtime
* [ ] Construct error messages from unfinished runs
* [ ] Deadlock detection
* [ ] Coverage checker for `case`
* [x] Standalone stacks (attached to strings, not judgements)

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
