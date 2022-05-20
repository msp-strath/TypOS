### Documentation

* [ ] Document `!.` and `^`, `/` extract modes
* [ ] More structured documentation à la readthedocs?

### Syntax

* [x] Annotating max locations (cf. (<!>) in Parse)
* [ ] User-friendly syntaxes
* [ ] Industrial-strength parsing
* [x] Source location information
* [ ] Let binders
* [ ] as-patterns
* [x] irrefutable patterns in binders

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

### CLI

* [ ] Hide extract mode under a CLI option

### Examples

* [x] STLC with clever lists
* [ ] Tests for extract mode
* [x] List induction

### Refactoring

* [x] Add range information to Variable
* [ ] More structured type of names
* [ ] Make sure LaTeX output is valid LaTeX
* [ ] `data Actor (ph :: Phase)`?

### Pretty

* [ ] Try alternative libraries

### Cleanup

* [ ] Fix all the incomplete patterns errors
