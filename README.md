# TypOS
being an operating system for typechecking processes

Are the processes being typechecked? Are the processes doing the
typechecking? Yes.

Still very much in the early stages of construction (may it never
leave them!), TypOS is a domain-specific language for implementing
type systems, based on an actor model (caveat emptor) of concurrent
execution. Each region of source code is processed by an actor,
implementing a typing judgement with a clearly specified interaction
protocol. Actors may spawn other actors: child processes which
correspond to the premises of typing rules. Actors communicate with
one another along channels, in accordance with their stated protocol.


## What's in a TypOS program?

1. descriptions of syntaxes
2. declarations of judgement interaction protocols
3. definitions of judgement actors
4. example invocations of judgement actors

And when you press go, you get to watch the execution trace of your
examples, as control flits about between a treelike hierarchy of
actors, making progress wherever possible. We are still at a
rudimentary stage: there is a lot which remains to be done.


## What gets typechecked?

We have a very simple syntax for the stuff that gets processed by
TypOS actors.

A *name* begins with an alphabetical character, followed by zero or
more characters which are alphabetical, numeric or `_`. Names are
used in two ways:

* as variables, *x*, once they have been brought into scope
* as atoms, `'`*x*, whose role is to be different from each other

We build up structure by means of

* binding: `\`*x*`.` *term* is a term which brings *x* into scope in *term*
* pairing: `[` *term* `|` *term* `]` is a term with two subterms

There is a special atom, `[]` (pronounced "nil"), and we adopt the
bias towards right-nesting which has been prevalent since LISP
established it in the 1950s. That is, every occurrence of
`|[` may be removed, provided its corresponding `]` is removed also.
It is typical, therefore, to build languages with terms of the form
`['`*tag* *subterm* .. *subterm*`]`.

Now, there is no particular ideological significance to this choice of
LISP-with-binding. It is a cheap way to get started, but it is not an
ideal way to encode languages with more complex scoping
structure. When we need more, we shall review this choice.

Of course, LISP-with-binding is intended merely as a substrate: not
all terms are expected to be meaningful in all situations. We provide
various means of classification. Let us begin.


## `syntax` declarations

We start with a basic notion of context-free grammar. A `syntax`
declaration allows a bunch of nonterminal symbols to be mutually
defined. Here is an example, being a bidirectional presentation of
simply typed lambda-calculus.

```
syntax
  { 'Check = ['Tag  [ ['Lam ['Bind 'Synth ['Rec 'Check]]]
                      ['Emb ['Rec 'Synth]]
             ]]
  ; 'Synth = ['Tag  [ ['Rad ['Rec 'Check] ['Rec 'Type]]
                      ['App ['Rec 'Synth] ['Rec 'Check]]
             ]]
  ; 'Type = ['Tag  [ ['Nat ]
                     ['Arr  ['Rec 'Type] ['Rec 'Type]]
            ]]
  }
```

What are we saying? The terms you can `'Check` can be
lambda-abstractions but we also `'Emb`ed all the terms whose type we
can `'Synth`esize. The latter comprise what we call `'Rad`icals
(checkable terms with a type annotation) and `'App`lications where a
synthesizable function is given a checkable argument. E.g., the
identity function might be written `['Lam \x. ['Emb x]]`.

How have we said it? Following the keyword `syntax` is a `{;}`-list
of equations, each defining an atom by a term which happens to be a
*syntax description*. You can see some components of syntax
descriptions:

* `['Tag` .. `]` takes a list of pairs of atoms with lists of syntax
  descriptions, allowing us to demand exactly a list whose head is a
  tag and whose other elements are specified in a manner selected by
  the tag. So `'Lam` and `'Emb` are the tags for `'Check` terms,
  `'Rad'` and `'App` for `'Synth` terms, `'Nat` and `'Arr` for `'Type`
  terms.
* `['Rec` ..`]`, for *recursive*, is followed by an atom which is the name of
  a syntax, including the syntaxes defined in previous syntax
  declarations, or the current syntax declaration. E.g., we see that
  the `'Emb` tag should be followed by one `'Synth` term, while the
  `'Arr` tag should be followed by two `'Type`s.
* `['Bind` ..`]` specifies a term of form `\`*x*`.`*t*. It takes an
  atom which determines the named syntax to which the *x* is being
  added, then a syntax description for the *t*.

Correspondingly, in our example above, the `x` is classified as a
`'Synth` term, and so must be `'Emb`edded as the `'Check`able body of
the `'Lam`bda abstraction.

The other permitted syntax descriptions are as follows:

* `['Nil]` admits only `[]`.
* `['Cons` *head* *tail*`]` admits pairs `[`*h*`|`*t*`]` where *head*
  admits *h* and *tail* admits *t*.
* `['NilOrCons` *head* *tail*`]` admits the union of the above two.
* `['Atom]` admits any atom.
* `['Enum` ..`]` takes a list of atoms and admits any of them. Note
  that `['Enum ['tt 'ff]]` admits `'tt` and `'ff`, as opposed to
  `['Tag [ ['tt] ['ff] ]`, which admits `['tt]` and `['ff]`.
* `['Fix \`*x*`.` ..`]` takes a syntax decsription in which the bound
  *x* is treated as a syntax description, allowing local recursion.
  * `['Term]` admits anything.

For a more exciting example, we take
```
syntax { 'syntax = ['Tag [
  ['Rec ['Atom]]
  ['Atom]
  ['Nil]
  ['Cons ['Rec 'syntax] ['Rec 'syntax]]
  ['NilOrCons ['Rec 'syntax] ['Rec 'syntax]]
  ['Bind ['Atom] ['Rec 'syntax]]
  ['Tag ['Fix (\list.['NilOrCons ['Cons ['Atom] ['Fix (\list.['NilOrCons ['Rec 'syntax] list])]] list])]]
  ['Fix ['Bind 'syntax ['Rec 'syntax]]]
  ['Enum ['Fix (\list.['NilOrCons ['Atom] list])]]
  ['Term]
]]}
```
