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
  { 'Check = ['Tag  [ ['Lam ['Bind 'Synth 'Check]]
                      ['Emb 'Synth] ]
             ]
  ; 'Synth = ['Tag  [ ['Rad 'Check 'Type]
                      ['App 'Synth 'Check] ]
             ]
  ; 'Type = ['EnumOrTag ['Nat ]
                        [ ['Arr 'Type 'Type] ]
            ]
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
  `'Rad'` and `'App` for `'Synth` terms.
* `['EnumOrTag` .. `]` takes two lists: the first one *enumerates* the
  permissible atoms, that is, it admits any of of them, whereas the
  second again is a list of pairs of tags and syntax descriptions (in
  fact, `['Tag` *ts*`]` is syntactic sugar for `[EnumOrTag []` *ts* `]`;
  similarly `['Enum` *es* `]` is syntactic sugar for `[EnumOrTag` *es* `[] ]`).
  So `Nat` on its own is a `'Type`, and `'Arr` is a tag demanding two
  further types.
* Names of syntax declarations can occur *recursively* in syntax
  descriptions: these are atoms which is the name of
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
* `['AtomBar *as*]` admits any atom, *except* those listed in *as*.
* `['Fix \`*x*`.` ..`]` takes a syntax decsription in which the bound
  *x* is treated as a syntax description, allowing local recursion.
* `['Wildcard]` admits anything.

For a more exciting example, we take

```
syntax { 'Syntax = ['EnumOrTag
  ['Nil 'Atom 'Wildcard 'Syntax]
  [['AtomBar ['Fix \at. ['NilOrCons 'Atom at]]]
   ['Cons 'Syntax 'Syntax]
   ['NilOrCons 'Syntax 'Syntax]
   ['Bind ['EnumOrTag ['Syntax] []] 'Syntax]
   ['EnumOrTag ['Fix \at. ['NilOrCons 'Atom at]]
               ['Fix \cell. ['NilOrCons ['Cons 'Atom ['Fix \rec. ['NilOrCons 'Syntax rec]]] cell]]]
   ['Enum ['Fix \at. ['NilOrCons 'Atom at]]]
   ['Tag ['Fix \cell. ['NilOrCons ['Cons 'Atom ['Fix \rec. ['NilOrCons 'Syntax rec]]] cell]]]
   ['Fix ['Bind 'Syntax 'Syntax]]]]
}
```
as the syntax description of syntax descriptions, using `'Fix` to
characterize the lists which occur in the `['AtomBar` ..`]`, `['Tag` ..`]`
and `['Enum` .. `]` constructs.


## Judgement forms and protocols

Before we can implement the actors which process our terms, we must
say which actors exist and how to communicate with them. Our version
of Milner's judgement-form-in-a-box names is to declare
*name* `:` *protocol*. A protocol is a sequence of *actions*. Each
action is specified by `?` for input or `!` for output, then the
intended syntax description for that transmission, then `.` as a closing
delimiter.

For our example language, we have

<!--
```
ctxt |- 'Synth -> 'Type
```
-->

```
type  : ?'Type.
check : ?'Type. ?'Check.
synth : ?'Synth. !'Type.
```
indicating that `type` actors receive only a `'Type` which they may
validate; `check` actors receive a `'Type` to check and a `'Check`able
term which we hope the type admits; `synth` actors receive a
`'Synth`esizable term, then (we hope) transmit the `'Type` synthesized
for that term.

Our protocols are nowhere near as exciting as session types, offering
only a rigid sequence of actions to do (or die). In the future, we
plan to enrich the notion of protocol in two ways:

1. Designate one input as the *subject* of the judgement, i.e., the
   currently untrusted thing whose validity the judgement is intended
   to establish. Above, the clue is in the name.
2. For every signal which is not the subject, indicate the
   *contract*. The actor is allowed to *rely* on properties of its
   inputs, but it must *guarantee* properties of its outputs. For the
   above, we should let `check` rely on receiving a `'Type` which
   `type` accepts, but demand that `synth` always yields a `'Type`
   which `type` accepts.

That is, we plan to check the checkers: at the moment we
check that actors stick to the designated interleaving of input and
output operations, and that syntax descriptions are adhered to.


## TypOS actors

An actor definition looks like *judgement*`@`*channel* `=` *actor*.
The channel is the actor's link with its parent (so we often call it
`p`) along which it must follow the declared protocol.
Here is a simple example:

```
type@p = p?ty. case ty
  { 'Nat ->
  ; ['Arr S T] ->
      ( type@q. q!S.
      | type@r. r!T.
      )
  }
  ```

This actor implements `type`, with channel `p` to its parent. Its
first action is `p?ty.` to ask its parent for an input, which
comes into scope as the value of the *actor-variable* `ty`. I.e.,
a *receiving* actor looks like *channel*`?`*actor-variable*`.` *actor*, which
performs an input on the given *channel*, then continues as the
*actor* with the *actor-variable* in scope. Actor variables stand for
terms, and may be used in terms as placeholders. Our actor has
received a type to validate. How does it proceed?

It performs a `case` analysis on the structure of the type. The
actor construct is `case` *term* `{` *pattern* `->` *actor* `;` ..`}`.
We shall specify patterns in more detail shortly, but let us
continue the overview. The `'Nat` pattern matches only if `ty`
is exactly `'Nat`, and the action taken in that case is nothing
at all! The empty actor denotes glorious success! Meanwhile, the
pattern `['Arr S T]` matches any three element list whose head is
the atom `'Arr`: the other two elements are brought into scope as
`S` and `T`, repsectively, then we proceed with the nonempty actor
to the right of `->`. What have we, now?

We have a *parallel* composition, *actor* `|` *actor*, and both
components will run concurrently. The first begins by *spawning*
a new `type` actor on fresh channel `q`. Spawning looks like
*judgement*`@`*channel*`.` *actor*, and it is another sequential
process, forking out a new actor for the given *judgement* and naming
the *channel* for talking to it, before continuing as the given
*actor* with the *channel* in scope. The channel follows the
protocol *dual* to that declared for the judgement. Our first fork
continues by *sending* `S` to `q`. Sending looks like
*channel*`!`*term*`.` *actor*. That is, we have delegated the
validation of `S` to a subprocess and hung up our boots, contented.
The second fork similarly delegates the validation of `T` to another
`type` actor on channel `r`.

We have seen actors for receiving, sending, case analysis, parallel
composition, and spawning. There is a little more to come. Let us
have a further example:

```
check@p = p?ty. p?tm. case tm
  { ['Emb e] -> synth@q. q!e. q?S. S ~ ty
  ; ['Lam \x. body] -> 'Type?S. 'Type?T.
      ( ty ~ ['Arr S T]
      | \x. ctxt |- x -> S. check@q. q!T. q!body.
      )

  }
```
The `check` actor follows the designated protocol, asking its parent
for a type `ty` and a checkable term `tm`. We expect `tm` to match
one of two patterns. The first is the simpler `['Emb e]`. This matches an
embedded `'Synth` term, bound to `e`, then spawns a `synth` actor
on channel `q` to determine the type of `e`. That is, we send `e` over
`q`, then receive type `S` in return. Our last act in this case is to
*constrain* `S ~ ty`, i.e., we demand that the type synthesized is
none other than the type we were asked to check. The actor form *term*
`~` *term* performs a unification process, attempting to make the
terms equal.

The `['Lam \x. body]` case shows a richness of features. Firstly,
the pattern indicates that the term must bind a variable, which the
term can name however it likes, but which the actor will think of as
`x`. The pattern variable `body` matches what is in the scope of `x`.
As a consequence, `body` stands for a term which may mention `x` and
thus may be used only in places where `x` is somehow captured. That
is, the use sites of actor variables are scope-checked, to ensure that
everything the terms they stand for might need is somehow in
existence. We have found the body of our abstraction. What happens
next?

It looks like we are making inputs `S` and `T` from the "syntactic
description `'Type` channel", and that is exactly what we are
doing! We request `S` and `T` from *thin air*. Operationally, TypOS
generates placeholders for terms as yet unknown, but which may yet be
solved, given subsequent constraints.  Indeed, one of our subsequent
forked actors exactly demands that `ty` is `['Arr S T]`, but we need
not wait to proceed. In parallel, we *bind* a fresh variable `x`,
allowing us to spawn a `check` actor on channel `q` and ask it to
check that type `T` admits `body` (whose `x` has been captured by our
binding). But we race ahead. A *binding* actor looks like `\` *variable* `.` *actor*.
It brings a fresh term *variable* into scope, then behaves like
*actor* for the duration of that scope.

Now, before we can `check` the `body`, we must ensure that `synth`
knows what to do whenever it is asked about `x`. We have explored
various options about how to manage that interaction. The current
incarnation is to allow the declaration of stacks of
*contextual data* for free variables. The form
*stackname* `|-` *variable* `->` *term* `.` *actor* pushes the
association of *term* with *variable* into the context
*stackname*, then continues as *actor*. Before we can make use of such a context, we must explain the syntactic
descriptions involved in. For our running example, we declare a context `ctxt`
which maps variables of syntactic category `'Synth` to types, as follows:

```typos-ignore
ctxt |- 'Synth -> 'Type
```
In our example, we have `ctxt |- x -> S. check@q. q!T. q!body.`, so
any actor which is a descendant of the `check` actor on
channel `q` will be able to access the `S` associated with `x` by
quering the `ctxt` context. To see an example how, let us look at the `synth`
actor's definition.

```
synth@p = p?tm . if tm in ctxt { S -> p!S. } else case tm
   { ['Rad t ty] ->
        ( type@q. q!ty.
        | check@r. r!ty. r!t.
        | p!ty.
        )
   ; ['App f s] -> 'Type?S. 'Type?T.
        ( synth@q. q!f. q?ty. ty ~ ['Arr S T]
        | check@r. r!S. r!s.
        | p!T.
        )
   }
```
We have only one new feature, which is invoked immediately we have
received `tm`. The actor `if` *term* `in` *stackname* `{` *actor-variable* `->` *actor*
`} else` *actor* attempts to access the context *stackname*, in this case `ctxt`. It will succeed if `tm` stands for a
free term variable with a context entry in scope, and in that case,
the *actor-variable* binds the associated value and the *actor* after `->`
is executed. As you can see, `ctxt` interprets the contextual data
associated with a free variable as exactly the type to send out.
If the *term* is not a free variable, or if there is no associated
data in the context, the `if-in` actor falls through to its `else`
clause.

Here, we fall back on the hope that `tm` might take one of the
two forms specified in the syntax of `'Synth` terms. For `'Rad`icals, we
concurrently validate the type, check that it accepts the term, and
deliver the type as our output. For `'App`lications, we guess source
and target types for the function, then concurrently confirm our guess
by constraining the output of `synth` on the function, check the
argument at our guessed source type, and output our guessed target
type as the type of the application.

You have been watching

* guessing: *syntax-desc*`?`*actor-variable*`.` *actor*
* receiving: *channel* `?`*actor-variable*`.` *actor*
* sending: *channel*`!`*term*`.` *actor*
* casing: `case` *term* `{` *pattern* `->` *actor* `;` ..`}`
* forking: *actor* `|` *actor*
* spawning: *judgement*`@`*channel*`.` *actor*
* constraining: *term* `~` *term*
* extending: *stackname* `|-` *variable* `->` *term* `.` *actor*
* querying: `if` *term* `in` *stackname* `{` *actor-variable* `->` *actor* `} else` *actor*
* winning:

and there's five more:

* plumbing: *channel* `<->` *channel* connects together two channels to forward on messages in both directions
* let-binders: `let` *actor-variable* `:` *syntax-desc* `=` *term* `.`  *actor*
* losing: `#` *format-string*
* printing: `PRINTF` *format-string*
* breaking: `BREAK` *format-string*

## Patterns

The patterns you can write in a TypOS `case` actor look like

* term variable:    *variable*
* specific atom:    `'`*name*
* paired patterns:  `[` *pattern* `|` *pattern* `]`
* variable binding: `\`*variable*`.` *pattern*
* scope selection:  `{` *selection* `}` *pattern*
* pattern binding:  *actor-variable*
* happy oblivion:   `_`

where a *selection* (sometimes known dually as a *thinning*) selects a
subset of the variables in scope as permitted dependencies. Inside the
braces, you write either the list of variables you want to keep or the
list of variables you want to exclude then `*`.

A term variable pattern matches exactly that term variable: we can
tell them apart from the pattern bindings of actor variables because
we can see where the term variable has been bound, whereas the actor
variable for a pattern binding must be fresh. E.g., we might want to
spot eta-redexes in our lambda calculus with the pattern
`['Lam \x. ['Emb ['App {x*}f x]]]`. The `f` is a pattern binding and
it matches any term not depending on `x`. The `x` is a bound variable,
and it matches only the variable bound by the `\x.`

At the binding sites of actor variables, TypOS detects which term
variables are in scope. TypOS further insists that everything which
was in scope at an actor variable's binding site is in scope at each
of its use sites. In the above example, we check that `f` matches a
term in which `x` plays no part, and we gain the right to use `f` with
no `x` in scope.


## Substitutions

When we write terms in actors, we are really talking *about* terms,
with actor-variables standing for terms, generically. Now, we have
insisted that every term variable in scope at an actor-variable's
binding site must be captured at each of its use sites, and we have
seen that one way to do that is with another `\`*variable*`.` binding
with a matching name. However, we may also *substitute* such
variables.

We extend the syntax of terms with `{`*substitution*`}`*term*. A
substitution is a comma-separated list of components which look like

* definition: *variable*`=`*term*
* exclusion: *variable*`*`
* preservation: *variable*

Order matters: substitutions should be read from right to left as
actions on the scope we find them in. Definitions bring new variables
into scope, by defining them to be terms using only variables already
in scope. Exclusions throw variables out of scope. Preservations
retain variables from the present scope but only as their own images:
in `{y=t,x}`, the `t` may not depend on `x`. A leftmost prefix of
preservations may safely be elided, so we need only say what is
*changing* at the local end of scope.

We may write substitutions anywhere in a term, but they act
structurally on all the term constructs (acquiring an extra
preservation at the local end wherever they go under a binder), piling
up at the use sites of actor-variables, where their role is to
reconcile any difference in scope with the binding sites of those
variables.


## Actors, channels, scope

Each actor knows about only those variables it binds itself. When
actors run, the terms which the actor-variables stand for will be
in a larger scope: the term variables mentioned in the actor's source
code will constitute the local end of that scope. Although the
`lookup` construct enables the basic means to find out stuff about
free variables, only the actor which binds the variable can choose
what that stuff is. Ignorance of free variables makes it easier to
achieve stability under substitution. In particular, the fact that
`case` patterns can test for only those free variables protected by their
binders from the action of substitution means that an actor's
`case` choices cannot be changed by the action of substitution on its
inputs. There is some sort of stability property to be proven about
`lookup` .. `else`, characterizing the things it is safe to substitute
for free variables.

Meanwhile, channels also have a notion of scope, restricting the
variables which may occur free in the terms which get sent along
them. The scope of a channel is exactly the scope at its time of
creation.

## Format strings

The actors `PRINTF`, `BREAK` and `#` can be used to print messages to
the user: `#` signifies failure, `BREAK` halts execution to display a
message, and `PRINTF` is often used to communicate success. Each of
these actors are followed by a format string enclosed in double quotes
", which may contain placeholders `%r`, `%i`, `%s`, `%S`, `%e`, and
`%m`, followed by a term for each `%r`, `%i`, and `%s` placeholder in
the string. Newlines and tabs are represented by `\n` and `\t`
respectively, and characters can be quoted by preceding them with a
backslash. The placeholders have the following meaning:

* `%r`: print "raw" term (without instantiating solved meta variables)
* `%i`: print "instantiated" term
* `%s`: print underlying term representation using Haskell's `show`
* `%S`: print current stack of virtual machine
* `%e`: print current environment of bindings
* `%m`: print current store of metavariable solutions

## Executing actors

Actors are executed using the `exec` command, in the context of all previous declarations and definitions. After the actors have finished running, a "typing derivation" is extracted and printed on the screen. For example, running the actor
```
exec  check@p. 'Check?t.
   p! ['Arr 'Nat 'Nat].
   p! ['Lam \z. ['Emb
         ['App ['Rad ['Lam \w. ['Emb w]] ['Arr 'Nat 'Nat]]
         ['Emb z]]]].
```
gives rise to the following output:
```output
check ['Arr 'Nat 'Nat]
      ['Lam \z. ['Emb ['App ['Rad ['Lam \w. ['Emb w]] ['Arr 'Nat 'Nat]]
                            ['Emb z]]]]
 \z_0. ctxt |- z_0 -> 'Nat.
  check 'Nat ['Emb ['App ['Rad ['Lam \w. ['Emb w]]
                               ['Arr 'Nat 'Nat]] ['Emb z_0]]]
   synth ['App ['Rad ['Lam \w. ['Emb w]] ['Arr 'Nat 'Nat]] ['Emb z_0]] 'Nat
    synth ['Rad ['Lam \w. ['Emb w]] ['Arr 'Nat 'Nat]] ['Arr 'Nat 'Nat]
     type ['Arr 'Nat 'Nat]
      type 'Nat
      type 'Nat
     check ['Arr 'Nat 'Nat] ['Lam \w. ['Emb w]]
      \w_1. ctxt |- w_1 -> 'Nat.
       check 'Nat ['Emb w_1]
        synth w_1 'Nat
    check 'Nat ['Emb z_0]
     synth z_0 'Nat
```

By running `typos INPUTFILE --latex OUTFILE`, the derivation above is written in latex format to `OUTFILE` as well. With commands redefined as in the [notations.tex](/build/notations.tex) file, this produces the following for our example execution:

<img src="build/trace.svg?raw=true" alt="Typing derivation in latex format" style="width: 700px; height: auto;">
