# Presentation Roadmap

## Big talking points

1. Judgements with modes (bidi stlc)
2. Rule systems as actors
   + Pattern/expression distinction
   + Schematic variables have 1 binding site with a clear scope
3. Why are we doing this?
   + LF-ness (syntax with binding, just works)
   + Resumptions are updated
   + Rule out design errors by construction
4. What are the prospects for verifying TypOS actors?
   + Modes ---> requirements vs. guarantees

### Rule systems as actors

TypOS reifies the metaphor:

> A rule is a server for its conclusion,
> and a client for its premises

### Pat vs. exp examples

 f ∈ Πx:S.T     S ∋ s  ) Ok, T[s/x] is in exp position:
---------------------- } demand to compute T[s/x] is easily satisfied
    f s ∈ T[s/x]       )

 s ∈ S     t ∈ T[s/x]  ) Not ok, T[s/x] is in pattern position:
---------------------- } demand to invert substitution T[s/x] to recover T
   (s, t) ∈ Σx:S.T     ) is magical thinking

### Example: Holey program

Example with hole in program, extend to fill hole.
Bonus marks if later parts of the program constrain type of the hole
Good propaganda case for updatable resumptions
