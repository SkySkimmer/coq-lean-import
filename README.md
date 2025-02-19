Alpha Announcement: Coq is a Lean Typechecker

# Introduction

This plugin provides the `Lean Import` command.

This is an experimental alpha, it is useful to compare how Lean and
Rocq work but probably not much beyond that.

# How do I install this?

This is a standard rocq makefile project and can be installed with

```sh
opam install coq-lean-import
```

# How do I use this?

You need Lean [exported files](https://github.com/leanprover/lean/blob/master/doc/export_format.md)
as input.

For use with Lean 4, you can use [lean4export](https://github.com/leanprover/lean4export).

For use with Lean 3, see [commit ce8ed08172d3247d992dacab08e0e8f59864a57b](https://github.com/coq-community/rocq-lean-import/commits/ce8ed08172d3247d992dacab08e0e8f59864a57b), which is compatible with Coq 8.20 and Lean 3, or [commit c513cee4f5edf8e8a06ba553ca58de5142cffde6](https://github.com/coq-community/rocq-lean-import/commits/c513cee4f5edf8e8a06ba553ca58de5142cffde6) which is compatible with Lean 3 and [coq/coq@a00be77](https://github.com/coq/coq/commit/a00be7706fad3eebbaec3d77ba2bb5cba516fb2b).

For your convenience, I have uploaded a few examples:
- [core.out](https://gist.githubusercontent.com/SkySkimmer/c8705b6d2d561ff7537d1dcabed371a0/raw/1538c7133d1334061e9ced67d3894d0b82cc83a4/core.out) (256KB)
  This corresponds to [core.lean](https://github.com/leanprover/lean/blob/master/library/init/core.lean) in Lean's stdlib.
  It contains 584 basic definitions and inductives such as equality, natural numbers, and the primitive quotient type (without the soundness axiom).
- [stdlib.out](https://gist.github.com/SkySkimmer/92e080ce3a0a89f0f592343076a86521/raw/7353fd277766a41a50cf4d6731443b3bb0e62c2a/stdlib.out) (14MB)
  This is the whole Lean stdlib, totalling 10244 definitions and inductives.
- [mathlib.7z](https://gofile.io/?c=8U8XpZ) (211MB compressed to 36MB)
  All mathlib (AFAICT): 66400 definitions and inductives (the way I counted may differ a bit from the way Lean counts).

Then start Coq and run

~~~coq
Require Lean.

Lean Import "/path/to/stdlib.out".
~~~
(if using the `mathlib.7z` I uploaded, make sure to decompress it first)

Coq will output many messages:
~~~
line 20: eq
eq is predeclared
line 21: quot
quot registered
line 38: has_add
line 59: has_add.add
line 90: add_semigroup
line 125: add_semigroup.add
line 136: add_semigroup.to_has_add
line 145: has_zero
line 159: has_zero.zero
line 168: has_mul
line 182: has_mul.mul
line 210: semigroup
line 243: semigroup.mul
line 253: semigroup.to_has_mul
line 262: has_one
line 276: has_one.one
line 285: has_le
line 305: has_le.le
line 323: list
line 331: nat
line 348: or
...
~~~

The `Require Lean` is needed for primitive quotient support (and
because quotients talk about equalities it predeclares `eq`). Without
it, you will get an error when trying to declare any value which
depends on `quot`.

Once it has finished working, Coq will output a summary:
~~~
...
line 586592: string.mk_iterator.equations._eqn_1
line 586615: heq.elim
Done!
- 10245 entries (24081 possible instances) (including quot).
- 274 universe expressions
- 14091 names
- 562009 expression nodes
Max universe instance length 4.
0 inductives have non syntactically arity types.
~~~

An "entry" means an axiom or constant, or an inductive type (including
its constructors and recursor), or the primitive quotient declarations
`quot`, `quot.mk`, `quot.lift` and `quot.ind`.

For ease of debugging, `Lean Import` will succeed even when an error
occurs: this allows inspecting the state from just before the failing entry.
This may probably be changed to only happen in a debugging mode at some point.

# How does it work?

The basic idea is to translate Lean `Prop` to Coq `SProp`, inductives
to inductives, etc.

We need to deal with a few issues in the translation:

## Differences in name handling

Lean has `.` separated namespaces, so we can have `foo.c` depend on
`bar.b` which depends on `foo.a`. This cannot be done with Coq
modules. Instead we replace dots by underscores, and add some indexing
to deal with collisions.

For instance,
~~~lean
inductive nat
| zero : nat
| succ (n : nat) : nat
~~~
becomes
~~~coq
Inductive nat := nat_zero | nat_succ (n : nat).
~~~
then if Lean declared a `nat_succ` it would get renamed to `nat_succ0`.

## Prop instantiations

Lean provides universe polymorphic values where universes may be
instantiated by `Prop`. For instance
~~~lean
inductive psum (α : Sort u) (β : Sort v)
| inl {} (val : α) : psum
| inr {} (val : β) : psum
~~~
provides discriminated sums of relevant as well as irrelevant types:
we can have `psum@{0 0} true true` as well as `psum@{1 1} nat bool` or
even `psum@{0 1} true nat`.

In Coq this is not possible. Instead we duplicate every value
according to which universes are instantiated to `Prop`. This
duplication is what the "possible instances" refers to in the end of
processing summary.

The version where no universe is `Prop` is considered the default and
gets the base name. The others have `_instX` appended to their name,
where `X` is the decimal representation of the number where bit `n` is
set if and only if universe `n` is instantiated by `Prop`. (this
naming scheme is subject to change)

By default, we produce the base instance, and the others are produced
as needed when encountered in other base instances. In other words,
when encountering the entry for `psum` we declare
~~~coq
Inductive psum (α:Type) (β:Type) := psum_inl (val:α) | psum_inr (val:β).
~~~
Then if we later encounter `def bla := ... psum@{0 u} ...` we will produce
~~~coq
Inductive psum_inst1 (α:Type) (β:Type) := psum_inl_inst1 (val:α) | psum_inr_inst1 (val:β).
~~~
and the same for `psum_inst2` and `psum_inst3`.

This lazyness has an exception: each instance of an inductive type
with large elimination has 2 instances of the recursor, depending on
whether we're eliminating to a `Prop` motive. These 2 instances are
always declared, so we don't wait until `psum_rec_inst1` is needed to
declare it.

Instances may be eagerly declared by using `Set Lean Upfront Instantiation`.

## Algebraic universes

Lean uses non cumulative universes, such that `Π (x:A), B` lives
exactly in the impredicative maximum of the domain and codomain
universes: `imax(uA,uB)`. We also get `max` in the level of inductive
types.

Thanks to the previous section, every universe name can be determined
to be either `SProp` or strictly greater than `Set`, so we can reduce
universe expressions to Coq algebraic universes. However this leaves
us with 2 issues:

- Coq expects universes in terms to be atomic, except in the codomain
  of the type of a global declaration. This is mostly required for the
  elaborator, so we could ignore it.

- Coq universe polymorphic values may only be instantiated by atomic
  universes (and, as we mentioned, ones which are not `SProp`).
  However Lean can (and must, due to lack of cumulativity) instantiate
  polymorphic universes with arbitrary expressions.

So we need to replace algebraic universes in universe instances by
some atomic name. In order to preserve conversions, we also need to
replace algebraic universes in terms (so for instance if we have `def
univ@{u} := Sort u`, the translation of `univ@{max(u,v)}` must be
convertible to `Sort (max (u,v))`).

The full process of translating a universe expression is then:

- first, produce a Coq algebraic universe:
  - `Prop` is translated to `SProp`
  - `a+1` is translated to the Coq successor of the translation of `a`
    (note that the successor of `SProp` is `Set + 1`, not `SProp + 1`
    which is invalid)
  - a Lean universe parameter is translated to `SProp` or a Coq named
    universe (depending on which instance we are currently producing)
  - `max(a,b)` is translated to the max of the respective translations
  - `imax(a,b)` is translated to `SProp` if `b` is translated to
    `SProp`, otherwise to the max of the respective translations.

We also need to make sure that every universe parameter not
instantiated by `Prop` is considered strictly greater than `Set`. This
is because Lean recognizes that `imax(Prop+1,l)+1 <= max(Prop+1,l+1)`:
either `l=Prop`, in which case the problem reduces to `Prop+1 <=
Prop+1`, or `l=l'+1`, in which case it reduces to `l'+1 <= l'+2`.
However in our translation we reduced to `max(Set+1,l)+1 <=
max(Set+1,l+1)` which is only true when `Set < l`.

To ensure this we keep constraints `Set < l` for every universe
parameter `l`, and we also apply a simplification step to the
translated universes which removes any `Set+n` subexpression when it
is together with a `l+k` with `n <= k + 1`.

We then associate a unique surrogate name for each simplified
algebraic universe.

At the end, we will produce a top-level universe polymorphic value
with the original parameters appended with the surrogates. It will
have constraints such that `Set < l` for each original parameter `l`,
and each pair of parameter (surrogate or original) is related by any
constraint relating its corresponding algebraic universes. For
instance, if `AB` is the surrogate for `max(a,b)` and `ABC` is the
surrogate for `max(a,b,c)` we must have all of `a <= AB, b <= AB, a <=
ABC, b <= ABC, c <= ABC` and `AB <= ABC`.

Since we have added universe parameters, we must adapt instances in
terms accordingly: if a definition `foo@{u}` is translated to `foo@{u,
U1}` where `U1` is the surrogate for `max(Set+2,u)`, its use as
`foo@{max(a,b)}` must be translated to `foo@{AB AB2}` where `AB` is the
surrogate for `max(a,b)` and `AB2` is the surrogate for
`max(Set+2,a,b)`.

By default, surrogate names are based on their corresponding universe.
For instance the surrogate for `max(u,v)` is `Lean.max__u_v.0`. If a
strangely-crafted input uses this to cause collisions, you can `Unset
Lean Fancy Universes` to get guaranteed unique names `bla.XXX` where
`bla` is the current file and `XXX` some unique index.

Note that once the kernel has accepted a declaration the universe
names are used only for printing.

## Subsingletons

Even with Coq accepting UIP, the rules for which inductives enjoy
unrestricted eliminations are different between Coq and Lean.
Typically, the accessibility predicate `Acc` is unrestricted in Lean
but is not accepted in `SProp` by Coq.

This is because it leads to an undecidable theory (of course we now
know that UIP combined with impredicativity is enough for that).

The workaround is simple: we detect when Coq is stricter than Lean and
in that case disable universe checking while declaring the inductive.

Sadly this is not enough to make the translation work in Coq without
UIP, because such a Coq also lacks the special reduction of the
eliminator of equality.

Note that this translation breaks extraction: for instance the recursor
of the translated `acc` cannot be extracted. However a more careful
translation could take advantage of Coq's non recursively uniform
parameter feature to fix extraction.

We may note that Lean is sometimes stricter than Coq. Specifically, if
an inductive has a `Prop` and a non-`Prop` instantiation, it may
happen that Coq only squashes the `Prop` instantiation.

## Primitive quotients

Lean's quotient primitives are
~~~lean
constant quot {α : Sort u} (r : α → α → Prop) : Sort u

constant quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : quot r

constant quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
  (∀ a b : α, r a b → eq (f a) (f b)) → quot r → β

constant quot.ind {α : Sort u} {r : α → α → Prop} {β : quot r → Prop} :
  (∀ a : α, β (quot.mk r a)) → ∀ q : quot r, β q
~~~
with the appropriate reductions.

Coq can emulate this using "Private inductive types". This emulation
has been done for you in the Coq module named `Coq.Lean`: simply
`Require` it before running `Lean Import`.

Because the `lift` mentions equality, `Coq.Lean` also predeclares the
equality type (we can't use the one from Coq's standard library since
it's not polymorphic). Declaring the eliminators for equality is still
done by `Lean Import`.

## Additional note on recursors

Coq autogenerates recursors for inductives types called (for an
inductive `foo`) `foo_sind`, `foo_ind`, `foo_rec` and `foo_rect`
(respectively for `SProp`, `Prop`, `Set` and `Type` motives).
These names are automatically detected by tactics like `induction`.

When the inductive is universe polymorphic (which is always the case
for our translations) the recursors are also universe polymorphic, and
notably the motive of the `_rect` version is a universe parameter.

However we cannot directly reuse the generated `_sind` and `_rect`
recursors as the 2 instantiations of the translated Lean recursor:

- In Lean the motive universe is the first parameter, in Coq it is the
  last. This is could be handled during the translation though.
- Coq generates non dependent eliminators for `SProp` inductives, but
  if the original Lean inductive has a non-`Prop` instantiation Lean
  expects a dependent eliminator.
- Each recursive argument of each constructor corresponds to an
  inductive hypothesis in the function for the branch of that
  constructor (the first `P n` in `nat_rect : forall P : nat -> Type,
  P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n`). In
  Coq each inductive hypothesis comes immediately after the recursive
  argument, but in Lean the inductive hypotheses come after all the
  constructor argument.

  This produces different types when a recursive argument is not the
  last constructor argument, for instance with
  ~~~coq
  Inductive bin_tree := Leaf | Node (a b : bin_tree).
  ~~~
  Coq generates
  ~~~
  bin_tree_rect
     : forall P : bin_tree -> Type,
       P Leaf ->
       (forall a : bin_tree, P a -> forall b : bin_tree, P b -> P (Node a b)) ->
       forall b : bin_tree, P b
   ~~~
   but Lean expects
   ~~~
   bin_tree_rect
     : forall P : bin_tree -> Type,
       P Leaf ->
       (forall a b : bin_tree, P a -> P b -> P (Node a b)) ->
       forall b : bin_tree, P b
   ~~~

To avoid these issues, we explicitly ask Coq for a term implementing
the recursor with the expected dependency, then post-process it to fix
universe and argument order. Since the result may not be compatible
with `induction`'s expectation, we use our own suffixes `_indl` and
`_recl` (`l` for `Lean`).

Since we use `_indl` for the `Prop`-motive recursor, any `_inst`
suffix corresponds to the instantiation of the inductive we eliminate.
For instance `psum_inst3_indl` is instance 5 (all universes `Prop`) of
`psum.rec`, its principal argument is of type `psum_inst3`.

# Experimental results

All times are on my laptop, which may have caused variance through
thermal throttling or whatever.

The export for just `core.lean` passes without issue in about 2s.

The whole stdlib cannot be checked as some conversion problems are
pathological. `two_pos` seems a typical example (`0 < 2` in an ordered
field). It's interesting to note that on this specific example,
changing the default conversion procedure to use Coq's VM makes it
succeeds in about 1 second (tested by importing with `Unset Conversion
Checking` (see next section), then `Require Import` the resulting
`.vo` and do `Definition foo := Eval cbv [two_pos] in two_pos.`).
Sadly using the VM makes other declarations take too long, and anyway
it hasn't been updated for proof irrelevance and for UIP's special
reduction.

As a superset of the stdlib, mathlib also cannot be fully checked.
Worse, even with `Unset Conversion Checking` it tries to use more RAM
and takes longer than I was willing to try.

Some stats:

- stdlib:
  lean --export in 46s, about 450MB RAM
  leanchecker in 8s, 80MB RAM

  Lean Import with Unset Conversion Checking: 43s, 723MB RAM
  resulting vo size 53MB

  Lean Import with 10s line timeout: 451s, 720MB RAM
  resulting vo size 50MB
  89 skipped entries out of 10244 (32 timeout, rest due to missing value from previous errors)

- mathlib:
  lean --export: didn't measure, took long enough and enough RAM that I don't want to retry
  (at least 1h / 10GB RAM I guess)
  leanchecker: 6min, 1GB RAM

  Lean Import with Just Parsing: 347s, 745MB RAM

  Lean Import with Unset Conversion Checking: killed at 4GB RAM on filter_mem_inf_sets_of_right

  Lean Import with Unset Conversion Checking and 10s timeout: 1h13min, 10GB RAM
  resulting vo size 1.4GB
  11867 skipped entries out of 66400 (first one is real.linear_order._proof_5)

# Options

## Lean Fancy Universes

See explanation of surrogate universe names.

## Lean Upfront Instantiation

See explanation of universe polymorphism and `Prop`.

## Lean Skip Missing Quotient

On by default, this means that encountering the primitive quotient
entry when the primitive quotient has not been predeclared is not an
error (i.e. when `Coq.Lean` is not loaded).

This means you will instead get a `quot was not instantiated` error
when a declaration refers to it.

## Lean Just Parsing

Off by default, if on `Lean Import` will not actually translate
anything. Useful to get the summary of how many entries are
encountered quickly.

## Lean Print Squash Info

Off by default, this may be useful for debugging if `Lean Import`
misdetects whether Lean would allow unrestricted elimination for some
inductive type.

## Lean Skip Errors

Off by default. With it on, when an error is encountered, skip the
failed line and keep going.

Useful to tell how much the current system can handle.

Note that timeouts and interrupts are also absorbed by this option. If
you turn it on and start loading mathlib, then change your mind and
decide to stop, you will need to kill the Coq process.

## Lean Line Timeout

An integer option, off by default. Use `Set Lean Line Timeout 10.` to
cause a failure whenever some entry takes more than 10s. Combined with
`Lean Skip Errors`, this allows processing all the entries which do
not depend on something that takes more than 10s.
