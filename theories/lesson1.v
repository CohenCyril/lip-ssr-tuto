(**
---
customTheme : "solarized"
slideNumber: true
title: "Lip Ssr Tutorial"
minScale: 0.2
width : 2000
height: 1250
---

## Intro

---

### Objectives of the Tutorial


#### Give you quick access to the Mathematical Components library

- formalization techniques
- proof language
- familiarize with some theories

⋄

<small>
Thanks to Yves Bertot, Laurence Rideau, Enrico Tassi and Laurent Thery for the contents.
Thanks to Emilio Jesús Gallego Arias for the `.mv` experience.
</small>

---

#### Tentative program for the 5 lectures and practice:

1. An overview of mathcomp
3. An introduction to SSReflect tactics and style, with examples from basic libraries.
4. The management of hierarchies a.k.a. automated ad-hoc polymorphism
5. Applications to algebra and matrices
6. Finiteness and iterated operators, arithmetic.
7. Mathcomp analysis, a journey with filters
8. Glimpses of future features


---

### Disclaimer

#### Captatio benevolentiae
  comme dirait [Enrico Tassi](https://www-sop.inria.fr/members/Enrico.Tassi/)
- I won't take comment on the syntax, I can give rationales, but I'm not responsible. :)
- it is not easy to appreciate the benefits on small examples, but we will try hard ;-)
- not enough time to explain everything, I'll focus on intuition rather than technical details

---

### Resources

- Greatly inspired by Enrico Tassi's and Yves Bertot's lectures at [Math Comp School & Workshop - 2022.](https://mathcomp-schools.gitlabpages.inria.fr/2022-12-school/school)
- The [Cheat Sheet](https://www-sop.inria.fr/teams/marelle/MC-2022/cheatsheet.pdf) (various versions [here](https://math-comp.github.io/documentation.html#org3b59844)) and the [interactive cheat sheet](https://perso.crans.org/cohen/IRIF-mathcomp-2021/irif.cheat_sheet.html)
- The [Mathcomp Book](https://math-comp.github.io/mcb/) (needs to be updated to mathcomp v2) <center><br/><img src="images/cover-front-web.png"></image><br/></center> and the [documentation](https://math-comp.github.io/)

- The [SSReflect User Manual](https://coq.inria.fr/doc/v8.20/refman/proof-engine/ssreflect-proof-language.html)

---

## What is the mathematical components library?

### Why another library? Why another proof language?
- large, consistent, library organized as a programming language library (interfaces, overloading, naming conventions, ...)
- proof language tuned to the library recommended coding practices,
- contributions are reworked until they match the standards of the library,
- maintained in the long term (stable for more than 10 years),
- validated on large formalization projects ...


The mathematical components library was used to formalize the
[Odd Order Theorem (a.k.a. Feit Thompson)](https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_theorem), a 250 pages book.
Such proof amounts to 40k lines of Rocq scripts, on top of 120k lines of mathematical components. The library has been maintained for more than 10 years now.

---

Example setup of a file using the mathcomp library:
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup.
From mathcomp Require Import all_algebra all_solvable all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**

⋄

This setup is interactive using Vscode and Coq-lsp
*)
Lemma test : True. Proof. by []. Qed.
(**

---

## An overview of mathcomp

---

### "mathcomp core" consists of 6 packages:
  - [`mathcomp-ssreflect`](https://github.com/math-comp/math-comp/tree/mathcomp-2.2.0/mathcomp/ssreflect): bigops, sequences (lists) and tuples,
    natural number arithmetic, divisibility and primality,
    finite types and sets, quotients, equalities, orders.
  - [`mathcomp-fingroup`](https://github.com/math-comp/math-comp/tree/mathcomp-2.2.0/mathcomp/fingroup): basic finite group theory, group morphisms,
    permutations, actions and group quotients.
  - [`mathcomp-algebra`](https://github.com/math-comp/math-comp/tree/mathcomp-2.2.0/mathcomp/algebra): hierarchy of algebraic structures,
    integer arithmetic, Z/pZ and rational numbers,
    univariate polynomials, polynomial arithmetic and fraction fields,
    ring quotients, matrices and vector spaces.
  - [`mathcomp-solvable`](https://github.com/math-comp/math-comp/tree/mathcomp-2.2.0/mathcomp/solvable): advanced results in group theory, including
    Sylow's theorems and group series.
  - [`mathcomp-field`](https://github.com/math-comp/math-comp/tree/mathcomp-2.2.0/mathcomp/field): field theory, finite field theory,
    field extension theory, Galois theory and algebraic numbers.
  - [`mathcomp-character`](https://github.com/math-comp/math-comp/tree/mathcomp-2.2.0/mathcomp/character): character and representation theory.

---

### Extensions consists of more packages

  - [`mathcomp-zify`](https://github.com/math-comp/mczify): compatibility layer between mathcomp and lia tactics.
  - [`mathcomp-algebra-tactics`](https://github.com/math-comp/algebra-tactics): compatibility layer between mathcomp and ring/field tactics.
  - [`mathcomp-finmap`](https://github.com/math-comp/finmap): finite sets and finite maps.
  - [`mathcomp-real-closed`](https://github.com/math-comp/real-closed): theory of real closed fields and quantifier elimination.
  - [`mathcomp-multinomials`](https://github.com/math-comp/multinomials): multivariate polynomials.
  - [`mathcomp-classical`](https://github.com/math-comp/analysis/tree/1.5.0/classical): compatibility layer to do classical reasonning on top of mathcomp,
    theory of injective, surjective, bijective functions and cardinality.
  - [`mathcomp-analysis`](https://github.com/math-comp/analysis/tree/1.5.0/theories): topology, normed vector spaces, real functions,
    Bachman-Landau notations, infinite sequences,
    measure theory, Lebesgue measure and integral,
- [`Coq-Combi`](https://github.com/math-comp/Coq-Combi/tree/v1.0.0beta2): various theorems  in combinatorics
- [`Graph theory`](https://github.com/coq-community/graph-theory/tree/v0.9.5): various theorems in graph theory
- [`Monae`](https://github.com/affeldt-aist/monae): theorems about monads
- [`infotheo`](https://github.com/affeldt-aist/infotheo): information theory package
- [`coq-robot`](https://github.com/affeldt-aist/coq-robot): basics of robotics
- ...

---

### Searching information

Strategy:
1. Read the header of dedicated files in the library (e.g. [ssrnat](https://github.com/math-comp/math-comp/blob/mathcomp-2.2.0/mathcomp/ssreflect/ssrnat.v))
2. Use `Search` using a mix of:
  - patterns (e.g. `(_ + _)`) found in the header
	- constant names (use  `Locate` if necessary)
	- substrings of name using the [naming conventions](https://github.com/math-comp/math-comp/blob/master/CONTRIBUTING.md#naming-conventions-for-lemmas-non-exhaustive)
	- restrictions (e.g. `in algebra` etc)

⋄

Examples:
*)
Add Search Blacklist "__canonical__" "__to__" "HB_unamed_mixin". (* HB bug #418 to fix *)

Search addn muln.
Search (_ * _.+1) inside ssrnat.
Search "add" "M".
Search "Gauss".
(**

---

##  An introduction to SSReflect tactics and style

with examples from basic libraries.

---

### The Small Scale approach

⋄

#### Small scale tactics and theorems
  - Designed to **compress "Bookkeeping" steps**, i.e. on the fly moving,
    reordering, renaming, generalizing.
  - Emphasis on **combinators** and high-order functions
  - Tactics with a small and very-well **delimited effect**
  - The proof language eases **composability** by preserving strong invariants

⋄

#### Booleans at the center of the methodolgy
  - when a concept is "computable", we represent it as a
    **computable** function, not as an inductive relation
  - Rocq knows how to compute, even symbolically, and computation is
    a very stable form of **automation**
  - Proposition as `bool` is a "simple" concept in CIC
    - EM holds
    - UIP holds
    - equivalence is equality

---

### Bookkeeping 101

---

#### Heap & Stack model of a Goal **vs** Curry-Howard

```
(* begining of heap *)
ci : Ti
…
dj := ej : Tj
…
Fk : Pk ci
…
(* end of heap *)
=================
forall (xl : Tl) (* top of the stack *)
…,
Pn xl ->         (* nth element of the stack *)
… ->
Conclusion       (* bottom of the stack = no more elements *)
```

---

### Handling the heap with tactics and tacticials

Handled via
- tacticial `=>`, with syntax `tactic=> names`,
  moves UP and names the first items from the stack to the heap,
- tacticial `:`, with syntax `tactic: names`,
  moves DOWN the named items as elements of the stack,
- all mathcomp tactics operate on the stack
  - `case`, `elim` and most intro items (`=> items`) operate on the top of the stack,
  - `apply`, `rewrite`, `have` operate on the whole stack
    in particular `apply: lem x y` should be read as: "apply `lem` after adding `x` and `y`` to the top of the stack".

---

### Example of bookkeeping

*)
Module GoalModel.
Section GoalModel.
Variables (Ti Tj Tl : Type) (ej : Tj).
Variables (Pk : Ti -> Type) (Pn : Tl -> Type).
Variables (Conclusion : Ti -> Tj -> Tl -> Type).

Lemma goal_model_example (ci : Ti) (dj : Tj := ej) (Fk : Pk ci) :
  forall (xl : Tl), Pn xl -> Conclusion ci dj xl.
Proof.
move=> xl pnxl.
Fail move: xl.
move: ci Fk.
Abort.
End GoalModel.
End GoalModel.
(**

---

#### Giving arguments to tactics


- Tatics `case`, `elim`, `apply` are all overloaded to respect this invariant.

- Using them with arguments switches them back to "Vanilla Rocq" mode...

- In order to use the "ssreflect" version, one must combine them with the discharge (`:`) tacticial:

*)
Module ArgumentsToTactics.

Lemma negb_and : forall b c, ~~ (b && c) = ~~ b || ~~ c.
Proof.
move=> b. move=> c. move: b. move: c.
by case; case.
(*
Restart.
move=> c b. move: b c.
Restart.
move=> b; case: b; move=> c; case: c.
Restart.
by case; case.
*)
Qed.

Lemma test_modus_ponens P Q (toto : Prop) : P -> (P -> Q) -> Q.
Proof.
move=> p H.
apply H. (* equivalent to `move=> pq; apply: pq` *)
by []. (* or simply `exact` instead of `by apply`. *)
Qed.

End ArgumentsToTactics.
(**

---

#### Bookkeeping idioms in a nutshell

⋄

SSReflect invariants
 - if you don't name it, you can't use it
 - no tactic should alter the context silently

⋄

Tactics
- `move=> stuff` replaces `intros`${}^\star$
- `move: stuff` replaces `discharge`${}^\star$
- `case: x => stuff` replaces `case x as stuff`${}^\star$
- `elim: x => stuff` replaces `elim x as stuff`${}^\star$
- `apply: H => stuff` replaces `apply H; intros stuff`${}^\star$
- `by []` or `done` applies a set of "trivial" tactics and enforces goal closure
- `by apply` $\simeq$ `exact`

<div align=right>${}^\star$ but more powerful</div>

---

### Boolean reflection

---

#### A taste of boolean reflection by examples

##### Warning
  - these examples are artificial and deliberately simplified
  - in the library, this is done in a slightly different way

---

##### The first predicate
   - order relation on `nat` is a program outputting a boolean
   - `if`-`is`-`then` syntax (is simply sugar for a 2-way `match`-`with`-`end`)
   - `.+1` syntax (postfix notations .something are recurrent, e.g. `.1`, `.2`, `.-tuple`, etc)

*)
Module BooleanReflection.

Fixpoint leq (n m : nat) : bool :=
  if n is p.+1 then
    if m is q.+1 then leq p q
    else false
  else true.

Arguments leq !n !m.
Infix "<=" := leq.
(**

---

#### The first proof about `leq`

- `... = true` to "state" something
- proof by computation
- `by []` to say, provable by trivial means
  (no tactic is inside `[]`, general syntax is `by [tac1|..|tacn]`).
- `by tac` to say: `tac` must solve the goal (up to trivial leftovers)
- naming convention: head symbol of the LHS, and suffix `0` and `n`

*)
Lemma leq0n n : (0 <= n) = true.
Proof. by []. Qed.
(**

---

#### The second proof about `leq`
- equality as a double implication
- naming convention: head symbol of the LHS, and suffix `S`

*)
Lemma leqSS n m : (n.+1 <= m.+1) = (n <= m).
Proof. (* simpl *) by []. Qed.
(**

---

##### The third proof about `leq`

Let's use these lemmas (or not):
- tactic `elim` with naming and automatic clear of n
- tactic `apply`, `exact`, `rewrite`
- indentation for subgoals
- no need to mention lemmas proved by computation

*)
Lemma leqnn n : (n <= n) = true.
Proof.
elim: n => [|n IHn].
  by [].
rewrite leqSS.
by apply: IHn.
Qed.
(**

---

#### Connectives can be booleans too

- naming convention: suffix `b`

*)
Definition andb (b1 b2 : bool) : bool :=
  if b1 then b2 else false.
Infix "&&" := andb.

Definition orb (b1 b2 : bool) : bool :=
  if b1 then true else b2.
Infix "||" := orb.

Definition negb b : bool :=
  if b then false else true.
Notation "~~ b" := (negb b).
(**

---

#### Proofs by truth tables
- we can use EM to reason about boolean predicates and connectives
- intro/rewrite item: `/=`
- naming convention: `C` suffix

*)
Lemma andbC b1 b2 : (b1 && b2) = (b2 && b1).
Proof.
case: b1 => /=.
  case: b2.
    by [].
  by [].
by case: b2.
(* by case: b1; case: b2. *)
Qed.
End BooleanReflection.
(**

---


## Examples from MathComp library

---

### Things to know:
- `Search head_symbol (pat _ term) "string" inside library`
- `(a < b)` is a notation for `(a.+1 <= b)`
- `==` stands for computable equality (overloaded)
- `!=` is a mere notation for `~~ (_ == _)`
- `is_true` automatic coercion

*)
Search (_ <= _) inside ssrnat.
Locate "_ < _".
Check (forall x, x.+1 <= x).
Search orb "C" inside ssr.ssrbool.
Print commutative.
Check (3 == 4) || (3 <= 4).
Eval compute in (3 == 4) || (3 <= 4).
Check (true == false).
Check (3 != 4).

Lemma test_is_true_coercion : true.
Proof. rewrite /is_true. by []. Qed.
(**

---

### Equality 1/2
- privileged role (many lemmas are stated with `_ = _` rather than `is_true (_ == _)`)
- the `eqP` view: `is_true (a == b)   <->    a = b`
- `=> /eqP` (both directions)
- `apply/eqP`
- `=> ->` (on the fly rewrite, "subst")
- notation `.*2`

*)
Lemma test_eqP n m : n == m -> n.+1 + m.+1 = m.+1.*2.
Proof.
move=> /eqP.
move=> ->.
rewrite addnn.
by [].
Qed.
(**

---

### Equality 2/2

- Infix `==` is overloaded (see next lecture)
- and `eqP` is too

*)
Lemma test2_eqP b1 b2 : b1 == ~~ b2 -> b1 || b2.
Proof.
(*
Search orb inside ssrbool.
*)
by move=> /eqP->; exact: orNb.
Qed.
(**

---

### Views are just lemmas (plus some automatic adaptors)

- lemmas like `A -> B` can be used as views too
- boolean connectives all have associated views
- `case`/dispatch as an intro item `=> [ ... ]`

*)
Lemma test_leqW i j k : (i <= k) && (k.+1 <= j) -> i <= j.+1.
Proof.
(* move=> /andP. case. move=> /leqW. move=> leq_ik1. *)
move=> /andP[/leqW leq_ik1 /leqW leq_k1j1].
exact: leq_trans leq_ik1 leq_k1j1.
Qed.
(**

---

### The reflect predicate
`reflect P b` is the preferred way to state that the predicate `P` (in `Prop`)
  is logically equivalent to [b = true]

*)
Module reflect_for_eqP.

Print reflect.

Fixpoint eqn m n :=
  match m, n with
  | 0, 0 => true
  | j.+1,k.+1 => eqn j k
  | _, _ => false
  end.
Arguments eqn !m !n.
(**

---

### Proving the reflection lemma for eqn
- the convenience lemma `iffP`
- the `congr` tactic
- trivial branches pruning intro/rewrite item `//`
- loaded induction `elim: n m`

*)
Lemma myeqP m n : reflect (m = n) (eqn m n).
Proof.
apply: (iffP idP) => [|->]; last by elim: n.
by elim: m n => [|m IHm] // [|n] // /IHm->.
Qed.

Lemma test_myeqP n m : (eqn n m) -> m = n.
Proof. by move=> /myeqP ->. Qed.

End reflect_for_eqP.
(**

---

## Recap 1/2

- Proof language:
  - the stack model
  - `move` is the default tactic that "does nothing",
  - `by []`, `by tac` to close goals,
  - `: names`, to prepare the goal for a tactic,
  - `case` performs a case analysis on the top of the stack,
  - `=> name // /view /= {name} [|..|]`, to post-process the goal,
  - `rewrite lem -lem ?lem // /= /def`,
  - `apply: lem` to use a lemma in backward reasoning,
  - `apply/view` to use a view on the stack,
  - `apply` to apply the top of the stack to the rest of the stack,
  - `elim` to do elimination,
  - `elim: n m` to do elimination on `n` while generalizing on `m`.

---

## Recap 2/2

- Library:
  - naming convention: `addnC`, `eqP`, `orbN`, `orNb`, ...
  - notations: `.+1`, `if-is-then-else`,
  - `Search (_ + _) inside ssrnat`,
  - `Search addn "C" inside ssrnat`,
  - Use the HTML doc!
- Methodology:
  - boolean predicates, (e.g. `<=`, `\in`, `==`)
  - indentation of subgoals,
  - `reflect P b` to link `bool` with `Prop`.
  - convenience lemma `iffP` for proving `reflect`

---

## What's next?

### Advanced ssreflect features

- the `in` tacticial
- selection patterns (for `rewrite`, `set` and `:`)
- more switches and operators (`{names}`, `/[dup]`, `/[swap]`, `/[apply]`, `/[inE]`, etc)
- complex ad-hoc induction schemes
- forward tactics (`have`, `suff`, `pose`, `wlog`)
- "spec" lemmas (`ifP`, `leqP` etc)

### Black belt ssreflect features

- full `wlog` and `gen have` syntax
- induction schemes with helpers

### Overloading

- HB
- hierarchies of algebraic structures and morphisms
- hierarchies of sub-structures
- canonical tuples
- iterated operations, etc

---

Thanks
*)
