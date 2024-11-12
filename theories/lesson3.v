(**
---
customTheme : "solarized"
slideNumber: true
title: "Lip Ssr Tutorial"
minScale: 0.2
width: 2000
height: 1250
---


#  Advanced ssreflect tactics

<div class="hidden">

## Setting up a file using the mathcomp library

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
</div>


---


## Reflect and spec lemmas

---

### The reflect predicate

- `reflect P b` is the preferred way to state that the predicate `P` (in `Prop`) is logically equivalent to `b = true`

*)
Module reflect_for_eqP.

Print reflect.

(* we use this boolean predicate in the examples below *)
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

- the convenience lemma iffP
- the congr tactic

*)
Lemma myeqP m n : reflect (m = n) (eqn m n).
Proof.
apply: (iffP idP) => [|->]; last by elim: n.
elim: m n; first by case.
move=> n IHn m eq_n1m.
case: m eq_n1m => // m eq_n1m1. (* case with generalization *)
congr (_.+1). (* cleanup of the goal *)
by apply: IHn.
(*
Restart.
apply: (iffP idP) => [|->]; last by elim: n.
by elim: m n => [|m IHm] // [|n] // /IHm->.
*)
Qed.

Lemma test_myeqP n m : (eqn n m) -> m = n.
Proof. by move=> /myeqP ->. Qed.

End reflect_for_eqP.
(**

---

### Spec lemmas

- Inductive predicates to drive the proof:
  - you chose how many branches
  - you chose which equations are automatically applied
  - you chose which extra assumption a branch has
- of syntax for inductives

*)
Inductive leq_xor_gtn m n : bool -> bool -> Prop :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n false true.

Axiom leqP : forall m n : nat, leq_xor_gtn m n (m <= n) (n < m).
(**

---

### Let's try out leqP on an ugly goal

matching of indexes uses the same discipline of rewrite

*)
Lemma test_leqP m n1 n2 :
  (m <= (if n1 < n2 then n1 else n2)) =
  (m <= n1) && (m <= n2) && ((n1 < n2) || (n2 <= n1)).
Proof.
(* the indexes of <tt>leqP</tt> give rise to patterns, which are matched
   right to left. So the first one is <tt>_ < _</tt> which finds <tt>n1 < n2</tt>
   and replaces it with <tt>false</tt> in the first branch and <tt>true</tt> in the
   second. Then it is the turn of <tt>n2 <= n1</tt>.

   use: Set Debug "ssreflect". for a slow motion *)
case: leqP => [leqn21 | /ltnW ltn12 ]; rewrite /= andbT.
  by rewrite andb_idl // => /leq_trans /(_ leqn21).
by rewrite andb_idr // => /leq_trans->.
Qed.
(**

---

### Another commodity: ifP

- a spec lemma for if-then-else
- handy with case, since matching spares you to write the expressions involved
- remark how the goal is used as a work space

*)
Lemma test_ifP n m : if n <= m then 0 <= m - n else m - n == 0.
Proof.
case: ifP => //.
(* MC idiom: don't introduce hyps if not necessary *)
by move=> /negbT; rewrite subn_eq0 leqNgt negbK=> /ltnW.
Qed.
(**

---

### Strong inductions on the fly: ubnP

- a spec lemma for strong induction

*)
Lemma test_ubnP P : P 0 -> (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
move=> P0 Plt k.
have [n] := ubnP k.
elim: n k => // n IHn [|k] kn.
  exact: P0.
apply: Plt => m mk; apply/IHn.
by rewrite (leq_trans mk).
Qed.
(**

---

### Without loss

---

- `wlog: / H` lets you prove `(H -> G) -> G` and `H -> G`

*)
Lemma test_wlog (H G : Prop) : G.
Proof.
wlog: / H.
Abort.
(**

---

- `wlog: x1 .. xn / H` generalizes over the variables `x1 .. xn`.
  It lets you prove `(forall x1 .. xn, H -> G) -> G` and `H -> G`.


*)
Lemma test_wlog (P : rel nat) (Psym : symmetric P) m n
  (H : forall m n, m <= n -> P m n) : P m n.
Proof.
wlog hwlog : m n / m <= n.
  move=> Pmn.
  have [/Pmn//|/ltnW/Pmn] := leqP m n.
  by rewrite Psym.
exact: H.
Qed.
(**

---

# Hierarchies of mathematical structures

[An introduction to HB](https://perso.crans.org/cohen/HIM2024.pdf)

---

# Finite types and iterated operators

---

## Finite types

- The mathcomp library gives some support for finite types.
- `'I_n` is the the set of natural numbers smaller than `n`.

*)
Check finType.
Check 'I__ : finType.
(**

- `a : 'I_n` is composed of a value m and a proof that `m < n`

*)
Definition oid {n} (x : 'I_n) : 'I_n.
Proof.
case: x => m lt_m_n.
exact: (Ordinal lt_m_n).
(*
Restart.
pose m : nat := x. (* Data part *)
pose lt_m_n := ltn_ord x. (* Proof part *)
exact: (Ordinal lt_m_n).
*)
Defined.
(**

---

### Equality type

- Every finite type is also an "equality type".
- For `'I_n`, only the numeric value matters (the proof is irrelevant)
- `'I_n` is a subtype of `nat`

*)
Definition i3 := Ordinal (isT : 3 < 4).

Lemma ieq : oid i3 == i3.
Proof.
exact: eqxx.
Qed.

Lemma ieq' (h : 3 < 4) : Ordinal h == i3.
Proof.
apply/eqP.
pose H := val_inj.
apply: val_inj.
rewrite /=.
by [].
Qed.
(**

---

### An optimistic map from nat to ordinal : inord

- Takes a natural number as input and return an element of `'I_n.+1`
- The same number if it is small enough, otherwise `0`.
- The expected type has to have the shape `'I_n.+1` because `'I_0` is empty

*)
Check inord.

Check inordK.

Check inord_val.

Example inord_val_3_4 : inord 3 = (Ordinal (isT : 3 < 4)) :> 'I_4.
Proof.
apply: val_inj. rewrite /=. rewrite inordK. by []. by [].
Qed.

(**

---


### Membership

- if `T` is a finite type, `enum T` gives a duplicate-free sequence of its elements,
- the cardinal of `T` is the size of `enum T`,
- there is a membership predicate that boils down to testing membership to the sequence.


*)
Lemma iseq n (x : 'I_n) : x \in 'I_n.
Proof.
set l := enum 'I_n.
rewrite /= in l.
pose ordinal_finType_n : finType := 'I_n.
have mem_enum := mem_enum.
have enum_uniq := enum_uniq.
have cardT := cardT.
have cardE := cardE.
by [].
Qed.
(**

---

### Boolean theory of finite types.

- for finite type, boolean reflection can be extended to quantifiers

*)
Lemma iforall (n : nat) : [forall x: 'I_n, x < n].
Proof.
apply/forallP.
rewrite /=.
move=> x.
exact: ltn_ord.
Qed.

Lemma iexists  (n : nat) : (n == 0) || [exists x: 'I_n, x == 0 :> nat].
Proof.
case: n.
  by [].
move=> n.
rewrite /=. (* optional, try removing this line. *)
apply/existsP.
pose H : 0 < n.+1 := isT. (* use of small scale reflection. *)
pose x := Ordinal H.
exists x.
by []. (* mention function ord0. *)
Qed.
(**

---

## Iterated operators

- Big operators provide a library to manipulate iterations in mathcomp
- this is an encapsulation of the fold function

*)
Section Illustrate_fold.

Definition f (x : nat) := 2 * x.
Definition g x y := x + y.
Definition r := [::1; 2; 3].

Lemma bfold : foldr (fun val res => g (f val) res) 0 r = 12.
Proof.
rewrite /=.
rewrite /g.
by [].
Qed.

End Illustrate_fold.
(**

---

### Notation

- iteration is provided by the `\big` notation
- the basic operation is on `list`
- special notations are introduced for usual case (`\sum`, `\prod`, `\bigcap` ..)

*)
Lemma bfoldl : \big[addn/0]_(i <- [::1; 2; 3]) i.*2 = 12.
Proof.
rewrite !big_cons.
rewrite big_nil.
by [].
Qed.

Lemma bfoldlm : \big[muln/1]_(i <- [::1; 2; 3]) i.*2 = 48.
Proof.
rewrite !big_cons.
rewrite big_nil.
by [].
Qed.

(**

---

### Ranges (natural numbers)

*)
Lemma bfoldl1 : \sum_(1 <= i < 4) i.*2 = 12.
Proof.
have big_ltn' := big_ltn.
have big_geq' := big_geq.
rewrite big_ltn.
  rewrite big_ltn.
    rewrite big_ltn.
      rewrite big_geq.
        by [].
      by [].
    by [].
  by [].
by [].
Qed.
(**

---

### Ranges ("ordinals" and finite types)

*)
Lemma bfoldl2 : \sum_(i < 4) i.*2 = 12.
Proof.
rewrite big_ord_recl.
rewrite /=.
rewrite big_ord_recl.
rewrite /=.
rewrite /bump.
rewrite big_ord_recl.
rewrite big_ord_recl.
rewrite big_ord0.
by [].
Qed.
(**

*)
Lemma bfoldl3 : \sum_(i : 'I_4) i.*2 = 12.
Proof.
exact: bfoldl2.
Qed.
(**

---

### Filtering with a predicate

*)
Lemma bfoldl4 : \sum_(i <- [::1; 2; 3; 4; 5; 6] | ~~ odd i) i = 12.
Proof.
have big_pred0' := big_pred0.
have big_hasC' := big_hasC.
pose x :=  \sum_(i < 8 | ~~ odd i) i.
pose y :=  \sum_(0 <= i < 8 | ~~ odd i) i.
rewrite !big_cons.
rewrite /=.
rewrite big_nil.
by [].
Qed.
(**

- Handling conditions:
*)
Check big_mkcond.
Check big_seq_cond.
(**

---

### Switching ranges

- One can switch from one range type to another.

*)
Lemma bswitch :  \sum_(i <- [::1; 2; 3]) i.*2 =
                 \sum_(i < 3) (nth 0 [::1; 2; 3] i).*2.
Proof.
have big_nth' := big_nth.
rewrite (big_nth 0).
rewrite /=.
have big_mkord' := big_mkord.
rewrite big_mkord.
by [].
Qed.

Check big_mkord.
Check big_tuple.
Check big_tnth.
(**

---

### The theory of iterated operators

- Read [bigop.v](https://math-comp.github.io/htmldoc/mathcomp.ssreflect.bigop.html) for more information.

- Important lemmas

*)
Check eq_bigr.
Check eq_bigl.
Check eq_big.

Check big_cat.
Check big_cat_nat.
Check big_geq.

Check big_ord0.
Check big_ord_recl.
Check big_ord_recr.

Check big_split.
Check exchange_big.
Check big_distrr.

Check big_ind.
Check big_ind2.
Check big_morph.
(**

---

### Examples

*)
Lemma bab2 : \sum_(i < 3) \sum_(j < 4) (i + j) =
                 \sum_(i < 4) \sum_(j < 3) (i + j).
Proof.
have exchange_big' := exchange_big.
have reindex_inj' := reindex_inj.
rewrite exchange_big.
rewrite /=.
apply: eq_bigr.
move=> i _.
apply: eq_bigr.
move=> j _.
by rewrite addnC.
Qed.
(**


---

## Resources

- Greatly inspired by Yves Bertot's and Enrico Tassi's lectures at [Math Comp School & Workshop - 2022.](https://mathcomp-schools.gitlabpages.inria.fr/2022-12-school/school)
- The [Cheat Sheet](https://www-sop.inria.fr/teams/marelle/MC-2022/cheatsheet.pdf) (various versions [here](https://math-comp.github.io/documentation.html#org3b59844)) and the [interactive cheat sheet](https://perso.crans.org/cohen/IRIF-mathcomp-2021/irif.cheat_sheet.html)
- The [Mathcomp Book](https://math-comp.github.io/mcb/) (needs to be updated to mathcomp v2) <center><br/><img src="images/cover-front-web.png"></image><br/></center> and the [documentation](https://math-comp.github.io/)

- The [SSReflect User Manual](https://coq.inria.fr/doc/v8.20/refman/proof-engine/ssreflect-proof-language.html)

---

## Next time(s)

- Generic lemmas and hierarchies
- Finite types and iterated operators
- black belt tactics (such as `wlog` and `gen have`)


<script type="text/javascript">
  // If Javascript is enabled, this code will gray out all text in elements of 
  // class 'spoiler', allowing the user to click the grayed-out block to make 
  // it visible.
  var spoilers = document.querySelectorAll(".hidden");
  for (let spoiler of spoilers) {
    spoiler.classList.add('spoiler-hidden');
    spoiler.onclick = function() { this.classList.remove('spoiler-hidden'); }  
  }
</script>
<style>
  .spoiler-hidden { background-color: gray; color: gray; cursor: pointer; visibility: collapse; }
</style>
*)
