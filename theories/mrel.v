From Coq Require Import Relations Relation_Operators.
From RelationAlgebra Require Import lattice monoid rel kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq order choice.
From mathcomp Require Import finmap fingraph fintype finfun ssrnat path.
From Equations Require Import Equations.
From monae Require Import hierarchy monad_model.
From smallsteps Require Import relalg wftype monad.

(******************************************************************************)
(* Auxiliary definitions and lemmas about binary decidable relations.         *)
(*                                                                            *)
(*   mrel f       == a relation corresponding to non-deterministic function   *)
(*                   Given a monad M and monadic function f, mrel f denotes   *) 
(*                   a relation consisting of pairs <x, y>, s.t. x \in f y.   *)
(*                   The monad M should have canonical morphism into          *)
(*                   list monad.                                              *)
(*   strictify f  == given a non-deterministic function, removes all the      *)
(*                   elements equal to the argument of the function.          *)
(*                   It can be used to obtain a strict (i.e. irreflexive)     *)
(*                   relation corresponding to f.                             *)
(*   suffix f     == given a well-founded function f and an element x,        *)
(*                   returns a strict suffix of x, i.e. a set { y | x R y }   *)
(*                   where R ::= sfrel f.                                     *)
(*   wsuffix f    == a weak (reflexive) suffix, i.e. a set { y | x R? y }     *)
(*   t_closure f  == given a well-founded function f returns its              *)
(*                   transitive closure as a decidable relation.              *)
(*                   t_closure f ≡ (sfrel f)^+                                *)
(*   rt_closure f == given a well-founded function f returns its              *)       
(*                   reflexive-transitive closure as a decidable relation,    *)
(*                   t_closure f ≡ (sfrel f)^*                                *)
(******************************************************************************)


(* TODO: get rid of copy-paste from event-struct 
 * in `relalg.v`, `wftype.v`, `mrel.v` 
 *)  

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Set Equations Transparent.

Import Order.LTheory.
Local Open Scope order_scope.
Local Open Scope ra_terms.
Local Open Scope monae_scope.

Import NDMonadMorphism.Syntax.

(* A shorter name for list monad. 
 * TODO: rename to Seq? 
 * TODO: Use canonical structures to infer the 
 *   monad instance for seq automatically?  
 *)
Local Notation List := ModelNondet.list.

(* TODO: move to `monad.v` ? *)
Definition mrel {M : nondetMonad} {η : M ≈> List}
  {T : eqType} (f : T -> M T) : {dhrel T & T} :=
    [rel a b | b \in η T (f a)].

Section Strictify.

Context (T : eqType).
Variable  (M : nondetMonad) (η : M ≈> List).
Implicit Type (f : T -> M T).

Definition strictify f : T -> M T :=
  fun x => mfilter M (f x) (fun y => x != y).

Lemma strictify_weq f :
  @mrel M η T (strictify f) ≡ (@mrel M η T f \ eq_op).
Proof. 
  move=> x y; rewrite /mrel /strictify /mfilter /=.
  by rewrite mem_mfilter andbC. 
Qed.

Lemma strictify_leq f : 
  @mrel M η T (strictify f) ≦ @mrel M η T f.
Proof. by rewrite strictify_weq; lattice. Qed.

End Strictify. 

Module WfClosure.

Section WfRTClosure.

Context {disp : unit} {T : wfType disp}.

Variable (M : nondetMonad) (η : M ≈> List) (f : T -> M T).

(* Hypothesis descend : forall x y, y \in f x -> y < x. *)
Hypothesis descend : @mrel M η T f ≦ (>%O).

(* A hack to get around a bug in Equations 
 * (see https://github.com/mattam82/Coq-Equations/issues/241).
 * In short, we cannot express this function directly in Equations' syntax
 * (we can do it by adding `noind` specifier, but then we cannot use `funelim`).
 * Thus we have to "tie a recursive knot" manually. 
 *)
 Definition suffix_aux (x : T) (rec : forall y : T, y < x -> M T) := 
  let ys := f x in 
  let ps := ys >>= (fun x => 
    if x \in η T ys =P true is ReflectT pf then
      rec x (descend _ _ pf)
    else
      Fail
  ) in 
  Alt ys ps.

(* strict suffix of an element `x`, i.e. a set { y | x R y } *)
Equations suffix (x : T) : M T by wf x (<%O : rel T) := 
  suffix x := suffix_aux x suffix.

(* weak suffix of an element `x`, i.e. a set { y | x R? y } *)
Definition wsuffix (x : T) : M T :=
  Alt (Ret x) (suffix x).

(* decidable transitive closure *)
Definition t_closure : {dhrel T & T} := 
  fun x y => y \in η T (suffix x).

(* decidable reflexive-transitive closure *)
Definition rt_closure : {dhrel T & T} := 
  fun x y => y \in η T (wsuffix x).
  
(* ************************************************************************** *)
(*       THEORY                                                               *)
(* ************************************************************************** *)

Lemma t_closure_1nP x y : 
  reflect (clos_trans_1n T (@mrel M η T f) x y) (t_closure x y).
Proof.
  rewrite /t_closure; funelim (suffix x)=> /=. 
  apply /(iffP idP); rewrite mem_alt /mrel /=.
  { move=> /orP[|/mem_bindP[z]] //; first exact: t1n_step.
    case: eqP=> // S /descend yz /X tr. 
    move: (tr yz) => H.
    by apply: t1n_trans; first exact: S. }
  move: X=> /[swap] [[?->//|{}y ? /[dup] ? L /[swap]]].
  move=> /[apply] H; apply/orP; right; apply/mem_bindP.
  exists y=> //. case: eqP => // /descend yz. exact: H.
Qed.

Lemma t_closureP x y :
  reflect (clos_trans T (@mrel M η T f) x y) (t_closure x y).
Proof.
  apply /(equivP (t_closure_1nP x y)).
  symmetry; exact: clos_trans_t1n_iff.
Qed.

Lemma clos_trans_gt : 
  clos_trans T (@mrel M η T f) ≦ (>%O : rel T).
Proof. 
  move=> ??; rewrite/mrel /=.
  elim=> [y z /descend | x y z _ ] //=.
  move=> /[swap] _ /[swap]; exact: lt_trans.
Qed.

Lemma t_closure_gt : t_closure ≦ (>%O : rel T).
Proof. by move=> x y /t_closureP /clos_trans_gt. Qed.

Lemma t_closure_antisym : antisymmetric t_closure.
Proof.
  move=> x y /andP[] /t_closure_gt ? /t_closure_gt ?. 
  by apply /eqP; rewrite eq_le !ltW.
Qed.

Lemma t_closure_trans : transitive t_closure.
Proof.
  move=> y x z /t_closureP ? /t_closureP ?.
  apply /t_closureP /t_trans; eauto. 
Qed.

Lemma rt_closureP x y :
  reflect (clos_refl_trans T (@mrel M η T f) x y) (rt_closure x y).
Proof.
  apply /equivP; last first.
  { rewrite clos_refl_transE clos_refl_hrel_qmk. 
    apply or_iff_compat_l; symmetry.
    apply rwP; exact: t_closureP. }
  rewrite /t_closure /rt_closure /wsuffix mem_alt mem_ret eq_sym /=.
  by apply predU1P.
Qed.

Lemma rt_closureE : rt_closure ≡ t_closure^?.
Proof. 
  move=> x y /=; rewrite /rt_closure /t_closure /wsuffix. 
  rewrite alt_morph /Alt /= /monae_lib.curry /= mem_cat /dhrel_one.
  by rewrite mem_ret eq_sym.
Qed.

Lemma rt_closure_ge : rt_closure ≦ (>=%O : rel T).
Proof.
  rewrite rt_closureE.
  move=> x y /orP[/eqP<-//=|].
  move=> /t_closure_gt; exact: ltW.
Qed.

Lemma rt_closure_refl x : rt_closure x x.
Proof.
  rewrite /rt_closure alt_morph /Alt /= /monae_lib.curry /= mem_cat.
  by rewrite mem_ret eq_refl. 
Qed.

Lemma rt_closure_antisym : antisymmetric rt_closure.
Proof.
  move=> x y /andP[]. 
  move=> /rt_closure_ge /= xy /rt_closure_ge /= yx. 
  by apply /eqP; rewrite eq_le xy yx. 
Qed.

Lemma rt_closure_trans : transitive rt_closure.
Proof.
  move=> y x z /rt_closureP xy /rt_closureP ?.
  by apply/rt_closureP; apply: rt_trans xy _.
Qed.

End WfRTClosure.

End WfClosure.

