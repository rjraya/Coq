Set Warnings "-notation-overridden,-parsing".
(*
Author: Rodrigo Raya

Following "The Semantics of Ownership and Borrowing in the Rust Programming Language" by Nienke Wessel.
*)

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import ZArith.Int.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.

Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Definition vname := string.

Inductive zext :=
| non_declared
| not_assigned
| val : Z -> zext.

Bind Scope move_scope with zext.
Notation "-__u" := non_declared : move_scope.
Notation "⊥" := not_assigned : move_scope.
 
Inductive type :=
| Int : type.

Inductive expr :=
| var : vname -> expr
| integer : Z -> expr
| add : expr -> expr -> expr.

Inductive com :=
| Skip : com
| Seq : com -> com -> com
| Bind : vname -> type -> com -> com
| Assign : vname -> expr -> com.

Bind Scope move_scope with com.
Notation "c1 ;; c2" :=
  (Seq c1 c2) (at level 60, right associativity) : move_scope.
(*
The notation emphasizes that a let statement in Rust:

let x = e

actually refers to a two step process:

1. Variable x is declared.
2. A value is assigned to the resource x owns.

We instead write:

let x in (x = e) 
*)
Notation "'LET' x ',' t 'IN' b" :=
  (Bind x t b) (at level 50, left associativity) : move_scope.
Notation "x ';=' e" :=
  (Assign x e) (at level 50) : move_scope.

Definition prog0 : com := Skip.

(* Some variables to work with *)
Definition X : string := "x".
Definition Y : string := "y".
Definition Z : string := "z".

Definition prog1 : com := LET X , Int IN Skip.

Definition prog2 : com :=
  LET X , Int IN (X ;= (integer 0) ;;
   LET Y , Int IN (Y ;= (var X) ;;
    LET Z , Int IN (Z ;= (var Y)))).

Definition state := vname -> zext.

Definition abs_state (A:Type) := string -> A.

Definition update {abs_value: Type} 
  (s : abs_state abs_value) (x : string) (v : abs_value) :=
  fun x' => if string_dec x x' then v else s x'.

Lemma update_eq : forall (s: state) (x: string) (v: zext),
    update s x v x = v.
Proof.
  intros. unfold update. destruct (string_dec x x) as [|Hs].
  - reflexivity. 
  - contradiction.
Qed.

Lemma update_neq : forall (s: state) (x1 x2: string) (v: zext),
    x1 <> x2 -> update s x1 v x2 = s x2.
Proof.
  intros. unfold update. destruct (string_dec x1 x2).
  - contradiction.
  - reflexivity.
Qed.

Definition update_list {abs_value: Type} 
  (s : abs_state abs_value) (l : list string) (v : abs_value) :=
  fold_left (fun (s': abs_state abs_value) (x: string)
             => update s' x v) l s.
 
Fixpoint contains (l: list string) (x: string): bool :=
  match l with
  | [] => false
  | h :: tl => (if (string_dec h x) then true else (contains tl x))
  end.

(* Some lemmas to finish the last case of variable allocation *)
Lemma update_comm_elems :
  forall (l1 l2: string) (s: state)  (x: string) (v: zext),
    update_list s [l1;l2] v x = update_list s [l2;l1] v x.
Proof.
  intros. 
  simpl.
  destruct (string_dec l1 l2).
  - subst. reflexivity.
  - unfold update.
    destruct (string_dec l2 x);
    destruct (string_dec l1 x); try(reflexivity).
Qed.

Lemma update_comm_list :
  forall (l1: string) (l2: list string) (s: state)
    (x: string) (v: zext),
    update_list s (l1::l2) v x = update_list s (l2++[l1]) v x.
Proof.
  induction l2.
  - simpl. intros. reflexivity.
  - simpl. intros. rewrite <- (IHl2 (update s a v) x v).
    simpl.
    assert (update (update s l1 v) a v =
            update (update s a v) l1 v).
    { apply functional_extensionality. intros.
      apply update_comm_elems. }
    rewrite H. reflexivity.
Qed.

Lemma update_comm :
  forall (l1 l2: list string) (s: state) (x: string) (v: zext),
    update_list s (l1++l2) v x = update_list s (l2++l1) v x.
Proof.
  induction l1.
  - simpl. intros. rewrite app_nil_r. reflexivity.
  - intros. simpl.
    assert (l2 ++ a :: l1 = (l2 ++ [a]) ++ l1).
    { apply (app_assoc l2 [a] l1). }
    rewrite H.
    rewrite <- (IHl1 (l2++[a]) s x v).
    rewrite app_assoc.
    rewrite <- (update_comm_list a (l1++l2)).
    reflexivity.
Qed.

Lemma update_last:
  forall (l: list string) (s: state)  (x: string) (v: zext),
    update_list s (l++[x]) v x = v.
Proof.
  induction l.
  - intros. simpl. apply update_eq.
  - intros. simpl. apply IHl.
Qed.

Lemma update_head :
  forall (l: list string) (s: state)  (x: string) (v: zext),
     update_list s (x::l) v x = v.
Proof.
  intros. 
  assert(update_list s (x::l) v x = update_list s (l++[x]) v x).
  { apply update_comm_list. }
  rewrite H. apply update_last. 
Qed.

Lemma update_contained :
  forall (l: list string) (s: state)  (x: string) (v: zext),
     contains l x = true -> update_list s l v x = v.
Proof.
  induction l; intros.   
  - discriminate.
  - destruct (string_dec a x).
    + subst. apply update_head.
    + simpl. apply IHl. simpl in H.
      destruct (string_dec a x). contradiction. apply H.      
Qed.

Lemma update_not_contained :
  forall (l: list string) (s: state)  (x: string) (v: zext),
     contains l x = false -> update_list s l v x = s x.
Proof.
  induction l; intros.   
  - reflexivity.
  - simpl. rewrite (IHl (update s a v) x v).
    + unfold update. simpl in H. destruct (string_dec a x).
      ++ discriminate.
      ++ reflexivity.
    + simpl in H. destruct (string_dec a x).
      ++ discriminate.
      ++ apply H.    
Qed.

Fixpoint vars (e: expr): list string :=
  match e with
  | var vn => [vn]
  | integer i => []
  | add e__1 e__2 => vars (e__1) ++ vars(e__2)
  end.

Fixpoint aval (s : state) (e : expr): zext :=
  match e with
  | var vn => s vn
  | integer i => val i
  | add e__1 e__2 =>
     match (aval s e__1, aval s e__2) with
     | (val i, val j) => val (i + j)
     | _ => non_declared
     end
  end.

Reserved Notation "e '⟹__b' b" (at level 90, left associativity).

Inductive big_step : com * state -> state -> Prop :=
| BSkip (s: state) : (Skip, s) ⟹__b s
| BSeq (s__1 s__2 s__3: state) (c__1 c__2: com) :
    (c__1,s__1) ⟹__b s__2 -> (c__2,s__2) ⟹__b s__3 -> (c__1;;c__2,s__1) ⟹__b s__3
| BLet (s s': state) (c : com) (x : vname) (t : type) :
    (c,update s x ⊥) ⟹__b s' ->
     (LET x , t IN c, s) ⟹__b (update s' x (s x))
| BAssign (s: state) (e : expr) (x: string) :
    aval s (var x) = ⊥ -> aval s e <> ⊥ -> aval s e <> -__u ->
    (x ;= e, s) ⟹__b (update_list (update s x (aval s e)) (vars e) -__u)
where "e '⟹__b' b" := (big_step e b) : move_scope.

Open Scope move_scope.

Theorem big_step_deterministic : forall (c: com) (s s__1 s__2 : state),
    (c,s) ⟹__b s__1 -> (c,s) ⟹__b s__2 -> s__1 = s__2.
Proof.
  intros c.
  induction c; intros s s__1 s__2 H1 H2;
  inversion H1; inversion H2; subst; try(reflexivity).
  - assert(eq1: s__3 = s__6). { apply (((IHc1 s s__3 s__6) H5) H11). }
    rewrite <- eq1 in H12.
    apply (((IHc2 s__3 s__1 s__2) H6) H12). 
  - rewrite ((IHc (update s v ⊥) s' s'0) H5 H10). reflexivity.
Qed.

(*
After execution, a program no longer has variables in memory.
*)
Theorem variable_allocation: forall (c: com) (s s' : state) (vn y : string),
    (c,s) ⟹__b s' -> aval s (var y) = -__u -> aval s' (var y) = -__u.
Proof.
  induction c; intros s s' vn y H1 H2; inversion H1; subst.
  - apply H2.
  - assert(eq1: aval s__2 (var y) = -__u).
    { apply ((IHc1 s s__2 vn y) H5 H2). }
    apply ((IHc2 s__2 s' vn y) H6 eq1).
  - destruct (string_dec v y); simpl.
    + rewrite e. rewrite update_eq. apply H2.
    + rewrite update_neq; try (apply n).
      apply ((IHc (update s v ⊥) s'0 vn y) H5); simpl.
      rewrite update_neq; try (apply n). apply H2.
  - destruct (string_dec v y). 
    + subst. rewrite H2 in H4. discriminate.
    + destruct (contains (vars e) y) eqn: H.
      ++ simpl. apply update_contained. apply H.
      ++ simpl. rewrite update_not_contained; try(apply H). simpl.
        unfold update. destruct (string_dec v y);  try(contradiction).
        apply H2.
Qed.
