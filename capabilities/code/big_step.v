Set Warnings "-notation-overridden,-parsing".
(*
Author: Rodrigo Raya

Following "The Semantics of Ownership and Borrowing in the Rust Programming Language" by Nienke Wessel.
*)

From Coq Require Import ZArith.Int.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import Capabilities.CustomTactics.

Import ListNotations.

Definition vname := string.

Inductive zext :=
| non_declared
| not_assigned
| val : Z -> zext.

Declare Scope move_scope.
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
  fun x' => if String.eqb x x' then v else s x'.

Lemma update_eq : forall (s: state) (x1 x2: string) (v: zext),
    x1 = x2 -> update s x1 v x2 = v.
Proof. unfold update; repeat light || destruct_match || strings. Qed.

Lemma update_refl : forall (s: state) (x: string) (v: zext),
    update s x v x = v.
Proof. repeat lights || rewrite update_eq. Qed.

Lemma update_neq : forall (s: state) (x1 x2: string) (v: zext),
    x1 <> x2 -> update s x1 v x2 = s x2.
Proof. unfold update; repeat light || destruct_match || strings. Qed.

Lemma update_com :
  forall (x1 x2: string) (s: state) (v: zext),
    update (update s x1 v) x2 v = update (update s x2 v) x1 v.
Proof.
  unfold update; repeat light || destruct_match ||
         apply functional_extensionality.
Qed.

Definition update_list {abs_value: Type} 
  (s : abs_state abs_value) (l : list string) (v : abs_value) :=
  fold_left (fun (s': abs_state abs_value) (x: string)
             => update s' x v) l s.

Lemma update_to_list :
  forall (x: string) (l: list vname) (s: state) (v: zext),
    update_list (update s x v) l v = update (update_list s l v) x v.
Proof.
  induction l;
    repeat clarify || rewrite update_com || rewrite_back_any.
Qed.

Lemma update_list_neq :
  forall (l: list string) (s: state) (x: string) (v: zext),
    not (In x l) -> update_list s l v x = s x.
Proof.
  induction l; repeat clarify || rewrite_any || rewrite update_neq. 
Qed.

Lemma update_list_eq :
  forall (l: list string) (s: state) (x: string) (v: zext),
    In x l -> update_list s l v x = v.
Proof.
  induction l;
  repeat clarify || rewrite update_to_list || unfold update ||
         rewrite String.eqb_refl.
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
  Ltac inductive P :=
      match goal with
      | [ IH: forall s s1 s2, P (?c1,s) s1 ->
                         P (?c1,s) s2 ->
                         s1 = s2,
            H1: P (?c1,?s) ?s3,
            H2:  P (?c1,?s) ?s4 |- _ ] =>
        pose proof (IH s s3 s4 H1 H2)
      end.
  induction c;
  repeat light || invert_pred big_step || inductive big_step.
Qed.

(*
After execution, a program no longer has variables in memory.
*)
Theorem variable_allocation:
  forall (c: com) (s s' : state) (y : string),
    (c,s) ⟹__b s' -> aval s (var y) = -__u -> aval s' (var y) = -__u.
Proof.
  Ltac destruct_updates :=
    match goal with
    | [ |- context[update _ ?x _ ?y] ] =>
      destruct (String.eqb x y) eqn: eq
    | [ |- context[update_list _ ?l _ ?y] ] =>
      destruct (in_dec string_dec y l)
    end.

  Ltac inductive_update :=
    repeat light || rewrite update_refl || rewrite update_neq ||
           eapply_any.

  Ltac inductive_update_list :=
    match goal with
    | [ H: In ?y ?l |- context[update_list _ ?l _ ?y] ] =>
      rewrite update_list_eq; try light
    | _ =>
      rewrite update_list_neq; try light;
      destruct_updates; inductive_update
    end. 
     
  induction c;
    repeat clarify || invert_pred big_step.
  - destruct_updates; strings; inductive_update.
  - destruct_updates; inductive_update_list.
Qed.
