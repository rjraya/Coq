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
Open Scope string_scope.
Open Scope list_scope.

Definition vname := string.

Inductive zext :=
| non_declared
| not_assigned
| val : Z -> zext.

Bind Scope move_scope with zext.
Notation "-__u" := non_declared : borrow_scope.
Notation "⊥" := not_assigned : borrow_scope.
 
Inductive type :=
| Int : type
| BorrowedT : type -> type. 

Inductive expr :=
| var : vname -> expr
| integer : Z -> expr
| add : expr -> expr -> expr
| borrowedVar : vname -> expr
| mutBorrowedVar : vname -> expr.

Inductive com :=
| Skip : com
| Seq : com -> com -> com
| Bind : vname -> type -> com -> com                                
| Assign : vname -> expr -> com
| MutBind : vname -> type -> com -> com.

Bind Scope borrow_scope with com.
Notation "c1 ;; c2" :=
  (Seq c1 c2) (at level 60, right associativity) : borrow_scope.
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
  (Bind x t b) (at level 50, left associativity) : borrow_scope.
Notation "x ';=' e" :=
  (Assign x e) (at level 50) : borrow_scope.
Notation "'LETM' x ',' t 'IN' b" :=
  (MutBind x t b) (at level 50, left associativity) : borrow_scope.

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

Definition prog3 : com := LETM X , Int IN Skip.

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
  (s : abs_state abs_value) (l : list string) v :=
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

(*
Collect variables of expression e that are not borrowed 
in expression e.
*)
Fixpoint vars (e: expr): list string :=
  match e with
  | var vn => [vn]
  | integer i => []
  | add e__1 e__2 => vars (e__1) ++ vars(e__2)
  | borrowedVar v => []
  | mutBorrowedVar v => []
  end.

(* Tells if variable is borrowed mutable or the variable
   it points to. *)
Definition mu := string -> (bool * bool * Datatypes.list vname).

Definition mu_union (m1 m2: bool * bool * Datatypes.list vname) := 
  match m1 with
  | (b1,mm1,pt1) =>
    match m2 with
    | (b2,mm2,pt2) =>
      (orb b1 b2, orb mm1 mm2, pt1 ++ pt2)
    end
  end.

Definition update_mu 
  (m : mu) (l : list string) f :=
  fold_left (fun (m': mu) (x: string)
             => update m' x (f x)) l m.


(*
Collect variables of expression e that are borrowed 
in expression e and are mutable.
*)
Fixpoint borrowed (e: expr) (m: mu): list string :=
  match e with
  | var vn => []
  | integer i => []
  | add e__1 e__2 => []
  | borrowedVar v =>
    match m(v) with
    | (_, true ,_) => [v]
    | _ => []
    end
  | mutBorrowedVar v =>
    match m(v) with
    | (_, true ,_) => [v]
    | _ => []
    end
  end.

(* Used to collect all variables in an expression *)
Fixpoint collect (e: expr): list string :=
  match e with
  | var v => [v]
  | integer i => []
  | add e__1 e__2 => vars (e__1) ++ vars(e__2)
  | borrowedVar v => [v]
  | mutBorrowedVar v => [v]
  end.


Fixpoint aval (s : state) (e : expr): zext :=
  match e with
  | var v => s v
  | integer i => val i
  | add e__1 e__2 =>
     match (aval s e__1, aval s e__2) with
     | (val i, val j) => val (i + j)
     | _ => non_declared
     end
  | borrowedVar v => s v
  | mutBorrowedVar v => s v
  end.
