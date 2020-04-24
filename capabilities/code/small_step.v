Set Warnings "-notation-overridden,-parsing".
(*
Author: Rodrigo Raya

Following "The Semantics of Ownership and Borrowing in the Rust Programming Language" by Nienke Wessel.
*)

From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.Int.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
(* for specific induction *)
Require Import Coq.Program.Equality.
Require Import Capabilities.big_step.
Require Import Capabilities.CustomTactics.

Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* Small-step semantics *)

Inductive instruction :=
| prog_instr : vname * zext -> instruction
| command : com -> instruction.

Notation "'c' com" := (command com) (at level 20) : move_scope.
Notation "'i' p_instr" := (prog_instr p_instr) (at level 20) : move_scope.

Definition list := list instruction.

Reserved Notation "e '⟹__s' b" (at level 120, left associativity).

Inductive small_step : instruction * list * state ->
                        instruction * list * state -> Prop :=
| SLoad (s: state) (I: instruction) (L: list) :
    (c Skip, I :: L, s) ⟹__s (I,L,s)
| SComp (s : state) (c__1 c__2: com) (L : list) :
    (c  (c__1;;c__2),L,s) ⟹__s  (c c__1, c c__2 :: L,s)
| SAss (s : state) (e : expr) (x: string) (L : list) :
    (c (x ;= e),L,s) ⟹__s
     (c Skip,L,update_list (update s x (aval s e)) (vars e) -__u)                 
| SLet (s : state) (c' : com) (x : vname) (t : type) (L:list) :
    (c (LET x , t IN c'), L, s) ⟹__s
     (c c', i (x, (s x)) :: L, update s x ⊥)
| SSet (s : state) (x : string) (v : zext) (L : list) :
    (i (x,v),L,s) ⟹__s (c Skip,L, update s x v)                                    
where "e '⟹__s' b" := (small_step e b) : move_scope.

Lemma deterministic_one_step
  (conf conf1 conf2: instruction * list * state) :
  (conf ⟹__s conf1) ->
  (conf ⟹__s conf2) ->
  conf1 = conf2.
Proof. induction 1; repeat lights || invert_pred small_step. Qed.

Inductive star {A : Type} (r : A -> A -> Prop) : A -> A -> Prop :=
| star_refl x : star r x x
| star_step x y z : r x y -> star r y z -> star r x z.

Notation "x '⟹__s*' y" := (star small_step x y) (at level 20) : move_scope.

Hint Constructors star : star.

Lemma star_trans {A} (r : A -> A -> Prop) :
  forall x y z, star r x y -> star r y z -> star r x z.
Proof.
  intros until 1.
  generalize dependent z.
  induction H; repeat clarify || eapply star_step.
Qed.

Lemma star_step' {A} (r : A -> A -> Prop) :
  forall x y, r x y -> star r x y.
Proof. light. eauto using star_step, star_refl. Qed.

Hint Resolve star_step' : star.

Inductive splus {A : Type} (r : A -> A -> Prop) : A -> A -> Prop :=
| plus_step x y : r x y -> splus r x y
| plus_steps x y z : r x y -> star r y z -> splus r x z.

Notation "x '⟹__s+' y" := (splus small_step x y) (at level 30) : move_scope.

Lemma plus_star {A} (r : A -> A -> Prop) :
  forall x y, splus r x y -> star r x y.
Proof. inversion 1; lights; eauto with star. Qed.

Lemma plus_right {A} (r : A -> A -> Prop) :
  forall x y z, star r x y -> r y z -> splus r x z.
Proof.
  induction 1;
    apply plus_step || 
      light; apply_anywhere (plus_star r); eapply plus_steps;
      clarify; lights.
Qed.
  
(* Traces *)

Definition trace
           (f: nat -> (instruction * list * state)) (m: nat)
           (c1 c2: instruction * list * state)  :=      
    (f 0 = c1) /\ (f m = c2) /\ 
    (forall (idx:nat), (0 <= idx /\ idx < m) -> f idx ⟹__s f (S idx)).

Lemma constant_trace
  (conf: instruction * list * state):
  trace (fun n => conf) 0 conf conf.
Proof. unfold trace; lights; omega. Qed.

Lemma zero_length_trace
  (f: nat -> (instruction * list * state))
  (conf1 conf2: instruction * list * state):
  trace f 0 conf1 conf2 -> conf1 = conf2. 
Proof. unfold trace; lights. Qed.

Lemma nonzero_length_trace
  (m: nat) (f: nat -> (instruction * list * state))
  (conf1 conf2: instruction * list * state):
  trace f (S m) conf1 conf2 -> (conf1 ⟹__s (f 1)). 
Proof. unfold trace; lights; apply_any; omega. Qed.

Lemma move_trace_left
  (f: nat -> (instruction * list * state)) (m:nat)
   (c0 c1 c2 : instruction * list * state):    
   (c0 ⟹__s c1) ->
   trace f m c1 c2 ->
   trace (fun n  =>
            match n with
            | O => c0
            | S n' => f n'
            end) (S m) c0 c2.
Proof.
  unfold trace; repeat lights || destruct_match || apply_any || omega.
Qed.

Lemma move_trace_right
  (f: nat -> (instruction * list * state)) (m:nat)
   (c1 c2 : instruction * list * state):    
   trace f (S m) c1 c2 ->
   trace (fun n  => f (S n)) (m) (f 1) c2.
Proof. unfold trace; lights; apply_any; omega. Qed.

Lemma small_trace
  (i1 i2 : instruction) (L1 L2 : list) (s1 s2 : state):
  (i1, L1, s1) ⟹__s* (i2, L2,s2) ->
  (exists (f : nat -> (instruction * list * state)) (m : nat),
      trace f m (i1,L1,s1) (i2,L2,s2)).
Proof.
  induction 1; try do 2 destruct_exists; do 2 eexists;
   apply constant_trace || (eapply move_trace_left; clarify). 
Qed.

Lemma small_trace'
  (m : nat) (conf1 conf2 : instruction * list * state)
  (f : nat -> (instruction * list * state)):
  trace f m conf1 conf2 ->
  conf1 ⟹__s* conf2.
Proof.
  Ltac rewrite_trace :=
    match goal with
    | [H: trace _ 0 ?conf1 ?conf2 |- _ ] =>
      apply zero_length_trace in H; try rewrite H
    | [H: trace _ (S ?m) ?conf1 ?conf2 |- _ ] =>
      pose proof H as H';
      eapply nonzero_length_trace in H;
      apply move_trace_right in H'
    end.
  
  generalize dependent conf1.
  generalize dependent f. 
  induction m; intros; rewrite_trace;
   try apply star_refl; try eapply star_step; clarify.
Qed.

Lemma compute_trace_step
  (f: nat -> (instruction * list * state)) (m:nat)
  (conf conf1 conf2: instruction * list * state) :
  trace f (S m) conf1 conf2 ->
  (conf1 ⟹__s conf) ->
  trace (fun n => f (S n)) m conf conf2.
Proof.
  intros.
  Ltac duplicate_trace :=
    match goal with
    | [ H: trace ?f ?m ?conf1 ?conf2 |- _ ] =>
      pose proof H as Hd
    end.

  Ltac one_step_determinism :=
    match goal with
    | [ H1: (?conf ⟹__s ?conf1) ,
        H2: (?conf ⟹__s ?conf2) |- _ ] =>
      pose proof (deterministic_one_step conf conf1 conf2 H1 H2)
    end.
  
  duplicate_trace.
  apply_anywhere move_trace_right.
  apply_anywhere nonzero_length_trace.
  one_step_determinism.
  rewrite_any.
  apply_any.
Qed.

Lemma subtraces_right
  (f: nat -> (instruction * list * state)) (m j:nat)
  (conf1 conf2: instruction * list * state) :
  trace f m conf1 conf2 ->
  0 <= j <= m ->
  trace (fun n => f (n+j)) (m-j) (f j) conf2.
Proof.
  Ltac extract_trace :=
    match goal with
    | [ H: trace ?f ?m ?conf1 ?conf2 |- _ ] =>
      pose proof H as HH;
      destruct HH as [H1' [H2' H3']]
    end.
  
  intros; induction j; extract_trace;
  repeat (split; lights ;
   repeat (try (apply f_equal)) ; try apply_any ; omega). 
Qed.

Lemma subtraces_left
  (f: nat -> (instruction * list * state)) (m j:nat)
  (conf1 conf2: instruction * list * state) :
  trace f m conf1 conf2 ->
  0 <= j <= m ->
  trace (fun n => f n) (j) conf1 (f j).
Proof.
  intros; destruct j; extract_trace;
  split; lights; try apply_any; omega.
Qed.       

Lemma trace_connected
      (f: nat -> (instruction * list * state)) (m:nat)
      (c1 c2: instruction * list * state) :
  trace f m c1 c2 ->
  (forall j, 0 <= j <= m -> (f j ⟹__s* c2 /\ c1 ⟹__s* f j)).
Proof.
  intros; split;
    eapply small_trace';
    (eapply subtraces_right || eapply subtraces_left);
     apply_any.
Qed.

(* Helper measure that decreases on traces *)

Fixpoint atomic_commands (c': com) :=
  match c' with
  | Skip => 1
  | c1 ;; c2 => atomic_commands c1 + atomic_commands c2
  | LET x , t IN b  => 1 + atomic_commands b
  | x ;= e => 1
  end.

Lemma atomic_positive (c': com) : atomic_commands c' > 0.
Proof. induction c'; simpl; omega. Qed.

Hint Rewrite atomic_positive : ariths.

Fixpoint command_number (l: list) :=
  match l with
  | [] => 0
  | c c' :: l => atomic_commands c' + command_number l
  | i p :: l => 1 + command_number l
  end.

Lemma commands_gr_1 (i': instruction): command_number ([i']) > 0.
Proof.
  lights. destruct_match. omega.
  rewrite <- plus_n_O. apply atomic_positive.
Qed.

Definition measure (conf: instruction * list * state) :=
  command_number [fst (fst (conf))] + command_number (snd (fst (conf))).       
Lemma step_decrease
  (conf1 conf2 : instruction * list * state) :
  (conf1 ⟹__s conf2) -> (measure conf2 <= measure conf1).
Proof.
  (repeat clarify || destruct_match);
    invert_pred_unbounded (small_step);
    try clarify;
    try omega.
Qed.

Lemma chain_decrease
   (conf1 conf2 : instruction * list * state) :
  (conf1 ⟹__s* conf2) -> (measure conf2 <= measure conf1).
Proof.  
  induction 1.
  + auto.
  + eapply le_trans. apply_any. apply step_decrease. lights.
Qed.

Lemma skip_decrease_step
 (instr2 : instruction) (L1 L2 : list) (s1 s2 : state) :
  ((c Skip, L1, s1) ⟹__s (instr2, L2, s2)) -> 
  (measure (instr2, L2, s2) < measure (c Skip, L1, s1)).
Proof. inversion 1. lights. destruct_match; omega. Qed.
    
Lemma skip_decrease
 (instr2 : instruction) (L1 L2 : list) (s1 s2 : state) :
  ((c Skip, L1, s1) ⟹__s+ (instr2, L2, s2)) -> 
  (measure (instr2, L2, s2) < measure (c Skip, L1, s1)).
Proof.
  inversion 1; clarify.
  - apply skip_decrease_step. apply_any.
  - eapply le_lt_trans.
    + apply chain_decrease; apply_any.
    + repeat destruct_pairs; eapply skip_decrease_step; apply_any.
Qed.

Corollary pop_changes_stacks_identity
  (l l': list) (s s': state) (i': instruction):
  (c Skip,l,s) ⟹__s+  (i',l',s') -> l <> l'.
Proof.
  Ltac apply_measure :=
    match goal with
    | [H:  (c Skip, ?L1, ?s1) ⟹__s+ (?instr2, ?L2, ?s2) |-
       _ ] =>
      pose proof (skip_decrease ?instr2 ?L1 ?L2 ?s1 ?s2 H)
    end.
  light.
apply_measure .
  pose proof (skip_decrease i' l l' s s' H).
  
  
  let v := (splus small_step (c Skip, l, s) (c Skip, l, s)) in 
   match v with
   | _ _ _ _ => idtac "succ"
   end.
   idtac "succ"
  end. 
  
  apply_measure.
  pose proof (skip_decrease i' l l' s s' H).
  
  apply skip_decrease.
  assert(measure i' l' < measure (c Skip) l).
  { eapply skip_decrease. apply H. }
  assert(command_number [i'] > 0). { apply commands_gr_1. }
  assert(command_number l' < command_number l).
  { unfold measure in H0. simpl in H0. simpl in H1. omega. } 
  intros contra.
  assert(command_number l' = command_number l).
  { rewrite contra. reflexivity. }
  omega.
Qed.


Lemma move_plus (c1 c2 c1' c2' : instruction * list * state ) :
  (c1 ⟹__s+ c2) ->
   (c1 ⟹__s c1') ->
   (c2 ⟹__s c2') ->
   (c1' ⟹__s+ c2').
Proof.
  intros. 
  assert(c1' ⟹__s* c2).
  { inversion H; subst.
    + rewrite (deterministic_one_step c1 c1' c2 H0 H2).
      apply star_refl.
    + rewrite (deterministic_one_step c1 c1' y H0 H2).
      apply H3. } 
  eapply plus_right. apply H2. apply H1.
Qed.

Lemma no_loops ( c1 c2 : instruction * list * state ) :
  ((c1 ⟹__s+ c2) -> c1 = c2 -> False).
Proof.
  intros H.
  destruct c1 as [[i1 l1] s1].
  induction i1 as [p | c']; subst.
  + intros. subst. destruct p as [x v]. 
    assert((c Skip, l1, update s1 x v) ⟹__s+
           (c Skip, l1, update s1 x v)).
      { eapply move_plus. apply H. apply SSet. apply SSet. }
    assert(l1 <> l1).
      { eapply pop_changes_stacks_identity. apply H0. }
      apply H1. reflexivity.
  + generalize dependent c2.
    generalize dependent l1.
    generalize dependent s1.
    induction c'; intros; subst.
    ++ assert(l1 <> l1).
      { eapply pop_changes_stacks_identity. apply H. }
      apply H0. reflexivity.
    ++ assert((c c'1, c c'2 :: l1, s1) ⟹__s+ (c c'1, c c'2 :: l1, s1)).
      { eapply move_plus. apply H. apply SComp. apply SComp. }
      eapply IHc'1. apply H0. reflexivity.
    ++ assert((c c', i (v, s1 v) :: l1, update s1 v ⊥) ⟹__s+
             (c c', i (v, s1 v) :: l1, update s1 v ⊥)).
      { eapply move_plus. apply H. apply SLet. apply SLet. }
      eapply IHc'. apply H0. reflexivity.     
    ++ assert((c Skip, l1,
             update_list (update s1 v (aval s1 e)) (vars e) -__u) ⟹__s+
             (c Skip, l1,
             update_list (update s1 v (aval s1 e)) (vars e) -__u)).
      { eapply move_plus. apply H. apply SAss. apply SAss. }
      assert(l1 <> l1).
      { eapply pop_changes_stacks_identity. apply H0. }
      apply H1. reflexivity.
Qed.

(* Stack *)

Lemma pop_skip (i1 i2 i': instruction) (l : list) (s1 s2: state) :
  ((i1,i'::l,s1) ⟹__s (i2,l,s2)) ->
  i1 = c Skip  /\ s1 = s2.
Proof.
  intros. inversion H.
  - split; reflexivity.
  - assert(List.length (c c__2 :: i' :: l) = List.length l).
    { rewrite H5. reflexivity. }
    simpl in H0. omega.
  - assert(List.length (i' :: l) = List.length l).
    { rewrite H5. reflexivity. }
    simpl in H0. omega.
  - assert(List.length (i (x, s1 x) :: i' :: l) = List.length l).
    { rewrite H5. reflexivity. }
    simpl in H0. omega.
  - assert(List.length (i' :: l) = List.length l).
    { rewrite H5. reflexivity. }
    simpl in H0. omega.
Qed.

(*
Lemma push_let_comp
   (i1 i2 i': instruction) (l : list) (s1 s2: state) :
  ((i1,l,s1) ⟹__s (i2,i'::l,s2)) ->
  (exists c1 c2, i1 = c (c1 ;; c2)  /\ s1 = s2) \/
  (exists x t c', i1 = c (LET x , t IN c') /\ s2 = update s1 x (s1 x)).
Proof.
  intros.
  inversion H; subst. 
  - 
Admitted.
*)

Lemma stack_changes (i1 i2: instruction) (l1 l2 : list) (s1 s2: state) :
  ((i1,l1,s1) ⟹__s (i2,l2,s2)) ->
  (l1 = l2 \/ (exists push, l2 = push :: l1) \/ (exists pop, l1 = pop :: l2)).
Proof.
  intros. 
  inversion H; subst. 
  - right. right. eauto.
  - right. left. eauto.
  - left. eauto. 
  - right. left. eauto.  
  - left. eauto. 
Qed.

Lemma stack_size_changes
  (i1 i2: instruction) (l1 l2 : list) (s1 s2: state) :
  ((i1,l1,s1) ⟹__s (i2,l2,s2)) ->
  List.length l1 = List.length l2 \/
  List.length l1 = List.length l2 + 1 \/
  List.length l1 + 1 = List.length l2.
Proof.
  intros. 
  destruct (stack_changes i1 i2 l1 l2 s1 s2 H)
    as [eq1 | [eq2 | eq3]].
  - left. rewrite eq1. reflexivity.
  - right. right. destruct eq2. rewrite H0. simpl. omega.
  - right. left. destruct eq3. rewrite H0. simpl. omega.
Qed.

Lemma stack_size_changes_explicit
  (conf1 conf2: instruction * list * state) :
  ((conf1 ⟹__s conf2) ->
  (List.length (snd (fst (conf1))) <>
  List.length (snd (fst (conf2)))) ->
  (List.length (snd (fst (conf1))) <>
  List.length (snd (fst (conf2))) + 1) ->
  (List.length (snd (fst (conf1))) + 1 <>
  List.length (snd (fst (conf2)))) ->
  False).
Proof.
  intros.
  destruct conf1 as [[i1' l1] s1].
  destruct conf2 as [[i2' l2] s2].
  simpl in H0. simpl in H1. simpl in H2.
  destruct (stack_size_changes i1' i2' l1 l2 s1 s2 H)
    as [eq1 | [eq2 | eq3]]; omega. 
Qed.
    
Definition trace_not_below
  (f: nat -> (instruction * list * state)) (m:nat) (l2: list) :=
  (forall j, 0 <= j < m -> (exists l', snd(fst (f j)) = l' ++ l2)).

Lemma trace_below_right
  (f: nat -> (instruction * list * state)) (m:nat) (l:list):
  ((exists l', snd (fst (f 0)) = l' ++ l) /\
   trace_not_below (fun n : nat => f (S n)) m l) ->
  trace_not_below f (S m) l.
Proof.
  intros. destruct H as [H1 H2].
  unfold trace_not_below. unfold trace_not_below in H2.
  intros. destruct j.
  - apply H1.
  - apply H2. omega.
Qed.

(* push lemma *)
Lemma not_below
  (f: nat -> (instruction * list * state)) (m:nat)
  (c1 c2: instruction) (s1 s2: state) (l1 l2: list) :
  trace f m (c1,l1++l2,s1) (c2,l2,s2) ->
  trace_not_below f m l2.
Proof.
  unfold trace_not_below. intros. 
  remember H as tr.
  unfold trace. destruct H as [eq1 [eq2 eq3]].
  induction j.
  + exists l1. rewrite eq1. reflexivity.
  + destruct IHj as [lj]; try(omega).
    assert(f j ⟹__s f (S j)). { apply eq3. omega. }
    assert(f j ⟹__s+ (c2,l2,s2)). {
      assert(f (S j) ⟹__s* (c2,l2,s2)). {
        eapply trace_connected. apply tr. omega. 
      }
      eapply plus_steps. apply H1. apply H2. 
    } 
    destruct (f j) as [p js]; destruct p as [jc jl].
    destruct (f (S j)) as [p sjs]; destruct p as [sjc sjl].  
    destruct (stack_changes jc sjc jl sjl js sjs H1) as [cond1 | [cond2 | cond3]].
    ++ simpl. simpl in H. exists lj. subst. reflexivity.
    ++ simpl. simpl in H. destruct cond2 as [push]. subst. 
      exists (push :: lj). auto. 
    ++ simpl. simpl in H. destruct cond3 as [pop].
      assert(jc = c Skip /\ js = sjs).
      { eapply pop_skip. rewrite H3 in H1. apply H1. }
      destruct H4 as [H4 H4'].
      subst. 
      destruct lj.
    * simpl in H1. simpl in H2. simpl in H3.
      destruct (pop_changes_stacks_identity l2 l2 sjs s2 c2 H2).
      reflexivity. 
    * simpl in H3. injection H3. intros. subst. exists lj. reflexivity.
Qed.

Lemma nil_trace
        (f: nat -> (instruction * list * state))
        (c1 c2: instruction) (l1 l2: list) (s1 s2: state):
    trace f 0 (c1,l1,s1) (c2,l2,s2) ->
    List.length l1 = List.length l2. 
Proof.
  intros. destruct H as [eq1 [eq2 eq3]].
  rewrite eq1 in eq2. injection eq2. intros. subst. reflexivity.
Qed.

Lemma linear_traces
  (f: nat -> (instruction * list * state)) (m j:nat)
  (c1 c2: instruction * list * state):
  trace f m c1 c2 -> 0 <= j <=  m ->
  (exists g m', trace g m' (f j) c2 /\
           (forall j', j <= j' <=  m -> f j' = g (j' - j)) /\
           m' + j = m
  ).
Proof.
  intros.
  induction j.
  - exists f. exists m. split.
    + assert(f 0 = c1). { apply H. } rewrite H1. apply H.
    + split. intros. apply f_equal. omega. omega.
  - destruct IHj as [g [m' [h1 h2]]]. omega.
    destruct m.
    + omega.
    + destruct m'.
      * assert(f (S j) ⟹__s* c2).
        { apply (trace_connected f (S m) c1 c2 H (S j)). omega. }
        destruct H as [eq1 [eq2 eq3]].
        destruct h1 as [eq1' [eq2' eq3']].
        assert(f j ⟹__s f (S j)).
        { apply eq3. omega. }
        assert(f j = c2).
        { rewrite eq1' in eq2'. apply eq2'. }
        assert(f (S j) ⟹__s+ f (S j)).
        { eapply plus_right. apply H1. rewrite <- H2. apply H. }
        exfalso. eapply no_loops. apply H3. reflexivity.
      * exists (fun n => g (S n)). exists m'. split.
        ** eapply compute_trace_step. apply h1.
           destruct H as [eq1 [eq2 eq3]].
           apply eq3. omega.
        ** split. intros.        
           assert(S (j' - S j) = j' - j). omega. rewrite H2.
           apply h2. omega. omega.
Qed.

(* pop lemma *)
Lemma compute_trace
  (f: nat -> (instruction * list * state)) (m:nat)
  (c1 c2 a: instruction) (l1 l2: list) (s s': state):
  trace f m (c1, a::l1 ++ l2,s) (c2,l2,s') ->
  (exists j s1, 0 <= j <  m /\ f j = (c Skip,a :: l1 ++ l2,s1) ).
Proof.  
  intros.
  induction c1 as [p | c']; intros.
  - destruct m.
    + destruct H as [eq1 [eq2 eq3]].
      rewrite eq1 in eq2. injection eq2. intros.
      assert(List.length (a :: l1 ++ l2) = List.length l2).
      { rewrite H0. reflexivity. }
      simpl in H2. rewrite app_length in H2. omega.
    + destruct p as [x v].
      exists 1. exists (update s x v).
      destruct m.
      ++ assert(f 0 ⟹__s f 1). { apply H. omega. }
        assert(f 0 = (i (x, v), a :: l1 ++ l2, s)). { apply H. }
        assert(f 1 = (c2, l2, s')). { apply H. }
        assert(f 1 = (c Skip, a :: l1 ++ l2, update s x v)).
        { rewrite H1 in H0. inversion H0. subst. reflexivity. }
        rewrite H2 in H3. injection H3. intros.
        assert(List.length (a :: l1 ++ l2) = List.length l2).
        { rewrite <- H5. reflexivity. }
        simpl in H7. rewrite app_length in H7. omega.
      ++ split. omega. inversion H.
        assert(f 0 ⟹__s f 1). { apply H1. omega. }
        rewrite H0 in H2. inversion H2. subst. reflexivity.
  - generalize dependent c2.
    generalize dependent a.
    generalize dependent m.
    generalize dependent l1.
    generalize dependent f.
    generalize dependent s. 
    induction c'; intros.
    + destruct m.
      ++ assert(List.length (a :: l1 ++ l2) = List.length l2).
        { eapply nil_trace. apply H. }
        simpl in H0. rewrite app_length in H0. omega.
      ++ exists 0. exists s. 
        split. omega.
        apply H.
    + destruct m.
      ++ assert(List.length (a :: l1 ++ l2) = List.length l2).
        { eapply nil_trace. apply H. }
        simpl in H0. rewrite app_length in H0. omega.      
      ++ destruct (IHc'1 s (fun n : nat => f (S n)) (a::l1)
                  m (c c'2) c2) as [j1 [s1 [h1 h1']]].
        { eapply compute_trace_step. apply H. apply SComp. }
        destruct m.        
        * omega.
        * assert(f (S j1) ⟹__s f (S (S j1))).
          { destruct H as [eq1 [eq2 eq3]]. apply eq3. omega.   }
          assert(f (S (S j1)) = (c c'2,(a :: l1) ++ l2, s1)).
          { rewrite h1' in H0. inversion H0. subst. reflexivity. }
          destruct (linear_traces f (S (S m)) (S (S j1))
          (c (c'1;; c'2), a :: l1 ++ l2, s)
          (c2, l2, s') H) as [g [m' [h2 [h2' h22]]]]. omega.
          rewrite H1 in h2.
          destruct (IHc'2 s1 g l1 m' a c2 h2) as [j3 [s3 [h3 h3']]].
          exists (j3+(S (S j1))). exists s3.
          split. omega. rewrite <- h3'.
          rewrite (h2' (j3 + S (S j1))).
          assert(j3 + S (S j1) - S (S j1) = j3). omega.
          rewrite H2. reflexivity. omega.     
    + assert(f 0 = (c (LET v, t IN c'), a :: l1 ++ l2, s)).
         { apply H. }                    
      destruct m.
     ++ assert(List.length (a :: l1 ++ l2) = List.length l2).
        { eapply nil_trace. apply H. }
        simpl in H1. rewrite app_length in H1. omega.     
     ++ assert(f 0 ⟹__s f 1). { apply H. omega. }
       assert(trace (fun n : nat => f (S n)) m
                    (c c', i (v, s v) :: a :: l1 ++ l2,
                     update s v ⊥) (c2, l2, s')).
       { eapply compute_trace_step. apply H. apply SLet. }
       destruct (IHc' (update s v ⊥) (fun n : nat => f (S n))
                      (a :: l1) m (i (v, s v)) c2 H2)
         as [j' [s1 [h1 h1']]].       
       destruct m; try(omega).         
       assert(f 1 ⟹__s f 2). { apply H. omega. }
       assert(f 1 = (c c',  i (v, s v) :: a :: l1 ++ l2,
                     update s v ⊥)).
       { rewrite H0 in H1. inversion H1. reflexivity. }
       assert(S j' <= (S (S m))). { omega. }
       assert(f (S (S m)) = (c2, l2, s')). apply H.                
       destruct(Nat.eqb_spec (S j') (S (S m))).
       * exfalso. rewrite e in h1'. rewrite H6 in h1'.
         injection h1'. intros.
         assert(List.length l2 =
                List.length (i (v, s v) :: a :: l1 ++ l2)).
         { rewrite <- H8. reflexivity. }
         simpl in H10. omega.
       * assert(f (S j') ⟹__s f (S (S j'))).
         { apply H. omega. }
         assert(f (S (S j')) =  (i (v, s v), (a :: l1) ++ l2, s1)).
            { rewrite h1' in H7. inversion H7. reflexivity. }
         destruct(Nat.eqb_spec (S (S j')) (S (S m))).                        ** exfalso. rewrite e in H8. rewrite H6 in H8.
            injection H8. intros.
            assert(List.length l2 =
                List.length (a :: l1 ++ l2)).
            { rewrite <- H10. reflexivity. }
            simpl in H12. rewrite app_length in H12. omega.
         ** assert(f (S (S j')) ⟹__s f (S (S (S j')))).
            { apply H. omega. }                                                     assert(f (S (S (S j'))) =                                                   (c Skip, a::l1 ++ l2, update s1 v (s v))).
            { rewrite H8 in H9. inversion H9. reflexivity. }                    destruct(Nat.eqb_spec (S (S (S j'))) (S (S m))).
            *** exfalso. rewrite e in H10. rewrite H6 in H10.
                injection H10. intros.
                assert(List.length l2 =
                  List.length (a :: l1 ++ l2)).
                { rewrite <- H12. reflexivity. }
                simpl in H14. rewrite app_length in H14. omega.
            *** exists (S (S (S j'))). exists (update s1 v (s v)).
                split. omega. apply H10.                                            
   + destruct m. 
      ++ assert(List.length (a :: l1 ++ l2) = List.length l2).
        { eapply nil_trace. apply H. }
        simpl in H0. rewrite app_length in H0. omega.      
      ++ assert(trace (fun n : nat => f (S n)) m
            (c Skip, a :: l1 ++ l2,
             update_list (update s v (aval s e)) (vars e) -__u)
                     (c2, l2, s')).
        { eapply compute_trace_step. apply H. apply SAss. }
        destruct m.
        * assert(List.length (a :: l1 ++ l2) = List.length l2).
          { eapply nil_trace. apply H0. }
          simpl in H1. rewrite app_length in H1. omega.
        * exists 1. exists (update_list (update s v (aval s e)) (vars e) -__u).
          split. omega. apply H0.
Qed.

(* Back to thesis *)

(* Lemma 3.5.1 *)
Lemma comp_to_skip (c1 c2 : com) (L : list) (s s' : state):
  (c (c1;;c2),L,s) ⟹__s* (c Skip,L,s') ->
  (exists (s2 : state),
      (c c1, c c2 :: L, s) ⟹__s* (c Skip, c c2 :: L,s2) /\
      ((c Skip, c c2 :: L,s2) ⟹__s (c c2, L, s2)) /\
       (c c2, L, s2) ⟹__s* (c Skip,L,s')).
Proof.
  intros.
  inversion H; inversion H0. subst.
  assert(exists f m, trace f m  (c c1, c c2 :: L, s) (c Skip, L, s')).
  { apply small_trace. apply H1. }
  destruct H2 as [f [m H']].
  assert(exists (j : nat) (s1 : state),
         0 <= j < m /\ f j = (c Skip, (c c2) :: L, s1)).
  { apply (compute_trace f m (c c1) (c Skip) (c c2) [] L s s').
    simpl. apply H'. } 
  destruct H2 as [j [s1 [H2 H2']]].
  exists s1.
  destruct (trace_connected f m
           (c c1, c c2 :: L, s) (c Skip, L, s') H' j) as [eq1 eq2].
  omega. split.
  - rewrite H2' in eq2. apply eq2.
  - split.
    + apply SLoad.
    + rewrite H2' in eq1.
      inversion eq1; subst.
      ++ assert(List.length (c c2 :: L) = List.length L).
        { rewrite H5. reflexivity. }
        simpl in H3. omega.
      ++ inversion H3. subst. apply H4. 
Qed.

(* Lemma 3.5.2 *)
Lemma let_to_skip
  (c': com) (L : list) (s s' : state) (t: type) (x: string) :
  (c (LET x , t IN c'),L,s) ⟹__s* (c Skip,L,s') ->
  (exists (s2 : state),
      (c (LET x , t IN c'), L, s) ⟹__s*
      (c Skip, (i (x, s x)) :: L, s2) /\
      ((c Skip, (i (x, s x)) :: L, s2) ⟹__s (i (x, s x), L,s2)) /\
       (i (x, s x), L,s2) ⟹__s* (c Skip,L,s')).
Proof.
  intros.
  inversion H; inversion H0. subst.
  assert(exists f m, trace f m
          (c c', i (x, s x) :: L, update s x ⊥) (c Skip, L, s')).
  { apply small_trace. apply H1. }
  destruct H2 as [f [m H']].
  assert(exists (j : nat) (s1 : state),
         0 <= j < m /\ f j = (c Skip, i (x, s x) :: L, s1)).
  { apply (compute_trace f m (c c') (c Skip)
                         (i (x, s x)) [] L (update s x ⊥) s').
    simpl. apply H'. } 
  destruct H2 as [j [s1 [H2 H2']]].
  exists s1.
  destruct (trace_connected f m
           (c c', i (x, s x) :: L, update s x ⊥)
           (c Skip, L, s') H' j) as [eq1 eq2].
  omega. split.
  - eapply star_step. apply SLet.
    rewrite H2' in eq2. apply eq2.
  - split.
    + apply SLoad.
    + rewrite H2' in eq1.
      inversion eq1; subst.
      ++ assert(List.length (i (x, s x) :: L) = List.length L).
        { rewrite H5. reflexivity. }
        simpl in H3. omega.
      ++ inversion H3. subst. apply H4.
Qed.

(* Proposition 3.5.3 *)

Lemma between_skips (L : list) (s1 s2 : state):
  (c Skip, L, s1) ⟹__s* (c Skip, L, s2)  -> s1 = s2.
Proof.
  intros.
  inversion H.
  - reflexivity.
  - assert((c Skip, L, s1) ⟹__s+ (c Skip, L, s2)).
    { eapply plus_steps. apply H0. apply H1. }
    exfalso.
    apply (pop_changes_stacks_identity L L s1 s2 (c Skip) H4).
    reflexivity.
Qed.

(*
The effect of a program in memory is not affected by stack content
*)
Proposition stack_independence
  (c': instruction) (l: list) (s s': state) :
  ((c',l,s) ⟹__s* (c Skip,l,s')) ->
  (forall l', (c',l',s) ⟹__s* (c Skip,l',s')).
Proof.
  intros. 
  induction c' as [p | c'].
  - inversion H. subst.
    inversion H0. subst.
    assert(s' = update s x v). {
      rewrite (between_skips l (update s x v) s' H1). reflexivity. }
    rewrite H2. apply  star_step'. apply SSet.
  - generalize dependent l.
    generalize dependent l'. 
    generalize dependent s.
    generalize dependent s'.
    induction c'; intros.
    + assert(s = s'). eapply between_skips. apply H.
      rewrite H0. apply star_refl.
    + destruct (comp_to_skip c'1 c'2 l s s' H) as [s1 [h1 [h2 h3]]].
      eapply star_step. apply SComp.
      eapply star_trans. 
      apply(IHc'1 s1 s ((c c'2) :: l') ((c c'2) :: l) h1).
      eapply star_step. apply SLoad.
      apply (IHc'2 s' s1 l' l h3).
    + destruct (let_to_skip c' l s s' t v H) as [s1 [h1 [h2 h3]]].
      eapply star_step. apply SLet.
      eapply star_trans.
      inversion h1. subst. inversion H0. subst.
      apply (IHc' s1 (update s v ⊥)
                  (i (v, s v) :: l') (i (v, s v) :: l) H1).
      eapply star_step. apply SLoad.
      eapply star_step. apply SSet.
      inversion h3. subst. inversion H0. subst.
      rewrite (between_skips l (update s1 v (s v)) s' H1).
      apply star_refl.
    + inversion H. subst.
      inversion H0. subst.
      eapply between_skips in H1.
      eapply star_step. apply SAss.
      rewrite H1. apply star_refl.
Qed.

(*
In a composition, the execution of c1 does not depend 
on what c2 entails.
*)
Lemma sequential_effects
  (c1 c2: com) (l: list) (s s': state) :
  ((c c1,l,s) ⟹__s* (c Skip,l,s)) ->
  ((c (c1 ;; c2),l,s) ⟹__s* (c c2,l,s)).
Proof.
  intros.
  eapply star_step. apply SComp.
  eapply star_trans.
  apply (stack_independence (c c1) l s s H (c c2 :: l)).
  apply star_step'. apply SLoad.
Qed.

(* Theorem 3.5.5 *)
Lemma determinism
  (c' : instruction) (L : list) (s s1 s2 : state) :
  (c',L,s) ⟹__s* (c Skip,L,s1) ->
  (c',L,s) ⟹__s* (c Skip,L,s2) ->
  s1 = s2.
Proof.
  intros.
  destruct c' as [p | c'].
  - inversion H. inversion H1. subst.
    inversion H0. inversion H3. subst.
    rewrite <- (between_skips L (update s x0 v) s1).
    rewrite <- (between_skips L (update s x0 v) s2).
    reflexivity. apply H4. apply H2.
  - generalize dependent L.
    generalize dependent s1.
    generalize dependent s2.
    generalize dependent s. 
    induction c'; intros. 
    + rewrite <- (between_skips L s s1).
      rewrite <- (between_skips L s s2).
      reflexivity. apply H0. apply H.
    + inversion H. subst. inversion H1. subst.
      destruct (comp_to_skip c'1 c'2 L s s1 H) as [s' [h1 [h2 h3]]].
      destruct (comp_to_skip c'1 c'2 L s s2 H0)
        as [ss' [h1' [h2' h3']]].
      remember (IHc'1 s ss' s' (c c'2 :: L) h1 h1') as eq1.
      subst. 
      apply (IHc'2 ss' s2 s1 L h3 h3').
    + destruct (let_to_skip c' L s s1 t v H) as [s' [h1 [h2 h3]]].
      destruct (let_to_skip c' L s s2 t v H0)
        as [ss' [h1' [h2' h3']]].
      inversion h1. inversion H1. subst.
      inversion h1'. inversion H3. subst.
      remember (IHc' (update s v ⊥) ss' s'
                     (i (v, s v) :: L) H2 H4) as eq.
      subst. 
      inversion h3. inversion H5. subst. 
      rewrite <- (between_skips L (update ss' v (s v)) s1).
      inversion h3'. inversion H7. subst.
      rewrite <- (between_skips L (update ss' v (s v)) s2).
      reflexivity. apply H8. apply H6.
    + inversion H. inversion H1. subst.
      rewrite <- (between_skips L
       (update_list (update s v (aval s e)) (vars e) -__u) s1 H2).
      inversion H0. inversion H3. subst.
      rewrite <- (between_skips L
       (update_list (update s v (aval s e)) (vars e) -__u) s2 H4).
      reflexivity.
Qed.
