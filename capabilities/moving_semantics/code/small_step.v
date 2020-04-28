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

Hint Constructors small_step: small_step.

Lemma deterministic_one_step
  (conf conf1 conf2: instruction * list * state) :
  (conf ⟹__s conf1) ->
  (conf ⟹__s conf2) ->
  conf1 = conf2.
Proof. induction 1; repeat lights || invert_pred small_step. Qed.

Ltac one_step_determinism :=
  match goal with
  | [ H1: (?conf ⟹__s ?conf1) ,
          H2: (?conf ⟹__s ?conf2) |- _ ] =>
    pose proof (deterministic_one_step conf conf1 conf2 H1 H2)
  end. 
  
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
  induction 1; eauto using plus_step, plus_star, plus_steps.
Qed.
  
(* Traces *)

Definition trace
           (f: nat -> (instruction * list * state)) (m: nat)
           (c1 c2: instruction * list * state)  :=      
    (f 0 = c1) /\ (f m = c2) /\ 
    (forall (idx:nat), idx < m -> f idx ⟹__s f (S idx)).

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
  (conf1 conf2 : instruction * list *state):
  conf1 ⟹__s* conf2 ->
  (exists (f : nat -> (instruction * list * state)) (m : nat),
      trace f m conf1 conf2).
Proof.
  induction 1; lights;
    eauto using constant_trace, move_trace_left. 
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
      poseNew (Mark H "rewrite_trace");
      let H' := fresh H in
      let H'' := fresh H in
      pose proof H as H';
      pose proof H as H'';
      eapply nonzero_length_trace in H';
      apply move_trace_right in H''
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
  j <= m ->
  trace (fun n => f (n+j)) (m-j) (f j) conf2.
Proof.
  Ltac extract_trace :=
    match goal with
    | [ H: trace ?f ?m ?conf1 ?conf2 |- _ ] =>
      let H' := fresh H in
      let H1' := fresh "H1'" in
      let H2' := fresh "H2'" in
      let H3' := fresh "H3'" in 
      pose proof H as H';
      clear H;
      destruct H' as [H1' [H2' H3']]
    end.  

  intros; induction j; extract_trace;
  repeat (split; lights ;
   repeat (try (apply f_equal)) ; try apply_any ; omega). 
Qed.

Lemma subtraces_left
  (f: nat -> (instruction * list * state)) (m j:nat)
  (conf1 conf2: instruction * list * state) :
  trace f m conf1 conf2 ->
  j <= m ->
  trace f j conf1 (f j).
Proof.
  intros; destruct j; extract_trace;
  split; lights; try apply_any; omega.
Qed.       

Lemma trace_connected
      (f: nat -> (instruction * list * state)) (m:nat)
      (c1 c2: instruction * list * state) :
  trace f m c1 c2 ->
  (forall j, j <= m -> (f j ⟹__s* c2 /\ c1 ⟹__s* f j)).
Proof.
  lights;
    eauto using small_trace', subtraces_right, subtraces_left.
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

Lemma command_number_app (l1 l2: list):
  command_number (l1 ++ l2) =
  command_number l1 + command_number l2. 
Proof. 
  induction l1. 
  - clarify.
  - simpl. destruct_match.
    + rewrite_any. omega.
    + rewrite_any. omega.
Qed.
      
Corollary pop_changes_stacks_identity
  (l l': list) (s s': state) (i': instruction):
  (c Skip,l,s) ⟹__s+  (i',l',s') -> (exists l1, l' = l1 ++ l) -> False.
Proof.
  Ltac apply_measure :=
    match goal with
    | [H:  (c Skip, ?L1, ?s1) ⟹__s+ (?instr2, ?L2, ?s2) |-
       _ ] =>
      pose proof (skip_decrease instr2 L1 L2 s1 s2 H)
    end.
  light. apply_measure. lights. 
  (* specialized version of destruct_match to give 
     good names not clashing with the command constructor
     
     check that it really gives good names
   *)
  Ltac destruct_match2 :=
    match goal with
  | |- context [ match ?t with
                 | _ => _
                 end ] =>
        let matched := fresh "matched" in
        destruct t as [c1 | c2] eqn:matched
  | H:context [ match ?t with
                | _ => _
                end ]
    |- _ =>
        let matched := fresh "matched" in
        destruct t as [c1 | c2] eqn:matched
  end.
  
  destruct_match2; rewrite_anywhere command_number_app. omega.
  pose proof (atomic_positive c2). omega.
Qed.

Lemma move_plus (c1 c2 c1' c2' : instruction * list * state ) :
  (c1 ⟹__s+ c2) ->
   (c1 ⟹__s c1') ->
   (c2 ⟹__s c2') ->
   (c1' ⟹__s+ c2').
Proof.
  intros. 
  invert_pred_unbounded (splus small_step); subst;
    one_step_determinism; subst.
  - apply plus_step; apply_any.
  - eapply plus_right; apply_any. 
Qed.

Lemma no_loops ( c1 c2 : instruction * list * state ) :
  ((c1 ⟹__s+ c2) -> c1 = c2 -> False).
Proof.
  intros H.
  destruct c1 as [[i1 l1] s1].
  induction i1 as [p | c']; subst.
  + lights.
    eapply pop_changes_stacks_identity. 
    eapply move_plus;
      try apply_any; try apply SSet.
    exists [] ; eauto.
  + generalize dependent c2.
    generalize dependent l1.
    generalize dependent s1.
    induction c'; lights.
    ++ eapply pop_changes_stacks_identity;
         try apply_any.
       exists [] ; eauto. 
    ++ eapply IHc'1. 
       eapply_anywhere move_plus;
         try apply_any; try apply SComp. reflexivity.
    ++ eapply_any; try reflexivity; 
       eapply_anywhere move_plus;    
        try apply_any; try apply SLet.  
    ++ eapply pop_changes_stacks_identity.
       try eapply move_plus; 
         try apply_any; try apply SAss.
       exists []; eauto.
Qed.

(* Stack *)

Lemma pop_skip
  (conf1 conf2: instruction * list * state) :
  (conf1 ⟹__s conf2) ->
  (exists e, (snd (fst conf1) = e :: snd (fst (conf2)))) ->
   (fst (fst conf1) = c Skip) /\
    (snd (conf1) = snd conf2).
Proof.
  Ltac equal_lengths :=
    match goal with
    | [H: ?l1 = ?l2 |- _] =>
      pose proof (f_equal (@List.length instruction) H)
    end. 
  inversion 1; lights; equal_lengths; lights; omega.
Qed.

Lemma stack_changes
  (conf1 conf2: instruction * list * state):
  (conf1 ⟹__s conf2) ->
  (snd (fst conf1) = snd (fst conf2) \/
   (exists push, snd (fst conf2) = push :: snd (fst conf1)) \/
   (exists pop, snd (fst conf1) = pop :: snd (fst conf2))).
Proof. intros; invert_pred_unbounded (small_step); clarify. Qed.
    
Definition trace_not_below
  (f: nat -> (instruction * list * state)) (m:nat) (l2: list) :=
  (forall j, j < m -> (exists l', snd(fst (f j)) = l' ++ l2)).

(* push lemma *)

(* TODO: find ways to simplify this lemma *)
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
    destruct (stack_changes (jc, jl, js) (sjc, sjl, sjs) H1)
      as [cond1 | [cond2 | cond3]].
    ++ exists lj. lights. 
    ++ destruct cond2 as [push]. exists (push :: lj). lights.
    ++ lights. 
       rewrite_any.      
      assert(jc = c Skip /\ js = sjs).
      { apply (pop_skip (jc, pop :: sjl, js) (sjc, sjl, sjs)).
        apply_any. lights. eexists. auto. }
      lights. 
      destruct lj. 
    * lights.
      exfalso.
      eapply pop_changes_stacks_identity.
      apply_any.
      exists [] ; eauto.
    * exists lj. lights. 
Qed.
  
Lemma nil_trace
        (f: nat -> (instruction * list * state))
        (c1 c2: instruction) (l1 l2: list) (s1 s2: state):
    trace f 0 (c1,l1,s1) (c2,l2,s2) ->
    List.length l1 = List.length l2.
Proof. intros; rewrite_trace; lights. Qed.

Lemma linear_traces
  (f: nat -> (instruction * list * state)) (m j:nat)
  (c1 c2: instruction * list * state):
  trace f m c1 c2 -> 0 <= j <=  m ->
  (exists g m', trace g m' (f j) c2 /\
           (forall j', j <= j' <=  m -> f j' = g (j' - j)) /\
           m' + j = m
  ).
Proof.
  lights; eexists; eexists; lights.
  - eapply subtraces_right; try apply_any; try omega.
  - simpl; apply f_equal; omega.
  - omega.
Qed.

Lemma n_step_determinism
  (f g: nat -> (instruction * list * state)) (m:nat)
  (conf conf1 conf2: instruction * list * state):
  trace f m conf conf1 ->
  trace g m conf conf2 ->
  (forall j, j <= m -> f j = g j).
Proof.
  generalize dependent conf.
  generalize dependent conf1.
  generalize dependent conf2. 
  generalize dependent f.
  generalize dependent g. 
  induction m; intros. 
  - rewrite (Nat.le_antisymm j 0); try omega;
     unfold trace in *; lights.
  - assert(j = 0 \/ j = S m \/ 0 < j < S m). { omega. }
    lights.
    + unfold trace in *; lights.
    + repeat rewrite_trace.
      eapply (IHm (fun n : nat => g (S n)) (fun n : nat => f (S n)));
        try (one_step_determinism; rewrite_any; eapply_any); omega.
    + assert(exists j', j = S j').
      { destruct j. omega. eauto. }
      lights.
      rewrite_trace. 
      rewrite_trace.
      one_step_determinism.
      rewrite_any.
      eapply (IHm (fun n : nat => g (S n)) (fun n : nat => f (S n))).
      apply_any. apply_any. omega.
Qed.

Lemma fold_trace
  (g: nat -> (instruction * list * state)) (m:nat)
  (conf conf': instruction * list * state):
  g 0 = conf -> g m = conf' -> 
  (forall idx, idx < m -> (g idx ⟹__s g (S idx))) ->
  trace g m conf conf'.
Proof. intros; unfold trace; lights. Qed.

Corollary steps_determinism
  (f g: nat -> (instruction * list * state)) (m:nat)
  (conf conf1 conf2: instruction * list * state):
  trace f m conf conf1 ->
  trace g m conf conf2 ->
  conf1 = conf2.
Proof.
  Ltac construct_trace :=
    match goal with
    | [H1: ?g 0 = ?conf,
       H2: ?g ?m = ?conf',
       H3: forall idx, idx < ?m -> ?g idx ⟹__s ?g (S idx) |- _] =>
      pose proof (fold_trace g m conf conf' H1 H2 H3);
       clear H1; clear H2; clear H3
    end.
  Ltac rewrite_back_any_conclusion :=
  match goal with
  | H: _ |- _ => rewrite <- H
  end.

  intros.
  repeat extract_trace.
  repeat rewrite_back_any_conclusion.
  repeat construct_trace.
  eapply n_step_determinism; try eapply_any; omega.
Qed.
  

Lemma same_length_traces
  (f g: nat -> (instruction * list * state)) (m n:nat)
  (conf1 conf2: instruction * list * state):
  trace f m conf1 conf2 ->
  trace g n conf1 conf2 ->
  m = n.
Proof.
  generalize dependent n.
  generalize dependent g.
  generalize dependent f. 
  generalize dependent conf1.
  induction m; intros.
  - rewrite_trace. subst. 
    destruct n.
    + reflexivity.
    + rewrite_trace.
      apply_anywhere small_trace'.
      exfalso.
      eapply no_loops.
      eapply plus_steps; clarify.
      reflexivity.
  - rewrite_trace. subst.  
    destruct n. 
    + rewrite_trace. subst.
      apply_anywhere small_trace'.
      exfalso.
      eapply no_loops.
      eapply plus_steps; clarify.
      reflexivity.
    + apply f_equal.
      rewrite_trace.
      one_step_determinism.
      rewrite_any.
      eapply_any;
      apply_any.
Qed.

Lemma between_skips (L : list) (s1 s2 : state):
  (c Skip, L, s1) ⟹__s* (c Skip, L, s2)  -> s1 = s2.
Proof.
  intros. invert_pred_unbounded (star small_step).
  - reflexivity.
  - exfalso. 
    eapply pop_changes_stacks_identity.
    eapply plus_steps; eapply_any; reflexivity.
    exists [] ; eauto.
Qed.

(* Theorem 3.5.5 *)

(*TODO: automation of arithmetic inequalities *)
Lemma determinism
  (c' : instruction) (L : list) (s s1 s2 : state) :
  (c',L,s) ⟹__s* (c Skip,L,s1) ->
  (c',L,s) ⟹__s* (c Skip,L,s2) ->
  s1 = s2.
Proof.
  Ltac steps_determinist :=
      match goal with
      | [H1: trace ?f ?m ?conf ?conf1,
         H2: trace ?g ?m ?conf ?conf2 |-
         _ ] =>
        poseNew (Mark (H1, H2) "steps_determinist"); 
        pose proof (steps_determinism f g m conf conf1 conf2 H1 H2)
      end.
  Ltac subtrace_left j f :=
    match goal with
    | [H: trace f ?m ?conf ?conf' |- _] =>
      unshelve epose proof (subtraces_left f m j conf conf' H _); try omega
    end.
  Ltac subtrace_right j f m :=
    match goal with
    | [H: trace f m ?conf ?conf' |- _] =>
      unshelve epose proof (subtraces_right f m j conf conf' H _); try omega
    end.
  
  intros.
  apply_anywhere small_trace.
  apply_anywhere small_trace.
  repeat destruct_exists.
  destruct (Nat.eqb_spec m m0).
  - repeat lights || steps_determinist.
  - edestruct not_eq. apply_any.
    + subtrace_left m f0.
      subtrace_right m f0 m0.
      steps_determinist.
      clear_marked.
      rewrite_back_any.     
      apply eq_sym.
      eapply between_skips.      
      apply_anywhere small_trace'.
      apply_any.
    + subtrace_left m0 f.
      subtrace_right m0 f m.
      steps_determinist.
      rewrite_back_any.
      eapply between_skips.
      apply_anywhere small_trace'.
      apply_any.
Qed.

Lemma final_state (d: instruction) (L: list) (s: state):
  exists s', (d,L,s) ⟹__s* (c Skip, L,s').
Proof.
  destruct d as [p | c']. 
  - lights; eexists; eapply star_step; constructor.
  - generalize dependent L.
    generalize dependent s. 
    induction c'; lights;
      eauto using star_step' with star small_step. 
    + destruct (IHc'1 s (c c'2 :: L)) as [s1 H1].
      destruct (IHc'2 s1 L) as [s2 H2]. 
      eauto using star_trans with star small_step. 
    + destruct (IHc' (update s v ⊥) (i (v, s v) :: L)).
      eauto 6 using star_trans, star_step' with star small_step. 
Qed.

Lemma cut_trace
  (conf conf1 conf2: instruction * list * state):
  conf ⟹__s* conf1 ->
  conf ⟹__s* conf2 ->
  conf1 ⟹__s* conf2 \/ conf2 ⟹__s* conf1.
Proof.
  intros.
  repeat eapply_anywhere small_trace.
  repeat destruct_exists.
  assert(m0 = m \/ m0 < m \/ m < m0). { omega. }
  repeat destruct_or.
  - subst. steps_determinist. subst. left. apply star_refl.
  - subtrace_left m0 f.
    steps_determinist. left. 
    subtrace_right m0 f m.
    rewrite_back_any.
    eapply small_trace'.
    apply_any.
  - subtrace_left m f0.
    steps_determinist. right. 
    subtrace_right m f0 m0.
    rewrite_back_any.
    eapply small_trace'.
    apply_any.
Qed.

Lemma star_one_none
  (conf1 conf2: instruction * list * state):
  conf1 ⟹__s* conf2 ->
  conf1 = conf2 \/ conf1 ⟹__s+ conf2.
Proof.   
  inversion 1. 
  - left. reflexivity.
  - right. eapply plus_steps; apply_any.
Qed.

(* Lemma 3.5.1 *)
Lemma comp_to_skip (c1 c2 : com) (L : list) (s s' : state):
  (c (c1;;c2),L,s) ⟹__s* (c Skip,L,s') ->
  (exists (s2 : state),
      (c c1, c c2 :: L, s) ⟹__s* (c Skip, c c2 :: L,s2) /\
      ((c Skip, c c2 :: L,s2) ⟹__s (c c2, L, s2)) /\
       (c c2, L, s2) ⟹__s* (c Skip,L,s')).
Proof.
  intros. 
  destruct (final_state (c c1) (c c2 :: L) s) as [s1 H1].
  destruct (final_state (c c2) (L) s1) as [s2 H2].
  exists s1. lights. constructor.
  assert((c (c1;; c2), L, s) ⟹__s* (c c2, L, s1)).
  { eapply star_step. constructor. eapply star_trans.
    apply_any. apply star_step'. constructor. } 
  destruct (cut_trace (c (c1;; c2), L, s) (c Skip, L, s')
                  (c c2, L, s1) H H0).  
  + 
    destruct (star_one_none (c Skip, L, s') (c c2, L, s1) H3).
    ++ lights.
    ++ exfalso. eapply pop_changes_stacks_identity.
       apply_any. exists [] ; eauto.
  + apply_any.
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
  invert_pred (star small_step).
  invert_pred (small_step).
  lights.
  destruct (final_state (c c') (i (x, s x) :: L) (update s x ⊥))
    as [s1 H2].
  exists s1.
  lights.
  - eapply star_step. constructor. assumption.
  - constructor.
  - edestruct cut_trace. apply H1. apply H2.
    + destruct (star_one_none (c Skip, L, s')
                              (c Skip, i (x, s x) :: L, s1) H).
      ++ lights. equal_lengths. lights. omega.
      ++ exfalso.
         eapply pop_changes_stacks_identity.
         apply_any. exists ([i (x, s x)]). auto.
    + inversion H; lights.
      ++ lights. equal_lengths. lights. omega.
      ++ inversion H0; lights. 
Qed.
 
(* Proposition 3.5.3 *)

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
  - lights.
    invert_pred (star small_step); lights.
    invert_pred (small_step); lights.
    apply_anywhere between_skips.
    rewrite_back_any.
    apply star_step'. constructor.
  - generalize dependent l.
    generalize dependent l'. 
    generalize dependent s.
    generalize dependent s'.
    induction c'; intros. 
    + apply_anywhere between_skips. rewrite_any. constructor.
    + destruct (comp_to_skip c'1 c'2 l s s' H) as [s1 [h1 [h2 h3]]].
      eapply star_step. constructor.
      eapply star_trans.
      eapply IHc'1. apply_any.
      eapply star_step. constructor.
      eapply IHc'2. apply_any.
    + destruct (let_to_skip c' l s s' t v H) as [s1 [h1 [h2 h3]]].
      eapply star_step. constructor.
      eapply star_trans.
      inversion h1. subst. inversion H0. subst.
      eapply IHc'. apply_any.
      eapply star_step. constructor.
      eapply star_step. constructor.
      inversion h3. subst. inversion H0. subst.
      apply_anywhere between_skips. lights. constructor.
    + inversion H. subst.
      inversion H0. subst.
      apply_anywhere between_skips.
      econstructor. constructor.
      rewrite_any. constructor.
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
  econstructor. constructor.
  eapply star_trans.
  eapply stack_independence.
  apply_any.
  apply star_step'. constructor.
Qed.

