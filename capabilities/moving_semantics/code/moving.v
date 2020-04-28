Set Warnings "-notation-overridden,-parsing".
(*
Author: Rodrigo Raya

Following "The Semantics of Ownership and Borrowing in the Rust Programming Language" by Nienke Wessel.

Moving means move only

Can only assign variables if you do so ownership of the resource
is moved to that varaible.

Cannot borrow and nothing is immutable.
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
(* for specific induction *)
Require Import Coq.Program.Equality.
Require Import Capabilities.big_step.
Require Import Capabilities.small_step.
Require Import Capabilities.CustomTactics.

(*
We have to check that the small and big step semantics match.
In particular, there is a side condition of the assignment in 
the big step semantics that needs to be checked.

We implement this side conditions as compile cheks. 
 *)

Inductive abstract_zext :=
| non_declared
| not_assigned
| not_specified.

Notation rstate := (string -> abstract_zext).

Bind Scope move_scope with abstract_zext.
Notation "⊥__a" := non_declared : move_scope.
Notation "-__a" := not_assigned: move_scope.
Notation "*__a" := not_specified : move_scope.

Definition related_states (s: state) (r: rstate) :=
  (forall (x:string),
      ((s x) = ⊥ <-> (r x) = ⊥__a) /\
      ((s x) = -__u <-> (r x) = -__a) /\
      ((exists z, (s x) = val z) <-> (r x) = *__a)).

Reserved Notation "e '⟹__c' b" (at level 90, left associativity).

Inductive ainstruction :=
| aprog_instr : vname * abstract_zext -> ainstruction
| acommand : com -> ainstruction.

Definition alist := List.list ainstruction.

Notation "'ac' com" := (acommand com) (at level 20) : move_scope.
Notation "'ai' p_instr" := (aprog_instr p_instr) (at level 20) : move_scope.

Inductive compile_step :
  (ainstruction * alist * rstate) + bool ->
  (ainstruction * alist * rstate) + bool -> Prop :=
| CSkipNil (r: rstate) :
    inl (ac Skip, nil, r) ⟹__c inr true
| CSkipCons (p: ainstruction) (l: alist) (r: rstate):
    inl (ac Skip, p :: l, r) ⟹__c inl (p, l, r)
| CSeq (c1 c2: com) (l: alist) (r: rstate):
    inl (ac (c1;;c2),l,r) ⟹__c inl (ac c1,ac c2 :: l,r)
| CAss_legal (x: string) (e: expr) (l: alist) (r: rstate):
    ((r x) = ⊥__a) -> ((forall y, In y (vars e) -> r(y) = *__a)) ->
    inl (ac (x ;= e),l,r) ⟹__c
    inl (ac Skip,l, update_list (update r x *__a) (vars e) -__a)
| CAss_illegal (x: string) (e: expr) (l: alist) (r: rstate):
    ((r x) <> ⊥__a \/ (exists y, In y (vars e) /\ r(y) <> *__a)) ->
    inl (ac (x ;= e),l,r) ⟹__c inr false
| CLet (x: string) (t: type) (c': com) (l: alist) (r: rstate):
    inl (ac (LET x, t IN c'),l,r) ⟹__c   
    inl (ac c', (ai (x,r(x))) :: l, update r x ⊥__a)
| CBind (x: string) (v: abstract_zext) (r: rstate) (l: alist) :
    inl (ai (x,v),l,r) ⟹__c inl (ac Skip,l,update r x v)
where "e '⟹__c' b" := (compile_step e b) : move_scope.

Notation "x '⟹__c*' y" := (star compile_step x y) (at level 30) : move_scope.


Fixpoint aicommand (c': com) :=
  match c' with
  | Skip => 1
  | (c1 ;; c2) => aicommand c1 + aicommand c2 + 1
  | (x ;= e) => 2
  | (LET x , t IN c') => aicommand c' + 3 
  end. 
  
Fixpoint ailength (c': ainstruction) :=
  match c' with
  | (ai (x,v)) => 2
  | (ac c') => aicommand c'
  end. 
  
Fixpoint allength (l: alist) :=
  match l with
  | nil => 0
  | h :: tl => ailength h + allength tl
  end.

Inductive terminating {A} (r: A -> A -> Prop) (c': A): Prop :=
| TStep : (forall c1, r c' c1 -> terminating r c1) ->
          terminating r c'.

(* Theorem 3.6.1 *)

Definition measure' (c': (ainstruction * alist * rstate) + bool) :=
  match c' with
  | inr b => 0
  | inl c' => ailength (fst (fst (c'))) + allength (snd (fst (c')))
  end.
  
Lemma measure_decrease
  (c1 c2: (ainstruction * alist * rstate) + bool):
  c1 ⟹__c c2 -> measure' c1 > measure' c2.
Proof.
  intros; invert_pred_unbounded (compile_step); lights; omega.
Qed.
  
Lemma compiling_terminates
  (c': (ainstruction * alist * rstate) + bool):
  terminating compile_step c'.
Proof.
  remember (measure' c') as n.
  generalize dependent c'.
  induction (lt_wf n) as [n _ IH].
  intros.
  constructor. intros.
  assert(measure' c1 < measure' c').
  { apply measure_decrease. apply H. }
  apply (IH (measure' c1)).
  - rewrite Heqn. apply H0.
  - reflexivity.
Qed.

(*
We will prove the big step semantics to be equivalent to the small 
step semantics combined with the compile time checker
*)

(* Lemma 3.6.2 *)
Lemma final_state_1 (d : com) (L : list) (s s' : state) :
  (d,s) ⟹__b s' -> (c d,L,s) ⟹__s* (c Skip,L,s').
Proof.
  intros.
  remember (d,s) as d'.
  generalize dependent d.
  generalize dependent s.
  generalize dependent L.
  induction H as [| | l s1 d |]; intros;
    injection Heqd'; intros; subst.
  - apply star_refl.
  - eapply star_step. constructor.
    eapply star_trans.
    apply (IHbig_step1 (c c__2 :: L) s c__1).
    reflexivity.
    eapply star_step. constructor.
    eapply_any. reflexivity.
  - eapply star_step. constructor.
    eapply star_trans.
    apply (IHbig_step (i (x, s x) :: L) (update s x ⊥) d).
    reflexivity.
    eapply star_step. constructor.
    eapply star_step. constructor.
    apply star_refl.
  - eapply star_step. constructor. apply star_refl.
Qed.

Lemma related_eq (s : state) (r r' : rstate) :
  related_states s r -> related_states s r' -> r = r'.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold related_states in *.
  destruct (H x) as [eq1 [eq2 eq3]].
  destruct (H0 x) as [eq1' [eq2' eq3']]. 
  destruct (r' x).
  rewrite eq1 in eq1'. rewrite eq1'. reflexivity.
  rewrite eq2 in eq2'. rewrite eq2'. reflexivity.
  rewrite eq3 in eq3'. rewrite eq3'. reflexivity.
Qed.

Definition abstract_equivalent (s: state): rstate :=
  (fun (x:string) =>
     (match (s x) with
     | ⊥ => ⊥__a
     | -__u => -__a
     | z => *__a
      end)).

Lemma equivalent_related (s:state):
  related_states s (abstract_equivalent s).
Proof.
  unfold related_states; unfold abstract_equivalent.
  repeat (try(split)); intros;
    try(rewrite H; reflexivity);
    try(destruct (s x); try (discriminate H); try(reflexivity));
    try(destruct H; inversion H);
    try(eexists; auto).
Qed.

Lemma update_related (s s': state) (r r': rstate) (x: string):
  related_states s r ->
  related_states s' r' ->
  related_states (update s x (s' x)) (update r x (r' x)).
Proof.
  lights;
  unfold related_states in *;
  intros;
  repeat split;
    intros;
    repeat destruct_updates;
    unfold update in *; 
    rewrite_any;
    repeat apply_any.
Qed.

Lemma update_related_list
  (L: List.list string) (s: state) (r: rstate):
  related_states s r ->
  related_states (update_list s L -__u) (update_list r L -__a).
Proof.
  generalize dependent s.
  generalize dependent r. 
  induction L; intros. 
  - simpl. apply_any.
  - simpl.
    assert(related_states (update s a -__u) (update r a -__a)).
    { apply (update_related s (fun x => -__u) r (fun x => -__a) a).
      apply H. unfold related_states. intros.
      repeat(split); intros; 
        try(discriminate H0); try(reflexivity).
      destruct H0. discriminate H0. }
    apply IHL. apply H0.
Qed.

Lemma unique_repr (s: state) (r r': rstate):
  related_states s r -> related_states s r' -> r = r'. 
Proof. 
  unfold related_states. intros. 
  apply functional_extensionality.
  intros. destruct (r x) eqn: eq;
  apply (H x) in eq; apply (H0 x) in eq; auto using eq.
Qed.
  
Lemma update_abstract (s s': state) (r: rstate) (x: string):
  related_states s r ->
  update (abstract_equivalent s') x (r x) =
  abstract_equivalent (update s' x (s x)).
Proof.
  intros.
  assert(related_states (update s' x (s x))
                        (update (abstract_equivalent s') x (r x))).
  { apply update_related. apply equivalent_related. apply H. }
  assert(related_states (update s' x (s x))
                        ( abstract_equivalent (update s' x (s x)))).
  { eapply equivalent_related.  }
  eapply unique_repr. apply H0. apply H1. 
Qed.

Lemma expr_evaluation
  (s: state) (e: expr) (y: string) (z: BinNums.Z):
  In y (vars e) -> aval s e = val z -> (exists z', s y = val z'). 
Proof.
  intros.
  generalize dependent z. 
  induction e; intros; simpl in H; simpl in H.
  - destruct H eqn: eq.
    + eexists. rewrite e in H0. apply H0.
    + exfalso. apply f.
  - exfalso. apply H.
  - apply in_app_or in H. destruct H.
    + destruct (aval s e1) eqn: eq1; destruct (aval s e2) eqn: eq2;
        try(simpl in H0) ; try (rewrite eq1 in H0) ;
          try (rewrite eq2 in H0) ; try(discriminate H0).
      apply (IHe1 H z0). reflexivity.
    + destruct (aval s e1) eqn: eq1; destruct (aval s e2) eqn: eq2;
        try(simpl in H0) ; try (rewrite eq1 in H0) ;
          try (rewrite eq2 in H0) ; try(discriminate H0).
      apply (IHe2 H z1). reflexivity. 
 Qed.

  
Lemma final_state_2
  (d : com) (L : alist) (s s': state) (r r' : rstate) :
  (d,s) ⟹__b s' ->
  related_states s r ->
  related_states s' r' ->
  inl (ac Skip, L, r') ⟹__c* inr true ->
  inl (ac d, L, r) ⟹__c* inr true .
Proof.
  intros.
  remember (d,s) as d'.
  generalize dependent r.
  generalize dependent s. 
  generalize dependent d.
  generalize dependent r'.
  generalize dependent L.
  induction H;
    intros; injection Heqd'; intros; subst.
  - rewrite <- (related_eq s0 r r') in H2.
    apply H2. apply H0. apply H1. 
  - eapply star_step. apply CSeq.
    eapply (IHbig_step1 (ac c__2 :: L) (abstract_equivalent s__2)
                        (equivalent_related s__2)).
    eapply star_step. apply CSkipCons.
    eapply IHbig_step2. apply H1. apply H2. eauto.
    apply (equivalent_related s__2). eauto. apply H3.
  - eapply star_step. apply CLet.
    eapply IHbig_step. apply (equivalent_related s'). 
    eapply star_step. apply CSkipCons.
    eapply star_step. apply CBind.
    rewrite (update_abstract s0 s' r x H0).
    rewrite <- ((unique_repr (update s' x (s0 x)) r'
           (abstract_equivalent (update s' x (s0 x)))) H1
           (equivalent_related (update s' x (s0 x)))).
    apply H2. eauto.
    apply (update_related s0 (fun e => ⊥) r (fun e => ⊥__a)).
    apply H0. unfold related_states. intros.
    (* add as constant lemma *)
    split. split. reflexivity. reflexivity.
    split. split. discriminate. discriminate.
    split. intros. destruct H3. discriminate H3.
           intros. discriminate H3.
  - eapply star_step. apply CAss_legal.
    + simpl in H. apply H4. apply H.
    + intros. destruct (aval s0 e) eqn: eq.
      ++ contradiction H1. reflexivity.
      ++ contradiction H0. reflexivity.
      ++ assert(exists z', s0 y = val z').
        { eapply expr_evaluation. apply H5. apply eq. }
        apply H4. apply H6.
    + intros. destruct (aval s0 e) eqn: eq.
      ++ contradiction H1. reflexivity.
      ++ contradiction H0. reflexivity.
      ++ assert(related_states
                 (update_list (update s0 x (val z)) (vars e) -__u)
                 (update_list (update r x *__a) (vars e) -__a)).
        { apply update_related_list.
          apply (update_related s0 (fun n => val z) r (fun n => *__a)).
          apply H4. unfold related_states. intros.
          repeat(split); intros;
            try(discriminate H5); try(eexists; eauto).
        }
        assert(r' = update_list (update r x *__a) (vars e) -__a).
        { eapply unique_repr. apply H2. apply H5. }
        rewrite <- H6. apply H3.     
Qed.

(* Todo: rewrite abstract_equivalent above with this definition *)
Definition abstract_value (z: zext): abstract_zext :=
  match z with
  | ⊥ => ⊥__a
  | -__u => -__a
  | z => *__a
  end.

Fixpoint abstract_instruction (i': instruction): ainstruction :=
  match i' with
  | i (x, v) => ai (x, abstract_value v) 
  | c v => ac v
  end.

Definition abstract_list (l: list): alist  :=
  map abstract_instruction l.

Lemma expr_eval (e: expr) (s: state) (r: rstate):
  (forall y : string, In y (vars e) -> r y = *__a) ->
  related_states s r ->
  (exists z, aval s e = val z).
Proof.
  induction e; intros. 
  - simpl. apply (H0 v). apply (H v). simpl. auto.
  - simpl. eexists. auto.
  - assert(exists z : BinNums.Z, aval s e1 = val z).
    { eapply IHe1. intros. apply H. simpl. 
      apply in_or_app. left. apply H1. apply H0. }
    assert(exists z : BinNums.Z, aval s e2 = val z).
    { eapply IHe2. intros. apply H. simpl. 
      apply in_or_app. right. apply H2. apply H0. }
    destruct H1. destruct H2. eexists. simpl.
    rewrite H1. rewrite H2. auto.
Qed.

Lemma related_abstract_values (s: state) (r: rstate) (x: string):
  related_states s r ->
  r x = abstract_value (s x).
Proof.
  intros. unfold related_states in H.
  destruct (s x) eqn: eq; apply (H x);
    try(apply eq) ; try(eexists; apply eq).  
Qed.
  
(* Lemma 3.6.3 *)
Lemma compile_one_step
  (d d': instruction) (l l': list) (s s': state) (r: rstate):
  ((d, l, s) ⟹__s (d', l', s')) ->
  related_states s r ->
  inl (abstract_instruction d, abstract_list l, r) ⟹__c* inr true ->
  (exists (r': rstate),
      related_states s' r' /\
      (inl (abstract_instruction d, abstract_list l, r) ⟹__c
      inl (abstract_instruction d', abstract_list l', r'))).
Proof.
  intros.
  inversion H; subst; simpl. 
  - inversion H1. subst. inversion H2. subst.
    eexists. split. apply H0. apply H2.
  - inversion H1. subst. inversion H2. subst.
    eexists. split. apply H0. apply H2.
  - inversion H1. subst. inversion H2. subst.
    eexists. split.
    + apply update_related_list.
      apply (update_related s (fun n => aval s e) r (fun n => *__a)).
      apply H0.
      assert(exists z, aval s e = val z).
      { eapply expr_eval. apply H10. apply H0. }
      destruct H4. rewrite H4.
      unfold related_states. intros.
      repeat(split); intros; try(discriminate H5).
      eexists. auto.
    + apply H2.
    + subst. inversion H3. inversion H4.
  - inversion H1. subst. inversion H2. subst.
    eexists. split.
    + apply (update_related s (fun n => ⊥) r (fun n => ⊥__a)).
      apply H0. unfold related_states. intros.
      repeat(split); intros; try(discriminate H4);
        try(destruct H4; discriminate H4; auto).
    + assert(r x = abstract_value (s x)). 
      { apply related_abstract_values. apply H0. }
      rewrite <- H4. apply H2.
  - inversion H1. subst. inversion H2. subst.
    simpl in H2. eexists. split.
    apply (update_related s (fun n => v) r (fun n => abstract_value v)).
    apply H0. unfold related_states. intros.
    repeat(split); intros; destruct v;
      try(discriminate H4); try(reflexivity);
        try(destruct H4; discriminate H4).
    eexists. eauto. apply H2.
Qed.

Lemma compile_deterministic_one_step
  (conf conf1 conf2: ainstruction * alist * rstate + bool):
  (conf ⟹__c conf1) -> (conf ⟹__c conf2) -> conf1 = conf2.
Proof.
  intros.
  inversion H; subst; inversion H0; subst; try(reflexivity).
  - exfalso. destruct H8.
    ++ contradiction.
    ++ destruct H3 as [y [H3 H3']]. apply H3'.
      apply (H2 y). apply H3.
  -  exfalso. destruct H1.
    ++ contradiction.
    ++ destruct H1 as [y [H1 H1']]. apply H1'.
      apply (H8 y). apply H1.
Qed.

Lemma compile_deterministic_truth
  (conf conf': ainstruction * alist * rstate + bool):
  (conf ⟹__c* conf') -> (conf ⟹__c* inr true) -> conf' ⟹__c* inr true.
Proof.
  intros.
  induction H.
  - apply H0.
  - apply IHstar.
    inversion H0; subst.
    + inversion H.
    + assert(y = y0).
      { eapply compile_deterministic_one_step. apply H. apply H2. }
      rewrite <- H4 in H3. apply H3.
Qed.

(* Lemma 3.6.4 *)
Lemma compile_steps
  (d d': instruction) (l l': list) (s s': state) (r: rstate):
  ((d, l, s) ⟹__s* (d', l', s')) ->
  related_states s r ->
  inl (abstract_instruction d, abstract_list l, r) ⟹__c* inr true ->
  (exists (r': rstate),
      related_states s' r' /\
      (inl (abstract_instruction d, abstract_list l, r) ⟹__c*
      inl (abstract_instruction d', abstract_list l', r'))).
Proof.
  intros H.
  remember (d, l, s) as conf1.
  remember (d',l', s') as conf2.
  generalize dependent d.
  generalize dependent d'.
  generalize dependent l.
  generalize dependent l'.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent r. 
  dependent induction H. 
  - lights. exists r. lights. constructor.
  - intros. subst. destruct y as [[d1 l1] s1].
    assert(exists r' : rstate, related_states s1 r' /\
      (inl (abstract_instruction d, abstract_list l, r)
    ⟹__c inl (abstract_instruction d1, abstract_list l1,
            r'))).
    { eapply compile_one_step. apply H. apply H1. apply H2. }
    destruct H3 as [r1 [H3 H3']].
    assert( exists r' : rstate,
         related_states s' r' /\
         inl (abstract_instruction d1, abstract_list l1, r1)
       ⟹__c* inl (abstract_instruction d', abstract_list l', r')).
    { eapply IHstar. reflexivity. eauto. apply H3.
      inversion H2. 
      + subst.
        assert(y = inl (abstract_instruction d1,
                        abstract_list l1, r1)).
        { eapply compile_deterministic_one_step.
          apply H4. apply H3'. }
        rewrite H6 in H5. apply H5.
    }
    destruct H4 as [r2 [H4 H4']].
    eexists. split. apply H4. eapply star_step.
    apply H3'. apply H4'.
Qed.

(* Lemma 3.6.5 *)
Lemma small_to_big
  (d: com) (l: list) (s s': state) (r: rstate):
  ((c d, l, s) ⟹__s* (c Skip, l, s')) ->
  related_states s r ->
  inl (abstract_instruction (c d), abstract_list l, r)
      ⟹__c* inr true ->
  (d, s) ⟹__b s'.
Proof.
  generalize dependent l.
  generalize dependent s'.
  generalize dependent s.
  generalize dependent r. 
  induction d; intros. 
  - lights. apply_anywhere between_skips.
    rewrite_any. constructor.
  - destruct (comp_to_skip d1 d2 l s s' H) as [s2 [H4 [H4' h4']]].
    econstructor. eapply IHd1. 
    inversion H. subst. inversion H2. subst.    
    eapply_any. eapply_any.
    inversion H1. subst. inversion H2. subst.
    apply H3.
    eapply IHd2. apply h4'.
    apply (equivalent_related s2).
    inversion H1. subst. inversion H2. subst.
    eapply compile_deterministic_truth.
    destruct (compile_steps (c d1) (c Skip) (c d2 :: l) (c d2 :: l)
                            s s2 r H4 H0 H3) as [r5 [H5 H5']].
    assert(r5 = abstract_equivalent s2).
    { eapply unique_repr. apply H5. apply equivalent_related. }
    rewrite H6 in H5'.
    assert(inl (abstract_instruction (c d1),
                abstract_list (c d2 :: l), r) ⟹__c* inl
          (abstract_instruction (c d2), abstract_list l,
          abstract_equivalent s2)). 
    { apply plus_star. eapply plus_right. apply H5'.
      apply CSkipCons. }
    apply H7. apply H3.
  - inversion H. subst. inversion H2. subst.
    inversion H1. subst. inversion H4. subst.
    destruct (let_to_skip d l s s' t v H) as [s2 [eq1 [eq2 eq3]]].
    inversion eq3. subst. inversion H6. subst.
    assert(update s2 v (s v) = s').
    { eapply between_skips. apply H7. }
    rewrite <- H8.
    apply BLet. eapply IHd.
    inversion eq1. subst. inversion H9. subst.
    apply H10.
    apply (update_related s (fun n => ⊥) r (fun n => ⊥__a)).
    apply H0. unfold related_states.
    repeat(split); intros; try(discriminate H9); try(reflexivity);
      try(destruct H9; discriminate H9).
    assert(r v = abstract_value (s v)).
    { apply related_abstract_values. apply H0. }
    simpl. rewrite <- H9. apply H5. 
  - lights.
    invert_pred (star small_step).
    lights.
    invert_pred (small_step).
    lights.
    apply_anywhere between_skips.
    rewrite_back_any.
    constructor.
    + lights.
      invert_pred (star compile_step). lights.
      invert_pred_unbounded (compile_step). lights.
      apply_any. apply_any.
      apply_any. lights.
      ++ exfalso. invert_pred (star compile_step).
         lights. invert_pred (compile_step).
      ++ exfalso. invert_pred (star compile_step).
         lights. invert_pred (compile_step).
    + lights.
      invert_pred (star compile_step). lights.
      invert_pred_unbounded (compile_step). lights.
      ++ assert(exists z : BinNums.Z, aval s e = val z).
         { eapply expr_eval; repeat apply_any. }
         destruct_exists. lights.         
      ++ subst.
         invert_pred (star compile_step). subst.
         invert_pred_unbounded (compile_step). 
    + lights.
      invert_pred (star compile_step). lights.
      invert_pred_unbounded (compile_step). lights.
      ++ assert(exists z : BinNums.Z, aval s e = val z).
         { eapply expr_eval; repeat apply_any. }
         destruct_exists. lights.
      ++ subst.
         invert_pred (star compile_step). subst.
         invert_pred_unbounded (compile_step). 
Qed.

(* Lemma 3.6.6 *)
Lemma small_big
  (d: com) (s s': state) (r: rstate):
  (d, s) ⟹__b s' <->
  (exists l, ((c d, l, s) ⟹__s* (c Skip, l, s')) /\
  related_states s (abstract_equivalent s) /\
  inl (abstract_instruction (c d), abstract_list l,
       (abstract_equivalent s))
      ⟹__c* inr true).
Proof.
  split; intros.
  - exists nil. split.
    + apply final_state_1. apply H.
    + split. apply (equivalent_related s).
      eapply final_state_2. apply H. apply (equivalent_related s).
      apply (equivalent_related s').
      eapply star_step. apply CSkipNil. apply star_refl.
  - destruct H as [l [eq1 [eq2 eq3]]].
    eapply small_to_big. apply eq1. apply (equivalent_related s).
    apply eq3.
Qed.

(*
Preservation

If the compile time checker says a program is okay and 
you take a step in the semantics, the checker will say 
it is still okay.
*)

(* Lemma 3.6.7 *)
Lemma preservation
  (d d': instruction) (s s': state) (r: rstate) (l l': list):
  inl (abstract_instruction d, abstract_list l, r) ⟹__c* inr true ->
  ((d, l, s) ⟹__s (d', l', s')) ->
  related_states s r ->
  (exists r', related_states s' r' /\
         inl (abstract_instruction d', abstract_list l', r') ⟹__c*
         inr true). 
Proof.
  intros.
  inversion H0; subst.
  - inversion H; subst. inversion H2; subst.
    eexists. split. apply H1. apply H3. 
  - inversion H; subst. inversion H2; subst.
    eexists. split. apply H1. apply H3.
  - inversion H; subst. inversion H2; subst.
    eexists. split.
    + apply update_related_list.
      assert(exists z, aval s e = val z).
      { eapply expr_eval. apply H10. apply H1. }
      apply (update_related s (fun n => aval s e) r (fun n => *__a)).
      apply H1. destruct H4 as [z H4]. rewrite H4. 
      repeat(split); intros; try(discriminate H5).
      eexists. eauto.
    + apply H3.
    + inversion H3. inversion H4.
  - inversion H; subst. inversion H2; subst.
    eexists. split. 
    + apply (update_related s (fun n => ⊥) r (fun n => ⊥__a)).
      apply H1. 
      repeat(split); intros; try(destruct H4; discriminate H4);
        try(discriminate H4).
    + simpl.
      assert(r x = abstract_value (s x)).
      { apply related_abstract_values. apply H1. }
      rewrite <- H4. apply H3. 
  - inversion H; subst. inversion H2; subst.
    eexists. split.
    + apply (update_related s (fun n => v) r
            (fun n => abstract_value v)).
      apply H1.
      repeat(split); intros; destruct v;
        try (discriminate H4); try(eauto);
          try(destruct H4; discriminate H4).
    + apply H3. 
Qed.

(*
Progress

If the program passes through the compile time checker, 
we can always do a step in the semantics.
 *)

Lemma invert_skip (d: instruction):
  ac Skip = abstract_instruction d -> d = c Skip. 
Proof.
  destruct d; intros.
  - destruct p. simpl in H. discriminate H.
  - simpl in H. injection H. intros. rewrite H0. reflexivity.
Qed.

Lemma invert_nil (l: list):
  nil = abstract_list l -> l = nil. 
Proof.
  destruct l; intros.
  - reflexivity.
  - simpl in H. discriminate H.
Qed.

Lemma invert_cons (l: list) (p: ainstruction) (l0: alist):
  p :: l0 = abstract_list l ->
  (exists p' l0', l = p' :: l0'). 
Proof.
  intros.
  destruct l as [|i' l']. 
  - simpl in H. discriminate H.
  - simpl in H. exists i'. exists l'. reflexivity.
Qed.

(* Todo: remove skip_nil *)
Lemma invert_command (c': com) (d: instruction):
  ac c' = abstract_instruction d -> d = c c'. 
Proof.
  destruct d; intros.
  - simpl in H. destruct p. discriminate H. 
  - destruct c'; intros; simpl in H;
      try(injection H; intros; rewrite H0; reflexivity).
Qed.

Lemma invert_binding
  (x: vname) (av: abstract_zext) (d: instruction):
  ai (x, av) = abstract_instruction d ->
  (exists cv, d = i (x, cv)). 
Proof.
  destruct d; intros.
  - destruct p. simpl in H. injection H. intros.
    exists z. rewrite H1. reflexivity.
  - simpl in H. discriminate H.
Qed.

(* Lemma 3.6.9 *)
Lemma progresss
  (d: instruction) (r: rstate) (l: list):
  inl (abstract_instruction d, abstract_list l, r) ⟹__c* inr true ->
  (d = c Skip /\ l = nil) \/
  (forall s, related_states s r ->
        (exists d' l' s', (d, l, s) ⟹__s (d', l', s'))).
Proof.
  intros.
  inversion H; subst. inversion H0; subst.
  - left. split.
    apply invert_skip. apply H3.
    apply invert_nil. apply H4.
  - right. intros.
    apply invert_cons in H4.
    destruct H4 as [p' [l0' H4]].
    exists p'. exists l0'. exists s.
    apply invert_skip in H3. rewrite H3. rewrite H4.
    apply SLoad.
  - right. intros. 
    apply invert_command in H3. rewrite H3.
    repeat(eexists). apply SComp.
  - right. intros.
    apply invert_command in H2. rewrite H2.
    repeat(eexists). apply SAss.
  - right. intros.
    apply invert_command in H2. rewrite H2.
    repeat(eexists). apply SAss.
  - right. intros.
    apply invert_command in H3. rewrite H3.
    repeat(eexists). apply SLet.
  - right. intros.
    apply invert_binding in H3. destruct H3. rewrite H3.
    repeat(eexists). apply SSet.
Qed.
