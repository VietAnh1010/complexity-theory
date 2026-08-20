(** * Alt/S5_100_Deep.v — 5_100 in the deep embedding, using [SWhile].

      n=int(input())
      k=1
      while(n>k):
         n-=k
         k+=1
      print(n)

    [SWhile] exists for this case: an unbounded loop, which the monad version
    can only express with fuel. What changes and what does not:

    - No fuel, and so no [run_finishes]. [S5_100.v] needs an adequacy lemma
      because a fuel-truncated loop satisfies any upper bound for free; here a
      truncated run is not a derivation.
    - The theorem is CONDITIONAL on a derivation existing. That is the price of
      dropping totality: [prog_sqrt] bounds every terminating run by about
      sqrt(2n) and says nothing about non-terminating ones. Termination of this
      program is a separate fact, not proved here.

    Cost model: one step per iteration ([ES_WhileTrue]), arithmetic free —
    the same model [S5_100.v] applies by hand. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From BigOBench.Alt Require Import Deep.

Definition vn : nat := 0.
Definition vk : nat := 1.

Definition guard : expr := ELt (EVar vk) (EVar vn).

Definition wbody : stmt :=
  SSeq (SAssign vn (ESub (EVar vn) (EVar vk)))
       (SAssign vk (EAdd (EVar vk) (ENat 1))).

Definition prog : stmt := SWhile guard wbody.

Definition init (n : nat) : state := [(vn, VN n); (vk, VN 1)].

(** One iteration: free, and it takes [(n,k)] to [(n-k, k+1)]. *)
Lemma body_step : forall st st' c n k,
    lookup st vn = VN n -> lookup st vk = VN k ->
    evalS st wbody st' c ->
    c = 0 /\ lookup st' vn = VN (n - k) /\ lookup st' vk = VN (k + 1).
Proof.
  intros st st' c n k Hn Hk H.
  inversion H; subst.
  repeat match goal with
         | H : evalS _ (SAssign _ _) _ _ |- _ => inversion H; subst; clear H
         end; peelE; reconcileN.
  repeat split; try lia;
    repeat rewrite lookup_update_neq by (unfold vn, vk; lia);
    rewrite lookup_update_eq; reflexivity.
Qed.

(** The guard is true exactly when [k < n]. *)
Lemma guard_true : forall st n k c,
    lookup st vn = VN n -> lookup st vk = VN k ->
    evalE st guard (VN 1) c -> c = 0 /\ k < n.
Proof.
  intros st n k c Hn Hk H. unfold guard in H. peelE. reconcileN.
  split; [lia |].
  match goal with H : (if ?x <? ?y then 1 else 0) = 1 |- _ =>
    destruct (Nat.ltb_spec x y); [assumption | discriminate] end.
Qed.

(** Same invariant as [S5_100.loop_bound], stated without subtraction:
    after [c] iterations from [(n,k)], [2*k*c + c*c <= 2*n + c]. *)
Lemma while_bound : forall st st' c,
    evalS st prog st' c ->
    forall n k, lookup st vn = VN n -> lookup st vk = VN k ->
                2 * k * c + c * c <= 2 * n + c.
Proof.
  intros st st' c H. unfold prog in H.
  remember (SWhile guard wbody) as p eqn:Hp.
  induction H; try discriminate; inversion Hp; subst; intros n k Hn Hk.
  - (* iteration *)
    destruct (guard_true _ _ _ _ Hn Hk H) as [-> Hlt].
    destruct (body_step _ _ _ _ _ Hn Hk H0) as [-> [Hn1 Hk1]].
    specialize (IHevalS2 eq_refl _ _ Hn1 Hk1).
    assert (Hd : exists d, n = k + d /\ 1 <= d) by (exists (n - k); lia).
    destruct Hd as [d [-> _]].
    replace (k + d - k) with d in IHevalS2 by lia.
    replace (k + 1) with (S k) in IHevalS2 by lia.
    nia.
  - (* guard false: zero iterations *)
    unfold guard in H. peelE. lia.
Qed.

(** ** Every terminating run costs at most about sqrt(2n). *)
Theorem prog_sqrt : forall n st' c,
    evalS (init n) prog st' c -> c * (c + 1) <= 2 * n.
Proof.
  intros n st' c H.
  pose proof (while_bound _ _ _ H n 1 eq_refl eq_refl). nia.
Qed.

(** ** Non-vacuity.

    [prog_sqrt] is conditional on a derivation existing, so it would hold
    vacuously if the semantics admitted none. At n = 4 the loop runs twice
    (4,1) -> (3,2) -> (1,3), where 3 < 1 fails. *)
(** The guard's operands must be given explicitly: until [a] and [b] are
    known, the unifier cannot reduce [if a <? b then 1 else 0] to [1]. *)
Ltac iter a b :=
  eapply ES_WhileTrue;
  [ eapply (EV_Lt _ _ _ a b); (eapply EV_Var'; reflexivity)
  | eapply ES_Seq;
    [ eapply ES_Assign; eapply EV_Sub; (eapply EV_Var'; reflexivity)
    | eapply ES_Assign; eapply EV_Add; [(eapply EV_Var'; reflexivity) | apply EV_Nat] ]
  | ].

Example run_4 : exists st' c, evalS (init 4) prog st' c /\ c = 2.
Proof.
  unfold prog, init, guard, wbody, vn, vk.
  eexists; eexists; split.
  - iter 1 4. iter 2 3.
    eapply ES_WhileFalse;
      [eapply (EV_Lt _ _ _ 3 1); (eapply EV_Var'; reflexivity) | cbn; discriminate].
  - reflexivity.
Qed.

(** Reproduces [S5_100.iters_sqrt] with no fuel, no adequacy lemma, and no
    shared definitions. Only the BOUND is shown to coincide; exact equality of
    the two costs is not proved and the verdict does not need it. *)
