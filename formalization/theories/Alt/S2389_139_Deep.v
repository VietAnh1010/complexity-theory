(** * Alt/S2389_139_Deep.v — 2389_139 again, in the deep embedding.

    The same solution as [Examples/S2389_139.v], modelled independently: there
    the cost is [tick]s in a Gallina function, here it is read off a
    derivation. Both reach n^2, so the verdict does not depend on the modelling
    style.

    Neither validates the cost model itself. Both encode the same judgement,
    that [str.count] scans the whole string. If that reading of Python is
    wrong, both are wrong together. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From BigOBench Require Import Asymptotic.
From BigOBench.Alt Require Import Deep.

Definition vs : nat := 0.
Definition vch : nat := 1.
Definition vi : nat := 2.

(** for i in s: if s.count(i) % 2 == 1: ch = 1 *)
Definition body : stmt :=
  SIf (EEq (EMod (ECount (EVar vs) (EVar vi)) (ENat 2)) (ENat 1))
      (SAssign vch (ENat 1)) SSkip.

Definition prog : stmt :=
  SSeq (SAssign vch (ENat 0)) (SForEach vi (EVar vs) body).

Definition init (str : list nat) : state := [(vs, VS str)].

Lemma guard_cost : forall st str v c,
    lookup st vs = VS str ->
    evalE st (EEq (EMod (ECount (EVar vs) (EVar vi)) (ENat 2)) (ENat 1)) v c ->
    c = length str.
Proof. intros. peelE. reconcile. lia. Qed.

(** The body costs one scan and leaves [s] unchanged. The second conjunct is
    needed: without it a later iteration could be scanning something
    shorter. *)
Lemma body_cost : forall st v st' c str,
    lookup st vs = VS str ->
    evalS (update vi (VN v) st) body st' c ->
    c = length str /\ lookup st' vs = VS str.
Proof.
  intros st v st' c str Hs Hev.
  assert (Hs' : lookup (update vi (VN v) st) vs = VS str)
    by (rewrite lookup_update_neq by (unfold vi, vs; lia); exact Hs).
  inversion Hev; subst;
    match goal with H : evalE _ (EEq _ _) _ _ |- _ =>
      pose proof (guard_cost _ _ _ _ Hs' H) end;
    [ inv_stmt (SAssign vch (ENat 1)) | inv_stmt SSkip ]; peelE;
    (split; [lia | idtac]).
  - rewrite lookup_update_neq by (unfold vch, vs; lia). exact Hs'.
  - exact Hs'.
Qed.

Lemma loop_cost : forall vals st st' c str,
    lookup st vs = VS str ->
    evalS st (SForVals vi vals body) st' c ->
    c = length vals * length str.
Proof.
  induction vals as [| v rest IH]; intros st st' c str Hs Hev;
    inversion Hev; subst; [reflexivity |].
  match goal with
  | Hb : evalS (update vi (VN v) st) body ?s1 _,
    Hr : evalS ?s1 (SForVals vi rest body) st' _ |- _ =>
      destruct (body_cost _ _ _ _ _ Hs Hb) as [-> Hs1];
      rewrite (IH _ _ _ _ Hs1 Hr)
  end.
  simpl. lia.
Qed.

(** Quantified over EVERY derivation, so nothing cheaper can hide. That is why
    no determinism lemma is needed. *)
Theorem prog_cost : forall str st' c,
    evalS (init str) prog st' c -> c = length str * length str.
Proof.
  intros str st' c Hev.
  assert (Hs : lookup (update vch (VN 0) (init str)) vs = VS str) by reflexivity.
  inversion Hev; subst.
  inv_stmt (SAssign vch (ENat 0)). peelE.
  inv_stmt (SForEach vi (EVar vs) body). peelE. reconcile.
  match goal with H : evalS _ (SForVals _ _ _) _ _ |- _ =>
    rewrite (loop_cost _ _ _ _ _ Hs H) end.
  lia.
Qed.

(** ** Non-vacuity.

    [prog_cost] is conditional on a derivation existing, so it would hold
    vacuously if the semantics admitted none. On "aa" (here [[7;7]]) each of
    the two iterations scans the 2-character string once, so the cost is
    4 = 2 * 2. *)

Ltac scan_iter :=
  eapply ES_ForCons;
  [ eapply ES_IfFalse;
    [ eapply EV_Eq;
      [ eapply EV_Mod;
        [ eapply EV_Count; (eapply EV_Var'; reflexivity) | apply EV_Nat ]
      | apply EV_Nat ]
    | cbn; discriminate
    | apply ES_Skip ]
  | ].

Example run_aa : exists st' c, evalS (init [7; 7]) prog st' c /\ c = 4.
Proof.
  unfold prog, init, body, vs, vch, vi.
  eexists; eexists; split.
  - eapply ES_Seq; [eapply ES_Assign, EV_Nat |].
    eapply ES_ForEach; [eapply EV_Var'; reflexivity |].
    scan_iter. scan_iter. apply ES_ForNil.
  - reflexivity.
Qed.

(** ** The verdict, reproduced independently of the monad. *)
Definition Tdeep (n : nat) : nat := n * n.

Theorem deep_label_is_tight : Theta Tdeep (fun n => n * n).
Proof. unfold Tdeep. split; exists 1, 0; intros; lia. Qed.

Theorem Tdeep_is_the_derivation_cost : forall n st' c,
    evalS (init (List.seq 0 n)) prog st' c -> c = Tdeep n.
Proof.
  intros n st' c H. unfold Tdeep.
  rewrite (prog_cost _ _ _ H), List.length_seq. reflexivity.
Qed.
