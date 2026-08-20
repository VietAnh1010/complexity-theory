(** * S450_204 — not in the catalog.

    time_complexity_test_set: solution_id 450_204, "1421_C. Palindromifier",
    fitted O(1).

    Source, verbatim:

      print('3 L 2 R 2 R',len(input())*2-1)

    COST MODEL. Per [Cost.v]: [input()] and [print] are free, and [len] on a
    built Python [str] is O(1) and charged nothing. Nothing else depends on the
    input, so the cost is constant and the fitted O(1) is correct.

    The second half of the file records what the cost is with the read charged
    — a fact about reading stdin, not about this solution. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From BigOBench Require Import Cost Asymptotic.

(** ** Constant cost, and the label is correct. *)

Definition palindromifier (s : list nat) : M nat :=
  ret (2 * length s - 1).

Theorem cost_palindromifier : forall s, cost (palindromifier s) = 0.
Proof. reflexivity. Qed.

Definition T (n : nat) : nat := cost (palindromifier (List.seq 0 n)).

Lemma T_eq : forall n, T n = 0.
Proof. reflexivity. Qed.

Theorem label_sound : BigO T (fun _ => 1).
Proof. exists 1, 0. intros n _. rewrite T_eq. lia. Qed.

(** ** With the read charged.

    One tick per character makes the cost the input length and refutes O(1).
    True, and true of every program that reads its input. *)

Fixpoint read_line (s : list nat) : M nat :=
  match s with
  | [] => ret 0
  | _ :: r => tick (n <- read_line r ;; ret (S n))
  end.

Lemma cost_read_line : forall s, cost (read_line s) = length s.
Proof.
  intros s. induction s as [| x r IH]; [reflexivity|].
  simpl read_line. rewrite cost_tick, cost_bind, IH. simpl. lia.
Qed.

Definition palindromifier_io (s : list nat) : M nat :=
  n <- read_line s ;; ret (2 * n - 1).

Definition T_io (n : nat) : nat := cost (palindromifier_io (List.seq 0 n)).

Lemma T_io_eq : forall n, T_io n = n.
Proof.
  intros n. unfold T_io, palindromifier_io.
  rewrite cost_bind, cost_read_line, List.length_seq. simpl. lia.
Qed.

Theorem label_unsound_if_io_charged : ~ BigO T_io (fun _ => 1).
Proof.
  apply not_BigO. intros c n0.
  exists (S (Nat.max c n0)). split.
  - pose proof (Nat.le_max_r c n0). lia.
  - rewrite T_io_eq. pose proof (Nat.le_max_l c n0). lia.
Qed.

Theorem true_class_if_io_charged : Theta T_io (fun n => n).
Proof.
  split; [exists 1, 0 | exists 1, 0]; intros n _; rewrite T_io_eq; lia.
Qed.
