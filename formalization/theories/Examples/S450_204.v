(** * S450_204 — verdict: UNSOUND_UNDER

    time_complexity_test_set: solution_id 450_204, "1421_C. Palindromifier",
    fitted O(1).

    Source, verbatim:

      print('3 L 2 R 2 R',len(input())*2-1)

    COST MODEL. [len] on an existing Python [str] is O(1) and charged nothing,
    but [input()] must read the line: one tick per character. Nothing else
    depends on the input.

    Total cost is exactly the input length, so the fitted O(1) is not a loose
    bound — it is not an upper bound at all. Likely cause: the framework's
    input expansion did not scale the single line this problem reads, so
    runtime looked flat. Still consistent with the paper's framing that labels
    are fitted performance profiles, not theorems. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From BigOBench Require Import Cost Asymptotic.

(** [input()] — consumes the line, returning its length. *)
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

Definition palindromifier (s : list nat) : M nat :=
  n <- read_line s ;; ret (2 * n - 1).

Theorem cost_palindromifier : forall s,
    cost (palindromifier s) = length s.
Proof.
  intros s. unfold palindromifier. rewrite cost_bind, cost_read_line.
  simpl. lia.
Qed.

Definition T (n : nat) : nat := cost (palindromifier (List.seq 0 n)).

Lemma T_eq : forall n, T n = n.
Proof.
  intros n. unfold T. rewrite cost_palindromifier, List.seq_length.
  reflexivity.
Qed.

(** ** The disagreement, as a theorem. *)

Theorem fitted_label_unsound : ~ BigO T (fun _ => 1).
Proof.
  apply not_BigO. intros c n0.
  exists (S (Nat.max c n0)). split.
  - pose proof (Nat.le_max_r c n0). lia.
  - rewrite T_eq. pose proof (Nat.le_max_l c n0). lia.
Qed.

(** And the true class, for the catalog. *)
Theorem true_class : Theta T (fun n => n).
Proof.
  split; [exists 1, 0 | exists 1, 0]; intros n _; rewrite T_eq; lia.
Qed.
