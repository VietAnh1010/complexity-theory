(** * S2389_139 — verdict: TIGHT (the fitted label is right)

    BigO(Bench) time_complexity_test_set
      solution_id   2389_139
      problem_name  p04012 AtCoder Beginner Contest 044 - Beautiful Strings
      fitted label  O(n**2)

    Source solution, verbatim:

      s=input()
      ch=0
      for i in s:
        if s.count(i)%2 ==1:
          ch=1
      print("YNeos"[ch::2])

    COST MODEL. One tick per character comparison performed by [str.count],
    which scans the whole string; the outer [for] is a single pass and is
    charged nothing beyond the counts it triggers. Characters are modelled as
    [nat] with decidable equality, strings as [list nat]. Input reading is not
    charged here (it is O(n) and would not change the class).

    This is the honest case: the fitted O(n^2) is not just an upper bound, it
    is exact, and the cost does not depend on the string's contents — so the
    size-indexed family below loses nothing. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From BigOBench Require Import Cost Asymptotic.

(** [s.count(i)] — scans [l] entirely, one tick per element. *)
Fixpoint count (x : nat) (l : list nat) : M nat :=
  match l with
  | [] => ret 0
  | y :: r => tick (c <- count x r ;; ret (if Nat.eqb x y then S c else c))
  end.

Lemma cost_count : forall x l, cost (count x l) = length l.
Proof.
  intros x l. induction l as [| y r IH]; [reflexivity|].
  simpl count. rewrite cost_tick, cost_bind, IH. simpl. lia.
Qed.

(** The [for i in s] loop. [whole] is the string being counted in, kept
    separate from the loop variable so the quadratic is visible. *)
Fixpoint scan (s whole : list nat) : M bool :=
  match s with
  | [] => ret false
  | i :: r => c <- count i whole ;;
              b <- scan r whole ;;
              ret (orb (Nat.odd c) b)
  end.

Lemma cost_scan : forall s whole,
    cost (scan s whole) = length s * length whole.
Proof.
  intros s whole. induction s as [| i r IH]; [reflexivity|].
  simpl scan. rewrite !cost_bind, cost_count, IH. simpl. lia.
Qed.

Definition beautiful (s : list nat) : M bool := scan s s.

Theorem cost_beautiful : forall s,
    cost (beautiful s) = length s * length s.
Proof. intros s. unfold beautiful. apply cost_scan. Qed.

(** ** The asymptotic statement.

    [T n] is the cost on an input of length [n]; by [cost_beautiful] the cost
    depends only on the length, so any family of that length gives the same
    number. *)
Definition T (n : nat) : nat := cost (beautiful (List.seq 0 n)).

Lemma T_eq : forall n, T n = n * n.
Proof.
  intros n. unfold T. rewrite cost_beautiful, List.seq_length. reflexivity.
Qed.

Theorem fitted_label_is_tight : Theta T (fun n => n * n).
Proof.
  split; [exists 1, 0 | exists 1, 0]; intros n _; rewrite T_eq; lia.
Qed.
