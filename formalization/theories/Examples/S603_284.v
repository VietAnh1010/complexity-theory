(** * S603_284 — verdict: SOUND_UPPER_ONLY

    time_complexity_test_set: solution_id 603_284, "1041_A. Heist",
    fitted O(nlogn).

    Source, verbatim:

      n=int(input())
      l=list(map(int,input().split()))
      l.sort()
      x=0
      for i in range(n-1):
          x+=l[i+1]-l[i]-1
      print(x)

    COST MODEL. The sort as modelled in MergeSort.v, one tick per iteration of
    the pairwise scan (indexed access is O(1) in Python, so the scan is
    linear). Reading and parsing the input is free, per the convention in
    [Cost.v]; [parse] is modelled so the step is visible, but charged nothing.
    The linear lower bound below therefore comes from the scan, not from the
    input read.

    NOT "Tight", deliberately. The upper bound transfers: CPython's [sort] is
    Timsort, also O(n log n) in the worst case. The matching LOWER bound does
    not: Timsort is Theta(n) on already-sorted input where merge sort is not,
    so Omega(n log n) would be an artefact of the model and false of the
    program. Proved here: Omega(n) <= cost <= O(n log n), gap left open. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From BigOBench Require Import Cost Asymptotic MergeSort.

(** [l=list(map(int,input().split()))] — input parsing, charged nothing. *)
Fixpoint parse (l : list nat) : M (list nat) :=
  match l with
  | [] => ret []
  | x :: r => t <- parse r ;; ret (x :: t)
  end.

Lemma cost_parse : forall l, cost (parse l) = 0.
Proof.
  intros l. induction l as [| x r IH]; [reflexivity|].
  simpl parse. rewrite cost_bind, IH. reflexivity.
Qed.

Lemma val_parse : forall l, val (parse l) = l.
Proof.
  intros l. induction l as [| x r IH]; [reflexivity|].
  simpl parse. rewrite val_bind, IH. reflexivity.
Qed.

(** [for i in range(n-1): x+=l[i+1]-l[i]-1] — the pairwise scan over the
    sorted list. Structurally recursive: the call is on the tail. *)
Fixpoint gaps (l : list nat) : M nat :=
  match l with
  | [] => ret 0
  | x :: r =>
      match r with
      | [] => ret 0
      | y :: _ => tick (s <- gaps r ;; ret (s + (y - x - 1)))
      end
  end.

Lemma gaps_nil : gaps [] = ret 0.
Proof. reflexivity. Qed.

Lemma gaps_one : forall x, gaps [x] = ret 0.
Proof. reflexivity. Qed.

Lemma gaps_cons2 : forall x y t,
    gaps (x :: y :: t) = tick (s <- gaps (y :: t) ;; ret (s + (y - x - 1))).
Proof. reflexivity. Qed.

Lemma cost_gaps : forall l, cost (gaps l) <= length l.
Proof.
  induction l as [| x r IH].
  - rewrite gaps_nil, cost_ret. simpl. lia.
  - destruct r as [| y t].
    + rewrite gaps_one, cost_ret. simpl. lia.
    + rewrite gaps_cons2, cost_tick, cost_bind, cost_ret.
      simpl length in *. lia.
Qed.

(** The scan runs once per adjacent pair, so it also bounds the cost from
    below. This is where the linear lower bound comes from now that parsing is
    free — real work over the list, not the input read. *)
Lemma cost_gaps_lower : forall l, length l - 1 <= cost (gaps l).
Proof.
  induction l as [| x r IH].
  - rewrite gaps_nil, cost_ret. simpl. lia.
  - destruct r as [| y t].
    + rewrite gaps_one, cost_ret. simpl. lia.
    + rewrite gaps_cons2, cost_tick, cost_bind, cost_ret.
      simpl length in *. lia.
Qed.

Definition solve (l : list nat) : M nat :=
  l1 <- parse l ;;
  l2 <- msort_top l1 ;;
  gaps l2.

Theorem cost_solve : forall l,
    cost (solve l) <= 2 * Nat.log2_up (length l) * length l + length l.
Proof.
  intros l. unfold solve.
  rewrite !cost_bind, cost_parse, val_parse.
  pose proof (cost_msort_top l) as Hs.
  pose proof (cost_gaps (val (msort_top l))) as Hg.
  rewrite msort_top_length in Hg.
  lia.
Qed.

(** The pairwise scan alone forces a linear lower bound. *)
Theorem cost_solve_lower : forall l, length l - 1 <= cost (solve l).
Proof.
  intros l. unfold solve.
  rewrite !cost_bind, cost_parse, val_parse.
  pose proof (cost_gaps_lower (val (msort_top l))) as Hg.
  rewrite msort_top_length in Hg.
  lia.
Qed.

Definition T (n : nat) : nat := cost (solve (List.seq 0 n)).

Lemma T_upper : forall n, T n <= 2 * Nat.log2_up n * n + n.
Proof.
  intros n. unfold T.
  pose proof (cost_solve (List.seq 0 n)) as H.
  rewrite List.length_seq in H. exact H.
Qed.

Lemma T_lower : forall n, n - 1 <= T n.
Proof.
  intros n. unfold T.
  pose proof (cost_solve_lower (List.seq 0 n)) as H.
  rewrite List.length_seq in H. exact H.
Qed.

Lemma log2_up_ge_1 : forall n, 2 <= n -> 1 <= Nat.log2_up n.
Proof.
  intros n Hn.
  destruct (Nat.eq_dec (Nat.log2_up n) 0) as [E | E].
  - apply Nat.log2_up_null in E. lia.
  - lia.
Qed.

(** ** The fitted label is a sound upper bound. *)
Theorem fitted_label_sound : BigO T (fun n => n * Nat.log2_up n).
Proof.
  exists 4, 2. intros n Hn.
  pose proof (T_upper n) as H.
  pose proof (log2_up_ge_1 n Hn) as Hlog.
  nia.
Qed.

(** ** What is NOT proved: the matching lower bound.

    Only Omega(n) is available, from the pairwise scan. Stated explicitly so
    the gap is on the record, not left implicit in a missing theorem. *)
Theorem lower_bound_is_only_linear : BigOmega T (fun n => n).
Proof.
  exists 2, 2. intros n Hn. pose proof (T_lower n). lia.
Qed.
