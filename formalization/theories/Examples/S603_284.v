(** * S603_284 — verdict: SOUND_UPPER_ONLY (matching upper bound proved;
      tightness deliberately not claimed)

    BigO(Bench) time_complexity_test_set
      solution_id   603_284
      problem_name  1041_A. Heist
      fitted label  O(nlogn)

    Source solution, verbatim:

      n=int(input())
      l=list(map(int,input().split()))
      l.sort()
      x=0
      for i in range(n-1):
          x+=l[i+1]-l[i]-1
      print(x)

    COST MODEL. One tick per element parsed, the sort as modelled in
    MergeSort.v, and one tick per iteration of the final pairwise scan. The
    list is read sequentially by index, which is O(1) per access in Python, so
    the scan is linear.

    WHY THE VERDICT IS NOT "Tight". Two separate gaps, and they point in
    opposite directions:

    - Upper bound. Proved: O(n log n), matching the label. CPython's [sort] is
      Timsort, whose worst case is also O(n log n), so modelling it as merge
      sort does not understate.

    - Lower bound. NOT proved, and deliberately so. Merge sort is Theta(n log n)
      on every input, but Timsort is Theta(n) on already-sorted input — it
      detects existing runs. So a Theta(n log n) claim about the real program
      is FALSE on sorted inputs, and "proving" it here by appealing to merge
      sort would be an artefact of the model, not a fact about the code.

    What is proved below is therefore a sandwich with a gap in it:
    Omega(n) <= cost <= O(n log n). Closing it would require modelling Timsort's
    run detection and quantifying over an input family that defeats it. The
    fitted label sits at the top of that range, which is the right place for a
    worst-case label — but this file does not establish that the framework's
    input expansion ever reached the worst case. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From BigOBench Require Import Cost Asymptotic MergeSort.

(** [l=list(map(int,input().split()))] — one tick per element. *)
Fixpoint parse (l : list nat) : M (list nat) :=
  match l with
  | [] => ret []
  | x :: r => tick (t <- parse r ;; ret (x :: t))
  end.

Lemma cost_parse : forall l, cost (parse l) = length l.
Proof.
  intros l. induction l as [| x r IH]; [reflexivity|].
  simpl parse. rewrite cost_tick, cost_bind, IH. simpl. lia.
Qed.

Lemma val_parse : forall l, val (parse l) = l.
Proof.
  intros l. induction l as [| x r IH]; [reflexivity|].
  simpl parse. rewrite val_tick, val_bind, IH. reflexivity.
Qed.

(** [for i in range(n-1): x+=l[i+1]-l[i]-1] — the pairwise scan over the
    sorted list. Structural: the recursive call is on the tail. *)
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

Definition solve (l : list nat) : M nat :=
  l1 <- parse l ;;
  l2 <- msort_top l1 ;;
  gaps l2.

Theorem cost_solve : forall l,
    cost (solve l) <= 2 * Nat.log2_up (length l) * length l + 2 * length l.
Proof.
  intros l. unfold solve.
  rewrite !cost_bind, cost_parse, val_parse.
  pose proof (cost_msort_top l) as Hs.
  pose proof (cost_gaps (val (msort_top l))) as Hg.
  rewrite msort_top_length in Hg.
  lia.
Qed.

(** The parse pass alone forces a linear lower bound. *)
Theorem cost_solve_lower : forall l, length l <= cost (solve l).
Proof.
  intros l. unfold solve.
  rewrite !cost_bind, cost_parse. lia.
Qed.

Definition T (n : nat) : nat := cost (solve (List.seq 0 n)).

Lemma T_upper : forall n, T n <= 2 * Nat.log2_up n * n + 2 * n.
Proof.
  intros n. unfold T.
  pose proof (cost_solve (List.seq 0 n)) as H.
  rewrite List.seq_length in H. exact H.
Qed.

Lemma T_lower : forall n, n <= T n.
Proof.
  intros n. unfold T.
  pose proof (cost_solve_lower (List.seq 0 n)) as H.
  rewrite List.seq_length in H. exact H.
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

    Only Omega(n) is available, from the parse pass. Stating it explicitly so
    the gap is on the record rather than implied by the absence of a theorem. *)
Theorem lower_bound_is_only_linear : BigOmega T (fun n => n).
Proof.
  exists 1, 0. intros n _. pose proof (T_lower n). lia.
Qed.
