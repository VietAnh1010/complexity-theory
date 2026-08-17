(** * S5_100 — verdict: UNSOUND_OVER

    time_complexity_test_set: solution_id 5_100, "622_A. Infinite Sequence",
    fitted O(n).

    Source, verbatim:

      n=int(input())
      k=1
      while(n>k):
         n-=k
         k+=1
      print(n)

    COST MODEL. One tick per loop iteration; the body is O(1) arithmetic.

    WHAT "n" IS. The value of a single integer, not the length of a
    collection. The loop subtracts 1, 2, 3, ..., so it stops after about
    sqrt(2n) iterations and the fitted O(n) is off by a square root. Two
    caveats that decide whether this counts:

    - Against the input's BIT LENGTH this loop is exponential, not sublinear.
      The framework and this file both use the numeric value, so the
      comparison is fair, but neither uses the textbook convention.
    - The bound is stated as [c * (c + 1) <= 2 * n] — exactly "c is at most
      about sqrt(2n)" with no [sqrt] on [nat], avoiding rounding questions.

    TERMINATION. Rocq needs structural recursion, so the loop takes fuel.
    Fuel makes a cost bound trivially satisfiable by truncation, so
    [run_finishes] proves the fuel is never exhausted at the call site. *)

From Stdlib Require Import Arith Lia.
From BigOBench Require Import Cost Asymptotic.

(** The bool tracks whether the loop exited through its guard (true) or ran
    out of fuel (false). It costs nothing and exists only to state
    [loop_adequate]. *)
Fixpoint loop (fuel n k : nat) : M (nat * bool) :=
  match fuel with
  | 0 => if Nat.ltb k n then ret (n, false) else ret (n, true)
  | S f => if Nat.ltb k n then tick (loop f (n - k) (S k)) else ret (n, true)
  end.

Definition run (n : nat) : M (nat * bool) := loop n n 1.
Definition iters (n : nat) : nat := cost (run n).
Definition finished (n : nat) : bool := snd (val (run n)).

(** ** Adequacy: the fuel supplied at the call site is always enough. *)

Lemma loop_adequate : forall fuel n k,
    1 <= k -> n <= k + fuel -> snd (val (loop fuel n k)) = true.
Proof.
  induction fuel as [| f IH]; intros n k Hk Hn.
  - simpl. destruct (Nat.ltb_spec k n) as [Hlt | Hge]; [lia | reflexivity].
  - simpl. destruct (Nat.ltb_spec k n) as [Hlt | Hge]; [| reflexivity].
    rewrite val_tick. apply IH; lia.
Qed.

Theorem run_finishes : forall n, finished n = true.
Proof. intros n. unfold finished, run. apply loop_adequate; lia. Qed.

(** ** The cost bound.

    The invariant: after [c] iterations starting at [k], the loop has consumed
    [c*k + (0 + 1 + ... + (c-1))] from [n]. Stated without subtraction as
    [2*k*c + c*c <= 2*n + c]. *)

Lemma loop_bound : forall fuel n k,
    2 * k * cost (loop fuel n k) + cost (loop fuel n k) * cost (loop fuel n k)
    <= 2 * n + cost (loop fuel n k).
Proof.
  induction fuel as [| f IH]; intros n k.
  - simpl. destruct (Nat.ltb_spec k n); rewrite cost_ret; lia.
  - simpl. destruct (Nat.ltb_spec k n) as [Hlt | Hge]; [| rewrite cost_ret; lia].
    rewrite cost_tick.
    (* replace n by k + d with d >= 1, so the IH's [n - k] is subtraction-free *)
    assert (Hd : exists d, n = k + d /\ 1 <= d) by (exists (n - k); lia).
    destruct Hd as [d [Hnd Hd1]]. subst n.
    replace (k + d - k) with d by lia.
    specialize (IH d (S k)).
    set (c' := cost (loop f d (S k))) in *.
    nia.
Qed.

Theorem iters_sqrt : forall n, iters n * (iters n + 1) <= 2 * n.
Proof.
  intros n. unfold iters, run. pose proof (loop_bound n n 1) as H. nia.
Qed.

(** ** The disagreement, as a theorem: the cost is not Omega(n), so O(n) is
       not a tight label. *)

Theorem fitted_label_not_tight : ~ BigOmega iters (fun n => n).
Proof.
  apply not_BigOmega. intros c n0.
  exists (S (Nat.max n0 (2 * c * c))). split.
  - pose proof (Nat.le_max_l n0 (2 * c * c)). lia.
  - pose proof (Nat.le_max_r n0 (2 * c * c)) as Hmax.
    set (n := S (Nat.max n0 (2 * c * c))) in *.
    pose proof (iters_sqrt n) as Hq.
    set (i := iters n) in *.
    destruct (Nat.eq_dec i 0) as [Hi0 | Hi0].
    + (* zero iterations: the guard failed at once, so c * 0 = 0 < n *)
      rewrite Hi0. unfold n. lia.
    + (* i >= 1, so i*i <= i*(i+1) <= 2n forces i to be small *)
      assert (Hi1 : 1 <= i) by lia.
      nia.
Qed.

(** A concrete witness, for the catalog: at n = 5050 the loop runs 99 times,
    not 5050. It subtracts 1 + 2 + ... + 99 = 4950, leaving n = 100 = k, at
    which point the guard [n > k] fails. *)
Example iters_5050 : iters 5050 = 99.
Proof. vm_compute. reflexivity. Qed.

Example final_value_5050 : fst (val (run 5050)) = 100.
Proof. vm_compute. reflexivity. Qed.
