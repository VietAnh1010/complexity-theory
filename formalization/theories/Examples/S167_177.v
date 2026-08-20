(** * S167_177 — verdict: OVERSTATED

    time_complexity_test_set: solution_id 167_177,
    "1184_A1. Heidi Learns Hashing (Easy)", fitted O(n).

    Source, verbatim (tabs as in the original):

      import math
      n = int(input())
      x = math.floor(math.sqrt(n))
      p = 0
      for i in range(1, x):
        if (n-1-i**2-i)%(2*i) == 0 :
          print(i,  (n-1-i**2-i)//(2*i))
          p = 1
          break
      if not p:
        print("NO")

    COST MODEL. One tick per loop iteration; the body is O(1) arithmetic.
    Reading the single integer is free, per the convention in [Cost.v].
    [math.floor(math.sqrt(n))] is [Nat.sqrt n], which is exactly floor of the
    real square root. The loop bound is therefore sqrt(n), not n.

    Two things charged as O(1) that are not, in the limit: [i**2] and [%] /
    [//] on Python bignums cost O(1) only while the values fit in a machine
    word. At this problem's sizes they do; beyond that the model would need a
    bit-cost for arithmetic. Flagged, not modelled.

    WHAT "n" IS. The numeric VALUE of the input integer, not a length. *)

From Stdlib Require Import Arith Lia.
From BigOBench Require Import Cost Asymptotic.

(** The loop guard's test. Its value does not affect the cost bound: the loop
    may exit early, so the count below is an upper bound. *)
Definition hit (n i : nat) : bool :=
  Nat.eqb ((n - 1 - i * i - i) mod (2 * i)) 0.

(** [for i in range(1, x)] with the [break]. [count] is the number of indices
    remaining. *)
Fixpoint scan (count i n : nat) : M bool :=
  match count with
  | 0 => ret false
  | S c => tick (if hit n i then ret true else scan c (S i) n)
  end.

Lemma cost_scan : forall count i n, cost (scan count i n) <= count.
Proof.
  (* [rewrite cost_ret] does not fire on [scan 0 i n]: convertible with
     [ret false] but not syntactically equal, so reduce first. *)
  induction count as [| c IH]; intros i n; [simpl; lia |].
  simpl scan. rewrite cost_tick.
  destruct (hit n i); [rewrite cost_ret; lia |].
  specialize (IH (S i) n). lia.
Qed.

(** [range(1, x)] has [x - 1] elements. *)
Definition solve (n : nat) : M bool := scan (Nat.sqrt n - 1) 1 n.

Definition T (n : nat) : nat := cost (solve n).

Theorem T_upper : forall n, T n <= Nat.sqrt n.
Proof.
  intros n. unfold T, solve.
  pose proof (cost_scan (Nat.sqrt n - 1) 1 n). lia.
Qed.

(** ** The disagreement.

    O(n) is a sound upper bound — [Nat.sqrt n <= n] — but not a tight one: the
    cost is not Omega(n). Witness family: perfect squares, where
    [Nat.sqrt (m * m) = m] exactly. *)

Theorem fitted_label_sound : BigO T (fun n => n).
Proof.
  exists 1, 0. intros n _.
  pose proof (T_upper n). pose proof (Nat.sqrt_le_lin n). lia.
Qed.

Theorem fitted_label_not_tight : ~ BigOmega T (fun n => n).
Proof.
  apply not_BigOmega. intros c n0.
  set (m := c + 1 + n0).
  exists (m * m). split.
  - (* m * m >= n0 *)
    assert (1 <= m) by (unfold m; lia). nia.
  - (* c * T (m*m) <= c * m < m * m *)
    pose proof (T_upper (m * m)) as Hup.
    rewrite Nat.sqrt_square in Hup.
    assert (Hc : c < m) by (unfold m; lia).
    nia.
Qed.

(** The bound is attained, not merely available: on a perfect square the loop
    is offered [m - 1] indices. *)
Lemma loop_bound_is_sqrt : forall m, solve (m * m) = scan (m - 1) 1 (m * m).
Proof. intros m. unfold solve. rewrite Nat.sqrt_square. reflexivity. Qed.

(** Computed witnesses. [n = 10000] gives at most 99 iterations, not 10000. *)
Example T_10000 : T 10000 <= 99.
Proof. vm_compute. lia. Qed.

Example sqrt_10000 : Nat.sqrt 10000 = 100.
Proof. vm_compute. reflexivity. Qed.
