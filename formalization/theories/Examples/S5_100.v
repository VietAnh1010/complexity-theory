(** * S5_100 — verdict: OVERSTATED

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
    Reading the single integer is free, per the convention in [Cost.v].

    WHAT "n" IS. The value of a single integer, not the length of a
    collection, which is what the framework's dataclass measures. The loop
    subtracts 1, 2, 3, ..., so it stops after about sqrt(2n) iterations and the
    fitted O(n) is off by a square root. The bound is stated as
    [c * (c + 1) <= 2 * n] — exactly "c is at most about sqrt(2n)" with no
    [sqrt] on [nat], avoiding rounding questions.

    TERMINATION. Rocq needs structural recursion, so the loop takes fuel. A
    truncated loop satisfies any upper bound, so [run_finishes] proves the fuel
    is never exhausted at the call site. *)

From Stdlib Require Import Arith Lia.
From BigOBench Require Import Cost Asymptotic.

(** The bool records whether the loop exited through its guard (true) or ran
    out of fuel (false). It costs nothing and exists to state
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

    [loop_bound] is the loop invariant, cleared of division and of [nat]
    subtraction. Write [c] for [cost (loop fuel n k)].

    From state [(n, k)] the loop subtracts [k], [k+1], ..., [k+c-1], so after
    [c] iterations it has consumed

      c*k + (0 + 1 + ... + (c-1))  =  c*k + c*(c-1)/2

    and that cannot exceed [n]. Two rearrangements make it a statement [nia]
    can work with:

    - multiply by 2, clearing the division: [2*k*c + c*c - c <= 2*n];
    - move the [-c] to the right, because [c*c - c] truncates at 0 in [nat]:
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

(** ** The fitted label is a sound upper bound.

    From [iters_sqrt]: if the loop runs at all then [c <= c * (c + 1) <= 2n],
    and [c = 0] is under the bound trivially. O(n) therefore holds — what
    fails is tightness, below. *)

Theorem fitted_label_sound : BigO iters (fun n => n).
Proof.
  exists 2, 0. intros n _. pose proof (iters_sqrt n) as H. nia.
Qed.

(** ** A matching lower bound.

    [iters_sqrt] alone does not pin the cost down: it is an upper bound, and a
    loop that exits immediately satisfies every upper bound. To say the cost is
    about sqrt(n) — and, below, that it is exponential in the input's bit
    length — requires a proof that the loop runs at least that many times.

    [iters_lower_gen] is the mirror of [loop_bound]: same invariant, read as a
    lower bound. It says [j] iterations happen, provided [n] starts far enough
    above the counter for the guard to survive [j] of them.

    Where the hypothesis comes from. After [j] iterations from [(n, k)] the
    loop has consumed [j*k + (0 + 1 + ... + (j-1))], so the value is at least
    [n - j*k - j*j] and the counter is [k + j]. The guard is
    counter < value, and

      k + j < n - (j*k + j*j)   iff   j*k + j*j + k + j < n

    is enough for all [j] of them. Two deliberate weakenings: the consumed
    total is really [j*k + j*(j-1)/2], and [j*j] over-counts it; and the guard
    only has to hold at the last iteration, not uniformly. Both keep the
    hypothesis polynomial and division-free, which is what [nia] needs. A
    sharper condition would buy nothing — the constants wash out in
    [cost_is_Omega_sqrt].

    [j <= fuel] is a fact about the model, not the algorithm: the loop cannot
    take [j] steps on less than [j] fuel. *)

Lemma iters_lower_gen : forall j fuel n k,
    j <= fuel -> j * k + j * j + k + j < n -> j <= cost (loop fuel n k).
Proof.
  induction j as [| j' IH]; intros fuel n k Hf Hc; [lia |].
  destruct fuel as [| f]; [lia |].
  simpl. destruct (Nat.ltb_spec k n) as [Hlt | Hge]; [| nia].
  rewrite cost_tick.
  assert (Hj : j' <= cost (loop f (n - k) (S k))).
  { apply IH; [lia |]. nia. }
  lia.
Qed.

(** At the call site [k = 1] and [fuel = n], and the hypothesis collapses to
    [(j+1)^2 < n]: the loop runs at least [j] times on any [n] past the next
    square. [j <= fuel] follows from it. *)
Theorem iters_lower : forall n j, (j + 1) * (j + 1) < n -> j <= iters n.
Proof.
  intros n j Hc. unfold iters, run.
  apply iters_lower_gen; nia.
Qed.

(** ** The tight class: Theta(sqrt n).

    [fitted_label_sound] and [fitted_label_not_tight] say O(n) holds and is not
    tight; these two pin down what does hold. [Nat.sqrt] is floor of the real
    square root, so the constants absorb the rounding: the upper bound is
    [2*sqrt n + 1], the lower [sqrt n - 2]. *)

Lemma iters_upper_sqrt : forall n, iters n <= 2 * Nat.sqrt n + 1.
Proof.
  intros n. pose proof (iters_sqrt n) as H.
  destruct (Nat.sqrt_spec n (Nat.le_0_l n)) as [Hlo Hhi]. nia.
Qed.

Lemma iters_lower_sqrt : forall n, 16 <= n -> Nat.sqrt n - 2 <= iters n.
Proof.
  intros n Hn.
  assert (Hs : 4 <= Nat.sqrt n) by (apply Nat.sqrt_le_square; lia).
  destruct (Nat.sqrt_spec n (Nat.le_0_l n)) as [Hlo Hhi].
  apply iters_lower. nia.
Qed.

Theorem cost_is_O_sqrt : BigO iters Nat.sqrt.
Proof.
  exists 3, 1. intros n Hn.
  assert (Hs : 1 <= Nat.sqrt n) by (apply Nat.sqrt_le_square; lia).
  pose proof (iters_upper_sqrt n). lia.
Qed.

Theorem cost_is_Omega_sqrt : BigOmega iters Nat.sqrt.
Proof.
  exists 2, 16. intros n Hn.
  assert (Hs : 4 <= Nat.sqrt n) by (apply Nat.sqrt_le_square; lia).
  pose proof (iters_lower_sqrt n Hn). lia.
Qed.

Theorem cost_is_theta_sqrt : Theta iters Nat.sqrt.
Proof. split; [apply cost_is_O_sqrt | apply cost_is_Omega_sqrt]. Qed.

(** ** The same loop against the input's bit length.

    [2 ^ (2*k+2)] is a [2*k+3]-bit number and the loop runs at least [2 ^ k]
    times on it, so no polynomial in the bit length bounds the cost. *)

Lemma pow_2k2 : forall k, 2 ^ (2 * k + 2) = 4 * (2 ^ k * 2 ^ k).
Proof.
  intros k.
  replace (2 * k + 2) with (k + k + 2) by lia.
  rewrite !Nat.pow_add_r.
  simpl (2 ^ 2). ring.
Qed.

Theorem iters_exponential_in_bitlength : forall k,
    1 <= k -> 2 ^ k <= iters (2 ^ (2 * k + 2)).
Proof.
  intros k Hk. apply iters_lower.
  rewrite pow_2k2.
  assert (H2 : 2 <= 2 ^ k) by (rewrite <- (Nat.pow_1_r 2) at 1;
                               apply Nat.pow_le_mono_r; lia).
  nia.
Qed.


(** Computed values, showing neither bound is vacuous. They track sqrt(2n)
    closely: sqrt(2*4096) = 90.5 against 90 computed. Read as bit lengths,
    these are the k = 2, 3, 4, 5 instances of the theorem above — 7, 9, 11 and
    13-bit inputs on which the loop runs 10, 22, 44 and 90 times. *)
Example iters_table :
  (iters 64, iters 256, iters 1024, iters 4096) = (10, 22, 44, 90).
Proof. vm_compute. reflexivity. Qed.

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
    not 5050. It subtracts 1 + 2 + ... + 99 = 4950, leaving n = 100 = k, where
    the guard [n > k] fails. *)
Example iters_5050 : iters 5050 = 99.
Proof. vm_compute. reflexivity. Qed.

Example final_value_5050 : fst (val (run 5050)) = 100.
Proof. vm_compute. reflexivity. Qed.
