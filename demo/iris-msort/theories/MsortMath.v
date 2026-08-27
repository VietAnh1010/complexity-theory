(** Pure arithmetic and list lemmas backing the O(n log n) bound for the
    HeapLang merge sort verified in [MsortProof.v].

    Nothing here mentions Iris: the recurrence is closed at the level of
    natural numbers, so the separation-logic proof only has to line the
    credits up with [msort_cost]. *)

From stdpp Require Import list sorting.
From Coq Require Import Arith Lia ssreflect.

(** * Two-step induction on lists *)

Lemma list_ind2 {A} (P : list A → Prop) :
  P [] →
  (∀ x, P [x]) →
  (∀ x y l, P l → P (x :: y :: l)) →
  ∀ l, P l.
Proof.
  intros H0 H1 H2. fix IH 1. intros [|x [|y l]].
  - exact H0.
  - exact (H1 x).
  - apply H2, IH.
Qed.

(** * Alternating split

    [split2] deals the elements out to two lists, taking every other one.
    It matches the HeapLang [split_list] of [MsortCode.v] step for step. *)

Fixpoint split2 {A} (l : list A) : list A * list A :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: l' => (x :: (split2 l').1, y :: (split2 l').2)
  end.

Lemma split2_perm {A} (l : list A) : (split2 l).1 ++ (split2 l).2 ≡ₚ l.
Proof.
  induction l as [| x | x y l IH] using list_ind2; [done|done|].
  simpl. rewrite -Permutation_middle IH. done.
Qed.

Lemma split2_lengths {A} (l : list A) :
  length (split2 l).1 + length (split2 l).2 = length l
  ∧ length (split2 l).2 ≤ length (split2 l).1
  ∧ length (split2 l).1 ≤ length (split2 l).2 + 1.
Proof.
  induction l as [| x | x y l IH] using list_ind2; simpl; lia.
Qed.

(** * Halving decreases [log2_up] *)

Lemma log2_up_ge_1 (n : nat) : 2 ≤ n → 1 ≤ Nat.log2_up n.
Proof.
  intros Hn. change 1 with (Nat.log2_up 2). by apply Nat.log2_up_le_mono.
Qed.

Lemma log2_up_half (a n : nat) :
  2 ≤ n → 0 < a → 2 * a ≤ n + 1 → S (Nat.log2_up a) ≤ Nat.log2_up n.
Proof.
  intros Hn Ha Hle.
  pose proof (log2_up_ge_1 n Hn) as HL.
  (* n ≤ 2 ^ log2_up n *)
  assert (n ≤ 2 ^ Nat.log2_up n) as Hpow
    by (apply Nat.log2_up_le_pow2; [lia|done]).
  (* hence a ≤ 2 ^ (log2_up n - 1) *)
  assert (a ≤ 2 ^ (Nat.log2_up n - 1)) as Ha2.
  { assert (2 ^ Nat.log2_up n = 2 * 2 ^ (Nat.log2_up n - 1)) as Heq.
    { rewrite -Nat.pow_succ_r'. f_equal. lia. }
    lia. }
  assert (Nat.log2_up a ≤ Nat.log2_up n - 1)
    by (apply Nat.log2_up_le_pow2; [lia|done]).
  lia.
Qed.

(** * The recurrence

    [msort_cost K E n = K * (n * ⌈log2 n⌉) + E] absorbs one level of merge
    sort provided each level costs at most [c] per element plus [d]. *)

Definition msort_cost (K E n : nat) : nat := K * (n * Nat.log2_up n) + E.
Arguments msort_cost K E n : simpl never.

Lemma msort_cost_step (K E c d a b n : nat) :
  2 ≤ n → a + b = n → b ≤ a → a ≤ b + 1 → c + d + E ≤ K →
  (c * n + d) + msort_cost K E a + msort_cost K E b ≤ msort_cost K E n.
Proof.
  intros Hn Hab Hba Hab1 HK. unfold msort_cost.
  set (L := Nat.log2_up n).
  assert (0 < a) as Ha0 by lia.
  assert (0 < b) as Hb0 by lia.
  assert (S (Nat.log2_up a) ≤ L) as Ha by (apply log2_up_half; lia).
  assert (S (Nat.log2_up b) ≤ L) as Hb by (apply log2_up_half; lia).
  assert (1 ≤ L) as HL by (apply log2_up_ge_1; lia).
  (* a * log a + b * log b + n ≤ n * L *)
  assert (a * Nat.log2_up a + b * Nat.log2_up b + n ≤ n * L) as Hsplit.
  { assert (a * Nat.log2_up a ≤ a * (L - 1)) as H1 by (apply Nat.mul_le_mono_l; lia).
    assert (b * Nat.log2_up b ≤ b * (L - 1)) as H2 by (apply Nat.mul_le_mono_l; lia).
    assert (a * (L - 1) + b * (L - 1) = n * L - n) as Heq.
    { rewrite -Nat.mul_add_distr_r Hab Nat.mul_sub_distr_l. lia. }
    assert (n ≤ n * L) as H3 by (rewrite -{1}(Nat.mul_1_r n); apply Nat.mul_le_mono_l; lia).
    lia. }
  (* c * n + d + E ≤ K * n, using n ≥ 2 *)
  assert (c * n + d + E ≤ K * n) as HKn.
  { assert ((c + d + E) * n ≤ K * n) as H1 by (apply Nat.mul_le_mono_r; lia).
    assert (d + E ≤ (d + E) * n) as H2 by (rewrite -{1}(Nat.mul_1_r (d + E)); apply Nat.mul_le_mono_l; lia).
    rewrite !Nat.mul_add_distr_r in H1. lia. }
  assert (K * (a * Nat.log2_up a) + K * (b * Nat.log2_up b) + K * n ≤ K * (n * L)) as Hfin.
  { rewrite -!Nat.mul_add_distr_l. apply Nat.mul_le_mono_l. lia. }
  lia.
Qed.

(** Monotonicity, so a caller can hand over credits for a bigger list. *)
Lemma msort_cost_mono (K E n m : nat) : n ≤ m → msort_cost K E n ≤ msort_cost K E m.
Proof.
  intros Hnm. unfold msort_cost.
  apply Nat.add_le_mono_r, Nat.mul_le_mono_l, Nat.mul_le_mono;
    [done | by apply Nat.log2_up_le_mono].
Qed.
