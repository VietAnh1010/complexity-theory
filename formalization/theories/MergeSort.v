(** * MergeSort.v — a sort in the cost monad, with an O(n log n) bound.

    Covers any solution calling [sort] or [sorted].

    - Depth, not fuel. [msort] takes a depth [d] with precondition
      [length l <= 2 ^ d], so the recurrence closes by induction on [d] alone
      and [log2_up] appears only at [msort_top].
    - Adequacy is required, not decoration. [fun l => ret l] and
      [fun _ => ret []] both cost nothing and satisfy every upper bound, so
      [msort_perm] and [msort_sorted] are what make [cost_msort] mean anything.
    - [merge] is a nested fix and [simpl] unfolds it unpredictably. Proofs go
      through the [merge_nil_l / merge_nil_r / merge_cons] equations. *)

From Stdlib Require Import List Arith Lia Sorting.Sorted Sorting.Permutation.
Import ListNotations.
From BigOBench Require Import Cost Asymptotic.

(** Two-step induction, for the functions that consume a list two elements at
    a time. *)
Lemma list_ind2 : forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall x, P [x]) ->
    (forall x y r, P r -> P (x :: y :: r)) ->
    forall l, P l.
Proof.
  intros A P H0 H1 H2.
  fix IH 1. intros [| x [| y r]].
  - exact H0.
  - exact (H1 x).
  - exact (H2 x y r (IH r)).
Qed.

(** ** Splitting.

    Alternating split, one tick per element. Defined in the monad, with the
    pure version read off it, so there is a single definition. *)

Fixpoint halveM (l : list nat) : M (list nat * list nat) :=
  match l with
  | [] => ret ([], [])
  | [x] => tick (ret ([x], []))
  | x :: y :: r => charge 2 (p <- halveM r ;; ret (x :: fst p, y :: snd p))
  end.

Definition halve (l : list nat) : list nat * list nat := val (halveM l).

Lemma halve_eq : forall l, val (halveM l) = halve l.
Proof. reflexivity. Qed.

Lemma cost_halveM : forall l, cost (halveM l) = length l.
Proof.
  intros l. induction l as [| x | x y r IH] using list_ind2; try reflexivity.
  simpl halveM. rewrite cost_charge, cost_bind, cost_ret, IH. simpl. lia.
Qed.

Lemma halve_cons2 : forall x y r,
    halve (x :: y :: r) = (x :: fst (halve r), y :: snd (halve r)).
Proof. reflexivity. Qed.

Lemma halve_perm : forall l, Permutation (fst (halve l) ++ snd (halve l)) l.
Proof.
  intros l. induction l as [| x | x y r IH] using list_ind2.
  - simpl. apply perm_nil.
  - simpl. apply Permutation_refl.
  - rewrite halve_cons2. simpl.
    apply perm_skip. rewrite <- Permutation_middle. apply perm_skip. exact IH.
Qed.

Lemma halve_length : forall l,
    length (fst (halve l)) + length (snd (halve l)) = length l /\
    length (snd (halve l)) <= length (fst (halve l)) <= S (length (snd (halve l))).
Proof.
  intros l. induction l as [| x | x y r IH] using list_ind2.
  - simpl. lia.
  - simpl. lia.
  - rewrite halve_cons2. simpl. lia.
Qed.

(** The two facts the depth recurrence needs. *)
Lemma halve_fst_half : forall l, 2 * length (fst (halve l)) <= S (length l).
Proof. intros l. pose proof (halve_length l). lia. Qed.

Lemma halve_snd_half : forall l, 2 * length (snd (halve l)) <= length l.
Proof. intros l. pose proof (halve_length l). lia. Qed.

(** ** Merging.

    The usual nested fix: the outer recursion is on [a], the inner on [b]. *)

Fixpoint merge (a : list nat) : list nat -> M (list nat) :=
  match a with
  | [] => fun b => ret b
  | x :: a' =>
      (fix mergeA (b : list nat) : M (list nat) :=
         match b with
         | [] => ret (x :: a')
         | y :: b' =>
             tick (if Nat.leb x y
                   then r <- merge a' (y :: b') ;; ret (x :: r)
                   else r <- mergeA b' ;; ret (y :: r))
         end)
  end.

(** The equations. All [reflexivity]; the third relies on the inner fix
    [mergeA b'] being convertible with [merge (x :: a') b']. *)

Lemma merge_nil_l : forall b, merge [] b = ret b.
Proof. reflexivity. Qed.

Lemma merge_nil_r : forall x a', merge (x :: a') [] = ret (x :: a').
Proof. reflexivity. Qed.

Lemma merge_cons : forall x a' y b',
    merge (x :: a') (y :: b') =
      tick (if Nat.leb x y
            then r <- merge a' (y :: b') ;; ret (x :: r)
            else r <- merge (x :: a') b' ;; ret (y :: r)).
Proof. reflexivity. Qed.

Lemma cost_merge : forall a b, cost (merge a b) <= length a + length b.
Proof.
  induction a as [| x a' IHa]; intros b.
  - rewrite merge_nil_l, cost_ret. lia.
  - induction b as [| y b' IHb].
    + rewrite merge_nil_r, cost_ret. lia.
    + rewrite merge_cons, cost_tick.
      destruct (Nat.leb x y).
      * rewrite cost_bind, cost_ret.
        specialize (IHa (y :: b')). simpl length in *. lia.
      * rewrite cost_bind, cost_ret. simpl length in *. lia.
Qed.

Lemma merge_perm : forall a b, Permutation (val (merge a b)) (a ++ b).
Proof.
  induction a as [| x a' IHa]; intros b.
  - rewrite merge_nil_l, val_ret. simpl. apply Permutation_refl.
  - induction b as [| y b' IHb].
    + rewrite merge_nil_r, val_ret, app_nil_r. apply Permutation_refl.
    + rewrite merge_cons, val_tick.
      destruct (Nat.leb x y); rewrite val_bind, val_ret.
      * simpl. apply perm_skip. apply (IHa (y :: b')).
      * eapply Permutation_trans; [apply perm_skip; exact IHb |].
        apply Permutation_middle.
Qed.

Lemma merge_length : forall a b, length (val (merge a b)) = length a + length b.
Proof.
  intros a b. rewrite (Permutation_length (merge_perm a b)).
  apply length_app.
Qed.

(** The head of a merge is one of the two heads, so a bound on both heads
    bounds the result's head. This is what carries [Sorted] through. *)
Lemma merge_hdrel : forall z a b,
    HdRel le z a -> HdRel le z b -> HdRel le z (val (merge a b)).
Proof.
  intros z [| x a'] [| y b'] Ha Hb.
  - rewrite merge_nil_l, val_ret. exact Hb.
  - rewrite merge_nil_l, val_ret. exact Hb.
  - rewrite merge_nil_r, val_ret. exact Ha.
  - rewrite merge_cons, val_tick.
    destruct (Nat.leb x y); rewrite val_bind, val_ret.
    + constructor. inversion Ha; assumption.
    + constructor. inversion Hb; assumption.
Qed.

Lemma merge_sorted : forall a b,
    Sorted le a -> Sorted le b -> Sorted le (val (merge a b)).
Proof.
  induction a as [| x a' IHa]; intros b Ha Hb.
  - rewrite merge_nil_l, val_ret. exact Hb.
  - induction b as [| y b' IHb].
    + rewrite merge_nil_r, val_ret. exact Ha.
    + inversion Ha as [| ?x ?xs Ha' Hax]; subst.
      inversion Hb as [| ?y ?ys Hb' Hby]; subst.
      rewrite merge_cons, val_tick.
      destruct (Nat.leb x y) eqn:Hxy; rewrite val_bind, val_ret.
      * apply Nat.leb_le in Hxy.
        constructor.
        -- apply IHa; [exact Ha' | exact Hb].
        -- apply merge_hdrel; [exact Hax | constructor; exact Hxy].
      * apply Nat.leb_gt in Hxy.
        constructor.
        -- apply IHb. exact Hb'.
        -- apply merge_hdrel; [constructor; lia | exact Hby].
Qed.

(** ** The sort.

    [d] is the recursion depth. The [d = 0] branch with a list of length >= 2
    cannot be reached when [length l <= 2 ^ d], and every theorem below
    carries that hypothesis. *)

Fixpoint msort (d : nat) (l : list nat) : M (list nat) :=
  match l with
  | [] => ret []
  | [x] => ret [x]
  | _ =>
      match d with
      | 0 => ret l
      | S d' =>
          p <- halveM l ;;
          a <- msort d' (fst p) ;;
          b <- msort d' (snd p) ;;
          merge a b
      end
  end.

Lemma msort_cons2 : forall d' x y r,
    msort (S d') (x :: y :: r) =
      p <- halveM (x :: y :: r) ;;
      a <- msort d' (fst p) ;;
      b <- msort d' (snd p) ;;
      merge a b.
Proof. reflexivity. Qed.

Lemma msort_perm : forall d l, Permutation (val (msort d l)) l.
Proof.
  induction d as [| d' IH]; intros l.
  - destruct l as [| x [| y r]]; simpl; apply Permutation_refl.
  - destruct l as [| x [| y r]];
      [simpl; apply Permutation_refl | simpl; apply Permutation_refl |].
    rewrite msort_cons2, !val_bind, !halve_eq.
    eapply Permutation_trans; [apply merge_perm |].
    eapply Permutation_trans; [apply Permutation_app; apply IH |].
    apply halve_perm.
Qed.

Lemma msort_length : forall d l, length (val (msort d l)) = length l.
Proof. intros. apply Permutation_length, msort_perm. Qed.

Lemma msort_sorted : forall d l,
    length l <= 2 ^ d -> Sorted le (val (msort d l)).
Proof.
  induction d as [| d' IH]; intros l Hlen.
  - destruct l as [| x [| y r]].
    + simpl. constructor.
    + simpl. repeat constructor.
    + simpl in Hlen. lia.
  - destruct l as [| x [| y r]].
    + simpl. constructor.
    + simpl. repeat constructor.
    + assert (Hfst : length (fst (halve (x :: y :: r))) <= 2 ^ d')
        by (pose proof (halve_fst_half (x :: y :: r));
            simpl Nat.pow in Hlen; simpl length in *; lia).
      assert (Hsnd : length (snd (halve (x :: y :: r))) <= 2 ^ d')
        by (pose proof (halve_snd_half (x :: y :: r));
            simpl Nat.pow in Hlen; simpl length in *; lia).
      rewrite msort_cons2, !val_bind, !halve_eq.
      apply merge_sorted; apply IH; assumption.
Qed.

(** ** The cost bound.

    [2 * d * n]: each of the [d] levels does one split pass and one merge pass
    over the whole level, and each pass is one tick per element. *)

Theorem cost_msort : forall d l,
    length l <= 2 ^ d -> cost (msort d l) <= 2 * d * length l.
Proof.
  induction d as [| d' IH]; intros l Hlen.
  (* d = 0: [msort 0 l] returns [l] unchanged, at cost 0, in every branch.
     Note [rewrite cost_ret] does NOT fire here — [msort 0 []] is convertible
     with [ret []] but not syntactically equal to it, so [simpl] first. *)
  - destruct l as [| x [| y r]]; simpl; lia.
  - destruct l as [| x [| y r]]; [simpl; lia | simpl; lia |].
    assert (Hfst : length (fst (halve (x :: y :: r))) <= 2 ^ d')
      by (pose proof (halve_fst_half (x :: y :: r));
          simpl Nat.pow in Hlen; simpl length in *; lia).
    assert (Hsnd : length (snd (halve (x :: y :: r))) <= 2 ^ d')
      by (pose proof (halve_snd_half (x :: y :: r));
          simpl Nat.pow in Hlen; simpl length in *; lia).
    rewrite msort_cons2, !cost_bind, !halve_eq, cost_halveM.
    pose proof (IH _ Hfst) as Ha.
    pose proof (IH _ Hsnd) as Hb.
    pose proof (cost_merge (val (msort d' (fst (halve (x :: y :: r)))))
                           (val (msort d' (snd (halve (x :: y :: r)))))) as Hm.
    rewrite !msort_length in Hm.
    destruct (halve_length (x :: y :: r)) as [Hsum _].
    (* [lia] treats [d' * A] as an opaque atom, so it cannot distribute the
       recursive bounds over the split. Supply both products by [ring]. *)
    assert (Hdist : 2 * d' * length (fst (halve (x :: y :: r)))
                  + 2 * d' * length (snd (halve (x :: y :: r)))
                  = 2 * d' * length (x :: y :: r))
      by (rewrite <- Hsum; ring).
    assert (Hexp : 2 * S d' * length (x :: y :: r)
                 = 2 * length (x :: y :: r) + 2 * d' * length (x :: y :: r))
      by ring.
    simpl length in *. lia.
Qed.

(** ** Top level: instantiate the depth with [log2_up]. *)

Lemma length_le_pow_log2_up : forall n, n <= 2 ^ Nat.log2_up n.
Proof.
  intros [| [| n]].
  - simpl. lia.
  - rewrite Nat.log2_up_eqn0 by lia. simpl. lia.
  - destruct (Nat.log2_up_spec (S (S n)) ltac:(lia)) as [_ H]. exact H.
Qed.

Definition msort_top (l : list nat) : M (list nat) :=
  msort (Nat.log2_up (length l)) l.

Theorem cost_msort_top : forall l,
    cost (msort_top l) <= 2 * Nat.log2_up (length l) * length l.
Proof.
  intros l. unfold msort_top.
  apply cost_msort, length_le_pow_log2_up.
Qed.

Theorem msort_top_sorted : forall l, Sorted le (val (msort_top l)).
Proof.
  intros l. unfold msort_top.
  apply msort_sorted, length_le_pow_log2_up.
Qed.

Theorem msort_top_perm : forall l, Permutation (val (msort_top l)) l.
Proof. intros l. apply msort_perm. Qed.

Theorem msort_top_length : forall l, length (val (msort_top l)) = length l.
Proof. intros l. apply msort_length. Qed.
