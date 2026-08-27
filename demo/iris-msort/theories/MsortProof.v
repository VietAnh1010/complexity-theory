From iris.program_logic Require Import adequacy.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Reduction Examples.
From iris_msort Require Import MsortMath MsortCode.
From stdpp Require Import sorting.
From Coq Require Import Lia.

Section proofs.
Context `{!timeCreditHeapG Σ}.

Lemma TC_le (m n : nat) : (n ≤ m)%nat → TC m -∗ TC n.
Proof. iIntros (Hle) "H". by iApply (TC_weaken m n Hle with "H"). Qed.

(** Cost of [split_list], in ticks, as a function of the list length. *)
Definition split_cost (n : nat) : nat := (40 * n + 40)%nat.
Arguments split_cost n : simpl never.

Lemma split_list_spec (n : nat) (l : list Z) (v : val) :
  length l = n →
  TC_invariant -∗
  {{{ is_list_tr l v ∗ TC (split_cost n) }}}
    « split_list v »
  {{{ w1 w2, RET (w1, w2)%V ;
      is_list_tr (split2 l).1 w1 ∗ is_list_tr (split2 l).2 w2 }}}.
Proof.
  intros <-.
  iIntros "#Htickinv !#" (Φ) "[Hl Htc] Post".
  iInduction l as [| x | x y l] "IH" using list_ind2 forall (v Φ).
  - iDestruct "Hl" as %->.
    replace (split_cost (length (@nil Z))) with 40%nat by (unfold split_cost; simpl; lia).
    wp_tick_rec. wp_tick_match.
    wp_tick_inj. wp_tick_inj. wp_tick_pair.
    iApply "Post". simpl. auto.
  - iDestruct "Hl" as (p) "[-> Hl]"; iDestruct "Hl" as (t) "[Hp Ht]".
    iDestruct "Ht" as %->.
    replace (split_cost (length [x])) with 80%nat by (unfold split_cost; simpl; lia).
    wp_tick_rec. wp_tick_match.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    wp_tick_match.
    wp_tick_inj. wp_tick_inj. wp_tick_pair. wp_tick. wp_alloc p1 as "Hp1".
    wp_tick_inj. wp_tick_pair.
    iApply "Post". simpl. iSplitR ""; last done.
    iExists p1. iSplit; first done. iExists NONEV. simpl. iFrame. done.
  - iDestruct "Hl" as (p) "[-> Hl]"; iDestruct "Hl" as (t) "[Hp Ht]".
    iDestruct "Ht" as (q) "[-> Ht]"; iDestruct "Ht" as (t2) "[Hq Ht2]".
    replace (split_cost (length (x :: y :: l))) with (80 + split_cost (length l))%nat
      by (unfold split_cost; simpl; lia).
    iDestruct "Htc" as "[Htc80 Htc]".
    wp_tick_rec. wp_tick_match.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    wp_tick_match.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    wp_apply ("IH" with "Ht2 Htc"). iIntros (w1 w2) "[Hw1 Hw2]".
    wp_tick_let.
    wp_tick_proj. wp_tick_pair. wp_tick. wp_alloc p2 as "Hp2". wp_tick_inj.
    wp_tick_proj. wp_tick_pair. wp_tick. wp_alloc p1 as "Hp1". wp_tick_inj.
    wp_tick_pair.
    iDestruct (is_list_tr_translation with "Hw1") as "[Hw1 %Hw1eq]".
    iDestruct (is_list_tr_translation with "Hw2") as "[Hw2 %Hw2eq]".
    iApply "Post". simpl. iSplitL "Hp1 Hw1".
    + iExists p1. iSplit; first done. iExists w1. rewrite -Hw1eq. iFrame.
    + iExists p2. iSplit; first done. iExists w2. rewrite -Hw2eq. iFrame.
Qed.

(** Call-site form: the argument of a translated call is the translation of
    a value, and [wp_apply] matches syntactically, so we restate the spec
    with the translated argument as an explicit parameter. *)
Lemma split_list_spec' (n : nat) (l : list Z) (v u : val) :
  length l = n → u = « v »%V →
  TC_invariant -∗
  {{{ is_list_tr l v ∗ TC (split_cost n) }}}
    (tick « split_list »%V u)%E
  {{{ w1 w2, RET (w1, w2)%V ;
      is_list_tr (split2 l).1 w1 ∗ is_list_tr (split2 l).2 w2 }}}.
Proof. intros Hn ->. by apply split_list_spec. Qed.

(** Cost of [merge_list], in ticks, as a function of the total length. *)
Definition merge_cost (n : nat) : nat := (40 * n + 40)%nat.
Arguments merge_cost n : simpl never.

Lemma merge_list_spec (m : nat) : ∀ (l1 l2 : list Z) (v1 v2 : val),
  (length l1 + length l2 ≤ m)%nat →
  TC_invariant -∗
  {{{ is_list_tr l1 v1 ∗ is_list_tr l2 v2
      ∗ TC (merge_cost (length l1 + length l2)) }}}
    « merge_list v1 v2 »
  {{{ w, RET w ; is_list_tr (list_merge Z.le l1 l2) w }}}.
Proof.
  induction m as [|m IHm].
  - iIntros (l1 l2 v1 v2 Hlen) "#Htickinv".
    iIntros "!#" (Φ) "(Hl1 & Hl2 & Htc) Post".
    destruct l1 as [|x l1]; last (simpl in Hlen; lia).
    destruct l2 as [|y l2]; last (simpl in Hlen; lia).
    iDestruct "Hl1" as %->. iDestruct "Hl2" as %->.
    replace (merge_cost (length (@nil Z) + length (@nil Z))) with 40%nat
      by (unfold merge_cost; simpl; lia).
    wp_tick_rec. wp_tick_let. wp_tick_match.
    iApply "Post". by rewrite list_merge_nil_l.
  - iIntros (l1 l2 v1 v2 Hlen) "#Htickinv".
    iIntros "!#" (Φ) "(Hl1 & Hl2 & Htc) Post".
    destruct l1 as [|x l1].
    { iDestruct "Hl1" as %->.
      replace (merge_cost (length (@nil Z) + length l2)) with (40 + 40 * length l2)%nat
        by (unfold merge_cost; simpl; lia).
      iDestruct "Htc" as "[Htc _]".
      wp_tick_rec. wp_tick_let. wp_tick_match.
      iDestruct (is_list_tr_translation with "Hl2") as "[Hl2 %Heq2]".
      iApply "Post". rewrite list_merge_nil_l -Heq2. iFrame. }
    iDestruct "Hl1" as (p) "[-> Hl1]"; iDestruct "Hl1" as (t1) "[Hp Ht1]".
    destruct l2 as [|y l2].
    { iDestruct "Hl2" as %->.
      replace (merge_cost (length (x :: l1) + length (@nil Z)))
        with (80 + 40 * length l1)%nat by (unfold merge_cost; simpl; lia).
      iDestruct "Htc" as "[Htc _]".
      wp_tick_rec. wp_tick_let. wp_tick_match. wp_tick_match.
      wp_tick_inj.
      rewrite list_merge_nil_r.
      iApply "Post". simpl. iExists p. iSplit; first done. iExists t1. iFrame. }
    iDestruct "Hl2" as (q) "[-> Hl2]"; iDestruct "Hl2" as (t2) "[Hq Ht2]".
    replace (merge_cost (length (x :: l1) + length (y :: l2)))
      with (40 + merge_cost (length l1 + length (y :: l2)))%nat
      by (unfold merge_cost; simpl; lia).
    iDestruct "Htc" as "[Htc40 Htc]".
    wp_tick_rec. wp_tick_let. wp_tick_match. wp_tick_match.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    wp_tick_op.
    case_bool_decide as Hxy.
    + wp_tick_if. wp_tick_inj.
      wp_apply (IHm l1 (y :: l2) t1 (InjRV #q)
                    ltac:(simpl in Hlen |- *; lia) with "Htickinv [Ht1 Hq Ht2 Htc]").
      { iFrame "Ht1 Htc". iExists q. iSplit; first done. iExists t2. iFrame. }
      iIntros (w) "Hw".
      iDestruct (is_list_tr_translation with "Hw") as "[Hw %Hweq]".
      wp_tick_pair. wp_tick. wp_alloc r as "Hr". wp_tick_inj.
      iApply "Post". rewrite list_merge_cons decide_True //.
      simpl. iExists r. iSplit; first done. iExists w. rewrite -Hweq. iFrame.
    + wp_tick_if. wp_tick_inj.
      wp_apply (IHm (x :: l1) l2 (InjRV #p) t2
                    ltac:(simpl in Hlen |- *; lia) with "Htickinv [Hp Ht1 Ht2 Htc]").
      { iFrame "Ht2". iSplitL "Hp Ht1".
        - iExists p. iSplit; first done. iExists t1. iFrame.
        - iApply (TC_le with "Htc"). unfold merge_cost; simpl; lia. }
      iIntros (w) "Hw".
      iDestruct (is_list_tr_translation with "Hw") as "[Hw %Hweq]".
      wp_tick_pair. wp_tick. wp_alloc r as "Hr". wp_tick_inj.
      iApply "Post". rewrite list_merge_cons decide_False //.
      simpl. iExists r. iSplit; first done. iExists w. rewrite -Hweq. iFrame.
Qed.

Lemma merge_list_spec' (m : nat) (l1 l2 : list Z) (v1 v2 u1 u2 : val) :
  (length l1 + length l2 ≤ m)%nat → u1 = « v1 »%V → u2 = « v2 »%V →
  TC_invariant -∗
  {{{ is_list_tr l1 v1 ∗ is_list_tr l2 v2
      ∗ TC (merge_cost (length l1 + length l2)) }}}
    (tick (tick « merge_list »%V u1) u2)%E
  {{{ w, RET w ; is_list_tr (list_merge Z.le l1 l2) w }}}.
Proof. intros Hm -> ->. by apply (merge_list_spec m). Qed.

(** Constants for the closed-form bound: [msort] on a list of length [n]
    costs at most [KM * (n * ⌈log2 n⌉) + KE] ticks. *)
Definition KM : nat := 220.
Definition KE : nat := 40.


Local Instance Z_le_total : Total Z.le.
Proof. intros x y. lia. Qed.

Lemma msort_spec (m : nat) : ∀ (n : nat) (l : list Z) (v u : val),
  length l = n → (n ≤ m)%nat → u = « v »%V →
  TC_invariant -∗
  {{{ is_list_tr l v ∗ TC (msort_cost KM KE n) }}}
    (tick « msort »%V u)%E
  {{{ w, RET w ; ∃ l', ⌜l' ≡ₚ l⌝ ∗ ⌜Sorted Z.le l'⌝ ∗ is_list_tr l' w }}}.
Proof.
  induction m as [|m IHm].
  - iIntros (n l v u Hn Hlen ->) "#Htickinv".
    iIntros "!#" (Φ) "(Hl & Htc) Post".
    destruct l as [|x l]; last (simpl in Hn; lia).
    simpl in Hn; subst n.
    iDestruct "Hl" as %->.
    replace (msort_cost KM KE 0) with 40%nat
      by (unfold msort_cost, KM, KE; simpl; lia).
    wp_tick_rec. wp_tick_match. wp_tick_inj.
    iApply "Post". iExists []. simpl. auto.
  - iIntros (n l v u Hn Hlen ->) "#Htickinv".
    iIntros "!#" (Φ) "(Hl & Htc) Post".
    destruct l as [|x l].
    { simpl in Hn; subst n. iDestruct "Hl" as %->.
      replace (msort_cost KM KE 0) with 40%nat
        by (unfold msort_cost, KM, KE; simpl; lia).
      wp_tick_rec. wp_tick_match. wp_tick_inj.
      iApply "Post". iExists []. simpl. auto. }
    iDestruct "Hl" as (p) "[-> Hl]"; iDestruct "Hl" as (t) "[Hp Ht]".
    destruct l as [|y l].
    { simpl in Hn; subst n. iDestruct "Ht" as %->.
      replace (msort_cost KM KE 1) with 40%nat
        by (unfold msort_cost, KM, KE; simpl; lia).
      wp_tick_rec. wp_tick_match.
      wp_tick_load. wp_tick_proj. wp_tick_let.
      wp_tick_match. wp_tick_inj.
      iApply "Post". iExists [x]. simpl.
      iSplit; first done. iSplit; first (iPureIntro; by repeat constructor).
      iExists p. iSplit; first done. iExists NONEV. simpl_trans. iFrame. done. }
    iDestruct "Ht" as (q) "[-> Ht]"; iDestruct "Ht" as (t2) "[Hq Ht2]".
    destruct (split2_lengths (x :: y :: l)) as (Hsum & Hba & Hab1).
    remember (length (split2 (x :: y :: l)).1) as a eqn:Ha.
    remember (length (split2 (x :: y :: l)).2) as b eqn:Hb.
    assert (2 ≤ n) as Hn2 by (rewrite -Hn; simpl; lia).
    assert (a + b = n) as Hab by (rewrite Hsum; exact Hn).
    (* Split the credits: one level of work, plus the two halves. *)
    iAssert (TC (80 * n + 100 + msort_cost KM KE a + msort_cost KM KE b))
      with "[Htc]" as "Htc".
    { iApply (TC_le with "Htc").
      apply (msort_cost_step KM KE 80 100); unfold KM, KE; lia. }
    replace (80 * n + 100)%nat with (20 + (split_cost n + merge_cost n))%nat
      by (unfold split_cost, merge_cost; lia).
    iDestruct "Htc" as "[[[Hbody [Hsplitc Hmergec]] HtcA] HtcB]".
    wp_tick_rec. wp_tick_match.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    simpl_trans. wp_tick_match.
    wp_tick_inj.
    wp_apply (split_list_spec' n (x :: y :: l) (InjRV #p) _ Hn ltac:(by simpl_trans)
                with "Htickinv [Hp Hq Ht2 Hsplitc]").
    { iFrame "Hsplitc". iExists p. iSplit; first done. iExists (InjRV #q).
      iFrame "Hp". iExists q. iSplit; first done. iExists t2. iFrame. }
    iIntros (u1 u2) "[Hu1 Hu2]".
    wp_tick_let. wp_tick_proj.
    iDestruct (is_list_tr_translation with "Hu2") as "[Hu2 %Hu2eq]".
    wp_apply (IHm b (split2 (x :: y :: l)).2 u2 u2 (eq_sym Hb) ltac:(lia) Hu2eq
                with "Htickinv [$Hu2 $HtcB]").
    iIntros (w2) "H2". iDestruct "H2" as (l2') "(%Hperm2 & %Hsort2 & Hl2')".
    wp_tick_proj.
    iDestruct (is_list_tr_translation with "Hu1") as "[Hu1 %Hu1eq]".
    wp_apply (IHm a (split2 (x :: y :: l)).1 u1 u1 (eq_sym Ha) ltac:(lia) Hu1eq
                with "Htickinv [$Hu1 $HtcA]").
    iIntros (w1) "H1". iDestruct "H1" as (l1') "(%Hperm1 & %Hsort1 & Hl1')".
    replace (merge_cost n) with (merge_cost (length l1' + length l2')).
    2:{ f_equal. rewrite (Permutation_length Hperm1) (Permutation_length Hperm2).
        rewrite -Ha -Hb. exact Hab. }
    iDestruct (is_list_tr_translation with "Hl1'") as "[Hl1' %Hw1eq]".
    iDestruct (is_list_tr_translation with "Hl2'") as "[Hl2' %Hw2eq]".
    wp_apply (merge_list_spec' (length l1' + length l2') l1' l2' w1 w2 w1 w2
                ltac:(lia) Hw1eq Hw2eq with "Htickinv [$Hl1' $Hl2' $Hmergec]").
    iIntros (w) "Hw".
    iApply "Post". iExists (list_merge Z.le l1' l2'). iFrame.
    iSplit.
    + iPureIntro.
      etrans; first apply merge_Permutation.
      etrans; first (apply Permutation_app; [exact Hperm1 | exact Hperm2]).
      apply split2_perm.
    + iPureIntro. apply Sorted_list_merge; [apply Z_le_total | exact Hsort1 | exact Hsort2].
Qed.

(** * End-to-end: sort a generated list and sum it

    The whole program is closed, so the adequacy theorem of the time-credit
    logic turns the Hoare triple into a statement about the number of steps
    the *untranslated* program takes. *)

Definition msort_prgm (n : nat) : expr := sum_list (msort (make_list #n)).

Definition msort_prgm_cost (n : nat) : nat :=
  ((4 + 7 * n) + msort_cost KM KE n + (4 + 13 * n))%nat.

Lemma sum_list_coq_perm (l1 l2 : list Z) :
  l1 ≡ₚ l2 → sum_list_coq l1 = sum_list_coq l2.
Proof. induction 1; simpl; lia. Qed.

Lemma msort_prgm_translation_spec (n : nat) :
  TC_invariant -∗
  {{{ TC (msort_prgm_cost n) }}}
    « msort_prgm n »
  {{{ v, RET v ; ⌜v = #(n * (n + 1) / 2)⌝ }}}.
Proof.
  iIntros "#Htickinv !#" (Φ) "Htc Post".
  unfold msort_prgm, msort_prgm_cost.
  iDestruct "Htc" as "[[Htc_make Htc_sort] Htc_sum]".
  simpl_trans.
  wp_apply (make_list_translation_spec with "Htickinv Htc_make").
  iIntros (v) "Hl".
  rewrite is_list_is_list_tr.
  iDestruct (is_list_tr_translation with "Hl") as "[Hl %Hveq]".
  wp_apply (msort_spec n n (make_list_coq n) v v
              (length_make_list_coq n) (Nat.le_refl n) Hveq
              with "Htickinv [$Hl $Htc_sort]").
  iIntros (w) "H". iDestruct "H" as (l') "(%Hperm & %Hsort & Hl')".
  assert (length l' = n) as Hlen'.
  { rewrite (Permutation_length Hperm). apply length_make_list_coq. }
  iDestruct (is_list_tr_translation with "Hl'") as "[Hl' %Hweq]".
  replace (4 + 13 * n)%nat with (4 + 13 * length l')%nat by (rewrite Hlen'; lia).
  rewrite {2}Hweq.
  wp_apply (sum_list_translation_spec l' w with "Htickinv [$Hl' $Htc_sum]").
  iIntros "_".
  iApply ("Post" with "[%]"). repeat f_equal.
  rewrite (sum_list_coq_perm _ _ Hperm). apply sum_list_coq_make_list_coq.
Qed.

End proofs.

Lemma msort_prgm_timed_spec (n : nat) (σ : state) `{!timeCreditHeapPreG Σ} :
    adequate NotStuck (msort_prgm n) σ (λ v _, v = #(n * (n + 1) / 2))
  ∧ bounded_time (msort_prgm n) σ (msort_prgm_cost n).
Proof.
  apply (spec_tctranslation__adequate_and_bounded' (Σ:=Σ)).
  - by intros _ ->.
  - intros HtcHeapG. apply msort_prgm_translation_spec.
  - assumption.
Qed.
