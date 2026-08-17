(** * Asymptotic.v — big-O over [nat], univariate and bivariate.

    Deliberately the naive definition. Two limits:

    - [BigO2] uses the product filter ([n] and [m] to infinity independently).
      That makes [O(n*m)] and [O(n+m)] mean what you expect, but multivariate
      big-O has real pitfalls; Gueneau/Chargueraud/Pottier, "A Fistful of
      Dollars" (ESOP 2018) does it properly with filters. Copy that if this
      file is outgrown.
    - Bounds are over [nat -> nat], so they cannot mention the shape of an
      input, only its size. Each example fixes a size-indexed family and says
      so when the worst case is not attained on it. *)

From Stdlib Require Import Arith Lia.

Definition BigO (f g : nat -> nat) : Prop :=
  exists c n0, forall n, n0 <= n -> f n <= c * g n.

Definition BigOmega (f g : nat -> nat) : Prop :=
  exists c n0, forall n, n0 <= n -> g n <= c * f n.

Definition Theta (f g : nat -> nat) : Prop := BigO f g /\ BigOmega f g.

Definition BigO2 (f g : nat -> nat -> nat) : Prop :=
  exists c p, forall n m, p <= n -> p <= m -> f n m <= c * g n m.

(** ** Introduction *)

Lemma BigO_intro : forall f g c n0,
    (forall n, n0 <= n -> f n <= c * g n) -> BigO f g.
Proof. intros f g c n0 H. exists c, n0. exact H. Qed.

Lemma BigO_of_global : forall f g c,
    (forall n, f n <= c * g n) -> BigO f g.
Proof. intros f g c H. exists c, 0. auto. Qed.

Lemma BigO_refl : forall f, BigO f f.
Proof. intros f. exists 1, 0. intros. lia. Qed.

Lemma Theta_refl : forall f, Theta f f.
Proof. split; apply BigO_refl. Qed.

Lemma BigO_trans : forall f g h, BigO f g -> BigO g h -> BigO f h.
Proof.
  intros f g h [c1 [n1 H1]] [c2 [n2 H2]].
  exists (c1 * c2), (Nat.max n1 n2). intros n Hn.
  assert (n1 <= n) by lia. assert (n2 <= n) by lia.
  specialize (H1 n ltac:(lia)). specialize (H2 n ltac:(lia)).
  nia.
Qed.

(** ** Refutation.

    The lemma that makes a *disagreement* with a fitted label provable rather
    than merely asserted: to refute [BigO f g], exhibit arbitrarily large [n]
    beating any constant. *)

Lemma not_BigO : forall f g,
    (forall c n0, exists n, n0 <= n /\ c * g n < f n) -> ~ BigO f g.
Proof.
  intros f g H [c [n0 Hb]].
  destruct (H c n0) as [n [Hn Hlt]].
  specialize (Hb n Hn). lia.
Qed.

Lemma not_BigOmega : forall f g,
    (forall c n0, exists n, n0 <= n /\ c * f n < g n) -> ~ BigOmega f g.
Proof.
  intros f g H [c [n0 Hb]].
  destruct (H c n0) as [n [Hn Hlt]].
  specialize (Hb n Hn). lia.
Qed.

(** ** Relating the univariate and bivariate forms.

    Used by examples whose fitted label names two size parameters but whose
    code only has one. [O(n)] is contained in [O(n+m)], so such a label is
    sound-but-loose rather than wrong. *)

Lemma BigO2_of_BigO_left : forall f g,
    BigO f g -> BigO2 (fun n _ => f n) (fun n m => g n + m).
Proof.
  intros f g [c [n0 H]]. exists c, n0. intros n m Hn Hm.
  specialize (H n Hn). nia.
Qed.
