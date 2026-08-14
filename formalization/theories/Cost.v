(** * Cost.v — a writer monad in [nat], for defining an algorithm and its
      cost in one place.

    The point of the monad is soundness of the *setup*, not of the proofs.
    If a cost function is written as a separate definition next to the
    algorithm, nothing connects the two: [cost := fun _ => 0] typechecks and
    every bound becomes provable. Here the cost is a projection of the same
    term that computes the value, so it cannot drift from the code.

    What the monad does NOT give you is fidelity to Python. Where the [tick]s
    go is a modelling decision, and it is the only place unsoundness can now
    enter. Every example file states its cost model in a header comment. *)

From Coq Require Import Arith Lia.

(** A computation returning [A] together with the number of steps it took. *)
Record M (A : Type) : Type := Mk { val : A ; cost : nat }.

Arguments Mk {A} _ _.
Arguments val {A} _.
Arguments cost {A} _.

Definition ret {A} (a : A) : M A := Mk a 0.

Definition bind {A B} (m : M A) (f : A -> M B) : M B :=
  Mk (val (f (val m))) (cost m + cost (f (val m))).

(** Charge one step. *)
Definition tick {A} (m : M A) : M A := Mk (val m) (S (cost m)).

(** Charge [n] steps — for modelling a primitive whose cost is not 1
    (a Python slice, a dict rehash, an int multiplication on bignums). *)
Definition charge {A} (n : nat) (m : M A) : M A := Mk (val m) (n + cost m).

Declare Scope cost_scope.
Delimit Scope cost_scope with cost.
Open Scope cost_scope.

Notation "x <- e ;; b" := (bind e (fun x => b))
  (at level 61, e at next level, right associativity) : cost_scope.

(** ** Projection lemmas — all definitional, but rewriting is easier than
       [simpl] once the terms get large. *)

Lemma val_ret : forall {A} (a : A), val (ret a) = a.
Proof. reflexivity. Qed.

Lemma cost_ret : forall {A} (a : A), cost (ret a) = 0.
Proof. reflexivity. Qed.

Lemma val_bind : forall {A B} (m : M A) (f : A -> M B),
    val (bind m f) = val (f (val m)).
Proof. reflexivity. Qed.

Lemma cost_bind : forall {A B} (m : M A) (f : A -> M B),
    cost (bind m f) = cost m + cost (f (val m)).
Proof. reflexivity. Qed.

Lemma val_tick : forall {A} (m : M A), val (tick m) = val m.
Proof. reflexivity. Qed.

Lemma cost_tick : forall {A} (m : M A), cost (tick m) = S (cost m).
Proof. reflexivity. Qed.

Lemma val_charge : forall {A} n (m : M A), val (charge n m) = val m.
Proof. reflexivity. Qed.

Lemma cost_charge : forall {A} n (m : M A), cost (charge n m) = n + cost m.
Proof. reflexivity. Qed.

(** ** Monad laws.

    Not used by the examples, but they are what justifies reading [<- ;;] as
    sequencing: rearranging a program's phrasing must not change its cost. *)

Lemma bind_ret_l : forall {A B} (a : A) (f : A -> M B), bind (ret a) f = f a.
Proof. intros A B a f. unfold bind, ret. simpl. destruct (f a); reflexivity. Qed.

Lemma bind_ret_r : forall {A} (m : M A), bind m (fun a => ret a) = m.
Proof.
  intros A m. unfold bind, ret. destruct m as [v c]. simpl.
  f_equal. lia.
Qed.

Lemma bind_assoc : forall {A B C} (m : M A) (f : A -> M B) (g : B -> M C),
    bind (bind m f) g = bind m (fun a => bind (f a) g).
Proof. intros. unfold bind. simpl. f_equal. lia. Qed.

(** Cost is monotone under sequencing: no step is ever refunded. *)
Lemma cost_bind_ge_l : forall {A B} (m : M A) (f : A -> M B),
    cost m <= cost (bind m f).
Proof. intros. rewrite cost_bind. lia. Qed.
