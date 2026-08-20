(** * Cost.v — a writer monad in [nat]: an algorithm and its cost, defined once.

    A separately-written [cost] function has nothing tying it to the algorithm
    it claims to measure, and [cost := fun _ => 0] would prove every bound.
    Here [cost] is a projection of the term that computes the value, so it
    cannot drift.

    What it does NOT give is fidelity to Python: where the [tick]s go is a
    modelling decision, stated in each example's header, and the only place
    unsoundness can still enter.

    INPUT AND OUTPUT ARE NOT CHARGED. Cost counts the work a solution does once
    its input is available. Reading stdin, parsing a line into a list, and
    printing the answer are free. Every program that reads its input is
    Omega(input size), so charging the read makes that trivial fact the finding
    whenever the real work is smaller — which is exactly what happened to the
    withdrawn entry 450_204 (see [Examples/S450_204.v]). Each example header
    restates the rule where it bites. *)

From Stdlib Require Import Arith Lia.

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

(** ** Projection lemmas — all definitional, but rewriting beats [simpl] once
       the terms get large. *)

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

    Not used by the examples. They justify reading [<- ;;] as sequencing:
    rephrasing a program must not change its cost. *)

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
