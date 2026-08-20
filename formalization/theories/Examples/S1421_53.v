(** * S1421_53 — verdict: SOUND_LOOSE

    time_complexity_test_set: solution_id 1421_53,
    "p02899 AtCoder Beginner Contest 142 - Go to School", fitted O(n+m).

    Source (one space added after "print(" — the Python is "print(*B)", and
    that "(*" would open a nested Rocq comment):

      N = int(input())
      A = [int(i) for i in input().split()]
      B=[0]*N
      for i in range(N):
        B[A[i]-1]=i+1
      print( *B)

    COST MODEL. One tick per iteration of the [for]. Reading and parsing the
    input is free, per the convention in [Cost.v]; [parse] is modelled so the
    step is visible, but charged nothing. B is a Python list, so [B[k]=v] is
    O(1): B is modelled as [nat -> nat] with pointwise update, NOT as a Rocq
    list, which would make each store O(n) and "prove" this program quadratic.
    Allocating [B=[0]*N] is charged nothing.

    There is one input size, N, which is also the length of A. The fitted
    O(n+m) is sound — O(n) is contained in it — but names a second parameter
    the program has nothing to vary with: a fact about how size variables are
    picked from the dataclass, not about the program. [true_class] is the
    statement that matters, one parameter and linear. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From BigOBench Require Import Cost Asymptotic.

(** Pointwise update — a Python list store, O(1). *)
Definition upd (b : nat -> nat) (k v : nat) : nat -> nat :=
  fun x => if Nat.eqb x k then v else b x.

(** [A = [int(i) for i in input().split()]] — input parsing, charged nothing. *)
Fixpoint parse (l : list nat) : M (list nat) :=
  match l with
  | [] => ret []
  | x :: r => t <- parse r ;; ret (x :: t)
  end.

Lemma cost_parse : forall l, cost (parse l) = 0.
Proof.
  intros l. induction l as [| x r IH]; [reflexivity|].
  simpl parse. rewrite cost_bind, IH. reflexivity.
Qed.

Lemma val_parse : forall l, val (parse l) = l.
Proof.
  intros l. induction l as [| x r IH]; [reflexivity|].
  simpl parse. rewrite val_bind, IH. reflexivity.
Qed.

(** [for i in range(N): B[A[i]-1]=i+1] *)
Fixpoint fill (i : nat) (a : list nat) (b : nat -> nat) : M (nat -> nat) :=
  match a with
  | [] => ret b
  | x :: r => tick (fill (S i) r (upd b (x - 1) (i + 1)))
  end.

Lemma cost_fill : forall a i b, cost (fill i a b) = length a.
Proof.
  intros a. induction a as [| x r IH]; intros i b; [reflexivity|].
  simpl fill. rewrite cost_tick, IH. reflexivity.
Qed.

Definition solve (a : list nat) : M (nat -> nat) :=
  a' <- parse a ;; fill 0 a' (fun _ => 0).

Theorem cost_solve : forall a, cost (solve a) = length a.
Proof.
  intros a. unfold solve.
  rewrite cost_bind, cost_parse, val_parse, cost_fill. lia.
Qed.

Definition T (n : nat) : nat := cost (solve (List.seq 0 n)).

Lemma T_eq : forall n, T n = n.
Proof.
  intros n. unfold T. rewrite cost_solve, List.length_seq. reflexivity.
Qed.

(** ** The true class: one parameter, linear. *)
Theorem true_class : Theta T (fun n => n).
Proof.
  split; [exists 1, 0 | exists 1, 0]; intros n _; rewrite T_eq; lia.
Qed.

(** ** The fitted label is sound: O(n) is inside O(n+m). *)
Theorem fitted_label_sound :
  BigO2 (fun n _ => T n) (fun n m => n + m).
Proof.
  apply (BigO2_of_BigO_left T (fun n => n)).
  exists 1, 0. intros n _. rewrite T_eq. lia.
Qed.
