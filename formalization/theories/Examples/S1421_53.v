(** * S1421_53 — verdict: SOUND_LOOSE (the label holds but names a size
      parameter the program does not have)

    BigO(Bench) time_complexity_test_set
      solution_id   1421_53
      problem_name  p02899 AtCoder Beginner Contest 142 - Go to School
      fitted label  O(n+m)

    Source solution (one space added after "print(" — the Python is
    "print(*B)", and that "(*" would open a nested Coq comment):

      N = int(input())
      A = [int(i) for i in input().split()]
      B=[0]*N
      for i in range(N):
        B[A[i]-1]=i+1
      print( *B)

    COST MODEL. One tick per element parsed by the list comprehension, and one
    per iteration of the [for]. B is a Python list, so [B[k]=v] is O(1) — it
    is modelled as a function [nat -> nat] with pointwise update, NOT as a
    Coq list. Modelling it as a list would make each write O(n) and would
    "prove" this program quadratic, which is the single easiest way to get a
    wrong answer out of this whole setup. Allocating [B=[0]*N] is charged
    nothing; adding N ticks for it changes no constant that matters.

    There is only one input size here: N, which is also the length of A. The
    fitted O(n+m) is therefore sound — O(n) is contained in O(n+m) — but its
    second parameter is spurious. Worth cataloguing separately from a wrong
    label: it says something about how the framework picks size variables from
    the dataclass, not about the program. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From BigOBench Require Import Cost Asymptotic.

(** Pointwise update — a Python list store, O(1). *)
Definition upd (b : nat -> nat) (k v : nat) : nat -> nat :=
  fun x => if Nat.eqb x k then v else b x.

(** [A = [int(i) for i in input().split()]] — one tick per element. *)
Fixpoint parse (l : list nat) : M (list nat) :=
  match l with
  | [] => ret []
  | x :: r => tick (t <- parse r ;; ret (x :: t))
  end.

Lemma cost_parse : forall l, cost (parse l) = length l.
Proof.
  intros l. induction l as [| x r IH]; [reflexivity|].
  simpl parse. rewrite cost_tick, cost_bind, IH. simpl. lia.
Qed.

Lemma val_parse : forall l, val (parse l) = l.
Proof.
  intros l. induction l as [| x r IH]; [reflexivity|].
  simpl parse. rewrite val_tick, val_bind, IH. reflexivity.
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

Theorem cost_solve : forall a, cost (solve a) = 2 * length a.
Proof.
  intros a. unfold solve.
  rewrite cost_bind, cost_parse, val_parse, cost_fill. lia.
Qed.

Definition T (n : nat) : nat := cost (solve (List.seq 0 n)).

Lemma T_eq : forall n, T n = 2 * n.
Proof.
  intros n. unfold T. rewrite cost_solve, List.seq_length. reflexivity.
Qed.

(** ** The true class: one parameter, linear. *)
Theorem true_class : Theta T (fun n => n).
Proof.
  split; [exists 2, 0 | exists 1, 0]; intros n _; rewrite T_eq; lia.
Qed.

(** ** The fitted label is sound: O(n) is inside O(n+m). *)
Theorem fitted_label_sound :
  BigO2 (fun n _ => T n) (fun n m => n + m).
Proof.
  apply (BigO2_of_BigO_left T (fun n => n)).
  exists 2, 0. intros n _. rewrite T_eq. lia.
Qed.

(** ** ...but loose: the cost does not grow with the second parameter at all.
       Fixing [n] and letting [m] run, the true cost is flat. *)
Theorem second_parameter_is_spurious :
  forall n m m',
    (fun (n _ : nat) => T n) n m = (fun (n _ : nat) => T n) n m'.
Proof. reflexivity. Qed.
