(** * Alt/Deep.v — a deep embedding: syntax, and a big-step semantics that
      counts steps.

    THE ALTERNATIVE TO THE COST MONAD, AND WHY IT MATTERS HERE.

    In [Cost.v] the cost model is a per-example judgement: I decide where the
    [tick]s go in each [Examples/S*.v], and nothing checks that decision. The
    README calls that the whole attack surface, and it is.

    Here the cost model lives in the semantics instead — one place,
    reviewable once, shared by every program written in the language. An
    example file becomes a syntax tree with no cost annotations at all, so
    there is nothing left to get wrong per example. That is the entire point
    of paying for a deep embedding.

    Trade-offs, honestly:

    + Cost model stated once, not per file.
    + Relational semantics: no fuel, no termination obligation. A program that
      diverges simply has no derivation, rather than needing a fuel parameter
      and an adequacy lemma (compare [S5_100.v]'s [run_finishes]).
    + The program is data, so you can quantify over programs — "no program in
      this fragment costs more than ..." is expressible. The monad cannot say
      that.
    - Much heavier per example: the program must be encoded as a tree, and
      every proof goes through inversion on derivations.
    - The language must actually cover the Python. This one does not have
      [while], so it cannot express [S5_100.v]. Extending it is real work.
    - Care is needed to state cost theorems so they quantify over every
      derivation, not merely assert that one exists — see the note below.

    THE COST MODEL, in one place: [ECount] charges one step per character
    scanned, matching Python's [str.count]. Everything else is free. That is
    the same model [Examples/S2389_139.v] applies by hand, which is what makes
    the cross-check in [S2389_139_Deep.v] meaningful. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(** ** Values, state.

    State is an association list rather than [nat -> V] so that state equality
    is ordinary list equality; reasoning about [nat -> V] states would need
    functional extensionality, and this development adds no axioms. *)

Inductive V : Type :=
  | VN : nat -> V
  | VS : list nat -> V.

Definition state := list (nat * V).

Fixpoint lookup (s : state) (x : nat) : V :=
  match s with
  | [] => VN 0
  | (y, v) :: r => if Nat.eqb x y then v else lookup r x
  end.

Definition update (x : nat) (v : V) (s : state) : state := (x, v) :: s.

Lemma lookup_update_eq : forall x v s, lookup (update x v s) x = v.
Proof. intros x v s. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_update_neq : forall x y v s,
    x <> y -> lookup (update y v s) x = lookup s x.
Proof.
  intros x y v s Hne. simpl.
  destruct (Nat.eqb_spec x y); [contradiction | reflexivity].
Qed.

(** ** Syntax.

    Minimal: exactly what [S2389_139] needs. [SForVals] is an internal form —
    the loop over an already-evaluated list — which lets the whole semantics
    be one inductive instead of a mutual one. *)

Inductive expr : Type :=
  | EVar   : nat -> expr
  | ENat   : nat -> expr
  | ECount : expr -> expr -> expr      (* e1.count(e2) *)
  | EMod   : expr -> expr -> expr
  | EEq    : expr -> expr -> expr.

Inductive stmt : Type :=
  | SSkip    : stmt
  | SAssign  : nat -> expr -> stmt
  | SSeq     : stmt -> stmt -> stmt
  | SIf      : expr -> stmt -> stmt -> stmt
  | SForEach : nat -> expr -> stmt -> stmt        (* for x in e: body *)
  | SForVals : nat -> list nat -> stmt -> stmt.   (* internal *)

Fixpoint countocc (x : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | y :: r => (if Nat.eqb x y then 1 else 0) + countocc x r
  end.

(** ** Semantics.

    [evalE s e v c] : in state [s], expression [e] evaluates to [v] at cost
    [c]. Likewise [evalS s t s' c] for statements. *)

Inductive evalE : state -> expr -> V -> nat -> Prop :=
  | EV_Var : forall s x,
      evalE s (EVar x) (lookup s x) 0
  | EV_Nat : forall s n,
      evalE s (ENat n) (VN n) 0
  (* THE cost rule: scanning the string costs its length. *)
  | EV_Count : forall s e1 e2 str ch c1 c2,
      evalE s e1 (VS str) c1 ->
      evalE s e2 (VN ch) c2 ->
      evalE s (ECount e1 e2) (VN (countocc ch str)) (c1 + c2 + length str)
  | EV_Mod : forall s e1 e2 a b c1 c2,
      evalE s e1 (VN a) c1 ->
      evalE s e2 (VN b) c2 ->
      evalE s (EMod e1 e2) (VN (a mod b)) (c1 + c2)
  | EV_Eq : forall s e1 e2 a b c1 c2,
      evalE s e1 (VN a) c1 ->
      evalE s e2 (VN b) c2 ->
      evalE s (EEq e1 e2) (VN (if Nat.eqb a b then 1 else 0)) (c1 + c2).

Inductive evalS : state -> stmt -> state -> nat -> Prop :=
  | ES_Skip : forall s,
      evalS s SSkip s 0
  | ES_Assign : forall s x e v c,
      evalE s e v c ->
      evalS s (SAssign x e) (update x v s) c
  | ES_Seq : forall s t1 t2 s1 s2 c1 c2,
      evalS s t1 s1 c1 ->
      evalS s1 t2 s2 c2 ->
      evalS s (SSeq t1 t2) s2 (c1 + c2)
  | ES_IfTrue : forall s e t1 t2 s' c c',
      evalE s e (VN 1) c ->
      evalS s t1 s' c' ->
      evalS s (SIf e t1 t2) s' (c + c')
  | ES_IfFalse : forall s e t1 t2 s' c c' n,
      evalE s e (VN n) c ->
      n <> 1 ->
      evalS s t2 s' c' ->
      evalS s (SIf e t1 t2) s' (c + c')
  | ES_ForEach : forall s x e body vs s' c1 c2,
      evalE s e (VS vs) c1 ->
      evalS s (SForVals x vs body) s' c2 ->
      evalS s (SForEach x e body) s' (c1 + c2)
  | ES_ForNil : forall s x body,
      evalS s (SForVals x [] body) s 0
  | ES_ForCons : forall s x v vs body s1 s2 c1 c2,
      evalS (update x (VN v) s) body s1 c1 ->
      evalS s1 (SForVals x vs body) s2 c2 ->
      evalS s (SForVals x (v :: vs) body) s2 (c1 + c2).

(** ** No determinism lemma, deliberately.

    A relational semantics tempts you to prove [evalS] deterministic so that
    "there is a derivation of cost c" upgrades to "the cost is c". It is not
    needed here: the example theorem is stated as

      forall s' c, evalS (init str) prog s' c -> c = length str * length str

    which already quantifies over EVERY derivation. Nothing cheap can hide —
    if some derivation had a smaller cost, that statement would be false.
    Determinism would be required only to conclude that a derivation exists,
    which is a different claim and not one the verdict rests on. *)
