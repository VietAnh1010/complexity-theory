(** * Alt/Deep.v — a deep embedding: syntax, and a big-step semantics that
      counts steps.

    An alternative to the cost monad of [Cost.v]. There the cost model is a
    per-example judgement — where the [tick]s go in each [Examples/S*.v], with
    nothing checking that decision. Here it lives in the semantics: one place,
    reviewed once, shared by every program in the language. An example file is
    then a syntax tree carrying no cost annotations at all.

    Trade-offs:

    + Cost model stated once, not per file.
    + No fuel and no termination obligation. A diverging program simply has no
      derivation, where the monad needs a fuel parameter plus an adequacy
      lemma (compare [S5_100.v]'s [run_finishes]).
    + The program is data, so one can quantify over programs — "no program in
      this fragment costs more than ..." is expressible. The monad cannot say
      that.
    - Heavier per example: the program must be encoded as a tree and every
      proof goes through inversion on derivations.
    - With [SWhile] the semantics is not total, so a cost theorem about a loop
      is conditional on a derivation existing. Each example therefore carries
      a worked witness ([run_aa], [run_4]) to rule out vacuity.
    - Cost theorems must be stated to quantify over every derivation, not to
      assert that one exists — see the note at the end of this file.

    THE COST MODEL, in one place: [ECount] charges one step per character
    scanned, matching Python's [str.count]; [ES_WhileTrue] charges one step
    per iteration. Everything else is free. *)

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

    Minimal: what the worked examples need, no more. [SForVals] is an internal
    form — the loop over an already-evaluated list — which lets the whole
    semantics be one inductive rather than a mutual one. *)

Inductive expr : Type :=
  | EVar   : nat -> expr
  | ENat   : nat -> expr
  | ECount : expr -> expr -> expr      (* e1.count(e2) *)
  | EMod   : expr -> expr -> expr
  | EEq    : expr -> expr -> expr
  | EAdd   : expr -> expr -> expr
  | ESub   : expr -> expr -> expr
  | ELt    : expr -> expr -> expr.

Inductive stmt : Type :=
  | SSkip    : stmt
  | SAssign  : nat -> expr -> stmt
  | SSeq     : stmt -> stmt -> stmt
  | SIf      : expr -> stmt -> stmt -> stmt
  | SForEach : nat -> expr -> stmt -> stmt        (* for x in e: body *)
  | SForVals : nat -> list nat -> stmt -> stmt    (* internal *)
  | SWhile   : expr -> stmt -> stmt.

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
      evalE s (EEq e1 e2) (VN (if Nat.eqb a b then 1 else 0)) (c1 + c2)
  | EV_Add : forall s e1 e2 a b c1 c2,
      evalE s e1 (VN a) c1 -> evalE s e2 (VN b) c2 ->
      evalE s (EAdd e1 e2) (VN (a + b)) (c1 + c2)
  | EV_Sub : forall s e1 e2 a b c1 c2,
      evalE s e1 (VN a) c1 -> evalE s e2 (VN b) c2 ->
      evalE s (ESub e1 e2) (VN (a - b)) (c1 + c2)
  | EV_Lt : forall s e1 e2 a b c1 c2,
      evalE s e1 (VN a) c1 -> evalE s e2 (VN b) c2 ->
      evalE s (ELt e1 e2) (VN (if Nat.ltb a b then 1 else 0)) (c1 + c2).

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
      evalS s (SForVals x (v :: vs) body) s2 (c1 + c2)
  (* One step per iteration, matching the [tick] in [S5_100.v]'s loop. *)
  | ES_WhileTrue : forall s g body s1 s' cg cb cr,
      evalE s g (VN 1) cg ->
      evalS s body s1 cb ->
      evalS s1 (SWhile g body) s' cr ->
      evalS s (SWhile g body) s' (S (cg + cb + cr))
  | ES_WhileFalse : forall s g body m cg,
      evalE s g (VN m) cg -> m <> 1 ->
      evalS s (SWhile g body) s cg.

(** Variable lookup with the value given explicitly. [apply EV_Var] leaves the
    value as [lookup s x], which the unifier will not reduce against an evar;
    this form lets [reflexivity] compute it. *)
Lemma EV_Var' : forall s x v, lookup s x = v -> evalE s (EVar x) v 0.
Proof. intros s x v <-. apply EV_Var. Qed.

(** ** Shared proof tactics.

    All three match on hypothesis SHAPE rather than on [inversion]'s generated
    names, which shift between Rocq versions.

    - [peelE] eliminates every expression derivation in the context.
    - [reconcile] / [reconcileN] merge two lookups of the same variable; the
      [constr_eq] guard stops them pairing a hypothesis with itself.
    - [inv_stmt] eliminates one statement derivation, named by its statement. *)

Ltac peelE :=
  repeat match goal with
         | H : evalE _ (ECount _ _) _ _ |- _ => inversion H; subst; clear H
         | H : evalE _ (EMod _ _)   _ _ |- _ => inversion H; subst; clear H
         | H : evalE _ (EEq _ _)    _ _ |- _ => inversion H; subst; clear H
         | H : evalE _ (EAdd _ _)   _ _ |- _ => inversion H; subst; clear H
         | H : evalE _ (ESub _ _)   _ _ |- _ => inversion H; subst; clear H
         | H : evalE _ (ELt _ _)    _ _ |- _ => inversion H; subst; clear H
         | H : evalE _ (ENat _)     _ _ |- _ => inversion H; subst; clear H
         | H : evalE _ (EVar _)     _ _ |- _ => inversion H; subst; clear H
         end.

Ltac reconcile :=
  repeat match goal with
         | H1 : lookup ?s ?x = VS ?a, H2 : lookup ?s ?x = VS ?b |- _ =>
             tryif constr_eq a b then fail
             else (assert (a = b) by congruence; subst)
         end.

Ltac reconcileN :=
  repeat match goal with
         | H1 : lookup ?s ?x = VN ?a, H2 : lookup ?s ?x = VN ?b |- _ =>
             tryif constr_eq a b then fail
             else (assert (a = b) by congruence; subst)
         end.

Ltac inv_stmt t :=
  match goal with H : evalS _ t _ _ |- _ => inversion H; subst; clear H end.

(** ** No determinism lemma, deliberately.

    A relational semantics tempts you to prove [evalS] deterministic so that
    "there is a derivation of cost c" upgrades to "the cost is c". It is not
    needed here: the example theorem is stated as

      forall s' c, evalS (init x) prog s' c -> c = <closed form>

    which already quantifies over EVERY derivation. Nothing cheap can hide —
    if some derivation had a smaller cost, that statement would be false.
    Determinism would be required only to conclude that a derivation exists,
    which is a different claim and not one the verdict rests on. *)
