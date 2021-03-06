(*
  Formalisation of the sequent calculus. Done according to the presentation
  found in [Girard, Taylor, Lafont 1989] Proofs and Types.
 *)

From Coq Require Import PeanoNat List.

Set Implicit Arguments.

Open Scope list_scope.
Import List.ListNotations.

Variable atom: Type.

Inductive formula: Type :=
| Var: nat -> formula
| Atom: atom -> formula
| Neg: formula -> formula
| Conj: formula -> formula -> formula
| Disj: formula -> formula -> formula
| Impl: formula -> formula -> formula
| Forall: formula -> formula
| Exists: formula -> formula.

Fixpoint subst (x: nat) (v: formula) (f: formula) :=
  match f with
  | Var n => if n =? x then v else Var n
  | Atom a => Atom a
  | Neg f' => subst x v f'
  | Conj f1 f2 => Conj (subst x v f1) (subst x v f2)
  | Disj f1 f2 => Disj (subst x v f1) (subst x v f2)
  | Impl f1 f2 => Impl (subst x v f1) (subst x v f2)
  | Forall f => Forall (subst (x + 1) v f)
  | Exists f => Exists (subst x v f)
  end.

Inductive sequent: list formula -> list formula -> Prop :=
| Ident c: sequent [c] [c]

(* Structural rules *)

| ExchL c d A A' B: sequent (A ++ c :: d :: A') B -> sequent (A ++ d :: c :: A') B
| ExchR c d A B B': sequent A (B ++ c :: d :: B') -> sequent A (B ++ d :: c :: B')

| WeakL c A B: sequent A B -> sequent (c :: A) B
| WeakR d A B: sequent A B -> sequent A (d :: B)

| ContrL c A B: sequent (c :: c :: A) B -> sequent (c :: A) B
| ContrR d A B: sequent A (d :: d :: B) -> sequent A (d :: B)

(* Logical rules *)

| NegL d A B: sequent A (d :: B) -> sequent ((Neg d) :: A) B
| NegR c A B: sequent (c :: A) B -> sequent A ((Neg c) :: B)

| ConjL1 c d A B: sequent (c :: A) B -> sequent ((Conj c d) :: A) B
| ConjL2 c d A B: sequent (d :: A) B -> sequent ((Conj c d) :: A) B
| ConjR c d A A' B B': sequent A (c :: B) -> sequent A' (d :: B') ->
                       sequent (A ++ A') (B ++ (Conj c d) :: B')

| DisjL c d A A' B B': sequent (c :: A) B -> sequent (d :: A') B' ->
                 sequent (A ++ (Disj c d) :: A') (B ++ B')
| DisjR1 c d A B: sequent A (c :: B) -> sequent A ((Disj c d) :: B)
| DisjR2 c d A B: sequent A (d :: B) -> sequent A ((Disj c d) :: B)

| ImplL c d A A' B B': sequent A (c :: B) -> sequent (d :: A') B' ->
                       sequent ((Impl c d) :: (A ++ A')) (B ++ B')
| ImplR c d A B: sequent (c :: A) (d :: B) -> sequent A ((Impl c d) :: B)

| ForallL x a c A B: sequent ((subst x a c) :: A) B -> sequent ((Forall c) :: A) B
| ForallR c A B: sequent A (c :: B) -> sequent A ((Forall c) :: B)

| ExistsL c A B: sequent (c :: A) B -> sequent ((Exists c) :: A) B
| ExistsR x a c A B: sequent A ((subst x a c) :: B) -> sequent A ((Exists c) :: B).

Hint Constructors sequent.

Notation "A |- B" := (sequent A B) (at level 70).

Lemma exch_head_l c d A B:
  c :: d :: A |- B <-> d :: c :: A |- B.
Proof.
  replace (c :: d :: A) with (nil ++ c :: d :: A) by trivial.
  replace (d :: c :: A) with (nil ++ d :: c :: A) by trivial.
  split; auto.
Qed.

Lemma exch_head_r c d A B:
  A |- c :: d :: B <-> A |- d :: c :: B.
Proof.
  replace (c :: d :: B) with (nil ++ c :: d :: B) by trivial.
  replace (d :: c :: B) with (nil ++ d :: c :: B) by trivial.
  split; auto.
Qed.

Lemma conj_l c d A B:
  c :: d :: A |- B -> (Conj c d) :: A |- B.
Proof.
  intros H.
  apply ContrL.
  apply ConjL2.
  apply exch_head_l; auto.
Qed.

Lemma disj_r c d A B:
  A |- c :: d :: B -> A |- (Disj c d) :: B.
Proof.
  intros H.
  apply ContrR.
  apply DisjR2.
  apply exch_head_r; auto.
Qed.

Lemma exch_formula_l c A A' A'' B:
  A ++ (A' ++ [c]) ++ A'' |- B <-> A ++ [c] ++ A' ++ A'' |- B.
Proof.
  revert A; induction A'; intros *; [intuition|].
  replace (A ++ ((a :: A') ++ [c]) ++ A'') with (A ++ ([a] ++ A' ++ [c]) ++ A'') by trivial.
  rewrite <- app_assoc.
  rewrite app_assoc.
  rewrite IHA'.
  rewrite <- app_assoc.
  cbn.
  intuition; apply ExchL.
Qed.

Lemma exch_l A B C D E:
  A ++ B ++ C ++ D |- E -> A ++ C ++ B ++ D |- E.
Proof.
  revert A C D; induction B; intros * H.
  - trivial.
  - cbn.
    replace (A ++ C ++ a :: B ++ D) with (A ++ C ++ [a] ++ B ++ D) by trivial.
    setoid_rewrite app_assoc at 2.
    rewrite exch_formula_l.
    rewrite app_assoc.
    apply IHB.
    rewrite <- app_assoc.
    trivial.
Qed.

Lemma exch_formula_r c A B B' B'':
  A |- B ++ (B' ++ [c]) ++ B'' <-> A |- B ++ [c] ++ B' ++ B''.
Proof.
  revert B; induction B'; intros *; [intuition|].
  replace (B ++ ((a :: B') ++ [c]) ++ B'') with (B ++ ([a] ++ B' ++ [c]) ++ B'') by trivial.
  rewrite <- app_assoc.
  rewrite app_assoc.
  rewrite IHB'.
  rewrite <- app_assoc.
  cbn.
  intuition; apply ExchR.
Qed.

Lemma exch_r A B C D E:
  E |- A ++ B ++ C ++ D -> E |- A ++ C ++ B ++ D.
Proof.
  revert A C D; induction B; intros * H.
  - trivial.
  - cbn.
    replace (A ++ C ++ a :: B ++ D) with (A ++ C ++ [a] ++ B ++ D) by trivial.
    setoid_rewrite app_assoc at 2.
    rewrite exch_formula_r.
    rewrite app_assoc.
    apply IHB.
    rewrite <- app_assoc.
    trivial.
Qed.

Lemma assum c A B:
  c :: A |- c :: B.
Proof.
  induction A.
  - induction B; auto.
    apply exch_head_r.
    now apply WeakR.
  - apply exch_head_l.
    now apply WeakL.
Qed.

Hint Resolve exch_l exch_r assum.

Lemma modus_ponens c d A B:
  [Impl c d; c] ++ A  |- B ++ [d].
Proof.
  apply ImplL; auto.
Qed.

Lemma EM c A B:
  A |- Disj c (Neg c) :: B.
Proof.
  apply disj_r.
  apply exch_head_r.
  auto.
Qed.

Close Scope list_scope.
