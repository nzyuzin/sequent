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

Lemma exch_head_left c d A B:
  c :: d :: A |- B <-> d :: c :: A |- B.
Proof.
  replace (c :: d :: A) with (nil ++ c :: d :: A) by trivial.
  replace (d :: c :: A) with (nil ++ d :: c :: A) by trivial.
  split; auto.
Qed.

Lemma exch_head_right c d A B:
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
  apply exch_head_left; auto.
Qed.

Lemma exch_formula_left c A A' A'' B:
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

Lemma exch_left A B C:
  A ++ B |- C -> B ++ A |- C.
Proof.
  revert A; induction B; intros * H; cbn.
  - now rewrite app_nil_r in H.
  - replace (A ++ a :: B) with (A ++ [a] ++ B ++ nil) in H by (rewrite app_nil_r; trivial).
    rewrite app_assoc in H.
    rewrite app_nil_r in H.
    specialize (IHB _ H).
    replace (B ++ A ++ [a]) with (nil ++ ((B ++ A) ++ [a]) ++ nil) in IHB
      by (now cbn; rewrite app_nil_r; rewrite app_assoc).
    rewrite exch_formula_left in IHB.
    now cbn in IHB; rewrite app_nil_r in IHB.
Qed.

Lemma disj_r c d A B:
  A |- c :: d :: B -> A |- (Disj c d) :: B.
Proof.
  intros H.
  apply ContrR.
  apply DisjR2.
  apply exch_head_right; auto.
Qed.

Lemma assum_left c B:
  [c] |- c :: B.
Proof.
  induction B; auto.
  apply exch_head_right.
  now apply WeakR.
Qed.

Lemma assum_right c A:
  c :: A |- [c].
Proof.
  induction A; auto.
  apply exch_head_left.
  now apply WeakL.
Qed.

Lemma assum c A B:
  c :: A |- c :: B.
Proof.
  induction A.
  - apply assum_left.
  - apply exch_head_left.
    now apply WeakL.
Qed.

Hint Resolve exch_head_left exch_head_right assum_left assum_right assum.

Lemma modus_ponens c d A B:
  [Impl c d; c] ++ A  |- B ++ [d].
Proof.
  apply ImplL; auto.
Qed.

Lemma EM c A B:
  A |- Disj c (Neg c) :: B.
Proof.
  apply disj_r.
  apply exch_head_right.
  auto.
Qed.

Close Scope list_scope.
