(*
  Formalisation of the sequent calculus. Done according to the presentation
  found in [Girard, Taylor, Lafont 1989] Proofs and Types.
 *)

From Coq Require List.

Set Implicit Arguments.

Open Scope list_scope.
Import List.ListNotations.

Variable atom: Type.

Inductive formulae: Type :=
| Atom: atom -> formulae
| Neg: formulae -> formulae
| Conj: formulae -> formulae -> formulae
| Disj: formulae -> formulae -> formulae
| Impl: formulae -> formulae -> formulae.

Inductive sequent: list formulae -> list formulae -> Prop :=
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
| ImplR c d A B: sequent (c :: A) (d :: B) -> sequent A ((Impl c d) :: B).

Hint Constructors sequent.

Notation "A |- B" := (sequent A B) (at level 70).

Lemma assum_left c B:
  [c] |- c :: B.
Proof.
  induction B; auto.
  replace (c :: a :: B) with (nil ++ (c :: a :: B)) by trivial.
  apply ExchR.
  now apply WeakR.
Qed.

Lemma assum_right c A:
  c :: A |- [c].
Proof.
  induction A; auto.
  replace (c :: a :: A) with (nil ++ (c :: a :: A)) by trivial.
  apply ExchL.
  now apply WeakL.
Qed.

Lemma assum c A B:
  c :: A |- c :: B.
Proof.
  induction A.
  - apply assum_left.
  - replace (c :: a :: A) with (nil ++ (c :: a :: A)) by trivial.
    apply ExchL.
    now apply WeakL.
Qed.

Hint Resolve assum_left assum_right assum.

Lemma modus_ponens c d A B:
  [Impl c d; c] ++ A  |- B ++ [d].
Proof.
  apply ImplL; auto.
Qed.

Close Scope list_scope.
