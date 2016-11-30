Require Import Coq.Logic.ClassicalFacts.

Definition or_to_boolp {A B:Prop}  (p: A \/ B) : boolP:=
match p with
| or_introl _ => trueP
| or_intror _ => falseP
end.


(* the only way to compute zero is for p to become canonical.
The only canonical member of A=A is eq_refl.
However, it seems impossible to show that p is propositionally equal to eq_refl.
If A were in type, then this would boil down to UIP which is known to be unprovable *)
Fixpoint zero (A : Prop)  (p : A = A) {struct p} : boolP := trueP.


Axiom exm : excluded_middle.

Definition isTrueP (A:Prop) := (or_to_boolp (exm A)).

(* same type as [zero] above, but provably non parametric *)
Definition nonParam (A : Prop)  (p : A = A) : boolP := isTrueP A.

(* because zero cannot be unfolded, it seems safe to assume the following *)
Axiom zeroOpaque :(zero = nonParam).


(*
Definition zero_type := ltac:(let T:= type of zero in exact T).
Declare ML Module "paramcoq".
Parametricity Recursive zero_type.
Print Top__o__zero_type_R.
Parametricity Recursive eq.
Print eq_R.
Parametricity Recursive excluded_middle.
Print False_R.
Definition trueP_type := ltac:(let T:= type of isTrueP in exact T).
Parametricity Recursive trueP_type.
Print Top__o__trueP_type_R.
Print boolP_R.
*)

Inductive boolP_R : boolP -> boolP -> Prop :=
    boolP_R_trueP_R : boolP_R trueP trueP
  | boolP_R_falseP_R : boolP_R falseP falseP.



Inductive eq_R (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (x₁ : A₁) (x₂ : A₂)
(x_R : A_R x₁ x₂)
  : forall (H : A₁) (H0 : A₂), A_R H H0 -> x₁ = H -> x₂ = H0 -> Prop :=
    eq_R_eq_refl_R : eq_R A₁ A₂ A_R x₁ x₂ x_R x₁ x₂ x_R eq_refl eq_refl.


Inductive False_R : False -> False -> Prop :=.

Inductive or_R (A₁ A₂ : Prop) (A_R : A₁ -> A₂ -> Prop) (B₁ B₂ : Prop)
(B_R : B₁ -> B₂ -> Prop) : A₁ \/ B₁ -> A₂ \/ B₂ -> Prop :=
    or_R_or_introl_R : forall (H : A₁) (H0 : A₂),
                       A_R H H0 ->
                       or_R A₁ A₂ A_R B₁ B₂ B_R (or_introl H) (or_introl H0)
  | or_R_or_intror_R : forall (H : B₁) (H0 : B₂),
                       B_R H H0 ->
                       or_R A₁ A₂ A_R B₁ B₂ B_R (or_intror H) (or_intror H0).




Definition not_R := 
fun (A₁ A₂ : Prop) (A_R : A₁ -> A₂ -> Prop) (H : A₁ -> False)
  (H0 : A₂ -> False) =>
forall (H1 : A₁) (H2 : A₂), A_R H1 H2 -> False_R (H H1) (H0 H2).


Lemma exmNotParam:
(forall (A₁ A₂ : Prop) (A_R : A₁ -> A₂ -> Prop),
or_R A₁ A₂ A_R (~ A₁) (~ A₂) (not_R A₁ A₂ A_R)
  (exm A₁) (exm A₂)) -> False.
Proof using.
  intros Hc.
  specialize (Hc True False (fun _ _ => True)).
  destruct Hc; auto.
Qed.

Lemma boolP_R_eq : forall a b:boolP, boolP_R a b <-> a=b.
Proof using.
  intros  ? ?. split; intros Hc.
- inversion Hc; reflexivity.
- subst. destruct b; constructor.
Qed.

(* PI stands for proof irrelevance *)
Lemma isTrueP_param_implies_PI :
(forall A₁ A₂ : Prop, (A₁ -> A₂ -> Prop) -> boolP_R (isTrueP A₁) (isTrueP A₂))->
  (trueP = falseP).
Proof using.
  intros Hc.
  specialize (Hc True False (fun _ _ => True)).
  apply boolP_R_eq in Hc.
  unfold isTrueP in Hc.
  destruct ((exm True)); destruct ((exm False)); simpl in Hc; tauto.
Qed.

Lemma  or_dep_elim :
    forall (A B:Prop) (P:or A B -> Prop),
      (forall a:A, P (@or_introl A B a)) ->
      (forall b:B, P (@or_intror A B b)) -> forall b:or A B, P b.
Proof.
  intros.
  destruct b; auto.
Qed.


Locate "or".

(* because of https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html#lab46,
this is not very interesting -- PI is already provable from LEM *)

Lemma zero_param_implies_PR: 
(forall (A₁ A₂ : Prop) (A_R : A₁ -> A₂ -> Prop) (p₁ : A₁ = A₁) (p₂ : A₂ = A₂),
eq_R Prop Prop (fun H1 H2 : Type => H1 -> H2 -> Type) A₁ A₂ A_R A₁ A₂ A_R p₁
  p₂ -> (zero A₁ p₁) = (zero A₂ p₂)) -> (trueP = falseP).
Proof using.
  intros Hc.
  apply isTrueP_param_implies_PI.
  intros.
  change ((isTrueP A₁)) with (nonParam A₁ eq_refl).
  change ((isTrueP A₂)) with (nonParam A₂ eq_refl).
  apply boolP_R_eq.
  rewrite <- zeroOpaque.
  apply Hc with (A_R := fun _ _ => True).
  simpl. constructor.
Qed.

