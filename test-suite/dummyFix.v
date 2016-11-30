
(* the only way to compute zero is for p to become canonical.
The only canonical member of A=A is eq_refl.
However, it is impossible to that p is propositionally equal to eq_refl.
In particular the univalence axiom allows for non-refl proofs. *)
Fixpoint zero (A : Set)  (p : A = A) {struct p} : nat := 0.


(* although this axiom breaks canonicity, it is believed to be consistent *)
Axiom strong_exm : Set -> nat.
Axiom strong_exm_true : strong_exm True = 0.
Axiom strong_exm_false : strong_exm False = 1.


(* same type as [zero] above, but provably non parametric *)
Definition nonParam (A : Set)  (p : A = A) : nat := strong_exm A.

(* because zero cannot be unfolded, it seems safe to assume the following *)
Axiom zeroOpaque :(forall x, zero x = nonParam x).


Inductive eq_R (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (x₁ : A₁) (x₂ : A₂)
(x_R : A_R x₁ x₂)
  : forall (H : A₁) (H0 : A₂), A_R H H0 -> x₁ = H -> x₂ = H0 -> Prop :=
    eq_refl_R : eq_R A₁ A₂ A_R x₁ x₂ x_R x₁ x₂ x_R eq_refl eq_refl.


Lemma zero_not_parametric :
(forall (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Set) (p₁ : A₁ = A₁) (p₂ : A₂ = A₂),
eq_R Set Set (fun H1 H2 : Set => H1 -> H2 -> Set) A₁ A₂ A_R A₁ A₂ A_R p₁
  p₂ -> (zero A₁ p₁) = (zero A₂ p₂)) -> False.
Proof using.
  intros Hc.
  specialize (Hc True False (fun _ _ => True) eq_refl eq_refl).
  do 2 rewrite zeroOpaque in Hc.
  unfold nonParam in Hc. simpl in Hc.
  rewrite strong_exm_true in Hc.
  rewrite strong_exm_false in Hc.
  specialize (Hc (@eq_refl_R _ _ _ _ _ _)).
  discriminate.
Qed.

