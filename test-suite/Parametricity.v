Declare ML Module "paramcoq".

Ltac destruct_reflexivity := 
  intros ; repeat match goal with 
    | [ x : _ |- _ = _ ] => destruct x; reflexivity; fail
  end.

Ltac destruct_construct x := 
    (destruct x; [ constructor 1 ]; auto; fail)
 || (destruct x; [ constructor 1 | constructor 2 ]; auto; fail)
 || (destruct x; [ constructor 1 | constructor 2 | constructor 3]; auto; fail).

Ltac unfold_cofix := intros; match goal with 
 [ |- _ = ?folded ] =>  
    let x := fresh "x" in 
    let typ := type of folded in 
    (match folded with _ _ => pattern folded | _ => pattern folded at 2 end);
    match goal with [ |- ?P ?x ] => 
    refine (let rebuild : typ -> typ := _ in 
            let path : rebuild folded = folded := _ in  
            eq_rect _ P _ folded path) end; 
    [ intro x ; destruct_construct x; fail 
    | destruct folded; reflexivity
    | reflexivity]; fail
end.

Ltac destruct_with_nat_arg_pattern x :=
  pattern x;
  match type of x with 
   | ?I 0 => refine (let gen : forall m (q : I m), 
     (match m return I m -> Type with 
         0 => fun p => _ p
     | S n => fun _  => unit end q) := _ in gen 0 x)     
   | ?I (S ?n) => refine (let gen : forall m (q : I m), 
     (match m return I m -> Type with 
         0 => fun _  => unit 
     | S n => fun p => _ p end q) := _ in gen (S n) x)
  end; intros m q; destruct q.

Ltac destruct_reflexivity_with_nat_arg_pattern := 
  intros ; repeat match goal with 
    | [ x : _ |- _ = _ ] => destruct_with_nat_arg_pattern x; reflexivity; fail
  end.
 
Global Parametricity Tactic := ((destruct_reflexivity; fail)
                            || (unfold_cofix; fail) 
                            || (destruct_reflexivity_with_nat_arg_pattern; fail)
                            ||  auto). 


Require Import ProofIrrelevance. (* for opaque terms *)

Set Allow StrictProp.  (* TODO: use SProp instead of ProofIrrelevance *)

Parametricity Module Logic.
Parametricity Module Datatypes.
Parametricity Module Specif.

Parametricity Module Decimal.
Parametricity Module Hexadecimal.
Parametricity Module Number.
Parametricity Module Nat.

Parametricity Module Peano.

Parametricity Module Wf.
Parametricity Module Tactics.

Export Logic_R Datatypes_R Specif_R Nat_R Peano_R Wf_R Tactics_R. 
