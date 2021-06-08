From HB Require Import structures.

(* ******************************************************************* *)
(* *********************** Hierarchy design ************************** *)
(* ******************************************************************* *)


Module BadInheritance.

HB.mixin Record Lt A := {
  lt : A -> A -> Prop;
  lt_irr : forall x, ~ (lt x x);
}.
HB.structure Definition O1 := { A of Lt A }.

HB.mixin Record Le A := {
  le : A -> A -> Prop;
  le_refl : forall x, le x x;
}.
HB.structure Definition O2 := { A of Le A }.

HB.builders Context T of Lt T.

Definition myle x y := lt x y \/ x = y.
Lemma myle_refl x : myle x x.
Proof. right; reflexivity. Qed.

HB.instance Definition _ := Le.Build T myle myle_refl.

HB.end.

HB.instance Definition _ := Lt.Build nat Peano.lt PeanoNat.Nat.lt_irrefl.

HB.instance Definition _ := Le.Build nat Peano.le PeanoNat.Nat.le_refl. (* move this up, inheritance broken *)

Lemma test : le 3 4 = (lt 3 4 \/ 3 = 4).
reflexivity.
Qed.

(* Peano.le   !=   Peano.lt \/ eq *)
(* PeanoNat.Nat.le_refl   !=   myle_refl *)

End BadInheritance.


Module ForgetfulInheritance.

HB.mixin Record Lt A := {
  lt : A -> A -> Prop;
  lt_irr : forall x, ~ (lt x x);
  (* already there *)
  le : A -> A -> Prop;
}.
HB.structure Definition O1 := { A of Lt A }.

HB.mixin Record Le A of Lt A := {
  le_refl : forall x : A, le x x;
  le_def : forall x y : A, le x y = (lt x y \/ x = y);
}.
HB.structure Definition O2 := { A of Le A }.

Definition myle (x y : nat) := Peano.lt x y \/ (x = y).
Lemma myle_refl x : myle x x.
Proof. right; reflexivity. Qed.

HB.instance Definition _ := Lt.Build nat Peano.lt PeanoNat.Nat.lt_irrefl myle.

HB.instance Definition _ := Le.Build nat (*PeanoNat.Nat.le_refl*) myle_refl (fun x y => refl_equal _).

Lemma test : le 3 4 = (lt 3 4 \/ 3 = 4).
reflexivity.
Qed.

End ForgetfulInheritance.

