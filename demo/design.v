(* ******************************************************************* *)
(* *********************** Hierarchy design ************************** *)
(* ******************************************************************* *)

From HB Require Import structures.
From Coq Require Import ssreflect.

Module BadInheritance.

HB.mixin Record HasMult T := {
  mult : T -> T -> T;
}.
HB.structure Definition Mult := { T of HasMult T }.

HB.mixin Record HasSquare T := {
  square : T -> T;
}.
HB.structure Definition Square := { T of HasSquare T }.

(* We need a functorial construction (a container)
   which preserves both structures. The simplest one is the option type. *)
Definition option_mult {T : Mult.type} (o1 o2 : option T) : option T :=
  match o1, o2 with
  | Some n, Some m => Some (mult n m)
  | _, _ => None
  end.
HB.instance Definition _ (T : Mult.type) := HasMult.Build (option T) option_mult.

Definition option_square {T : Square.type} (o : option T) : option T :=
  match o with
  | Some n => Some (square n)
  | None => None
  end.
HB.instance Definition _ (T : Square.type) := HasSquare.Build (option T) option_square.

(* Now we mix the two unrelated structures by building Sq out of Mul.

               *** This breaks Non Forgetful Inheritance ***
https://math-comp.github.io/competing-inheritance-paths-in-dependent-type-theory/

*)
#[non_forgetful_inheritance]
HB.instance Definition _ (T : Mult.type) := HasSquare.Build T (fun x => mult x x).

(* As we expect we can proved this (by reflexivity) *)
Lemma square_mult (T : Mult.type) (x : T) : square x = mult x x.
Proof. by reflexivity. Qed.

Lemma problem (T : Mult.type) (o : option T) : square o = mult o o.
Proof.
Fail reflexivity. (* What? It used to work! *)
Fail rewrite square_mult. (* Lemmas don't cross the container either! *)
(* Let's investigate *)
rewrite /mult/= /square/=.
(* As we expect, we are on the option type. In the LHS it is the Sq built using
   the NFI instance
 
     option_square w = option_mul w w
*)
rewrite /option_mult/=.
rewrite /option_square/square/=.
congr (match o with Some n => _ | None => None end).
(* The branches for Some differ, since w is a variable,
   they don't compare as equal

      (fun n : W => Some (mul n n)) =
      (fun n : W => match w with
                    | Some m => Some (mul n m)
                    | None => None
                    end)
*)
Abort.

End BadInheritance.

Module GoodInheritance.

HB.mixin Record HasMult T := {
  mult : T -> T -> T;
}.
HB.structure Definition Mult := { T of HasMult T }.

HB.mixin Record HasSquare T of Mult T := {
  square : T -> T;
  square_mult : forall x, square x = mult x x;
}.
HB.structure Definition Square := { T of HasSquare T & Mult T }.

Definition option_mult {T : Mult.type} (o1 o2 : option T) : option T :=
  match o1, o2 with
  | Some n, Some m => Some (mult n m)
  | _, _ => None
  end.
HB.instance Definition _ (T : Mult.type) := HasMult.Build (option T) option_mult.

Definition option_square {T : Square.type} (o : option T) : option T :=
  match o with
  | Some n => Some (square n)
  | None => None
  end.

Lemma option_square_mult {T : Square.type} (o : option T) : option_square o = mult o o.
Proof. by rewrite /option_square; case: o => [x|//]; rewrite square_mult. Qed.

HB.instance Definition _ (T : Square.type) :=
  HasSquare.Build (option T) option_square option_square_mult.

Lemma problem (T : Square.type) (o : option T) : square o = mult o o.
Proof. by rewrite square_mult. Qed.

End GoodInheritance.
