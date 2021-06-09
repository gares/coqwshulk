
From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.

(* ******************************************************************* *)
(* *********************** Hierarchy design ************************** *)
(* ******************************************************************* *)

Module BadInheritance.

HB.mixin Record HasMul T := {
  mul : T -> T -> T;
}.
HB.structure Definition Mul := { T of HasMul T }.

HB.mixin Record HasSq T := {
  sq : T -> T;
}.
HB.structure Definition Sq := { T of HasSq T }.

(* We need a functorial construction (a container)
   which preserves both structures. The simplest one is the option type. *)
Definition option_mul {T : Mul.type} (o1 o2 : option T) : option T :=
  match o1, o2 with
  | Some n, Some m => Some (mul n m)
  | _, _ => None
  end.
HB.instance Definition _ (T : Mul.type) := HasMul.Build (option T) option_mul.

Definition option_square {T : Sq.type} (o : option T) : option T :=
  match o with
  | Some n => Some (sq n)
  | None => None
  end.
HB.instance Definition _ (T : Sq.type) := HasSq.Build (option T) option_square.

(* Now we mix the two unrelated structures by building Sq out of Mul.

               *** This breaks Non Forgetful Inheritance ***
https://math-comp.github.io/competing-inheritance-paths-in-dependent-type-theory/

*)
HB.instance Definition _ (T : Mul.type) := HasSq.Build T (fun x => mul x x).

(* As we expect we can proved this (by reflexivity) *)
Lemma sq_mul (V : Mul.type) (v : V) : sq v = mul v v.
Proof. by reflexivity. Qed.

Lemma problem (W : Mul.type) (w : option W) : sq w = mul w w.
Proof.
Fail reflexivity. (* What? It used to work! *)
Fail rewrite sq_mul. (* Lemmas don't cross the container either! *)
(* Let's investigate *)
rewrite /mul/= /sq/=.
(* As we expect, we are on the option typem in the LHS it's the Sq built using
   the NFI instance
 
     option_square w = option_mul w w
*)
rewrite /option_mul/=.
rewrite /option_square/sq/=.
congr (match w with Some n => _ | None => None end).
(* The branched for Some differ, since w is a variable,
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

HB.mixin Record HasMul T := {
  mul : T -> T -> T;
}.
HB.structure Definition Mul := { T of HasMul T }.

HB.mixin Record HasSq T of Mul T := {
  sq : T -> T;
  sq_mul : forall x, sq x = mul x x;
}.
HB.structure Definition Sq := { T of HasSq T & Mul T }.

Definition option_mul {T : Mul.type} (o1 o2 : option T) : option T :=
  match o1, o2 with
  | Some n, Some m => Some (mul n m)
  | _, _ => None
  end.
HB.instance Definition _ (T : Mul.type) := HasMul.Build (option T) option_mul.

Definition option_square {T : Sq.type} (o : option T) : option T :=
  match o with
  | Some n => Some (sq n)
  | None => None
  end.
Lemma option_sq_mul {T : Sq.type} (o : option T) : option_square o = mul o o.
Proof. by rewrite /option_square; case: o => [x|//]; rewrite sq_mul. Qed.
HB.instance Definition _ (T : Sq.type) := HasSq.Build (option T) option_square option_sq_mul.

Lemma problem (W : Sq.type) (w : option W) : sq w = mul w w.
Proof. by rewrite sq_mul. Qed.

End GoodInheritance.

(* ******************************************************************* *)
(* ********************** Feather factories *********************** *)
(* ******************************************************************* *)

Module Feather.

HB.mixin Record IsDiscrete T := {
    eqtest : T -> T -> bool;
    eqOK : forall x y, reflect (x = y) (eqtest x y);
}.
HB.structure Definition Equality := { T of IsDiscrete T }.

HB.mixin Record IsSingleton T of IsDiscrete T := {
    def : T;
    all_def : forall x, eqtest x def = true;
}.
HB.structure Definition Singleton := { T of IsSingleton T }.

(* xT is a right type, T is a new type linked to xT *)
Definition link {xT T : Type} {f : xT -> T} {g : T -> xT} (e : forall x, f (g x) = x) := T.

Section TransferEQ.

Context {eT : Equality.type} {T : Type} {f : eT -> T} {g : T -> eT}.
Context (canfg : forall x, f (g x) = x).

Definition link_eqtest (x y : T) : bool := eqtest (g x) (g y).

Lemma link_eqOK (x y : T) : reflect (x = y) (link_eqtest x y).
Proof.
rewrite /link_eqtest; case: (eqOK (g x) (g y)) => [E|abs].
  by constructor; rewrite -[x]canfg -[y]canfg E canfg.
by constructor=> /(f_equal g)/abs.
Qed.
HB.instance Definition link_IsDiscrete :=
  IsDiscrete.Build (link canfg) link_eqtest link_eqOK.

End TransferEQ.

Section TransferSingleton.

Context {eT : Singleton.type} {T : Type} {f : eT -> T} {g : T -> eT}.
Context (canfg : forall x, f (g x) = x).

Definition link_def : link canfg := f def.

Lemma link_all_def x : eqtest x link_def = true.
Proof.
rewrite /link_def; have /eqOK <- := all_def (g x).
by rewrite canfg; case: (eqOK x x).
Qed.

HB.instance Definition _ := IsSingleton.Build (link canfg) link_def link_all_def.

End TransferSingleton.

Axioms B : Type.

Axiom testB : B -> B -> bool.
Axiom testOKB : forall x y, reflect (x = y) (testB x y).
HB.instance Definition _ := IsDiscrete.Build B testB testOKB.

Axiom defB : B.
Axiom all_defB : forall x, eqtest x defB = true.
HB.instance Definition _ := IsSingleton.Build B defB all_defB.

Axiom A : Type.
Axiom f : B -> A.
Axiom g : A -> B.
Axiom canfg : forall x, f (g x) = x.

HB.instance Definition _ := Singleton.copy A (link canfg).

HB.about A. (* both Equality and Singleton have been copied *)

End Feather.


(* ******************************************************************* *)
(* ********************** Abstraction barriers *********************** *)
(* ******************************************************************* *)

Require Import Arith.

Module SlowFailure.

Definition large := 999999.

Lemma test x : large ^ x ^ large = x ^ large ^ large.
Time Fail reflexivity. (* takes 7s, both by and // call reflexivity *)
Abort.

End SlowFailure.


Module FastFailure.

HB.lock Definition large := 999999.

Lemma test x : large ^ x ^ large = x ^ large ^ large.
Time Fail reflexivity. (* takes 0s *)
rewrite large.unlock.
Time Fail reflexivity. (* takes 7s *)
Abort.

Print Module Type largeLocked.
(*
   Parameter body : nat.
   Parameter unlock : body = 999999
*)
Print large.
(*
Notation large := large.body
*)

End FastFailure.
