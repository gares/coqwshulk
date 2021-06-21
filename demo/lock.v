(* ******************************************************************* *)
(* ********************** Abstraction barriers *********************** *)
(* ******************************************************************* *)

From HB Require Import structures.
From Coq Require Import ssreflect Arith.

Module SlowFailure.

(* 
   When building a library it is natural to stack definitions up and reuse
   things you already have as much as possible.
   
   More often that not we want to set up abstraction barriers.
   For example one may define a mathematical concept using, say, lists and their
   operations, provide a few lemmas about the new concept, and then expect the
   user to never unfold the concept and work with lists directly.

   Abstraction barriers are not only good for clients, which are granted to work
   at the right abstraction level, but also for Coq itself, since it may be
   tricked into unfolding definitions and manipulate huge terms.

   HB.lock is a tool to easily impose abstraction barriers. It uses modules
   and module signatures to seal the body of a definition, keeping access to
   it via an equation.

*)

(* not a very clever construction, but a large one. Bare with us. *)
Definition new_concept := 999999.

Lemma test x : new_concept ^ x ^ new_concept = x ^ new_concept ^ new_concept.
Proof.
(* this goal is not trivial, and maybe even false, but you may call
   some automation on it anyway *)
Time Fail reflexivity. (* takes 7s, note that both by and // call reflexivity *)
Abort.

End SlowFailure.


Module FastFailure.

HB.lock Definition new_concept := 999999.

Lemma test x : new_concept ^ x ^ new_concept = x ^ new_concept ^ new_concept.
Time Fail reflexivity. (* takes 0s *)
rewrite new_concept.unlock.
Time Fail reflexivity. (* takes 7s, the original body is restored *)
Abort.

Print Module Type new_conceptLocked.
Print Module new_concept.
(*
   Module Type new_conceptLocked = Sig
     Parameter body : nat.
     Parameter unlock : body = 999999
   End
   Module new_concept : new_conceptLocked := ...
*)
Print new_concept.
(*
   Notation new_concept := new_concept.body
*)

Canonical unlock_new_concept := Unlockable new_concept.unlock.

End FastFailure.
