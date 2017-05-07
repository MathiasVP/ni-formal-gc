Require Import Arith.

(* From Spitters/van der Weegen, 2011.
   and use it by writing decide (n1 = n2).
 *)
Class Decision (P: Prop): Type := decide: {P} + {~ P}.
Arguments decide _ {_}.


Instance nat_dec: forall n1 n2 : nat, Decision (n1 = n2).
Proof. apply eq_nat_dec. Defined.