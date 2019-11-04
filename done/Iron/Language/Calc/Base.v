
Require Export Coq.Strings.String.
Require Export Coq.Arith.EqNat.
Require Export Iron.Hectic.Rip.
Require Export Iron.Hectic.Nope.


Fixpoint ble_nat (n m : nat): bool :=
 match n with
 | O => true
 | S n' =>
    match m with
    | O => false
    | S m' => ble_nat n' m'
    end
 end.


Fixpoint bge_nat (n m : nat): bool :=
 match m with
 | O => true
 | S m' =>
    match n with
    | O => false
    | S n' => ble_nat n' m'
    end
 end.


Definition blt_nat (n m: nat): bool :=
 (andb (negb (beq_nat n m)) (ble_nat n m)).


Definition bgt_nat (n m: nat): bool :=
 (andb (negb (beq_nat n m)) (bge_nat n m)).

