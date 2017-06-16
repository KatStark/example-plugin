Declare ML Module "myplug".

Require Import Arith.

Definition test := True.

Definition id :=  (fun (y: nat) => y). 
Definition foo :=  (fun (y: nat) => 3). 

Record R := mkR {
                field : nat -> nat
              }.

Definition F := mkR id. 
Definition G := mkR (fun y => 3). 

Definition type (x : nat) : Type.
Admitted.


Detect (fun (x: nat) => x).
Detect (fun (x: nat) => 3).
Detect (fun (x: nat) => (fun y => y) x).
ReduceAwayLamVar red := (fun (x: nat) => (fun y => y) x).
Print red.

ReduceAwayLamVar red2 := (fun (x: nat) => foo x).
Print red2.

Detect (fun (x: nat) => (fun y => Some y) x).
Detect (fun (x: nat) => id x).
Detect (fun (x : nat) => (fun y => 3) x). 
Detect (fun (x: nat) => forall (y: nat), x = 3). 
Detect (fun (x: nat) => forall (y: nat), y = 3).  
Detect (fun (x : nat) => let y := 3 in x).
Detect (fun (x : nat) => let y := 3 in y).
Detect (fun (x : nat) => let y := 3 in x + y).
Detect (fun (x : nat) => let y := x + 2 in y).
Detect (fun (x: nat) => match x with |0 => 2 |S x => 3 end).
Detect (fun (x: nat) => match 2 with |0 => 2 |S x => 3 end). 
Detect (fun (x: nat) => match 2 with |0 => x |S y => x end). 
Detect (fun (x: nat) (y: nat) => match y with |0 => x |S y => 2 end). 
Detect (fun (x : nat) => field F x).
Detect (fun (x : nat) => field G x). (* Seems not to reduce. Check. *)
Detect (fun (x : nat) => fix f (m n o : nat) := match n with 0 => 0 | S n => id x end). 
Detect (fun (x : nat) => fix f (m n o : nat) (p : type x) := match n with 0 => 0 | S n => 0 end).
Detect (fun (x : nat) => fix f n := match n with 0 => 0 | S n => g n end
                               with g n := match n with 0 => 0 | S n => 0 end
                               with h n := match n with 0 => 0 | S n => 0 end             
                                             for f).
Detect (fun (x : nat) => fix f n := match n with 0 => 0 | S n => g n end
                               with g n := match n with 0 => 0 | S n => 0 end
                               with h n := match n with 0 => x | S n => 0 end             
                                             for f).
Detect (fun (x : nat) => fix f n := match n with 0 => 0 | S n => h n end
                               with g n (z: type x) := match n with 0 => 0 | S n => 0 end
                               with h n := match n with 0 => 0 | S n => 0 end             
                                             for f).

Detect (fun (x : nat) => (fix f n := match n with 0 => 0 | S n => h n end
                               with g n (z: type x) := match n with 0 => 0 | S n => 0 end
                               with h n := match n with 0 => 0 | S n => 0 end             
                                             for f) 0).


(* Goal forall A : Prop, A -> A.
Proof.
  myintro A x.
  exact x.
Qed. *)


(* Checking that this works in sections. *)
Section X.
Variable y:nat.
Detect (fun (x: nat) => x).
Detect (fun (x: nat) => y).
Detect (fun (x: nat) => if true then x else y).
Detect (fun (x: nat) => if false then x else y).
End X.