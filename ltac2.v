(* Require Import Ltac2.Message. *)
From Ltac2 Require Import Ltac2 Control Message.
Set Default Proof Mode "Ltac2".

Ltac2 my_failure s := Tactic_failure (Some (of_string s)).
Ltac2 fail_with s := throw (my_failure s).
Ltac2 p s := print (of_string s).
Ltac2 foo () := fail_with "fail".
Ltac2 bar () := print (of_exn (Tactic_failure None)).
Goal True.
Proof.
let a () := plus (fun _ => p "a") (fun _ => p "b") in
a (); fail.
case(a); fail.
let a () := zero (Tactic_failure None) in
plus (fun _ => p "a") (fun _ => p "b"). (fun e => print (of_exn e)).
plus (zero (Tactic_failure None)).

(p "a") (p "b").
once (fun _ => ()).
fail.
foo ().
ltac2:(foo ()).
idtac; ltac2:(foo). fail. let x := 1 in print x. print (message "1").
(* foo. *)
ltac2:(foo).

Ltac2 foo () := ltac1:(pose proof I).
(* From Ltac2 Require Import Ltac2. *)


