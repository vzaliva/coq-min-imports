Require Import Bool.DecBool.
 Require Import Arith.Min.
Require Import   Omega. (* comment *)
Require Import BinNums  List Setoid.
Require Import Setoid. (* Presently for testing only. Consider moving it elsewhere *)

(* requires Arith.Min *)
Definition bar1 := min_0_l.

(* requires Omega *)
Lemma foo: 1<2.
Proof.
  omega.
Qed.

(* Requires List *)
Definition bar2 := hd.
