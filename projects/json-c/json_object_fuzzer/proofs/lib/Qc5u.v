(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
Import ListNotations.
Open Scope Z_scope.

Lemma land7_of_mod8 : forall p, p mod 8 = 0 -> Z.land p 7 = 0.
Proof. intros p H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.
Lemma land3_of_mod4 : forall p, p mod 4 = 0 -> Z.land p 3 = 0.
Proof. intros p H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.

Ltac ub_if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.

Ltac ub_land H :=
lazymatch type of H with
| ?p mod 16 = 0 => rewrite ?(unsigned_lit p) by lia; first [ rewrite (land7_of_mod16 p H) | rewrite (land3_of_mod16 p H) ]
| ?p mod 8 = 0 => rewrite ?(unsigned_lit p) by lia; rewrite (land7_of_mod8 p H)
| ?p mod 4 = 0 => rewrite ?(unsigned_lit p) by lia; rewrite (land3_of_mod4 p H)
end.
Ltac ub_align_far H := ub_land H; first [if_true | ub_if_lit].
Ltac ub_align_near H := ub_land H; first [if_false | ub_if_lit].

Ltac ub_slti0 d := rewrite (v_slti_0 (Z_to_bv 64 d) 0) by (rewrite zsig_lit by lia; lia).
Ltac ub_snez p := rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 p)) by (rewrite (unsigned_lit 0), (unsigned_lit p) by lia; lia).
Ltac ub_seqz0 p := rewrite (v_sltiu_0 (Z_to_bv 64 p) 1) by (rewrite ?(unsigned_lit p) by lia; lia).
Ltac ub_geu a b := rewrite (v_sltu_0' (Z_to_bv 64 a) (Z_to_bv 64 b)) by (rewrite (unsigned_lit a), (unsigned_lit b) by lia; lia).

Ltac ub_lvl q bse d :=
rewrite ?(v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 q)) by (rewrite (unsigned_lit 0), (unsigned_lit q) by lia; lia);
rewrite ?(v_sltiu_0 (Z_to_bv 64 bse) 1) by (rewrite ?(unsigned_lit bse) by lia; lia);
rewrite ?(v_sltu_0' (Z_to_bv 64 bse) (Z_to_bv 64 q)) by (rewrite (unsigned_lit bse), (unsigned_lit q) by lia; lia);
rewrite ?(v_slti_0 (Z_to_bv 64 d) 0) by (rewrite zsig_lit by lia; lia).

Ltac ub_bse q bse d :=
rewrite ?(unsigned_lit d) by lia; rewrite ?Z.shiftl_mul_pow2 by lia; change (2 ^ 5) with 32;
lazymatch goal with
| |- context [q + d * 32] => replace (q + d * 32) with bse by lia
| |- context [d * 32 + q] => replace (d * 32 + q) with bse by lia
end.

Lemma ub_div8_add : forall p j, p mod 8 = 0 -> 0 <= j -> (p + j) / 8 = p / 8 + j / 8.
Proof. intros p j Hp Hj. Z.div_mod_to_equations. lia. Qed.
Ltac ub_div8 :=
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (ub_div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.
Ltac asan_chkB := step; step; sh_norm; ub_div8; step; step; first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.
Ltac asan_rechkB := step; rewrite ?sxb_zero, ?zxb_zero; step; first [ if_false | if_true ].
Tactic Notation "asan_rechkMB" integer(n) := step; rewrite ?sxb_zero, ?zxb_zero; do n step; step; first [ if_false | if_true ].
Tactic Notation "asan_chkMB" integer(n) := step; step; sh_norm; ub_div8; step; do n step; step; first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.
