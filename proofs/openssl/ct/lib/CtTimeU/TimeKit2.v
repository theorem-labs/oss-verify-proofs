(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import ZBridge MState Exec Mem SysStep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma sx32_signed z : - 2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros Hz. unfold sx32. f_equal. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 z) with (z mod 2^64). rewrite <- (Z.add_0_r (z mod 2^64)). rewrite swrap32_mod64, Z.add_0_r. apply swrap32_small. lia.
Qed.

(* [comment removed for export] *)
Ltac brT tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
  let BC := fresh "BC" in assert (BC : c = true) by tac; rewrite BC; clear BC; change (if true then a else b) with a end.
Ltac brF tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
  let BC := fresh "BC" in assert (BC : c = false) by tac; rewrite BC; clear BC; change (if false then a else b) with b end.
Ltac ltsz := rewrite ?lts_lit; rewrite ?swrap64_small by lia; rewrite ?swrap64_big by lia; cbn [negb];
  first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity | rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity].

(* [comment removed for export] *)
Lemma addiw_small z k : - 2^31 <= z + k < 2^31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + k) = z + k.
Proof.
  intros H. rewrite Z_to_bv_unsigned. change (bv_wrap 64 z) with (z mod 2^64). rewrite swrap32_mod64. apply swrap32_small. lia.
Qed.

(* [comment removed for export] *)
Lemma unsigned_small_eq0 d : - 2^63 <= d < 2^63 -> bv_unsigned (Z_to_bv 64 d) = 0 -> d = 0.
Proof.
  intros Hd H. rewrite Z_to_bv_unsigned in H. change (bv_wrap 64 d) with (d mod 2^64) in H.
  Z.to_euclidean_division_equations; lia.
Qed.
Lemma unsigned_small_ne0 d : - 2^63 <= d < 2^63 -> d <> 0 -> bv_unsigned (Z_to_bv 64 d) <> 0.
Proof. intros Hd H E. apply H. apply unsigned_small_eq0; assumption. Qed.

(* [comment removed for export] *)
Lemma zxb_lit c : 0 <= c < 256 -> zxb (Z_to_bv 8 c) = Z_to_bv 64 c.
Proof. intros Hc. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. change (bv_wrap 8 c) with (c mod 2^8). apply Z.mod_small. lia. Qed.

Lemma isdigit_range c : 48 <= c <= 57 -> (48 <=? c) && (c <=? 57) = true.
Proof. intros H. rewrite (proj2 (Z.leb_le 48 c)) by lia. rewrite (proj2 (Z.leb_le c 57)) by lia. reflexivity. Qed.
Lemma isdigit_false c : c < 48 \/ 57 < c -> (48 <=? c) && (c <=? 57) = false.
Proof. intros H. destruct (Z.leb_spec 48 c); destruct (Z.leb_spec c 57); cbn; first [reflexivity| lia]. Qed.

(* [comment removed for export] *)
Lemma sgt0_lit x : 0 <= x < 2^63 -> (9223372036854775808 <? Z.lxor x 9223372036854775808) = (0 <? x).
Proof.
  intros Hx. change 9223372036854775808 with (2^63) at 2. rewrite zb_lxor_sign by lia. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec 0 x); [apply Z.ltb_lt| apply Z.ltb_ge]; lia.
Qed.
