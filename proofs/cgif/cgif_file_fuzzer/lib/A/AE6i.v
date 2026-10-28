(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI00 YI16.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y AE3i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2h AE2g AE2j AE24.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE25.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tfc_mbyte_of_aview : forall (H : word -> bool) mem a v,
aview tfibsegs H mem a = Some v -> mbyte tfibsegs (mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof. intros H mem a v Hv. exact (AF0x.aview_byte H mem a v Hv). Qed.
Lemma tfc_lit_unowned : forall B, TfibSyms B -> forall a, (0x20e00 <= a < 0x20e0d \/ 0x20e60 <= a < 0x20e63) ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B TB a Ha. split.
- intros HX. rewrite (ts_owned B TB) in HX. apply Exists_exists in HX as (r & Hr & Hin). unfold Tfib_owned_static in Hr. unfold in_zr in Hin.
cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Hin; lia|]). destruct Hr.
- rewrite (ts_errno B TB). unfold TFIB_ERRNO. lia.
Qed.
Theorem tfib_ff_cells_ok : forall B, TfibSyms B -> ff_cells_law B.
Proof.
intros B TB ly S W mem md HAR HRO. set (H := w_H W). set (m := mrestrict H mem).
pose proof (proj1 HAR) as HM.
assert (C8 : forall a v, const_chk ly a 8%N v = true -> val_mem tfibsegs m a 8 v).
{ intros a v Hc. exact (tfib_const_lookup B TB ly S H mem a 8%nat v HM (const_chk_sound _ _ _ _ Hc)). }
assert (C1 : forall a v, const_chk ly a 1%N v = true -> mbyte tfibsegs m a = Some (Z_to_bv 8 v)).
{ intros a v Hc. pose proof (tfib_const_lookup B TB ly S H mem a 1%nat v HM (const_chk_sound _ _ _ _ Hc) 0%nat ltac:(lia)) as X.
rewrite Z.add_0_r in X. subst m. rewrite X. f_equal. apply bv_eq. unfold YO0f.le_byte. rewrite Z.shiftr_0_r.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !Z.mod_mod by lia. reflexivity. }
assert (ZS : forall lo len i, In (lo, len) Tfib_zero_shadow -> 0 <= i < len / 8 -> mbyte tfibsegs m (SHADOW_OFF + lo / 8 + i) = Some (Z_to_bv 8 0)).
{ intros lo len i Hin Hi. apply tfc_mbyte_of_aview.
pose proof (AR_zshadow_law_ok tfibsegs B ly S W mem md (lo, len) HAR ltac:(right; rewrite (ts_zsh B TB); exact Hin)) as Z0.
exact (Z0 i Hi). }
assert (RO : forall a v, (0x20e00 <= a < 0x20e0d \/ 0x20e60 <= a < 0x20e63) ->
option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)) = Some v -> mbyte tfibsegs m a = Some (Z_to_bv 8 v)).
{ intros a v Ha Hrom. apply tfc_mbyte_of_aview. destruct (tfc_lit_unowned B TB a Ha) as [Hns Hne].
unfold H. rewrite (HRO a ltac:(left; exists Asan.Asan_segment_000; split; [left; reflexivity|]; split; [reflexivity | cbn; lia]) Hns Hne).
exact Hrom. }
assert (SB : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (CELL : forall a n v (bs : list Z), (forall k, (k < n)%nat -> nth k bs 0 = YO0f.le_byte v n k) ->
(forall k, (k < n)%nat -> mbyte tfibsegs m (a + Z.of_nat k) = Some (Z_to_bv 8 (nth k bs 0))) -> val_mem tfibsegs m a n v).
{ intros a n v bs Hb Hm k Hk. rewrite (Hm k Hk), (Hb k Hk). reflexivity. }
split.
-
unfold cells_hold, io_cells, FF_got_fopen, FF_real_fopen, FF_got_cflags, FF_cflags, SH_PATH, SH_WB0, A_PATH, A_WB, AE2k.A_PATH, AE2k.A_WB.
repeat (apply Forall_cons; [cbn [fst snd]; split; [lia|]; split; [lia|] |]); try apply Forall_nil.
+ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd N.to_nat Z.of_N]. split; [rewrite Z.add_0_r; apply C8; vm_compute; reflexivity | lia].
+ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd N.to_nat Z.of_N]. split; [rewrite Z.add_0_r; apply C8; vm_compute; reflexivity | lia].
+ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd N.to_nat Z.of_N]. split; [|lia]. rewrite Z.add_0_r.
apply (CELL _ 8%nat _ [0; 5; 0xf9; 0xf9; 0; 0; 0; 0]); [intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try reflexivity; lia|]. intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; [| | | | | | | | lia].
* replace (2147467712 + Z.of_nat 0) with (SHADOW_OFF + 0x10000 / 8 + 8640) by (rewrite SB; reflexivity). apply (ZS 0x10000 (0x20e08 - 0x10000)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* apply C1. vm_compute. reflexivity.
* apply C1. vm_compute. reflexivity.
* apply C1. vm_compute. reflexivity.
* replace (2147467712 + Z.of_nat 4) with (SHADOW_OFF + 0x20e20 / 8 + 0) by (rewrite SB; reflexivity). apply (ZS 0x20e20 (0x20e60 - 0x20e20)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467712 + Z.of_nat 5) with (SHADOW_OFF + 0x20e20 / 8 + 1) by (rewrite SB; reflexivity). apply (ZS 0x20e20 (0x20e60 - 0x20e20)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467712 + Z.of_nat 6) with (SHADOW_OFF + 0x20e20 / 8 + 2) by (rewrite SB; reflexivity). apply (ZS 0x20e20 (0x20e60 - 0x20e20)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467712 + Z.of_nat 7) with (SHADOW_OFF + 0x20e20 / 8 + 3) by (rewrite SB; reflexivity). apply (ZS 0x20e20 (0x20e60 - 0x20e20)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
+ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd N.to_nat Z.of_N]. split; [|lia]. rewrite Z.add_0_r.
apply (CELL _ 8%nat _ [0; 0; 0; 0; 3; 0xf9; 0xf9; 0xf9]); [intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try reflexivity; lia|]. intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; [| | | | | | | | lia].
* replace (2147467720 + Z.of_nat 0) with (SHADOW_OFF + 0x20e20 / 8 + 4) by (rewrite SB; reflexivity). apply (ZS 0x20e20 (0x20e60 - 0x20e20)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467720 + Z.of_nat 1) with (SHADOW_OFF + 0x20e20 / 8 + 5) by (rewrite SB; reflexivity). apply (ZS 0x20e20 (0x20e60 - 0x20e20)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467720 + Z.of_nat 2) with (SHADOW_OFF + 0x20e20 / 8 + 6) by (rewrite SB; reflexivity). apply (ZS 0x20e20 (0x20e60 - 0x20e20)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467720 + Z.of_nat 3) with (SHADOW_OFF + 0x20e20 / 8 + 7) by (rewrite SB; reflexivity). apply (ZS 0x20e20 (0x20e60 - 0x20e20)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* apply C1. vm_compute. reflexivity.
* apply C1. vm_compute. reflexivity.
* apply C1. vm_compute. reflexivity.
* apply C1. vm_compute. reflexivity.
+ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd N.to_nat Z.of_N]; (split; [|lia]).
* rewrite Z.add_0_r. apply (CELL _ 8%nat _ [0x2f; 0x74; 0x6d; 0x70; 0x2f; 0x6f; 0x75; 0x74]); [intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try reflexivity; lia|].
intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; [| | | | | | | | lia]; (apply RO; [lia | vm_compute; reflexivity]).
* apply (CELL _ 4%nat _ [0x2e; 0x67; 0x69; 0x66]); [intros k Hk; destruct k as [|[|[|[|k]]]]; try reflexivity; lia|].
intros k Hk; destruct k as [|[|[|[|k]]]]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; [| | | | lia]; (apply RO; [lia | vm_compute; reflexivity]).
* apply (CELL _ 1%nat _ [0]); [intros k Hk; destruct k as [|k]; try reflexivity; lia|].
intros k Hk; destruct k as [|k]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; [| lia]; (apply RO; [lia | vm_compute; reflexivity]).
+ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd N.to_nat Z.of_N]. split; [|lia]. rewrite Z.add_0_r.
apply (CELL _ 8%nat _ [0x77; 0x62; 0; 0; 0; 0; 0; 0]); [intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try reflexivity; lia|].
intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; [| | | | | | | | lia]; [apply RO; [lia | vm_compute; reflexivity] | apply RO; [lia | vm_compute; reflexivity] | apply RO; [lia | vm_compute; reflexivity] |
apply C1; vm_compute; reflexivity | apply C1; vm_compute; reflexivity | apply C1; vm_compute; reflexivity | apply C1; vm_compute; reflexivity | apply C1; vm_compute; reflexivity].
-
unfold cells_hold, st_cells, A_WB, AE2k.A_WB.
repeat (apply Forall_cons; [cbn [fst snd]; split; [lia|]; split; [lia|] |]); try apply Forall_nil.
+ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd N.to_nat Z.of_N]. split; [rewrite Z.add_0_r; apply C8; vm_compute; reflexivity | lia].
+ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd N.to_nat Z.of_N]. split; [|lia]. rewrite Z.add_0_r.
apply (CELL _ 8%nat _ [0; 0; 0; 0; 0; 0; 0; 0]); [intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try reflexivity; lia|]. intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; [| | | | | | | | lia].
* replace (2147467296 + Z.of_nat 0) with (SHADOW_OFF + 0x10000 / 8 + 8224) by (rewrite SB; reflexivity). apply (ZS 0x10000 (0x20e08 - 0x10000)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467296 + Z.of_nat 1) with (SHADOW_OFF + 0x10000 / 8 + 8225) by (rewrite SB; reflexivity). apply (ZS 0x10000 (0x20e08 - 0x10000)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467296 + Z.of_nat 2) with (SHADOW_OFF + 0x10000 / 8 + 8226) by (rewrite SB; reflexivity). apply (ZS 0x10000 (0x20e08 - 0x10000)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467296 + Z.of_nat 3) with (SHADOW_OFF + 0x10000 / 8 + 8227) by (rewrite SB; reflexivity). apply (ZS 0x10000 (0x20e08 - 0x10000)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467296 + Z.of_nat 4) with (SHADOW_OFF + 0x10000 / 8 + 8228) by (rewrite SB; reflexivity). apply (ZS 0x10000 (0x20e08 - 0x10000)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467296 + Z.of_nat 5) with (SHADOW_OFF + 0x10000 / 8 + 8229) by (rewrite SB; reflexivity). apply (ZS 0x10000 (0x20e08 - 0x10000)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467296 + Z.of_nat 6) with (SHADOW_OFF + 0x10000 / 8 + 8230) by (rewrite SB; reflexivity). apply (ZS 0x10000 (0x20e08 - 0x10000)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467296 + Z.of_nat 7) with (SHADOW_OFF + 0x10000 / 8 + 8231) by (rewrite SB; reflexivity). apply (ZS 0x10000 (0x20e08 - 0x10000)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
+ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd N.to_nat Z.of_N]. split; [|lia]. rewrite Z.add_0_r.
apply (CELL _ 8%nat _ [0; 0; 0; 0; 3; 0xf9; 0xf9; 0xf9]); [intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try reflexivity; lia|]. intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; [| | | | | | | | lia].
* replace (2147467720 + Z.of_nat 0) with (SHADOW_OFF + 0x20e20 / 8 + 4) by (rewrite SB; reflexivity). apply (ZS 0x20e20 (0x20e60 - 0x20e20)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467720 + Z.of_nat 1) with (SHADOW_OFF + 0x20e20 / 8 + 5) by (rewrite SB; reflexivity). apply (ZS 0x20e20 (0x20e60 - 0x20e20)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467720 + Z.of_nat 2) with (SHADOW_OFF + 0x20e20 / 8 + 6) by (rewrite SB; reflexivity). apply (ZS 0x20e20 (0x20e60 - 0x20e20)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* replace (2147467720 + Z.of_nat 3) with (SHADOW_OFF + 0x20e20 / 8 + 7) by (rewrite SB; reflexivity). apply (ZS 0x20e20 (0x20e60 - 0x20e20)); [cbn; tauto | vm_compute; split; [discriminate | reflexivity]].
* apply C1. vm_compute. reflexivity.
* apply C1. vm_compute. reflexivity.
* apply C1. vm_compute. reflexivity.
* apply C1. vm_compute. reflexivity.
+ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd N.to_nat Z.of_N]. split; [|lia]. rewrite Z.add_0_r.
apply (CELL _ 8%nat _ [0x77; 0x62; 0; 0; 0; 0; 0; 0]); [intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try reflexivity; lia|].
intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; [| | | | | | | | lia]; [apply RO; [lia | vm_compute; reflexivity] | apply RO; [lia | vm_compute; reflexivity] | apply RO; [lia | vm_compute; reflexivity] |
apply C1; vm_compute; reflexivity | apply C1; vm_compute; reflexivity | apply C1; vm_compute; reflexivity | apply C1; vm_compute; reflexivity | apply C1; vm_compute; reflexivity].
Qed.
End c.
