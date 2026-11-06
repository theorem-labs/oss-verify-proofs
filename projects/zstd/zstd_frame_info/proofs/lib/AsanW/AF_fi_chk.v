(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zify_lts K :=
  unfold bv_lts in K; rewrite ?land7_mod in K;
  rewrite !signed_lit_small64 in K by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia);
  zify_bool K.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma chk1A : forall m1 A B a N, unpoisoned m1 A B -> A <= a -> a + N <= B -> 1 <= N -> a mod 8 + N <= 8 ->
  exists b, ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
            /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + N - 1 < sval b)) /\ -128 <= sval b <= 127.
Proof.
  intros m1 A B a N U A0 A1 N1 N8.
  destruct (unpoisoned_check_rd asegs m1 A B a N U A0 A1 N1 N8) as (b & RDB & CK).
  exists b. unfold shad, ASHOFF in RDB. Local Ltac2 Set LiaHints.tbl := fun () => "0010=8454139159.14000001S".
replace (2147450880 + Z.shiftr a 3) with (Z.shiftr a 3 + 2147450880) in RDB by lia.
  split; [exact RDB|]. split; [exact CK| apply sval_range].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
(* [comment removed for export] *)
#[using="Type"] Lemma chkB : forall m1 A B a, unpoisoned m1 A B -> A <= a -> a + 1 <= B ->
  exists b, ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
            /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 < sval b)) /\ -128 <= sval b <= 127.
Proof.
  intros m1 A B a U A0 A1. Local Ltac2 Set LiaHints.tbl := fun () => "0040>40394284147.9 43608420002.9 57212451866.1363368169133.8 00000400500900:S2M8SS2CKS".
pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as M8.
  destruct (chk1A m1 A B a 1 U A0 A1 ltac:(lia) ltac:(lia)) as (b & RDB & CK & SR).
  exists b. split; [exact RDB|]. split; [| exact SR]. destruct CK as [CK|CK]; [left; exact CK| right; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chk8_zero : forall m1 A B a, unpoisoned m1 A B -> A <= a -> a + 8 <= B -> a mod 8 = 0 ->
  ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m1 A B a U A0 A1 A8.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=3455007348.9 48186849906.962329267424.900000700800?S2A12A8SS2A02A8".
replace (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) with (wa (shad a)) by (unfold wa, shad, ASHOFF; f_equal; lia).
  apply (unpoisoned_full_rd asegs m1 A B (shad a) U); rewrite !shad_div; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".


(* [comment removed for export] *)
#[using="Type"] Lemma chkA_802dc : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 y x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80330) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8032c) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_802f0 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x14 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 (Z_to_bv 64 b) x13 y x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80344) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80340) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80340 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80394) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80390) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_803f8 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8044c) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80448) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8041c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80470) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8046c) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8048c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x11 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) y x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x804e0) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x804dc) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80494 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x11 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) y (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x804e8) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x804e4) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80510 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x11 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) y (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80564) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80560) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80524 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80578) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80574) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_805ac : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x16 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 y x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80600) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x805fc) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_805d4 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x16 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 y x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80628) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80624) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_805e8 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x17 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 x15 (Z_to_bv 64 (sval sb)) y x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8063c) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 x15 (Z_to_bv 64 (sval sb)) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80638) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8061c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x16 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 y x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80670) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8066c) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80630 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x17 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 x15 (Z_to_bv 64 (sval sb)) y x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80684) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 x15 (Z_to_bv 64 (sval sb)) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80680) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80698 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x15 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 y x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x806ec) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x806e8) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_806ac : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x17 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 (Z_to_bv 64 (sval sb)) x16 y x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80700) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 (Z_to_bv 64 (sval sb)) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x806fc) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_806f0 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x15 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 y x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80744) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80740) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80704 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x17 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 (Z_to_bv 64 (sval sb)) x16 y x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80758) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 (Z_to_bv 64 (sval sb)) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80754) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80734 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x15 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 y x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80788) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80784) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80748 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x17 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 (Z_to_bv 64 (sval sb)) x16 y x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8079c) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 (Z_to_bv 64 (sval sb)) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80798) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80864 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x15 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 y x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x808b8) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x808b4) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_803dc : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80430) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8042c) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8047c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x15 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 x12 x13 (Z_to_bv 64 (sval sb)) y x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x804d0) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 x12 x13 (Z_to_bv 64 (sval sb)) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x804cc) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_804b8 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x16 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 x12 x13 x14 (Z_to_bv 64 (sval sb)) y x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8050c) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 x12 x13 x14 (Z_to_bv 64 (sval sb)) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80508) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_804f4 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80548) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80544) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_807bc : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x15 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 x12 x13 (Z_to_bv 64 (sval sb)) y x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80810) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 x12 x13 (Z_to_bv 64 (sval sb)) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8080c) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8080c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x14 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 y x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80860) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8085c) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80824 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80878) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80874) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8083c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) (Z_to_bv 64 b) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80890) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8088c) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80ea4 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x11 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) y x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80ef8) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80ef4) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80eb8 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80f0c) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80f08) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80f08 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80f5c) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80f58) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80f1c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) (Z_to_bv 64 b) y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80f70) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80f6c) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
