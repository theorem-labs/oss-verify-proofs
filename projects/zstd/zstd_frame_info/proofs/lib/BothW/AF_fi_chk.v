(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase.
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
  exists b, ov_read_bytes bsegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
            /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + N - 1 < sval b)) /\ -128 <= sval b <= 127.
Proof.
  intros m1 A B a N U A0 A1 N1 N8.
  destruct (unpoisoned_check_rd bsegs m1 A B a N U A0 A1 N1 N8) as (b & RDB & CK).
  exists b. unfold shad, ASHOFF in RDB. Local Ltac2 Set LiaHints.tbl := fun () => "0010=8454139159.14000001S".
replace (2147450880 + Z.shiftr a 3) with (Z.shiftr a 3 + 2147450880) in RDB by lia.
  split; [exact RDB|]. split; [exact CK| apply sval_range].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
(* [comment removed for export] *)
#[using="Type"] Lemma chkB : forall m1 A B a, unpoisoned m1 A B -> A <= a -> a + 1 <= B ->
  exists b, ov_read_bytes bsegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
            /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 < sval b)) /\ -128 <= sval b <= 127.
Proof.
  intros m1 A B a U A0 A1. Local Ltac2 Set LiaHints.tbl := fun () => "0040>40394284147.9 43608420002.9 57212451866.1363368169133.8 00000400500900:S2M8SS2CKS".
pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as M8.
  destruct (chk1A m1 A B a 1 U A0 A1 ltac:(lia) ltac:(lia)) as (b & RDB & CK & SR).
  exists b. split; [exact RDB|]. split; [| exact SR]. destruct CK as [CK|CK]; [left; exact CK| right; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chk8_zero : forall m1 A B a, unpoisoned m1 A B -> A <= a -> a + 8 <= B -> a mod 8 = 0 ->
  ov_read_bytes bsegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m1 A B a U A0 A1 A8.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=3455007348.9 48186849906.962329267424.900000700800?S2A12A8SS2A02A8".
replace (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) with (wa (shad a)) by (unfold wa, shad, ASHOFF; f_equal; lia).
  apply (unpoisoned_full_rd bsegs m1 A B (shad a) U); rewrite !shad_div; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".


(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8030c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x11 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) y x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80358) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80354) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8036c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 y x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x803b8) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x803b4) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80380 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x15 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 (Z_to_bv 64 b) x13 x14 y x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x803cc) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x803c8) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_803d4 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80420) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8041c) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_804a0 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) (Z_to_bv 64 b) x12 y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x804ec) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x804e8) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_804c4 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80510) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8050c) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_804f4 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80540) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8053c) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8055c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x15 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 x12 x13 (Z_to_bv 64 (sval sb)) y x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x805a8) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 x12 x13 (Z_to_bv 64 (sval sb)) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x805a4) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8056c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x11 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) y x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x805b8) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x805b4) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80574 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x11 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) y (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x805c0) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x805bc) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80598 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x16 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 x12 x13 x14 (Z_to_bv 64 (sval sb)) y x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x805e4) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 x12 x13 x14 (Z_to_bv 64 (sval sb)) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x805e0) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_805d4 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80620) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8061c) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_805f8 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x11 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) y (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80644) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80640) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8060c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80658) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80654) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80694 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x16 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 y x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x806e0) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x806dc) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_806c4 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x16 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 y x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80710) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8070c) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_806d8 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x17 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 x15 (Z_to_bv 64 (sval sb)) y x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80724) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 x15 (Z_to_bv 64 (sval sb)) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80720) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80714 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x16 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 y x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80760) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8075c) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80728 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x17 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 x15 (Z_to_bv 64 (sval sb)) y x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80774) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 x14 x15 (Z_to_bv 64 (sval sb)) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80770) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80798 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x14 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 y x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x807e4) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x807e0) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_807ac : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x17 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 (Z_to_bv 64 (sval sb)) x15 x16 y x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x807f8) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 (Z_to_bv 64 (sval sb)) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x807f4) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_807f8 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x14 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 y x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80844) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80840) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8080c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x17 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 (Z_to_bv 64 (sval sb)) x15 x16 y x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80858) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 (Z_to_bv 64 (sval sb)) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80854) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8083c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x15 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 x12 x13 (Z_to_bv 64 (sval sb)) y x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80888) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 x12 x13 (Z_to_bv 64 (sval sb)) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80884) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8088c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x14 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 y x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x808d8) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x808d4) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_808a4 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x808f0) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x808ec) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_808bc : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 3 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) (Z_to_bv 64 b) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80908) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80904) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4546931632035.4659308692554.4667499333341.4600000700;00D00JS2CK2HbS2SRS2CK1G2G'S2CK1G".
if_cases G; zify_cond G.
  - zstep. zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_808ec : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x14 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 y x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80938) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80934) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_80900 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x17 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 (Z_to_bv 64 (sval sb)) x15 x16 y x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8094c) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 b) x13 (Z_to_bv 64 (sval sb)) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80948) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_8097c : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x14 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 y x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x809c8) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x809c4) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
