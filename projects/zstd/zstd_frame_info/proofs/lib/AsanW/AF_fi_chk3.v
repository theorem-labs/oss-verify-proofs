(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase AF_fi_chk.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_7fee0 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x7ff34) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x7ff30) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_7fef4 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) (Z_to_bv 64 b) y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x7ff48) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x7ff44) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_7ffbc : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80010) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8000c) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_81d90 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81de4) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81de0) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_81da4 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x15 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) x12 (Z_to_bv 64 b) x14 y x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81df8) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) x12 (Z_to_bv 64 b) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81df4) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_81dc0 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x10 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y (Z_to_bv 64 b) x12 (Z_to_bv 64 (sval sb)) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81e14) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12 (Z_to_bv 64 (sval sb)) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81e10) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_815b0 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x11 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) y x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81604) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81600) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_815c4 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81618) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81614) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_81610 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81664) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81660) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_81624 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv asegs m ->
  (forall y : word, evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81678) fc None m (seg_rom asegs))) ->
  evtF asegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81674) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
