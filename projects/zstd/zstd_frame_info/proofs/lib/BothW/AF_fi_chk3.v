(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase AF_fi_chk.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_7fef0 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x7ff3c) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 (Z_to_bv 64 (sval sb)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x7ff38) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_7ff04 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) (Z_to_bv 64 b) y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x7ff50) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) (Z_to_bv 64 b) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x7ff4c) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_7ffd8 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80024) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x80020) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_81f64 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x13 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81fb0) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81fac) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_81f78 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x15 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) x12 (Z_to_bv 64 b) x14 y x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81fc4) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) x12 (Z_to_bv 64 b) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81fc0) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_81f94 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x10 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y (Z_to_bv 64 b) x12 (Z_to_bv 64 (sval sb)) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81fe0) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12 (Z_to_bv 64 (sval sb)) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81fdc) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_81744 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x11 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) y x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81790) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sval sb)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8178c) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_81758 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x817a4) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x817a0) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_817ac : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x817f8) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x817f4) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chkA_817c0 : forall (RNG : footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x12 : word) (sb : byte) (b : Z)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Q : machine_state -> Prop),
  (sval sb = 0 \/ (0 < sval sb <= 7 /\ b mod 8 + 0 < sval sb)) -> -128 <= sval sb <= 127 -> 0 <= b < 2^64 ->
  mem_inv bsegs m ->
  (forall y : word, evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) y x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8180c) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sval sb)) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 b) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x81808) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros CK SR Hb MI K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20694722321.4537827810569.4646931632035.4659308692554.4600000700=00A00JS2CK2HbS2CK1GS2SRS2CK1G2G'".
if_cases G; zify_cond G.
  - zstep. zstep. if_cases G'; zify_lts G'; [apply K| exfalso; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
  - apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
