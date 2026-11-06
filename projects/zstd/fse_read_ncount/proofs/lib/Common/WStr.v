(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import MState Mem Cells Step Arr Bytes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
Import ListNotations.
Open Scope Z_scope.
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. unfold le4, le_bytes_to_word.
pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
change (256 ^ Z.of_nat 4) with (2^32) in HR. rewrite <- bytes_le_to_Z_le_val in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Lemma u32s_of_bytes : forall k (bs : list byte), length bs = (4 * k)%nat ->
exists ws, length ws = k /\ u32s ws = bs.
Proof.
induction k as [|k IH]; intros bs HL.
- exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
- destruct (IH (skipn 4 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hlen & Hu).
exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [cbn; lia|].
cbn [u32s]. rewrite Hu, le4_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn.
Qed.
Lemma u32arr_of_u8arr : forall segs m A bs k,
u8arr segs m A bs -> length bs = (4 * k)%nat ->
exists ws, length ws = k /\ u32s ws = bs /\ u32arr segs m A ws.
Proof.
intros segs m A bs k [Hb Hw] HL.
destruct (u32s_of_bytes k bs HL) as (ws & Hlen & Hu). exists ws. split; [exact Hlen|]. split; [exact Hu|]. split.
- rewrite Hu. exact Hb.
- rewrite Hlen. replace (4 * Z.of_nat k) with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.
Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof.
intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length.
replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact Hw.
Qed.
