(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section LE64FT.
  Variables (sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x29 x30 x31 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (S : Z) (bs : list Z) (POST : machine_state -> Prop).
  Hypothesis SRC : bytes_at usegs m S (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.

  Ltac ldb0 p k :=
    let RX := fresh "RX" in
    pose proof (src_rd usegs m S bs (p + k) SRC ltac:(lia)) as RX;
    rewrite ?Z.add_assoc, ?Z.add_0_r in RX;
    zstep; cbv beta; clear RX.

  (* [comment removed for export] *)
  Lemma ft_ld1 : forall (p : Z) (y1 y17 y25 y26 y27 y28 : word),
    0 <= p -> p + 8 <= zlen bs ->
    (forall (z1 z17 z25 z26 z27 : word),
       evt usegs POST (MS (mkR z1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 z17 x18 x19 x20 x21 x22 x23
                               (Z_to_bv 64 (S + p)) z25 z26 z27 (Z_to_bv 64 (le64v bs p)) x29 x30 x31)
                          F (Z_to_bv 64 (PFSE_DECOMP + 4056)) fc None m (seg_rom usegs))) ->
    evt usegs POST (MS (mkR y1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 y17 x18 x19 x20 x21 x22 x23
                            (Z_to_bv 64 (S + p)) y25 y26 y27 y28 x29 x30 x31)
                       F (Z_to_bv 64 (PFSE_DECOMP + 3968)) fc None m (seg_rom usegs)).
  Proof.
    intros p y1 y17 y25 y26 y27 y28 P0 P8 K.
    pose proof (src_rd usegs m S bs p SRC ltac:(lia)) as RX0.
    pose proof (src_rd usegs m S bs (p + 1) SRC ltac:(lia)) as RX1.
    pose proof (src_rd usegs m S bs (p + 2) SRC ltac:(lia)) as RX2.
    pose proof (src_rd usegs m S bs (p + 3) SRC ltac:(lia)) as RX3.
    pose proof (src_rd usegs m S bs (p + 4) SRC ltac:(lia)) as RX4.
    pose proof (src_rd usegs m S bs (p + 5) SRC ltac:(lia)) as RX5.
    pose proof (src_rd usegs m S bs (p + 6) SRC ltac:(lia)) as RX6.
    pose proof (src_rd usegs m S bs (p + 7) SRC ltac:(lia)) as RX7.
    pose proof (byte_Znth bs p BY ltac:(lia)) as B0. pose proof (byte_Znth bs (p + 1) BY ltac:(lia)) as B1.
    pose proof (byte_Znth bs (p + 2) BY ltac:(lia)) as B2. pose proof (byte_Znth bs (p + 3) BY ltac:(lia)) as B3.
    pose proof (byte_Znth bs (p + 4) BY ltac:(lia)) as B4. pose proof (byte_Znth bs (p + 5) BY ltac:(lia)) as B5.
    pose proof (byte_Znth bs (p + 6) BY ltac:(lia)) as B6. pose proof (byte_Znth bs (p + 7) BY ltac:(lia)) as B7.
    unfold PFSE_DECOMP. cbn [Z.add].
    repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 132624) _ _ _ _) => fail
      | |- _ => zstep end).
    rewrite le64_lbu_raw by lia.
    apply K.
  Qed.

  (* [comment removed for export] *)
  Lemma ft_ld2 : forall (p : Z) (y1 y17 y25 y26 y27 y28 : word),
    0 <= p -> p + 8 <= zlen bs ->
    (forall (z1 z17 z25 z26 z27 : word),
       evt usegs POST (MS (mkR z1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 z17 x18 x19 x20 x21 x22 x23
                               (Z_to_bv 64 (S + p)) z25 z26 z27 (Z_to_bv 64 (le64v bs p)) x29 x30 x31)
                          F (Z_to_bv 64 (PFSE_DECOMP + 4396)) fc None m (seg_rom usegs))) ->
    evt usegs POST (MS (mkR y1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 y17 x18 x19 x20 x21 x22 x23
                            (Z_to_bv 64 (S + p)) y25 y26 y27 y28 x29 x30 x31)
                       F (Z_to_bv 64 (PFSE_DECOMP + 4308)) fc None m (seg_rom usegs)).
  Proof.
    intros p y1 y17 y25 y26 y27 y28 P0 P8 K.
    pose proof (src_rd usegs m S bs p SRC ltac:(lia)) as RX0.
    pose proof (src_rd usegs m S bs (p + 1) SRC ltac:(lia)) as RX1.
    pose proof (src_rd usegs m S bs (p + 2) SRC ltac:(lia)) as RX2.
    pose proof (src_rd usegs m S bs (p + 3) SRC ltac:(lia)) as RX3.
    pose proof (src_rd usegs m S bs (p + 4) SRC ltac:(lia)) as RX4.
    pose proof (src_rd usegs m S bs (p + 5) SRC ltac:(lia)) as RX5.
    pose proof (src_rd usegs m S bs (p + 6) SRC ltac:(lia)) as RX6.
    pose proof (src_rd usegs m S bs (p + 7) SRC ltac:(lia)) as RX7.
    pose proof (byte_Znth bs p BY ltac:(lia)) as B0. pose proof (byte_Znth bs (p + 1) BY ltac:(lia)) as B1.
    pose proof (byte_Znth bs (p + 2) BY ltac:(lia)) as B2. pose proof (byte_Znth bs (p + 3) BY ltac:(lia)) as B3.
    pose proof (byte_Znth bs (p + 4) BY ltac:(lia)) as B4. pose proof (byte_Znth bs (p + 5) BY ltac:(lia)) as B5.
    pose proof (byte_Znth bs (p + 6) BY ltac:(lia)) as B6. pose proof (byte_Znth bs (p + 7) BY ltac:(lia)) as B7.
    unfold PFSE_DECOMP. cbn [Z.add].
    repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 132964) _ _ _ _) => fail
      | |- _ => zstep end).
    rewrite le64_lbu_raw by lia.
    apply K.
  Qed.
End LE64FT.
