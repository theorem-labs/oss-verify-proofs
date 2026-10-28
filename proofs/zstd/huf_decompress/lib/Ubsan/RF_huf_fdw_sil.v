(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_fil.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section LE64SI.
  Variables (ra sp gp tp x6 x7 x8 x9 x10 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (S : Z) (bs : list Z) (POST : machine_state -> Prop).
  Hypothesis SRC : bytes_at usegs m S (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.
  (* [comment removed for export] *)
  Lemma si_ld : forall (p : Z) (y5 y11 y12 y13 y14 y15 : word),
    0 <= p -> p + 8 <= zlen bs ->
    (forall (z5 z12 z13 z14 z15 : word),
       evt usegs POST (MS (mkR ra sp gp tp z5 x6 x7 x8 x9 x10 (Z_to_bv 64 (le64v bs p)) z12 z13 z14 z15 (Z_to_bv 64 (S + p))
                               x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x1fa50) fc None m (seg_rom usegs))) ->
    evt usegs POST (MS (mkR ra sp gp tp y5 x6 x7 x8 x9 x10 y11 y12 y13 y14 y15 (Z_to_bv 64 (S + p))
                            x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1f9f8) fc None m (seg_rom usegs)).
  Proof.
    intros p y5 y11 y12 y13 y14 y15 P0 P8 K.
    assert (BYn : forall i, 0 <= i < zlen bs -> 0 <= Znth i bs < 256) by (intros; apply byte_Znth; auto).
    fi_src8 S bs SRC p.
    do 22 zstep.
    rewrite le64_lbu_raw by (apply BYn; lia).
    rewrite Z.add_0_r. apply K.
  Qed.
End LE64SI.
(* [comment removed for export] *)
