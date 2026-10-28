(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase RZ_seq_l_ient2a RZ_seq_l_ient2b RZ_seq_l_ient2c RZ_seq_l_ient2d.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_entry : forall (P : slp) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
  seql_mem P -> seql_ranges P -> seql_side P -> seql_sep P -> seql_tables P -> y_nbSeq P <> 0 ->
  (forall OEND, (1 <= zlen (y_sq P) -> seql_static P OEND (y_LITP P) (y_LBE P) (y_LOC P)) -> ai_i0 P OEND (y_LITP P) (y_LBE P) (y_LOC P)) ->
  evt usegs (seql_post P)
    (MS (mkR (y_ra P) (Z_to_bv 64 (y_SPV P)) (y_gp P) (y_tp P) t0 t1 t2 (y_s0 P) (y_s1 P) (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (y_DST P))
             (Z_to_bv 64 (y_CAP P)) (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 (zlen (y_sq P))) (Z_to_bv 64 (y_nbSeq P)) a6 a7
             (y_s2 P) (y_s3 P) (y_s4 P) (y_s5 P) (y_s6 P) (y_s7 P) (y_s8 P) (y_s9 P) (y_s10 P) (y_s11 P) t3 t4 t5 t6)
        (y_F P) (Z_to_bv 64 0x17a94) (y_fc P) None (y_m P) (seg_rom usegs)).
Proof.
  intros P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP TBL NZ CONT.
  assert (LOCK : (y_LOC P = 0 /\ y_CAP P <= 0) \/ (y_LOC P = 0 /\ 1 <= y_CAP P) \/ y_LOC P = 1 \/ y_LOC P = 2).
  { clear - SIDE. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seql_side y_LOC y_CAP] in *. destruct SIDE as (_ & _ & _ & D4 & _). unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split in D4. lia. }
  destruct LOCK as [H|[H|[H|H]]].
  - exact (seql_entry_a P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP TBL NZ H CONT).
  - exact (seql_entry_b P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP TBL NZ H CONT).
  - exact (seql_entry_c P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP TBL NZ H CONT).
  - exact (seql_entry_d P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP TBL NZ H CONT).
Qed.
