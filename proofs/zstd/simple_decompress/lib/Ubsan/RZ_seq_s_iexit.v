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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqs_iexit : forall P OEND LLO LEND LOCV m1 fr r (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  seqs_ranges P -> seqs_iinv P OEND LLO LEND LOCV m1 fr -> cells_size (firstn 29 fr) = 280%nat -> skipn 29 fr = [CB 104 (le8 (v_s11 P) ++ le8 (v_s10 P) ++ le8 (v_s9 P) ++ le8 (v_s8 P) ++ le8 (v_s7 P) ++ le8 (v_s6 P) ++ le8 (v_s5 P) ++ le8 (v_s4 P) ++ le8 (v_s3 P) ++ le8 (v_s2 P) ++ le8 (v_s1 P) ++ le8 (v_s0 P) ++ le8 (v_ra P))] ->
  0 <= r < 2^64 -> (zd_is_error r = true \/ r <= v_CAP P) ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 r) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c6fc) (v_fc P) None m1 (seg_rom usegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 fr r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 RG (FR & _ & _ & _ & _ & _ & _ & _ & H5V & XI) SZ SK HR RES.
  apply (rw_cells_forget _ _ _ 29%nat 280%nat) in FR; [|exact SZ]. rewrite SK in FR.
  set (X := cells_bytes _) in FR. clearbody X.
  assert (FRX : rw_cells usegs m1 (v_SPV P + -384) (CB 280 X :: seqs_saved P)).
  { pose proof FR as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (WX & _).
    eapply rw_cells_recell; [exact FR | | ].
    - clear - WX. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqs_saved cells_wf cell_wf]. split; [exact WX|]. repeat split.
    - clear. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqs_saved cells_bytes cbytes v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws]. rewrite !app_nil_r. reflexivity. }
  eapply (seqs_p_exit P m1 X r); [exact RG | exact XI | exact H5V | exact FRX | exact HR | exact RES].
Qed.
