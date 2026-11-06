(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_iexit : forall P OEND LLO LEND LOCV m1 fr r (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  seql_ranges P -> seql_iinv P OEND LLO LEND LOCV m1 fr -> cells_size (firstn 39 fr) = 504%nat -> skipn 39 fr = [CB 104 (le8 (y_s11 P) ++ le8 (y_s10 P) ++ le8 (y_s9 P) ++ le8 (y_s8 P) ++ le8 (y_s7 P) ++ le8 (y_s6 P) ++ le8 (y_s5 P) ++ le8 (y_s4 P) ++ le8 (y_s3 P) ++ le8 (y_s2 P) ++ le8 (y_s1 P) ++ le8 (y_s0 P) ++ le8 (y_ra P))] ->
  0 <= r < 2^64 -> (zd_is_error r = true \/ r <= y_CAP P) ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 r) x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18c10) (y_fc P) None m1 (seg_rom psegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 fr r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 RG (FR & _ & _ & _ & _ & _ & _ & _ & H5V & XI) SZ SK HR RES.
  apply (rw_cells_forget _ _ _ 39%nat 504%nat) in FR; [|exact SZ]. rewrite SK in FR.
  set (X := cells_bytes _) in FR. clearbody X.
  assert (FRX : rw_cells psegs m1 (y_SPV P + -608) (CB 504 X :: seql_saved P)).
  { pose proof FR as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (WX & _).
    eapply rw_cells_recell; [exact FR | | ].
    - clear - WX. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seql_saved cells_wf cell_wf]. split; [exact WX|]. repeat split.
    - clear. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seql_saved cells_bytes cbytes y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws]. rewrite !app_nil_r. reflexivity. }
  eapply (seql_p_exit P m1 X r); [exact RG | exact XI | exact H5V | exact FRX | exact HR | exact RES].
Qed.
