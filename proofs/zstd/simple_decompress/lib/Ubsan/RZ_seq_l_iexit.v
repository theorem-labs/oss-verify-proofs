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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_iexit : forall P OEND LLO LEND LOCV m1 pre r (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seql_ranges P -> seql_iinv P OEND LLO LEND LOCV m1 (pre ++ seql_saved P) -> cells_size pre = 584%nat ->
  0 <= r < 2^64 -> (zd_is_error r = true \/ r <= y_CAP P) ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 r) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1abb4) (y_fc P) None m1 (seg_rom usegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 pre r x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 RG (FR & _ & _ & _ & _ & _ & _ & _ & H5V & XI) SZ HR RES.
  pose proof (rw_cells_merge usegs m1 (y_SPV P + -688) [] pre (seql_saved P) FR) as FRX. cbn [app] in FRX. rewrite SZ in FRX.
  eapply (seql_p_exit P m1 (cells_bytes pre) r); [exact RG | exact XI | exact H5V | exact FRX | exact HR | exact RES].
Qed.

Lemma seql_iexit_ifr : forall P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 bd st p0 p1 p2 jring jseq r (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seql_ranges P -> seql_iinv P OEND LLO LEND LOCV m1 (seql_ifr P OEND LEND c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 bd st p0 p1 p2 jring jseq) ->
  (cells_size bd + cells_size st = 88)%nat ->
  0 <= r < 2^64 -> (zd_is_error r = true \/ r <= y_CAP P) ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 r) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1abb4) (y_fc P) None m1 (seg_rom usegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 bd st p0 p1 p2 jring jseq r x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 RG INV SBS HR RES.
  unfold seql_ifr in INV. rewrite !app_assoc in INV.
  eapply (seql_iexit P OEND LLO LEND LOCV m1 _ r); [exact RG | exact INV | | exact HR | exact RES].
  rewrite !cells_size_app. cbn [cells_size csize]. lia.
Qed.
