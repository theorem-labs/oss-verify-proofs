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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_xat RZ_seq_l_lf_at RZ_seq_l_end.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma seql_frame_exit : forall P OEND (m1 : fmem) c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq,
  rw_cells usegs m1 (y_SPV P + -688) (seql_frame P OEND c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq) ->
  exists jpre, rw_cells usegs m1 (y_SPV P + -688) (CB 584 jpre :: seql_saved P).
Proof.
  intros P OEND m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_frame seql_saved y_SPV] in *.
  apply (rw_cells_forget _ _ _ 49%nat 584%nat) in FR; [|reflexivity].
  cbn [skipn] in FR. set (X := cells_bytes _) in FR. clearbody X.
  pose proof FR as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (WX & _).
  exists X. eapply rw_cells_recell; [exact FR | | ].
  - cbn [cells_wf cell_wf]. split; [exact WX|]. repeat split.
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma seql_frame_eframe : forall P OEND (m1 : fmem) c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq,
  rw_cells usegs m1 (y_SPV P + -688) (seql_frame P OEND c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq) ->
  exists ja jb jc jd, rw_cells usegs m1 (y_SPV P + -688) ([CB 96 ja; C8 (Z_to_bv 64 (y_DST P)); CB 56 jb; C8 (Z_to_bv 64 OEND); CB 72 jc; C8 c240; CB 336 jd] ++ seql_saved P).
Proof.
  intros P OEND m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_frame seql_saved y_SPV y_DST app] in *.
  pose proof FR as [[WF _] _]. cbn [cells_wf cell_wf] in WF.
  repeat match type of WF with _ /\ _ => let W := fresh "W" in destruct WF as (W & WF) end.
  lazymatch type of FR with rw_cells _ _ _ ?L =>
    exists (cells_bytes (firstn 12 L)), (cells_bytes (firstn 7 (skipn 13 L))), (cells_bytes (firstn 9 (skipn 21 L))), (cells_bytes (firstn 18 (skipn 31 L))) end.
  eapply rw_cells_recell; [exact FR | | ].
  - cbn [firstn skipn cells_wf cell_wf cells_bytes cbytes]. rewrite ?length_app, ?length_le8, ?length_le4. cbn [length]. repeat split; lia.
  - cbn [firstn skipn cells_bytes cbytes]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma seql_at_err_ok : forall P OEND LLO LEND LOCV, seql_ranges P -> seql_at_err P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV RG. unfold seql_at_err.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP r x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV HR RES.
  destruct INV as ((jpad & jseq & FR) & _ & _ & _ & _ & _ & _ & H5V & XI).
  apply seql_frame_exit in FR. destruct FR as (jpre & FRX).
  eapply (seql_p_exit P m1 jpre r); [exact RG | exact XI | exact H5V | exact FRX | exact HR | exact RES].
Qed.

Lemma seql_lf_end_ok : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> seql_ranges P -> seql_sep P -> lf_end P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST RG0 SEP0. unfold lf_end.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 INV HOP HLP.
  pose proof (seql_p_last1 P) as PL1. pose proof (seql_p_last2 P) as PL2. pose proof (seql_frame_eframe P OEND) as EFR.
  pose proof INV as MI. apply seql_linv_mi in MI.
  pose proof INV as ((jpad & jseq & FR) & _ & _ & _ & _ & LIT & XLIT & (H5C & H5L) & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_xinv seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, LIT, XLIT, H5C, XI, HOP, PL1, PL2, EFR |- *.
  sd_static_open ST.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold h5_vcells in H5C. unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= DCTX < 2^47 /\ 4096 <= DST < 2^47 /\
               0 <= LEND - LP <= 2^47 /\ 0 <= OEND - OP <= 2^47 /\ 0 <= LOCV <= 2)
    by (clear - HOP HLP S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 S19 S20 S41; lia).
  assert (DJ : SPV - 688 + 688 <= DCTX \/ DCTX + 95992 <= SPV - 688) by (unfold held in S27; clear - S27 S18; lia).
  assert (MUL : munch [(DCTX + 26684, DCTX + 26684 + 12)] m1 m1) by apply munch_refl.
  hold PL1. hold PL2. hold EFR. hold INV. hold RG0. hold SEP0. hold LIT. hold XLIT. hold OKLL. hold OKOF. hold OKML.
  kx_autoLx [0x18330; 0x1ab6c] 60%nat [KZRange SPV 896 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange OEND 4096 (2^47); KZRange LOCV 0 2; KZWr (DCTX + 26684) 12; KZDisj (SPV - 688) 688 DCTX 95992] [(SPV - 688, 688); (DCTX + 30096, 276)].
  all: kx_mem.
  all: unfold held in *.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (LIT2 : rdbl usegs mm LLO (LEND + 32)) by (eapply rdbl_transport; [exact LIT | exact MUL | intros x' Hx; left; cbn [outside]; split; [clear - S36 Hx; lia| exact I]]);
      destruct (EFR mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as (ja & jb & jc & jd & FRE) end.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18330) _ _ ?mm _) =>
    assert (LE32 : B0 <= LLO /\ LEND + 32 <= OEND) by (clear - S42 KXBR; lia);
    assert (XL2 : rdbl usegs mm (DCTX + 30372) (DCTX + 95940)) by (eapply rdbl_transport; [exact (XLIT ltac:(clear - KXBR; lia)) | exact MUL | intros x' Hx; left; cbn [outside]; split; [lia| exact I]]);
    eapply (PL1 mm ja jb jc jd OEND OP LP LEND (Z_to_bv 64 LOCV)); [exact RG0 | exact SEP0 | | split; [exact H5C | exact H5L] | exact FRE | lia | lia | lia | lia | lia | lia | lia | exact XL2]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ab6c) _ _ ?mm _) =>
    eapply (PL2 mm ja jb jc jd OEND OP LP LEND (Z_to_bv 64 LOCV)); [exact RG0 | exact SEP0 | | split; [exact H5C | exact H5L] | exact FRE | lia | lia | lia | lia | lia | lia | eapply rdbl_sub; [exact LIT2 | lia | lia]]
  end.
  all: (split; [exists p0, p1, p2; exact REP|]); (split; [exact HH3|]); (split; [exact BUF|]); (split; [exact STK|]); (split; [exact MU|]); (split; [exact WM| exact KXMI]).
Qed.
