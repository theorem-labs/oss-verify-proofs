(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_xat RZ_seq_s_end.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma seqs_frame_exit : forall P OEND (m1 : fmem) c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq,
  rw_cells usegs m1 (v_SPV P + -384) (seqs_frame P OEND c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq) ->
  exists jpre, rw_cells usegs m1 (v_SPV P + -384) (CB 280 jpre :: seqs_saved P).
Proof.
  intros P OEND m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_frame seqs_saved v_SPV] in *.
  apply (rw_cells_forget _ _ _ 34%nat 280%nat) in FR; [|reflexivity].
  cbn [skipn] in FR. set (X := cells_bytes _) in FR. clearbody X.
  pose proof FR as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (WX & _).
  exists X. eapply rw_cells_recell; [exact FR | | ].
  - cbn [cells_wf cell_wf]. split; [exact WX|]. repeat split.
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma seqs_frame_eframe : forall P OEND (m1 : fmem) c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq,
  rw_cells usegs m1 (v_SPV P + -384) (seqs_frame P OEND c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq) ->
  exists ja jb jc jd je, rw_cells usegs m1 (v_SPV P + -384) ([CB 48 ja; C8 (Z_to_bv 64 (v_DST P)); C8 (Z_to_bv 64 OEND); CB 32 jb; C8 (Z_to_bv 64 (v_DCTX P + 29896)); CB 16 jc; C8 lec; CB 120 jd; C8 (Z_to_bv 64 LP); CB 24 je] ++ seqs_saved P).
Proof.
  intros P OEND m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_frame seqs_saved v_SPV v_DST v_DCTX app] in *.
  pose proof FR as [[WF _] _]. cbn [cells_wf cell_wf] in WF.
  do 5 eexists. eapply rw_cells_recell; [exact FR | | ].
  2: { cbn [cells_bytes cbytes]. rewrite !app_nil_r.
       instantiate (1 := jseq).
       instantiate (1 := cells_bytes [C8 c128; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (MLT + 8)); C8 p0; C8 p1; C8 p2]).
       instantiate (1 := cells_bytes [C8 (Z_to_bv 64 (2^60)); C8 (Z_to_bv 64 PFX)]).
       instantiate (1 := cells_bytes [C8 (Z_to_bv 64 (DCTX + 26684)); C8 (Z_to_bv 64 0); C8 dend; C8 (Z_to_bv 64 PFX)]).
       instantiate (1 := cells_bytes [C8 c0; C8 c8; C8 (Z_to_bv 64 (PFX + 8)); C8 (Z_to_bv 64 (- (SPV - 160) - 1)); C8 (Z_to_bv 64 DCTX); C8 c40]).
       cbn [cells_bytes cbytes]. rewrite !app_nil_r, <- !app_assoc. reflexivity. }
  cbn [cells_wf cell_wf cells_bytes cbytes]. rewrite !length_app, ?length_le8, ?length_le4.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WS & _).
  rewrite WP, WS. repeat split.
Qed.

Lemma seqs_at_err_ok : forall P OEND LLO LEND LOCV, seqs_ranges P -> seqs_at_err P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV RG. unfold seqs_at_err.
  intros m1 c0 c8 c40 c128 cw bc ptr sLL sOF sML p0 p1 p2 LP r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 INV HR RES.
  destruct INV as ((jpad & jseq & FR) & _ & _ & _ & _ & _ & _ & H5V & XI).
  destruct (seqs_frame_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as (jpre & FRX).
  eapply (seqs_p_exit P m1 jpre r); [exact RG | exact XI | exact H5V | exact FRX | exact HR | exact RES].
Qed.

Lemma seqs_at_lexit_ok : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> seqs_ranges P -> seqs_sep P -> seqs_at_lexit P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST RG0 SEP0. unfold seqs_at_lexit.
  intros m1 c0 c8 c40 c128 cw bc ptr sLL sOF sML p0 p1 p2 LP OP x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 INV HOP HLP HBC.
  pose proof (seqs_at_err_ok P OEND LLO LEND LOCV RG0) as AERR. unfold seqs_at_err in AERR.
  pose proof (seqs_p_last1 P) as PL1. pose proof (seqs_p_last2 P) as PL2. pose proof (seqs_frame_eframe P OEND) as EFR.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _ & _ & _ & _ & LIT & XLIT & (H5C & H5L) & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_frame seqs_xinv seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, FR, LIT, XLIT, H5C, XI, HOP, AERR, PL1, PL2, EFR |- *.
  sd_static_open ST.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold h5_vcells in H5C. unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= DCTX < 2^47 /\
               0 <= LEND - LP <= 2^47 /\ 0 <= OEND - OP <= 2^47 /\ 0 <= bc <= 2147483647 /\ 0 <= LOCV <= 2)
    by (clear - HOP HLP S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 S19 S20 S41 HBC; lia).
  assert (DJ : SPV - 384 + 384 <= DCTX \/ DCTX + 95992 <= SPV - 384) by (unfold held in S27; clear - S27 S18; lia).
  assert (MUL : munch [(DCTX + 26684, DCTX + 26684 + 12)] m1 m1) by apply munch_refl.
  hold AERR. hold PL1. hold PL2. hold EFR. hold INV. hold RG0. hold SEP0. hold LIT. hold XLIT. hold OKLL. hold OKOF. hold OKML.
  kx_autoLx [0x1c6fc; 0x1b99c; 0x1c6b8] 60%nat [KZRange SPV 592 (2^47); KZRange DCTX 4096 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange OEND 4096 (2^47); KZRange bc 0 2147483647; KZRange LOCV 0 2; KZWr (DCTX + 26684) 12; KZDisj (SPV - 384) 384 DCTX 95992] [(SPV - 384, 384); (DCTX + 30096, 276)].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end).
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c6fc) _ _ _ _) => unfold held in *; eapply AERR; [exact INV | lia | left; reflexivity] end).
  all: kx_mem.
  all: unfold held in *.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (XL2 : rdbl usegs mm (DCTX + 30372) (DCTX + 95940)) by (eapply rdbl_transport; [exact XLIT | exact MUL | intros x' Hx; left; cbn [outside]; split; [lia| exact I]]);
      assert (LIT2 : rdbl usegs mm LLO (LEND + 32)) by (eapply rdbl_transport; [exact LIT | exact MUL | intros x' Hx; left; cbn [outside]; split; [clear - S36 Hx; lia| exact I]]);
      destruct (EFR mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as (ja & jb & jc & jd & je & FRE) end.
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1b99c) _ _ ?mm _) =>
      assert (LE32 : B0 <= LLO /\ LEND + 32 <= OEND) by (clear - S42 KXBR1; lia);
      eapply (PL1 mm ja jb jc jd je OEND OP LP LEND (Z_to_bv 64 LP) (Z_to_bv 64 LOCV)); [exact RG0 | exact SEP0 | | split; [exact H5C | exact H5L] | exact FRE | lia | lia | lia | lia | lia | lia | lia | exact XL2];
      split; [exists p0, p1, p2; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| exact KXMI]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c6b8) _ _ ?mm _) =>
      assert (DJX : LEND <= OP \/ OEND <= LP) by (clear - S42 KXBR1 HOP HLP S1 S2 S3 S4 S5 S6; lia);
      eapply (PL2 mm ja jb jc jd je OEND OP LP LEND (Z_to_bv 64 LP) (Z_to_bv 64 LOCV)); [exact RG0 | exact SEP0 | | split; [exact H5C | exact H5L] | exact FRE | lia | lia | lia | lia | lia | lia | eapply rdbl_sub; [exact LIT2 | lia | lia] | exact DJX];
      split; [exists p0, p1, p2; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| exact KXMI]
  end.
Qed.
