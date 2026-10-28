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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_huf_iface RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_ibase RZ_seq_s_iexit seqD_kit_bitinit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqs_bitinit : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> seqs_ranges P -> ai_i1 P OEND LLO LEND LOCV -> ai_i0 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST RG0 CONT. unfold ai_i0.
  intros m1 c0 c8 c16 c24 c40 c72 c104 c128 u176 u184 u192 u200 u208 u216 p0 p1 p2 jbd jseq x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV.
  pose proof (seqs_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seqs_iexit P OEND LLO LEND LOCV) as IEXIT.
  pose proof (seqs_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i1 in CONT.
  destruct INV as (FR & PT & _ & _ & _ & SQB & _).
  unfold seqs_ifr in FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, FR, PT, SQB, CONT, TRANS |- *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  apply rw_cells_app in FR. destruct FR as (PRE & FR). apply rw_cells_app in FR. destruct FR as (BDC & POST).
  lazymatch type of BDC with rw_cells _ _ ?A _ => replace A with (SPV + -248) in BDC by (cbn [cells_size csize Nat.add]; lia) end.
  pose proof seqd_bit_init_proof as BIP. unfold seqd_bit_init_stmt, PZD_BITINIT in BIP.
  eapply evt_cut.
  { eapply (BIP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SPV + -248) SEQ (zlen sq) (map (Z_to_bv 8) sq) jbd);
      [ exact MI | exact BDC | clear - AL4; lia | exact SQB | first [rewrite length_map; reflexivity | unfold zlen; rewrite length_map; reflexivity]
      | clear - S18; lia | clear - S17; lia | clear - S13; lia | clear - S14; lia | clear - S18 S25; unfold held in S25; lia ]. }
  clear BIP BDC.
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & r & -> & MUc & WMc & MIc & RES).
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?nr)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 nr)) with (Z_to_bv 64 nr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  assert (MUW : munch [(SPV - 384, SPV)] m1 m2) by (eapply munch_weaken; [|exact MUc]; unfold sub_fp; cbn [outside]; intros xq Hxq; clear - Hxq; lia).
  lazymatch type of PRE with rw_cells _ _ ?A ?cs => assert (PRE2 : rw_cells usegs m2 A cs)
    by (eapply rw_cells_transport; [exact PRE | exact MUc | exact WMc | cbn [disjoint_from app cells_size csize Nat.add]; split; [lia | exact I]]) end.
  lazymatch type of POST with rw_cells _ _ ?A ?cs => assert (POST2 : rw_cells usegs m2 A cs)
    by (eapply rw_cells_transport; [exact POST | exact MUc | exact WMc | cbn [disjoint_from app cells_size csize Nat.add]; split; [lia | exact I]]) end.
  assert (PT2 : rw_cells usegs m2 DCTX [C8 (Z_to_bv 64 LLT); C8 (Z_to_bv 64 MLT); C8 (Z_to_bv 64 OFT); C8 huf])
    by (eapply rw_cells_transport; [exact PT | exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [unfold held in S27; clear - S18 S20 S27; lia | exact I]]).
  clear PRE POST PT SQB MI MUc.
  destruct RES as [(-> & HN1 & cont & bc & pad & HBC & HB8 & BDC2) | (ER & HR & bs & BDC2)]; [unfold bitd_cells in BDC2 | apply zd_is_error_true_iff in ER].
  all: lazymatch type of PRE2 with rw_cells _ _ _ ?c1 => lazymatch type of POST2 with rw_cells _ _ ?A2 ?c2 => lazymatch type of BDC2 with rw_cells _ _ _ ?cb =>
    assert (FR2 : rw_cells usegs m2 (SPV + -384) (c1 ++ cb ++ c2))
      by (apply rw_cells_app; split; [exact PRE2 | apply rw_cells_app; split;
          [ lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (SPV + -248) by (cbn [cells_size csize Nat.add]; lia) end; exact BDC2
          | lazymatch goal with |- rw_cells _ _ ?A _ => replace A with A2 by (cbn [cells_size csize Nat.add]; lia) end; exact POST2 ]]) end end end.
  all: clear PRE2 POST2 BDC2; cbn [app] in FR2.
  - clear HB8.
    hold TRANS. hold CONT. hold IEXIT. hold RG0. hold AL1. hold AL2. hold AL3. hold AL4.
    kx_autoLx [0x1db98] 40%nat [KZRange SPV 592 (2^47); KZRange DCTX 4096 (2^47); KZRange LLT 4096 (2^47); KZRange (zlen sq) 1 (2^47)] [].
    all: kx_mem.
    all: unfold held in TRANS, CONT.
    all: eapply (CONT _ c0 c8 c16 c24 c40 c72 c104 c128 cont u176 u184 u192 u200 u208 u216 p0 p1 p2 pad jseq bc (bitd_ptr SEQ (zlen sq)));
      [ first [ eapply TRANS; [exact MUW | exact WMc | exact KXMI | exact FR2] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUW | exact WMc | exact KXMI | exact FR2] | repeat f_equal; lia] ]
      | unfold seqs_ibits; cbn [v_SEQ v_sq]; split; [lia | unfold bit_ok, bitd_ptr; intros _; destruct (Z.leb_spec 8 (zlen sq)); cbv beta iota; [right; lia | left; reflexivity]] ].
  - hold TRANS. hold CONT. hold IEXIT. hold RG0. hold AL1. hold AL2. hold AL3. hold AL4.
    kx_autoLx [0x1c6fc] 12%nat [KZRange SPV 592 (2^47); KZRange r (2^64 - 119) (2^64 - 1)] [].
    all: kx_mem.
    all: unfold held in TRANS, IEXIT, RG0.
    all: eapply IEXIT;
      [ exact RG0
      | first [ eapply TRANS; [exact MUW | exact WMc | exact KXMI | exact FR2] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUW | exact WMc | exact KXMI | exact FR2] | repeat f_equal; lia] ]
      | reflexivity | reflexivity | lia | left; reflexivity ].
Qed.
