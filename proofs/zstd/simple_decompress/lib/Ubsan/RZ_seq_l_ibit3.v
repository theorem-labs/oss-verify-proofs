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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase RZ_seq_l_ibit RZ_seq_l_ibit2 RZ_huf_iface seqD_kit_bitinit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_bitinit : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> seql_ranges P -> ai_i1 P OEND LLO LEND LOCV -> ai_i0 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST RG0 CONT.
  destruct (Z_le_gt_dec 8 (zlen (y_sq P))) as [H8|H8]; [exact (seql_bitinit_a P OEND LLO LEND LOCV ST RG0 (or_introl H8) CONT)|].
  destruct (Z_le_gt_dec (zlen (y_sq P)) 3) as [H3|H3]; [exact (seql_bitinit_a P OEND LLO LEND LOCV ST RG0 (or_intror H3) CONT)|].
  apply (seql_bitinit_b P OEND LLO LEND LOCV ST RG0); [lia | exact CONT].
Qed.

Lemma seql_ibit_xmove : forall P m1 fe loc, seql_ranges P -> seql_sep P -> seql_xinv P m1 fe -> h5_viewed m1 (y_DCTX P) (y_ws P) loc ->
  forall m2, munch [(y_SPV P - 688, y_SPV P)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  seql_xinv P m2 fe /\ h5_viewed m2 (y_DCTX P) (y_ws P) loc.
Proof.
  intros P m1 fe loc RG SEP XI (H5V & H5L) m2 MUL WML MI2.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe0 ws].
  cbn [seql_ranges seql_sep seql_xinv y_SPV y_DCTX y_ws] in RG, SEP, XI, H5V, MUL |- *.
  unfold off_stack, apart in SEP.
  unfold h5_viewed, dctx_h3, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  split; [| split; [eapply rw_cells_transport; [exact H5V | exact MUL | exact WML | unfold h5_vcells; cbn [disjoint_from cells_size csize Nat.add]; split; [clear - P1 G1 G14; lia | exact I]] | exact H5L]].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - P1 G1 G14; lia | exact I]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - P1 G1 G14; lia | exact I]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - P2 G14; lia | exact I]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - G14; lia | exact I]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

Lemma seql_bitinit0 : forall P OEND LLO LEND LOCV, seql_ranges P -> seql_sep P -> y_SPV P mod 16 = 0 -> zlen (y_sq P) = 0 -> ai_i0 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV RG0 SEP SP16 N0. unfold ai_i0.
  intros m1 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 u288 u296 u304 u312 u320 u328 p0 p1 p2 jbd jring jseq x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV.
  pose proof (seql_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  destruct INV as (FR & _ & _ & _ & _ & SQB & _ & _ & H5V & XI).
  pose proof (seql_ibit_xmove P m1 _ _ RG0 SEP XI H5V) as XMV. clear XI H5V.
  pose proof (seql_p_exit P) as PEXIT.
  pose proof RG0 as RG. pose proof SEP as SP.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbv beta iota zeta delta [seql_ifr seql_saved y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in FR.
  cbn [seql_ranges seql_sep y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in RG, SP, SQB, SP16, N0 |- *.
  unfold off_stack in SP.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct SP as (_ & _ & P3 & _).
  hold RG0. hold SEP. hold XMV. hold PEXIT.
  assert (MI8 : (SPV + -440) mod 8 = 0) by (clear - SP16; lia).
  assert (DJS : SPV + -440 + 40 <= SEQ \/ SEQ + zlen sq <= SPV + -440) by (clear - P3 G14 N0; lia).
  clear G1 G2 G5 G6 G7 G8 G9 G10 G11 G12 G13 P3.
  pose proof (seql_ibit_split _ _ _ _ _ 248 (SPV + -440) FR eq_refl ltac:(lia)) as (FRA & FRB & FRC).
  clear FR.
  eapply evt_cut.
  { eapply (seqd_bit_init_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -440) SEQ (zlen sq) (map (Z_to_bv 8) sq) jbd);
      [ exact MI | exact FRB | exact MI8 | exact SQB | rewrite length_map; reflexivity
      | clear - G14 G16; lia | clear - G15; lia | exact G3 | exact G4 | exact DJS ]. }
  clear MI8 DJS G3 G4.
  intros ms2 POST. unfold bit_init_post in POST.
  destruct POST as (b_t0 & b_t1 & b_t2 & b_a1 & b_a2 & b_a3 & b_a4 & b_a5 & b_a6 & b_a7 & b_t3 & b_t4 & b_t5 & b_t6 & m2 & r & -> & MU2 & WM2 & MI2 & RES).
  rewrite ret_pc_even by (first [reflexivity | lia]).
  destruct RES as [(RN & N1 & _) | (RERR & RLT & bs & FBD)]; [exfalso; clear - N1 N0; lia|].
  assert (RR : 2^64 - 119 <= r <= 2^64 - 1) by (unfold zd_is_error, ZE_maxCode in RERR; apply Z.ltb_lt in RERR; lia).
  clear RERR RLT.
  eapply rw_cells_transport in FRA; [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I]].
  eapply rw_cells_transport in FRC; [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I]].
  assert (MUL2 : munch [(SPV - 688, SPV)] m1 m2) by (eapply munch_weaken; [|exact MU2]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia).
  unfold held in XMV. destruct (XMV m2 MUL2 WM2 MI2) as (XI2 & H52). clear XMV.
  pose proof (seql_ibit_join _ _ _ _ _ _ 248 (SPV + -440) FRA FBD FRC eq_refl eq_refl ltac:(lia)) as FRE.
  cbn [app] in FRE.
  clear FRA FRB FRC FBD MU2 MUL2 WM2 MI SQB.
  hold XI2. hold H52.
  kx_autoLx [0x1db98; 0x1abb4] 20%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange r (2^64 - 119) (2^64 - 1); KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
  all: kx_mem.
  all: (try unfold held in PEXIT; try unfold held in RG0; try unfold held in XI2; try unfold held in H52).
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) =>
        apply (RZ_seq_kit.rw_cells_forget _ _ _ 44%nat 584%nat) in FRE; [|reflexivity];
        cbn [skipn] in FRE;
        eapply PEXIT; [exact RG0 | exact XI2 | exact H52 | exact FRE | lia | left; reflexivity]
    end.
Qed.
