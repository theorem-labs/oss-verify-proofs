(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk Frame Exec.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_huf_iface huf411_kit_rs seqD_kit_bitinit RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_ibase RZ_seq_d_ient.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sde_zbv_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2^64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma seqd_iinv_move : forall P LEND m1 fr,
  seqd_ranges P -> seqd_sep P -> seqd_tables P -> LEND = q_LITP P + q_LITSZ P -> seqd_iinv P LEND m1 fr ->
  forall m2 fr2,
  munch [(q_SPV P - 352, q_SPV P)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  rw_cells usegs m2 (q_SPV P + -352) fr2 -> seqd_iinv P LEND m2 fr2.
Proof.
  intros P LEND m1 fr RG SEP TBL EL INV m2 fr2 MUL WML MI2 FR.
  destruct INV as (_ & PT & TLL & TOF & TML & SQB & LIT & XI).
  split; [exact FR|]. clear FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_ranges seqd_sep seqd_tables seqd_xinv q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  destruct TBL as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & _ & _ & _ & T7 & T8 & T9 & _).
  destruct SEP as (P1 & P2 & P3 & P4 & _).
  unfold off_stack, DCTX_SIZEOF, WILDCOPY_OVERLENGTH in *. subst LEND.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_ptrs, dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy in *.
  split; [eapply rw_cells_transport; [exact PT | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - P1 RG; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - T7 RG LLL; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - T8 RG LOF; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - T9 RG LML; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - P3 RG; unfold zlen in *; lia|exact I]]|].
  split; [eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - P4 RG Hx; lia|exact I]]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - P1 RG; lia|exact I]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - P1 RG; lia|exact I]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - P2 RG; lia|exact I]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - RG; lia|exact I]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

Lemma seqd_ai1ac_z0 : forall P OEND LEND,
  seqd_ranges P -> seqd_sep P -> seqd_tables P -> zlen (q_sq P) = 0 -> q_SPV P mod 16 = 0 -> LEND = q_LITP P + q_LITSZ P ->
  ai_1ac P OEND LEND.
Proof.
  intros P OEND LEND RG0 SEP0 TBL0 Z0 AL16 EL. unfold ai_1ac.
  intros m1 c0 c8 c16 c48 c72 c80 c88 u144 u152 u160 u168 u176 u184 p0 p1 p2 jbd jseq x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 INV.
  pose proof (seqd_iinv_move P LEND m1 _ RG0 SEP0 TBL0 EL INV) as TRANS.
  pose proof (seqd_iexit P LEND) as IEXIT.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  destruct INV as (FR0 & _ & _ & _ & _ & SQB & _).
  pose proof (fun m' bd' => seqd_ifr_join m1 m' P OEND LEND c0 c8 c16 c48 c72 c80 c88 [CB 40 jbd] [C8 u144; C8 u152; C8 u160; C8 u168; C8 u176; C8 u184] bd' [C8 u144; C8 u152; C8 u160; C8 u168; C8 u176; C8 u184] p0 p1 p2 jseq FR0 eq_refl eq_refl) as JOIN.
  pose proof FR0 as FR. unfold seqd_ifr in FR.
  apply rw_cells_app in FR as (_ & FR). apply rw_cells_app in FR as (FBD & FR). apply rw_cells_app in FR as (FST & _).
  change (Z.of_nat (cells_size (seqd_ifr_hd P OEND LEND c0 c8 c16 c48 c72 c80 c88))) with 104 in FBD, FST.
  change (Z.of_nat (cells_size [CB 40 jbd])) with 40 in FST.
  clear FR0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_ranges seqd_sep seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in RG0, SEP0, Z0, AL16, EL, FBD, FST, SQB |- *.
  replace (SPV + -352 + 104) with (SPV + -248) in FBD by lia.
  replace (SPV + -352 + 104 + 40) with (SPV + -208) in FST by lia.
  assert (BDA : (SPV + -248) mod 8 = 0) by (clear - AL16; Z.div_mod_to_equations; lia).
  assert (LSQ : zlen (map (Z_to_bv 8) sq) = zlen sq) by (unfold zlen; rewrite length_map; reflexivity).
  assert (RS : 4096 <= SPV + -248 /\ SPV + -248 + 40 < 2^47 /\ 4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ (SPV + -248 + 40 <= SEQ \/ SEQ + zlen sq <= SPV + -248) /\ 544 <= SPV < 2^47).
  { clear - RG0 SEP0 Z0. unfold off_stack, DCTX_SIZEOF, WILDCOPY_OVERLENGTH in *. destruct SEP0 as (_ & _ & P3 & _). lia. }
  assert (RD : 4096 <= DCTX < 2^47) by (clear - RG0; unfold DCTX_SIZEOF in RG0; lia).
  eapply evt_cut.
  { eapply (seqd_bit_init_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SPV + -248) SEQ (zlen sq) (map (Z_to_bv 8) sq) jbd);
      [ exact MI | exact FBD | exact BDA | exact SQB | exact LSQ | clear - RS; lia | clear - RS; lia | clear - RS; lia | clear - RS; lia | clear - RS; lia ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & r & -> & MUc & WMc & MIc & RES).
  replace (ret_pc (Z_to_bv 64 0x1cb84)) with (Z_to_bv 64 0x1cb84) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (MU1 : munch [(SPV - 352, SPV)] m1 m2) by (eapply munch_weaken; [|exact MUc]; unfold sub_fp; cbn [outside]; intros x (H1 & _); split; [clear - H1; lia | exact I]).
  assert (MU2 : munch [(SPV - 248, SPV - 160)] m1 m2) by (eapply munch_weaken; [|exact MUc]; unfold sub_fp; cbn [outside]; intros x (H1 & _); split; [clear - H1; lia | exact I]).
  assert (FST2 : rw_cells usegs m2 (SPV + -208) [C8 u144; C8 u152; C8 u160; C8 u168; C8 u176; C8 u184]).
  { eapply rw_cells_transport; [exact FST | exact MUc | exact WMc |]. cbn [disjoint_from cells_size csize Nat.add]. split; [lia | exact I]. }
  clear FST FBD MUc SQB MI.
  destruct RES as [(RN & N1 & _) | (RERR & RLT & bs & FBD2)]; [exfalso; clear - N1 Z0; lia|].
  pose proof (JOIN m2 _ MU2 WMc FBD2 FST2 eq_refl eq_refl) as FR2.
  pose proof (TRANS m2 _ MU1 WMc MIc FR2) as INV2.
  pose proof INV2 as (FR3 & PT2 & _).
  unfold seqd_ifr, seqd_ifr_hd, seqd_ifr_tl, dctx_ptrs in FR3, PT2.
  cbn [app q_SPV q_DST q_DCTX q_dend q_PFX q_LITP q_SEQ q_s11 q_s10 q_s9 q_s8 q_s7 q_s6 q_s5 q_s4 q_s3 q_s2 q_s1 q_s0 q_ra q_LLT q_MLT q_OFT q_huf] in FR3, PT2.
  clear FR2 FBD2 FST2 MU1 MU2 JOIN.
  unfold zd_is_error, ZE_maxCode in RERR. apply Z.ltb_lt in RERR.
  clear TRANS SEP0 TBL0. hold IEXIT. hold RG0. hold INV2.
  kx_autoLx [0x1db98; 0x1d6e4] 40%nat
    [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZWr (SPV - 352) 352]
    [(SPV - 352, 352)].
  all: unfold held in IEXIT, RG0, INV2.
  all: lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _) _ (Z_to_bv 64 0x1d6e4) _ _ _ _) =>
        rewrite (sde_zbv_mod v);
        eapply IEXIT; [exact RG0 | rewrite seqd_ifr_saved in INV2; exact INV2 | reflexivity | apply Z.mod_pos_bound; lia | left; reflexivity]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1db98) _ _ _ _) => exfalso; first [kx_trap_fast | lia]
    end.
Qed.
