(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk Frame Exec.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll KXUb KXUb2.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_huf_iface huf411_kit_rs seqD_kit_bitinit RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_ibase RZ_seq_d_ient.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqd_iinv_eq2 : forall P LEND m1 fr fr', seqd_iinv P LEND m1 fr -> fr = fr' -> seqd_iinv P LEND m1 fr'.
Proof. intros P LEND m1 fr fr' H E. subst fr'. exact H. Qed.

Lemma zbv_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2^64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma seqd_bitinit : forall P OEND LEND, seqd_static P OEND LEND -> seqd_ranges P -> ai_408 P OEND LEND -> ai_1ac P OEND LEND.
Proof.
  intros P OEND LEND ST RG0 CONT. unfold ai_1ac.
  intros m1 c0 c8 c16 c48 c72 c80 c88 u144 u152 u160 u168 u176 u184 p0 p1 p2 jbd jseq x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 INV.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iexit P LEND) as IEXIT.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  unfold ai_408 in CONT.
  destruct INV as (FR0 & _ & _ & _ & _ & SQB & _).
  pose proof (fun m' bd' => seqd_ifr_join m1 m' P OEND LEND c0 c8 c16 c48 c72 c80 c88 [CB 40 jbd] [C8 u144; C8 u152; C8 u160; C8 u168; C8 u176; C8 u184] bd' [C8 u144; C8 u152; C8 u160; C8 u168; C8 u176; C8 u184] p0 p1 p2 jseq FR0 eq_refl eq_refl) as JOIN.
  pose proof FR0 as FR. unfold seqd_ifr in FR.
  apply rw_cells_app in FR as (_ & FR). apply rw_cells_app in FR as (FBD & FR). apply rw_cells_app in FR as (FST & _).
  change (Z.of_nat (cells_size (seqd_ifr_hd P OEND LEND c0 c8 c16 c48 c72 c80 c88))) with 104 in FBD, FST.
  change (Z.of_nat (cells_size [CB 40 jbd])) with 40 in FST.
  clear FR0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST.
  replace (SPV + -352 + 104) with (SPV + -248) in FBD by lia.
  replace (SPV + -352 + 104 + 40) with (SPV + -208) in FST by lia.
  pose proof (rsk_al_e _ _ ALSP) as AL16.
  assert (BDA : (SPV + -248) mod 8 = 0) by (clear - AL16; Z.div_mod_to_equations; lia).
  assert (LSQ : zlen (map (Z_to_bv 8) sq) = zlen sq) by (unfold zlen; rewrite length_map; reflexivity).
  eapply evt_cut.
  { eapply (seqd_bit_init_proof (Z_to_bv 64 0x1cb84) (Z_to_bv 64 (SPV + -352)) gp tp x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 (Z_to_bv 64 nbSeq) x19 (Z_to_bv 64 DCTX) x21 x22 (Z_to_bv 64 PFX) x24 x25 x26 x27 x28 x29 x30 x31 F fc m1 (SPV + -248) SEQ (zlen sq) (map (Z_to_bv 8) sq) jbd);
      [ exact MI | exact FBD | exact BDA | exact SQB | exact LSQ | clear - S18; lia | clear - S17; lia | clear - S13; lia | clear - S14; lia
      | clear - S25 S18; unfold held in S25; lia ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & r & -> & MUc & WMc & MIc & RES).
  replace (ret_pc (Z_to_bv 64 0x1cb84)) with (Z_to_bv 64 0x1cb84) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (MU1 : munch [(SPV - 352, SPV)] m1 m2) by (eapply munch_weaken; [|exact MUc]; unfold sub_fp; cbn [outside]; intros x (H1 & _); split; [clear - H1; lia | exact I]).
  assert (MU2 : munch [(SPV - 248, SPV - 160)] m1 m2) by (eapply munch_weaken; [|exact MUc]; unfold sub_fp; cbn [outside]; intros x (H1 & _); split; [clear - H1; lia | exact I]).
  assert (FST2 : rw_cells usegs m2 (SPV + -208) [C8 u144; C8 u152; C8 u160; C8 u168; C8 u176; C8 u184]).
  { eapply rw_cells_transport; [exact FST | exact MUc | exact WMc |]. cbn [disjoint_from cells_size csize Nat.add]. split; [lia | exact I]. }
  clear FST FBD MUc SQB MI.
  destruct RES as [(RN & N1 & cont & bc & pad & BC1 & BC8 & FBD2) | (RERR & RLT & bs & FBD2)].
  - subst r.
    pose proof (JOIN m2 _ MU2 WMc FBD2 FST2 eq_refl eq_refl) as FR2.
    pose proof (TRANS m2 _ MU1 WMc MIc FR2) as INV2.
    pose proof INV2 as (FR3 & PT2 & _).
    unfold seqd_ifr, seqd_ifr_hd, seqd_ifr_tl, bitd_cells, dctx_ptrs in FR3, PT2.
    cbn [app q_SPV q_DST q_DCTX q_dend q_PFX q_LITP q_SEQ q_s11 q_s10 q_s9 q_s8 q_s7 q_s6 q_s5 q_s4 q_s3 q_s2 q_s1 q_s0 q_ra q_LLT q_MLT q_OFT q_huf] in FR3, PT2.
    clear FR2 FBD2 FST2 MU1 MU2 JOIN.
    hold TRANS. hold CONT. hold IEXIT. hold RG0. hold INV2.
    kx_autoLx [0x1db98; 0x1d6e4] 40%nat
      [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZRange (zlen sq) 1 (2^47); KZWr (SPV - 352) 352]
      [(SPV - 352, 352)].
    all: unfold held in TRANS, CONT, IEXIT, RG0, INV2.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1db98) _ _ _ _) =>
          eapply CONT; [exact INV2 |];
          unfold seqd_ibits, bit_ok, bitd_ptr; cbn [q_SEQ q_sq]; split; [lia|];
          intros _; destruct (8 <=? zlen sq) eqn:E8; cbv iota; [apply Z.leb_le in E8; right; lia | left; reflexivity]
      end.
  - pose proof (JOIN m2 _ MU2 WMc FBD2 FST2 eq_refl eq_refl) as FR2.
    pose proof (TRANS m2 _ MU1 WMc MIc FR2) as INV2.
    pose proof INV2 as (FR3 & PT2 & _).
    unfold seqd_ifr, seqd_ifr_hd, seqd_ifr_tl, dctx_ptrs in FR3, PT2.
    cbn [app q_SPV q_DST q_DCTX q_dend q_PFX q_LITP q_SEQ q_s11 q_s10 q_s9 q_s8 q_s7 q_s6 q_s5 q_s4 q_s3 q_s2 q_s1 q_s0 q_ra q_LLT q_MLT q_OFT q_huf] in FR3, PT2.
    clear FR2 FBD2 FST2 MU1 MU2 JOIN.
    unfold zd_is_error, ZE_maxCode in RERR. apply Z.ltb_lt in RERR.
    hold TRANS. hold CONT. hold IEXIT. hold RG0. hold INV2.
    kx_autoLx [0x1db98; 0x1d6e4] 40%nat
      [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZWr (SPV - 352) 352]
      [(SPV - 352, 352)].
    all: unfold held in TRANS, CONT, IEXIT, RG0, INV2.
    all: lazymatch goal with
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _) _ (Z_to_bv 64 0x1d6e4) _ _ _ _) =>
          rewrite (zbv_mod v);
          eapply IEXIT; [exact RG0 | rewrite seqd_ifr_saved in INV2; exact INV2 | reflexivity | apply Z.mod_pos_bound; lia | left; reflexivity]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1db98) _ _ _ _) => exfalso; first [kx_trap_fast | lia]
      end.
Qed.
