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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase RZ_seq_l_iexit RZ_huf_iface seqD_kit_bitinit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma zbv_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2^64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma seql_ibit_split : forall m A pre mid post k B,
  rw_cells usegs m A (pre ++ mid ++ post) -> Z.of_nat (cells_size pre) = k -> A + k = B ->
  rw_cells usegs m A pre /\ rw_cells usegs m B mid /\ rw_cells usegs m (B + Z.of_nat (cells_size mid)) post.
Proof.
  intros m A pre mid post k B H E1 E2. subst k B.
  apply rw_cells_app in H. destruct H as (H1 & H2). apply rw_cells_app in H2. destruct H2 as (H2 & H3).
  split; [exact H1|]. split; [exact H2|exact H3].
Qed.

Lemma seql_ibit_join : forall m A pre mid mid' post k B,
  rw_cells usegs m A pre -> rw_cells usegs m B mid' -> rw_cells usegs m (B + Z.of_nat (cells_size mid)) post ->
  cells_size mid' = cells_size mid -> Z.of_nat (cells_size pre) = k -> A + k = B ->
  rw_cells usegs m A (pre ++ mid' ++ post).
Proof.
  intros m A pre mid mid' post k B H1 H2 H3 S E1 E2. subst k B.
  apply rw_cells_app. split; [exact H1|]. apply rw_cells_app. split; [exact H2|]. rewrite S. exact H3.
Qed.

Lemma seql_bitinit_u : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> seql_ranges P -> ai_i1 P OEND LLO LEND LOCV -> ai_i0 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST RG0 CONT. unfold ai_i0.
  intros m1 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 u288 u296 u304 u312 u320 u328 p0 p1 p2 jbd jring jseq x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV.
  pose proof (seql_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seql_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  pose proof ST as ST0.
  unfold ai_i1 in CONT.
  destruct INV as (FR & _ & _ & _ & _ & SQB & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbv beta iota zeta delta [seql_ifr seql_saved y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in FR.
  cbn [seql_static y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST |- *.
  cbn [y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in SQB, CONT, TRANS.
  sd_static_open ST.
  assert (MI8 : (SPV + -440) mod 8 = 0) by (clear - AL4; lia).
  assert (DJS : SPV + -440 + 40 <= SEQ \/ SEQ + zlen sq <= SPV + -440) by (unfold held in S25; clear - S25 S18; lia).
  assert (DJD : SPV - 688 + 688 <= DCTX \/ DCTX + 32 <= SPV - 688) by (unfold held in S27; clear - S27 S18; lia).
  try hold S8. try hold S9. try hold S10. try hold S11. try hold S16. try hold S21. try hold S22. try hold S23. try hold S41.
  try hold OKLL. try hold OKOF. try hold OKML. try hold AL1. try hold AL2. try hold AL3.
  pose proof (seql_ibit_split _ _ _ _ _ 248 (SPV + -440) FR eq_refl ltac:(lia)) as (FRA & FRB & FRC).
  clear FR.
  eapply evt_cut.
  { eapply (seqd_bit_init_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -440) SEQ (zlen sq) (map (Z_to_bv 8) sq) jbd);
      [ exact MI | exact FRB | exact MI8 | exact SQB | rewrite length_map; reflexivity
      | clear - S18; lia | clear - S17; lia | exact S13 | exact S14 | exact DJS ]. }
  clear MI8 DJS.
  intros ms2 POST. unfold bit_init_post in POST.
  destruct POST as (b_t0 & b_t1 & b_t2 & b_a1 & b_a2 & b_a3 & b_a4 & b_a5 & b_a6 & b_a7 & b_t3 & b_t4 & b_t5 & b_t6 & m2 & r & -> & MU2 & WM2 & MI2 & RES).
  rewrite ret_pc_even by (first [reflexivity | lia]).
  eapply rw_cells_transport in FRA; [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I]].
  eapply rw_cells_transport in FRC; [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I]].
  assert (MUL2 : munch [(SPV - 688, SPV)] m1 m2) by (eapply munch_weaken; [|exact MU2]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia).
  destruct RES as [(RN & N1 & cont & bc & pad & BC1 & BC8 & FBD) | (RERR & RLT & bs & FBD)].
  - subst r. clear N1 BC8.
    unfold bitd_cells in FBD.
    assert (HPB : bit_ok SEQ (zlen sq) bc (bitd_ptr SEQ (zlen sq))).
    { unfold bit_ok, bitd_ptr. intros _. destruct (Z.leb_spec 8 (zlen sq)) as [L8|L8]; [right; lia | left; reflexivity]. }
    revert FBD HPB. generalize (bitd_ptr SEQ (zlen sq)) as ptr. intros ptr FBD HPB.
    pose proof (seql_ibit_join _ _ _ _ _ _ 248 (SPV + -440) FRA FBD FRC eq_refl eq_refl ltac:(lia)) as FR2.
    pose proof (TRANS m2 _ MUL2 WM2 MI2 FR2) as INV2.
    pose proof (seql_iinv_frame _ OEND LLO LEND LOCV m2 _ ST0 INV2) as TRANS2.
    destruct INV2 as (_ & PT & _).
    unfold dctx_ptrs in PT. cbn [y_DCTX y_LLT y_MLT y_OFT y_huf] in PT. cbn [y_SPV] in TRANS2.
    cbn [app] in FR2.
    clear TRANS FRA FRB FRC FBD MU2 MUL2 WM2 MI SQB.
    remember (zlen sq) as n eqn:En.
    assert (MUL : munch [(SPV - 688, SPV)] m2 m2) by apply munch_refl. assert (WMl : wmono usegs m2 m2) by apply wmono_refl.
    hold TRANS2. hold CONT. hold RG0. hold ST0. hold HPB.
    kx_autoLx [0x1db98; 0x1abb4] 40%nat
      [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange DCTX 4096 (2^47); KZRange n 1 (2^47);
       KZWr (SPV - 688) 688; KZDisj (SPV - 688) 688 DCTX 32]
      [(SPV - 688, 688)].
    all: kx_mem.
    all: (try unfold held in TRANS2; try unfold held in CONT; try unfold held in HPB).
    all: lazymatch goal with
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?r19 _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1db98) _ _ _ _) =>
          replace r19 with (Z_to_bv 64 (DST - PFX)) by (f_equal; lia);
          eapply (CONT _ c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cont u288 u296 u304 u312 u320 u328 p0 p1 p2 pad jring jseq bc ptr);
          [ eapply TRANS2; [exact MUL | exact WMl | exact KXMI | exact FR2]
          | unfold seql_ibits; cbn [y_SEQ y_sq]; split; [lia | rewrite <- En; exact HPB]
          | cbn [y_sq]; lia ]
      end.
  - assert (RR : 2^64 - 119 <= r <= 2^64 - 1) by (unfold zd_is_error, ZE_maxCode in RERR; apply Z.ltb_lt in RERR; lia).
    clear RERR RLT.
    pose proof (seql_ibit_join _ _ _ _ _ _ 248 (SPV + -440) FRA FBD FRC eq_refl eq_refl ltac:(lia)) as FRE.
    pose proof (TRANS m2 _ MUL2 WM2 MI2 FRE) as INV2.
    pose proof (seql_iinv_frame _ OEND LLO LEND LOCV m2 _ ST0 INV2) as TRANS2.
    clear INV2. cbn [y_SPV] in TRANS2.
    cbn [app] in FRE.
    clear TRANS FRA FRB FRC FBD MU2 MUL2 WM2 MI SQB.
    assert (MUL : munch [(SPV - 688, SPV)] m2 m2) by apply munch_refl. assert (WMl : wmono usegs m2 m2) by apply wmono_refl.
    hold TRANS2. hold CONT. hold RG0. hold ST0.
    kx_autoLx [0x1db98; 0x1abb4] 20%nat
      [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange r (2^64 - 119) (2^64 - 1); KZWr (SPV - 688) 688]
      [(SPV - 688, 688)].
    all: kx_mem.
    all: (try unfold held in TRANS2; try unfold held in RG0).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) =>
          eapply (seql_iexit_ifr (mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) OEND LLO LEND LOCV _ c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 [CB 40 bs] [C8 u288; C8 u296; C8 u304; C8 u312; C8 u320; C8 u328] p0 p1 p2 jring jseq);
          [ exact RG0 | eapply TRANS2; [exact MUL | exact WMl | first [exact KXMI | exact MI2] | exact FRE] | reflexivity | lia | left; reflexivity ]
      end.
Qed.

Lemma seql_bitinit_a : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> seql_ranges P -> (8 <= zlen (y_sq P) \/ zlen (y_sq P) <= 3) -> ai_i1 P OEND LLO LEND LOCV -> ai_i0 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST RG0 _ CONT. exact (seql_bitinit_u P OEND LLO LEND LOCV ST RG0 CONT).
Qed.
