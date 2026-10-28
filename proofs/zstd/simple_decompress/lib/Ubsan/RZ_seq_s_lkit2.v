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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqs_linv_step : forall P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqs_static P OEND LLO LEND LOCV -> seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq D1 D2,
  munch [(D1, D2); (v_SPV P - 384, v_SPV P)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  stk usegs m2 (v_B0 P) (v_B1 P) -> v_DST P <= D1 -> D2 <= OEND ->
  rw_cells usegs m2 (v_SPV P + -384) (seqs_frame P OEND c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq) ->
  seqs_linv P OEND LLO LEND LOCV m2 c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP'.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq D1 D2 MUL WML MI2 BUF2 HD1 HD2 FR.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exists jpad, jseq; exact FR|]. clear FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_xinv v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST. unfold held in S18, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S33 S1 S2 S3 S4 S5 S6 HD1 HD2 LLL; lia| split; [clear - S28 S18 LLL; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S34 S1 S2 S3 S4 S5 S6 HD1 HD2 LOF; lia| split; [clear - S29 S18 LOF; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S35 S1 S2 S3 S4 S5 S6 HD1 HD2 LML; lia| split; [clear - S30 S18 LML; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S31 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S25 S18; lia| exact I]]]|].
  split; [unfold held in S12; destruct S12 as [(A1 & A2)|A]; [eapply rdbl_sub; [eapply rdbl_of_stk; exact BUF2 | exact A1 | exact A2] | eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - A S1 S2 S3 S4 S5 S6 HD1 HD2 Hx; lia| split; [clear - S26 S18 Hx; lia| exact I]]]]|].
  split; [eapply rdbl_transport; [exact XLIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2 Hx; lia| split; [clear - S27 S18 Hx; lia| exact I]]]|].
  split; [split; [eapply rw_cells_transport; [exact H5V | exact MUL | exact WML | unfold h5_vcells; cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18; lia| exact I]]] | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18; lia| exact I]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18; lia| exact I]]]|].
  split; [exact BUF2|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S24 S18 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S18; lia|exact I]]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx HD1 HD2 S5; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

Lemma seqs_linv_buf : forall P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqs_static P OEND LLO LEND LOCV -> seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 D1 D2,
  munch [(D1, D2)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  stk usegs m2 (v_B0 P) (v_B1 P) -> v_DST P <= D1 -> D2 <= OEND ->
  seqs_linv P OEND LLO LEND LOCV m2 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 D1 D2 MUL WML MI2 BUF2 HD1 HD2.
  pose proof INV as ((jpad & jseq & FR) & _).
  eapply (seqs_linv_step P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq D1 D2); try assumption.
  - eapply munch_weaken; [|exact MUL]. unfold sub_fp; cbn [outside]. intros x Hx. tauto.
  - eapply rw_cells_transport; [exact FR | exact MUL | exact WML |].
    clear - ST HD1 HD2. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqs_static seqs_frame v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *. sd_static_open ST. unfold held in S24.
    cbn [disjoint_from cells_size csize Nat.add]. split; [|exact I]. clear - S24 S18 S1 S2 S3 S4 S5 S6 HD1 HD2. lia.
Qed.

(* [comment removed for export] *)
Definition seqs_copy_post (P : ssp) (OEND LLO LEND LOCV : Z) (c0 c8 c40 lec c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (D : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ seqs_linv P OEND LLO LEND LOCV m' c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP.

Lemma seqs_copy_facts : forall P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqs_static P OEND LLO LEND LOCV -> seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  stk usegs m1 (v_B0 P) (v_B1 P) /\ rdbl usegs m1 LLO (LEND + 32) /\
  4096 <= v_B0 P /\ v_B0 P <= v_DST P /\ OEND <= v_B1 P /\ v_B1 P < 2^47 /\ 4096 <= LLO /\ LEND + 32 < 2^47.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV.
  destruct INV as (_ & _ & _ & _ & _ & LIT & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqs_static seqs_xinv v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *. sd_static_open ST.
  destruct XI as (_ & _ & BUF & _). repeat (split; [first [assumption | lia]|]). lia.
Qed.

Lemma seqs_copy_spec : forall P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP (D S n : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  seqs_static P OEND LLO LEND LOCV -> seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  v_DST P <= D -> 0 <= n -> D + n <= OEND ->
  ((LLO <= S /\ S + n <= LEND + 32) \/ (v_B0 P <= S /\ S + n <= v_B1 P)) ->
  evt usegs (seqs_copy_post P OEND LLO LEND LOCV c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35670) fc None m1 (seg_rom usegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP D S n ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ST INV HD Hn HDn SRC.
  pose proof (seqs_linv_buf P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as STEP.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (seqs_copy_facts P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as FACTS.
  destruct FACTS as (BUF & LIT & F1 & F2 & F3 & F4 & F5 & F6).
  destruct SRC as [(SL1 & SL2)|(SB1 & SB2)].
  - eapply evt_mono.
    + eapply (memmove_reg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 D S n (v_B0 P) (v_B1 P) LLO (LEND + 32) BUF LIT);
        [ lia | exact MI | reflexivity | reflexivity | reflexivity ].
    + intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & BUF' & _).
      do 15 eexists. split; [reflexivity|]. eapply STEP; [exact MU | exact WM | exact MI' | exact BUF' | exact HD | exact HDn].
  - eapply evt_mono.
    + eapply (memmove_reg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 D S n (v_B0 P) (v_B1 P) (v_B0 P) (v_B1 P) BUF (rdbl_of_stk usegs m1 _ _ BUF));
        [ lia | exact MI | reflexivity | reflexivity | reflexivity ].
    + intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & BUF' & _).
      do 15 eexists. split; [reflexivity|]. eapply STEP; [exact MU | exact WM | exact MI' | exact BUF' | exact HD | exact HDn].
Qed.
