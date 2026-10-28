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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_linv_step : forall P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  seql_static P OEND LLO LEND LOCV -> seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  forall m2 c0' c8' c16' c24' c40' c48' c64' c72' c104' c128' c152' c168' c176' c184' c216' c224' c232' c240' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq D1 D2,
  munch [(D1, D2); (y_SPV P - 688, y_SPV P)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  stk usegs m2 (y_B0 P) (y_B1 P) -> y_DST P <= D1 -> D2 <= OEND ->
  rw_cells usegs m2 (y_SPV P + -688) (seql_frame P OEND c0' c8' c16' c24' c40' c48' c64' c72' c104' c128' c152' c168' c176' c184' c216' c224' c232' c240' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq) ->
  seql_linv P OEND LLO LEND LOCV m2 c0' c8' c16' c24' c40' c48' c64' c72' c104' c128' c152' c168' c176' c184' c216' c224' c232' c240' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP'.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV m2 c0' c8' c16' c24' c40' c48' c64' c72' c104' c128' c152' c168' c176' c184' c216' c224' c232' c240' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq D1 D2 MUL WML MI2 BUF2 HD1 HD2 FR.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exists jpad, jseq; exact FR|]. clear FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_xinv y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  sd_static_open ST. unfold held in S18, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S33 S1 S2 S3 S4 S5 S6 HD1 HD2 LLL; lia| split; [clear - S28 S18 LLL; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S34 S1 S2 S3 S4 S5 S6 HD1 HD2 LOF; lia| split; [clear - S29 S18 LOF; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S35 S1 S2 S3 S4 S5 S6 HD1 HD2 LML; lia| split; [clear - S30 S18 LML; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S31 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S25 S18; lia| exact I]]]|].
  split; [unfold held in S12; destruct S12 as [(A1 & A2)|A]; [eapply rdbl_sub; [eapply rdbl_of_stk; exact BUF2 | exact A1 | exact A2] | eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - A S1 S2 S3 S4 S5 S6 HD1 HD2 Hx; lia| split; [clear - S26 S18 Hx; lia| exact I]]]]|].
  split; [intros HL2; eapply rdbl_transport; [exact (XLIT HL2) | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2 Hx; lia| split; [clear - S27 S18 Hx; lia| exact I]]]|].
  split; [split; [eapply rw_cells_transport; [exact H5V | exact MUL | exact WML | unfold h5_vcells; cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18; lia| exact I]]] | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18; lia| exact I]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18; lia| exact I]]]|].
  split; [exact BUF2|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S24 S18 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S18; lia|exact I]]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx HD1 HD2 S5; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

Lemma seql_linv_buf : forall P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  seql_static P OEND LLO LEND LOCV -> seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  forall m2 D1 D2,
  munch [(D1, D2)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  stk usegs m2 (y_B0 P) (y_B1 P) -> y_DST P <= D1 -> D2 <= OEND ->
  seql_linv P OEND LLO LEND LOCV m2 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV m2 D1 D2 MUL WML MI2 BUF2 HD1 HD2.
  pose proof INV as ((jpad & jseq & FR) & _).
  eapply (seql_linv_step P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV m2 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq D1 D2); try assumption.
  - eapply munch_weaken; [|exact MUL]. unfold sub_fp; cbn [outside]. intros x Hx. tauto.
  - eapply rw_cells_transport; [exact FR | exact MUL | exact WML |].
    clear - ST HD1 HD2. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seql_static seql_frame y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *. sd_static_open ST. unfold held in S24.
    cbn [disjoint_from cells_size csize Nat.add]. split; [|exact I]. clear - S24 S18 S1 S2 S3 S4 S5 S6 HD1 HD2. lia.
Qed.

(* [comment removed for export] *)
Definition seql_copy_post (P : slp) (OEND LLO LEND LOCV : Z) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (D : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ seql_linv P OEND LLO LEND LOCV m' c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP.

Lemma seql_copy_facts : forall P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  seql_static P OEND LLO LEND LOCV -> seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  stk usegs m1 (y_B0 P) (y_B1 P) /\ rdbl usegs m1 LLO (LEND + 32) /\
  4096 <= y_B0 P /\ y_B0 P <= y_DST P /\ OEND <= y_B1 P /\ y_B1 P < 2^47 /\ 4096 <= LLO /\ LEND + 32 < 2^47.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV.
  destruct INV as (_ & _ & _ & _ & _ & LIT & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seql_static seql_xinv y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *. sd_static_open ST.
  destruct XI as (_ & _ & BUF & _). repeat (split; [first [assumption | lia]|]). lia.
Qed.

Lemma seql_copy_spec : forall P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP (D S n : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  seql_static P OEND LLO LEND LOCV -> seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  y_DST P <= D -> 0 <= n -> D + n <= OEND ->
  ((LLO <= S /\ S + n <= LEND + 32) \/ (y_B0 P <= S /\ S + n <= y_B1 P)) ->
  evt usegs (seql_copy_post P OEND LLO LEND LOCV c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35670) fc None m1 (seg_rom usegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP D S n ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ST INV HD Hn HDn SRC.
  pose proof (seql_linv_buf P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as STEP.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (seql_copy_facts P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as FACTS.
  destruct FACTS as (BUF & LIT & F1 & F2 & F3 & F4 & F5 & F6).
  destruct SRC as [(SL1 & SL2)|(SB1 & SB2)].
  - eapply evt_mono.
    + eapply (memmove_reg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 D S n (y_B0 P) (y_B1 P) LLO (LEND + 32) BUF LIT);
        [ lia | exact MI | reflexivity | reflexivity | reflexivity ].
    + intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & BUF' & _).
      do 15 eexists. split; [reflexivity|]. eapply STEP; [exact MU | exact WM | exact MI' | exact BUF' | exact HD | exact HDn].
  - eapply evt_mono.
    + eapply (memmove_reg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 D S n (y_B0 P) (y_B1 P) (y_B0 P) (y_B1 P) BUF (rdbl_of_stk usegs m1 _ _ BUF));
        [ lia | exact MI | reflexivity | reflexivity | reflexivity ].
    + intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & BUF' & _).
      do 15 eexists. split; [reflexivity|]. eapply STEP; [exact MU | exact WM | exact MI' | exact BUF' | exact HD | exact HDn].
Qed.
