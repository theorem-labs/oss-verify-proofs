(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_rkit AZ_seq_l_v_lt AZ_seq_l_xat AZ_seq_l_md_at AZ_seq_l_lm_at.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Local Ltac cells_split n H :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cl => rewrite <- (firstn_skipn n cl) in H; cbn [firstn skipn] in H end.
Local Ltac cells_split2 k H :=
  lazymatch type of H with rw_cells ?sg ?mm ?A (?pre ++ ?rest) => rewrite <- (firstn_skipn k rest) in H; cbn [firstn skipn] in H end.

(* [comment removed for export] *)
Lemma sql_lfacts_lp_op : forall P OEND LLO LEND B B' OP OP' LP bc ptr sLL sOF sML,
  sql_lfacts P OEND LLO LEND B OP LP bc ptr sLL sOF sML -> l_DST P <= OP' <= OEND -> B <= B' ->
  sql_lfacts P OEND LLO LEND B' OP' LP bc ptr sLL sOF sML.
Proof. intros until 0. intros (L1 & L2 & L3 & L4 & L5 & L6 & L7) HO HB. unfold sql_lfacts. repeat split; try assumption; try lia. Qed.

Lemma lm_latch_ok : forall P OEND LLO LEND LOCV K, sql_static P OEND LLO LEND LOCV -> 1 <= K <= l_nbSeq P ->
  (1 < K -> md_head P OEND LLO LEND LOCV (K - 1)) -> lm_done P OEND LLO LEND LOCV 1 -> lm_latch P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  unfold lm_latch. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c128 c232 c264 c320 c352 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP r sn cidx dll dml dof x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x20 x26 x27 x28 x29 x30 x31 INV LF HR0 HOP HSN HS8 HCI HDL HDM HDO HRING.
   cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in HK.
  pose proof ST as ST0.
  pose proof (sql_linv_frame _ _ _ _ _ m1 c8 c16 (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) (Z_to_bv 64 (DCTX + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (DCTX + 30372)) c128 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (nbSeq - 1)) c232 (Z_to_bv 64 cidx) c264 (Z_to_bv 64 LEND) (Z_to_bv 64 dof) c320 (Z_to_bv 64 sn) (Z_to_bv 64 139648) c352 (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as TRANS. cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in TRANS.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) (Z_to_bv 64 (DCTX + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (DCTX + 30372)) c128 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (nbSeq - 1)) c232 (Z_to_bv 64 cidx) c264 (Z_to_bv 64 LEND) (Z_to_bv 64 dof) c320 (Z_to_bv 64 sn) (Z_to_bv 64 139648) c352 (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  apply sql_fr_vlt in FR. cbv delta [sql_ffr] in FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  pose proof LF as LF0. apply (sql_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  sd_static_open ST. unfold held in RGB.
  assert (MUL : munch [(FRB, FRB + 568); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  clear SQB USEQ RSQ RSQS UFL INV.
  unfold md_head in CONT1. unfold lm_done in CONT2. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in CONT1, CONT2.
  replace (100 + 100 * (nbSeq - (K - 1)) + 0) with (100 + 100 * (nbSeq - K) + 100) in CONT1 by (clear; lia). rewrite <- (Z.add_assoc DCTX _ 4) in CONT1.
  assert (RG : 8 <= sn <= 98046 /\ 9 <= nbSeq <= 98047 /\ 4096 <= OP < 2^47 /\ 0 <= r < 2^47 /\ 4096 <= OP + r < 2^47 /\ 0 <= dll <= 262143 /\ 0 <= dml <= 262143 /\ 0 <= dof <= 2^64 - 1)
    by (clear - S1 S2 S3 S4 S5 S6 S7 S16 HK HSN HS8 L1 HR0 HOP HDL HDM HDO; lia).
  assert (CASES : cidx = 0 \/ cidx = 1 \/ cidx = 2 \/ cidx = 3 \/ cidx = 4 \/ cidx = 5 \/ cidx = 6 \/ cidx = 7) by (clear - HCI; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; subst cidx.
  - cells_split 19%nat FR; apply (sql_ring_open_0 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML;
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8ae50; 0x8cdac] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange sn 8 98046;
     KZRange nbSeq 9 98047;
     KZRange OP 4096 (2^47);
     KZRange r 0 (2^47);
     KZRange (OP + r) 4096 (2^47);
     KZRange dll 0 262143;
     KZRange dml 0 262143;
     KZRange dof 0 (2^64 - 1)]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ae50) _ _ _ _) => (cells_split 19%nat FR; cells_split2 4%nat FR; apply sql_ring_close_0 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 0 dll dml dof HRING HDL HDM HDO) as HRING2; eapply (CONT1 ltac:(clear - KXBR HK HSN S16; lia)) with (c320 := Z_to_bv 64 0) (c336 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | clear - HSN KXBR; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | clear - HS8 KXBR HSN; lia | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8cdac) _ _ _ _) => (cells_split 19%nat FR; cells_split2 4%nat FR; apply sql_ring_close_0 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 0 dll dml dof HRING HDL HDM HDO) as HRING2; assert (ESN : sn = nbSeq - 1) by (clear - KXBR HSN HS8 HK S16 RG; first [lia | (rewrite ?Z.mod_small in * by lia; lia)]); rewrite ESN in FR; eapply CONT2 with (c128 := Z_to_bv 64 0) (c232 := Z_to_bv 64 0) (c320 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - cells_split 19%nat FR; apply (sql_ring_open_1 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML;
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8ae50; 0x8cdac] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange sn 8 98046;
     KZRange nbSeq 9 98047;
     KZRange OP 4096 (2^47);
     KZRange r 0 (2^47);
     KZRange (OP + r) 4096 (2^47);
     KZRange dll 0 262143;
     KZRange dml 0 262143;
     KZRange dof 0 (2^64 - 1)]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ae50) _ _ _ _) => (cells_split 19%nat FR; cells_split2 5%nat FR; apply sql_ring_close_1 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 1 dll dml dof HRING HDL HDM HDO) as HRING2; eapply (CONT1 ltac:(clear - KXBR HK HSN S16; lia)) with (c320 := Z_to_bv 64 0) (c336 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | clear - HSN KXBR; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | clear - HS8 KXBR HSN; lia | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8cdac) _ _ _ _) => (cells_split 19%nat FR; cells_split2 5%nat FR; apply sql_ring_close_1 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 1 dll dml dof HRING HDL HDM HDO) as HRING2; assert (ESN : sn = nbSeq - 1) by (clear - KXBR HSN HS8 HK S16 RG; first [lia | (rewrite ?Z.mod_small in * by lia; lia)]); rewrite ESN in FR; eapply CONT2 with (c128 := Z_to_bv 64 0) (c232 := Z_to_bv 64 0) (c320 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - cells_split 19%nat FR; apply (sql_ring_open_2 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML;
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8ae50; 0x8cdac] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange sn 8 98046;
     KZRange nbSeq 9 98047;
     KZRange OP 4096 (2^47);
     KZRange r 0 (2^47);
     KZRange (OP + r) 4096 (2^47);
     KZRange dll 0 262143;
     KZRange dml 0 262143;
     KZRange dof 0 (2^64 - 1)]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ae50) _ _ _ _) => (cells_split 19%nat FR; cells_split2 5%nat FR; apply sql_ring_close_2 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 2 dll dml dof HRING HDL HDM HDO) as HRING2; eapply (CONT1 ltac:(clear - KXBR HK HSN S16; lia)) with (c320 := Z_to_bv 64 0) (c336 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | clear - HSN KXBR; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | clear - HS8 KXBR HSN; lia | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8cdac) _ _ _ _) => (cells_split 19%nat FR; cells_split2 5%nat FR; apply sql_ring_close_2 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 2 dll dml dof HRING HDL HDM HDO) as HRING2; assert (ESN : sn = nbSeq - 1) by (clear - KXBR HSN HS8 HK S16 RG; first [lia | (rewrite ?Z.mod_small in * by lia; lia)]); rewrite ESN in FR; eapply CONT2 with (c128 := Z_to_bv 64 0) (c232 := Z_to_bv 64 0) (c320 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - cells_split 19%nat FR; apply (sql_ring_open_3 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML;
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8ae50; 0x8cdac] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange sn 8 98046;
     KZRange nbSeq 9 98047;
     KZRange OP 4096 (2^47);
     KZRange r 0 (2^47);
     KZRange (OP + r) 4096 (2^47);
     KZRange dll 0 262143;
     KZRange dml 0 262143;
     KZRange dof 0 (2^64 - 1)]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ae50) _ _ _ _) => (cells_split 19%nat FR; cells_split2 5%nat FR; apply sql_ring_close_3 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 3 dll dml dof HRING HDL HDM HDO) as HRING2; eapply (CONT1 ltac:(clear - KXBR HK HSN S16; lia)) with (c320 := Z_to_bv 64 0) (c336 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | clear - HSN KXBR; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | clear - HS8 KXBR HSN; lia | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8cdac) _ _ _ _) => (cells_split 19%nat FR; cells_split2 5%nat FR; apply sql_ring_close_3 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 3 dll dml dof HRING HDL HDM HDO) as HRING2; assert (ESN : sn = nbSeq - 1) by (clear - KXBR HSN HS8 HK S16 RG; first [lia | (rewrite ?Z.mod_small in * by lia; lia)]); rewrite ESN in FR; eapply CONT2 with (c128 := Z_to_bv 64 0) (c232 := Z_to_bv 64 0) (c320 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - cells_split 19%nat FR; apply (sql_ring_open_4 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML;
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8ae50; 0x8cdac] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange sn 8 98046;
     KZRange nbSeq 9 98047;
     KZRange OP 4096 (2^47);
     KZRange r 0 (2^47);
     KZRange (OP + r) 4096 (2^47);
     KZRange dll 0 262143;
     KZRange dml 0 262143;
     KZRange dof 0 (2^64 - 1)]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ae50) _ _ _ _) => (cells_split 19%nat FR; cells_split2 5%nat FR; apply sql_ring_close_4 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 4 dll dml dof HRING HDL HDM HDO) as HRING2; eapply (CONT1 ltac:(clear - KXBR HK HSN S16; lia)) with (c320 := Z_to_bv 64 0) (c336 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | clear - HSN KXBR; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | clear - HS8 KXBR HSN; lia | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8cdac) _ _ _ _) => (cells_split 19%nat FR; cells_split2 5%nat FR; apply sql_ring_close_4 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 4 dll dml dof HRING HDL HDM HDO) as HRING2; assert (ESN : sn = nbSeq - 1) by (clear - KXBR HSN HS8 HK S16 RG; first [lia | (rewrite ?Z.mod_small in * by lia; lia)]); rewrite ESN in FR; eapply CONT2 with (c128 := Z_to_bv 64 0) (c232 := Z_to_bv 64 0) (c320 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - cells_split 19%nat FR; apply (sql_ring_open_5 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML;
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8ae50; 0x8cdac] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange sn 8 98046;
     KZRange nbSeq 9 98047;
     KZRange OP 4096 (2^47);
     KZRange r 0 (2^47);
     KZRange (OP + r) 4096 (2^47);
     KZRange dll 0 262143;
     KZRange dml 0 262143;
     KZRange dof 0 (2^64 - 1)]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ae50) _ _ _ _) => (cells_split 19%nat FR; cells_split2 5%nat FR; apply sql_ring_close_5 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 5 dll dml dof HRING HDL HDM HDO) as HRING2; eapply (CONT1 ltac:(clear - KXBR HK HSN S16; lia)) with (c320 := Z_to_bv 64 0) (c336 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | clear - HSN KXBR; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | clear - HS8 KXBR HSN; lia | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8cdac) _ _ _ _) => (cells_split 19%nat FR; cells_split2 5%nat FR; apply sql_ring_close_5 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 5 dll dml dof HRING HDL HDM HDO) as HRING2; assert (ESN : sn = nbSeq - 1) by (clear - KXBR HSN HS8 HK S16 RG; first [lia | (rewrite ?Z.mod_small in * by lia; lia)]); rewrite ESN in FR; eapply CONT2 with (c128 := Z_to_bv 64 0) (c232 := Z_to_bv 64 0) (c320 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - cells_split 19%nat FR; apply (sql_ring_open_6 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML;
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8ae50; 0x8cdac] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange sn 8 98046;
     KZRange nbSeq 9 98047;
     KZRange OP 4096 (2^47);
     KZRange r 0 (2^47);
     KZRange (OP + r) 4096 (2^47);
     KZRange dll 0 262143;
     KZRange dml 0 262143;
     KZRange dof 0 (2^64 - 1)]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ae50) _ _ _ _) => (cells_split 19%nat FR; cells_split2 5%nat FR; apply sql_ring_close_6 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 6 dll dml dof HRING HDL HDM HDO) as HRING2; eapply (CONT1 ltac:(clear - KXBR HK HSN S16; lia)) with (c320 := Z_to_bv 64 0) (c336 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | clear - HSN KXBR; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | clear - HS8 KXBR HSN; lia | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8cdac) _ _ _ _) => (cells_split 19%nat FR; cells_split2 5%nat FR; apply sql_ring_close_6 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 6 dll dml dof HRING HDL HDM HDO) as HRING2; assert (ESN : sn = nbSeq - 1) by (clear - KXBR HSN HS8 HK S16 RG; first [lia | (rewrite ?Z.mod_small in * by lia; lia)]); rewrite ESN in FR; eapply CONT2 with (c128 := Z_to_bv 64 0) (c232 := Z_to_bv 64 0) (c320 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - cells_split 19%nat FR; apply (sql_ring_open_7 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML;
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8ae50; 0x8cdac] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange sn 8 98046;
     KZRange nbSeq 9 98047;
     KZRange OP 4096 (2^47);
     KZRange r 0 (2^47);
     KZRange (OP + r) 4096 (2^47);
     KZRange dll 0 262143;
     KZRange dml 0 262143;
     KZRange dof 0 (2^64 - 1)]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ae50) _ _ _ _) => (cells_split 19%nat FR; cells_split2 4%nat FR; apply sql_ring_close_7 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 7 dll dml dof HRING HDL HDM HDO) as HRING2; eapply (CONT1 ltac:(clear - KXBR HK HSN S16; lia)) with (c320 := Z_to_bv 64 0) (c336 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | clear - HSN KXBR; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | clear - HS8 KXBR HSN; lia | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8cdac) _ _ _ _) => (cells_split 19%nat FR; cells_split2 4%nat FR; apply sql_ring_close_7 in FR; cbn [app] in FR; pose proof (sql_ring_ok_upd 8 rl rm ro 7 dll dml dof HRING HDL HDM HDO) as HRING2; assert (ESN : sn = nbSeq - 1) by (clear - KXBR HSN HS8 HK S16 RG; first [lia | (rewrite ?Z.mod_small in * by lia; lia)]); rewrite ESN in FR; eapply CONT2 with (c128 := Z_to_bv 64 0) (c232 := Z_to_bv 64 0) (c320 := Z_to_bv 64 0) (c352 := Z_to_bv 64 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ult _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF] | eapply sql_lfacts_lp_op; [exact LF0 | cbn [l_DST]; clear - L1 HR0 HOP; lia | clear - HK; lia] | exact HRING2 ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
Qed.

End CANSEC1.
