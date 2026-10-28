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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_fin AZ_seq_l_xat.
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

Lemma sql_err_ok : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_fin P -> sql_at_err P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST FIN.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  unfold sql_at_err. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP r x1 x5 x6 x7 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 INV HR RES.
  unfold sql_at_fin, sql_finv, sql_fe in FIN. cbn [sql_saved sql_Wb l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FIN. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in FIN.
  pose proof ST as ST0.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sql_frame sql_ffr] in FR, FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof INV as (_ & _ & _ & _ & _ & _ & _ & H5V & XI). cbn [sql_xinv l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI. unfold sql_fe in XI. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI, H5V.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & _).
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in REP, HH3, MU |- *.
  clear INV SQB UFL USEQ RSQ RSQS.
  sd_static_open ST. unfold held in RGB.
  (* [comment removed for export] *)
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sql_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  assert (MUX : munch [(SHF, SHF + 32); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMX : wmono bsegs m1 m1) by apply wmono_refl.
  sql_blob_all SHS.     (* [comment removed for export] *)
  try hold FIN; try hold HR; try hold RES; try hold REP; try hold HH3; try hold H5V; try hold MU; try hold WM; try hold BDL; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML.
  kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8e5f8] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange SHF 2147450880 17594333495296;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZWr SHF 32;
     KZDisj SHF 32 FRB 568;
     KZDisj SHF 32 FF 256]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SHF, 32)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
  all: try sql_aclose.
  all: kx_mem.
  all: (try unfold held in FIN; try unfold held in HR; try unfold held in RES; try unfold held in REP; try unfold held in HH3; try unfold held in H5V; try unfold held in MU; try unfold held in WM; try unfold held in BDL; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
    eapply FIN; [| exact HR | exact RES];
    (* [comment removed for export] *)
    sql_blob_last FRF; sql_blob_all SHS;
    pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
    split; [eexists; exact FRF|];
    split; [eexists; exact SHS|];
    split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - RGA6; lia]|];
    split; [exact SAV|];
    split; [exists (Z_to_bv 64 LOCV); destruct H5V as [H5R H5L]; split; [| exact H5L];
            eapply rw_cells_transport; [exact H5R | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add h5_vcells]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|];
    split; [eapply wmono_trans; [exact WM | exact WMX] | exact KXMI]
  end.
Qed.

Lemma sql_errx_ok : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_fin P -> sql_at_errx P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST FIN.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  unfold sql_at_errx. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP r x1 x5 x6 x7 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 INV HR RES.
  unfold sql_at_fin, sql_finv, sql_fe in FIN. cbn [sql_saved sql_Wb l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FIN. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in FIN.
  pose proof ST as ST0.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sql_frame sql_ffr] in FR, FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof INV as (_ & _ & _ & _ & _ & _ & _ & H5V & XI). cbn [sql_xinv l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI. unfold sql_fe in XI. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI, H5V.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & _).
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in REP, HH3, MU |- *.
  clear INV SQB UFL USEQ RSQ RSQS.
  sd_static_open ST. unfold held in RGB.
  (* [comment removed for export] *)
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sql_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  assert (MUX : munch [(SHF, SHF + 32); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMX : wmono bsegs m1 m1) by apply wmono_refl.
  sql_blob_all SHS.     (* [comment removed for export] *)
  try hold FIN; try hold HR; try hold RES; try hold REP; try hold HH3; try hold H5V; try hold MU; try hold WM; try hold BDL; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML.
  kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8e5f8] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange SHF 2147450880 17594333495296;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZWr SHF 32;
     KZDisj SHF 32 FRB 568;
     KZDisj SHF 32 FF 256]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SHF, 32)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
  all: try sql_aclose.
  all: kx_mem.
  all: (try unfold held in FIN; try unfold held in HR; try unfold held in RES; try unfold held in REP; try unfold held in HH3; try unfold held in H5V; try unfold held in MU; try unfold held in WM; try unfold held in BDL; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
    eapply FIN; [| exact HR | exact RES];
    (* [comment removed for export] *)
    sql_blob_last FRF; sql_blob_all SHS;
    pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
    split; [eexists; exact FRF|];
    split; [eexists; exact SHS|];
    split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - RGA6; lia]|];
    split; [exact SAV|];
    split; [exists (Z_to_bv 64 LOCV); destruct H5V as [H5R H5L]; split; [| exact H5L];
            eapply rw_cells_transport; [exact H5R | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add h5_vcells]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|];
    split; [eapply wmono_trans; [exact WM | exact WMX] | exact KXMI]
  end.
Qed.

Lemma sql_errq_ok : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_fin P -> sql_at_errq P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST FIN.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  unfold sql_at_errq. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP r x1 x5 x6 x7 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 INV HR RES.
  unfold sql_at_fin, sql_finv, sql_fe in FIN. cbn [sql_saved sql_Wb l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FIN. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in FIN.
  pose proof ST as ST0.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sql_frame sql_ffr] in FR, FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof INV as (_ & _ & _ & _ & _ & _ & _ & H5V & XI). cbn [sql_xinv l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI. unfold sql_fe in XI. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI, H5V.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & _).
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in REP, HH3, MU |- *.
  clear INV SQB UFL USEQ RSQ RSQS.
  sd_static_open ST. unfold held in RGB.
  (* [comment removed for export] *)
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sql_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  assert (MUX : munch [(SHF, SHF + 32); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMX : wmono bsegs m1 m1) by apply wmono_refl.
  sql_blob_all SHS.     (* [comment removed for export] *)
  try hold FIN; try hold HR; try hold RES; try hold REP; try hold HH3; try hold H5V; try hold MU; try hold WM; try hold BDL; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML.
  kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8e5f8] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange SHF 2147450880 17594333495296;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZWr SHF 32;
     KZDisj SHF 32 FRB 568;
     KZDisj SHF 32 FF 256]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SHF, 32)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
  all: try sql_aclose.
  all: kx_mem.
  all: (try unfold held in FIN; try unfold held in HR; try unfold held in RES; try unfold held in REP; try unfold held in HH3; try unfold held in H5V; try unfold held in MU; try unfold held in WM; try unfold held in BDL; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
    eapply FIN; [| exact HR | exact RES];
    (* [comment removed for export] *)
    sql_blob_last FRF; sql_blob_all SHS;
    pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
    split; [eexists; exact FRF|];
    split; [eexists; exact SHS|];
    split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - RGA6; lia]|];
    split; [exact SAV|];
    split; [exists (Z_to_bv 64 LOCV); destruct H5V as [H5R H5L]; split; [| exact H5L];
            eapply rw_cells_transport; [exact H5R | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add h5_vcells]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|];
    split; [eapply wmono_trans; [exact WM | exact WMX] | exact KXMI]
  end.
Qed.

Lemma sql_errp_ok : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_fin P -> sql_at_errp P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST FIN.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  unfold sql_at_errp. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP r x1 x5 x6 x7 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 INV HR RES.
  unfold sql_at_fin, sql_finv, sql_fe in FIN. cbn [sql_saved sql_Wb l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FIN. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in FIN.
  pose proof ST as ST0.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sql_frame sql_ffr] in FR, FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof INV as (_ & _ & _ & _ & _ & _ & _ & H5V & XI). cbn [sql_xinv l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI. unfold sql_fe in XI. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI, H5V.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & _).
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in REP, HH3, MU |- *.
  clear INV SQB UFL USEQ RSQ RSQS.
  sd_static_open ST. unfold held in RGB.
  (* [comment removed for export] *)
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sql_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  assert (MUX : munch [(SHF, SHF + 32); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMX : wmono bsegs m1 m1) by apply wmono_refl.
  sql_blob_all SHS.     (* [comment removed for export] *)
  try hold FIN; try hold HR; try hold RES; try hold REP; try hold HH3; try hold H5V; try hold MU; try hold WM; try hold BDL; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML.
  kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8e5f8] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange SHF 2147450880 17594333495296;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZWr SHF 32;
     KZDisj SHF 32 FRB 568;
     KZDisj SHF 32 FF 256]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SHF, 32)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
  all: try sql_aclose.
  all: kx_mem.
  all: (try unfold held in FIN; try unfold held in HR; try unfold held in RES; try unfold held in REP; try unfold held in HH3; try unfold held in H5V; try unfold held in MU; try unfold held in WM; try unfold held in BDL; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
    eapply FIN; [| exact HR | exact RES];
    (* [comment removed for export] *)
    sql_blob_last FRF; sql_blob_all SHS;
    pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
    split; [eexists; exact FRF|];
    split; [eexists; exact SHS|];
    split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - RGA6; lia]|];
    split; [exact SAV|];
    split; [exists (Z_to_bv 64 LOCV); destruct H5V as [H5R H5L]; split; [| exact H5L];
            eapply rw_cells_transport; [exact H5R | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add h5_vcells]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|];
    split; [eapply wmono_trans; [exact WM | exact WMX] | exact KXMI]
  end.
Qed.

Lemma sql_e70_ok : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_fin P ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (x1 x5 x6 x7 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 (Z_to_bv 64 (l_FF P)) x12 x13 (Z_to_bv 64 18446744073709551546) x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 (l_SHF P)) x23 x24 (Z_to_bv 64 (l_FF P)) x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8e5a8) (l_fc P) None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST FIN.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP x1 x5 x6 x7 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 INV.
  set (r := 18446744073709551546).
  assert (HR : 0 <= r < 2^64) by (subst r; clear; lia).
  assert (RES : zd_is_error r = true \/ r <= CAP) by (left; subst r; reflexivity).
  unfold sql_at_fin, sql_finv, sql_fe in FIN. cbn [sql_saved sql_Wb l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FIN. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in FIN.
  pose proof ST as ST0.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sql_frame sql_ffr] in FR, FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof INV as (_ & _ & _ & _ & _ & _ & _ & H5V & XI). cbn [sql_xinv l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI. unfold sql_fe in XI. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI, H5V.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & _).
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in REP, HH3, MU |- *.
  clear INV SQB UFL USEQ RSQ RSQS.
  sd_static_open ST. unfold held in RGB.
  (* [comment removed for export] *)
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sql_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  assert (MUX : munch [(SHF, SHF + 32); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMX : wmono bsegs m1 m1) by apply wmono_refl.
  sql_blob_all SHS.     (* [comment removed for export] *)
  try hold FIN; try hold HR; try hold RES; try hold REP; try hold HH3; try hold H5V; try hold MU; try hold WM; try hold BDL; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML.
  kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8e5f8] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange SHF 2147450880 17594333495296;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZWr SHF 32;
     KZDisj SHF 32 FRB 568;
     KZDisj SHF 32 FF 256]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SHF, 32)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
  all: try sql_aclose.
  all: kx_mem.
  all: (try unfold held in FIN; try unfold held in HR; try unfold held in RES; try unfold held in REP; try unfold held in HH3; try unfold held in H5V; try unfold held in MU; try unfold held in WM; try unfold held in BDL; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
    try replace (Z_to_bv 64 (-70)) with (Z_to_bv 64 r) by (subst r; apply Z_to_bv_eqm; reflexivity);
    eapply FIN; [| exact HR | exact RES];
    (* [comment removed for export] *)
    sql_blob_last FRF; sql_blob_all SHS;
    pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
    split; [eexists; exact FRF|];
    split; [eexists; exact SHS|];
    split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - RGA6; lia]|];
    split; [exact SAV|];
    split; [exists (Z_to_bv 64 LOCV); destruct H5V as [H5R H5L]; split; [| exact H5L];
            eapply rw_cells_transport; [exact H5R | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add h5_vcells]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|];
    split; [eapply wmono_trans; [exact WM | exact WMX] | exact KXMI]
  end.
Qed.

Lemma sql_err20_ok : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_fin P ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (x1 x5 x6 x7 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 (Z_to_bv 64 (l_FF P)) x12 x13 (Z_to_bv 64 18446744073709551596) x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 (l_SHF P)) x23 x24 (Z_to_bv 64 (l_FF P)) x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8e5a8) (l_fc P) None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST FIN.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP x1 x5 x6 x7 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 INV.
  set (r := 18446744073709551596).
  assert (HR : 0 <= r < 2^64) by (subst r; clear; lia).
  assert (RES : zd_is_error r = true \/ r <= CAP) by (left; subst r; reflexivity).
  unfold sql_at_fin, sql_finv, sql_fe in FIN. cbn [sql_saved sql_Wb l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FIN. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in FIN.
  pose proof ST as ST0.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sql_frame sql_ffr] in FR, FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof INV as (_ & _ & _ & _ & _ & _ & _ & H5V & XI). cbn [sql_xinv l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI. unfold sql_fe in XI. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI, H5V.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & _).
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in REP, HH3, MU |- *.
  clear INV SQB UFL USEQ RSQ RSQS.
  sd_static_open ST. unfold held in RGB.
  (* [comment removed for export] *)
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sql_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  assert (MUX : munch [(SHF, SHF + 32); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMX : wmono bsegs m1 m1) by apply wmono_refl.
  sql_blob_all SHS.     (* [comment removed for export] *)
  try hold FIN; try hold HR; try hold RES; try hold REP; try hold HH3; try hold H5V; try hold MU; try hold WM; try hold BDL; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML.
  kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8e5f8] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange SHF 2147450880 17594333495296;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZWr SHF 32;
     KZDisj SHF 32 FRB 568;
     KZDisj SHF 32 FF 256]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SHF, 32)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
  all: try sql_aclose.
  all: kx_mem.
  all: (try unfold held in FIN; try unfold held in HR; try unfold held in RES; try unfold held in REP; try unfold held in HH3; try unfold held in H5V; try unfold held in MU; try unfold held in WM; try unfold held in BDL; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
    try replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 r) by (subst r; apply Z_to_bv_eqm; reflexivity);
    eapply FIN; [| exact HR | exact RES];
    (* [comment removed for export] *)
    sql_blob_last FRF; sql_blob_all SHS;
    pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
    split; [eexists; exact FRF|];
    split; [eexists; exact SHS|];
    split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - RGA6; lia]|];
    split; [exact SAV|];
    split; [exists (Z_to_bv 64 LOCV); destruct H5V as [H5R H5L]; split; [| exact H5L];
            eapply rw_cells_transport; [exact H5R | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add h5_vcells]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|];
    split; [eapply wmono_trans; [exact WM | exact WMX] | exact KXMI]
  end.
Qed.

Lemma sql_err20c_ok : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_fin P ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 (l_SHF P)) x23 x24 (Z_to_bv 64 (l_FF P)) x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8e5a0) (l_fc P) None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST FIN.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 INV.
  set (r := 18446744073709551596).
  assert (HR : 0 <= r < 2^64) by (subst r; clear; lia).
  assert (RES : zd_is_error r = true \/ r <= CAP) by (left; subst r; reflexivity).
  unfold sql_at_fin, sql_finv, sql_fe in FIN. cbn [sql_saved sql_Wb l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FIN. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in FIN.
  pose proof ST as ST0.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sql_frame sql_ffr] in FR, FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof INV as (_ & _ & _ & _ & _ & _ & _ & H5V & XI). cbn [sql_xinv l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI. unfold sql_fe in XI. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI, H5V.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & _).
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in REP, HH3, MU |- *.
  clear INV SQB UFL USEQ RSQ RSQS.
  sd_static_open ST. unfold held in RGB.
  (* [comment removed for export] *)
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sql_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  assert (MUX : munch [(SHF, SHF + 32); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMX : wmono bsegs m1 m1) by apply wmono_refl.
  sql_blob_all SHS.     (* [comment removed for export] *)
  try hold FIN; try hold HR; try hold RES; try hold REP; try hold HH3; try hold H5V; try hold MU; try hold WM; try hold BDL; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML.
  kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8e5f8] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange SHF 2147450880 17594333495296;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZWr SHF 32;
     KZDisj SHF 32 FRB 568;
     KZDisj SHF 32 FF 256]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SHF, 32)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
  all: try sql_aclose.
  all: kx_mem.
  all: (try unfold held in FIN; try unfold held in HR; try unfold held in RES; try unfold held in REP; try unfold held in HH3; try unfold held in H5V; try unfold held in MU; try unfold held in WM; try unfold held in BDL; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
    try replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 r) by (subst r; apply Z_to_bv_eqm; reflexivity);
    eapply FIN; [| exact HR | exact RES];
    (* [comment removed for export] *)
    sql_blob_last FRF; sql_blob_all SHS;
    pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
    split; [eexists; exact FRF|];
    split; [eexists; exact SHS|];
    split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - RGA6; lia]|];
    split; [exact SAV|];
    split; [exists (Z_to_bv 64 LOCV); destruct H5V as [H5R H5L]; split; [| exact H5L];
            eapply rw_cells_transport; [exact H5R | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add h5_vcells]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|];
    split; [eapply wmono_trans; [exact WM | exact WMX] | exact KXMI]
  end.
Qed.

Lemma sql_err20d_ok : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_fin P ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 (l_SHF P)) x23 x24 x25 x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8e79c) (l_fc P) None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST FIN.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV.
  set (r := 18446744073709551596).
  assert (HR : 0 <= r < 2^64) by (subst r; clear; lia).
  assert (RES : zd_is_error r = true \/ r <= CAP) by (left; subst r; reflexivity).
  unfold sql_at_fin, sql_finv, sql_fe in FIN. cbn [sql_saved sql_Wb l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FIN. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in FIN.
  pose proof ST as ST0.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sql_frame sql_ffr] in FR, FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof INV as (_ & _ & _ & _ & _ & _ & _ & H5V & XI). cbn [sql_xinv l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI. unfold sql_fe in XI. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI, H5V.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & _).
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in REP, HH3, MU |- *.
  clear INV SQB UFL USEQ RSQ RSQS.
  sd_static_open ST. unfold held in RGB.
  (* [comment removed for export] *)
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sql_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  assert (MUX : munch [(SHF, SHF + 32); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMX : wmono bsegs m1 m1) by apply wmono_refl.
  sql_blob_all SHS.     (* [comment removed for export] *)
  try hold FIN; try hold HR; try hold RES; try hold REP; try hold HH3; try hold H5V; try hold MU; try hold WM; try hold BDL; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML.
  kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8e5f8] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange SHF 2147450880 17594333495296;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZWr SHF 32;
     KZDisj SHF 32 FRB 568;
     KZDisj SHF 32 FF 256]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SHF, 32)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
  all: try sql_aclose.
  all: kx_mem.
  all: (try unfold held in FIN; try unfold held in HR; try unfold held in RES; try unfold held in REP; try unfold held in HH3; try unfold held in H5V; try unfold held in MU; try unfold held in WM; try unfold held in BDL; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
    try replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 r) by (subst r; apply Z_to_bv_eqm; reflexivity);
    eapply FIN; [| exact HR | exact RES];
    (* [comment removed for export] *)
    sql_blob_last FRF; sql_blob_all SHS;
    pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
    split; [eexists; exact FRF|];
    split; [eexists; exact SHS|];
    split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - RGA6; lia]|];
    split; [exact SAV|];
    split; [exists (Z_to_bv 64 LOCV); destruct H5V as [H5R H5L]; split; [| exact H5L];
            eapply rw_cells_transport; [exact H5R | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add h5_vcells]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|];
    split; [eapply wmono_trans; [exact WM | exact WMX] | exact KXMI]
  end.
Qed.

End CANSEC1.
