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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_ibase AZ_seq_s_iat AZ_seq_s_fin AZ_seq_s_xat.
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

Section CANSEC1. Context {rc : runConstT}.

Lemma sqs_ierr_ok : forall P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> sqs_at_fin P -> sqs_at_ierr P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST FIN.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  unfold sqs_at_ierr. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1].
  intros m1 ja jb jc jf x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 IINV.
  unfold sqs_at_fin, sqs_finv, sqs_fe in FIN. cbn [sqs_saved sqs_Wb v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in FIN. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in FIN.
  pose proof ST as ST0.
  apply (sqs_rg_k _ _ _ _ _ ST); cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  destruct IINV as (FR & FRF & _ & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI). cbn [sqs_xinv sqs_fe v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in FR, FRF, H5V, XI.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & MI).
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in REP, HH3, MU |- *.
  sd_static_open ST. unfold held in RGB.
  (* [comment removed for export] *)
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sqs_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  assert (MUX : munch [(SHF, SHF + 32); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMX : wmono bsegs m1 m1) by apply wmono_refl.
  sqs_blob_all SHS.     (* [comment removed for export] *)
  try hold FIN; try hold REP; try hold HH3; try hold H5V; try hold H5L; try hold MU; try hold WM; try hold BDL; try hold TLL; try hold TOF; try hold TML; try hold SQB; try hold LIT; try hold XLIT; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold S72; try hold S73; try hold OKLL; try hold OKOF; try hold OKML.
  kx_autoFLA (FR, FRF) [] [0x91ffc] 48%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 384);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange SHF 2147450880 17594333495296;
     KZWr FRB 280;
     KZWr FF 256;
     KZDisj FF 256 FRB 280;
     KZWr SHF 32;
     KZDisj SHF 32 FRB 280;
     KZDisj SHF 32 FF 256]
    [(FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256); (SHF, 32)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try sqs_aclose.
  all: kx_mem.
  all: (try unfold held in FIN; try unfold held in REP; try unfold held in HH3; try unfold held in H5V; try unfold held in H5L; try unfold held in MU; try unfold held in WM; try unfold held in BDL; try unfold held in TLL; try unfold held in TOF; try unfold held in TML; try unfold held in SQB; try unfold held in LIT; try unfold held in XLIT; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in S72; try unfold held in S73; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x91ffc) _ _ ?mx _) =>
    try replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply Z_to_bv_eqm; reflexivity);
    eapply (FIN _ 18446744073709551596); [| clear; lia | left; reflexivity];
    (* [comment removed for export] *)
    sqs_blob_last FRF; sqs_blob_all SHS;
    pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
    split; [eexists; exact FRF|];
    split; [eexists; exact SHS|];
    split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - RGA6; lia]|];
    split; [exact SAV|];
    split; [exists (Z_to_bv 64 LOCV); split; [| exact H5L];
            eapply rw_cells_transport; [exact H5V | exact MUX | exact WMX | unfold h5_vcells; cbn [disjoint_from cells_size csize Nat.add]; unfold held in S54; unfold held in BDL; clear - BDL S54 RGA1 RGA2 RGA8 RGB RGC1; split; [lia| split; [lia| exact I]]]|];
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|];
    split; [eapply wmono_trans; [exact WM | exact WMX] | exact KXMI]
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
  | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
  end.
Qed.

End CANSEC1.
