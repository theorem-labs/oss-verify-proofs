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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit .
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

Lemma sqs_static_m2 : forall P OEND, sqs_ranges P -> sqs_side P -> sqs_sep P -> sqs_tables P -> sqs_astat P -> sqs_asan P (v_m P) -> sqs_pro P ->
  zd_memmoveZ_stmtA -> zd_memcpyZ_stmtA -> zd_execend_stmtA -> zd_execend_split_stmtA ->
  (v_LLT P + 4104 <= 2^47 /\ v_OFT P + 2056 <= 2^47 /\ v_MLT P + 4104 <= 2^47) ->
  v_nbSeq P <> 0 -> 1 <= zlen (v_sq P) -> v_LOC P = 2 -> OEND = v_DST P + v_CAP P ->
  sqs_static P OEND (v_LITP P) (v_LBE P) 2.
Proof.
  intros P OEND RG SD SEP TB AS ASN PRO S64 S65 S66 S72 TH NZ N1 EL EO. pose proof AS as AS0. pose proof ASN as ASN0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_ranges sqs_side sqs_sep sqs_tables sqs_astat sqs_asan v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
  destruct SD as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct ASN as (_ & _ & _ & _ & _ & AOUT & _).
  pose proof PRO as PRO0. destruct PRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FBK).
  destruct TH as (TH1 & TH2 & TH3). destruct AST as (AST1 & _).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_entropy_rep, DCTX_litExtraBuffer, AIMG_HI, KHIGH in *.
  pose proof atop_range as ATR.
  specialize (Y5 NZ). destruct (Y11 NZ) as (A1 & A2 & A3). specialize (Y12 NZ). destruct (AFT NZ) as (AT1 & AT2 & AT3).
  assert (NZD : DST <> 0) by (intros E; destruct (Y3 E) as (_ & E2); exact (NZ E2)). specialize (Y4 NZD).
  destruct (Y9 EL) as (LD & LD1). assert (LD2 : True) by exact I. pose proof LD2 as LD3. clear Y7 Y8.
  assert (BB : B0 < B1) by (clear - G6 G7 Y5 Y12; lia).
  destruct (AOUT BB) as (ABO & _). destruct (ABO ltac:(clear - BB; lia)) as (BO & _). pose proof (ablk_lits _ _ BO) as BOL.
  pose proof (ablk_lits _ _ FBK) as FBL. assert (FF0 : 0 <= FF) by (clear - FFa; lia).
  assert (ESHF2 : SHF = 2147450880 + FF / 8) by (rewrite ESHF, shad_div; reflexivity).
  subst OEND. clear Y3 Y6 AOUT ABO.
  constructor; cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1].
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) left; clear - LD LD1 G6 G7; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y11 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) clear - P2; lia.
  - (* [comment removed for export] *) clear - P3; lia.
  - (* [comment removed for export] *) clear - P4; lia.
  - (* [comment removed for export] *) clear - P1; lia.
  - (* [comment removed for export] *) clear - T7; lia.
  - (* [comment removed for export] *) clear - T8; lia.
  - (* [comment removed for export] *) clear - T9; lia.
  - (* [comment removed for export] *) clear - P6; lia.
  - (* [comment removed for export] *) clear - P5; lia.
  - (* [comment removed for export] *) clear - T10; lia.
  - (* [comment removed for export] *) clear - T11; lia.
  - (* [comment removed for export] *) clear - T12; lia.
  - (* [comment removed for export] *) (* [comment removed for export] *) clear - LD LD1 G6 G7 P5 BB; lia.
  - (* [comment removed for export] *) clear - T13; lia.
  - (* [comment removed for export] *) clear - T14; lia.
  - (* [comment removed for export] *) clear - T15; lia.
  - (* [comment removed for export] *) clear - P7; lia.
  - (* [comment removed for export] *) clear; lia.
  - (* [comment removed for export] *) left; split; [reflexivity|]; clear - LD LD1 G6 G7; lia.
  - (* [comment removed for export] *) exact Y10.
  - (* [comment removed for export] *) clear - A1; lia.
  - (* [comment removed for export] *) clear - A2; lia.
  - (* [comment removed for export] *) clear - A3; lia.
  - (* [comment removed for export] *) exact ES1.
  - (* [comment removed for export] *) exact ES1b.
  - (* [comment removed for export] *) clear - FBL; lia.
  - (* [comment removed for export] *) clear - FFb ATL; lia.
  - (* [comment removed for export] *) exact FFc.
  - (* [comment removed for export] *) clear - ESHF2 FF0; Z.div_mod_to_equations; lia.
  - (* [comment removed for export] *) clear - ESHF2 FFb ATR AST1 G13; Z.div_mod_to_equations; lia.
  - (* [comment removed for export] *) clear - AFD; lia.
  - (* [comment removed for export] *) specialize (AFO BB); clear - AFO; lia.
  - (* [comment removed for export] *) specialize (AFS ltac:(clear - N1; lia)); clear - AFS; lia.
  - (* [comment removed for export] *) clear - AFL; lia.
  - (* [comment removed for export] *) clear - AT1; lia.
  - (* [comment removed for export] *) clear - AT2; lia.
  - (* [comment removed for export] *) clear - AT3; lia.
  - (* [comment removed for export] *) exact AS0.
  - (* [comment removed for export] *) exact ASN0.
  - (* [comment removed for export] *) exact PRO0.
  - (* [comment removed for export] *) exact S64.
  - (* [comment removed for export] *) exact S65.
  - (* [comment removed for export] *) exact S66.
  - (* [comment removed for export] *) left; clear; split; reflexivity.
  - (* [comment removed for export] *) exact BB.
  - (* [comment removed for export] *) clear - BOL; lia.
  - exact OKLL.
  - exact OKOF.
  - exact OKML.
  - (* [comment removed for export] *) clear - G10 G11 G12; lia.
  - (* [comment removed for export] *) intros _; clear - EL; repeat split; lia.
  - (* [comment removed for export] *) exact S72.
  - (* [comment removed for export] *) intros NE; exfalso; clear - NE; lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
Qed.

End CANSEC1.
