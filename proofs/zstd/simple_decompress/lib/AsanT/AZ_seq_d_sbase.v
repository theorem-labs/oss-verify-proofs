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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit .
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

Lemma sqd_static_m0 : forall P OEND, sqd_ranges P -> sqd_side P -> sqd_sep P -> sqd_tables P -> sqd_astat P -> sqd_asan P (w_m P) -> sqd_pro P ->
  zd_memmoveZ_stmtA -> zd_memcpyZ_stmtA -> zd_execend_stmtA ->
  (w_LLT P + 4104 <= 2^47 /\ w_OFT P + 2056 <= 2^47 /\ w_MLT P + 4104 <= 2^47) ->
  w_nbSeq P <> 0 -> 1 <= zlen (w_sq P) -> w_LOC P = 0 -> OEND = w_DST P + w_CAP P ->
  sqd_static P OEND (w_LITP P) (w_LITP P + w_LITSZ P) 0.
Proof.
  intros P OEND RG SD SEP TB AS ASN PRO S64 S65 S66 TH NZ N1 EL EO. pose proof AS as AS0. pose proof ASN as ASN0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_ranges sqd_side sqd_sep sqd_tables sqd_astat sqd_asan w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
  destruct SD as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct ASN as (_ & _ & _ & _ & _ & AOUT & _).
  pose proof PRO as PRO0. destruct PRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FBK).
  destruct TH as (TH1 & TH2 & TH3). destruct AST as (AST1 & _).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, ZSTD_not_in_dst, ZSTD_in_dst, DCTX_entropy_rep, DCTX_litExtraBuffer, AIMG_HI, KHIGH in *.
  pose proof atop_range as ATR.
  specialize (Y5 NZ). destruct (Y10 NZ) as (A1 & A2 & A3). specialize (Y11 NZ). destruct (AFT NZ) as (AT1 & AT2 & AT3).
  assert (NZD : DST <> 0) by (intros E; destruct (Y3 E) as (_ & E2); exact (NZ E2)). specialize (Y4 NZD).
  assert (LD : LITP + (LITSZ + 32) <= B0 \/ B0 + (B1 - B0) <= LITP) by (exact (Y8 EL)). assert (LD1 : True) by exact I. pose proof LD1 as LD2. pose proof LD1 as LD3. clear Y7 Y8.
  assert (BB : B0 < B1) by (clear - G6 G7 Y5 Y11; lia).
  destruct (AOUT BB) as (ABO & _). destruct (ABO ltac:(clear - BB; lia)) as (BO & _). pose proof (ablk_lits _ _ BO) as BOL.
  pose proof (ablk_lits _ _ FBK) as FBL. assert (FF0 : 0 <= FF) by (clear - FFa; lia).
  assert (ESHF2 : SHF = 2147450880 + FF / 8) by (rewrite ESHF, shad_div; reflexivity).
  subst OEND. clear Y3 Y6 AOUT ABO.
  constructor; cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1].
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
  - (* [comment removed for export] *) clear - LD; lia.
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
  - (* [comment removed for export] *) clear - P8; lia.
  - (* [comment removed for export] *) clear - T13; lia.
  - (* [comment removed for export] *) clear - T14; lia.
  - (* [comment removed for export] *) clear - T15; lia.
  - (* [comment removed for export] *) clear - P7; lia.
  - (* [comment removed for export] *) clear; lia.
  - (* [comment removed for export] *) right; split; [clear; lia|]; clear - LD; lia.
  - (* [comment removed for export] *) exact Y9.
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
  - (* [comment removed for export] *) clear; split; reflexivity.
  - (* [comment removed for export] *) exact BB.
  - (* [comment removed for export] *) clear - BOL; lia.
  - exact OKLL.
  - exact OKOF.
  - exact OKML.
  (* [comment removed for export] *)
Qed.

Lemma sqd_static_m1 : forall P OEND, sqd_ranges P -> sqd_side P -> sqd_sep P -> sqd_tables P -> sqd_astat P -> sqd_asan P (w_m P) -> sqd_pro P ->
  zd_memmoveZ_stmtA -> zd_memcpyZ_stmtA -> zd_execend_stmtA ->
  (w_LLT P + 4104 <= 2^47 /\ w_OFT P + 2056 <= 2^47 /\ w_MLT P + 4104 <= 2^47) ->
  w_nbSeq P <> 0 -> 1 <= zlen (w_sq P) -> w_LOC P = 1 -> OEND = w_LITB P ->
  sqd_static P OEND (w_LITP P) (w_LITP P + w_LITSZ P) 1.
Proof.
  intros P OEND RG SD SEP TB AS ASN PRO S64 S65 S66 TH NZ N1 EL EO. pose proof AS as AS0. pose proof ASN as ASN0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_ranges sqd_side sqd_sep sqd_tables sqd_astat sqd_asan w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
  destruct SD as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct ASN as (_ & _ & _ & _ & _ & AOUT & _).
  pose proof PRO as PRO0. destruct PRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FBK).
  destruct TH as (TH1 & TH2 & TH3). destruct AST as (AST1 & _).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, ZSTD_not_in_dst, ZSTD_in_dst, DCTX_entropy_rep, DCTX_litExtraBuffer, AIMG_HI, KHIGH in *.
  pose proof atop_range as ATR.
  specialize (Y5 NZ). destruct (Y10 NZ) as (A1 & A2 & A3). specialize (Y11 NZ). destruct (AFT NZ) as (AT1 & AT2 & AT3).
  assert (NZD : DST <> 0) by (intros E; destruct (Y3 E) as (_ & E2); exact (NZ E2)). specialize (Y4 NZD).
  destruct (Y7 EL) as (LD1 & LD2 & LD3). assert (LD : True) by exact I. clear Y8.
  assert (BB : B0 < B1) by (clear - G6 G7 Y5 Y11; lia).
  destruct (AOUT BB) as (ABO & _). destruct (ABO ltac:(clear - BB; lia)) as (BO & _). pose proof (ablk_lits _ _ BO) as BOL.
  pose proof (ablk_lits _ _ FBK) as FBL. assert (FF0 : 0 <= FF) by (clear - FFa; lia).
  assert (ESHF2 : SHF = 2147450880 + FF / 8) by (rewrite ESHF, shad_div; reflexivity).
  subst OEND. clear Y3 Y6 AOUT ABO.
  constructor; cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1].
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
  - (* [comment removed for export] *) left; clear - LD1 LD2 LD3 Y5 Y4 G6; lia.
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
  - (* [comment removed for export] *) clear - P8; lia.
  - (* [comment removed for export] *) clear - T13; lia.
  - (* [comment removed for export] *) clear - T14; lia.
  - (* [comment removed for export] *) clear - T15; lia.
  - (* [comment removed for export] *) clear - P7; lia.
  - (* [comment removed for export] *) clear; lia.
  - (* [comment removed for export] *) right; split; [clear; lia|]; left; clear - LD1 LD2 LD3; lia.
  - (* [comment removed for export] *) exact Y9.
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
  - (* [comment removed for export] *) clear; split; reflexivity.
  - (* [comment removed for export] *) exact BB.
  - (* [comment removed for export] *) clear - BOL; lia.
  - exact OKLL.
  - exact OKOF.
  - exact OKML.
  (* [comment removed for export] *)
Qed.

End CANSEC1.
