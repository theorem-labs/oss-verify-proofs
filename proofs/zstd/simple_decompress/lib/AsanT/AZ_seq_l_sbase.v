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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit .
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

Lemma sql_static_m : forall P OEND, sql_ranges P -> sql_side P -> sql_sep P -> sql_tables P -> sql_astat P -> sql_asan P (l_m P) -> sql_pro P ->
  zd_memmoveZ_stmtA -> zd_execend_split_stmtA -> zd_execend_stmtA ->
  (l_LLT P + 4104 <= 2^47 /\ l_OFT P + 2056 <= 2^47 /\ l_MLT P + 4104 <= 2^47) ->
  l_nbSeq P <> 0 -> 1 <= zlen (l_sq P) -> (l_LOC P = 1 -> OEND = l_LITB P) -> (l_LOC P <> 1 -> OEND = l_DST P + l_CAP P) ->
  sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P).
Proof.
  intros P OEND RG SD SEP TB AS ASN PRO S64 S65 S66 TH NZ N1 EO1 EO2. pose proof AS as AS0. pose proof ASN as ASN0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_ranges sql_side sql_sep sql_tables sql_astat sql_asan l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
  destruct SD as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct ASN as (_ & _ & _ & _ & _ & AOUT & _).
  pose proof PRO as PRO0. destruct PRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FBK).
  destruct TH as (TH1 & TH2 & TH3). destruct AST as (AST1 & _).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, ZSTD_not_in_dst, ZSTD_in_dst, DCTX_entropy_rep, DCTX_litExtraBuffer, AIMG_HI, KHIGH in *.
  pose proof atop_range as ATR.
  specialize (Y5 NZ). destruct (Y11 NZ) as (A1 & A2 & A3). specialize (Y12 NZ). destruct (AFT NZ) as (AT1 & AT2 & AT3).
  assert (NZD : DST <> 0) by (intros E; destruct (Y3 E) as (_ & E2); exact (NZ E2)). specialize (Y4 NZD).
  assert (BB : B0 < B1) by (clear - G6 G7 Y5 Y12; lia).
  unfold ZSTD_split in *.
  assert (HO : DST <= OEND <= DST + CAP).
  { destruct (Z.eq_dec LOC 1) as [EL1|EL1]; [rewrite (EO1 EL1); destruct (Y7 EL1) as (X1 & _); clear - X1; lia | rewrite (EO2 EL1); clear - G8; lia]. }
  assert (LD : (B0 <= LITP /\ LBE + 32 <= B1) \/ LBE + 32 <= B0 \/ B1 <= LITP).
  { destruct Y6 as [EL|[EL|EL]]; [pose proof (Y8 EL) as X; clear - X; lia | destruct (Y7 EL) as (X1 & X2 & X3); clear - X1 X2 X3 G6; lia | destruct (Y9 EL) as (X1 & X2); clear - X1 X2 G6 G7; lia]. }
  assert (LD36 : LBE + 32 <= DCTX + 26684 \/ DCTX + 30372 <= LITP).
  { destruct (Z.eq_dec LOC 2) as [EL|EL]; [destruct (Y9 EL) as (X1 & X2); clear - X1 X2 G6 G7 P5; lia | pose proof (P8 EL) as X; clear - X G10 G11; lia]. }
  assert (LD42 : (LOC = 2 /\ B0 <= LITP /\ LBE + 32 <= OEND) \/ (LOC <> 2 /\ ((OEND <= LITP /\ LBE + 32 <= B1) \/ LBE + 32 <= B0 \/ B1 <= LITP))).
  { destruct Y6 as [EL|[EL|EL]].
    - right. split; [clear - EL; lia|]. pose proof (Y8 EL) as X; clear - X; lia.
    - right. split; [clear - EL; lia|]. left. rewrite (EO1 EL). destruct (Y7 EL) as (X1 & X2 & X3); clear - X1 X2 X3; lia.
    - left. rewrite (EO2 ltac:(clear - EL; lia)). destruct (Y9 EL) as (X1 & X2); clear - EL X1 X2 G6; repeat split; lia. }
  assert (LD1 : True) by exact I. pose proof LD1 as LD2. pose proof LD1 as LD3. clear Y7 Y8.
  destruct (AOUT BB) as (ABO & _). destruct (ABO ltac:(clear - BB; lia)) as (BO & _). pose proof (ablk_lits _ _ BO) as BOL.
  pose proof (ablk_lits _ _ FBK) as FBL. assert (FF0 : 0 <= FF) by (clear - FFa; lia).
  assert (ESHF2 : SHF = 2147450880 + FF / 8) by (rewrite ESHF, shad_div; reflexivity).
  clear Y3 AOUT ABO.
  constructor; cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - LD; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
  - (* [comment removed for export] *) clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 Y4 Y5 Y12 N1 NZ T4 T5 T6 TH1 TH2 TH3 LD LD1 LD2 LD3 HO; lia.
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
  - (* [comment removed for export] *) clear - LD36; lia.
  - (* [comment removed for export] *) clear - T13; lia.
  - (* [comment removed for export] *) clear - T14; lia.
  - (* [comment removed for export] *) clear - T15; lia.
  - (* [comment removed for export] *) clear - P7; lia.
  - (* [comment removed for export] *) clear - Y6; lia.
  - (* [comment removed for export] *) exact LD42.
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
  - (* [comment removed for export] *) left; split; reflexivity.
  - (* [comment removed for export] *) exact BB.
  - (* [comment removed for export] *) clear - BOL; lia.
  - exact OKLL.
  - exact OKOF.
  - exact OKML.
  - (* [comment removed for export] *) clear - G10 G11 G12; lia.
  - (* [comment removed for export] *) intros EL2; split; [reflexivity|]; split; [reflexivity| exact EL2].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
Qed.

End CANSEC1.
