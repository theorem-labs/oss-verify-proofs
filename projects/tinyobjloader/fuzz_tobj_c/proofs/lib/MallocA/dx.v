(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Kernel.Fork.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require di.

(* [comment removed for export] *)
Module InvInitV.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "nat"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "sv"; "rw"; "eval"; "SLit"; "SAlu"; "SVar"; "smatch"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "cell_ok"; "filled"; "mkACell"; "present"; "acell"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Logic"; "and"; "ex"; "eq"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "STORE"; "DEPOT"; "MAP1"; "MAP1N"; "NFBLK"; "TABSZ"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "mkEntry"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init"; "imgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8"; "MAIN_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoff"; "sheet"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.di.InvInitV0"; "LIT0"; "LITV"; "PRES0"; "PRESV"; "SYM0"; "SYMV"; "ZEROV"; "bkV"; "f0V"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Kernel.Fork.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundI SymSoundM SymFrame SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvInitB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvInitZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require di.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvInitB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.InvInitC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvInitZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.di.InvInitV0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Placement KxA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartArgBytes StartReshape Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartTop StartMain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartHandoffLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartHandoff StartHandoffFacts.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartArgBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.StartBD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8Out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartTop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.StartMainFds OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoffLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g5.StartHandoffStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g5.StartHandoffApart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.StartHandoffBlocks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.StartHandoffBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoff OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoffFacts.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Facts.
Variables (sp brk mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
Hypothesis Hent : ltac2:(tb__ "0|0|
S32S2dS2bVsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Variables (tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 : word) (x : Z) (o : out18) (v : bool) (rho4 rho' rho1 rhoM : valuation) (tp : list word) (w : world).
Hypothesis HS : ltac2:(tb__ "0|0|
S2fVsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vb10;Vb12;Vb13;Vb14;Vx;Vo;Vv;Vrho4;Vrho';Vrho1;VrhoM;Vtp;Vw;A1d").

Local Notation L := (objsV v).
Local Notation m := (view segsA (rm rhoM)).
Local Notation U := bv_unsigned.

Lemma sheet_match : ltac2:(tb__ "0|2|
S1cS7S28A1M0G0S1cS25S25S1cS27S27S1bS11S9Vrho1;S31S2eVv;A1A1M1S4G0S29R3S2aR2R1A2A4A4S1aQ40A1S30Vrho1;S12G1A1R1A3S1dS8S1aQ8A1A1SaVrhoM;R2A2S26R4R2A2A3F_;Fa;A2Lmd;A2Lms;A2Ltr;A2").
Proof.
  pose proof HS as (Sfds & Sfs & Slim & SMI & Stid & Sx & G2 & G3 & HPL & HPL4 & HPL5 & HPL6 & HPL7 & HPL8 & HPL9 & HPL10 & Ho & HPL12 & HPL13 & HPL14
                    & W12 & W13 & W14 & SJ & V25 & Lr & ROK & RW1 & RL1 & H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & H36 & H77 & H78 & H83
                    & H159 & H160 & H161 & Etp & Hsm1 & RMo & RMi & _).
  destruct w as [tr [ms md]]. rewrite virt_unfold in Hsm1, RMi. cbn [snd cfg_ms] in RMi. eexists _, _, _. split; [exact Hsm1 | exact RMi].
Qed.

Lemma U_lit0 : ltac2:(tb__ "0|1|
S1dS0S19Q40SdVrho1;SeZ0M0A1A2A2G0A3").
Proof. cbn [eval]. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma V_lit0 : ltac2:(tb__ "0|0|
S18S1eS18R1S33A3S14S13S9SaVrhoM;A1A2R2A2F_;Fc;").
Proof.
  intros [a wd val] Hin. destruct sheet_match as (tr & ms & md & Hsm & Hrm).
  pose proof (proj1 (forallb_forall _ _) (LIT0_chk v) _ Hin) as C. cbn [c_addr c_w c_val] in C.
  pose proof (hcell_lit rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm (SLit 0) a wd val C) as X. cbv beta zeta in X. rewrite U_lit0, Z.add_0_l in X. exact X.
Qed.
Lemma V_sym0 : ltac2:(tb__ "0|1|
S0S6SbS1eS5S5S0S6A2M0SbA2S4G0SbS4S0S6R3R2A4R1A4S37A3S14S13S9SaVrhoM;A1A2S16R4R3S19Q40SdVrho1;R2A2A2A3A2F_;Fe;Fwd;Fa;").
Proof.
  intros a wd e Hin. destruct sheet_match as (tr & ms & md & Hsm & Hrm).
  pose proof (proj1 (forallb_forall _ _) (SYM0_chk v) _ Hin) as C. cbn [fst snd] in C.
  pose proof (hcell_sym rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm (SLit 0) a wd e (U (eval rho1 e)) C ltac:(symmetry; apply Z_to_bv_bv_unsigned)) as X.
  cbv beta zeta in X. rewrite U_lit0, Z.add_0_l in X. exact X.
Qed.
Lemma V_litv : ltac2:(tb__ "0|2|
S1S0S6S0S1eS5S5S5S1S0A2M0S6A2M1S0A2S4G1S0S4G0S6S4S1S0R4R3A4R2A4R1A4S34A3S14S13S9SaVrhoM;A1A2S16S2S19Q40ScVrho1;R5A2A2R4A2R3R2A3A2F_;Fval;Fwd;Foff;Fi;").
Proof.
  intros i off wd val Hin. destruct sheet_match as (tr & ms & md & Hsm & Hrm).
  pose proof (proj1 (forallb_forall _ _) (LITV_chk v) _ Hin) as C. cbn [fst snd] in C.
  exact (hcell_lit rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm (SVar i) off wd val C).
Qed.
Lemma V_symv : ltac2:(tb__ "0|3|
S1S0S6SbS1eS5S5S5S1S0A2M0S6A2M1SbA2S4G1SbS4G0S6S4S1S0R4R3A4R2A4R1A4S38A3S14S13S9SaVrhoM;A1A2S16S2S19Q40M2ScVrho1;R5A2A2R4A2R3S19G2SdVrho1;R2A2A2A3A2F_;Fe;Fwd;Foff;Fi;").
Proof.
  intros i off wd e Hin. destruct sheet_match as (tr & ms & md & Hsm & Hrm).
  pose proof (proj1 (forallb_forall _ _) (SYMV_chk v) _ Hin) as C. cbn [fst snd] in C.
  exact (hcell_sym rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm (SVar i) off wd e (U (eval rho1 e)) C ltac:(symmetry; apply Z_to_bv_bv_unsigned)).
Qed.
Lemma V_zerov : ltac2:(tb__ "0|2|
S1S0S0S1eS5S5S1S0A2M0S0A2S4G0S0S4S1S0R3R2A4R1A4S39A3S15S13S9SaVrhoM;A1A2S2S19Q40ScVrho1;R4A2A2M1R3A2S2G1R2A2Z0A4F_;Fb;Fa;Fi;").
Proof.
  intros i a b Hin. destruct sheet_match as (tr & ms & md & Hsm & Hrm).
  pose proof (proj1 (forallb_forall _ _) (proj1 (RNGV_chk v)) _ Hin) as C. cbn [fst snd] in C.
  exact (hrange_zero rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm (SVar i) a b C).
Qed.
Lemma V_presv : ltac2:(tb__ "0|2|
S1S0S0S1eS5S5S1S0A2M0S0A2S4G0S0S4S1S0R3R2A4R1A4S36A3S17S13S9SaVrhoM;A1A2S2S19Q40ScVrho1;R4A2A2M1R3A2S2G1R2A2A3F_;Fb;Fa;Fi;").
Proof.
  intros i a b Hin. destruct sheet_match as (tr & ms & md & Hsm & Hrm).
  pose proof (proj1 (forallb_forall _ _) (proj1 (proj2 (RNGV_chk v))) _ Hin) as C. cbn [fst snd] in C.
  exact (hrange_present rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm (SVar i) a b C).
Qed.
Lemma V_pres0 : ltac2:(tb__ "0|0|
S0S0S1eS5S0S0A2S4S0S0R2R1A4S35A3S17S13S9SaVrhoM;A1A2R3R2A3F_;Fb;Fa;").
Proof.
  intros a b Hin. destruct sheet_match as (tr & ms & md & Hsm & Hrm).
  pose proof (proj1 (forallb_forall _ _) (proj1 (PRES0_chk v)) _ Hin) as C. cbn [fst snd] in C.
  pose proof (hrange_present rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm (SLit 0) a b C) as X. cbv beta zeta in X. rewrite U_lit0, !Z.add_0_l in X. exact X.
Qed.

Lemma V_ri : ltac2:(tb__ "0|2|
S15S13S9SaVrhoM;A1A2S2S19Q40SdVrho1;SfS2cS10P1eA1SeZ2000000000A1A3A2A2M0Z0M1A2S2G0Z1000A2G1A4").
Proof.
  destruct sheet_match as (tr & ms & md & Hsm & Hrm).
  exact (hrange_zero rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm _ 0 4096 (proj1 (proj2 (proj2 (RNGV_chk v))))).
Qed.
Lemma V_hash : ltac2:(tb__ "0|0|
S1cS0S0S14S13S9SaVrhoM;A1A2S16S2S19Q40ScVrho1;P9fA2A2Z10A2U8R1A3A2Lh;A2").
Proof.
  destruct sheet_match as (tr & ms & md & Hsm & Hrm). eexists.
  exact (hcell_lit rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm (SVar 159) 16 8 _ (proj2 (proj2 (proj2 (RNGV_chk v))))).
Qed.

Lemma V_ia : filled m IA_BEG IA_END 0.
Proof.
  destruct sheet_match as (tr & ms & md & Hsm & Hrm).
  apply (hrange_img_zero rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm IA_BEG IA_END (proj2 (PRES0_chk v))).
  apply (image_zero_3 IA_BEG (Z.to_N (IA_END - IA_BEG)) zscan_IA); unfold IA_BEG, IA_END; lia.
Qed.

Lemma V_depot : ltac2:(tb__ "0|7|
S1bS14S13S9SaVrhoM;A1A2M0S16S1fU8S3bVv;A1A3A2S1bS14G0S16S3aVv;A1M1U4Z1A3A2S1bS15G0S20G1Z0M2A4S1bS15G0S2G1Z4M3A2S2S20S3G3S24A2A2G2A4S1bS15G0S2S21Z8M4A2S2S21S3G4S22A2A2G2A4S1bS15G0S2S1fZ20A2S2S2S1fZ10M5A2M6S3G5S23A2A2G2A4S1bS17G0S2S1fG4A2G6A3S17G0S2S1fZ18A2S2S1fZ1cA2A3A2A2A2A2A2A2A2").
Proof.
  destruct sheet_match as (tr & ms & md & Hsm & Hrm).
  destruct (DEP_chk v) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  assert (BK : DEPOT <= bkV v /\ bkV v + 4 <= DEPOT + 4 * TABSZ) by (unfold DEPOT, TABSZ, bkV; destruct v; lia).
  split.
  { pose proof (hcell_sym rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm (SLit 0) STORE 8 _ (f0V v) C1) as X. cbv beta zeta in X. rewrite U_lit0, Z.add_0_l in X. apply X.
    destruct v; apply bv_eq; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. }
  split.
  { pose proof (hcell_lit rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm (SLit 0) (bkV v) 4 1 C2) as X. cbv beta zeta in X. rewrite U_lit0, Z.add_0_l in X. exact X. }
  split.
  { apply (hrange_img_zero rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm _ _ C3).
    intros y Hy. apply (image_zero_3 DEPOT _ (zscan_tab1 v)); clear - Hy BK; unfold DEPOT, TABSZ in *; rewrite ?Z2N.id by lia; try lia; unfold bkV in *; destruct v; lia. }
  split.
  { apply (hrange_img_zero rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm _ _ C4).
    intros y Hy. apply (image_zero_3 (bkV v + 4) _ (zscan_tab2 v)); clear - Hy BK; unfold DEPOT, TABSZ in *; rewrite ?Z2N.id by lia; try lia; unfold bkV in *; destruct v; lia. }
  split.
  { apply (hrange_img_zero rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm _ _ C5).
    intros y Hy. apply (image_zero_3 (MAP1 + 8) _ zscan_map1); clear - Hy; unfold MAP1, MAP1N in *; rewrite ?Z2N.id by lia; lia. }
  split.
  { apply (hrange_img_zero rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm _ _ C6).
    intros y Hy. apply (image_zero_3 (STORE + 32) _ zscan_blocks); clear - Hy; unfold STORE, NFBLK in *; rewrite ?Z2N.id by lia; lia. }
  split.
  { pose proof (hrange_present rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm (SLit 0) _ _ C7) as X. cbv beta zeta in X. rewrite U_lit0, !Z.add_0_l in X. exact X. }
  pose proof (hrange_present rho1 rhoM (ax_S (MAIN_of v)) tr ms md Hsm Hrm (SLit 0) _ _ C8) as X. cbv beta zeta in X. rewrite U_lit0, !Z.add_0_l in X. exact X.
Qed.
End Facts.
End InvInitV.

(* [comment removed for export] *)
Module InvInitA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "or"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "mul"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "rw"; "sprop"; "SLit"; "SPUle"; "SVar"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "filled"; "maskv"; "cell_ok"; "acell"; "present"; "c_addr"; "c_w"; "bview"; "mkACell"; "c_val"; "restrictv"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "option"; "bool"; "prod"; "list"; "true"; "Some"; "andb"; "nil"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dx.InvInitA.Facts"; "G0g"; "safe"; "nband"; "A0"; "SBz"; "TOPz"; "STOPz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "fs_footb"; "AInvA"; "fs_inv"; "geom_ok"; "inv3"; "model_inv"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "m_vm_lazy"; "Model"; "VmMaps"; "alloc_top"; "vm_maps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "FS_total"; "Sh"; "kSpaceSize"; "FS_frames_off"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "erase_mat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoff"; "tpF"; "sheet"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartMain"; "M1"; "B0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartTop"; "Mmain"; "Bmain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dx.InvInitA"; "inclb"; "acell_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.di.InvInitV0"; "f0V"; "LITV"; "@Corelib.Lists.ListDef"; "repeat"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "mkEntry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init"; "imgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4"; "n7"; "n9"; "spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6"; "n17"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8"; "MAIN_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "pageZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.InvInitP"; "A_0"; "G_0"; "grantZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "FBSZ"; "G0"; "NBSZ"; "depot_inv"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Kernel.Fork.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundI SymSoundM SymFrame SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface IfaceEx SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvInitB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvInitZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require di.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceEx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.InvInitP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvInitB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.InvInitC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvInitZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.di.InvInitG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.di.InvInitL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.di.InvInitV0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dx.InvInitV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Placement KxA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartArgBytes StartReshape Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartTop StartMain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartHandoffLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartHandoff StartHandoffFacts.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartArgBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.StartBD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8Out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartTop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.StartMainFds OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoffLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g5.StartHandoffStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g5.StartHandoffApart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.StartHandoffBlocks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.StartHandoffBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoff OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoffFacts.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition inclb (l1 l2 : list sprop) : bool := ltac2:(tb__ "0|0|
S41S13S13S40S13S17R1A1Vl2;A3Lp;Vl1;A3").
Lemma inclb_incl : ltac2:(tb__ "0|1|
S2bS13A1M0G0S3S29S59R2R1A2S2cA3S42S13R3R2A3F_;Fl2;Fl1;").
Proof.
  intros l1 l2 H p Hp. pose proof (proj1 (forallb_forall _ _) H p Hp) as X. apply existsb_exists in X as (q & Hq & E).
  apply sprop_eqb_sound in E. subst. exact Hq.
Qed.

Lemma F81_chk : ltac2:(tb__ "0|1|
S29S3S29S59S26S13S15S14Z7fff80000000A1S16P51A1M0A2S26S13S15G0S14Z800000000000A1A2S2fS13A1A3A3S18S66S64R1A1A1A1A2S2cA3Fv';").
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Definition acell_eqb (c d : acell) : bool := ltac2:(tb__ "0|0|
S2eS2eSfS1fVc;A1S1fVd;A1A2S70S20Vc;A1S20Vd;A1A2A2SfS23Vc;A1S23Vd;A1A2A2").
Lemma acell_inb : ltac2:(tb__ "0|0|
S1dS2bS1dA1S3S29S40S1dS5aR2A1R1A3S2cA3S3fS1dR3R2A3F_;Fl;Fc;").
Proof.
  intros c l H. apply existsb_exists in H as (d & Hd & E). unfold acell_eqb in E. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.eqb_eq in E1. apply Nat.eqb_eq in E2. apply Z.eqb_eq in E3. destruct c, d. cbn in *. subst. exact Hd.
Qed.

Ltac bands := unfold Placement.SHADOW_BAND_LO, Placement.SHADOW_BAND_HI, Geometry.SHADOW_BAND_LO, Geometry.SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.

Section Facts.
Variables (sp brk mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
Hypothesis Hent : ltac2:(tb__ "0|0|
S68S5fS5eVsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Variables (tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 : word) (x : Z) (o : out18) (v : bool) (rho4 rho' rho1 rhoM : valuation) (tp : list word) (w : world).
Hypothesis HS : ltac2:(tb__ "0|0|
S54Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vb10;Vb12;Vb13;Vb14;Vx;Vo;Vv;Vrho4;Vrho';Vrho1;VrhoM;Vtp;Vw;A1d").

Local Notation m1 := (StartMain.M1 sp brk mb draw lim inp tid).
Local Notation Mm := (StartTop.Mmain m1 a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14).
Local Notation U := bv_unsigned.
Local Notation m := (view segsA (rm rhoM)).

Local Notation VV_LIT0 := (V_lit0 sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) (only parsing).
Local Notation VV_SYM0 := (V_sym0 sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) (only parsing).
Local Notation VV_LITV := (V_litv sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) (only parsing).
Local Notation VV_SYMV := (V_symv sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) (only parsing).
Local Notation VV_ZEROV := (V_zerov sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) (only parsing).
Local Notation VV_PRESV := (V_presv sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) (only parsing).
Local Notation VV_PRES0 := (V_pres0 sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) (only parsing).
Local Notation VV_RI := (V_ri sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) (only parsing).
Local Notation VV_HASH := (V_hash sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) (only parsing).
Local Notation VV_IA := (V_ia sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) (only parsing).
Local Notation VV_DEPOT := (V_depot sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) (only parsing).
Definition SBz : Z := U (spacebeg P).
Definition STOPz : Z := U (rw rho1 81%positive).
Definition TOPz : Z := U sp - 8388608.
Definition A0 : AA := ltac2:(tb__ "0|2|
S69S36S7Q40M0Vb5;A2S7G0Vb6;A2S7G0Vb8;A2S7G0Vb10;A2S7G0Vb4;A2S7G0Vb12;A2S7G0Vb13;A2S38S7G0Vsp;A2S37S5bVv;A1Z0M1S5dS0G1UbA3Ae").
Definition G0g : ageom := ltac2:(tb__ "0|1|
S6aS36S7Q40M0Vb5;A2S7G0Vb6;A2S7G0Vb8;A2S7G0Vb10;A2S7G0Vb4;A2S7G0Vb12;A2S7G0Vb13;A2S38S7G0Vsp;A2S37Ab").

Lemma vals : ltac2:(tb__ "0|1|
S2S3S8Q40A1M0S12Vrho1;P1eA2S62VP;A1A3S2S3G0S12Vrho1;P20A2Vb4;A3S2S3G0S12Vrho1;P21A2Vb5;A3S2S3G0S12Vrho1;P22A2Vb6;A3S2S3G0S12Vrho1;P4dA2Vb8;A3S2S3G0S12Vrho1;P53A2Vb10;A3S2S3G0S12Vrho1;P9fA2Vb12;A3S3G0S12Vrho1;Pa0A2Vb13;A3A2A2A2A2A2A2A2").
Proof.
  pose proof (rho1_vals sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS)
    as (_ & _ & _ & _ & _ & _ & E30 & _ & E32 & E33 & E34 & _ & E77 & _ & E83 & E159 & E160 & _).
  repeat split; assumption.
Qed.

Lemma stop_facts : 140735340871680 <= STOPz <= 2 ^ 47.
Proof.
  pose proof (GM1 sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as (_ & _ & _ & HF).
  pose proof (inclb_incl _ _ (F81_chk v)) as I.
  pose proof (proj1 (Forall_forall _ _) HF _ (I _ (or_introl eq_refl))) as H1.
  pose proof (proj1 (Forall_forall _ _) HF _ (I _ (or_intror (or_introl eq_refl)))) as H2.
  cbn [holds eval] in H1, H2. rewrite u64_of_lit in H1, H2 by lia. unfold STOPz. change (2 ^ 47) with 140737488355328. split; assumption.
Qed.

Lemma geo : ltac2:(tb__ "0|0|
S2S3cS32A1S3dS35A1A2").
Proof.
  pose proof (geo_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS)
    as (HTOP & HP0 & HSB & HgT & HgC & HgD & HgF & HgPAB & HgN & HgS & HSEP).
  pose proof stop_facts as SF.
  split.
  - apply (geom_ok_0 (U P) SBz (U b5) (U b6) (U b8) (U b10) (U b4) (U b12) (U b13) STOPz (U sp) TOPz HTOP HP0 HSB HgT HgC HgD HgF HgPAB HSEP).
    split; [lia | exact (proj2 SF)].
  - exact (inv3_0 (U P) SBz (U b5) (U b6) (U b8) (U b10) (U b4) (U b12) (U b13) STOPz (U sp) TOPz (f0V v) 0 (repeat 0 11) HTOP HSB HgN HgS HSEP).
Qed.

Lemma topG0 : topG G0g = TOPz.
Proof.
  pose proof (geo_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as (HTOP & _).
  exact (topG_0 SBz (U b5) (U b6) (U b8) (U b10) (U b4) (U b12) (U b13) STOPz (U sp) TOPz HTOP).
Qed.

Variables (rhoX : valuation) (q : Z) (n : nat).
Hypothesis VX1 : ltac2:(tb__ "0|2|
S8Q40M0A1S4S2SbVq;S7G0R1A2M1A2ScG1SaVq;SeZ1000SdVn;A1A2A2A2A2A1S3S28S8Q8A1A1S11VrhoX;R2A2S11VrhoM;R2A2A3F_;Fa;").
Hypothesis VX2 : ltac2:(tb__ "0|1|
S0S2SbVq;R1A2ScR1SaVq;SeZ1000SdVn;A1A2A2A2A2S4S3S28S8Q8A1M0A1S11VrhoX;S9Q40R2A2A2S30G0A1A3A1F_;Fz;").
Hypothesis HQB : ltac2:(tb__ "0|0|
S2SbS52Vq;A2SbSaVq;SeZ1000SdVn;A1A2A2S51A2A2").
Hypothesis HQF : ltac2:(tb__ "0|1|
S2SbVq;S4aSaS7Q40Vb10;A2M0S4cA2A1A2SbS4aSaG0S49A2A1SaVq;SeZ1000SdVn;A1A2A2A2A2").
Local Notation mX := (view segsA (rm rhoX)).

Lemma mX_out : ltac2:(tb__ "0|0|
S0S4S2SbVq;R1A2ScR1SaVq;SeZ1000SdVn;A1A2A2A2A2A1S3S28S8Q8A1A1S19S10S11VrhoX;A1R2A3S19S10S11VrhoM;A1R2A3A3F_;Fz;").
Proof.
  intros z Hz. destruct (Z_le_dec 0 z) as [H0|H0]; [destruct (Z_lt_dec z (2 ^ 64)) as [H1|H1]|].
  - rewrite !(view_in segsA) by lia. unfold rd_of. rewrite (VX1 (Z_to_bv 64 z)); [reflexivity|]. rewrite u64_of_lit by lia. exact Hz.
  - rewrite !(view_out segsA) by lia. reflexivity.
  - rewrite !(view_out segsA) by lia. reflexivity.
Qed.
Lemma mX_in : ltac2:(tb__ "0|1|
S0S2SbVq;R1A2ScR1SaVq;SeZ1000SdVn;A1A2A2A2A2S5S8Q8A1M0G0S3S28G0A1S19S10S11VrhoX;A1R3A3S2dG0R1A2A3Lb;A2F_;Fz;").
Proof.
  intros z Hz. assert (R : 0 <= z < 2 ^ 64) by (destruct HQB as [B1 B2]; unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, SHADOW_BAND_HI, HIGH_SHADOW_END in *; lia).
  rewrite (view_in segsA) by exact R. unfold rd_of. pose proof (VX2 z Hz) as D. destruct (rm rhoX (Z_to_bv 64 z)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Definition safe (z : Z) : Prop := ltac2:(tb__ "0|1|
S2S4S2SbS52Vz;A2ScVz;S51A2A2A1S4S2SbS7Q40Vb10;A2M0Vz;A2ScVz;SaG0S49A2A2A2A1A2").
Lemma F_grant : ltac2:(tb__ "0|0|
S6bS37S7Q40Vb10;A2S49A3").
Proof. pose proof (geo_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as (_ & _ & _ & _ & _ & _ & HgF & _). exact HgF. Qed.
Lemma fs_foot_safe : ltac2:(tb__ "0|0|
S0S33R1A1S3S29S39S32R2A2S31A3F_;Fz;").
Proof.
  intros z [Hb Hf]. pose proof F_grant as (_ & F1 & F2 & F3 & F4).
  pose proof (geo_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as (HTOP & _).
  unfold fs_footb, G0g, G_0. cbn [ag_fsb]. rewrite FS_total_val, FS_frames_off_val, FS_kFlagsOffset_val in *.
  assert (SHB : forall y, 0x646000 <= y -> y <= 2 ^ 47 -> SHADOW_BAND_LO <= Sh y /\ Sh y <= SHADOW_BAND_HI).
  { intros y Y1 Y2. unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, LOW_SHADOW_BEG, SHADOW_BAND_HI, HIGH_SHADOW_END.
    pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Y1) as D1. pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Y2) as D2.
    change (2 ^ 47 / 8) with 17592186044416 in D2. change (6578176 / 8) with 822272 in D1. lia. }
  assert (FI : 0x646000 <= U b10) by (unfold IMG_LO, IMG_HI in *; lia).
  pose proof (SHB (U b10 + 36864) ltac:(lia) ltac:(unfold TOPz in *; lia)) as [S1 _].
  pose proof (SHB (U b10 + 11571200) ltac:(lia) ltac:(unfold TOPz in *; lia)) as [_ S2].
  assert (MONO : Sh (U b10 + 36864) <= Sh (U b10 + 11571200)) by (unfold Sh; pose proof (Z.div_le_mono (U b10 + 36864) (U b10 + 11571200) 8 ltac:(lia) ltac:(lia)); lia).
  clear - Hb Hf S1 S2 MONO.
  repeat match goal with |- context [(?a <=? ?b)] => destruct (Z.leb_spec a b) end; repeat match goal with |- context [(?a <? ?b)] => destruct (Z.ltb_spec a b) end; cbn; try reflexivity; exfalso; lia.
Qed.
Lemma mR_safe : ltac2:(tb__ "0|0|
S0S33R1A1S3S28S8Q8A1A1S1bS39S32A1S19S10S11VrhoX;A1A2R2A3S19S10S11VrhoM;A1R2A3A3F_;Fz;").
Proof.
  intros z Hs. rewrite (maskv_out _ _ _ (fs_foot_safe z Hs)). apply mX_out. destruct Hs as [Hb _]. destruct HQB. lia.
Qed.
Lemma cell_safe : ltac2:(tb__ "0|0|
S1dS1cS19S10S11VrhoM;A1A2R1A2S27S4fR1S20R3A1A2S33SaS1fR4A1SdR2A1A2A1F_;Fk;S1cS1bS39S32A1S19S10S11VrhoX;A1A2A2R3A2F_;F_;Fc;").
Proof. intros c Hc Hs k Hk. rewrite (mR_safe _ (Hs k Hk)). exact (Hc k Hk). Qed.
Lemma filled_safe : ltac2:(tb__ "0|0|
S0S0S0S1aS19S10S11VrhoM;A1A2R3R2R1A4S0S2SbR5R1A2ScR1R4A2A2S33R2A1F_;Fz;S1aS1bS39S32A1S19S10S11VrhoX;A1A2A2R5R4R3A4F_;F_;Fb;Fhi;Flo;").
Proof. intros lo hi b H Hs z Hz. rewrite (mR_safe _ (Hs z Hz)). exact (H z Hz). Qed.
Lemma present_safe : ltac2:(tb__ "0|0|
S0S0S1eS19S10S11VrhoM;A1A2R2R1A3S0S2SbR4R1A2ScR1R3A2A2S33R2A1F_;Fz;S1eS1bS39S32A1S19S10S11VrhoX;A1A2A2R4R3A3F_;F_;Fhi;Flo;").
Proof. intros lo hi H Hs z Hz. rewrite (mR_safe _ (Hs z Hz)). exact (H z Hz). Qed.

Lemma safe_sets : ltac2:(tb__ "0|9|
S2S0S2SbZ0R1A2ScR1Z646000A2A2S33R2A1M0F_;Fz;S2S0S2SbS7Q40M1Vb5;A2M2R1A2ScR1SaG2Z1000M3A2A2A2G0F_;Fz;S2S0S2SbS7G1Vb6;A2M4R1A2ScR1SaG4Z10000A2A2A2G0F_;Fz;S2S0S2SbS7G1Vb8;A2M5R1A2ScR1SaG5G3A2A2A2G0F_;Fz;S2S0S2SbSaS36S4bA2M6R1A2ScR1SaG6G3A2A2A2G0F_;Fz;S2S0S2SbS7G1Vb12;A2M7R1A2ScR1SaG7S6eA2A2A2G0F_;Fz;S0S2SbS7G1Vb13;A2M8R1A2ScR1SaG8S6cA2A2A2G0F_;Fz;A2A2A2A2A2A2").
Proof.
  pose proof (geo_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS)
    as (HTOP & HP0 & HSB & HgT & HgC & HgD & HgF & HgPAB & HgN & HgS & HSEP).
  pose proof (seps (U P) (U b5) (U b6) (U b8) (U b10) (U b4) (U b12) (U b13) HSEP)
    as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28).
  pose proof (SB_range (U P) SBz HSB) as (SBr & _).
  assert (KS : kSpaceSize = 0x2000000000) by reflexivity.
  unfold safe, grantZ, sepZ in *. cbn [fst snd] in *. rewrite FS_total_val in *. unfold IMG_LO, IMG_HI, NBSZ, FBSZ, PG in *. bands.
  split; [intros z Hz; clear - Hz HgF; lia|].
  split; [intros z Hz; clear - Hz HgT S10; lia|].
  split; [intros z Hz; clear - Hz HgC S15; lia|].
  split; [intros z Hz; clear - Hz HgD S19; lia|].
  split; [intros z Hz; clear - Hz HP0 SBr KS S4; lia|].
  split; [intros z Hz; clear - Hz HgN S24; lia|].
  intros z Hz; clear - Hz HgS S25; lia.
Qed.

Definition nband (z : Z) : Prop := ltac2:(tb__ "0|0|
S4S2SbS4eVz;A2ScVz;S4dA2A2A1").
Lemma safe_nband : ltac2:(tb__ "0|0|
S0S33R1A1S34R2A1F_;Fz;").
Proof. intros z [H _]. unfold nband. bands. exact H. Qed.
Lemma F_nband : ltac2:(tb__ "0|1|
S0S2SbS7Q40Vb10;A2M0R1A2ScR1SaG0S49A2A2A2S34R2A1F_;Fz;").
Proof. intros z Hz. pose proof F_grant as (_ & _ & _ & _ & F4). unfold nband. bands. lia. Qed.
Lemma cell_X : ltac2:(tb__ "0|0|
S1dS1cS19S10S11VrhoM;A1A2R1A2S27S4fR1S20R3A1A2S34SaS1fR4A1SdR2A1A2A1F_;Fk;S1cS19S10S11VrhoX;A1A2R3A2F_;F_;Fc;").
Proof. intros c Hc Hs k Hk. rewrite mX_out; [exact (Hc k Hk)|]. pose proof (Hs k Hk) as Hb. unfold nband in Hb. destruct HQB. bands. lia. Qed.
Lemma filled_X : ltac2:(tb__ "0|0|
S0S0S0S1aS19S10S11VrhoM;A1A2R3R2R1A4S0S2SbR5R1A2ScR1R4A2A2S34R2A1F_;Fz;S1aS19S10S11VrhoX;A1A2R5R4R3A4F_;F_;Fb;Fhi;Flo;").
Proof. intros lo hi b H Hs z Hz. rewrite mX_out; [exact (H z Hz)|]. pose proof (Hs z Hz) as Hb. unfold nband in Hb. destruct HQB. bands. lia. Qed.
Lemma present_X : ltac2:(tb__ "0|0|
S0S0S1eS19S10S11VrhoM;A1A2R2R1A3S0S2SbR4R1A2ScR1R3A2A2S34R2A1F_;Fz;S1eS19S10S11VrhoX;A1A2R4R3A3F_;F_;Fhi;Flo;").
Proof. intros lo hi H Hs z Hz. rewrite mX_out; [exact (H z Hz)|]. pose proof (Hs z Hz) as Hb. unfold nband in Hb. destruct HQB. bands. lia. Qed.

Ltac in_small := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac lit0_tac := apply cell_X; [apply VV_LIT0; apply acell_inb; vm_compute; reflexivity
                               | intros k Hk; cbn [c_addr c_w] in *; apply safe_nband; apply (proj1 safe_sets); lia].

Theorem rtc_X : rtc_inv mX G0g.
Proof.
  destruct vals as (E30 & E32 & E33 & E34 & E77 & E83 & E159 & E160).
  pose proof safe_sets as (SI & ST & SC & SD & SR & SN & SS).
  unfold rtc_inv, cells_ok, rtc_cells. apply Forall_app. split.
  -
    assert (SYM : forall a e val, In (a, 8%nat, e) SYM0 -> U (eval rho1 e) = val -> 0 <= a -> a + 8 <= 0x646000 -> cell_ok mX (mkACell a 8 val)).
    { intros a e val Hin Ev A0' A1. subst val. apply cell_X; [exact (VV_SYM0 a 8%nat e Hin)|].
      intros k Hk. cbn [c_addr c_w] in *. apply safe_nband. apply SI. lia. }
    unfold rtc_cells_img, G0g, G_0. cbn [ag_spacebeg ag_ss0 ag_nodes0 ag_fsb ag_dtls ag_ctx].
    repeat (apply Forall_cons; [first [ lit0_tac | idtac ] | ]); try apply Forall_nil.
    + apply (SYM 0xeddb8 (SVar 30)); [in_small | cbn [eval]; rewrite E30; reflexivity | lia | lia].
    + apply (SYM 0xeddc8 (SAlu ALU_ADD (SVar 30) (SLit 137438953472))); [in_small | | lia | lia].
      rewrite Start7.U_add_slit'; [cbn [eval]; rewrite E30; reflexivity | lia |].
      cbn [eval]. rewrite E30. pose proof (geo_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as (HTOP & HP0 & HSB & _).
      pose proof (SB_range (U P) SBz HSB) as (SBr & _). unfold SBz in *. clear - HTOP HP0 SBr. bands. lia.
    + apply (SYM 0x1c32d8 (SVar 160)); [in_small | cbn [eval]; rewrite E160; reflexivity | lia | lia].
    + apply (SYM 0x5d32e8 (SVar 159)); [in_small | cbn [eval]; rewrite E159; reflexivity | lia | lia].
    + apply (SYM 0x6245b8 (SVar 83)); [in_small | cbn [eval]; rewrite E83; reflexivity | lia | lia].
    + apply (SYM 0x6245c0 (SVar 77)); [in_small | cbn [eval]; rewrite E77; reflexivity | lia | lia].
    + apply (SYM 0x645960 (SVar 34)); [in_small | cbn [eval]; rewrite E34; reflexivity | lia | lia].
  -
    pose proof stop_facts as SF.
    assert (LV : forall i b off wd val, rw rho1 i = b -> In (i, off, wd, val) LITV -> (forall k, (k < wd)%nat -> nband (U b + off + Z.of_nat k)) -> cell_ok mX (mkACell (U b + off) wd val)).
    { intros i b off wd val Eb Hin Hnb. subst b. apply cell_X; [exact (VV_LITV i off wd val Hin) | exact Hnb]. }
    assert (SV : forall i b off wd e val, rw rho1 i = b -> In (i, off, wd, e) SYMV -> U (eval rho1 e) = val -> (forall k, (k < wd)%nat -> nband (U b + off + Z.of_nat k)) -> cell_ok mX (mkACell (U b + off) wd val)).
    { intros i b off wd e val Eb Hin Ev Hnb. subst b val. apply cell_X; [exact (VV_SYMV i off wd e Hin) | exact Hnb]. }
    unfold rtc_cells_geom, G0g, G_0, fs_log_cell, fs_needs_gc_cell. cbn [ag_ctx ag_thread ag_dtls ag_fsb ag_stack_top ag_stack_bottom].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (SV 34%positive b6 0x98 8%nat (SVar 33)); [exact E34 | in_small | cbn [eval]; rewrite E33; reflexivity | intros k Hk; apply safe_nband, SC; lia].
    + apply (LV 34%positive b6 8 4%nat 0); [exact E34 | in_small | intros k Hk; apply safe_nband, SC; lia].
    + apply (SV 33%positive b5 0 8%nat (SVar 34)); [exact E33 | in_small | cbn [eval]; rewrite E34; reflexivity | intros k Hk; apply safe_nband, ST; lia].
    + apply (SV 33%positive b5 8 8%nat (SVar 81)); [exact E33 | in_small | reflexivity | intros k Hk; apply safe_nband, ST; lia].
    + apply (SV 33%positive b5 16 8%nat (SAlu ALU_ADD (SVar 81) (SLit (-8388608)))); [exact E33 | in_small | | intros k Hk; apply safe_nband, ST; lia].
      rewrite Start7.U_add_slit'; [reflexivity | lia | cbn [eval]; unfold STOPz in SF; lia].
    + apply (LV 33%positive b5 40 1%nat 0); [exact E33 | in_small | intros k Hk; apply safe_nband, ST; lia].
    + apply (LV 33%positive b5 0x30 8%nat 0x624cf0); [exact E33 | in_small | intros k Hk; apply safe_nband, ST; lia].
    + apply (LV 33%positive b5 0x38 8%nat 0x624dcc); [exact E33 | in_small | intros k Hk; apply safe_nband, ST; lia].
    + apply (SV 33%positive b5 0x48 8%nat (SVar 83)); [exact E33 | in_small | cbn [eval]; rewrite E83; reflexivity | intros k Hk; apply safe_nband, ST; lia].
    + apply (LV 77%positive b8 0x18 8%nat 0x6245b8); [exact E77 | in_small | intros k Hk; apply safe_nband, SD; lia].
    + apply (LV 83%positive b10 88 8%nat FS_LOG); [exact E83 | in_small | intros k Hk; apply F_nband; rewrite FS_total_val; lia].
    + apply (LV 83%positive b10 96 1%nat 0); [exact E83 | in_small | intros k Hk; apply F_nband; rewrite FS_total_val; lia].
Qed.

Lemma cell_zero_of_filled : ltac2:(tb__ "0|1|
S21S0S0S0S27S1aR5R4R3Z0M0A4SbR5R3A2SbSaR4SdR3A1A2R5A2S1cR8S22R5R4G0A3A2F_;F_;F_;Fwd;Fa;Fhi;Flo;Fmm;").
Proof.
  intros mm lo hi a wd H H1 H2 k Hk. cbn [c_addr c_w c_val] in *. rewrite (H (a + Z.of_nat k)) by lia. f_equal.
  rewrite (enc_lit_byte wd k 0 Hk). unfold lit_byte. rewrite Z.mod_0_l by lia. rewrite Z.shiftr_0_l. reflexivity.
Qed.

Theorem fs_X : ltac2:(tb__ "0|0|
S3bS24S39S32A1S19S10S11VrhoX;A1A2A2S35A2").
Proof.
  destruct vals as (E30 & E32 & E33 & E34 & E77 & E83 & E159 & E160).
  pose proof F_grant as (_ & F1 & F2 & F3 & F4).
  pose proof (VV_ZEROV 83%positive 0 88 ltac:(in_small)) as Z1. pose proof (VV_ZEROV 83%positive 4096 36864 ltac:(in_small)) as Z2.
  pose proof (VV_PRESV 83%positive 36864 11571200 ltac:(in_small)) as P1. rewrite E83 in Z1, Z2, P1.
  assert (FB : forall c, 0 <= c < FS_NCLASSES -> fs_busy A0 c = []).
  { intros c Hc. unfold fs_busy, nthZ, A0, A_0. cbn [aa_fs_busy]. apply nth_repeat. }
  assert (FOOT1 : forall z, U b10 <= z < U b10 + 88 -> fs_footb G0g z = true).
  { intros z Hz. unfold fs_footb, G0g, G_0. cbn [ag_fsb]. apply orb_true_intro. left. apply orb_true_intro. left.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (FOOT2 : forall z, U b10 + 4096 <= z < U b10 + FS_total -> fs_footb G0g z = true).
  { intros z Hz. unfold fs_footb, G0g, G_0. cbn [ag_fsb]. apply orb_true_intro. left. apply orb_true_intro. right. rewrite FS_kFlagsOffset_val.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (FOOT3 : forall z, Sh (U b10 + FS_frames_off) <= z < Sh (U b10 + FS_total) -> fs_footb G0g z = true).
  { intros z Hz. unfold fs_footb, G0g, G_0. cbn [ag_fsb]. apply orb_true_intro. right.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (MF : forall z, U b10 <= z < U b10 + FS_total -> fs_footb G0g z = true -> restrictv (fs_footb G0g) mX z = m z).
  { intros z Hz Hf. rewrite (restrictv_in _ _ _ Hf). apply mX_out. pose proof (F_nband z Hz) as NB. unfold nband in NB. destruct HQB. bands. lia. }
  unfold fs_inv. cbn zeta. change (aa_geom A0) with G0g. change (ag_fsb G0g) with (U b10).
  split; [reflexivity|].
  split. { intros c Hc. rewrite (FB c Hc). split; [constructor | intros pf []]. }
  split.
  { split; [reflexivity|]. intros c Hc. unfold FS_NCLASSES in Hc.
    assert (EH : nthZ (aa_fs_hint A0) c 0 = 0) by (unfold nthZ, A0, A_0; cbn [aa_fs_hint]; apply nth_repeat).
    rewrite EH. split; [lia|]. unfold fs_hint_cell. intros k Hk. cbn [c_addr c_w c_val] in *.
    rewrite (MF (U b10 + 8 * c + Z.of_nat k)); [|rewrite FS_total_val; lia | apply FOOT1; lia].
    exact (cell_zero_of_filled m _ _ (U b10 + 8 * c) 8 Z1 ltac:(lia) ltac:(lia) k Hk). }
  split.
  { intros c pos Hc Hpos. unfold busyb. rewrite (FB c Hc). cbn [existsb].
    pose proof (fs_class_ok c Hc) as (K1 & _ & _ & _ & _ & _ & K7). unfold fs_flags. rewrite FS_kFlagsOffset_val.
    rewrite MF; [| rewrite FS_total_val; lia | apply FOOT2; rewrite FS_total_val; lia].
    apply Z2. lia. }
  split.
  { intros c pos Hc Hpos _. pose proof (fs_class_ok c Hc) as (_ & K2 & K3 & _ & K5 & K6 & _).
    assert (B : fs_frame (U b10) c pos + fs_frame_size c <= U b10 + FS_total /\ U b10 + 36864 <= fs_frame (U b10) c pos).
    { unfold fs_frame. rewrite FS_frames_off_val, FS_total_val. change (Z.shiftl 1 FS_LOG) with (2 ^ 20) in *.
      assert (pos * fs_frame_size c + fs_frame_size c <= fs_num_iter c * fs_frame_size c) by nia.
      assert (0 <= pos * fs_frame_size c) by nia. unfold FS_NCLASSES in Hc. lia. }
    intros z Hz. rewrite MF; [| rewrite FS_total_val in *; lia | apply FOOT2; rewrite FS_total_val in *; lia].
    apply P1. rewrite FS_total_val in B. lia. }
  intros z Hz. rewrite (restrictv_in _ _ _ (FOOT3 z Hz)). apply mX_in. destruct HQF. lia.
Qed.

Local Notation mR := (maskv (fs_footb G0g) mX).
Lemma present_of_filled : ltac2:(tb__ "0|0|
S21S0S0S0S1aR4R3R2R1A4S1eR5R4R3A3F_;Fb;Fhi;Flo;Fmm;").
Proof. intros mm lo hi b H z Hz. eexists. exact (H z Hz). Qed.

Lemma RI_zero : ltac2:(tb__ "0|1|
S1aS1bS39S32A1S19S10S11VrhoX;A1A2A2SaS36S4bA2M0SaG0Z1000A2Z0A4").
Proof.
  destruct vals as (E30 & _). pose proof safe_sets as (_ & _ & _ & _ & SR & _).
  pose proof VV_RI as Z0.
  assert (EU : U (eval rho1 (SAlu ALU_ADD (SVar 30) (SLit 137438953472))) = SBz + kSpaceSize).
  { rewrite Start7.U_add_slit'; [cbn [eval]; rewrite E30; reflexivity | lia |].
    cbn [eval]. rewrite E30. pose proof (geo_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as (HTOP & HP0 & HSB & _).
    pose proof (SB_range (U P) SBz HSB) as (SBr & _). unfold SBz in *. clear - HTOP HP0 SBr. bands. lia. }
  rewrite EU, Z.add_0_r in Z0. apply filled_safe; [exact Z0 | exact SR].
Qed.
Lemma T_zero : ltac2:(tb__ "0|1|
S1aS1bS39S32A1S19S10S11VrhoX;A1A2A2SaS7Q40Vb5;A2M0Zd0A2SaG0Za80A2Z0A4").
Proof.
  destruct vals as (_ & _ & E33 & _). pose proof safe_sets as (_ & ST & _).
  pose proof (VV_ZEROV 33%positive 208 2688 ltac:(in_small)) as Z0. rewrite E33 in Z0.
  apply filled_safe; [exact Z0 | intros z Hz; apply ST; lia].
Qed.

Theorem primary_X : primary_repr mR A0.
Proof.
  pose proof RI_zero as RZ. pose proof T_zero as TZ.
  unfold primary_repr. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros c Hc.
  assert (EC : nthZ (aa_cls A0) c cs_empty = cs_empty) by (unfold nthZ, A0, A_0; cbn [aa_cls]; apply nth_repeat).
  rewrite EC. pose proof (cap_facts c Hc) as (CS & _ & _ & _ & _ & _ & CF & CQ).
  assert (MU : 0 <= MUCAP c).
  { unfold MUCAP. assert (0 <= Size c * (PRIM_LIVE_MAX + 1 + qmax c + 8)) by (apply Z.mul_nonneg_nonneg; unfold PRIM_LIVE_MAX; lia). unfold kUserMapSize. lia. }
  assert (FA : 0 <= FACAP c).
  { assert (0 <= MUCAP c / Size c) by (apply Z.div_pos; lia). unfold kFreeArrayMapSize in CF. lia. }
  assert (RIc : SBz + kSpaceSize <= region_info SBz c /\ region_info SBz c + kRegionInfoStride <= SBz + kSpaceSize + 4096).
  { unfold region_info, kRegionInfoStride. lia. }
  assert (CZ : forall off wd, 0 <= off -> off + Z.of_nat wd <= kRegionInfoStride -> cell_ok mR (mkACell (region_info SBz c + off) wd 0)).
  { intros off wd O1 O2. apply (cell_zero_of_filled mR _ _ _ wd RZ); lia. }
  assert (QI : q_ids G0g (qall A0) c = []).
  { unfold q_ids, qall, A0, A_0. cbn [aa_q_thread aa_q_global app qitems flat_map List.filter map]. destruct (c =? 24); reflexivity. }
  assert (LI : live_ids G0g A0 c = []) by reflexivity.
  unfold class_repr. cbn zeta. change (aa_geom A0) with G0g. change (ag_spacebeg G0g) with SBz. change (ag_thread G0g) with (U b5).
  cbn [cs_free_array cs_mapped_free_array cs_allocated_user cs_mapped_user cs_cache cs_empty length app]. rewrite QI, LI.
  unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted.
  split; [apply CZ; unfold kRegionInfoStride; cbn; lia|]. split; [apply CZ; unfold kRegionInfoStride; cbn; lia|]. split; [apply CZ; unfold kRegionInfoStride; cbn; lia|].
  split; [apply CZ; unfold kRegionInfoStride; cbn; lia|]. split; [apply CZ; unfold kRegionInfoStride; cbn; lia|]. split; [apply CZ; unfold kRegionInfoStride; cbn; lia|].
  split; [apply CZ; unfold kRegionInfoStride; cbn; lia|]. split; [apply CZ; unfold kRegionInfoStride; cbn; lia|].
  split; [intros z Hz; eexists; apply RZ; lia|].
  split; [reflexivity|]. split; [lia|]. split; [unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize; lia|].
  split; [apply Z.mod_0_l; lia|].
  split; [reflexivity|]. split; [unfold kFreeArraySize; cbn; lia|].
  split; [intros i xx Hi; destruct i; discriminate Hi|].
  split; [intros z Hz; lia|].
  split; [intros xx []|].
  split; [intros z Hz; lia|]. split; [intros z Hz; rewrite Z.add_0_r in Hz; lia|].
  split; [intros z Hz; eexists; apply TZ; lia|].
  split; [constructor|].
  split; [intros b nn []|].
  split; [intros HI; discriminate HI|].
  split; [intros _; split; [reflexivity|]; intros z Hz; apply TZ; lia|].
  split; [lia|].
  split; [unfold slots; cbn [cs_allocated_user cs_empty]; rewrite Z.div_0_l by lia; reflexivity|].
  split; [exact MU | exact FA].
Qed.

Ltac lit0R := apply cell_safe; [apply VV_LIT0; apply acell_inb; vm_compute; reflexivity
                               | intros k Hk; cbn [c_addr c_w] in *; apply (proj1 safe_sets); unfold SEC_INST, QG, NODESMU, STORE in *; lia].
Lemma byte_of_cell1 : ltac2:(tb__ "0|3|
S21S0S1cR2S22R1U1Z0M0A3A2S3S28S8Q8M1A1M2A1R3R2A1S2dG2S9G1G0A2A2A3F_;Fa;Fmm;").
Proof.
  intros mm a H. pose proof (H 0%nat ltac:(cbn; lia)) as X. cbn [c_addr c_w c_val] in X. rewrite Z.add_0_r in X. rewrite X.
  rewrite (enc_lit_byte 1 0 0 ltac:(lia)). reflexivity.
Qed.
Lemma T_present : ltac2:(tb__ "0|1|
S1eS1bS39S32A1S19S10S11VrhoX;A1A2A2S7Q40Vb5;A2M0SaG0Z1000A2A3").
Proof.
  destruct vals as (_ & _ & E33 & _). pose proof safe_sets as (_ & ST & _).
  pose proof (VV_PRESV 33%positive 0 4096 ltac:(in_small)) as P0'. rewrite E33, Z.add_0_r in P0'. apply present_safe; [exact P0' | exact ST].
Qed.
Lemma T_litR : ltac2:(tb__ "0|2|
S0S27S0S3fS2aS2aS2aS1S0A2M0S27A2M1S0A2S25G1S0S25G0S27S25S1S0P21R3A4R2A4R1A4S5cA3SbZ0R4A2SbSaR5SdR4A1A2Z1000A2S1cS1bS39S32A1S19S10S11VrhoX;A1A2A2S22SaS7Q40Vb5;A2R6A2R5R4A3A2F_;F_;F_;Fval;Fwd;Foff;").
Proof.
  intros off wd val Hin O1 O2. destruct vals as (_ & _ & E33 & _). pose proof safe_sets as (_ & ST & _).
  pose proof (VV_LITV 33%positive off wd val Hin) as X. rewrite E33 in X. apply cell_safe; [exact X|]. intros k Hk. cbn [c_addr c_w] in *. apply ST. lia.
Qed.

Theorem secondary_X : secondary_repr mR A0.
Proof.
  destruct vals as (E30 & E32 & _).
  pose proof (geo_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS)
    as (HTOP & HP0 & HSB & HgT & HgC & HgD & HgF & HgPAB & HgN & HgS & HSEP).
  assert (SYM : forall a, In (a, 8%nat, SVar 32) SYM0 -> 0 <= a -> a + 8 <= 0x646000 -> cell_ok mR (mkACell a 8 (U b4))).
  { intros a Hin A0' A1. pose proof (VV_SYM0 a 8%nat (SVar 32) Hin) as X. cbn [eval] in X. rewrite E32 in X.
    apply cell_safe; [exact X|]. intros k Hk. cbn [c_addr c_w] in *. apply (proj1 safe_sets). lia. }
  unfold secondary_repr. cbn zeta. change (aa_geom A0) with G0g. change (ag_pab G0g) with (U b4).
  change (aa_sec A0) with (@nil sec_chunk). change (aa_ptr_committed A0) with 0. cbn [length Z.of_nat].
  rewrite topG0.
  split; [intros i ch Hi; destruct i; discriminate Hi|].
  split; [intros z Hz; lia|].
  split; [unfold kPtrArrayReserve; lia|]. split; [reflexivity|].
  split; [apply grantZ_dyn_ok; [exact HgPAB | unfold kPtrArrayReserve; lia]|].
  split; [lit0R|].
  split; [apply SYM; [in_small | unfold SEC_INST; lia | unfold SEC_INST; lia]|].
  split; [apply SYM; [in_small | unfold SEC_INST; lia | unfold SEC_INST; lia]|].
  split; [lit0R|]. split; [change (0 / 8) with 0; lit0R|]. split; [lit0R|].
  split; [apply present_safe; [apply VV_PRES0; in_small | intros z Hz; apply (proj1 safe_sets); unfold SEC_INST in *; lia]|].
  split; [lit0R|].
  apply present_safe; [apply VV_PRES0; in_small | intros z Hz; apply (proj1 safe_sets); lia].
Qed.

Theorem quarantine_X : quarantine_repr mR A0.
Proof.
  pose proof T_present as TP.
  unfold quarantine_repr. change (aa_q_thread A0) with (@nil qbatch). change (aa_q_global A0) with (@nil qbatch). change (aa_geom A0) with G0g. change (ag_thread G0g) with (U b5).
  cbn [app qlinks]. split; [constructor|]. split; [exact I|]. split; [exact I|].
  split.
  { unfold qhdr_repr. cbn [length Z.of_nat qsize fold_right].
    split; [apply T_litR; [in_small | lia | cbn; lia]|]. split; [intros H; exfalso; apply H; reflexivity|].
    split; [intros z Hz; apply TP; lia|]. rewrite <- Z.add_assoc. apply T_litR; [in_small | lia | cbn; lia]. }
  split.
  { unfold qhdr_repr. cbn [length Z.of_nat qsize fold_right].
    split; [lit0R|]. split; [intros H; exfalso; apply H; reflexivity|].
    split; [apply present_safe; [apply VV_PRES0; in_small | intros z Hz; apply (proj1 safe_sets); unfold QG in *; lia]|]. lit0R. }
  split; [lit0R|]. split; [lit0R|].
  split; [cbn; unfold kQuarantineCacheMax; lia|]. split; [cbn; unfold kQuarantineMax; lia|]. constructor.
Qed.

Theorem ia_X : ia_inv mR A0.
Proof.
  unfold ia_inv. change (aa_internal_inited A0) with false.
  split; [apply byte_of_cell1; lit0R|]. split; [apply byte_of_cell1; lit0R|]. split; [apply byte_of_cell1; lit0R|].
  split; [apply byte_of_cell1; lit0R|].
  apply filled_safe; [exact VV_IA | intros z Hz; apply (proj1 safe_sets); unfold IA_BEG, IA_END in *; lia].
Qed.

Theorem thread_X : thread_inv mR G0g.
Proof.
  pose proof T_present as TP. unfold thread_inv. change (ag_thread G0g) with (U b5).
  split; [apply byte_of_cell1; apply T_litR; [in_small | lia | cbn; lia] | intros z Hz; apply TP; lia].
Qed.

Theorem misc_X : misc_inv mR.
Proof.
  unfold misc_inv. split.
  - unfold cells_ok, rtc_extra. repeat (apply Forall_cons; [lit0R|]). apply Forall_nil.
  - split; apply present_safe; [apply VV_PRES0; in_small | intros z Hz; apply (proj1 safe_sets); lia | apply VV_PRES0; in_small | intros z Hz; apply (proj1 safe_sets); unfold ERRNO_A in *; lia].
Qed.

Variables (tpX : list word) (md : Model).
Hypothesis TX1 : ltac2:(tb__ "0|1|
S8Q40A1M0S3fG0R1S53Vtp;A1A3S3fG0R2VtpX;A3F_;Fp;").
Hypothesis TX2 : ltac2:(tb__ "0|1|
S8Q40A1M0S3fG0R1VtpX;A3S6S3fG0R2S53Vtp;A1A3S5S27S27S2S4fR1Vn;A2S3G0R3S65Vq;R1A2A3A2Lk;A2A2F_;Fp;").
Hypothesis HMD : ltac2:(tb__ "0|0|
S3S45S50Vmd;A1S50S57S55Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10A1A3").

Lemma md_fields : ltac2:(tb__ "0|2|
S2S3S46S43Vmd;A1S43S57S55Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10M0A1A3S3S2bS2aS8Q40A1M1G1A2A1S44Vmd;A1S44G0A1A3A2").
Proof. pose proof (erase_mat_eq_fields md Mm HMD) as (E1 & E2 & _). split; assumption. Qed.
Lemma md_top : ltac2:(tb__ "0|0|
S3S0S47S43Vmd;A1A1S37A3").
Proof.
  destruct md_fields as [E _]. rewrite E.
  exact (proj1 (proj2 (limit_main sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS))).
Qed.
Lemma Lm_in : ltac2:(tb__ "0|5|
S2aS8Q40M0A1M1G1A2M2S6S3fG2R1S26G2S25G1G1Vb14;S9G0Z1000A2M3A4S26G2S25G1G1Vb13;S9G0Z800000A2A4S26G2S25G1G1Vb12;S9G0Z100000A2A4S2fG2A1M4A3A3A3A3S3fG2R1S26G2S25G1G1Vb10;S9G0S63A2A4S26G2S25G1G1Vb8;G3A4S26G2S25G1G1Vb7;G3A4S26G2S25G1G1Vb6;S9G0Z10000A2A4S26G2S25G1G1Vb5;G3A4S26G2S25G1G1Vb4;S61A4S26G2S25G1G1VP;S60A4G4A3A3A3A3A3A3A3A3A2S3fG2R2S48S43Vmd;A1A1A3F_;Fe;").
Proof.
  intros e He. destruct md_fields as [E _]. rewrite E.
  rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (Mm_fds sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS)))))).
  rewrite (Lmain_explicit sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS).
  destruct He as [He|He]; [apply in_or_app; left; exact He|]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact He.
Qed.

Theorem depot_X : ltac2:(tb__ "0|1|
S6fS10S6dS7Q40M0Vb12;A2S7G0Vb13;A2S5bVv;A1A3VrhoX;Vmd;VtpX;A5").
Proof.
  destruct vals as (E30 & E32 & E33 & E34 & E77 & E83 & E159 & E160).
  pose proof safe_sets as (SI & ST & SC & SD & SR & SN & SS).
  pose proof (geo_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS)
    as (HTOP & HP0 & HSB & HgT & HgC & HgD & HgF & HgPAB & HgN & HgS & HSEP).
  pose proof (seps (U P) (U b5) (U b6) (U b8) (U b10) (U b4) (U b12) (U b13) HSEP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S28).
  destruct VV_DEPOT as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  destruct (ss0_lazy_acc sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as (LZ & ACC).
  destruct md_fields as [EV ELZ]. pose proof md_top as MT.
  assert (IMGc : forall c, cell_ok m c -> 0 <= c_addr c -> c_addr c + Z.of_nat (c_w c) <= 0x646000 -> cell_ok mX c).
  { intros c Hc C1 C2. apply cell_X; [exact Hc|]. intros k Hk. apply safe_nband, SI. lia. }
  assert (IMGf : forall lo hi, filled m lo hi 0 -> 0 <= lo -> hi <= 0x646000 -> filled mX lo hi 0).
  { intros lo hi H C1 C2. apply filled_X; [exact H|]. intros z Hz. apply safe_nband, SI. lia. }
  assert (IMGp : forall lo hi, present m lo hi -> 0 <= lo -> hi <= 0x646000 -> present mX lo hi).
  { intros lo hi H C1 C2. apply present_X; [exact H|]. intros z Hz. apply safe_nband, SI. lia. }
  assert (BK : 0x1d32d8 <= bkV v /\ bkV v + 4 <= 0x1d32d8 + 4 * 1048576 /\ (bkV v - 0x1d32d8) mod 4 = 0) by (unfold bkV; destruct v; repeat split; lia || reflexivity).
  destruct BK as (B1 & B2 & B3).
  unfold grantZ in HgN, HgS. unfold PG, NBSZ, FBSZ, IMG_LO, IMG_HI in *.
  apply (depot_inv_G0_intro segsA (U b12) (U b13) (f0V v) rhoX md tpX).
  - unfold f0V. destruct v; lia.
  -   apply IMGc; [|unfold NIDS; cbn; lia | unfold NIDS; cbn; lia].
    pose proof (VV_SYM0 NIDS 4%nat (SAlu ALU_ADD (SLit 0) (SLit 1)) ltac:(in_small)) as X.
    replace (U (eval rho1 (SAlu ALU_ADD (SLit 0) (SLit 1)))) with 1 in X by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). exact X.
  - apply IMGc; [exact D1 | unfold STORE; cbn; lia | unfold STORE; cbn; lia].
  - apply IMGc; [apply VV_LIT0; apply acell_inb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | unfold NODESMU; cbn; lia | unfold NODESMU; cbn; lia].
  - apply IMGp; [exact D7 | unfold STORE; lia | unfold STORE; lia].
  -
    intros i Hi. destruct (Z.eq_dec (DEPOT + 4 * i) (bkV v)) as [Eb|Nb].
    + exists 1. split; [|right; reflexivity]. unfold cellZ. rewrite Eb. apply IMGc; [exact D2 | cbn; clear - B1; lia | cbn; clear - B2; lia].
    + exists 0. split; [|left; reflexivity]. unfold cellZ.
      apply Z.mod_divide in B3 as [kk Hk]; [|lia]. unfold DEPOT, TABSZ in *.
      destruct (Z_lt_dec (1913560 + 4 * i) (bkV v)) as [Lt|Ge].
      * apply (cell_zero_of_filled mX 1913560 (bkV v)); [apply IMGf; [exact D3 | lia | clear - B2; lia] | clear - Hi; lia | cbn; clear - Lt Hk; lia].
      * apply (cell_zero_of_filled mX (bkV v + 4) (1913560 + 4 * 1048576)); [apply IMGf; [exact D4 | clear - B1; lia | lia] | clear - Ge Nb Hk; lia | cbn; clear - Hi; lia].
  -
    pose proof (VV_SYM0 0x5d32e8 8%nat (SVar 159) ltac:(in_small)) as X. cbn [eval] in X. rewrite E159 in X.
    apply IMGc; [exact X | unfold MAP1, STORE; cbn; lia | unfold MAP1, STORE; cbn; lia].
  - intros j Hj. apply (cell_zero_of_filled mX (MAP1 + 8) (MAP1 + 8 * MAP1N)); [apply IMGf; [exact D5 | unfold MAP1; lia | unfold MAP1, MAP1N; lia] | unfold MAP1 in *; lia | unfold MAP1, MAP1N in *; cbn; lia].
  - exact (proj1 HgN).
  - unfold IMG_HI. clear - HgN. lia.
  - rewrite MT. unfold NBSZ, TOPz. clear - HgN. lia.
  - pose proof (VV_PRESV 159%positive 0 1048576 ltac:(in_small)) as X. rewrite E159, Z.add_0_r in X. apply present_X; [exact X | intros z Hz; apply safe_nband, SN; exact Hz].
  - destruct VV_HASH as [h Hh]. rewrite E159 in Hh. exists h. apply cell_X; [exact Hh | intros k Hk; cbn [c_addr c_w] in *; apply safe_nband, SN; lia].
  - pose proof (VV_LITV 159%positive 24 4%nat 0 ltac:(in_small)) as X. rewrite E159 in X. apply cell_X; [exact X | intros k Hk; cbn [c_addr c_w] in *; apply safe_nband, SN; lia].
  - pose proof (VV_SYM0 0x1c32d8 8%nat (SVar 160) ltac:(in_small)) as X. cbn [eval] in X. rewrite E160 in X.
    apply IMGc; [exact X | unfold MAP1, STORE; cbn; lia | unfold MAP1, STORE; cbn; lia].
  - clear - HgS. lia.
  - apply IMGp; [exact D8 | unfold STORE; lia | unfold STORE; lia].
  - apply IMGc; [apply VV_LIT0; apply acell_inb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | unfold STORE; cbn; lia | unfold STORE; cbn; lia].
  - intros b Hb. intros z Hz. apply (IMGf (STORE + 32) (STORE + 16 + 16 * NFBLK) D6); [unfold STORE; lia | unfold STORE, NFBLK; lia | unfold NFBLK in *; lia].
  - exact (proj1 HgS).
  - unfold IMG_HI. clear - HgS. lia.
  - rewrite MT. unfold FBSZ, TOPz. clear - HgS. lia.
  - pose proof (VV_PRESV 160%positive 0 4096 ltac:(in_small)) as X. rewrite E160, Z.add_0_r in X. apply present_X; [exact X | intros z Hz; apply safe_nband, SS; unfold PG in Hz; lia].
  - clear - S28. unfold sepZ in S28. cbn [fst snd] in S28. unfold NBSZ, FBSZ in *. lia.
  - rewrite MT. exact HTOP.
  - apply Lm_in. left. rewrite Z_to_bv_bv_unsigned. in_small.
  - apply Lm_in. left. rewrite Z_to_bv_bv_unsigned. in_small.
  - rewrite ELZ, Z_to_bv_bv_unsigned. exact LZ.
  - intros j Hj. rewrite EV. apply ACC. unfold FBSZ in Hj. clear - Hj. lia.
  -
    intros k Hk. unfold FBPAGES in Hk. change PG with 4096. split.
    + intros Hin. destruct (Z.eq_dec k 0) as [|NE]; [assumption|exfalso].
      assert (UP : U (Z_to_bv 64 (U b13 + 4096 * k)) = U b13 + 4096 * k) by (apply u64_of_lit; clear - HgS HTOP Hk; lia).
      destruct (TX2 _ Hin) as [Ht|(kk & Hkk & Ek)].
      * destruct (tpF_pages sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS _ Ht) as [Zp|[Ep|[Ep|[Ep|Bp]]]].
        -- rewrite UP in Zp. unfold ZPAGES, PA0, PR0 in Zp. clear - Zp HgS Hk. bands. lia.
        -- apply (f_equal U) in Ep. rewrite UP in Ep. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs.PGB in Ep. rewrite u64_of_lit in Ep by lia. clear - Ep HgS Hk. bands. lia.
        -- apply (f_equal U) in Ep. rewrite UP in Ep. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs.PGA in Ep. rewrite u64_of_lit in Ep by lia. clear - Ep HgS Hk. bands. lia.
        -- apply (f_equal U) in Ep. rewrite UP in Ep. clear - Ep NE. lia.
        -- rewrite UP in Bp. clear - Bp HgS Hk. bands. lia.
      * apply (f_equal U) in Ek. rewrite UP in Ek. unfold pageZ in Ek. rewrite u64_of_lit in Ek by (destruct HQB; clear - H H0 Hkk; bands; lia).
        destruct HQB as [Q1 Q2]. clear - Ek HgS Hk Q1 Q2 Hkk. bands. lia.
    + intros ->. apply TX1. rewrite Z.mul_0_r, Z.add_0_r, Z_to_bv_bv_unsigned.
      pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Etp & _).
      unfold tpF. apply in_or_app. right. apply in_or_app. right. rewrite Etp. unfold TPmain. right. right. left. reflexivity.
Qed.

Theorem rest_X : rest_inv mR A0.
Proof.
  unfold rest_inv.
  split; [intros b nn []|]. split; [intros b nn []|].
  split; [exact primary_X|]. split; [exact secondary_X|]. split; [exact quarantine_X|].
  split.
  {
    unfold depot_wf. change (aa_depot A0) with (G0 (U b12) (U b13) (f0V v)).
    pose proof safe_sets as (SI & _ & _ & _ & _ & SN & SS).
    apply (depot_mem_frame _ mX); [|exact (proj1 depot_X)].
    intros a [Hs|[(b & Hb & Ha)|(b & Hb & Ha)]].
    - assert (Sa : safe a) by (apply SI; unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs; lia).
      rewrite (maskv_out _ _ _ (fs_foot_safe a Sa)). reflexivity.
    - cbn [dNB G0 In] in Hb. destruct Hb as [<-|[]]. rewrite (maskv_out _ _ _ (fs_foot_safe a (SN a Ha))). reflexivity.
    - cbn [dFB G0 In] in Hb. destruct Hb as [<-|[]]. rewrite (maskv_out _ _ _ (fs_foot_safe a (SS a Ha))). reflexivity. }
  split; [exact ia_X|]. split; [exact thread_X | exact misc_X].
Qed.

Hypothesis HPAID : ltac2:(tb__ "0|0|
SbS67Vmd;VtpX;A2SaSaS58S56A1Z4000A2SeZ1000Z162A2A2A2").
Hypothesis Hlim : lim = LIMIT.

Theorem model_X : ltac2:(tb__ "0|0|
S3eS10S35VtpX;Vmd;A4").
Proof.
  pose proof HS as (Sfds & Sfs & Slim & SMI & _).
  destruct md_fields as [EV ELZ]. pose proof md_top as MT.
  pose proof (geo_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS)
    as (HTOP & HP0 & HSB & HgT & HgC & HgD & HgF & HgPAB & HgN & HgS & HSEP).
  pose proof (SB_range (U P) SBz HSB) as (SBr & _).
  assert (KS : kSpaceSize = 0x2000000000) by reflexivity.
  assert (INM : forall (b : word) (s : Z) lo hi, In (b, Z_to_bv 64 s) (vm_maps (m_vmmaps md)) -> 0 <= s < 2 ^ 64 -> U b <= lo -> hi <= U b + s -> in_maps (m_vmmaps md) lo hi).
  { intros b s lo hi Hin Hs H1 H2. exists (b, Z_to_bv 64 s). split; [exact Hin|]. cbn [fst snd]. rewrite u64_of_lit by lia. lia. }
  unfold model_inv. change (aa_geom A0) with G0g. change (aa_V A0) with 0. change (aa_Km A0) with 0. change (aa_Kf A0) with 0.
  split.
  {
    unfold vm_geom. cbn zeta. change (aa_geom A0) with G0g. change (aa_sec A0) with (@nil sec_chunk).
    change (ag_spacebeg G0g) with SBz. change (ag_thread G0g) with (U b5). change (ag_ctx G0g) with (U b6). change (ag_dtls G0g) with (U b8).
    change (ag_fsb G0g) with (U b10). change (ag_pab G0g) with (U b4).
    split.
    { intros e xx He Hx. rewrite EV in He |- *. destruct e as [eb es]. cbn [fst snd] in Hx.
      assert (C : covered (vm_noaccess (m_vmmaps Mm)) xx = true).
      { unfold covered. apply existsb_exists. exists (eb, es). split; [exact He|]. unfold in_iv, in_rng, ivB, ivS. cbn [fst snd].
        apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      destruct (mi_namaps SMI xx C) as (b & s & Hin & Hr). exists (b, s). split; [rewrite (mi_maps SMI); exact Hin | exact Hr]. }
    split; [apply (INM P 0x2000011000); [apply Lm_in; right; unfold n7; in_small | lia | lia | lia]|].
    split; [apply (INM b5 4096); [apply Lm_in; right; in_small | lia | lia | lia]|].
    split; [apply (INM b6 65536); [apply Lm_in; right; in_small | lia | lia | lia]|].
    split; [apply (INM b8 4096); [apply Lm_in; right; in_small | lia | lia | lia]|].
    split; [apply (INM b10 n17); [apply Lm_in; right; in_small | unfold n17; lia | lia | rewrite FS_total_val; unfold n17; lia]|].
    split; [apply (INM b4 0x800000); [apply Lm_in; right; unfold n9; in_small | lia | lia | unfold kPtrArrayReserve; lia]|].
    split; [intros ch []|].
    intros p Hal Hb. rewrite ELZ, EV.
    destruct Hb as [[B1 B2]|[B1 B2]].
    - split; [apply (mi_lzlow SMI); unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, Placement.SHADOW_BAND_LO, Placement.SHADOW_RW_LO_END, PG in *; lia|].
      intros j Hj. apply (mi_acclow SMI). unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, Placement.SHADOW_BAND_LO, Placement.SHADOW_RW_LO_END, PG in *. lia.
    - split; [apply (HBL_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS);
               unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, Placement.SHADOW_BAND_HI, PG in *; lia|].
      intros j Hj. apply (mi_acchigh SMI). unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, Placement.SHADOW_BAND_HI, Placement.SHADOW_RW_HI_BEG, PG in *. lia. }
  split.
  {
    assert (PC : prim_credit A0 = PRIM0) by (apply prim_credit_init; intros c Hc; unfold A0, A_0; cbn [aa_cls]; apply nth_repeat).
    rewrite PC. pose proof QPRIM_ok as QP. pose proof StartHandoff.Bmain_val as BV.
    unfold budget_boundD. change (aa_V A0) with 0. change (aa_Km A0) with 0. change (aa_Kf A0) with 0. change (aa_ptr_committed A0) with 0.
    change (aa_depot A0) with (G0 (U b12) (U b13) (f0V v)).
    assert (DC : dep_cost (G0 (U b12) (U b13) (f0V v)) = NBSZ + PG) by reflexivity. rewrite DC. unfold NBSZ.
    assert (AC : acost 0 = 0) by reflexivity. rewrite AC.
    unfold Q1, QPIECES, Budget.U0 in *. unfold kUserMapSize, PG in *. lia. }
  split; [rewrite EV, Slim; exact Hlim|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [rewrite MT; reflexivity|].

  unfold ledger_inv. cbn zeta.
  split; [rewrite EV; exact (mi_res SMI)|].
  split.
  { rewrite EV. intros xx Hx. destruct (mi_band SMI xx Hx) as (b & s & Hin & Hr). exists b, s. split; [|exact Hr].
    apply in_app_or in Hin as [Hin|Hin]; [|rewrite (mi_maps SMI); exact Hin]. exfalso.
    rewrite StartLib.segments_reserved_A in Hin. unfold Placement.SHADOW_BAND_LO in Hx.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite !u64_of_lit in Hr by lia; lia|]). destruct Hin. }
  split; [rewrite EV; exact (maps_disjoint_main sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS)|].
  split.
  {
    pose proof (hwN_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as HN.
    pose proof (hwS_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as HSs.
    unfold gap_ok, gapN_ok, gapS_ok, blocks_left. rewrite EV. change (aa_V A0) with 0. change (aa_depot A0) with (G0 (U b12) (U b13) (f0V v)).
    cbn [dNB dFB G0 length Z.of_nat]. unfold NLIM, SLIM, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger.N0, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger.S0, NBMAX, FBMAX, GN, NBSZ, FBSZ.
    pose proof (Z.div_mod VCAP 64513 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound VCAP 64513 ltac:(lia)) as MB.
    split; lia. }
  split; [exact (proj2 depot_X)|].
  split; [cbn; lia|]. split; [change (aa_ptr_committed A0) with 0; change (aa_Km A0) with 0; unfold kPtrArrayCommit; lia|].
  split.
  {
    rewrite EV.
    pose proof (Mm_fds sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as (_ & _ & _ & _ & _ & EM).
    pose proof (Lmain_explicit sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as EL.
    pose proof (X18_small sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as (_ & _ & X18).
    rewrite EM, EL. split; [|split].
    - intros b s Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply in_app_or in Hin as [Hin|Hin]; [|apply in_app_or in Hin as [Hin|Hin]]].
      + cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rewrite u64_of_lit by lia; lia|]). destruct Hin.
      + destruct (X18 b s Hin) as ([E|E] & _); rewrite E; lia.
      + cbn [In] in Hin. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.n9, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.n7, Start6.n17 in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rewrite u64_of_lit by lia; lia|]). destruct Hin.
      + cbn [In] in Hin. unfold StartTop.HSe, StartTop.GPe, StartTop.LWe in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rewrite u64_of_lit by lia; lia|]). destruct Hin.
    - unfold in_maps. exists StartTop.LWe. rewrite EM, EL. split; [apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; cbn; tauto|]. unfold StartTop.LWe. cbn [fst snd]. rewrite !u64_of_lit by lia. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG. lia.
    - unfold in_maps. exists StartTop.HSe. rewrite EM, EL. split; [apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; cbn; tauto|]. unfold StartTop.HSe. cbn [fst snd]. rewrite !u64_of_lit by lia. unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END. lia. }
  split; [cbn; lia|].
  rewrite EV. exact (noaccess_pos_main sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS).
Qed.

Theorem bandtp_X : bandtp_inv mX tpX.
Proof.
  intros p Hp Hb z Hz. unfold PG in Hz.
  destruct (Z_le_dec q z) as [Q1|Q1]; [destruct (Z_lt_dec z (q + 4096 * Z.of_nat n)) as [Q2|Q2]|].
  - apply mX_in. lia.
  - rewrite mX_out by lia. destruct (TX2 p Hp) as [Ht|(k & Hk & Ek)].
    + pose proof (tpF_defined sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS p Ht Hb z Hz) as D.
      assert (R : 0 <= z < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 p) as R; change (bv_modulus 64) with (2 ^ 64) in R; clear - Hb Hz R; unfold Inv.band_page, StartHandoffFacts.band_page, PG in Hb; bands; unfold SHADOW_GAP_BEG, HIGH_SHADOW_BEG in *; lia).
      rewrite (view_in segsA) by exact R. unfold rd_of. destruct (rm rhoM (Z_to_bv 64 z)) as [b|]; [exists b; reflexivity | contradiction].
    + exfalso. apply (f_equal U) in Ek. unfold pageZ in Ek. rewrite u64_of_lit in Ek by (destruct HQB; clear - H H0 Hk; bands; lia).
      clear - Ek Hz Q1 Q2 Hk. lia.
  - rewrite mX_out by lia. destruct (TX2 p Hp) as [Ht|(k & Hk & Ek)].
    + pose proof (tpF_defined sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS p Ht Hb z Hz) as D.
      assert (R : 0 <= z < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 p) as R; change (bv_modulus 64) with (2 ^ 64) in R; clear - Hb Hz R; unfold Inv.band_page, StartHandoffFacts.band_page, PG in Hb; bands; unfold SHADOW_GAP_BEG, HIGH_SHADOW_BEG in *; lia).
      rewrite (view_in segsA) by exact R. unfold rd_of. destruct (rm rhoM (Z_to_bv 64 z)) as [b|]; [exists b; reflexivity | contradiction].
    + exfalso. apply (f_equal U) in Ek. unfold pageZ in Ek. rewrite u64_of_lit in Ek by (destruct HQB; clear - H H0 Hk; bands; lia).
      clear - Ek Hz Q1 Hk. lia.
Qed.

Theorem AInvA_X : ltac2:(tb__ "0|0|
S3aS10S35VrhoX;VtpX;Vmd;A5").
Proof.
  unfold AInvA. cbn zeta. change (aa_geom A0) with G0g.
  split; [exact (proj1 geo)|]. split; [exact rtc_X|]. split; [exact fs_X|]. split; [exact rest_X|].
  split; [exact model_X|]. split; [exact (proj2 geo) | exact bandtp_X].
Qed.
End Facts.
End InvInitA.

