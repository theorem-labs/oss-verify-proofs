(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "nil"; "cons"; "list"; "prod"; "true"; "Some"; "bool"; "option"; "pair"; "app"; "@Corelib.Init.Logic"; "eq"; "ex"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sv"; "agree_below"; "SLit"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "ax_S"; "sym_runA"; "axst"; "mkAX"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "event"; "Model"; "vm_init_sp"; "vm_maps"; "vm_reserved"; "vm_limit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "LQA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States"; "E_s3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start3.Seg3"; "n6"; "Post3"; "m6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start3States"; "SPIN6"; "E_k7"; "S_s3x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start3"; "SPIN_MMAPORDIE"; "S_s3fail"; "ECALL_MMAP"; "FUEL3"; "G3"; "G3l"; "HMCUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "RsSymJump"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "cfg1_okA"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes"; "eager_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib KxA Placement PlacementA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start3States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ECALL_MMAP : Z := 0x706a0.
Definition HMCUT : Z := 0x71554.
Definition SPIN_MMAPORDIE : Z := 0x6bf18.

Lemma S_s3x_eq : S_s3x = eager_ok E_s3 0x38e000 29%positive.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition S_s3fail : axst := ltac2:(tb__ "0|0|
S1fS4cS1cS2cA1S4dA2S1S4S16S16A2A1S18S48A1A3").
Lemma runF_s3 : ltac2:(tb__ "0|1|
SbS8S3S1aA1M0A1S1dS0U190S2SfS3aS1SfA1A3S3bS5A5S6G0S2S1aS1bS30S42A2S1S1aA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin6 : ltac2:(tb__ "0|1|
SbS8S3S1aA1M0A1S1dS0U2S2SfS3aS1SfA1A3S30S5A5S6G0S2S1aS1bS30S42A2S1S1aA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition FUEL3 : nat := (160 * 1000)%nat.
Definition G3 : positive := 29%positive.
Lemma check3 : ltac2:(tb__ "0|0|
SbS7S49S3dS2SfS40S2SfS3cS1SfA1A3A3S3eS32S31A5S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition G3l : list (sv * Z) := ltac2:(tb__ "0|1|
S2S4S16SfA2M0S9S16SfS19P1bA1Z10000A4S1G0A1A3").

Section Seg3.
Variables (m : Model) (a1 : word) (B : Z).
Hypothesis Hres : ltac2:(tb__ "0|1|
SbS3S4S11Q40A1M0G0A2A1S25S20Vm;A1A1S44S0A1A3").
Hypothesis Ha1 : ltac2:(tb__ "0|2|
S4fS4S11Q40M0A1M1G1A2S9G1G1Va1;S13G0Z10000A2A4S24S20Vm;A1A1A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
S47SaS4S11Q40A1M0G0A2S25S20Vm;A1M1A1S24G1A1A3S46S45A3").
Hypothesis HBlim : ltac2:(tb__ "0|0|
S39S38VB;Z38e000A2S26S20Vm;A1A1A2").

Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S28S14S3S11Q40A1A1S3S21A1M0S22R5R4R3R2R1A4SbG0R3S1S21A1A3F_;Fmd;Ftr;Ftp;Frho;S29S0Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S28S14S3S11Q40A1A1S3S21A1M0S22R5R4R3R2R1A4SbG0R3S1S21A1A3F_;Fmd;Ftr;Ftp;Frho;S4eS0Vok;R2A3F_;FJ;").

Definition n6 : word := Z_to_bv 64 0x38e000.
Definition m6 (a : word) : Model := eager_model 0x38e000 m a.

Definition Post3 (rho : valuation) : assn := ltac2:(tb__ "0|2|
S33ScS11Q40M0A1M1G1ScS14S14SdS37S13G0Z0A2Vm;S2dR2A4SdS17P1dS41Vrho;P1cR2A3R1A3S27S0S2bS2fR2A1S38VB;Z38e000A2A2S31R1S1G1A1R3A6A2A2Lrho';A2La;A2Lw;").

Lemma OKFx : ltac2:(tb__ "0|0|
S22SfS29S0Vok;S2bR2R1A2A3FBB;Fmm;").
Proof using OKF. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.

Lemma clear_s3 : ltac2:(tb__ "0|0|
SbS7S4aS3fS1cS2cA1A2S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma node_s3 : ltac2:(tb__ "0|5|
S14SbS11Q40M0A1M1S15R1P1bA2Va1;A3SbSfS12G0S15R2P1A2A2S12G0S23S20Vm;A1A1A2A3S36S0Vok;S27S0S2bVm;VB;A2M2S2cR3S1G1A1M3A5S33SeS27S0G2S3bR4G3R1A6ScG1G1SdS37S13G0Z0A2Vm;S2dR1A4S27S0S2bS2fR1A1S38VB;Z38e000M4A2A2S4bS2cG4P1dA3S41R5P1cR1A3G3R2A6A2La;A2A2Lw;A4F_;F_;Frho;").
Proof using HBlim Hband Hres Htop Ha1 OKF OKP.
  intros rho H27 Hv1.
  apply (eager_rw_node ok OKF OKP E_s3 0x38e000 m B G3l 29%positive);
    [ reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | reflexivity | reflexivity | lia | cbv; reflexivity
    | exact clear_s3 | exact Hres | exact Htop | exact Hband | exact HBlim
    | intros e sz [[= <- <-]|[]]; left; exists a1, (Z_to_bv 64 0x10000); split; [exact Ha1|]; cbn [eval]; rewrite H27, u64_of_lit by lia; lia
    | exact Hv1 ].
Qed.

Lemma LQA1_SPA : ltac2:(tb__ "0|1|
S28S10S14S1eS33S2aS0R5R4R3S1S11Q40A1A1M0S2S1aS1bR2S43A2S1S1aA1A3R1A7ScS14S14SdS17R6R5R1A3S27S0R7R4R1G0R3A6A2Lrho';A2F_;Fw;FE;Frho;Fn;FJ;").
Proof. intros J n rho E w (L & rho' & [<-|[]] & Hag & Hsm & Hk). exists rho'. split; [exact Hag | split; [exact Hsm | exact Hk]]. Qed.

Theorem start3_sum_A : ltac2:(tb__ "0|2|
S14SbS11Q40M0A1M1S15R1P1bA2Va1;A3SbSfS12G0S15R2P1A2A2S12G0S23S20Vm;A1A1A2A3S35S0Vok;S27S0S2bVm;VB;A2S2cR3S1G1A1A5S2eR3A1A4F_;F_;Frho;").
Proof using HBlim Hband Hres Htop Ha1 OKF OKP.
  intros rho H27 Hv1.
  eapply triple_seq; [apply triple1_triple; apply (node_s3 rho H27 Hv1)|].
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA m B) (OKFx _ _) (fun n => stableA_KxA segsA n m B) S_s3fail SPIN6 400%nat SPIN_MMAPORDIE);
      [ reflexivity | reflexivity | reflexivity | exact runF_s3 | exact spin6 ].
  - apply triple_ex; intros a. apply triple_pure; intros Hpl.
    set (rho' := rho_set_rw rho 28%positive a). set (J6 := KxA (m6 a) (B + 0x38e000)).
    change (eager_model 0x38e000 m a) with (m6 a). change (KxA (m6 a) (B + 0x38e000)) with J6. rewrite <- S_s3x_eq.
    eapply triple_conseq; [intros w Hw; exact Hw | | apply (run_cfg1 ok J6 FUEL3 [HMCUT; ECALL_MMAP] G3 S_s3x E_k7 _ [] (OKFx _ _) (fun n => stableA_KxA segsA n _ _) check3)].
    intros w Hw. destruct (LQA1_SPA J6 G3 rho' E_k7 w Hw) as (rho3 & Hag3 & Hsp3).
    exists a, rho3. split; [exact Hpl|]. split; [exact Hag3 | exact Hsp3].
Qed.

Hypothesis Hwit : ltac2:(tb__ "0|2|
ScS11Q40M0A1M1G1S37S13G0Z0A2Vm;S2dR1A4La;A2").

Theorem start3_sum_ex_A : ltac2:(tb__ "0|2|
S14SbS11Q40M0A1M1S15R1P1bA2Va1;A3SbSfS12G0S15R2P1A2A2S12G0S23S20Vm;A1A1A2A3S34S0S27S0S2bVm;VB;A2S2cR3S1G1A1A5S2eR3A1A3F_;F_;Frho;").
Proof using HBlim Hband Hres Htop Ha1 Hwit.
  intros rho H27 Hv1.
  eapply etriple_seq.
  { apply (eager_rw_enode E_s3 0x38e000 m B G3l 29%positive);
      [ reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | reflexivity | reflexivity | lia | cbv; reflexivity
      | exact clear_s3 | exact Hres | exact Htop | exact Hband | exact HBlim | exact Hwit
      | intros e sz [[= <- <-]|[]]; left; exists a1, (Z_to_bv 64 0x10000); split; [exact Ha1|]; cbn [eval]; rewrite H27, u64_of_lit by lia; lia
      | exact Hv1 ]. }
  apply etriple_ex; intros a. intros w [Hpl Hsp]. revert w Hsp.
  set (rho' := rho_set_rw rho 28%positive a). set (J6 := KxA (m6 a) (B + 0x38e000)).
  change (eager_model 0x38e000 m a) with (m6 a). change (KxA (m6 a) (B + 0x38e000)) with J6. rewrite <- S_s3x_eq.
  change (etriple segsA (SPA segsA J6 S_s3x rho' []) (Post3 rho)).
  eapply etriple_conseq; [intros w Hw; exact Hw | | apply (erun_cfg1 J6 FUEL3 [HMCUT; ECALL_MMAP] G3 S_s3x E_k7 _ [] (fun n => stableA_KxA segsA n _ _) check3)].
  intros w Hw. destruct (LQA1_SPA J6 G3 rho' E_k7 w Hw) as (rho3 & Hag3 & Hsp3).
  exists a, rho3. split; [exact Hpl|]. split; [exact Hag3 | exact Hsp3].
Qed.
End Seg3.
