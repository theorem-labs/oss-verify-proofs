(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "nil"; "cons"; "list"; "prod"; "true"; "bool"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Logic"; "eq"; "ex"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "SLit"; "sprop"; "rw"; "SAlu"; "agree_below"; "holds"; "SPBranch"; "SPNot"; "SVar"; "ss_facts"; "swf"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "LQA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start1States"; "E_s2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "mkLeafA"; "axst"; "sym_runA"; "mkAX"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "event"; "Model"; "vm_init_sp"; "vm_reserved"; "vm_limit"; "vm_maps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start2States"; "S_hm2"; "SPIN5"; "S_s2x"; "T_hm2"; "E_s3"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start2.Seg2"; "n5"; "Post2"; "m5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes"; "eager_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "@Stdlib.ZArith.BinInt.Z"; "add"; "modulo"; "le"; "pow"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_OR"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start2"; "ECALL_MMAP"; "FUEL2"; "G2"; "HMCUT"; "MF2"; "SPIN_MMAPORDIE"; "S_s2fail"; "sd_hm2"; "Xhm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "cfg1_okA"; "SHB"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "RsSymJump"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.Riscv.Prelude"; "bv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHm"; "smear_sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartLib KxA Placement PlacementA SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartHm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start1States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start2States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ECALL_MMAP : Z := 0x7050c.
Definition SPIN_MMAPORDIE : Z := 0x6bd84.

Definition MF2 : sprop := ltac2:(tb__ "0|0|
S1bS1aS4cS17S4aS17S4bS14Z120A1S17S49S1cP1A1S14N248A1A3A3S14ZfA1A3S14Z0A1A3A1").

Lemma S_s2x_eq : ltac2:(tb__ "0|0|
SeS2aS3bS66S3S15S51S2S15A1A3S42S26Z10000P1cA3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition S_s2fail : axst := ltac2:(tb__ "0|0|
S2cS64S28S26A1S65A2S2S5S13S13A2A1S14S57A1A3").
Lemma runF_s2 : ltac2:(tb__ "0|1|
SeS9S4S27A1M0A1S2bSdU190S3S0S52S2S0A1A3S53S6A5S8G0S3S27S29S3aS5aA2S2S27A1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin5 : ltac2:(tb__ "0|1|
SeS9S4S27A1M0A1S2bSdU2S3S0S52S2S0A1A3S3aS6A5S8G0S3S27S29S3aS5aA2S2S27A1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition HMCUT : Z := 0x713c0.
Definition FUEL2 : nat := (70 * 1000)%nat.
Definition G2 : positive := 28%positive.
Lemma check2a : ltac2:(tb__ "0|0|
SeS7S56S4eS3S0S50S3S0S4dS2S0A1A3A3S4fS3bS3cA5S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma check2b : ltac2:(tb__ "0|0|
SeS7S56S4eS3S0S50S3S0S4dS2S0A1A3A3S4fS39S3dA5S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition Xhm : sv := SAlu ALU_ADD (SVar 1%positive) (SLit (-160)).
Definition sd_hm2 := Eval vm_compute in (match state_diff (ax_S T_hm2) (ax_S S_hm2) with Some p => p | None => ([], []) end).
Lemma sd_hm2_eq : ltac2:(tb__ "0|1|
SeS9S5S4S5S13S13A2A1S4S15A1A2M0A1S63S28S3cA1S28S39A1A2S8G0S54A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd_hm2_shape : ltac2:(tb__ "0|5|
SeS5S4S5S13S13A2M0A1M1S4S15A1M2A2S54SaG1G2S3G0SaS13S13S62S55S3S0Z1M3S3S0Z2M4S3S0Z4S3S0Z8S3S0Z10S3S0Z20S2S0A1A3A3A3A3A3A3A2S14S48S47G4Z2fA2G3A2A1A4S2G0A1A3S2S15A1A4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma swf_S_hm2 : ltac2:(tb__ "0|0|
SeS7S1eS28S39A1A1S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma restate_hm2 : ltac2:(tb__ "0|1|
S23S12S35S22SdR3S3cR2S2S1fQ40A1A1M0R1A6S22SdR4S39R3G0R2A6F_;Fw;Frho;FJ;").
Proof.
  intros J rho w Hsp.
  pose proof (SPA_facts_hold segsA J rho T_hm2 [] w Hsp) as HF.
  assert (Hv1 : 0x7fff80000000 <= bv_unsigned (rw rho 1%positive) <= 0x7fffffffff20).
  { assert (X1 : In (SPUle (SLit 140735340871680) (SVar 1%positive)) (ss_facts (ax_S T_hm2))) by (vm_compute; tauto).
    assert (X2 : In (SPUle (SVar 1%positive) (SLit 140737488355104)) (ss_facts (ax_S T_hm2))) by (vm_compute; tauto).
    pose proof (proj1 (Forall_forall _ _) HF _ X1) as Y1. pose proof (proj1 (Forall_forall _ _) HF _ X2) as Y2.
    cbn [holds eval] in Y1, Y2. rewrite Z_to_bv_unsigned in Y1, Y2.
    change (bv_wrap 64 140735340871680) with 140735340871680 in Y1. change (bv_wrap 64 140737488355104) with 140737488355104 in Y2. lia. }
  change S_hm2 with (ax_setS T_hm2 (ax_S S_hm2)).
  apply (SPA_restate segsA J rho T_hm2 (ax_S S_hm2) [] w (fst sd_hm2) (snd sd_hm2)); [exact swf_S_hm2 | rewrite sd_hm2_eq; destruct sd_hm2; reflexivity | reflexivity | | | exact Hsp].
  - rewrite sd_hm2_shape. cbn [fst]. unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    cbn [eval]. apply eval_smear_sv_47. unfold Xhm. cbn [eval]. rewrite add_val, Z_to_bv_unsigned.
    change (bv_wrap 64 (-160)) with (2 ^ 64 - 160).
    replace (bv_unsigned (rw rho 1%positive) + (2 ^ 64 - 160)) with ((bv_unsigned (rw rho 1%positive) - 160) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
  - rewrite sd_hm2_shape. cbn [snd]. apply Forall_nil.
Qed.

Lemma memset_test_ne : ltac2:(tb__ "0|2|
S1fQ40M0A1SeS0S45S20G0R1A2Z10A2Z0M1A3SeS7S5eG0S3eS4aS3eS4bS21G0Z120A2S3eS49R2S21G0N248A2A3A3S21G0ZfA2A3S21G0G1A2A3ScA3F_;Fv;").
Proof.
  intros v Hv. pose proof (bv_unsigned_in_range _ v) as R. change (bv_modulus 64) with 18446744073709551616 in R.
  unfold bv_eqb. apply Z.eqb_neq.
  unfold alu64, alu. rewrite bv_and_unsigned, bv_or_unsigned, bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_wrap 64 288) with 288. change (bv_wrap 64 15) with 15. change (bv_wrap 64 0) with 0.
  change (bv_wrap 64 (-584)) with 18446744073709551032.
  unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
  set (y := (bv_unsigned v + 18446744073709551032) mod 18446744073709551616).
  assert (Ypos : 0 <= y) by (subst y; apply Z.mod_pos_bound; lia).
  assert (Hy : y mod 16 = 8).
  { subst y. destruct (Z.mod_divide (bv_unsigned v) 16) as [Hd _]; [lia|]. destruct (Hd Hv) as [q Hq].
    rewrite Hq.
    match goal with |- ?a mod _ mod 16 = 8 =>
      rewrite (Zdiv.Zmod_eq_full a 18446744073709551616) by lia;
      set (d := a / 18446744073709551616) end.
    match goal with |- ?a mod 16 = 8 =>
      replace a with (8 + (q + 1152921504606846939 - d * 1152921504606846976) * 16) by lia end.
    rewrite Z.mod_add by lia. reflexivity. }
  rewrite Z.land_lor_distr_l. change (Z.land 288 15) with 0. rewrite Z.lor_0_l.
  change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. lia.
Qed.

Lemma MF2_holds : ltac2:(tb__ "0|0|
S12SeS0S45S20Q40S16R1P1A2A2Z10A2Z0A3S19R2S51A2F_;Frho;").
Proof.
  intros rho H16. cbn [holds MF2]. unfold branch_taken. cbn [eval]. rewrite (memset_test_ne (rw rho 1%positive) H16). discriminate.
Qed.

Section Seg2.

Variables (m : Model) (B : Z).
Hypothesis Hres : ltac2:(tb__ "0|1|
SeS4S5S1fQ40A1M0G0A2A1S31S2dVm;A1A1S5dSdA1A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
S61SbS5S1fQ40A1M0G0A2S31S2dVm;A1M1A1S33G1A1A3S60S5fA3").
Hypothesis HBlim : ltac2:(tb__ "0|0|
S46S44VB;Z10000A2S32S2dVm;A1A1A2").

Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S23S12S4S1fQ40A1A1S4S2eA1M0S2fR5R4R3R2R1A4SeG0R3S2S2eA1A3F_;Fmd;Ftr;Ftp;Frho;S24SdVok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S23S12S4S1fQ40A1A1S4S2eA1M0S2fR5R4R3R2R1A4SeG0R3S2S2eA1A3F_;Fmd;Ftr;Ftp;Frho;S67SdVok;R2A3F_;FJ;").

Definition n5 : word := Z_to_bv 64 0x10000.

Definition m5 (a : word) : Model := eager_model 0x10000 m a.

Definition Post2 (rho : valuation) : assn := ltac2:(tb__ "0|2|
S35SfS1fQ40M0A1M1G1SfS12S12S10S43S21G0Z0A2Vm;S3fR2A4S10S18P1cS59Vrho;P1bR2A3R1A3S22SdS34S41R2A1S44VB;Z10000A2A2S3dR1S2G1A1R3A6A2A2Lrho';A2La;A2Lw;").

Lemma OKFx : ltac2:(tb__ "0|0|
S2fS0S24SdVok;S34R2R1A2A3FBB;Fmm;").
Proof using OKF. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.

Lemma clear_s2 : ltac2:(tb__ "0|0|
SeS7S58S2S5S13S0A2A1S28S26A1A2S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma sp16_of_facts : ltac2:(tb__ "0|0|
S12S5cS15S19R1A1S1dS28S26A1A1A3SeS0S45S20Q40S16R2P1A2A2Z10A2Z0A3F_;Frho;").
Proof.
  intros rho HF.
  assert (X : In (SPAlign 1%positive 4) (ss_facts (ax_S E_s2))) by (vm_compute; tauto).
  pose proof (proj1 (Forall_forall _ _) HF _ X) as H. cbn [holds] in H. change (2 ^ 4) with 16 in H. lia.
Qed.

Lemma node_s2 : ltac2:(tb__ "0|5|
S12SeS0S20Q40M0S16R1P1A2A2S20G0S30S2dVm;A1A1A2A3S38SdVok;S22SdS34Vm;VB;A2M1S26R2S2S1fG0A1M2A1M3A5S35S11S22SdG1S53R3G3R1A6SfG2G2S10S43S21G0Z0A2Vm;S3fR1A4S22SdS34S41R1A1S44VB;Z10000M4A2A2S42S26G4P1cA3S59R4P1bR1A3G3R2A6A2La;A2A2Lw;A4F_;Frho;").
Proof using HBlim Hband Hres Htop OKF OKP.
  intros rho Hv1.
  apply (eager_rw_node ok OKF OKP E_s2 0x10000 m B [] 28%positive);
    [ reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | reflexivity | reflexivity | lia | cbv; reflexivity
    | exact clear_s2 | exact Hres | exact Htop | exact Hband | exact HBlim
    | intros e sz [] | exact Hv1 ].
Qed.

Lemma LQA1_SPA : ltac2:(tb__ "0|1|
S23S1S12S2aS35S25SdR5R4R3S2S1fQ40A1A1M0S3S27S29R2S5bA2S2S27A1A3R1A7SfS12S12S10S18R6R5R1A3S22SdR7R4R1G0R3A6A2Lrho';A2F_;Fw;FE;Frho;Fn;FJ;").
Proof. intros J n rho E w (L & rho' & [<-|[]] & Hag & Hsm & Hk). exists rho'. split; [exact Hag | split; [exact Hsm | exact Hk]]. Qed.

Lemma to_S_s2x : ltac2:(tb__ "0|1|
S23S12S35S22SdR3S42S26Z10000P1cA3R2S2S1fQ40A1A1M0R1A6S22SdR4S3bR3G0R2A6F_;Fw;Frho;FJ;").
Proof.
  intros J rho w [Hsm Hk]. split; [|exact Hk]. rewrite S_s2x_eq. apply smatchA_add_facts; [exact Hsm | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  apply Forall_cons; [|apply Forall_nil]. apply MF2_holds.
  apply sp16_of_facts. pose proof (SPA_facts_hold segsA _ rho _ [] w (conj Hsm Hk)) as HF.
  cbn [ax_S eager_ok ss_facts add_facts S_after] in HF. apply Forall_app in HF as [_ HF]. exact HF.
Qed.

Theorem start2_sum_A : ltac2:(tb__ "0|1|
S12SeS0S20Q40M0S16R1P1A2A2S20G0S30S2dVm;A1A1A2A3S37SdVok;S22SdS34Vm;VB;A2S26R2S2S1fG0A1A1A5S40R2A1A4F_;Frho;").
Proof using HBlim Hband Hres Htop OKF OKP.
  intros rho Hv1.
  eapply triple_seq; [apply triple1_triple; apply (node_s2 rho Hv1)|].
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA m B) (OKFx _ _) (fun n => stableA_KxA segsA n m B) S_s2fail SPIN5 400%nat SPIN_MMAPORDIE);
      [ reflexivity | reflexivity | reflexivity | exact runF_s2 | exact spin5 ].
  - apply triple_ex; intros a. apply triple_pure; intros Hpl.
    set (rho' := rho_set_rw rho 27%positive a). set (J5 := KxA (m5 a) (B + 0x10000)).
    change (eager_model 0x10000 m a) with (m5 a). change (KxA (m5 a) (B + 0x10000)) with J5.
    eapply triple_conseq; [intros w Hw; exact (to_S_s2x J5 rho' w Hw) | intros w Hw; exact Hw |].
    eapply triple_seq; [apply (run_cfg1 ok J5 FUEL2 [HMCUT; ECALL_MMAP] G2 S_s2x T_hm2 _ [] (OKFx _ _) (fun n => stableA_KxA segsA n _ _) check2a)|].
    apply triple_ex; intros L. apply triple_ex; intros rho2. apply triple_pure; intros HinL. apply triple_pure; intros Hag2.
    destruct HinL as [<-|[]]. cbn [la_state].
    change (fun w => smatchA segsA rho2 [] T_hm2 w /\ J5 rho2 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA J5 T_hm2 rho2 []).
    eapply triple_conseq; [intros w Hw; exact (restate_hm2 J5 rho2 w Hw) | | apply (run_cfg1 ok J5 FUEL2 [HMCUT; ECALL_MMAP] G2 S_hm2 E_s3 _ [] (OKFx _ _) (fun n => stableA_KxA segsA n _ _) check2b)].
    intros w Hw. destruct (LQA1_SPA J5 G2 rho2 E_s3 w Hw) as (rho3 & Hag3 & Hsp3).
    exists a, rho3. split; [exact Hpl|]. split; [eapply agree_below_trans; [exact Hag2 | exact Hag3] | exact Hsp3].
Qed.

Hypothesis Hwit : ltac2:(tb__ "0|2|
SfS1fQ40M0A1M1G1S43S21G0Z0A2Vm;S3fR1A4La;A2").

Theorem start2_sum_ex_A : ltac2:(tb__ "0|1|
S12SeS0S20Q40M0S16R1P1A2A2S20G0S30S2dVm;A1A1A2A3S36SdS22SdS34Vm;VB;A2S26R2S2S1fG0A1A1A5S40R2A1A3F_;Frho;").
Proof using HBlim Hband Hres Htop Hwit.
  intros rho Hv1.
  eapply etriple_seq.
  { apply (eager_rw_enode E_s2 0x10000 m B [] 28%positive);
      [ reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | reflexivity | reflexivity | lia | cbv; reflexivity
      | exact clear_s2 | exact Hres | exact Htop | exact Hband | exact HBlim | exact Hwit
      | intros e sz [] | exact Hv1 ]. }
  apply etriple_ex; intros a. intros w [Hpl Hsp]. revert w Hsp.
  set (rho' := rho_set_rw rho 27%positive a). set (J5 := KxA (m5 a) (B + 0x10000)).
  change (eager_model 0x10000 m a) with (m5 a). change (KxA (m5 a) (B + 0x10000)) with J5.
  change (etriple segsA (SPA segsA J5 (eager_ok E_s2 0x10000 28%positive) rho' []) (Post2 rho)).
  eapply etriple_conseq; [intros w Hw; exact (to_S_s2x J5 rho' w Hw) | intros w Hw; exact Hw |].
  eapply etriple_seq; [apply (erun_cfg1 J5 FUEL2 [HMCUT; ECALL_MMAP] G2 S_s2x T_hm2 _ [] (fun n => stableA_KxA segsA n _ _) check2a)|].
  apply etriple_ex; intros L. apply etriple_ex; intros rho2. apply etriple_pure; intros HinL. apply etriple_pure; intros Hag2.
  destruct HinL as [<-|[]]. cbn [la_state].
  change (fun w => smatchA segsA rho2 [] T_hm2 w /\ J5 rho2 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA J5 T_hm2 rho2 []).
  eapply etriple_conseq; [intros w Hw; exact (restate_hm2 J5 rho2 w Hw) | | apply (erun_cfg1 J5 FUEL2 [HMCUT; ECALL_MMAP] G2 S_hm2 E_s3 _ [] (fun n => stableA_KxA segsA n _ _) check2b)].
  intros w Hw. destruct (LQA1_SPA J5 G2 rho2 E_s3 w Hw) as (rho3 & Hag3 & Hsp3).
  exists a, rho3. split; [exact Hpl|]. split; [eapply agree_below_trans; [exact Hag2 | exact Hag3] | exact Hsp3].
Qed.
End Seg2.
