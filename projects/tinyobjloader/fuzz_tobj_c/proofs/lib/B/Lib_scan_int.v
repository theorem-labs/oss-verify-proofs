(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "app"; "prod"; "None"; "false"; "list"; "bool"; "true"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SLit"; "SPUle"; "SVar"; "sobj"; "cell"; "SAlu"; "SPUlt"; "valuation"; "DUnknown"; "FcsrFrm0"; "mkCell"; "mkObj"; "mkSS"; "SPAlign"; "holds"; "ss_facts"; "SPBranch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_int"; "pB"; "v120"; "vE"; "v121"; "vI"; "vL"; "Pre_si"; "X_si"; "base_facts"; "v141"; "vB"; "vOG"; "FUEL_si"; "O_out"; "O_pp"; "O_stk"; "O_txt"; "P_none"; "P_num"; "X_t1"; "X_t2"; "X_t3"; "cutpcs_si"; "si_state"; "two40"; "C1"; "C2"; "C3"; "F_si"; "Posts_si"; "cuts_si"; "imax"; "inv3"; "post_objs"; "two47"; "F8_pp"; "exits_si"; "g_pp"; "inv1"; "inv2"; "og_facts"; "regs1"; "regs2"; "sh_pp"; "vcuts_si"; "vexits_si"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "A_globals"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "cut_regs"; "pre_regs"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_LTU"; "@Corelib.Init.Logic"; "False"; "eq"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_int.ScanIntAddr"; "si_L1"; "si_L2"; "si_L3"; "si_entry"; "si_ret1"; "si_ret2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ScanIntAddr.
  Definition si_entry : Z := 0xa014c.
  Definition si_L1 : Z := 0xa01a0.
  Definition si_L3 : Z := 0xa0230.
  Definition si_L2 : Z := 0xa027c.
  Definition si_ret1 : Z := 0xa02fc.
  Definition si_ret2 : Z := 0xa034c.
End ScanIntAddr.
Import ScanIntAddr.

Definition FUEL_si : nat := 300%nat.

Definition vB : sv := SVar 15.
Definition vI : sv := SVar 16.
Definition vE : sv := SVar 17.
Definition vL : sv := SVar 18.
Definition pB (off : sv) : sv := SAlu ALU_ADD vB off.
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.
Definition imax : Z := 0x7fffffff.

Definition vOG : sv := SVar 19.
Definition og_facts : list sprop := ltac2:(tb__ "0|2|
S0ScS1bP13Z3A2S0ScSfS2aS10PeA1M0A2S0ScS14G0S13S60S2aSeZ8A1A3M1A2S0ScSfS13S60G0SeZ4A1A3G1A2S0ScSfS2aSeS41A1A2S1ScA1A3A3A3A3A3").
Definition base_facts : list sprop := ltac2:(tb__ "0|3|
S4ScS0ScSfS23S21A2S0ScSfS21S24A2S0ScSfS24SeS37A1A2S0ScSfS29SeS41A1M0A2S0ScSfSeZ1A1S29A2S0ScS1bPcM1Z3A2S0ScS1bPeM2Z2A2S0ScSfS10G1A1G0A2S0ScSfS10G2A1G0A2S1ScA1A3A3A3A3A3A3A3A3A3S47A3").

Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S10PaA1SeN10A1SeZ0A1Vcells;S16A5").
Definition O_pp (c0 : sv) : sobj := ltac2:(tb__ "0|2|
S19S10PcA1SeZ0A1M0SeZ8M1A1S0S12S18G0G1Vc0;A3S1S12A1A3S16A5").
Definition O_txt (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S29SeZ0A1S24Vcells;S16A5").
Definition O_out (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S10PeA1SeZ0A1SeZ4A1Vcells;S16A5").

Definition X_si : list (sv * sv) := ltac2:(tb__ "0|2|
S0S5SdSdA2M0S3SdSdS10PcA1SeZ8A1M1A4S0G0S3SdSdS29S24A4S0G0S3SdSdS2aG1A4S1G0A1A3A3A3").

Definition Pre_si : axst := ltac2:(tb__ "0|2|
S4eS1aS69S5bS5eS0S5S2SdA2M0S3S2SdUbS1fS21A1A4S1G0A1A3A2S5aS17S6SdA1S4S11S0S11S2eS1S12A1M1A1S0S11S2dS1fS23A1A1S0S11S2fG1A1S0S11S2cG1A1S1S11A1A3A3A3A3S4fA3S27S59S7A9S26A2").

Definition v120 : sv := SVar 120.
Definition v121 : sv := SVar 121.

Definition inv1 : list sprop := ltac2:(tb__ "0|0|
S0ScS14S20S21A2S0ScS14S20S24A2S0ScSfS23S20A2S0ScSfS20SeS37A1A2S0ScS1eS62S1fS20A1S1fS21A1A3S1ScA1A3A3A3A3A3").
Definition inv3 : list sprop := ltac2:(tb__ "0|1|
S0ScS14S22S21A2S0ScS14S22S24A2S0ScSfS23S22A2S0ScSfS22SeS37A1M0A2S0ScS1eS62S1fS22A1S1fS21A1A3S0ScS14S20S21A2S0ScSfS23S20A2S0ScSfS20G0A2S1ScA1A3A3A3A3A3A3A3A3").

Definition g_pp : positive := 125%positive.
Definition F8_pp : list sprop := F8x g_pp (SVar 12).
Definition sh_pp : sv := ltac2:(tb__ "0|0|
S13S60S10S44A1S50A3").

Definition si_state (pc : Z) (regs : list (nat * sv)) (c0 : sv) (txt out : list cell)
           (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|1|
S4eS1aVpc;S5bS5dS59A1S4S5S2SdA2M0S0G0S3S2SdU2S13S60S10PaA1SeN10A1A3A4S0G0S3S2SdUaS10PcA1A4S0G0S3S2SdUbS1fS21A1A4S0G0S3S2SdUcS10PeA1A4S0G0S3S2SdUfS4aA4S0G0S3S2SdU10S50A4S1G0A1A3A3A3A3A3A3Vregs;A3A2S5aS17S6SdA1S4S11S0S11S2eS0S12S18SeN8A1Z8S10PbA1A3S1S12A1A3A1S0S11S2dVc0;A1S0S11S2fVtxt;A1S0S11S2cVout;A1S1S11A1A3A3A3A3S4fA3S4ScVfacts;S4ScS42S27A3A3Vnx;S7A9S26A2").

Definition regs1 (c : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S2SdA2M0S3S2SdUdVc;A4S0G0S3S2SdUeVc;A4S0G0S3S2SdU11SeZ20A1A4S0G0S3S2SdU5SeZ9A1A4S1G0A1A3A3A3A3").
Definition C1 : axst := ltac2:(tb__ "0|1|
S36S66S48S1fS20A1A1S1fS23A1S1S12A1M0G0S45P87A7").

Definition C3 : axst := ltac2:(tb__ "0|2|
S36S68S0S5S2SdA2M0S3S2SdUdS1fS22A1A4S0G0S3S2SdU11S10P7aA1A4S1G0A1A3A3S1fS20A1S1S12A1M1G1S3fP87A7").

Definition regs2 (c : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S2SdA2M0S3S2SdUdVc;A4S0G0S3S2SdUeVc;A4S0G0S3S2SdU11S10P7aA1A4S0G0S3S2SdU5S10P7bA1A4S0G0S3S2SdU1dS10P7cA1A4S0G0S3S2SdU6SeZ9A1A4S0G0S3S2SdU7SeZaA1A4S0G0S3S2SdU1cSeS3eA1A4S1G0A1A3A3A3A3A3A3A3A3").

Definition inv2 : list sprop := ltac2:(tb__ "0|0|
S4ScS3fS0ScSfS10P7bA1SeS3eA1A2S1ScA1A3A3").
Definition C2 : axst := ltac2:(tb__ "0|1|
S36S67S49S1fS22A1A1S1fS20A1S1S12A1M0G0S46P87A7").

Definition v141 : sv := SVar 141.
Definition F_si : list sprop := ltac2:(tb__ "0|0|
S0ScSfS23S28A2S0ScSfS28S21A2S1ScA1A3A3").
Definition post_objs (c0 : sv) (out : list cell) : list sobj := ltac2:(tb__ "0|1|
S4S11S0S11S2eS0S12S18SeN8A1Z8S10PbA1A3S1S12A1M0A3A1S0S11S2dVc0;A1S0S11S2fG0A1S0S11S2cVout;A1S1S11A1A3A3A3A3S4fA3").
Definition P_none : axst := ltac2:(tb__ "0|1|
S4eS1aS6aS5bS5cS59A1S0S5S2SdA2M0S3S2SdUaSeZ0A1A4S1G0A1A3A2S5aS17S6SdA1S40S1fS28A1S1S12A1A2S4ScS3bS27A3P8fS7A9S26A2").
Definition P_num : axst := ltac2:(tb__ "0|1|
S4eS1aS6bS5bS5cS59A1S0S5S2SdA2M0S3S2SdUaSeZ1A1A4S1G0A1A3A2S5aS17S6SdA1S40S1fS28A1S0S12S18SeZ0A1Z4S10P8eA1A3S1S12A1A3A2S4ScS3bS27A3P8fS7A9S26A2").
Definition Posts_si : list leafA := ltac2:(tb__ "0|0|
S0S56S58S30S6cA2S0S56S58S31S6cA2S1S56A1A3A3").

Definition cuts_si : list axst := ltac2:(tb__ "0|0|
S0S55S25S0S55S38S0S55S3aS0S55S39S1S55A1A3A3A3A3").

Definition si_trap : Z := 0xa0350.
Definition X_t1 : axst := Eval vm_compute in nth 0 (leavesA_at FUEL_si [si_L1; si_L3; si_L2] C2 si_trap) Pre_si.
Definition X_t2 : axst := Eval vm_compute in nth 1 (leavesA_at FUEL_si [si_L1; si_L3; si_L2] C2 si_trap) Pre_si.
Definition X_t3 : axst := Eval vm_compute in nth 2 (leavesA_at FUEL_si [si_L1; si_L3; si_L2] C2 si_trap) Pre_si.
Definition exits_si : list axst := ltac2:(tb__ "0|0|
S0S55S30S0S55S31S0S55S32S0S55S33S0S55S34S1S55A1A3A3A3A3A3").
Definition cutpcs_si : list Z := ltac2:(tb__ "0|0|
S0S5fS66S0S5fS68S0S5fS67S1S5fA1A3A3A3").

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2.

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Definition check_si__runs : ltac2:(tb__ "0|0|
S8SbS8S56A1A1A1") := ltac2:(tb__ "0|0|
S76S4dS2bS35S3dA4").
Lemma check_si : ltac2:(tb__ "0|0|
S64S9S53S4dS2bS35S59S3dS43A6SaA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUEL_si cutpcs_si NF cuts_si exits_si check_si__runs); [unfold check_si__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Lemma contra_t1 : ltac2:(tb__ "0|0|
S15S65ScS1cR1A1S1dS57S32A1A1A3S63F_;Frho;").
Proof. intros rho HF. concrete_facts HF. pick_facts HF [0; 14]%nat. zfacts; lia. Qed.
Lemma contra_t2 : ltac2:(tb__ "0|0|
S15S65ScS1cR1A1S1dS57S33A1A1A3S63F_;Frho;").
Proof. intros rho HF. concrete_facts HF. pick_facts HF [0; 16]%nat. zfacts; lia. Qed.
Lemma contra_t3 : ltac2:(tb__ "0|0|
S15S65ScS1cR1A1S1dS57S34A1A1A3S63F_;Frho;").
Proof. intros rho HF. concrete_facts HF. pick_facts HF [0; 3; 5; 17]%nat. zfacts; lia. Qed.

Theorem scan_int_sum : ltac2:(tb__ "0|0|
S75OF_;S6fS15S8S72Q40A1A1S71S4dR4R3A3S70S4dS59R4A3S74S4dR6S6eS4dR5S25R4R3A5S6dS4dR5S59R4R3S3cA6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_si rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_si cutpcs_si NF cuts_si exits_si (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_si) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_si.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply exit_postA. in_nth 0.
    + apply exit_postA. in_nth 1.
    + apply (exit_contraA segs ok _ X_t1). intros r tp' tr md _ HF. exact (contra_t1 r HF).
    + apply (exit_contraA segs ok _ X_t2). intros r tp' tr md _ HF. exact (contra_t2 r HF).
    + apply (exit_contraA segs ok _ X_t3). intros r tp' tr md _ HF. exact (contra_t3 r HF).
  - left; reflexivity.
Qed.

Definition vcuts_si : list vnodeA := ltac2:(tb__ "0|1|
S0S51S52S25Z1eSeZ0A1A3S0S51S52S38Z14S13S61S21S20A3A3S0S51S52S3aZfS13S61S21S22A3M0A3S0S51S52S39ZaG0A3S1S51A1A3A3A3A3").
Definition vexits_si : list vnodeA := ltac2:(tb__ "0|3|
S0S51S52S30Z1M0SeZ0M1A1M2A3S0S51S52S31G0G2A3S0S51S52S32G1G2A3S0S51S52S33G1G2A3S0S51S52S34G1G2A3S1S51A1A3A3A3A3A3").

Lemma echeck_si : ltac2:(tb__ "0|0|
S64S9S54S4dS2bS35S59S4bS4cA6SaA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUEL_si cutpcs_si NF vcuts_si vexits_si check_si__runs); [unfold check_si__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem scan_int_sum_ex : ltac2:(tb__ "0|0|
S6fS15S8S72Q40A1A1S70S4dS59R3A3S73S4dS6eS4dR4S25R3R2A5S6dS4dR4S59R3R2S3cA6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_si rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_si with (vna_state (mkVNA Pre_si 30 (SLit 0))).
  apply (cfg_complete_autoA segs FUEL_si cutpcs_si NF vcuts_si vexits_si (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_si) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbv; congruence.
  - exact echeck_si.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply (eexit_postA segs J NF rho vcuts_si Posts_si (mkVNA P_none 1 (SLit 0))). in_nth 0.
    + apply (eexit_postA segs J NF rho vcuts_si Posts_si (mkVNA P_num 1 (SLit 0))). in_nth 1.
    + apply (eexit_contraA segs _ X_t1). intros r tp' tr md _ HF. exact (contra_t1 r HF).
    + apply (eexit_contraA segs _ X_t2). intros r tp' tr md _ HF. exact (contra_t2 r HF).
    + apply (eexit_contraA segs _ X_t3). intros r tp' tr md _ HF. exact (contra_t3 r HF).
  - left; reflexivity.
Qed.
