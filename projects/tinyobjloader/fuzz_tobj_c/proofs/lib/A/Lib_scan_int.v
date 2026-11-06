(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "app"; "prod"; "None"; "false"; "list"; "bool"; "true"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SLit"; "SPUle"; "SVar"; "sobj"; "cell"; "SAlu"; "SPUlt"; "DUnknown"; "FcsrFrm0"; "mkCell"; "mkObj"; "mkSS"; "SPAlign"; "SPBranch"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_int"; "pB"; "v120"; "vE"; "v121"; "vI"; "vL"; "Pre_si"; "X_si"; "base_facts"; "v141"; "vB"; "vOG"; "FUEL_si"; "O_out"; "O_pp"; "O_stk"; "O_txt"; "P_none"; "P_num"; "cutpcs_si"; "si_state"; "two40"; "C1"; "C2"; "C3"; "F_si"; "Posts_si"; "cuts_si"; "inv3"; "post_objs"; "two47"; "F8_pp"; "exits_si"; "g_pp"; "imax"; "inv1"; "og_facts"; "regs1"; "regs2"; "sh_pp"; "vcuts_si"; "vexits_si"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "mkA"; "A_globals"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "setregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "mkLeafA"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_LTU"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_int.ScanIntAddr"; "si_L1"; "si_L2"; "si_L3"; "si_entry"; "si_ret1"; "si_ret2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ScanIntAddr.
  Definition si_entry : Z := 0xa1840.
  Definition si_L1 : Z := 0xa1888.
  Definition si_L3 : Z := 0xa1914.
  Definition si_L2 : Z := 0xa1960.
  Definition si_ret1 : Z := 0xa1908.
  Definition si_ret2 : Z := 0xa19f8.
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
S0ScS1aP13Z3A2S0ScSfS28S10PeA1M0A2S0ScS14G0S13S59S28SeZ8A1A3M1A2S0ScSfS13S59G0SeZ4A1A3G1A2S0ScSfS28SeS3bA1A2S1ScA1A3A3A3A3A3").
Definition base_facts : list sprop := ltac2:(tb__ "0|3|
S4ScS0ScSfS21S1fA2S0ScSfS1fS22A2S0ScSfS22SeS32A1A2S0ScSfS27SeS3bA1M0A2S0ScSfSeZ1A1S27A2S0ScS1aPcM1Z3A2S0ScS1aPeM2Z2A2S0ScSfS10G1A1G0A2S0ScSfS10G2A1G0A2S1ScA1A3A3A3A3A3A3A3A3A3S41A3").

Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S10PaA1SeN10A1SeZ0A1Vcells;S15A5").
Definition O_pp (c0 : sv) : sobj := ltac2:(tb__ "0|2|
S18S10PcA1SeZ0A1M0SeZ8M1A1S0S12S17G0G1Vc0;A3S1S12A1A3S15A5").
Definition O_txt (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S27SeZ0A1S22Vcells;S15A5").
Definition O_out (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S10PeA1SeZ0A1SeZ4A1Vcells;S15A5").

Definition X_si : list (sv * sv) := ltac2:(tb__ "0|2|
S0S5SdSdA2M0S3SdSdS10PcA1SeZ8A1M1A4S0G0S3SdSdS27S22A4S0G0S3SdSdS28G1A4S1G0A1A3A3A3").

Definition Pre_si : axst := ltac2:(tb__ "0|2|
S48S19S60S4eS50S0S5S2SdA2M0S3S2SdUbS1dS1fA1A4S1G0A1A3A2S4cS16S6SdA1S4S11S0S11S2cS1S12A1M1A1S0S11S2bS1dS21A1A1S0S11S2dG1A1S0S11S2aG1A1S1S11A1A3A3A3A3S49A3S25S4bS7A9S24A2").

Definition v120 : sv := SVar 120.
Definition v121 : sv := SVar 121.

Definition inv1 : list sprop := ltac2:(tb__ "0|0|
S0ScS14S1eS1fA2S0ScS14S1eS22A2S0ScSfS21S1eA2S0ScSfS1eSeS32A1A2S0ScS1bS5bS1dS1eA1S1dS1fA1A3S1ScA1A3A3A3A3A3").
Definition inv3 : list sprop := ltac2:(tb__ "0|1|
S0ScS14S20S1fA2S0ScS14S20S22A2S0ScSfS21S20A2S0ScSfS20SeS32A1M0A2S0ScS1bS5bS1dS20A1S1dS1fA1A3S0ScS14S1eS1fA2S0ScSfS21S1eA2S0ScSfS1eG0A2S1ScA1A3A3A3A3A3A3A3A3").

Definition g_pp : positive := 125%positive.
Definition F8_pp : list sprop := F8x g_pp (SVar 12).
Definition sh_pp : sv := ltac2:(tb__ "0|0|
S13S59S10S3eA1S4aA3").

Definition si_state (pc : Z) (regs : list (nat * sv)) (c0 : sv) (txt out : list cell)
           (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|1|
S48S19Vpc;S4eS4fS4bA1S4S5S2SdA2M0S0G0S3S2SdU2S13S59S10PaA1SeN10A1A3A4S0G0S3S2SdUaS10PcA1A4S0G0S3S2SdUbS1dS1fA1A4S0G0S3S2SdUcS10PeA1A4S0G0S3S2SdUfS44A4S0G0S3S2SdU10S4aA4S1G0A1A3A3A3A3A3A3Vregs;A3A2S4cS16S6SdA1S4S11S0S11S2cS0S12S17SeN8A1Z8S10PbA1A3S1S12A1A3A1S0S11S2bVc0;A1S0S11S2dVtxt;A1S0S11S2aVout;A1S1S11A1A3A3A3A3S49A3S4ScVfacts;S4ScS3cS25A3A3Vnx;S7A9S24A2").

Definition regs1 (c : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S2SdA2M0S3S2SdUdVc;A4S0G0S3S2SdUeVc;A4S0G0S3S2SdU11SeZ20A1A4S0G0S3S2SdU5SeZ9A1A4S1G0A1A3A3A3A3").
Definition C1 : axst := ltac2:(tb__ "0|1|
S31S5dS42S1dS1eA1A1S1dS21A1S1S12A1M0G0S40P87A7").

Definition C3 : axst := ltac2:(tb__ "0|2|
S31S5fS0S5S2SdA2M0S3S2SdUdS1dS20A1A4S0G0S3S2SdU11S10P7aA1A4S1G0A1A3A3S1dS1eA1S1S12A1M1G1S39P87A7").

Definition regs2 (c : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S2SdA2M0S3S2SdUdVc;A4S0G0S3S2SdUeVc;A4S0G0S3S2SdU11S10P7aA1A4S0G0S3S2SdU5S10P7bA1A4S0G0S3S2SdU1dS10P7cA1A4S0G0S3S2SdU6SeZ9A1A4S0G0S3S2SdU7SeZaA1A4S0G0S3S2SdU1cSeS3fA1A4S1G0A1A3A3A3A3A3A3A3A3").
Definition C2 : axst := ltac2:(tb__ "0|1|
S31S5eS43S1dS20A1A1S1dS1eA1S1S12A1M0G0S39P87A7").

Definition v141 : sv := SVar 141.
Definition F_si : list sprop := ltac2:(tb__ "0|0|
S0ScSfS21S26A2S0ScSfS26S1fA2S1ScA1A3A3").
Definition post_objs (c0 : sv) (out : list cell) : list sobj := ltac2:(tb__ "0|1|
S4S11S0S11S2cS0S12S17SeN8A1Z8S10PbA1A3S1S12A1M0A3A1S0S11S2bVc0;A1S0S11S2dG0A1S0S11S2aVout;A1S1S11A1A3A3A3A3S49A3").
Definition P_none : axst := ltac2:(tb__ "0|0|
S48S19S61S4dS4bA1S4cS16S6SdA1S3aS1dS26A1S1S12A1A2S4ScS36S25A3P8fS7A9S24A2").
Definition P_num : axst := ltac2:(tb__ "0|0|
S48S19S62S4dS4bA1S4cS16S6SdA1S3aS1dS26A1S0S12S17SeZ0A1Z4S10P8eA1A3S1S12A1A3A2S4ScS36S25A3P8fS7A9S24A2").
Definition Posts_si : list leafA := ltac2:(tb__ "0|0|
S0S56S57S2eS63A2S0S56S57S2fS63A2S1S56A1A3A3").

Definition cuts_si : list axst := ltac2:(tb__ "0|0|
S0S55S23S0S55S33S0S55S35S0S55S34S1S55A1A3A3A3A3").
Definition exits_si : list axst := ltac2:(tb__ "0|0|
S0S55S2eS0S55S2fS1S55A1A3A3").
Definition cutpcs_si : list Z := ltac2:(tb__ "0|0|
S0S58S5dS0S58S5fS0S58S5eS1S58A1A3A3A3").

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Definition check_si__runs : ltac2:(tb__ "0|0|
S8SbS8S56A1A1A1") := ltac2:(tb__ "0|0|
S6dS47S29S30S38A4").
Lemma check_si : ltac2:(tb__ "0|0|
S5cS9S53S47S29S30S4bS38S3dA6SaA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUEL_si cutpcs_si NF cuts_si exits_si check_si__runs); [unfold check_si__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem scan_int_sum : ltac2:(tb__ "0|0|
S6cOF_;S66S1cS8S69Q40A1A1S68S47R4R3A3S67S47S4bR4A3S6bS47R6S65S47R5S23R4R3A5S64S47R5S4bR4R3S37A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_si rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_si cutpcs_si NF cuts_si exits_si (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_si) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_si.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[]]].
    + apply exit_postA. in_nth 0.
    + apply exit_postA. in_nth 1.
  - left; reflexivity.
Qed.

Definition vcuts_si : list vnodeA := ltac2:(tb__ "0|1|
S0S51S52S23Z1eSeZ0A1A3S0S51S52S33Z14S13S5aS1fS1eA3A3S0S51S52S35ZfS13S5aS1fS20A3M0A3S0S51S52S34ZaG0A3S1S51A1A3A3A3A3").
Definition vexits_si : list vnodeA := ltac2:(tb__ "0|2|
S0S51S52S2eZ1M0SeZ0A1M1A3S0S51S52S2fG0G1A3S1S51A1A3A3").

Lemma echeck_si : ltac2:(tb__ "0|0|
S5cS9S54S47S29S30S4bS45S46A6SaA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUEL_si cutpcs_si NF vcuts_si vexits_si check_si__runs); [unfold check_si__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem scan_int_sum_ex : ltac2:(tb__ "0|0|
S66S1cS8S69Q40A1A1S67S47S4bR3A3S6aS47S65S47R4S23R3R2A5S64S47R4S4bR3R2S37A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_si rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_si with (vna_state (mkVNA Pre_si 30 (SLit 0))).
  apply (cfg_complete_autoA segs FUEL_si cutpcs_si NF vcuts_si vexits_si (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_si) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbv; congruence.
  - exact echeck_si.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[]]].
    + apply (eexit_postA segs J NF rho vcuts_si Posts_si (mkVNA P_none 1 (SLit 0))). in_nth 0.
    + apply (eexit_postA segs J NF rho vcuts_si Posts_si (mkVNA P_num 1 (SLit 0))). in_nth 1.
  - left; reflexivity.
Qed.
