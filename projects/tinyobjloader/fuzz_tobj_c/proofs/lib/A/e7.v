(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From Stdlib Require Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require PlacementA e2 SysStartA.

(* [comment removed for export] *)
Module Lib_diag_append.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nil"; "cons"; "list"; "prod"; "None"; "app"; "bool"; "false"; "nat"; "true"; "option"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "A_globals"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "FcsrFrm0"; "cell"; "mkSS"; "sprop"; "valuation"; "DUnknown"; "SVar"; "mkObj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "FUEL_da"; "Pre_da"; "cutpcs_da"; "O_dstk"; "P_da"; "Posts_da"; "cuts_da"; "NXP_da"; "exits_da"; "vcuts_da"; "vexits_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.DiagAppendAddr"; "da_entry"; "da_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"].
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

Module DiagAppendAddr.
  Definition da_entry : Z := 0xa6088.
  Definition da_ret : Z := 0xa6280.
End DiagAppendAddr.
Import DiagAppendAddr.

Definition FUEL_da : nat := 100%nat.
Definition NXP_da : positive := 140%positive.

Definition O_dstk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S18PaA1S11N60A1S11Z0A1Vcells;S17A5").

Definition Pre_da : axst := ltac2:(tb__ "0|1|
SeS14S37S1eS1dS1S3S8SfA2M0SbS8SfUaS11Z0A1A4S0G0A1A3A2S1bS12S4SfA1S5S10S1S10S26S0S13A1A1S0S10A1A3SdA3S0S15A1S1aS7A9S0S3SfSfA2A1A2").

Definition P_da : axst := ltac2:(tb__ "0|0|
SeS14S38S1cS1aA1S1bS12S4SfA1S5S10S1S10S26S0S13A1A1S0S10A1A3SdA3S0S15A1S2aS7A9S0S3SfSfA2A1A2").
Definition Posts_da : list leafA := ltac2:(tb__ "0|0|
S1S2eS2fS27S3cA2S0S2eA1A3").

Definition cuts_da : list axst := [Pre_da].
Definition exits_da : list axst := [P_da].
Definition cutpcs_da : list Z := [].

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Definition check_da__runs : ltac2:(tb__ "0|0|
S2SaS2S2eA1A1A1") := ltac2:(tb__ "0|0|
S3dScS23S25S29A4").
Lemma check_da : ltac2:(tb__ "0|0|
S30S6S21ScS23S25S1aS29S2bA6S9A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUEL_da cutpcs_da NF cuts_da exits_da check_da__runs); [unfold check_da__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem diag_append_sum : ltac2:(tb__ "0|0|
S3bOF_;S33S16S2S36Q40A1A1S35ScR4R3A3S34ScS1aR4A3S3aScR6S32ScR5S24R4R3A5S31ScR5S1aR4R3S28A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_da rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_da cutpcs_da NF cuts_da exits_da (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_da) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_da.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply exit_postA. in_nth 0.
  - left; reflexivity.
Qed.

Definition vcuts_da : list vnodeA := ltac2:(tb__ "0|0|
S1S1fS20S24Z1eS11Z0A1A3S0S1fA1A3").
Definition vexits_da : list vnodeA := ltac2:(tb__ "0|0|
S1S1fS20S27Z1S11Z0A1A3S0S1fA1A3").

Lemma echeck_da : ltac2:(tb__ "0|0|
S30S6S22ScS23S25S1aS2cS2dA6S9A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUEL_da cutpcs_da NF vcuts_da vexits_da check_da__runs); [unfold check_da__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem diag_append_sum_ex : ltac2:(tb__ "0|0|
S33S16S2S36Q40A1A1S34ScS1aR3A3S39ScS32ScR4S24R3R2A5S31ScR4S1aR3R2S28A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_da rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_da with (vna_state (mkVNA Pre_da 30 (SLit 0))).
  apply (cfg_complete_autoA segs FUEL_da cutpcs_da NF vcuts_da vexits_da (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_da) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. destruct Hin as [<-|[]]; cbv; congruence.
  - exact echeck_da.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply (eexit_postA segs J NF rho vcuts_da Posts_da (mkVNA P_da 1 (SLit 0))). in_nth 0.
  - left; reflexivity.
Qed.
End Lib_diag_append.

(* [comment removed for export] *)
Module Lib_next_token.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "app"; "prod"; "false"; "None"; "list"; "bool"; "true"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SLit"; "SPUle"; "sobj"; "SVar"; "cell"; "SPUlt"; "mkCell"; "DUnknown"; "SPBranch"; "mkObj"; "FcsrFrm0"; "SAlu"; "mkSS"; "SPAlign"; "SPEq"; "SPNot"; "valuation"; "SExt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_next_token"; "pB"; "vE"; "v141"; "v120"; "vL"; "v143"; "vI"; "v123"; "Pre_nt"; "base_facts"; "two40"; "v142"; "vB"; "FUEL_nt"; "O_cur"; "O_stk"; "O_tl"; "O_tok"; "O_txt"; "P_found"; "P_nf"; "X_nt"; "cur2"; "cutpcs_nt"; "inv1"; "nt_state"; "C1"; "C2"; "C2f"; "Posts_nt"; "VD"; "cuts_nt"; "post_objs"; "regs2"; "F8_c"; "F_found"; "F_nf"; "exits_nt"; "g_c"; "inv2"; "nonblank"; "regs1"; "shc"; "two47"; "vcuts_nt"; "vexits_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "A_globals"; "mkA"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "mkLeafA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "BC_EQ"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_next_token.NextTokenAddr"; "nt_L2"; "nt_L1"; "nt_ret"; "nt_entry"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"].
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

Module NextTokenAddr.
  Definition nt_entry : Z := 0x9bdb4.
  Definition nt_L1 : Z := 0x9be14.
  Definition nt_L2 : Z := 0x9be74.
  Definition nt_ret : Z := 0x9bf00.

End NextTokenAddr.
Import NextTokenAddr.

Definition FUEL_nt : nat := 300%nat.

Definition vB : sv := SVar 15.
Definition vI : sv := SVar 16.
Definition vE : sv := SVar 17.
Definition vL : sv := SVar 18.
Definition pB (off : sv) : sv := SAlu ALU_ADD vB off.
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.

Definition base_facts : list sprop := ltac2:(tb__ "0|5|
S0ScSfS26S21A2S0ScSfS21S24A2S0ScSfS24SeS2aA1A2S0ScSfS2cSeS4bA1M0A2S0ScSfSeZ1A1S2cA2S0ScS1bPcM1Z3M2A2S0ScS1bPdM3G2A2S0ScS1bPeM4G2A2S0ScSfS11G1A1G0A2S0ScSfS11G3A1G0A2S0ScSfS11G4A1G0A2S1ScA1A3A3A3A3A3A3A3A3A3A3A3").

Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17S11PaA1SeN10A1SeZ0A1Vcells;S15A5").
Definition O_cur (c0 : sv) : sobj := ltac2:(tb__ "0|2|
S17S11PcA1SeZ0A1M0SeZ10A1S0S12S14G0Z8M1Vc0;A3S0S12S14SeG1A1G1S20S21A1A3S1S12A1A3A3S15A5").
Definition O_txt (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17S2cSeZ0A1S24Vcells;S15A5").
Definition O_tok (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17S11PdA1SeZ0A1SeZ8A1Vcells;S15A5").
Definition O_tl (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17S11PeA1SeZ0A1SeZ8A1Vcells;S15A5").

Definition X_nt : list (sv * sv) := ltac2:(tb__ "0|2|
S0S5SdSdA2M0S3SdSdS11PcA1SeZ10A1A4S0G0S3SdSdS2cS24A4S0G0S3SdSdS11PdA1SeZ8A1M1A4S0G0S3SdSdS11PeA1G1A4S1G0A1A3A3A3A3").

Definition Pre_nt_S : sstate := ltac2:(tb__ "0|1|
S1aS66S57S53S18S7SdA1S4S10S0S10S2fS1S12A1M0A1S0S10S2eS20S26A1A1S0S10S32G0A1S0S10S31G0A1S0S10S30G0A1S1S10A1A3A3A3A3A3S4fA3S29S52S6A9").
Definition Pre_nt : axst := mkA Pre_nt_S X_nt.

Definition v120 : sv := SVar 120.
Definition v123 : sv := SVar 123.
Definition cur2 : sv := pB v123.

Definition inv1 : list sprop := ltac2:(tb__ "0|0|
S0ScS13S23S21A2S0ScS13S23S24A2S0ScSfS26S23A2S0ScSfS23SeS2aA1A2S0ScS16S60S20S23A1S20S21A1A3S1ScA1A3A3A3A3A3").
Definition inv2 : list sprop := ltac2:(tb__ "0|0|
S4ScS38S0ScSfS19S5fS23SeZ1A1A3S27A2S0ScS13S27S21A2S0ScS13S27S24A2S0ScSfS27SeS2aA1A2S0ScS16S60S36S20S21A1A3S1ScA1A3A3A3A3A3A3").
Definition nonblank (x : positive) : list sprop := ltac2:(tb__ "0|1|
S0ScS1dS16S61S1fS6Q8S11Vx;A1A3M0SeZ20A1A3A1S0ScS1dS16S61G0SeZ9A1A3A1S1ScA1A3A3").

Definition g_c : positive := 124%positive.
Definition F8_c : list sprop := F8x g_c (SVar 12).
Definition shc : sv := ltac2:(tb__ "0|0|
S19S5fS11S46A1S51A3").

Definition nt_state (pc : Z) (regs : list (nat * sv)) (c0 : sv) (txt : list cell)
           (tok tl : list cell) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|1|
S50S1aVpc;S54S56S52A1S4S5S2SdA2M0S0G0S3S2SdU2S19S5fS11PaA1SeN10A1A3A4S0G0S3S2SdUaS11PcA1A4S0G0S3S2SdUbS11PdA1A4S0G0S3S2SdUcS11PeA1A4S0G0S3S2SdUeS51A4S0G0S3S2SdU11S4aA4S1G0A1A3A3A3A3A3A3Vregs;A3A2S53S18S7SdA1S4S10S0S10S2fS0S12S14SeN8A1Z8S11PbA1A3S1S12A1A3A1S0S10S2eVc0;A1S0S10S32Vtxt;A1S0S10S31Vtok;A1S0S10S30Vtl;A1S1S10A1A3A3A3A3A3S4fA3S4ScVfacts;S4ScS42S29A3A3Vnx;S6A9S35A2").

Definition regs1 (c : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S2SdA2M0S3S2SdUdVc;A4S0G0S3S2SdU10Vc;A4S0G0S3S2SdUfS20S21A1A4S0G0S3S2SdU5SeZ20A1A4S0G0S3S2SdU6SeZ9A1A4S1G0A1A3A3A3A3A3").
Definition C1 : axst := ltac2:(tb__ "0|1|
S39S64S49S20S23A1A1S20S26A1S1S12A1M0G0G0S38P87A8").

Definition regs2 (c : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S2SdA2M0S3S2SdU5Vc;A4S0G0S3S2SdUdVc;A4S0G0S3S2SdU10S20S23A1A4S0G0S3S2SdUfS20S21A1A4S0G0S3S2SdU6SeZ9A1A4S0G0S3S2SdU7SeZ20A1A4S1G0A1A3A3A3A3A3A3").

Definition C2f : axst := ltac2:(tb__ "0|3|
S39S63S41S20S23A1M0A1G0S0S12S14S23Z1S11P7aM1A1A3S1S12A1M2A3G2G2S4ScS48G1A1S38A3P87A8").
Definition C2 : axst := ltac2:(tb__ "0|1|
S39S63S41S36A1S36S1S12A1M0G0G0S47P87A8").

Definition v141 : sv := SVar 141.
Definition v142 : sv := SVar 142.
Definition v143 : sv := SVar 143.
Definition F_nf : list sprop := ltac2:(tb__ "0|0|
S0ScS1cS22S21A2S0ScSfS26S22A2S0ScSfS22S21A2S1ScA1A3A3A3").
Definition F_found : list sprop := ltac2:(tb__ "0|1|
S0ScSfS26S22A2S0ScS13S22S21A2S0ScS13S22S24A2S0ScS16S60S20S22A1S20S21A1A3S0ScSfSeZ1A1S2bA2S0ScS1cS19S5fS22S2bA3S25A2S0ScS13S22S25A2S0ScSfS25S21A2S0ScSfS25S24A2S0ScSfS22SeS2aA1M0A2S0ScSfS2bG0A2S0ScSfS25G0A2S1ScA1A3A3A3A3A3A3A3A3A3A3A3A3").

Definition post_objs (c0 : sv) (tok tl : list cell) : list sobj := ltac2:(tb__ "0|1|
S4S10S0S10S2fS0S12S14SeN8A1Z8S11PbA1A3S1S12A1M0A3A1S0S10S2eVc0;A1S0S10S32G0A1S0S10S31Vtok;A1S0S10S30Vtl;A1S1S10A1A3A3A3A3A3S4fA3").
Definition P_nf : axst := ltac2:(tb__ "0|3|
S50S1aS65S54S55S52A1S0S5S2SdA2M0S3S2SdUaSeZ0A1A4S0G0S3S2SdU10S20S22A1M1A4S1G0A1A3A3A2S53S18S7SdA1S40G1S1S12A1M2G2A3S4ScS44S29A3P90S6A9S35A2").
Definition P_found : axst := ltac2:(tb__ "0|5|
S50S1aS65S54S55S52A1S0S5S2SdA2M0S3S2SdUaSeZ1A1A4S0G0S3S2SdU10S20S22A1M1A4S1G0A1A3A3A2S53S18S7SdA1S40S20S25A1S0S12S14SeZ0A1M2Z8M3G1A3S1S12A1M4A3S0S12S14G2G3S2bA3G4A3A3S4ScS43S29A3P90S6A9S35A2").
Definition Posts_nt : list leafA := ltac2:(tb__ "0|0|
S0S5dS5eS34S68A2S0S5dS5eS33S68A2S1S5dA1A3A3").

Definition cuts_nt : list axst := ltac2:(tb__ "0|0|
S0S5cS28S0S5cS3aS0S5cS3cS0S5cS3bS1S5cA1A3A3A3A3").
Definition exits_nt : list axst := ltac2:(tb__ "0|0|
S0S5cS34S0S5cS33S1S5cA1A3A3").
Definition cutpcs_nt : list Z := ltac2:(tb__ "0|0|
S0S62S64S0S62S63S1S62A1A3A3").

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Definition check_nt__runs : ltac2:(tb__ "0|0|
S8SbS8S5dA1A1A1") := ltac2:(tb__ "0|0|
S72S4eS2dS37S3fA4").
Lemma check_nt : ltac2:(tb__ "0|0|
S67S9S5aS4eS2dS37S52S3fS45A6SaA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUEL_nt cutpcs_nt NF cuts_nt exits_nt check_nt__runs); [unfold check_nt__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem next_token_sum : ltac2:(tb__ "0|0|
S71OF_;S6bS1eS8S6eQ40A1A1S6dS4eR4R3A3S6cS4eS52R4A3S70S4eR6S6aS4eR5S28R4R3A5S69S4eR5S52R4R3S3dA6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_nt rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_nt cutpcs_nt NF cuts_nt exits_nt (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_nt) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_nt.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[]]].
    + apply exit_postA. in_nth 0.
    + apply exit_postA. in_nth 1.
  - left; reflexivity.
Qed.

Definition VD (w : sv) : sv := SAlu ALU_SUB vE w.
Definition vcuts_nt : list vnodeA := ltac2:(tb__ "0|1|
S0S58S59S28Z1eSeZ0A1A3S0S58S59S3aZ14S3eS23A1M0A3S0S58S59S3cZfG0A3S0S58S59S3bZaS3eS27A1A3S1S58A1A3A3A3A3").
Definition vexits_nt : list vnodeA := ltac2:(tb__ "0|2|
S0S58S59S34Z1M0SeZ0A1M1A3S0S58S59S33G0G1A3S1S58A1A3A3").

Lemma echeck_nt : ltac2:(tb__ "0|0|
S67S9S5bS4eS2dS37S52S4cS4dA6SaA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUEL_nt cutpcs_nt NF vcuts_nt vexits_nt check_nt__runs); [unfold check_nt__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem next_token_sum_ex : ltac2:(tb__ "0|0|
S6bS1eS8S6eQ40A1A1S6cS4eS52R3A3S6fS4eS6aS4eR4S28R3R2A5S69S4eR4S52R3R2S3dA6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_nt rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_nt with (vna_state (mkVNA Pre_nt 30 (SLit 0))).
  apply (cfg_complete_autoA segs FUEL_nt cutpcs_nt NF vcuts_nt vexits_nt (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_nt) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbv; congruence.
  - exact echeck_nt.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[]]].
    + apply (eexit_postA segs J NF rho vcuts_nt Posts_nt (mkVNA P_nf 1 (SLit 0))). in_nth 0.
    + apply (eexit_postA segs J NF rho vcuts_nt Posts_nt (mkVNA P_found 1 (SLit 0))). in_nth 1.
  - left; reflexivity.
Qed.
End Lib_next_token.

(* [comment removed for export] *)
Module StartNodes.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "valuation"; "eval"; "ss_next"; "ss_pc"; "rm"; "sprop"; "rw"; "sobj"; "SPUle"; "SVar"; "ss_objs"; "SPAlign"; "agree_below"; "obj_range"; "ranges_disjoint"; "ro_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "mkAX"; "ax_base"; "ax_X"; "shadow_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "prod"; "list"; "pair"; "bool"; "nil"; "true"; "cons"; "false"; "option"; "Some"; "app"; "None"; "fst"; "snd"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "sub"; "leb"; "ltb"; "modulo"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "event"; "vm_maps"; "vm_reserved"; "Model"; "iv_overlap"; "vm_init_sp"; "vm_limit"; "with_vmmaps"; "VmMaps"; "mkVmMapsFull"; "vm_brk"; "vm_mmap_base"; "vm_noaccess"; "vm_start_brk"; "vm_add_lazy"; "alloc_top"; "region_free"; "vm_backing_used"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "objs_clear_e"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes"; "LB_of"; "lazy_none_model"; "lazy_rw_model"; "eager_model"; "eager_ok"; "null_none_model"; "null_none_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "alloc_ceiling_lo"; "mmap_place_ok_none"; "alloc_ceiling_hi"; "init_sp_ok"; "mmap_place_ok"; "mmap_rw_vm"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "find_segment"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "mmap_obj"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes.EagerRw"; "eager_model"; "eager_facts"; "eager_h"; "eager_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_flags_core"; "mmap_modeled_b"; "mmap_noaccess_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes.LazyFixedNone"; "lazy_none_model"; "none_h";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes.LazyFixedRw"; "lazy_rw_h"; "lazy_rw_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes.LazyNullNone"; "null_none_facts"; "null_none_h"; "null_none_model"; "null_none_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartLib KxA Placement PlacementA SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma find_segment_none_A : ltac2:(tb__ "0|0|
S37S4S1S2fZ10000R1A2S31R1Z646000A2A2A1S0S29S78A1S6dS1dR2Z1A3S2cS78A1A3F_;Fz;").
Proof.
  intros z Hz. unfold segsA. cbn -[Z.leb Z.ltb Z.add Z.of_N].
  change (Z.of_N 65536%N) with 65536. change (Z.of_N 172032%N) with 172032.
  change (Z.of_N 237568%N) with 237568. change (Z.of_N 696320%N) with 696320.
  change (Z.of_N 933888%N) with 933888. change (Z.of_N 20480%N) with 20480.
  change (Z.of_N 954368%N) with 954368. change (Z.of_N 5623808%N) with 5623808.
  repeat match goal with |- context [if ?c then _ else _] =>
    destruct c eqn:?C; [apply andb_prop in C as [?C1 ?C2]; apply Z.leb_le in C1; apply Z.leb_le in C2; lia | clear C] end.
  reflexivity.
Qed.

Lemma u64_of_lit : ltac2:(tb__ "0|1|
S37S1S2fZ0R1A2S31R1S32Z2Z40A2A2A2S0S37S1fQ40M0S20G0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

Lemma region_free_of_forall : ltac2:(tb__ "0|2|
S22S21S1eQ40A1M0G0A2M1A1G0G0G0G0S4bG1S23G0G0R2R1A4R5A3S0S24S3dR5R4R3R2A4S28A3F_;Fs;Fb;S0S24S49R4R3R2A3S26A3F_;Fn;Fa;Fl;").
Proof.
  intros l a n H. induction l as [|[b s] l IH]; [reflexivity|]. cbn.
  rewrite (H b s (or_introl eq_refl)). cbn. apply IH. intros b' s' Hin. apply H. right. exact Hin.
Qed.

Lemma reserved_A_clear : ltac2:(tb__ "0|2|
S1eQ40M0A1M1G1G1G1S4bS21G1G1A2S23G1G1R2R1A4S54S1dA1A3S2fZ646000S1fG0R5A2A2S0S24S3dR6R5R4R3A4S28A3F_;F_;Fs;Fb;Fn;Fa;").
Proof.
  intros a n b s Hin Ha. rewrite segments_reserved_A in Hin.
  unfold iv_overlap. apply andb_false_iff. left. apply Z.ltb_ge.
  destruct Hin as [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]; rewrite !u64_of_lit by lia; lia.
Qed.
Lemma reserved_A_clear_lo : ltac2:(tb__ "0|2|
S1eQ40M0A1M1G1G1G1S4bS21G1G1A2S23G1G1R2R1A4S54S1dA1A3S2fS30S1fG0R5A2S1fG0R4A2A2Z10000A2S0S24S3dR6R5R4R3A4S28A3F_;F_;Fs;Fb;Fn;Fa;").
Proof.
  intros a n b s Hin Ha. rewrite segments_reserved_A in Hin.
  unfold iv_overlap. apply andb_false_iff. right. apply Z.ltb_ge.
  destruct Hin as [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]; rewrite !u64_of_lit by lia; lia.
Qed.

Definition LB_of (lenZ : Z) : Z := ltac2:(tb__ "0|1|
S24S37L_;M0S34S32Z2Z1fA2VlenZ;A2Z10007fff8000G0S35Zf000VlenZ;A2Z646000Z1000X24x2X24x2").

Lemma LB_of_range : ltac2:(tb__ "0|1|
S37S1S2fZ1000S5cR1A1M0A2S2fG0Z10007fff8000A2A2FlenZ;").
Proof. intros lenZ. unfold LB_of. destruct (2 ^ 31 <=? lenZ); [lia|]. destruct (0xf000 <? lenZ); lia. Qed.

Lemma place_LB_A : ltac2:(tb__ "0|8|
S3cS37S1eQ40M0A1M1S69S38R3A1A1S0S22S21G1G1A2M2A1S3bS38R4A1A1S54S1dA1A3S71S2bG2S3bS38R5A1M3A1S3aG3A1A3S70S6fA3S1S31Z0M4R5A2S31R5S32Z2Z3eA2A2A2S0S37S36R6Z1000A2G4A3S67S20G0G4A2R8S20G0R7A2R6A4S1S2fS5cR8A1S1fG0R7A2M5A2S1S2S2fS30G5R8A2M6Z10000A2S2fZ646000G5A2A2S1S2S2fG6S70A2S2fS6fG5A2A2S1S2fG6S48S38R9A1A1M7A2S2fG7S68A2A2A2A2A2F_;F_;F_;F_;F_;F_;Fa;FlenZ;Fm;").
Proof.
  intros m lenZ a Hsp Hres Hband Hlen Hmod Hpl.
  assert (Nv : bv_unsigned (Z_to_bv 64 lenZ) = lenZ) by (apply u64_of_lit; lia).
  assert (NZ : mmap_nZ (Z_to_bv 64 lenZ) = lenZ).
  { unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    pose proof Hmod as Hm'. apply Z.mod_divide in Hm' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (Himg : band_covered (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) IMG_BAND_LO IMG_BAND_HI).
  { apply img_band_covered. rewrite Hres. intros x Hx. apply in_app_iff. left. exact Hx. }
  destruct (place_ok_none_windows m Hsp Himg Hband (Z_to_bv 64 0) (Z_to_bv 64 lenZ) a Hpl ltac:(rewrite Nv; lia)) as (En & Ht & Hhi & W).
  rewrite NZ in Ht, W.
  unfold IMG_BAND_LO, IMG_BAND_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, alloc_ceiling_hi in *.
  unfold LB_of. destruct (Z.leb_spec (2 ^ 31) lenZ); [|destruct (Z.ltb_spec 0xf000 lenZ)]; (split; [|split; [|split]]); try lia.
Qed.

Lemma mmap_noaccess_b_intro_core : ltac2:(tb__ "0|3|
S1eQ40M0A1M1G1G1S0S37S1fG0R3A2Z0M2A3S0S37S7eR3A1Z22A3S0G1R3S20G0G2A2A3S1S0S24S80R6R5R4A3S26A3S0S24S7fR6R5R4A3S28A3A2F_;F_;F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off Hp Hf ->. unfold mmap_noaccess_b, mmap_modeled_b.
  rewrite Hp, Hf. unfold PROT_READ, PROT_WRITE, PROT_NONE, MAP_PRIVATE, MAP_ANONYMOUS. cbn.
  split; reflexivity.
Qed.

Section LazyFixedRw.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S4dS8S22S1eQ40A1A1S22S39A1M0S3cR5R4R3R2R1A4S0G0R3S25S39A1A3F_;Fmd;Ftr;Ftp;Frho;S4eS1dVok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S4dS8S22S1eQ40A1A1S22S39A1M0S3cR5R4R3R2R1A4S0G0R3S25S39A1A3F_;Fmd;Ftr;Ftp;Frho;S72S1dVok;R2A3F_;FJ;").

Variables (E : axst) (addrZ lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)).
Let a : word := Z_to_bv 64 addrZ.
Let n : word := Z_to_bv 64 lenZ.
Definition lazy_rw_h (md : Model) : VmMaps := ltac2:(tb__ "0|1|
S38Vmd;A1S41S42S3bR1A1S27S21S1eQ40A1M0G0A2S23G0G0Va;Vn;A4S3aR1A1A3S45R1A1S46R1A1S43R1A1S3fR1A1S44R1A1S3eR1A1A8Th;").
Definition lazy_rw_model (md : Model) : Model := ltac2:(tb__ "0|0|
S47Va;Vn;S40S83Vmd;A1Vmd;A2A3").

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S5S1aVE;A1S6S52A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S29S50A1S59S1dSbS18VE;A1A1A2S2aS50S51A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1Z11A2S6ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZaA2S6VaddrZ;A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZbA2S6VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZdA2S6Z4032A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZfA2S6Z0A1A3").
Hypothesis Hal : addrZ mod 4096 = 0.
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hlo : 0x646000 <= addrZ.
Hypothesis Hceil : ltac2:(tb__ "0|0|
S2fS30VaddrZ;VlenZ;A2S66A2").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S24S53VGl;S18VE;A1A2S26A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S22S21S1eQ40A1M0G0A2A1S3bS38Vm;A1A1S54S1dA1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|1|
S1eQ40A1M0G0S4bS21G0G0A2S23G0G0R2R1A4S3aS38Vm;A1A1A3S0S24S3dVa;Vn;R3R2A4S28A3F_;Fs;Fb;").

Lemma a_val : bv_unsigned a = addrZ.
Proof using Hceil Hlo Hpos. unfold alloc_ceiling_lo in Hceil. unfold a. apply u64_of_lit. lia. Qed.
Lemma n_val : bv_unsigned n = lenZ.
Proof using Hceil Hlo Hpos. unfold alloc_ceiling_lo in Hceil. unfold n. apply u64_of_lit. lia. Qed.

Theorem lazy_fixed_rw_node : ltac2:(tb__ "0|6|
S8S22S1eQ40M0A1A1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S2fS30VaddrZ;VlenZ;A2S1fG0S9R5R3A2A2M1A2S2fS30G1R2A2VaddrZ;A2A2F_;Fsz;Fe;S65S1dVok;S4cS1dS4fVm;VB;A2M2VE;R3R2A5S63S2S4cS1dG2S19S57S18VE;A1M3S58A2S25S21S5S5A2A1M4S6S52A1M5A3R4R3R1A6S4cS1dS4fS84Vm;A1VB;A2S19S57G3VaddrZ;A2G4G5A3S5bR4S5aScR4A1Va;Vn;A3A2R3R1A6A2Lw;A4F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG.
  pose proof a_val as Av. pose proof n_val as Nv. pose proof Hceil as CL. unfold alloc_ceiling_lo in CL.
  apply triple1_ecall_detA; [apply OKF; intros; eapply KxA_nil; eassumption | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold a in G0. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  destruct (mmap_fixed_rw_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnrw & Hnnone & Hnfn).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_16434. reflexivity. }
  { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    apply Z.mod_divide in Hnl as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  assert (Hceil' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, Av, HnZ', Evm; apply (alloc_top_ge_lo _ _ Htop); exact Hceil).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0, Av; exact Hal).
  assert (Hpos' : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0, Av; lia).
  assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true).
  { rewrite Evm. apply region_free_of_forall. exact Hmaps. }
  assert (Hfresh : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm. apply region_free_of_forall. intros b s Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite Hres in Hin. apply (reserved_A_clear a n b s Hin). rewrite Av. exact Hlo.
    - apply Hmaps. exact Hin. }
  split.
  - apply (OKP (KxA m B) ltac:(intros; eapply KxA_nil; eassumption) rho tp [] ms md (Z_to_bv 64 222));
      [split; [reflexivity|split; [exact Hem|exact Hpaid]] | exact Hp |].
    apply (fixed_rw_fresh_only_okA segsA ms md _ H222 Hlen Hshape Hnfn Hnnone Hnrw Hceil' Halign Hpos' Hfresh).
  - intros w' Hw.
    destruct (wstep_fixed_rw_fresh_invA segsA ms md _ Hh H222 Hlen Hshape Hnfn Hnnone Hnrw Hceil' Halign Hpos' Hfresh [] w' Hp Hw)
      as [-> | [Hb ->]].
    + left. split; [|split; [reflexivity|split; [exact Hem|exact Hpaid]]].
      change (mkAX (S_ret_lit (ax_S E) enomem_ret) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit (bv_unsigned (errno_ret ENOMEM))) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
      replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
      eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right.
      assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_16434; reflexivity).
      unfold mmap_rw_model, mmap_rw_vm, with_mmap_backing. rewrite Enr, HnZ, G0.
      split.
      * change (mkAX (S_ret_lit (ax_S E) addrZ) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit addrZ) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
        replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
        eapply (smatchA_after_grant_lazy segsA rho _ tp E [] ms md [] (lazy_rw_h md)); try exact Hsp.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- rewrite Av. exact Hal.
        -- rewrite Nv. exact Hnl.
        -- rewrite Nv. exact Hpos.
        -- rewrite Av, Nv. unfold two_pow_64 in CL. lia.
        -- exact Hfree_m.
        -- intros z Hz. apply find_segment_none_A. rewrite Av in Hz. lia.
        -- intros o Ho. rewrite Nv.
           apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
           ++ lia.
           ++ rewrite Av. left. exact CL.
           ++ intros x Hx. rewrite Av in Hx. lia.
           ++ intros e sz Hin x Hx. rewrite Av in Hx. destruct (HG e sz Hin); lia.
           ++ exact Ho.
        -- rewrite HX. intros rr y [] _.
        -- apply agree_below_refl.
        -- apply Pos.le_refl.
        -- reflexivity.
        -- cbn [eval]. rewrite <- Av. apply Z_to_bv_bv_unsigned.
      *
        assert (Hclr : tp_clear_of tp (lazy_interior a n)).
        { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
          rewrite Av, Nv. unfold two_pow_64 in CL. lia. }
        assert (Hpaid' : paid (lazy_rw_model md) tp <= B).
        { unfold lazy_rw_model. rewrite (paid_add_lazy (with_vmmaps (lazy_rw_h md) md) a n tp Hclr), paid_with_vmmaps.
          pose proof (used_rw_noreserve_le md (lazy_rw_h md) a n (MI_ivs_wf segsA _ _ HMI)
                        ltac:(rewrite Av; exact Hal) ltac:(rewrite Nv; exact Hnl) ltac:(rewrite Nv; exact Hpos)
                        ltac:(rewrite Av, Nv; unfold two_pow_64 in CL; lia) eq_refl eq_refl) as U.
          lia. }
        assert (Hem' : erase_mat (lazy_rw_model md) = erase_mat (lazy_rw_model m)).
        { unfold lazy_rw_model, lazy_rw_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
        split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End LazyFixedRw.

Section LazyFixedNone.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S4dS8S22S1eQ40A1A1S22S39A1M0S3cR5R4R3R2R1A4S0G0R3S25S39A1A3F_;Fmd;Ftr;Ftp;Frho;S4eS1dVok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S4dS8S22S1eQ40A1A1S22S39A1M0S3cR5R4R3R2R1A4S0G0R3S25S39A1A3F_;Fmd;Ftr;Ftp;Frho;S72S1dVok;R2A3F_;FJ;").

Variables (E : axst) (addrZ lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)).
Let a : word := Z_to_bv 64 addrZ.
Let n : word := Z_to_bv 64 lenZ.
Definition none_h (md : Model) : VmMaps := ltac2:(tb__ "0|3|
S38Vmd;A1S41S42S3bR1A1S27S21S1eQ40A1M0G0A2M1S23G0G0Va;Vn;A4M2S3aR1A1A3S27G1G2S45R1A1A3S46R1A1S43R1A1S3fR1A1S44R1A1S3eR1A1A8Th;").
Definition lazy_none_model (md : Model) : Model := ltac2:(tb__ "0|0|
S47Va;Vn;S40S82Vmd;A1Vmd;A2A3").

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S5S1aVE;A1S6S52A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S29S50A1S59S1dSbS18VE;A1A1A2S2aS50S51A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1Z11A2S6ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZaA2S6VaddrZ;A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZbA2S6VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZcA2S6Z0A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZdA2S6Z4032A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZfA2S6Z0A1A3").
Hypothesis Hal : addrZ mod 4096 = 0.
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hlo : 0x646000 <= addrZ.
Hypothesis Hceil : ltac2:(tb__ "0|0|
S2fS30VaddrZ;VlenZ;A2S66A2").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S24S53VGl;S18VE;A1A2S26A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S22S21S1eQ40A1M0G0A2A1S3bS38Vm;A1A1S54S1dA1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|1|
S1eQ40A1M0G0S4bS21G0G0A2S23G0G0R2R1A4S3aS38Vm;A1A1A3S0S24S3dVa;Vn;R3R2A4S28A3F_;Fs;Fb;").

Lemma a_valN : bv_unsigned a = addrZ.
Proof using Hceil Hlo Hpos. unfold alloc_ceiling_lo in Hceil. unfold a. apply u64_of_lit. lia. Qed.
Lemma n_valN : bv_unsigned n = lenZ.
Proof using Hceil Hlo Hpos. unfold alloc_ceiling_lo in Hceil. unfold n. apply u64_of_lit. lia. Qed.

Theorem lazy_fixed_none_node : ltac2:(tb__ "0|6|
S8S22S1eQ40M0A1A1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S2fS30VaddrZ;VlenZ;A2S1fG0S9R5R3A2A2M1A2S2fS30G1R2A2VaddrZ;A2A2F_;Fsz;Fe;S65S1dVok;S4cS1dS4fVm;VB;A2M2VE;R3R2A5S63S2S4cS1dG2S19S57S18VE;A1M3S58A2S25S21S5S5A2A1M4S6S52A1M5A3R4R3R1A6S4cS1dS4fS81Vm;A1VB;A2S19S57G3VaddrZ;A2G4G5A3S5bR4S5aScR4A1Va;Vn;A3A2R3R1A6A2Lw;A4F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG.
  pose proof a_valN as Av. pose proof n_valN as Nv. pose proof Hceil as CL. unfold alloc_ceiling_lo in CL.
  apply triple1_ecall_detA; [apply OKF; intros; eapply KxA_nil; eassumption | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold a in G0. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  destruct (mmap_fixed_none_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnrw & Hnnone).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_16434. reflexivity. }
  { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    apply Z.mod_divide in Hnl as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  assert (Hceil' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, Av, HnZ', Evm; apply (alloc_top_ge_lo _ _ Htop); exact Hceil).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0, Av; exact Hal).
  assert (Hpos' : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0, Av; lia).
  assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true).
  { rewrite Evm. apply region_free_of_forall. exact Hmaps. }
  assert (Hfresh : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm. apply region_free_of_forall. intros b s Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite Hres in Hin. apply (reserved_A_clear a n b s Hin). rewrite Av. exact Hlo.
    - apply Hmaps. exact Hin. }
  split.
  - apply (OKP (KxA m B) ltac:(intros; eapply KxA_nil; eassumption) rho tp [] ms md (Z_to_bv 64 222));
      [split; [reflexivity|split; [exact Hem|exact Hpaid]] | exact Hp |].
    apply (fixed_none_fresh_only_okA segsA ms md _ H222 Hlen Hshape Hnnone Hnrw Hceil' Halign Hpos' Hfresh).
  - intros w' Hw.
    destruct (wstep_fixed_none_fresh_invA segsA ms md _ Hh H222 Hlen Hshape Hnnone Hnrw Hceil' Halign Hpos' Hfresh [] w' Hp Hw)
      as [-> | ->].
    + left. split; [|split; [reflexivity|split; [exact Hem|exact Hpaid]]].
      change (mkAX (S_ret_lit (ax_S E) enomem_ret) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit (bv_unsigned (errno_ret ENOMEM))) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
      replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
      eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right.
      assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_16434; reflexivity).
      unfold mmap_none_model, mmap_none_vm. rewrite HnZ, G0.
      split.
      * change (mkAX (S_ret_lit (ax_S E) addrZ) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit addrZ) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
        replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
        eapply (smatchA_after_grant_none segsA rho _ tp E [] ms md [] (none_h md)); try exact Hsp.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- rewrite Av. exact Hal.
        -- rewrite Nv. exact Hnl.
        -- rewrite Nv. exact Hpos.
        -- rewrite Av, Nv. unfold two_pow_64 in CL. lia.
        -- exact Hfree_m.
        -- intros z Hz. apply find_segment_none_A. rewrite Av in Hz. lia.
        -- intros o Ho. rewrite Nv.
           apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
           ++ lia.
           ++ rewrite Av. left. exact CL.
           ++ intros x Hx. rewrite Av in Hx. lia.
           ++ intros e sz Hin x Hx. rewrite Av in Hx. destruct (HG e sz Hin); lia.
           ++ exact Ho.
        -- rewrite HX. intros rr y [] _.
        -- apply agree_below_refl.
        -- apply Pos.le_refl.
        -- reflexivity.
        -- cbn [eval]. rewrite <- Av. apply Z_to_bv_bv_unsigned.
      * assert (Hclr : tp_clear_of tp (lazy_interior a n)).
        { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
          rewrite Av, Nv. unfold two_pow_64 in CL. lia. }
        assert (Hpaid' : paid (lazy_none_model md) tp <= B).
        { unfold lazy_none_model. rewrite (paid_add_lazy (with_vmmaps (none_h md) md) a n tp Hclr), paid_with_vmmaps.
          pose proof (used_add_lazy_le (with_vmmaps (none_h md) md) a n) as U1.
          pose proof (used_none_cons_le md (none_h md) a n (MI_ivs_wf segsA _ _ HMI)) as U2.
          assert (Hiv : iv_wf (a, n)) by (unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Av, Nv; unfold two_pow_64 in CL; lia).
          assert (Hwf1 : model_ivs_wf (with_vmmaps (none_h md) md)).
          { pose proof (MI_ivs_wf segsA _ _ HMI) as (W1 & W2 & W3). unfold model_ivs_wf. unfold none_h.
            rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps. cbn [vm_maps vm_noaccess].
            split; [apply ivs_wf_cons; assumption|]. split; [apply ivs_wf_cons; assumption|]. exact W3. }
          specialize (U1 Hwf1 ltac:(rewrite Av, Nv; unfold two_pow_64 in CL; lia)).
          specialize (U2 Hiv eq_refl eq_refl). lia. }
        assert (Hem' : erase_mat (lazy_none_model md) = erase_mat (lazy_none_model m)).
        { unfold lazy_none_model, none_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
        unfold with_mmap_backing. rewrite Enr.
        split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End LazyFixedNone.

Section LazyNullNone.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S4dS8S22S1eQ40A1A1S22S39A1M0S3cR5R4R3R2R1A4S0G0R3S25S39A1A3F_;Fmd;Ftr;Ftp;Frho;S4eS1dVok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S4dS8S22S1eQ40A1A1S22S39A1M0S3cR5R4R3R2R1A4S0G0R3S25S39A1A3F_;Fmd;Ftr;Ftp;Frho;S72S1dVok;R2A3F_;FJ;").

Variables (E : axst) (lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)) (nxt : positive).
Let n : word := Z_to_bv 64 lenZ.
Definition null_none_h (md : Model) (a : word) : VmMaps := ltac2:(tb__ "0|3|
S38Vmd;A1S41S42S3bR1A1S27S21S1eQ40A1M0G0A2M1S23G0G0Va;Vn;A4M2S3aR1A1A3S27G1G2S45R1A1A3S46R1A1S43R1A1S3fR1A1S44R1A1S3eR1A1A8Th;").
Definition null_none_model (md : Model) (a : word) : Model := ltac2:(tb__ "0|0|
S47Va;Vn;S40S86Vmd;Va;A2Vmd;A2A3").

Definition null_none_facts : list sprop := ltac2:(tb__ "0|2|
S27SdS13SaS18VE;A1A1M0ZcA2S27SdS10S6S5cVlenZ;A1A1S11G0A1M1A2S27SdS10G1S6S33S68VlenZ;A2A1A2S25SdA1A3A3A3").
Definition null_none_ok : axst := ltac2:(tb__ "0|1|
S19S7dS85S76S18VE;A1M0S11SaG0A1A1S12G0A1Vnxt;A4A2S25S21S5S5A2A1S6S52A1A3").

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S5S1aVE;A1S6S52A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S29S50A1S59S1dSbS18VE;A1A1A2S2aS50S51A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1Z11A2S6ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZaA2S6Z0A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZbA2S6VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZcA2S6Z0A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZdA2S6Z4022A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZfA2S6Z0A1A3").
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hsmall : lenZ < 2 ^ 62.
Hypothesis Hnxt : ltac2:(tb__ "0|0|
S74SaS18VE;A1A1Vnxt;A2").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S24S53VGl;S18VE;A1A2S26A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S22S21S1eQ40A1M0G0A2A1S3bS38Vm;A1A1S54S1dA1A3").

Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
S71S2bS21S1eQ40A1M0G0A2S3bS38Vm;A1M1A1S3aG1A1A3S70S6fA3").

Variable rho_of : ltac2:(tb__ "0|0|
S8S1eQ40A1S8F_;F_;").
Hypothesis Hrho_ag : ltac2:(tb__ "0|0|
S8S1eQ40A1S14SaS18VE;A1A1S5bR2S5aScR2A1R1Vn;A3A2Vrho_of;R2R1A2A3Fa;Frho;").
Hypothesis Hrho_at : ltac2:(tb__ "0|1|
S8S1eQ40A1M0S0G0SeVrho_of;R2R1A2SaS18VE;A1A1A2R1A3Fa;Frho;").

Lemma n_valU : bv_unsigned n = lenZ.
Proof using Hpos Hsmall. unfold n. apply u64_of_lit. clear -Hpos Hsmall. lia. Qed.

Theorem lazy_null_none_node : ltac2:(tb__ "0|6|
S8S22S1eQ40M0A1M1A1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S3G1G1S3G1G1S1S4bS21G1G1A2S23G1G1R2R1A4S3aS38Vm;A1M2A1A3S1S2fS1fG0R2A2M3S1fG0S9R7R5A2A2M4A2S2fS30G4R4A2S30G3S1fG0R1A2A2A2A2A2Ls;A2Lb;A2S2fS30S1fG0S9R5R3A2A2R2A2S5cVlenZ;A1A2A2F_;Fsz;Fe;S0S37S1fG0SeR3P1A2A2S1fG0S3eG2A1A2A3S65S1dVok;S4cS1dS4fVm;VB;A2M5VE;R4R3A5S63S2S4cS1dG5S19S57S18VE;A1S58A2S25S21S5S5A2A1S6S52A1A3R5R4R1A6S3G1G1S1S67S20G0Z0A2Vm;Vn;R1A4S4cS1dS4fS87Vm;R1A2VB;A2S88Vrho_of;R6R1A2R5R2A6A2La;A2A2Lw;A4F_;F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG Hv1.
  pose proof n_valU as Nv. pose proof (alloc_top_lt (m_vmmaps m)) as CL.
  apply triple1_ecall_detA; [apply OKF; intros; eapply KxA_nil; eassumption | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_swf segsA _ _ _ _ Hsp) as Hswf.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  destruct (mmap_noaccess_b_intro_core (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnrw).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_16418. reflexivity. }
  { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    pose proof Hnl as Hnl'. apply Z.mod_divide in Hnl' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  split.
  - apply (OKP (KxA m B) ltac:(intros; eapply KxA_nil; eassumption) rho tp [] ms md (Z_to_bv 64 222));
      [split; [reflexivity|split; [exact Hem|exact Hpaid]] | exact Hp |].
    apply (mmap_none_only_okA segsA ms md _ Hh H222 Hlen Hshape Hnrw).
  - intros w' Hw.
    destruct (wstep_mmap_none_invA segsA ms md _ Hh H222 Hlen Hshape Hnrw [] w' Hp Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|split; [reflexivity|split; [exact Hem|exact Hpaid]]].
      change (mkAX (S_ret_lit (ax_S E) enomem_ret) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit (bv_unsigned (errno_ret ENOMEM))) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
      replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
      eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right. exists a.
      rewrite G0, G1 in Hpl.
      assert (HnZn : mmap_nZ n = lenZ) by (rewrite <- G1; exact HnZ').
      assert (Hmn : mmap_n n = n) by (rewrite <- G1 at 1; exact HnZ).
      assert (Hplm : mmap_place_ok_none (Z_to_bv 64 0) m n a).
      { unfold mmap_place_ok_none in Hpl |- *. rewrite Evm in Hpl. exact Hpl. }
      split; [exact Hplm|].
      pose proof Hpl as (Pal & Ppos & Pceil & Pfree). rewrite HnZn in Pceil. rewrite Hmn in Pfree. rewrite Evm in Pceil.
      pose proof (place_LB_A m lenZ a Htop Hres Hband ltac:(lia) Hnl Hplm) as (PLB & Pimg & Pband & Ptop & Phi).
      assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true) by exact (region_free_app_r _ _ _ _ Pfree).
      assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_16418; reflexivity).
      unfold mmap_none_model, mmap_none_vm. rewrite HnZ.
      set (rho' := rho_of rho a).
      split.
      * unfold null_none_ok.
        assert (SM : smatchA segsA rho' tp (ax_setS E (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E)) nxt))
                       ([], mkCfg (after_sys_mem ms a (unmap_range (ms_mem ms) a n)) (with_mmap_backing (ms_gpr ms 3) a n (with_vmmaps (null_none_h md a) md)))).
        { eapply (smatchA_after_grant_none segsA rho rho' tp E [] ms md [] (null_none_h md a)); try exact Hsp.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- exact Pal.
          -- rewrite Nv. exact Hnl.
          -- rewrite Nv. exact Hpos.
          -- rewrite Nv. unfold two_pow_64 in CL. lia.
          -- exact Hfree_m.
          -- intros z Hz. apply find_segment_none_A. rewrite Nv in Hz. lia.
          -- intros o Ho. rewrite Nv.
             apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
             ++ lia.
             ++ right. revert Pceil. unfold alloc_top. rewrite stack_max_size_val, <- Hv1. intros Pceil. exact Pceil.
             ++ intros x Hx. lia.
             ++ intros e sz Hin x Hx Hblk. destruct (HG e sz Hin) as [(b & s0 & Hm & Hb1 & Hb2) | Hlow]; [|lia].
                pose proof (region_free_In _ _ _ _ _ Hfree_m ltac:(rewrite Evm; exact Hm)) as R.
                unfold iv_overlap in R. rewrite Nv in R.
                apply andb_false_iff in R. destruct R as [R|R]; apply Z.ltb_ge in R; lia.
             ++ exact Ho.
          -- rewrite HX. intros rr y [] _.
          -- subst rho'. apply Hrho_ag.
          -- lia.
          -- cbn. apply Pos.ltb_lt. exact Hnxt.
          -- subst rho'. cbn [eval]. apply Hrho_at. }

        replace E with (mkAX (ax_S E) [] (SLit SHB)) in SM by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
        destruct SM as (Ssm & SMI & Swf & Ssh & Shz). cbn [ax_S ax_setS ax_X ax_base] in Ssm, Swf, Ssh.
        split; [|split; [exact SMI|split; [|split; [|exact Shz]]]].
        -- cbn [ax_S]. apply smatch_add_facts; [exact Ssm| |].
           ++ unfold null_none_facts. assert (E1 : rw rho' (ss_next (ax_S E)) = a) by (subst rho'; apply Hrho_at).
              repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
              ** change (2 ^ 12) with 4096. split; [lia|exact Pal].
              ** rewrite u64_of_lit by (pose proof (LB_of_range lenZ); lia). exact PLB.
              ** unfold alloc_ceiling_hi in *. rewrite u64_of_lit by lia. lia.
           ++ assert (X : (ss_next (ax_S E) <? nxt)%positive = true) by (apply Pos.ltb_lt; exact Hnxt). cbn. rewrite !X. reflexivity.
        -- unfold axwf in Swf |- *. cbn [ax_S ax_X ax_base ss_next add_facts] in Swf |- *. exact Swf.
        -- unfold shadow_ok. cbn. constructor.
      * assert (Hclr : tp_clear_of tp (lazy_interior a n)).
        { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
          rewrite Nv. unfold two_pow_64 in CL. lia. }
        assert (Hpaid' : paid (null_none_model md a) tp <= B).
        { unfold null_none_model. rewrite (paid_add_lazy (with_vmmaps (null_none_h md a) md) a n tp Hclr), paid_with_vmmaps.
          pose proof (used_add_lazy_le (with_vmmaps (null_none_h md a) md) a n) as U1.
          pose proof (used_none_cons_le md (null_none_h md a) a n (MI_ivs_wf segsA _ _ HMI)) as U2.
          assert (Hiv : iv_wf (a, n)) by (unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Nv; unfold two_pow_64 in CL; lia).
          assert (Hwf1 : model_ivs_wf (with_vmmaps (null_none_h md a) md)).
          { pose proof (MI_ivs_wf segsA _ _ HMI) as (W1 & W2 & W3). unfold model_ivs_wf. unfold null_none_h.
            rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps. cbn [vm_maps vm_noaccess].
            split; [apply ivs_wf_cons; assumption|]. split; [apply ivs_wf_cons; assumption|]. exact W3. }
          specialize (U1 Hwf1 ltac:(rewrite Nv; unfold two_pow_64 in CL; lia)).
          specialize (U2 Hiv eq_refl eq_refl). lia. }
        assert (Hem' : erase_mat (null_none_model md a) = erase_mat (null_none_model m a)).
        { unfold null_none_model, null_none_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
        unfold with_mmap_backing. rewrite Enr.
        split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End LazyNullNone.

Section ELazyFixedRw.
Variables (E : axst) (addrZ lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)).
Let a : word := Z_to_bv 64 addrZ.
Let n : word := Z_to_bv 64 lenZ.
Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S5S1aVE;A1S6S52A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S29S50A1S59S1dSbS18VE;A1A1A2S2aS50S51A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1Z11A2S6ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZaA2S6VaddrZ;A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZbA2S6VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZdA2S6Z4032A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZfA2S6Z0A1A3").
Hypothesis Hal : addrZ mod 4096 = 0.
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hlo : 0x646000 <= addrZ.
Hypothesis Hceil : ltac2:(tb__ "0|0|
S2fS30VaddrZ;VlenZ;A2S66A2").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S24S53VGl;S18VE;A1A2S26A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S22S21S1eQ40A1M0G0A2A1S3bS38Vm;A1A1S54S1dA1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|1|
S1eQ40A1M0G0S4bS21G0G0A2S23G0G0R2R1A4S3aS38Vm;A1A1A3S0S24S3dVa;Vn;R3R2A4S28A3F_;Fs;Fb;").

Theorem lazy_fixed_rw_enode : ltac2:(tb__ "0|2|
S8S22S1eQ40M0A1A1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S2fS30VaddrZ;VlenZ;A2S1fG0S9R5R3A2A2M1A2S2fS30G1R2A2VaddrZ;A2A2F_;Fsz;Fe;S64S1dS4cS1dS4fVm;VB;A2VE;R3R2A5S4cS1dS4fS5eVaddrZ;VlenZ;Vm;A3VB;A2S19S57S18VE;A1VaddrZ;A2S25S21S5S5A2A1S6S52A1A3S5bR3S5aScR3A1Va;Vn;A3A2R2A5A3F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG.
  assert (Av : bv_unsigned a = addrZ) by (clear -Hceil Hlo Hpos; unfold alloc_ceiling_lo in Hceil; unfold a; apply u64_of_lit; lia).
  assert (Nv : bv_unsigned n = lenZ) by (clear -Hceil Hlo Hpos; unfold alloc_ceiling_lo in Hceil; unfold n; apply u64_of_lit; lia).
  pose proof Hceil as CL. unfold alloc_ceiling_lo in CL.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold a in G0. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  destruct (mmap_fixed_rw_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnrw & Hnnone & Hnfn).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_16434. reflexivity. }
  { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    pose proof Hnl as Hnl'. apply Z.mod_divide in Hnl' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  assert (Hceil' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, Av, HnZ', Evm; apply (alloc_top_ge_lo _ _ Htop); exact Hceil).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0, Av; exact Hal).
  assert (Hpos' : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0, Av; lia).
  assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true).
  { rewrite Evm. apply region_free_of_forall. exact Hmaps. }
  assert (Hfresh : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm. apply region_free_of_forall. intros b s Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite Hres in Hin. apply (reserved_A_clear a n b s Hin). rewrite Av. exact Hlo.
    - apply Hmaps. exact Hin. }
  assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_16434; reflexivity).
  assert (Hb : mmap_noreserve_backed_ok (ms_gpr ms 3) md (mmap_nZ (ms_gpr ms 1)) = true) by (unfold mmap_noreserve_backed_ok; rewrite Enr; reflexivity).
  eexists. split.
  { exact (wstep_fixed_rw_fresh_intro_okA segsA ms md _ Hh H222 Hlen Hshape Hnfn Hnnone Hnrw Hceil' Halign Hpos' Hfresh [] Hp Hb). }
  unfold mmap_rw_model, mmap_rw_vm, with_mmap_backing. rewrite Enr, HnZ, G0.
  split.
  * change (mkAX (S_ret_lit (ax_S E) addrZ) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit addrZ) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
    replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
    eapply (smatchA_after_grant_lazy segsA rho _ tp E [] ms md [] (lazy_rw_h addrZ lenZ md)); try exact Hsp.
    -- reflexivity.
    -- reflexivity.
    -- reflexivity.
    -- rewrite Av. exact Hal.
    -- rewrite Nv. exact Hnl.
    -- rewrite Nv. exact Hpos.
    -- rewrite Av, Nv. unfold two_pow_64 in CL. lia.
    -- exact Hfree_m.
    -- intros z Hz. apply find_segment_none_A. rewrite Av in Hz. lia.
    -- intros o Ho. rewrite Nv.
       apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
       ++ lia.
       ++ rewrite Av. left. exact CL.
       ++ intros x Hx. rewrite Av in Hx. lia.
       ++ intros e sz Hin x Hx. rewrite Av in Hx. destruct (HG e sz Hin); lia.
       ++ exact Ho.
    -- rewrite HX. intros rr y [] _.
    -- apply agree_below_refl.
    -- apply Pos.le_refl.
    -- reflexivity.
    -- cbn [eval]. rewrite <- Av. apply Z_to_bv_bv_unsigned.
  * assert (Hclr : tp_clear_of tp (lazy_interior a n)).
    { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
      rewrite Av, Nv. unfold two_pow_64 in CL. lia. }
    assert (Hpaid' : paid (lazy_rw_model addrZ lenZ md) tp <= B).
    { unfold lazy_rw_model. fold a n. rewrite (paid_add_lazy (with_vmmaps (lazy_rw_h addrZ lenZ md) md) a n tp Hclr), paid_with_vmmaps.
      pose proof (used_rw_noreserve_le md (lazy_rw_h addrZ lenZ md) a n (MI_ivs_wf segsA _ _ HMI)
                    ltac:(rewrite Av; exact Hal) ltac:(rewrite Nv; exact Hnl) ltac:(rewrite Nv; exact Hpos)
                    ltac:(rewrite Av, Nv; unfold two_pow_64 in CL; lia) eq_refl eq_refl) as U.
      lia. }
    assert (Hem' : erase_mat (lazy_rw_model addrZ lenZ md) = erase_mat (lazy_rw_model addrZ lenZ m)).
    { unfold lazy_rw_model, lazy_rw_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
    split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End ELazyFixedRw.

Section ELazyFixedNone.
Variables (E : axst) (addrZ lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)).
Let a : word := Z_to_bv 64 addrZ.
Let n : word := Z_to_bv 64 lenZ.
Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S5S1aVE;A1S6S52A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S29S50A1S59S1dSbS18VE;A1A1A2S2aS50S51A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1Z11A2S6ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZaA2S6VaddrZ;A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZbA2S6VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZcA2S6Z0A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZdA2S6Z4032A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZfA2S6Z0A1A3").
Hypothesis Hal : addrZ mod 4096 = 0.
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hlo : 0x646000 <= addrZ.
Hypothesis Hceil : ltac2:(tb__ "0|0|
S2fS30VaddrZ;VlenZ;A2S66A2").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S24S53VGl;S18VE;A1A2S26A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S22S21S1eQ40A1M0G0A2A1S3bS38Vm;A1A1S54S1dA1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|1|
S1eQ40A1M0G0S4bS21G0G0A2S23G0G0R2R1A4S3aS38Vm;A1A1A3S0S24S3dVa;Vn;R3R2A4S28A3F_;Fs;Fb;").

Theorem lazy_fixed_none_enode : ltac2:(tb__ "0|2|
S8S22S1eQ40M0A1A1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S2fS30VaddrZ;VlenZ;A2S1fG0S9R5R3A2A2M1A2S2fS30G1R2A2VaddrZ;A2A2F_;Fsz;Fe;S64S1dS4cS1dS4fVm;VB;A2VE;R3R2A5S4cS1dS4fS5dVaddrZ;VlenZ;Vm;A3VB;A2S19S57S18VE;A1VaddrZ;A2S25S21S5S5A2A1S6S52A1A3S5bR3S5aScR3A1Va;Vn;A3A2R2A5A3F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG.
  assert (Av : bv_unsigned a = addrZ) by (clear -Hceil Hlo Hpos; unfold alloc_ceiling_lo in Hceil; unfold a; apply u64_of_lit; lia).
  assert (Nv : bv_unsigned n = lenZ) by (clear -Hceil Hlo Hpos; unfold alloc_ceiling_lo in Hceil; unfold n; apply u64_of_lit; lia).
  pose proof Hceil as CL. unfold alloc_ceiling_lo in CL.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold a in G0. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  destruct (mmap_fixed_none_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnrw & Hnnone).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_16434. reflexivity. }
  { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    pose proof Hnl as Hnl'. apply Z.mod_divide in Hnl' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  assert (Hceil' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, Av, HnZ', Evm; apply (alloc_top_ge_lo _ _ Htop); exact Hceil).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0, Av; exact Hal).
  assert (Hpos' : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0, Av; lia).
  assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true).
  { rewrite Evm. apply region_free_of_forall. exact Hmaps. }
  assert (Hfresh : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm. apply region_free_of_forall. intros b s Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite Hres in Hin. apply (reserved_A_clear a n b s Hin). rewrite Av. exact Hlo.
    - apply Hmaps. exact Hin. }
  assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_16434; reflexivity).
  eexists. split.
  { exact (wstep_fixed_none_fresh_intro_okA segsA ms md _ Hh H222 Hlen Hshape Hnnone Hnrw Hceil' Halign Hpos' Hfresh [] Hp). }
  unfold mmap_none_model, mmap_none_vm. rewrite HnZ, G0.
  split.
  * change (mkAX (S_ret_lit (ax_S E) addrZ) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit addrZ) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
    replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
    eapply (smatchA_after_grant_none segsA rho _ tp E [] ms md [] (none_h addrZ lenZ md)); try exact Hsp.
    -- reflexivity.
    -- reflexivity.
    -- reflexivity.
    -- rewrite Av. exact Hal.
    -- rewrite Nv. exact Hnl.
    -- rewrite Nv. exact Hpos.
    -- rewrite Av, Nv. unfold two_pow_64 in CL. lia.
    -- exact Hfree_m.
    -- intros z Hz. apply find_segment_none_A. rewrite Av in Hz. lia.
    -- intros o Ho. rewrite Nv.
       apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
       ++ lia.
       ++ rewrite Av. left. exact CL.
       ++ intros x Hx. rewrite Av in Hx. lia.
       ++ intros e sz Hin x Hx. rewrite Av in Hx. destruct (HG e sz Hin); lia.
       ++ exact Ho.
    -- rewrite HX. intros rr y [] _.
    -- apply agree_below_refl.
    -- apply Pos.le_refl.
    -- reflexivity.
    -- cbn [eval]. rewrite <- Av. apply Z_to_bv_bv_unsigned.
  * assert (Hclr : tp_clear_of tp (lazy_interior a n)).
    { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
      rewrite Av, Nv. unfold two_pow_64 in CL. lia. }
    assert (Hpaid' : paid (lazy_none_model addrZ lenZ md) tp <= B).
    { unfold lazy_none_model. fold a n. rewrite (paid_add_lazy (with_vmmaps (none_h addrZ lenZ md) md) a n tp Hclr), paid_with_vmmaps.
      pose proof (used_add_lazy_le (with_vmmaps (none_h addrZ lenZ md) md) a n) as U1.
      pose proof (used_none_cons_le md (none_h addrZ lenZ md) a n (MI_ivs_wf segsA _ _ HMI)) as U2.
      assert (Hiv : iv_wf (a, n)) by (unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Av, Nv; unfold two_pow_64 in CL; lia).
      assert (Hwf1 : model_ivs_wf (with_vmmaps (none_h addrZ lenZ md) md)).
      { pose proof (MI_ivs_wf segsA _ _ HMI) as (W1 & W2 & W3). unfold model_ivs_wf. unfold none_h.
        rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps. cbn [vm_maps vm_noaccess].
        split; [apply ivs_wf_cons; assumption|]. split; [apply ivs_wf_cons; assumption|]. exact W3. }
      specialize (U1 Hwf1 ltac:(rewrite Av, Nv; unfold two_pow_64 in CL; lia)).
      specialize (U2 Hiv eq_refl eq_refl). lia. }
    assert (Hem' : erase_mat (lazy_none_model addrZ lenZ md) = erase_mat (lazy_none_model addrZ lenZ m)).
    { unfold lazy_none_model, none_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
    unfold with_mmap_backing. rewrite Enr.
    split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End ELazyFixedNone.

Section ELazyNullNone.
Variables (E : axst) (lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)) (nxt : positive).
Let n : word := Z_to_bv 64 lenZ.
Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S5S1aVE;A1S6S52A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S29S50A1S59S1dSbS18VE;A1A1A2S2aS50S51A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1Z11A2S6ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZaA2S6Z0A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZbA2S6VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZcA2S6Z0A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZdA2S6Z4022A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZfA2S6Z0A1A3").
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hsmall : lenZ < 2 ^ 62.
Hypothesis Hnxt : ltac2:(tb__ "0|0|
S74SaS18VE;A1A1Vnxt;A2").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S24S53VGl;S18VE;A1A2S26A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S22S21S1eQ40A1M0G0A2A1S3bS38Vm;A1A1S54S1dA1A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
S71S2bS21S1eQ40A1M0G0A2S3bS38Vm;A1M1A1S3aG1A1A3S70S6fA3").
Variable rho_of : ltac2:(tb__ "0|0|
S8S1eQ40A1S8F_;F_;").
Hypothesis Hrho_ag : ltac2:(tb__ "0|0|
S8S1eQ40A1S14SaS18VE;A1A1S5bR2S5aScR2A1R1Vn;A3A2Vrho_of;R2R1A2A3Fa;Frho;").
Hypothesis Hrho_at : ltac2:(tb__ "0|1|
S8S1eQ40A1M0S0G0SeVrho_of;R2R1A2SaS18VE;A1A1A2R1A3Fa;Frho;").

Hypothesis Hwit : ltac2:(tb__ "0|2|
S3S1eQ40M0A1M1G1S67S20G0Z0A2Vm;Vn;R1A4La;A2").

Theorem lazy_null_none_enode : ltac2:(tb__ "0|5|
S8S22S1eQ40M0A1M1A1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S3G1G1S3G1G1S1S4bS21G1G1A2S23G1G1R2R1A4S3aS38Vm;A1M2A1A3S1S2fS1fG0R2A2M3S1fG0S9R7R5A2A2M4A2S2fS30G4R4A2S30G3S1fG0R1A2A2A2A2A2Ls;A2Lb;A2S2fS30S1fG0S9R5R3A2A2R2A2S5cVlenZ;A1A2A2F_;Fsz;Fe;S0S37S1fG0SeR3P1A2A2S1fG0S3eG2A1A2A3S64S1dS4cS1dS4fVm;VB;A2VE;R4R3A5S63S3G1G1S1S67S20G0Z0A2Vm;Vn;R1A4S4cS1dS4fS61VlenZ;Vm;R1A3VB;A2S62VE;VlenZ;Vnxt;A3Vrho_of;R6R1A2R5R2A6A2La;A2Lw;A3F_;F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG Hv1.
  assert (Nv : bv_unsigned n = lenZ) by (unfold n; apply u64_of_lit; clear -Hpos Hsmall; lia).
  pose proof (alloc_top_lt (m_vmmaps m)) as CL.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_swf segsA _ _ _ _ Hsp) as Hswf.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  destruct (mmap_noaccess_b_intro_core (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnrw).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_16418. reflexivity. }
  { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    pose proof Hnl as Hnl'. apply Z.mod_divide in Hnl' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  destruct Hwit as [a Hplm].
  assert (Hpl : mmap_place_ok_none (ms_gpr ms 0) md (ms_gpr ms 1) a).
  { rewrite G0, G1. unfold mmap_place_ok_none in Hplm |- *. rewrite Evm. exact Hplm. }
  eexists. split.
  { exact (wstep_mmap_none_intro_okA segsA ms md _ Hh H222 Hlen Hshape Hnrw [] a Hp Hpl). }
  exists a. split; [exact Hplm|].
  rewrite G0, G1 in Hpl.
  assert (HnZn : mmap_nZ n = lenZ) by (rewrite <- G1; exact HnZ').
  assert (Hmn : mmap_n n = n) by (rewrite <- G1 at 1; exact HnZ).
  pose proof Hpl as (Pal & Ppos & Pceil & Pfree). rewrite HnZn in Pceil. rewrite Hmn in Pfree. rewrite Evm in Pceil.
  pose proof (place_LB_A m lenZ a Htop Hres Hband ltac:(lia) Hnl Hplm) as (PLB & Pimg & Pband & Ptop & Phi).
  assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true) by exact (region_free_app_r _ _ _ _ Pfree).
  assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_16418; reflexivity).
  unfold mmap_none_model, mmap_none_vm. rewrite HnZ.
  set (rho' := rho_of rho a).
  split.
  * unfold null_none_ok.
    assert (SM : smatchA segsA rho' tp (ax_setS E (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E)) nxt))
                   ([], mkCfg (after_sys_mem ms a (unmap_range (ms_mem ms) a n)) (with_mmap_backing (ms_gpr ms 3) a n (with_vmmaps (null_none_h lenZ md a) md)))).
    { eapply (smatchA_after_grant_none segsA rho rho' tp E [] ms md [] (null_none_h lenZ md a)); try exact Hsp.
      -- reflexivity.
      -- reflexivity.
      -- reflexivity.
      -- exact Pal.
      -- rewrite Nv. exact Hnl.
      -- rewrite Nv. exact Hpos.
      -- rewrite Nv. unfold two_pow_64 in CL. lia.
      -- exact Hfree_m.
      -- intros z Hz. apply find_segment_none_A. rewrite Nv in Hz. lia.
      -- intros o Ho. rewrite Nv.
         apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
         ++ lia.
         ++ right. revert Pceil. unfold alloc_top. rewrite stack_max_size_val, <- Hv1. intros Pceil. exact Pceil.
         ++ intros x Hx. lia.
         ++ intros e sz Hin x Hx Hblk. destruct (HG e sz Hin) as [(b & s0 & Hm & Hb1 & Hb2) | Hlow]; [|lia].
            pose proof (region_free_In _ _ _ _ _ Hfree_m ltac:(rewrite Evm; exact Hm)) as R.
            unfold iv_overlap in R. rewrite Nv in R.
            apply andb_false_iff in R. destruct R as [R|R]; apply Z.ltb_ge in R; lia.
         ++ exact Ho.
      -- rewrite HX. intros rr y [] _.
      -- subst rho'. apply Hrho_ag.
      -- lia.
      -- cbn. apply Pos.ltb_lt. exact Hnxt.
      -- subst rho'. cbn [eval]. apply Hrho_at. }
    replace E with (mkAX (ax_S E) [] (SLit SHB)) in SM by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
    destruct SM as (Ssm & SMI & Swf & Ssh & Shz). cbn [ax_S ax_setS ax_X ax_base] in Ssm, Swf, Ssh.
    split; [|split; [exact SMI|split; [|split; [|exact Shz]]]].
    -- cbn [ax_S]. apply smatch_add_facts; [exact Ssm| |].
       ++ unfold null_none_facts. assert (E1 : rw rho' (ss_next (ax_S E)) = a) by (subst rho'; apply Hrho_at).
          repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
          ** change (2 ^ 12) with 4096. split; [lia|exact Pal].
          ** rewrite u64_of_lit by (pose proof (LB_of_range lenZ); lia). exact PLB.
          ** unfold alloc_ceiling_hi in *. rewrite u64_of_lit by lia. lia.
       ++ assert (X : (ss_next (ax_S E) <? nxt)%positive = true) by (apply Pos.ltb_lt; exact Hnxt). cbn. rewrite !X. reflexivity.
    -- unfold axwf in Swf |- *. cbn [ax_S ax_X ax_base ss_next add_facts] in Swf |- *. exact Swf.
    -- unfold shadow_ok. cbn. constructor.
  * assert (Hclr : tp_clear_of tp (lazy_interior a n)).
    { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
      rewrite Nv. unfold two_pow_64 in CL. lia. }
    assert (Hpaid' : paid (null_none_model lenZ md a) tp <= B).
    { unfold null_none_model. fold n. rewrite (paid_add_lazy (with_vmmaps (null_none_h lenZ md a) md) a n tp Hclr), paid_with_vmmaps.
      pose proof (used_add_lazy_le (with_vmmaps (null_none_h lenZ md a) md) a n) as U1.
      pose proof (used_none_cons_le md (null_none_h lenZ md a) a n (MI_ivs_wf segsA _ _ HMI)) as U2.
      assert (Hiv : iv_wf (a, n)) by (unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Nv; unfold two_pow_64 in CL; lia).
      assert (Hwf1 : model_ivs_wf (with_vmmaps (null_none_h lenZ md a) md)).
      { pose proof (MI_ivs_wf segsA _ _ HMI) as (W1 & W2 & W3). unfold model_ivs_wf. unfold null_none_h.
        rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps. cbn [vm_maps vm_noaccess].
        split; [apply ivs_wf_cons; assumption|]. split; [apply ivs_wf_cons; assumption|]. exact W3. }
      specialize (U1 Hwf1 ltac:(rewrite Nv; unfold two_pow_64 in CL; lia)).
      specialize (U2 Hiv eq_refl eq_refl). lia. }
    assert (Hem' : erase_mat (null_none_model lenZ md a) = erase_mat (null_none_model lenZ m a)).
    { unfold null_none_model, null_none_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
    unfold with_mmap_backing. rewrite Enr.
    split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End ELazyNullNone.

Section EagerRw.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S4dS8S22S1eQ40A1A1S22S39A1M0S3cR5R4R3R2R1A4S0G0R3S25S39A1A3F_;Fmd;Ftr;Ftp;Frho;S4eS1dVok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S4dS8S22S1eQ40A1A1S22S39A1M0S3cR5R4R3R2R1A4S0G0R3S25S39A1A3F_;Fmd;Ftr;Ftp;Frho;S72S1dVok;R2A3F_;FJ;").

Variables (E : axst) (lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)) (nxt : positive).
Let n : word := Z_to_bv 64 lenZ.
Definition eager_h (md : Model) (a : word) : VmMaps := ltac2:(tb__ "0|1|
S38Vmd;A1S41S42S3bR1A1S27S21S1eQ40A1M0G0A2S23G0G0Va;Vn;A4S3aR1A1A3S45R1A1S46R1A1S43R1A1S3fR1A1S44R1A1S3eR1A1A8Th;").
Definition eager_model (md : Model) (a : word) : Model := ltac2:(tb__ "0|0|
S40S7bVmd;Va;A2Vmd;A2").
Definition eager_facts : list sprop := ltac2:(tb__ "0|2|
S27SdS13SaS18VE;A1A1M0ZcA2S27SdS10S6S5cVlenZ;A1A1S11G0A1M1A2S27SdS10G1S6S33S68VlenZ;A2A1A2S25SdA1A3A3A3").
Definition eager_ok : axst := ltac2:(tb__ "0|2|
S19S7dS7aS76S18VE;A1M0S11SaG0A1M1A1S2bSfS12G0A1S27SfS77G1VlenZ;A2S25SfA1A3A3Vnxt;A4A2S25S21S5S5A2A1S6S52A1A3").

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S5S1aVE;A1S6S52A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S29S50A1S59S1dSbS18VE;A1A1A2S2aS50S51A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1Z11A2S6ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZaA2S6Z0A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZbA2S6VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZdA2S6Z22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZfA2S6Z0A1A3").
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hsmall : lenZ < 2 ^ 62.
Hypothesis Hnxt : ltac2:(tb__ "0|0|
S74SaS18VE;A1A1Vnxt;A2").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S24S53VGl;S18VE;A1A2S26A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S22S21S1eQ40A1M0G0A2A1S3bS38Vm;A1A1S54S1dA1A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
S71S2bS21S1eQ40A1M0G0A2S3bS38Vm;A1M1A1S3aG1A1A3S70S6fA3").
Hypothesis HBlim : ltac2:(tb__ "0|0|
S2fS30VB;VlenZ;A2S3fS38Vm;A1A1A2").

Lemma n_valE : bv_unsigned n = lenZ.
Proof using Hpos Hsmall. unfold n. apply u64_of_lit. clear -Hpos Hsmall. lia. Qed.

Lemma nZ_valE : mmap_nZ n = lenZ.
Proof using Hpos Hsmall Hnl.
  clear Hnxt Hclear HBlim. unfold mmap_nZ, page_round_up_Z, page_size. rewrite n_valE.
  pose proof Hnl as Hnl'. apply Z.mod_divide in Hnl' as [q Hq]; [|clear -Hpos; lia]. rewrite Hq.
  replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. clear -Hpos. lia.
Qed.

Lemma eager_user : ltac2:(tb__ "0|12|
S8S22S1eQ40M0A1M1A1S6eS3cG1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S3G1G1S3G1G1S1S4bS21G1G1A2S23G1G1R2R1A4S3aS38Vm;A1M2A1A3S1S2fS1fG0R2A2M3S1fG0S9RaR5A2A2M4A2S2fS30G4R4A2S30G3S1fG0R1A2M5A2A2A2A2Ls;A2Lb;A2S2fS30S1fG0S9R8R3A2A2R2A2S5cVlenZ;A1A2A2F_;Fsz;Fe;S0S37S1fG0SeR6P1A2A2S1fG0S3eG2A1A2A3S73S1dR7R6VE;S23S22S39A1S55S25S39A1M6S56R5R4A2A4A5S4fVm;VB;R8R7G6R5A6S0G1S6cR7U0M7A2S20G0Z0A2M8A3S0G1S6cR8U1M9A2Vn;A3S0G1S6cR9U3MaA2S20G0Z22A2A3S6aS6cRaG7A2S6cRaGaA2R9S6cRaG9A2R8A5S1SfS4bSfR1S12S18VE;A1MbA1A3S16S15RfR2A2S23S37S37S1fG0RbA2McS30GcVlenZ;A2A4A2F_;Fo;S1G1S1S2fS1fG0RaA2MdG5A2S31G5S30GdVlenZ;A2A2A2S0S24S17S1dR2A2S28A3F_;Fx;S1S21S5S5A2MeS37S4bGeR2S1bVE;A1A3S1S2fS1fG0S9R10S2dS5S5R3A3A2A2MfR2A2S31R2S30GfS1fG0S9R10S2eS5S5R3A3A2A2A2A2A2S4S1S2fS1fG0RdA2M10S1fG0S1cS1fG0S9R11S1aVE;A1A2A2R3A2A2M11A2S31G11S30G10VlenZ;A2A2A2A1F_;F_;Fy;Frr;S1S67G8Vm;Vn;R9A4S4fS79Vm;R9A2S30VB;VlenZ;A2S75RdSaGbA1R9A3RcG6S40S6bS38RaA1S6cRbG9A2R9A3RaA2A6A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fa;Fmd;Fms;Ftp;Frho;").
Proof using HX Hclear Hnl Hpos Hres Hsmall Htop Hband.
  clear Hnxt HBlim. intros rho tp ms md a HG Hv1 Hsp (_ & Hem & Hpaid) G0 G1 G3 Hpl.
  pose proof n_valE as Nv. pose proof nZ_valE as NZ. pose proof (alloc_top_lt (m_vmmaps m)) as CL.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & _).
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  assert (HnZ : mmap_n n = n) by (unfold mmap_n; rewrite NZ; reflexivity).
  rewrite G0, G1, G3 in Hpl.
  pose proof Hpl as (Pal & Ppos & Pceil & Pfree & _). rewrite NZ in Pceil. rewrite HnZ in Pfree.
  assert (Hplm : mmap_place_ok_none (Z_to_bv 64 0) m n a).
  { unfold mmap_place_ok_none. rewrite NZ, HnZ, <- Evm. repeat split; assumption. }
  pose proof (place_LB_A m lenZ a Htop Hres Hband ltac:(lia) Hnl Hplm) as (PLB & Pimg & Pband & Ptop & Phi).
  assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true) by exact (region_free_app_r _ _ _ _ Pfree).
  split; [|split; [|split]].
  - intros o Ho.
    apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
    + lia.
    + right. revert Pceil. rewrite Evm. unfold alloc_top. rewrite stack_max_size_val, <- Hv1. intros Pceil. exact Pceil.
    + intros x Hx. lia.
    + intros e sz Hin x Hx Hblk. destruct (HG e sz Hin) as [(b & s0 & Hm & Hb1 & Hb2) | Hlow]; [|lia].
      pose proof (region_free_In _ _ _ _ _ Hfree_m ltac:(rewrite Evm; exact Hm)) as R.
      unfold iv_overlap in R. rewrite Nv in R.
      apply andb_false_iff in R. destruct R as [R|R]; apply Z.ltb_ge in R; lia.
    + exact Ho.
  - intros x Hx. apply (grant_no_ro_A a lenZ); [|exact Hx]. intros z Hz. lia.
  - rewrite HX. intros rr y [] _.
  - split; [exact Hplm|]. rewrite G1. split; [reflexivity|]. split.
    + unfold eager_model, eager_h, mmap_rw_vm. rewrite HnZ, <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
    + rewrite paid_with_vmmaps.
      pose proof (used_maps_cons_le md (mmap_rw_vm (m_vmmaps md) n a) a n (MI_ivs_wf segsA _ _ HMI)
                   ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Nv; unfold two_pow_64 in CL; lia)
                   ltac:(unfold mmap_rw_vm; rewrite HnZ; reflexivity) eq_refl) as U.
      rewrite Nv in U. lia.
Qed.

Theorem eager_rw_node : ltac2:(tb__ "0|7|
S8S22S1eQ40M0A1M1A1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S3G1G1S3G1G1S1S4bS21G1G1A2S23G1G1R2R1A4S3aS38Vm;A1M2A1A3S1S2fS1fG0R2A2M3S1fG0S9R7R5A2A2M4A2S2fS30G4R4A2S30G3S1fG0R1A2A2A2A2A2Ls;A2Lb;A2S2fS30S1fG0S9R5R3A2A2R2A2S5cVlenZ;A1A2A2F_;Fsz;Fe;S0S37S1fG0SeR3P1A2A2S1fG0S3eG2A1A2A3S65S1dVok;S4cS1dS4fVm;VB;A2M5VE;R4R3A5S63S2S4cS1dG5S19S57S18VE;A1M6S58A2S25S21S5S5A2A1S6S52A1A3R5R4R1A6S3G1G1S1S67S20G0Z0A2Vm;Vn;R1A4S4cS1dS4fS79Vm;R1A2S30VB;VlenZ;A2A2S7cS75R6SaG6A1R1A3R5R2A6A2La;A2A2Lw;A4F_;F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG Hv1. pose proof n_valE as Nv.
  eapply triple1_conseq; [intros w Hw; exact Hw | |].
  2:{ apply (triple1_mmap_rw_objA segsA ok (KxA m B) (KxA m B)
        (fun a rho' tp' tr' md' => mmap_place_ok_none (Z_to_bv 64 0) m n a /\ KxA (eager_model m a) (B + lenZ) rho' tp' tr' md')
        E rho tp lenZ).
      - apply OKF. intros; eapply KxA_nil; eassumption.
      - apply OKP. intros; eapply KxA_nil; eassumption.
      - apply stableA_KxA.
      - exact Hecall.
      - exact R17.
      - exact R11.
      - exact Hnl.
      - lia.
      - intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
        pose proof (erase_mat_eq_fields md m Hem) as (Evm & _).
        destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
        rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
        cbn [eval] in G0, G1, G2, G3, G4, G5. fold n in G1.
        split; [rewrite G2, G3, G5; apply mmap_modeled_b_intro; reflexivity|].
        split; [rewrite G3; reflexivity|].
        split; [unfold headroom; rewrite Evm; lia|].
        split; [exact HK|].
        intros a Hpl. exact (eager_user rho tp ms md a HG Hv1 Hsp HK G0 G1 G3 Hpl). }
  intros w [Hw|(a & [Hsm [Hpl Hk]])]; [left | right; exists a].
  { replace (mkAX (S_ret_lit (ax_S E) enomem_ret) [] (SLit SHB)) with (A_after E (SLit (bv_unsigned (errno_ret ENOMEM)))); [exact Hw|].
    unfold A_after, S_ret_lit, enomem_ret. destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity. }
  split; [exact Hpl|].

  unfold eager_ok.
  change (mkAX (add_facts eager_facts (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) lenZ]) nxt)) [] (SLit SHB))
    with (ax_with_facts (mkAX (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) lenZ]) nxt) [] (SLit SHB))
            (eager_facts ++ ss_facts (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) lenZ]) nxt))).
  assert (Hsm' : smatchA segsA (rho_set_rw rho (ss_next (ax_S E)) a) tp
                   (mkAX (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) lenZ]) nxt) [] (SLit SHB)) w).
  {
    destruct Hsm as (S1 & S2 & S3 & S4 & S5). replace E with (mkAX (ax_S E) [] (SLit SHB)) in S1, S3, S4
      by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
    cbn [ax_S ax_setS ax_X ax_base] in S1, S3, S4.
    split; [|split; [exact S2|split; [|split; [unfold shadow_ok; cbn; constructor|exact S5]]]].
    - cbn [ax_S]. destruct S1 as (W & rest). split; [|exact rest].
      unfold S_after in W |- *. cbn in W |- *.
      eapply (swf_mono_next (mkSS _ _ _ _ _ _ _ (Pos.succ (ss_next (ax_S E))) _) nxt); [cbn; lia | exact W].
    - unfold axwf in S3 |- *. cbn in S3 |- *. reflexivity. }
  apply SPA_refacts; [split; [exact Hsm'|exact Hk] | |].
  - cbn [ax_S ss_next S_after]. rewrite forallb_app.
    assert (X : (ss_next (ax_S E) <? nxt)%positive = true) by (apply Pos.ltb_lt; exact Hnxt).
    apply andb_true_intro. split.
    + unfold eager_facts. cbn. rewrite !X. reflexivity.
    + destruct Hsm' as ((W & _) & _). cbn [ax_S] in W. exact (swf_facts _ W).
  - intros HF. apply Forall_app. split; [|exact HF].
    pose proof (place_LB_A m lenZ a Htop Hres Hband ltac:(lia) Hnl Hpl) as (PLB & Pimg & Pband & Ptop & Phi).
    pose proof Hpl as (Pal & Ppos & _).
    unfold eager_facts. cbn [ax_S ss_next S_after].
    assert (E1 : rw (rho_set_rw rho (ss_next (ax_S E)) a) (ss_next (ax_S E)) = a) by apply rho_set_rw_at.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
    + change (2 ^ 12) with 4096. split; [lia|exact Pal].
    + rewrite u64_of_lit by (pose proof (LB_of_range lenZ); lia). exact PLB.
    + unfold alloc_ceiling_hi in *. rewrite u64_of_lit by lia. lia.
Qed.
End EagerRw.

Section EEagerRw.
Variables (E : axst) (lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)) (nxt : positive).
Let n : word := Z_to_bv 64 lenZ.
Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S5S1aVE;A1S6S52A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S29S50A1S59S1dSbS18VE;A1A1A2S2aS50S51A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1Z11A2S6ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZaA2S6Z0A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZbA2S6VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZdA2S6Z22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZfA2S6Z0A1A3").
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hsmall : lenZ < 2 ^ 62.
Hypothesis Hnxt : ltac2:(tb__ "0|0|
S74SaS18VE;A1A1Vnxt;A2").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S24S53VGl;S18VE;A1A2S26A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S22S21S1eQ40A1M0G0A2A1S3bS38Vm;A1A1S54S1dA1A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
S71S2bS21S1eQ40A1M0G0A2S3bS38Vm;A1M1A1S3aG1A1A3S70S6fA3").
Hypothesis HBlim : ltac2:(tb__ "0|0|
S2fS30VB;VlenZ;A2S3fS38Vm;A1A1A2").
Hypothesis Hwit : ltac2:(tb__ "0|2|
S3S1eQ40M0A1M1G1S67S20G0Z0A2Vm;Vn;R1A4La;A2").

Lemma paid_ge_used : ltac2:(tb__ "0|0|
S3cS22S1eQ40A1A1S2fS4aR2A1S89R2R1A2A2Ftp;Fmd;").
Proof. intros md tp. unfold paid. pose proof page_size_pos. nia. Qed.

Theorem eager_rw_enode : ltac2:(tb__ "0|5|
S8S22S1eQ40M0A1M1A1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S3G1G1S3G1G1S1S4bS21G1G1A2S23G1G1R2R1A4S3aS38Vm;A1M2A1A3S1S2fS1fG0R2A2M3S1fG0S9R7R5A2A2M4A2S2fS30G4R4A2S30G3S1fG0R1A2A2A2A2A2Ls;A2Lb;A2S2fS30S1fG0S9R5R3A2A2R2A2S5cVlenZ;A1A2A2F_;Fsz;Fe;S0S37S1fG0SeR3P1A2A2S1fG0S3eG2A1A2A3S64S1dS4cS1dS4fVm;VB;A2VE;R4R3A5S63S3G1G1S1S67S20G0Z0A2Vm;Vn;R1A4S4cS1dS4fS5fVlenZ;Vm;R1A3S30VB;VlenZ;A2A2S60VE;VlenZ;Vnxt;A3S75R6SaS18VE;A1A1R1A3R5R2A6A2La;A2Lw;A3F_;F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG Hv1.
  pose proof (n_valE lenZ Hpos Hsmall) as Nv. pose proof (nZ_valE lenZ Hnl Hpos Hsmall) as NZ.
  assert (HnZ : mmap_n n = n) by (unfold mmap_n; fold n in NZ; rewrite NZ; reflexivity).
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply (etriple_mmap_rw_objA segsA (KxA m B)
        (fun a rho' tp' tr' md' => mmap_place_ok_none (Z_to_bv 64 0) m n a /\ KxA (eager_model lenZ m a) (B + lenZ) rho' tp' tr' md')
        E rho tp lenZ).
      - apply stableA_KxA.
      - exact Hecall.
      - exact R17.
      - exact R11.
      - exact Hnl.
      - lia.
      - intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
        pose proof (erase_mat_eq_fields md m Hem) as (Evm & _).
        destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
        rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
        cbn [eval] in G0, G1, G2, G3, G4, G5. fold n in G1.
        split; [rewrite G2, G3, G5; apply mmap_modeled_b_intro; reflexivity|].
        split; [rewrite G3; reflexivity|].
        split; [unfold headroom; rewrite Evm; lia|].
        destruct Hwit as [a Hplm]. exists a.
        assert (Hpl : mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a).
        { rewrite G0, G1, G3. pose proof Hplm as (P1 & P2 & P3 & P4). unfold mmap_place_ok. rewrite Evm.
          split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
          unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 34)) with false. apply Z.leb_le.
          fold n in NZ. rewrite NZ, Evm. pose proof (paid_ge_used md tp). lia. }
        split; [exact Hpl|].
        exact (eager_user E lenZ m B Gl HX Hnl Hpos Hsmall Hclear Hres Htop Hband rho tp ms md a HG Hv1 Hsp HK G0 G1 G3 Hpl). }
  intros w (a & [Hsm [Hpl Hk]]). exists a. split; [exact Hpl|].
  unfold eager_ok.
  change (mkAX (add_facts (eager_facts E lenZ) (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) lenZ]) nxt)) [] (SLit SHB))
    with (ax_with_facts (mkAX (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) lenZ]) nxt) [] (SLit SHB))
            (eager_facts E lenZ ++ ss_facts (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) lenZ]) nxt))).
  assert (Hsm' : smatchA segsA (rho_set_rw rho (ss_next (ax_S E)) a) tp
                   (mkAX (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) lenZ]) nxt) [] (SLit SHB)) w).
  { destruct Hsm as (S1 & S2 & S3 & S4 & S5). replace E with (mkAX (ax_S E) [] (SLit SHB)) in S1, S3, S4
      by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
    cbn [ax_S ax_setS ax_X ax_base] in S1, S3, S4.
    split; [|split; [exact S2|split; [|split; [unfold shadow_ok; cbn; constructor|exact S5]]]].
    - cbn [ax_S]. destruct S1 as (W & rest). split; [|exact rest].
      unfold S_after in W |- *. cbn in W |- *.
      eapply (swf_mono_next (mkSS _ _ _ _ _ _ _ (Pos.succ (ss_next (ax_S E))) _) nxt); [cbn; lia | exact W].
    - unfold axwf in S3 |- *. cbn in S3 |- *. reflexivity. }
  apply SPA_refacts; [split; [exact Hsm'|exact Hk] | |].
  - cbn [ax_S ss_next S_after]. rewrite forallb_app.
    assert (X : (ss_next (ax_S E) <? nxt)%positive = true) by (apply Pos.ltb_lt; exact Hnxt).
    apply andb_true_intro. split.
    + unfold eager_facts. cbn. rewrite !X. reflexivity.
    + destruct Hsm' as ((W & _) & _). cbn [ax_S] in W. exact (swf_facts _ W).
  - intros HF. apply Forall_app. split; [|exact HF].
    pose proof (place_LB_A m lenZ a Htop Hres Hband ltac:(lia) Hnl Hpl) as (PLB & Pimg & Pband & Ptop & Phi).
    pose proof Hpl as (Pal & Ppos & _).
    unfold eager_facts. cbn [ax_S ss_next S_after].
    assert (E1 : rw (rho_set_rw rho (ss_next (ax_S E)) a) (ss_next (ax_S E)) = a) by apply rho_set_rw_at.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
    + change (2 ^ 12) with 4096. split; [lia|exact Pal].
    + rewrite u64_of_lit by (pose proof (LB_of_range lenZ); lia). exact PLB.
    + unfold alloc_ceiling_hi in *. rewrite u64_of_lit by lia. lia.
Qed.
End EEagerRw.

Section LazyNoreplaceRw.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S4dS8S22S1eQ40A1A1S22S39A1M0S3cR5R4R3R2R1A4S0G0R3S25S39A1A3F_;Fmd;Ftr;Ftp;Frho;S4eS1dVok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S4dS8S22S1eQ40A1A1S22S39A1M0S3cR5R4R3R2R1A4S0G0R3S25S39A1A3F_;Fmd;Ftr;Ftp;Frho;S72S1dVok;R2A3F_;FJ;").

Variables (E : axst) (addrZ lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)).
Let a : word := Z_to_bv 64 addrZ.
Let n : word := Z_to_bv 64 lenZ.

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S5S1aVE;A1S6S52A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S29S50A1S59S1dSbS18VE;A1A1A2S2aS50S51A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1Z11A2S6ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZaA2S6VaddrZ;A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZbA2S6VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZdA2S6Z104022A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZfA2S6Z0A1A3").
Hypothesis Hal : addrZ mod 4096 = 0.
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hlo : 0x646000 <= addrZ.
Hypothesis Hceil : ltac2:(tb__ "0|0|
S2fS30VaddrZ;VlenZ;A2S66A2").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S24S53VGl;S18VE;A1A2S26A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S22S21S1eQ40A1M0G0A2A1S3bS38Vm;A1A1S54S1dA1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|1|
S1eQ40A1M0G0S4bS21G0G0A2S23G0G0R2R1A4S3aS38Vm;A1A1A3S0S24S3dVa;Vn;R3R2A4S28A3F_;Fs;Fb;").

Lemma a_valR : bv_unsigned a = addrZ.
Proof using Hceil Hlo Hpos. unfold alloc_ceiling_lo in Hceil. unfold a. apply u64_of_lit. lia. Qed.
Lemma n_valR : bv_unsigned n = lenZ.
Proof using Hceil Hlo Hpos. unfold alloc_ceiling_lo in Hceil. unfold n. apply u64_of_lit. lia. Qed.

Theorem lazy_noreplace_rw_node : ltac2:(tb__ "0|6|
S8S22S1eQ40M0A1A1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S2fS30VaddrZ;VlenZ;A2S1fG0S9R5R3A2A2M1A2S2fS30G1R2A2VaddrZ;A2A2F_;Fsz;Fe;S65S1dVok;S4cS1dS4fVm;VB;A2M2VE;R3R2A5S63S2S4cS1dG2S19S57S18VE;A1M3S58A2S25S21S5S5A2A1M4S6S52A1M5A3R4R3R1A6S4cS1dS4fS5eVaddrZ;VlenZ;Vm;A3VB;A2S19S57G3VaddrZ;A2G4G5A3S5bR4S5aScR4A1Va;Vn;A3A2R3R1A6A2Lw;A4F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG.
  pose proof a_valR as Av. pose proof n_valR as Nv. pose proof Hceil as CL. unfold alloc_ceiling_lo in CL.
  apply triple1_ecall_detA; [apply OKF; intros; eapply KxA_nil; eassumption | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold a in G0. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  destruct (mmap_noreplace_rw_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnnrn & Hnfrw & Hnfn & Hnnone & Hnrw).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_0x104022. reflexivity. }
  { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    apply Z.mod_divide in Hnl as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  assert (Hceil' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, Av, HnZ', Evm; apply (alloc_top_ge_lo _ _ Htop); exact Hceil).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0, Av; exact Hal).
  assert (Hpos' : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0, Av; lia).
  assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true).
  { rewrite Evm. apply region_free_of_forall. exact Hmaps. }
  assert (Hfresh : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm. apply region_free_of_forall. intros b s Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite Hres in Hin. apply (reserved_A_clear a n b s Hin). rewrite Av. exact Hlo.
    - apply Hmaps. exact Hin. }
  split.
  - apply (OKP (KxA m B) ltac:(intros; eapply KxA_nil; eassumption) rho tp [] ms md (Z_to_bv 64 222));
      [split; [reflexivity|split; [exact Hem|exact Hpaid]] | exact Hp |].
    apply (noreplace_rw_fresh_only_okA segsA ms md _ H222 Hlen Hshape Hnnrn Hnfrw Hnfn Hnnone Hnrw Hceil' Halign Hpos' Hfresh).
  - intros w' Hw.
    destruct (wstep_noreplace_rw_fresh_invA segsA ms md _ Hh H222 Hlen Hshape Hnnrn Hnfrw Hnfn Hnnone Hnrw Hceil' Halign Hpos' Hfresh [] w' Hp Hw)
      as [-> | [Hb ->]].
    + left. split; [|split; [reflexivity|split; [exact Hem|exact Hpaid]]].
      change (mkAX (S_ret_lit (ax_S E) enomem_ret) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit (bv_unsigned (errno_ret ENOMEM))) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
      replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
      eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right.
      assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_0x104022; reflexivity).
      unfold mmap_rw_model, mmap_rw_vm, with_mmap_backing. rewrite Enr, HnZ, G0.
      split.
      * change (mkAX (S_ret_lit (ax_S E) addrZ) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit addrZ) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
        replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
        eapply (smatchA_after_grant_lazy segsA rho _ tp E [] ms md [] (lazy_rw_h addrZ lenZ md)); try exact Hsp.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- rewrite Av. exact Hal.
        -- rewrite Nv. exact Hnl.
        -- rewrite Nv. exact Hpos.
        -- rewrite Av, Nv. unfold two_pow_64 in CL. lia.
        -- exact Hfree_m.
        -- intros z Hz. apply find_segment_none_A. rewrite Av in Hz. lia.
        -- intros o Ho. rewrite Nv.
           apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
           ++ lia.
           ++ rewrite Av. left. exact CL.
           ++ intros x Hx. rewrite Av in Hx. lia.
           ++ intros e sz Hin x Hx. rewrite Av in Hx. destruct (HG e sz Hin); lia.
           ++ exact Ho.
        -- rewrite HX. intros rr y [] _.
        -- apply agree_below_refl.
        -- apply Pos.le_refl.
        -- reflexivity.
        -- cbn [eval]. rewrite <- Av. apply Z_to_bv_bv_unsigned.
      *
        assert (Hclr : tp_clear_of tp (lazy_interior a n)).
        { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
          rewrite Av, Nv. unfold two_pow_64 in CL. lia. }
        assert (Hpaid' : paid (lazy_rw_model addrZ lenZ md) tp <= B).
        { unfold lazy_rw_model. fold a n. rewrite (paid_add_lazy (with_vmmaps (lazy_rw_h addrZ lenZ md) md) a n tp Hclr), paid_with_vmmaps.
          pose proof (used_rw_noreserve_le md (lazy_rw_h addrZ lenZ md) a n (MI_ivs_wf segsA _ _ HMI)
                        ltac:(rewrite Av; exact Hal) ltac:(rewrite Nv; exact Hnl) ltac:(rewrite Nv; exact Hpos)
                        ltac:(rewrite Av, Nv; unfold two_pow_64 in CL; lia) eq_refl eq_refl) as U.
          lia. }
        assert (Hem' : erase_mat (lazy_rw_model addrZ lenZ md) = erase_mat (lazy_rw_model addrZ lenZ m)).
        { unfold lazy_rw_model, lazy_rw_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
        split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End LazyNoreplaceRw.

Section LazyNoreplaceNone.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S4dS8S22S1eQ40A1A1S22S39A1M0S3cR5R4R3R2R1A4S0G0R3S25S39A1A3F_;Fmd;Ftr;Ftp;Frho;S4eS1dVok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S4dS8S22S1eQ40A1A1S22S39A1M0S3cR5R4R3R2R1A4S0G0R3S25S39A1A3F_;Fmd;Ftr;Ftp;Frho;S72S1dVok;R2A3F_;FJ;").

Variables (E : axst) (addrZ lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)).
Let a : word := Z_to_bv 64 addrZ.
Let n : word := Z_to_bv 64 lenZ.

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S5S1aVE;A1S6S52A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S29S50A1S59S1dSbS18VE;A1A1A2S2aS50S51A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1Z11A2S6ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZaA2S6VaddrZ;A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZbA2S6VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZcA2S6Z0A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZdA2S6Z104022A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZfA2S6Z0A1A3").
Hypothesis Hal : addrZ mod 4096 = 0.
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hlo : 0x646000 <= addrZ.
Hypothesis Hceil : ltac2:(tb__ "0|0|
S2fS30VaddrZ;VlenZ;A2S66A2").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S24S53VGl;S18VE;A1A2S26A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S22S21S1eQ40A1M0G0A2A1S3bS38Vm;A1A1S54S1dA1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|1|
S1eQ40A1M0G0S4bS21G0G0A2S23G0G0R2R1A4S3aS38Vm;A1A1A3S0S24S3dVa;Vn;R3R2A4S28A3F_;Fs;Fb;").

Lemma a_valRN : bv_unsigned a = addrZ.
Proof using Hceil Hlo Hpos. unfold alloc_ceiling_lo in Hceil. unfold a. apply u64_of_lit. lia. Qed.
Lemma n_valRN : bv_unsigned n = lenZ.
Proof using Hceil Hlo Hpos. unfold alloc_ceiling_lo in Hceil. unfold n. apply u64_of_lit. lia. Qed.

Theorem lazy_noreplace_none_node : ltac2:(tb__ "0|6|
S8S22S1eQ40M0A1A1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S2fS30VaddrZ;VlenZ;A2S1fG0S9R5R3A2A2M1A2S2fS30G1R2A2VaddrZ;A2A2F_;Fsz;Fe;S65S1dVok;S4cS1dS4fVm;VB;A2M2VE;R3R2A5S63S2S4cS1dG2S19S57S18VE;A1M3S58A2S25S21S5S5A2A1M4S6S52A1M5A3R4R3R1A6S4cS1dS4fS5dVaddrZ;VlenZ;Vm;A3VB;A2S19S57G3VaddrZ;A2G4G5A3S5bR4S5aScR4A1Va;Vn;A3A2R3R1A6A2Lw;A4F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG.
  pose proof a_valRN as Av. pose proof n_valRN as Nv. pose proof Hceil as CL. unfold alloc_ceiling_lo in CL.
  apply triple1_ecall_detA; [apply OKF; intros; eapply KxA_nil; eassumption | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold a in G0. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  destruct (mmap_noreplace_none_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnnrw & Hnfrw & Hnfn & Hnnone & Hnrw).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_0x104022. reflexivity. }
  { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    apply Z.mod_divide in Hnl as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  assert (Hceil' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, Av, HnZ', Evm; apply (alloc_top_ge_lo _ _ Htop); exact Hceil).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0, Av; exact Hal).
  assert (Hpos' : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0, Av; lia).
  assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true).
  { rewrite Evm. apply region_free_of_forall. exact Hmaps. }
  assert (Hfresh : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm. apply region_free_of_forall. intros b s Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite Hres in Hin. apply (reserved_A_clear a n b s Hin). rewrite Av. exact Hlo.
    - apply Hmaps. exact Hin. }
  split.
  - apply (OKP (KxA m B) ltac:(intros; eapply KxA_nil; eassumption) rho tp [] ms md (Z_to_bv 64 222));
      [split; [reflexivity|split; [exact Hem|exact Hpaid]] | exact Hp |].
    apply (noreplace_none_fresh_only_okA segsA ms md _ H222 Hlen Hshape Hnfrw Hnfn Hnnone Hnrw Hceil' Halign Hpos' Hfresh).
  - intros w' Hw.
    destruct (wstep_noreplace_none_fresh_invA segsA ms md _ Hh H222 Hlen Hshape Hnfrw Hnfn Hnnone Hnrw Hceil' Halign Hpos' Hfresh [] w' Hp Hw)
      as [-> | ->].
    + left. split; [|split; [reflexivity|split; [exact Hem|exact Hpaid]]].
      change (mkAX (S_ret_lit (ax_S E) enomem_ret) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit (bv_unsigned (errno_ret ENOMEM))) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
      replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
      eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right.
      assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_0x104022; reflexivity).
      unfold mmap_none_model, mmap_none_vm. rewrite HnZ, G0.
      split.
      * change (mkAX (S_ret_lit (ax_S E) addrZ) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit addrZ) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
        replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
        eapply (smatchA_after_grant_none segsA rho _ tp E [] ms md [] (none_h addrZ lenZ md)); try exact Hsp.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- rewrite Av. exact Hal.
        -- rewrite Nv. exact Hnl.
        -- rewrite Nv. exact Hpos.
        -- rewrite Av, Nv. unfold two_pow_64 in CL. lia.
        -- exact Hfree_m.
        -- intros z Hz. apply find_segment_none_A. rewrite Av in Hz. lia.
        -- intros o Ho. rewrite Nv.
           apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
           ++ lia.
           ++ rewrite Av. left. exact CL.
           ++ intros x Hx. rewrite Av in Hx. lia.
           ++ intros e sz Hin x Hx. rewrite Av in Hx. destruct (HG e sz Hin); lia.
           ++ exact Ho.
        -- rewrite HX. intros rr y [] _.
        -- apply agree_below_refl.
        -- apply Pos.le_refl.
        -- reflexivity.
        -- cbn [eval]. rewrite <- Av. apply Z_to_bv_bv_unsigned.
      * assert (Hclr : tp_clear_of tp (lazy_interior a n)).
        { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
          rewrite Av, Nv. unfold two_pow_64 in CL. lia. }
        assert (Hpaid' : paid (lazy_none_model addrZ lenZ md) tp <= B).
        { unfold lazy_none_model. fold a n. rewrite (paid_add_lazy (with_vmmaps (none_h addrZ lenZ md) md) a n tp Hclr), paid_with_vmmaps.
          pose proof (used_add_lazy_le (with_vmmaps (none_h addrZ lenZ md) md) a n) as U1.
          pose proof (used_none_cons_le md (none_h addrZ lenZ md) a n (MI_ivs_wf segsA _ _ HMI)) as U2.
          assert (Hiv : iv_wf (a, n)) by (unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Av, Nv; unfold two_pow_64 in CL; lia).
          assert (Hwf1 : model_ivs_wf (with_vmmaps (none_h addrZ lenZ md) md)).
          { pose proof (MI_ivs_wf segsA _ _ HMI) as (W1 & W2 & W3). unfold model_ivs_wf. unfold none_h.
            rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps. cbn [vm_maps vm_noaccess].
            split; [apply ivs_wf_cons; assumption|]. split; [apply ivs_wf_cons; assumption|]. exact W3. }
          specialize (U1 Hwf1 ltac:(rewrite Av, Nv; unfold two_pow_64 in CL; lia)).
          specialize (U2 Hiv eq_refl eq_refl). lia. }
        assert (Hem' : erase_mat (lazy_none_model addrZ lenZ md) = erase_mat (lazy_none_model addrZ lenZ m)).
        { unfold lazy_none_model, none_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
        unfold with_mmap_backing. rewrite Enr.
        split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End LazyNoreplaceNone.

Section ELazyNoreplaceRw.
Variables (E : axst) (addrZ lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)).
Let a : word := Z_to_bv 64 addrZ.
Let n : word := Z_to_bv 64 lenZ.
Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S5S1aVE;A1S6S52A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S29S50A1S59S1dSbS18VE;A1A1A2S2aS50S51A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1Z11A2S6ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZaA2S6VaddrZ;A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZbA2S6VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZdA2S6Z104022A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZfA2S6Z0A1A3").
Hypothesis Hal : addrZ mod 4096 = 0.
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hlo : 0x646000 <= addrZ.
Hypothesis Hceil : ltac2:(tb__ "0|0|
S2fS30VaddrZ;VlenZ;A2S66A2").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S24S53VGl;S18VE;A1A2S26A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S22S21S1eQ40A1M0G0A2A1S3bS38Vm;A1A1S54S1dA1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|1|
S1eQ40A1M0G0S4bS21G0G0A2S23G0G0R2R1A4S3aS38Vm;A1A1A3S0S24S3dVa;Vn;R3R2A4S28A3F_;Fs;Fb;").

Theorem lazy_noreplace_rw_enode : ltac2:(tb__ "0|2|
S8S22S1eQ40M0A1A1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S2fS30VaddrZ;VlenZ;A2S1fG0S9R5R3A2A2M1A2S2fS30G1R2A2VaddrZ;A2A2F_;Fsz;Fe;S64S1dS4cS1dS4fVm;VB;A2VE;R3R2A5S4cS1dS4fS5eVaddrZ;VlenZ;Vm;A3VB;A2S19S57S18VE;A1VaddrZ;A2S25S21S5S5A2A1S6S52A1A3S5bR3S5aScR3A1Va;Vn;A3A2R2A5A3F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG.
  assert (Av : bv_unsigned a = addrZ) by (clear -Hceil Hlo Hpos; unfold alloc_ceiling_lo in Hceil; unfold a; apply u64_of_lit; lia).
  assert (Nv : bv_unsigned n = lenZ) by (clear -Hceil Hlo Hpos; unfold alloc_ceiling_lo in Hceil; unfold n; apply u64_of_lit; lia).
  pose proof Hceil as CL. unfold alloc_ceiling_lo in CL.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold a in G0. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  destruct (mmap_noreplace_rw_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnnrn & Hnfrw & Hnfn & Hnnone & Hnrw).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_0x104022. reflexivity. }
  { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    pose proof Hnl as Hnl'. apply Z.mod_divide in Hnl' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  assert (Hceil' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, Av, HnZ', Evm; apply (alloc_top_ge_lo _ _ Htop); exact Hceil).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0, Av; exact Hal).
  assert (Hpos' : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0, Av; lia).
  assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true).
  { rewrite Evm. apply region_free_of_forall. exact Hmaps. }
  assert (Hfresh : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm. apply region_free_of_forall. intros b s Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite Hres in Hin. apply (reserved_A_clear a n b s Hin). rewrite Av. exact Hlo.
    - apply Hmaps. exact Hin. }
  assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_0x104022; reflexivity).
  assert (Hb : mmap_noreserve_backed_ok (ms_gpr ms 3) md (mmap_nZ (ms_gpr ms 1)) = true) by (unfold mmap_noreserve_backed_ok; rewrite Enr; reflexivity).
  eexists. split.
  { exact (wstep_noreplace_rw_fresh_intro_okA segsA ms md _ Hh H222 Hlen Hshape Hnnrn Hnfrw Hnfn Hnnone Hnrw Hceil' Halign Hpos' Hfresh [] Hp Hb). }
  unfold mmap_rw_model, mmap_rw_vm, with_mmap_backing. rewrite Enr, HnZ, G0.
  split.
  * change (mkAX (S_ret_lit (ax_S E) addrZ) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit addrZ) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
    replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
    eapply (smatchA_after_grant_lazy segsA rho _ tp E [] ms md [] (lazy_rw_h addrZ lenZ md)); try exact Hsp.
    -- reflexivity.
    -- reflexivity.
    -- reflexivity.
    -- rewrite Av. exact Hal.
    -- rewrite Nv. exact Hnl.
    -- rewrite Nv. exact Hpos.
    -- rewrite Av, Nv. unfold two_pow_64 in CL. lia.
    -- exact Hfree_m.
    -- intros z Hz. apply find_segment_none_A. rewrite Av in Hz. lia.
    -- intros o Ho. rewrite Nv.
       apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
       ++ lia.
       ++ rewrite Av. left. exact CL.
       ++ intros x Hx. rewrite Av in Hx. lia.
       ++ intros e sz Hin x Hx. rewrite Av in Hx. destruct (HG e sz Hin); lia.
       ++ exact Ho.
    -- rewrite HX. intros rr y [] _.
    -- apply agree_below_refl.
    -- apply Pos.le_refl.
    -- reflexivity.
    -- cbn [eval]. rewrite <- Av. apply Z_to_bv_bv_unsigned.
  * assert (Hclr : tp_clear_of tp (lazy_interior a n)).
    { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
      rewrite Av, Nv. unfold two_pow_64 in CL. lia. }
    assert (Hpaid' : paid (lazy_rw_model addrZ lenZ md) tp <= B).
    { unfold lazy_rw_model. fold a n. rewrite (paid_add_lazy (with_vmmaps (lazy_rw_h addrZ lenZ md) md) a n tp Hclr), paid_with_vmmaps.
      pose proof (used_rw_noreserve_le md (lazy_rw_h addrZ lenZ md) a n (MI_ivs_wf segsA _ _ HMI)
                    ltac:(rewrite Av; exact Hal) ltac:(rewrite Nv; exact Hnl) ltac:(rewrite Nv; exact Hpos)
                    ltac:(rewrite Av, Nv; unfold two_pow_64 in CL; lia) eq_refl eq_refl) as U.
      lia. }
    assert (Hem' : erase_mat (lazy_rw_model addrZ lenZ md) = erase_mat (lazy_rw_model addrZ lenZ m)).
    { unfold lazy_rw_model, lazy_rw_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
    split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End ELazyNoreplaceRw.

Section ELazyNoreplaceNone.
Variables (E : axst) (addrZ lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)).
Let a : word := Z_to_bv 64 addrZ.
Let n : word := Z_to_bv 64 lenZ.
Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S5S1aVE;A1S6S52A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S29S50A1S59S1dSbS18VE;A1A1A2S2aS50S51A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1Z11A2S6ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZaA2S6VaddrZ;A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZbA2S6VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZcA2S6Z0A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZdA2S6Z104022A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S5S7S18VE;A1ZfA2S6Z0A1A3").
Hypothesis Hal : addrZ mod 4096 = 0.
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hlo : 0x646000 <= addrZ.
Hypothesis Hceil : ltac2:(tb__ "0|0|
S2fS30VaddrZ;VlenZ;A2S66A2").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S24S53VGl;S18VE;A1A2S26A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S22S21S1eQ40A1M0G0A2A1S3bS38Vm;A1A1S54S1dA1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|1|
S1eQ40A1M0G0S4bS21G0G0A2S23G0G0R2R1A4S3aS38Vm;A1A1A3S0S24S3dVa;Vn;R3R2A4S28A3F_;Fs;Fb;").

Theorem lazy_noreplace_none_enode : ltac2:(tb__ "0|2|
S8S22S1eQ40M0A1A1S5S37S4bS21S5S37A2S23S5S37R2R1A4VGl;A3S2S2fS30VaddrZ;VlenZ;A2S1fG0S9R5R3A2A2M1A2S2fS30G1R2A2VaddrZ;A2A2F_;Fsz;Fe;S64S1dS4cS1dS4fVm;VB;A2VE;R3R2A5S4cS1dS4fS5dVaddrZ;VlenZ;Vm;A3VB;A2S19S57S18VE;A1VaddrZ;A2S25S21S5S5A2A1S6S52A1A3S5bR3S5aScR3A1Va;Vn;A3A2R2A5A3F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG.
  assert (Av : bv_unsigned a = addrZ) by (clear -Hceil Hlo Hpos; unfold alloc_ceiling_lo in Hceil; unfold a; apply u64_of_lit; lia).
  assert (Nv : bv_unsigned n = lenZ) by (clear -Hceil Hlo Hpos; unfold alloc_ceiling_lo in Hceil; unfold n; apply u64_of_lit; lia).
  pose proof Hceil as CL. unfold alloc_ceiling_lo in CL.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold a in G0. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  destruct (mmap_noreplace_none_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnnrw & Hnfrw & Hnfn & Hnnone & Hnrw).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_0x104022. reflexivity. }
  { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    pose proof Hnl as Hnl'. apply Z.mod_divide in Hnl' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  assert (Hceil' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, Av, HnZ', Evm; apply (alloc_top_ge_lo _ _ Htop); exact Hceil).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0, Av; exact Hal).
  assert (Hpos' : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0, Av; lia).
  assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true).
  { rewrite Evm. apply region_free_of_forall. exact Hmaps. }
  assert (Hfresh : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm. apply region_free_of_forall. intros b s Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite Hres in Hin. apply (reserved_A_clear a n b s Hin). rewrite Av. exact Hlo.
    - apply Hmaps. exact Hin. }
  assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_0x104022; reflexivity).
  eexists. split.
  { exact (wstep_noreplace_none_fresh_intro_okA segsA ms md _ Hh H222 Hlen Hshape Hnfrw Hnfn Hnnone Hnrw Hceil' Halign Hpos' Hfresh [] Hp). }
  unfold mmap_none_model, mmap_none_vm. rewrite HnZ, G0.
  split.
  * change (mkAX (S_ret_lit (ax_S E) addrZ) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit addrZ) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
    replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
    eapply (smatchA_after_grant_none segsA rho _ tp E [] ms md [] (none_h addrZ lenZ md)); try exact Hsp.
    -- reflexivity.
    -- reflexivity.
    -- reflexivity.
    -- rewrite Av. exact Hal.
    -- rewrite Nv. exact Hnl.
    -- rewrite Nv. exact Hpos.
    -- rewrite Av, Nv. unfold two_pow_64 in CL. lia.
    -- exact Hfree_m.
    -- intros z Hz. apply find_segment_none_A. rewrite Av in Hz. lia.
    -- intros o Ho. rewrite Nv.
       apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
       ++ lia.
       ++ rewrite Av. left. exact CL.
       ++ intros x Hx. rewrite Av in Hx. lia.
       ++ intros e sz Hin x Hx. rewrite Av in Hx. destruct (HG e sz Hin); lia.
       ++ exact Ho.
    -- rewrite HX. intros rr y [] _.
    -- apply agree_below_refl.
    -- apply Pos.le_refl.
    -- reflexivity.
    -- cbn [eval]. rewrite <- Av. apply Z_to_bv_bv_unsigned.
  * assert (Hclr : tp_clear_of tp (lazy_interior a n)).
    { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
      rewrite Av, Nv. unfold two_pow_64 in CL. lia. }
    assert (Hpaid' : paid (lazy_none_model addrZ lenZ md) tp <= B).
    { unfold lazy_none_model. fold a n. rewrite (paid_add_lazy (with_vmmaps (none_h addrZ lenZ md) md) a n tp Hclr), paid_with_vmmaps.
      pose proof (used_add_lazy_le (with_vmmaps (none_h addrZ lenZ md) md) a n) as U1.
      pose proof (used_none_cons_le md (none_h addrZ lenZ md) a n (MI_ivs_wf segsA _ _ HMI)) as U2.
      assert (Hiv : iv_wf (a, n)) by (unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Av, Nv; unfold two_pow_64 in CL; lia).
      assert (Hwf1 : model_ivs_wf (with_vmmaps (none_h addrZ lenZ md) md)).
      { pose proof (MI_ivs_wf segsA _ _ HMI) as (W1 & W2 & W3). unfold model_ivs_wf. unfold none_h.
        rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps. cbn [vm_maps vm_noaccess].
        split; [apply ivs_wf_cons; assumption|]. split; [apply ivs_wf_cons; assumption|]. exact W3. }
      specialize (U1 Hwf1 ltac:(rewrite Av, Nv; unfold two_pow_64 in CL; lia)).
      specialize (U2 Hiv eq_refl eq_refl). lia. }
    assert (Hem' : erase_mat (lazy_none_model addrZ lenZ md) = erase_mat (lazy_none_model addrZ lenZ m)).
    { unfold lazy_none_model, none_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
    unfold with_mmap_backing. rewrite Enr.
    split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End ELazyNoreplaceNone.
End StartNodes.

