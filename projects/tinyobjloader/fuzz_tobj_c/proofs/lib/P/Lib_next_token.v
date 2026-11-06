(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "app"; "false"; "prod"; "None"; "bool"; "list"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "sv"; "sobj"; "SPUle"; "cell"; "sstate"; "SVar"; "SPUlt"; "SPBranch"; "mkCell"; "DUnknown"; "FcsrFrm0"; "SAlu"; "mkObj"; "mkSS"; "SPAlign"; "SPEq"; "SPNot"; "valuation"; "SExt"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token"; "pB"; "v120"; "vE"; "v141"; "vL"; "v143"; "vI"; "v121"; "O_cur"; "O_tl"; "O_tok"; "O_txt"; "Pre_nt"; "base_facts"; "two40"; "v142"; "P_found"; "P_nf"; "cur2"; "nt_state"; "vB"; "C1"; "C2"; "C2f"; "FUEL_nt"; "Posts_nt"; "cutpcs_nt"; "cuts_nt"; "inv1"; "regs2"; "F_found"; "F_nf"; "exits_nt"; "nonblank"; "regs1"; "two47"; "vcuts_nt"; "vexits_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "mkVN"; "check_cfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "cut_regs"; "pre_regs"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "BC_EQ"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token.NextTokenAddr"; "nt_L2"; "nt_L1"; "nt_ret"; "nt_entry"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "vTop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue"; "check_ecfgI"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module NextTokenAddr.
  Definition nt_entry : Z := 0x19b18.
  Definition nt_L1 : Z := 0x19b38.
  Definition nt_L2 : Z := 0x19b60.
  Definition nt_ret : Z := 0x19b8c.
End NextTokenAddr.
Import NextTokenAddr.

Definition FUEL_nt : nat := 200%nat.

Definition vB : sv := SVar 15.
Definition vI : sv := SVar 16.
Definition vE : sv := SVar 17.
Definition vL : sv := SVar 18.
Definition pB (off : sv) : sv := SAlu ALU_ADD vB off.
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.

Definition base_facts : list sprop := ltac2:(tb__ "0|1|
S0SbSfS27S23A2S0SbSfS23S25A2S0SbSfS25ScS2fA1A2S0SbSfS35ScS44A1A2S0SbSfScZ1A1S35A2S0SbS1bPcZ3M0A2S0SbS1bPdG0A2S0SbS1bPeG0A2S1SbA1A3A3A3A3A3A3A3A3").

Definition O_cur (c0 : sv) : sobj := ltac2:(tb__ "0|2|
S19S12PcA1ScZ0A1M0ScZ10A1S0S10S15G0Z8M1Vc0;A3S0S10S15ScG1A1G1S21S23A1A3S1S10A1A3A3S16A5").
Definition O_txt (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S35ScZ0A1S25Vcells;S16A5").
Definition O_tok (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S12PdA1ScZ0A1ScZ8A1Vcells;S16A5").
Definition O_tl (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S12PeA1ScZ0A1ScZ8A1Vcells;S16A5").

Definition Pre_nt : sstate := ltac2:(tb__ "0|1|
S1aS5cS50S4cS17S7SdA1S0SeS29S21S27A1A1S0SeS2cS1S10A1M0A1S0SeS2bG0A1S0SeS2aG0A1S1SeA1A3A3A3A3S2eS4bS5A9").

Definition v120 : sv := SVar 120.
Definition v121 : sv := SVar 121.
Definition cur2 : sv := ltac2:(tb__ "0|0|
S18S51S21S22A1S28A3").
Definition plus1 (e : sv) : sv := SAlu ALU_ADD e (SLit 1).

Definition inv1 : list sprop := ltac2:(tb__ "0|0|
S0SbS13S22S23A2S0SbS13S22S25A2S0SbSfS27S22A2S0SbSfS22ScS2fA1A2S0SbS14S52S21S22A1S21S23A1A3S1SbA1A3A3A3A3A3").
Definition inv2 : list sprop := ltac2:(tb__ "0|1|
S4SbS3dS0SbS13S18S51S22S28A3M0S23A2S0SbS13G0S25A2S0SbSfScZ1A1S28A2S0SbSfS28ScS2fA1A2S0SbS14S52S33S21S23A1A3S1SbA1A3A3A3A3A3A3").
Definition nonblank (x : positive) : list sprop := ltac2:(tb__ "0|1|
S0SbS1dS14S53S1fS5Q8S12Vx;A1A3M0ScZ9A1A3A1S0SbS1dS14S53G0ScZ20A1A3A1S1SbA1A3A3").

Definition nt_state (pc : Z) (regs : list (nat * sv)) (c0 : sv) (txt : list cell)
           (tok tl : list cell) (facts : list sprop) (nx : positive) : sstate := ltac2:(tb__ "0|1|
S1aVpc;S4dS4fS4bA1S4S6S2SdA2M0S0G0S3S2SdUaS12PcA1A4S0G0S3S2SdUbS12PdA1A4S0G0S3S2SdUcS12PeA1A4S1G0A1A3A3A3Vregs;A3A2S4cS17S7SdA1S0SeS29Vc0;A1S0SeS2cVtxt;A1S0SeS2bVtok;A1S0SeS2aVtl;A1S1SeA1A3A3A3A3S4SbVfacts;S2eA3Vnx;S5A9").

Definition regs1 (c : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S2SdA2M0S3S2SdUdS21S23A1A4S0G0S3S2SdUeVc;A4S0G0S3S2SdUfScZ20A1A4S0G0S3S2SdU10ScZ9A1A4S1G0A1A3A3A3A3").
Definition C1_0 : sstate := ltac2:(tb__ "0|1|
S34S5aS43S21S22A1A1S21S27A1S1S10A1M0G0G0S1SbA1P87A8").
Definition C1 : sstate := add_facts inv1 C1_0.

Definition regs2 (c : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S2SdA2M0S3S2SdUdS21S23A1A4S0G0S3S2SdUeS21S22A1A4S0G0S3S2SdU11Vc;A4S0G0S3S2SdUfScZ9A1A4S0G0S3S2SdU10ScZ20A1A4S1G0A1A3A3A3A3A3").

Definition C2f : sstate := ltac2:(tb__ "0|3|
S34S59S3eS21S22A1M0A1G0S0S10S15S22Z1S12P7aM1A1A3S1S10A1M2A3G2G2S4SbS42G1A1S3dA3P87A8").
Definition C2_0 : sstate := ltac2:(tb__ "0|1|
S34S59S3eS33A1S33S1S10A1M0G0G0S1SbA1P87A8").
Definition C2 : sstate := add_facts inv2 C2_0.

Definition v141 : sv := SVar 141.
Definition v142 : sv := SVar 142.
Definition v143 : sv := SVar 143.
Definition F_nf : list sprop := ltac2:(tb__ "0|0|
S0SbS1cS24S23A2S0SbSfS27S24A2S0SbSfS24S23A2S1SbA1A3A3A3").
Definition F_found : list sprop := ltac2:(tb__ "0|1|
S0SbSfS27S24A2S0SbS13S24S23A2S0SbS13S24S25A2S0SbS14S52S21S24A1S21S23A1A3S0SbSfScZ1A1S30A2S0SbS1cS18S51S24S30A3S26A2S0SbS13S24S26A2S0SbSfS26S23A2S0SbSfS26S25A2S0SbSfS24ScS2fA1M0A2S0SbSfS30G0A2S0SbSfS26G0A2S1SbA1A3A3A3A3A3A3A3A3A3A3A3A3").

Definition P_nf : sstate := ltac2:(tb__ "0|3|
S1aS5bS4dS4eS4bA1S0S6S2SdA2M0S3S2SdUaScZ0A1A4S0G0S3S2SdUeS21S24A1M1A4S1G0A1A3A3A2S4cS17S7SdA1S0SeS29G1A1S0SeS2cS1S10A1M2A1S0SeS2bG2A1S0SeS2aG2A1S1SeA1A3A3A3A3S4SbS40S2eA3P90S5A9").
Definition P_found : sstate := ltac2:(tb__ "0|5|
S1aS5bS4dS4eS4bA1S0S6S2SdA2M0S3S2SdUaScZ1A1A4S0G0S3S2SdUeS21S24A1M1A4S1G0A1A3A3A2S4cS17S7SdA1S0SeS29S21S26A1A1S0SeS2cS1S10A1M2A1S0SeS2bS0S10S15ScZ0A1M3Z8M4G1A3G2A3A1S0SeS2aS0S10S15G3G4S30A3G2A3A1S1SeA1A3A3A3A3S4SbS3fS2eA3P90S5A9").
Definition Posts_nt : list leaf := ltac2:(tb__ "0|0|
S0S56S58S32S57A2S0S56S58S31S57A2S1S56A1A3A3").

Definition cuts_nt : list sstate := ltac2:(tb__ "0|0|
S0S11S2dS0S11S36S0S11S38S0S11S37S1S11A1A3A3A3A3").
Definition exits_nt : list sstate := ltac2:(tb__ "0|0|
S0S11S32S0S11S31S1S11A1A3A3").
Definition cutpcs_nt : list Z := ltac2:(tb__ "0|0|
S0S55S5aS0S55S59S1S55A1A3A3").

Lemma check_nt : ltac2:(tb__ "0|0|
S54S8S4aS47S39S3bS4bS3cS41A6SaA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cuts_nt_strict : ltac2:(tb__ "0|0|
S54S8S67S11S20S3cA3S5A3").
Proof. vm_compute. reflexivity. Qed.

Theorem next_token_sum : ltac2:(tb__ "0|0|
S65OF_;S9S5eA1S5dOF_;F_;S1eS61S47R3R2A3S64S47R4S60S47R3S2dR2A4S5fS47R3S4bR2S3aA5A4F_;Frho;FK;Fok;").
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segs FUEL_nt cutpcs_nt NF cuts_nt exits_nt
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho Posts_nt) Hok).
  - rewrite cuts_nt_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_nt.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[]]]; revert HagE.
    + apply exit_post. in_nth 0.
    + apply exit_post. in_nth 1.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_nt : list vnode := ltac2:(tb__ "0|0|
S0S48S49S2dZ1eScZ0A1A3S0S48S49S36Z14S22A3S0S48S49S38ZfS22A3S0S48S49S37ZaS18S51S22S28A3A3S1S48A1A3A3A3A3").
Definition vexits_nt : list vnode := ltac2:(tb__ "0|1|
S0S48S49S32Z1M0S62A3S0S48S49S31G0S62A3S1S48A1A3A3").

Lemma echeck_nt : ltac2:(tb__ "0|0|
S54S8S66S47S39S3bS4bS45S46A6SaA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem next_token_sum_ex : ltac2:(tb__ "0|0|
S9S5eA1S5dOF_;F_;S1eS63S47S60S47R2S2dR1A4S5fS47R2S4bR1S3aA5A3Frho;FK;").
Proof.
  intros K rho.
  change Pre_nt with (vn_state (mkVN Pre_nt 30 (SLit 0))).
  apply (cfg_complete_autoI segs FUEL_nt cutpcs_nt NF vcuts_nt vexits_nt
           (fun rho' => agree_below NF rho rho') K (LQ segs K NF rho Posts_nt)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_nt.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[<-|[]]]; revert HgE.
    + apply (eexit_post_I0 segs K NF rho vcuts_nt Posts_nt (mkVN P_nf 1 vTop)). in_nth 0.
    + apply (eexit_post_I0 segs K NF rho vcuts_nt Posts_nt (mkVN P_found 1 vTop)). in_nth 1.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
