(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "prod"; "false"; "None"; "bool"; "app"; "list"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "sprop"; "SPUle"; "sobj"; "sstate"; "cell"; "SPUlt"; "FcsrFrm0"; "mkSS"; "DUnknown"; "mkCell"; "mkObj"; "SAlu"; "valuation"; "SPAlign"; "SPEq"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "mkVN"; "check_cfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner"; "vT"; "pB"; "oEnd"; "m1"; "pc_state"; "pEnd"; "O_txt"; "Pre_pc"; "base_facts"; "O_out"; "P_early"; "P_ret"; "imax"; "vB"; "vL"; "vOut"; "vTL"; "C_D1"; "C_D2"; "C_D3"; "C_S1"; "C_S2"; "C_S3"; "FUEL_pc"; "Posts_pc"; "cutpcs_pc"; "cuts_pc"; "two40"; "exits_pc"; "two47"; "vcuts_pc"; "vexits_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "cut_regs"; "pre_regs"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "vTop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner.ParseCornerAddr"; "pc_D1"; "pc_D2"; "pc_D3"; "pc_S1"; "pc_S2"; "pc_S3"; "pc_entry"; "pc_ret0"; "pc_ret1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue"; "check_ecfgI"; "@Stdlib.Lists.List"; "existsb"].
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

Module ParseCornerAddr.
  Definition pc_entry : Z := 0x1a15c.
  Definition pc_S1 : Z := 0x1a194.
  Definition pc_D1 : Z := 0x1a214.
  Definition pc_S2 : Z := 0x1a2d0.
  Definition pc_D2 : Z := 0x1a34c.
  Definition pc_S3 : Z := 0x1a3f8.
  Definition pc_D3 : Z := 0x1a470.
  Definition pc_ret0 : Z := 0x1a204.
  Definition pc_ret1 : Z := 0x1a4e4.
End ParseCornerAddr.
Import ParseCornerAddr.

Definition FUEL_pc : nat := 400%nat.

Definition vB : sv := SVar 15.
Definition vT : sv := SVar 16.
Definition vTL : sv := SVar 13.
Definition vL : sv := SVar 18.
Definition vOut : sv := SVar 35.
Definition pB (off : sv) : sv := SAlu ALU_ADD vB off.
Definition pEnd : sv := ltac2:(tb__ "0|0|
S19S4fS22S21A1S31A3").
Definition oEnd : sv := SAlu ALU_ADD vT vTL.
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.
Definition imax : Z := 0x7fffffff.
Definition m1 : Z := 18446744073709551615.

Definition base_facts : list sprop := ltac2:(tb__ "0|1|
S0SeSfS23S2fA2S0SeSfS21SdS3cA1M0A2S0SeSfS31G0A2S0SeSfS2fG0A2S0SeSfS2eSdS3eA1A2S0SeSfSdZ1A1S2eA2S0SeS1bP23Z2A2S3SeA1A3A3A3A3A3A3A3").

Definition O_txt (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S2eSdZ0A1S2fVcells;S16A5").
Definition O_out (c0 c4 c8 : sv) : sobj := ltac2:(tb__ "0|2|
S18S30SdZ0A1M0SdZcA1S0S12S17G0Z4M1Vc0;A3S0S12S17SdG1A1G1Vc4;A3S0S12S17SdZ8A1G1Vc8;A3S3S12A1A3A3A3S16A5").

Definition Pre_pc : sstate := ltac2:(tb__ "0|2|
S15S5aS44S47S0S4S1SbA2M0S2S1SbUaS22S21A1A4S3G0A1A3A2S43S14S6SbA1S0S10S27S3S12A1M1A1S0S10S18S30SdZ0A1SdZcA1G1S16A5S3S10A1A3A3S29S42S5A9").

Definition pc_state (pc : Z) (regs : list (nat * sv)) (c0 c4 c8 : sv) (facts : list sprop) : sstate := ltac2:(tb__ "0|1|
S15Vpc;S44S46S42A1S8S4S1SbA2M0S0G0S2S1SbUfS30A4S3G0A1A3Vregs;A3A2S43S14S6SbA1S0S10S27S3S12A1A1S0S10S2aVc0;Vc4;Vc8;A3S3S10A1A3A3S8SeVfacts;S29A3P91S5A9").

Definition C_S1 : sstate := ltac2:(tb__ "0|5|
S25S57S0S4S1SbA2M0S2S1SbUaS22S21A1A4S0G0S2S1SbUbS31A4S0G0S2S1SbUcScPeA1A4S0G0S2S1SbUdScP21A1A4S0G0S2S1SbUeScP22A1A4S0G0S2S1SbU10S22ScP84A1M1A1A4S0G0S2S1SbU6ScP85A1M2A4S0G0S2S1SbU11SdZ20A1A4S0G0S2S1SbU5SdZ9A1A4S3G0A1A3A3A3A3A3A3A3A3A3SdS24A1M3G3G3S0SeS13G1S23A2S0SeS1cS19S4fG1G2A3S23A2S0SeSfSdZ1A1G2A2S0SeSfS21G1A2S0SeSfG1SdS3cA1M4A2S0SeSfG2G4A2S3SeA1A3A3A3A3A3A3A6").

Definition C_D1 : sstate := ltac2:(tb__ "0|4|
S25S54S0S4S1SbA2M0S2S1SbUbS26A4S0G0S2S1SbUcScPeA1A4S0G0S2S1SbUdScP21A1A4S0G0S2S1SbUeScP22A1A4S0G0S2S1SbU10S22ScP84A1M1A1A4S0G0S2S1SbUaScP86A1M2A4S0G0S2S1SbU11ScP87A1A4S0G0S2S1SbU1cScP88A1A4S0G0S2S1SbU6SdZaA1A4S0G0S2S1SbU7SdS2dA1A4S0G0S2S1SbU5SdZ9A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3SdS24A1M3G3G3S0SeS13G1S23A2S0SeSfS21G1A2S0SeSfG2SdZ1A1A2S3SeA1A3A3A3A6").

Definition C_S2 : sstate := ltac2:(tb__ "0|3|
S25S58S0S4S1SbA2M0S2S1SbUbS26A4S0G0S2S1SbUdScP21A1A4S0G0S2S1SbUeScP22A1A4S0G0S2S1SbU10S22ScP84A1M1A1A4S0G0S2S1SbUcSdZ20A1A4S0G0S2S1SbU11SdZ9A1A4S3G0A1A3A3A3A3A3A3ScP8dA1SdS24A1M2G2S0SeS13G1S23A2S0SeSfS21G1A2S3SeA1A3A3A6").

Definition C_D2 : sstate := ltac2:(tb__ "0|4|
S25S55S0S4S1SbA2M0S2S1SbUbS26A4S0G0S2S1SbUdScP21A1A4S0G0S2S1SbUeScP22A1A4S0G0S2S1SbU5S22ScP84A1M1A1A4S0G0S2S1SbUcScP86A1M2A4S0G0S2S1SbU11ScP87A1A4S0G0S2S1SbU1cScP88A1A4S0G0S2S1SbU10SdZaA1A4S0G0S2S1SbU7SdS2dA1A4S0G0S2S1SbU6SdZ9A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3ScP8dA1SdS24A1M3G3S0SeS13G1S23A2S0SeSfS21G1A2S0SeSfG2SdZ1A1A2S3SeA1A3A3A3A6").

Definition C_S3 : sstate := ltac2:(tb__ "0|2|
S25S59S0S4S1SbA2M0S2S1SbUbS26A4S0G0S2S1SbUeScP22A1A4S0G0S2S1SbU10S22ScP84A1M1A1A4S0G0S2S1SbUcSdZ20A1A4S0G0S2S1SbUdSdZ9A1A4S3G0A1A3A3A3A3A3ScP8dA1SdS24A1ScP8fA1S0SeS13G1S23A2S0SeSfS21G1A2S3SeA1A3A3A6").

Definition C_D3 : sstate := ltac2:(tb__ "0|3|
S25S56S0S4S1SbA2M0S2S1SbUbS26A4S0G0S2S1SbUeScP22A1A4S0G0S2S1SbU10S22ScP84A1M1A1A4S0G0S2S1SbUcScP86A1M2A4S0G0S2S1SbUdScP87A1A4S0G0S2S1SbU7ScP88A1A4S0G0S2S1SbU5SdZaA1A4S0G0S2S1SbU6SdS2dA1A4S0G0S2S1SbU11SdZ9A1A4S3G0A1A3A3A3A3A3A3A3A3A3ScP8dA1SdS24A1ScP8fA1S0SeS13G1S23A2S0SeSfS21G1A2S0SeSfG2SdZ1A1A2S3SeA1A3A3A3A6").

Definition P_early : sstate := ltac2:(tb__ "0|1|
S15S5bS44S45S42A1S0S4S1SbA2M0S2S1SbUaSdZ0A1A4S3G0A1A3A2S43S14S6SbA1S0S10S27S3S12A1A1S0S10S2aScP8dA1ScP8eA1ScP8fA1A3S3S10A1A3A3S29P96S5A9").
Definition P_ret : sstate := ltac2:(tb__ "0|1|
S15S5cS44S45S42A1S0S4S1SbA2M0S2S1SbUaScP8cA1A4S3G0A1A3A2S43S14S6SbA1S0S10S27S3S12A1A1S0S10S2aScP8dA1ScP8eA1ScP8fA1A3S3S10A1A3A3S29P96S5A9").
Definition Posts_pc : list leaf := ltac2:(tb__ "0|0|
S0S4aS4cS2bS4bA2S0S4aS4cS2cS4bA2S3S4aA1A3A3").

Definition cuts_pc : list sstate := ltac2:(tb__ "0|0|
S0S11S28S0S11S35S0S11S32S0S11S36S0S11S33S0S11S37S0S11S34S3S11A1A3A3A3A3A3A3A3").
Definition exits_pc : list sstate := ltac2:(tb__ "0|0|
S0S11S2bS0S11S2cS3S11A1A3A3").
Definition cutpcs_pc : list Z := ltac2:(tb__ "0|0|
S0S48S57S0S48S54S0S48S58S0S48S55S0S48S59S0S48S56S3S48A1A3A3A3A3A3A3").

Lemma check_pc : ltac2:(tb__ "0|0|
S49S7S20S41S38S3aS42S3bS3dA6SaA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cuts_pc_strict : ltac2:(tb__ "0|0|
S49S7S61S11S1dS3bA3S5A3").
Proof. vm_compute. reflexivity. Qed.

Theorem parse_corner_sum : ltac2:(tb__ "0|0|
S5fOF_;S9S4eA1S4dOF_;F_;S1aS52S41R3R2A3S5eS41R4S51S41R3S28R2A4S50S41R3S42R2S39A5A4F_;Frho;FK;Fok;").
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segs FUEL_pc cutpcs_pc NF cuts_pc exits_pc
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho Posts_pc) Hok).
  - rewrite cuts_pc_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_pc.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[]]]; revert HagE.
    + apply exit_post. in_nth 0.
    + apply exit_post. in_nth 1.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_pc : list vnode := ltac2:(tb__ "0|1|
S0S1eS1fS28Z5aSdZ0A1A3S0S1eS1fS35Z50ScP84A1M0A3S0S1eS1fS32Z46G0A3S0S1eS1fS36Z3cG0A3S0S1eS1fS33Z32G0A3S0S1eS1fS37Z28G0A3S0S1eS1fS34Z1eG0A3S3S1eA1A3A3A3A3A3A3A3").
Definition vexits_pc : list vnode := ltac2:(tb__ "0|1|
S0S1eS1fS2bZ1M0S53A3S0S1eS1fS2cG0S53A3S3S1eA1A3A3").

Lemma echeck_pc : ltac2:(tb__ "0|0|
S49S7S60S41S38S3aS42S3fS40A6SaA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem parse_corner_sum_ex : ltac2:(tb__ "0|0|
S9S4eA1S4dOF_;F_;S1aS5dS41S51S41R2S28R1A4S50S41R2S42R1S39A5A3Frho;FK;").
Proof.
  intros K rho.
  change Pre_pc with (vn_state (mkVN Pre_pc 90 (SLit 0))).
  apply (cfg_complete_autoI segs FUEL_pc cutpcs_pc NF vcuts_pc vexits_pc
           (fun rho' => agree_below NF rho rho') K (LQ segs K NF rho Posts_pc)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_pc.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[<-|[]]]; revert HgE.
    + apply (eexit_post_I0 segs K NF rho vcuts_pc Posts_pc (mkVN P_early 1 vTop)). in_nth 0.
    + apply (eexit_post_I0 segs K NF rho vcuts_pc Posts_pc (mkVN P_ret 1 vTop)). in_nth 1.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
