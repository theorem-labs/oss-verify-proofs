(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "app"; "prod"; "list"; "None"; "false"; "bool"; "true"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SVar"; "SPUle"; "SAlu"; "sobj"; "cell"; "mkCell"; "DUnknown"; "FcsrFrm0"; "mkObj"; "mkSS"; "SPAlign"; "valuation"; "SPUlt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner"; "v120"; "vOut"; "pB"; "pc_state"; "pEnd"; "v128"; "v121"; "cur_lt"; "oEnd"; "v122"; "vT"; "cur_le"; "Pre_pc"; "args1"; "args2"; "out_regs3"; "v123"; "vB"; "vL"; "FUEL_pc"; "O_out12"; "O_stk"; "O_txt"; "X_pc"; "args3"; "cutpcs_pc"; "imax"; "out_regs"; "out_regs2"; "pc_base_facts"; "two40"; "v124"; "vTL"; "C_A1"; "C_A2"; "C_A3"; "C_D1"; "C_D2"; "C_D3"; "C_J1"; "C_J2"; "C_K1"; "C_K2"; "C_K3"; "C_X"; "P_ret"; "Posts_pc"; "cuts_pc"; "gO0"; "gO4"; "gO8"; "stk_cells"; "exits_pc"; "shO0"; "shO4"; "shO8"; "sh_facts"; "sh_regs"; "spo"; "two47"; "vcuts_pc"; "vexits_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "mkLeafA"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "shb"; "A_globals"; "F8x"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "cut_regs"; "post_regs"; "pre_regs"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner.ParseCornerAddr"; "pc_A1"; "pc_A2"; "pc_A3"; "pc_D1"; "pc_D2"; "pc_D3"; "pc_J1"; "pc_J2"; "pc_K1"; "pc_K2"; "pc_K3"; "pc_X"; "pc_entry"; "pc_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"].
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

Module ParseCornerAddr.
  Definition pc_entry : Z := 0x9c930.
  Definition pc_K1 : Z := 0x9c9dc.
  Definition pc_A1 : Z := 0x9ca0c.
  Definition pc_D1 : Z := 0x9cac8.
  Definition pc_J1 : Z := 0x9cb70.
  Definition pc_K2 : Z := 0x9cbdc.
  Definition pc_A2 : Z := 0x9cc10.
  Definition pc_D2 : Z := 0x9cca0.
  Definition pc_J2 : Z := 0x9cd4c.
  Definition pc_K3 : Z := 0x9cd90.
  Definition pc_A3 : Z := 0x9cdc4.
  Definition pc_D3 : Z := 0x9ce50.
  Definition pc_X  : Z := 0x9cef0.
  Definition pc_ret : Z := 0x9cab4.
End ParseCornerAddr.
Import ParseCornerAddr.

Definition FUEL_pc : nat := 400%nat.

Definition vB : sv := SVar 15.
Definition vT : sv := SVar 16.
Definition vTL : sv := SVar 13.
Definition vL : sv := SVar 18.
Definition vOut : sv := SVar 35.
Definition pB (off : sv) : sv := SAlu ALU_ADD vB off.
Definition oEnd : sv := SAlu ALU_ADD vT vTL.
Definition pEnd : sv := pB oEnd.
Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
S11S62SfPaA1SdVk;A1A3").
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.

Definition pc_base_facts : list sprop := ltac2:(tb__ "0|4|
S0SeS10S24S2eA2S0SeS10S26SdS3aA1M0A2S0SeS10S3cG0A2S0SeS10S2eG0A2S0SeS10S2dSdS57A1M1A2S0SeS10SdZ1A1S2dA2S0SeS10SfPeA1G0A2S0SeS10SfP21A1G0A2S0SeS10SfP22A1G0A2S0SeS19P23Z2A2S0SeS19PaM2Z4A2S0SeS10SdZ10000A1SfG2A1M3A2S0SeS10G3G1A2S0SeS10S1dG1A2S3SeA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17SfPaA1SdN40A1SdZ0A1Vcells;S15A5").
Definition O_txt : sobj := ltac2:(tb__ "0|0|
S17S2dSdZ0A1S2eS3S13A1S15A5").
Definition O_out12 (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17S1dSdZ0A1SdZcA1Vcells;S15A5").
Definition X_pc : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5ScScA2M0S2ScScS2dS2eA4S0G0S2ScScS1dSdZcA1A4S3G0A1A3A3").

Definition Pre_pc : axst := ltac2:(tb__ "0|2|
S68S18S7cS6bS6eS0S5S1ScA2M0S2S1ScUaS1eS26A1A4S3G0A1A3A2S6aS16S7ScA1S4S12S0S12S31S3S13A1M1A1S0S12S32S0S12S30G1A1S3S12A1A3A3A3S66A3S39S69S8A9S33A2").

Definition stk_cells : list cell := ltac2:(tb__ "0|1|
S0S13S14SdN8A1Z8M0SfPbA1A3S0S13S14SdN10A1G0SfP1cA1A3S0S13S14SdN18A1G0SfP1dA1A3S0S13S14SdN20A1G0SfP26A1A3S0S13S14SdN28A1G0SfP27A1A3S0S13S14SdN30A1G0SfP28A1A3S0S13S14SdN38A1G0SfP29A1A3S3S13A1A3A3A3A3A3A3A3").

Definition cutpcs_pc : list Z := ltac2:(tb__ "0|0|
S0S61S78S0S61S70S0S61S73S0S61S76S0S61S79S0S61S71S0S61S74S0S61S77S0S61S7aS0S61S72S0S61S75S0S61S7bS3S61A1A3A3A3A3A3A3A3A3A3A3A3A3").

Definition gO0 : positive := 125%positive.
Definition gO4 : positive := 126%positive.
Definition gO8 : positive := 127%positive.
Definition shO0 : sv := ltac2:(tb__ "0|0|
S11S62SfS4cA1S65A3").
Definition shO4 : sv := ltac2:(tb__ "0|0|
S11S62SfS4dA1S65A3").
Definition shO8 : sv := ltac2:(tb__ "0|0|
S11S62SfS4eA1S65A3").
Definition sh_regs (n : nat) : list (nat * sv) := ltac2:(tb__ "0|5|
S1S6S5S1ScA2M0A1M1Ln;Vn;S3G0A1M2S1S1G1Ln0;R1S0G0S2S1ScU7S52A4M3G2A3S1S1G1Ln1;R1S0G0G3S0G0S2S1ScU1dS53A4M4G2A3A3S1S1G1Ln2;R1S0G0G3S0G0G4S0G0S2S1ScU1eS51A4G2A3A3A3S1G2Ln3;X1x2Ln2;X1x2Ln1;X1x2Ln0;X1x2").
Definition sh_facts (n : nat) : list sprop := ltac2:(tb__ "0|4|
S1S6SeA1M0Ln;Vn;S3SeA1M1S1S1G0Ln0;R1S67S4dS11S62S1dSdZ4A1A3A2M2S1S1G0Ln1;R1S4SeG2S67S4eS11S62S1dSdZ8A1A3A2M3A3S1S1G0Ln2;R1S4SeG2S4SeG3S67S4cS1dA2A3A3S1G1Ln3;X1x2Ln2;X1x2Ln1;X1x2Ln0;X1x2").

Definition args3 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S1ScA2M0S2S1ScUcSfPeA1A4S0G0S2S1ScUdSfP21A1A4S0G0S2S1ScUeSfP22A1A4S3G0A1A3A3A3").
Definition args2 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S1ScA2M0S2S1ScUdSfP21A1A4S0G0S2S1ScUeSfP22A1A4S3G0A1A3A3").
Definition args1 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S1ScA2M0S2S1ScUeSfP22A1A4S3G0A1A3").

Definition pc_state (n : nat) (pc : Z) (regs : list (nat * sv)) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|1|
S68S18Vpc;S6bS6cS69A1S4S5S1ScA2M0S0G0S2S1ScU2S56N40A1A4S0G0S2S1ScU8SfP6cA1A4S0G0S2S1ScU9SfP6dA1A4S0G0S2S1ScU12SfP76A1A4S0G0S2S1ScU13SfP77A1A4S0G0S2S1ScU14SfP8aA1A4S0G0S2S1ScU15SfP8bA1A4S0G0S2S1ScU1cS65A4S3G0A1A3A3A3A3A3A3A3A3S4G0S55Vn;A1Vregs;A3A3A2S6aS16S7ScA1S4S12S0S12S31S4fA1S0S12S32S0S12S30S3S13A1A1S3S12A1A3A3A3S66A3S4SeVfacts;S4SeS54Vn;A1S39A3A3Vnx;S8A9S33A2").

Definition cur_lt (w : sv) : list sprop := ltac2:(tb__ "0|0|
S0SeS10S26Vw;A2S0SeS1bVw;S24A2S0SeS10Vw;SdS3aA1A2S3SeA1A3A3A3").
Definition cur_le (w : sv) : list sprop := ltac2:(tb__ "0|0|
S0SeS10S26Vw;A2S0SeS10Vw;S24A2S0SeS10Vw;SdS3aA1A2S3SeA1A3A3A3").

Definition v120 : sv := SVar 132.
Definition v121 : sv := SVar 133.

Definition C_K1 : axst := ltac2:(tb__ "0|2|
S1fU3S78S4S5S1ScA2M0S34S0G0S2S1ScU5S1eS26A1A4S0G0S2S1ScU6S1eS1cA1M1A4S0G0S2S1ScU10G1A4S0G0S2S1ScU9S11S63S24S1cA3A4S0G0S2S1ScU8SdZ9A1A4S0G0S2S1ScU1fSdZ20A1A4S0G0S2S1ScUaS11S62S1dSdZ4A1A3A4S0G0S2S1ScU11S11S62S1dSdZ8A1A3A4S0G0S2S1ScUfS1dA4S0G0S2S1ScUbS3cA4S3G0A1A3A3A3A3A3A3A3A3A3A3A3S23S1cA1P91A5").

Definition out_regs : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S1ScA2M0S2S1ScUaS11S62S1dSdZ4A1A3A4S0G0S2S1ScU11S11S62S1dSdZ8A1A3A4S0G0S2S1ScUfS1dA4S3G0A1A3A3A3").

Definition C_A1 : axst := ltac2:(tb__ "0|1|
S1fU3S70S4S5S1ScA2M0S34S4G0S0G0S2S1ScU5S1eS26A1A4S0G0S2S1ScUbS3cA4S0G0S2S1ScU10S1eS1cA1A4S3G0A1A3A3A3S37A3A3S27S1cA1P91A5").

Definition imax : Z := 0x7fffffff.
Definition v122 : sv := SVar 134.
Definition v123 : sv := SVar 135.
Definition v124 : sv := SVar 136.
Definition v128 : sv := SVar 137.

Definition C_D1 : axst := ltac2:(tb__ "0|2|
S1fU3S73S4S5S1ScA2M0S34S4G0S0G0S2S1ScUbS1eS22A1M1A4S0G0S2S1ScU10G1A4S0G0S2S1ScU5S20A4S0G0S2S1ScU6S25A4S0G0S2S1ScU8SdZ9A1A4S0G0S2S1ScU9SdZaA1A4S0G0S2S1ScU12SdS36A1A4S0G0S2S1ScU13S3bA4S0G0S2S1ScU1fS2cA4S3G0A1A3A3A3A3A3A3A3A3A3S37A3A3S4SeS23S22A1S0SeS10S25SdZ1A1A2S3SeA1A3A3P91A5").

Definition C_J1 : axst := ltac2:(tb__ "0|1|
S1fU3S76S4S5S1ScA2M0S2aS4G0S0G0S2S1ScU1fS2cA4S0G0S2S1ScU6S21A4S0G0S2S1ScU10S1eS1cA1A4S0G0S2S1ScU5S20A4S3G0A1A3A3A3A3S37A3A3S27S1cA1P91A5").

Definition out_regs2 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S1ScA2M0S2S1ScUaS11S62S1dSdZ4A1A3A4S0G0S2S1ScU11S11S62S1dSdZ8A1A3A4S3G0A1A3A3").

Definition out_regs3 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S1ScA2M0S2S1ScUaS11S62S1dSdZ4A1A3A4S3G0A1A3").

Definition C_K2 : axst := ltac2:(tb__ "0|2|
S1fU2S79S4S5S1ScA2M0S2aS4G0S0G0S2S1ScU10S1eS1cA1M1A4S0G0S2S1ScUbG1A4S0G0S2S1ScUcSdZ20A1A4S0G0S2S1ScUfSdZ9A1A4S0G0S2S1ScU6S21A4S0G0S2S1ScU5S20A4S3G0A1A3A3A3A3A3A3S38A3A3S23S1cA1P91A5").

Definition C_A2 : axst := ltac2:(tb__ "0|1|
S1fU2S71S4S5S1ScA2M0S2aS4G0S0G0S2S1ScU10S1eS1cA1A4S0G0S2S1ScU6S21A4S0G0S2S1ScU5S20A4S3G0A1A3A3A3S38A3A3S27S1cA1P91A5").

Definition C_D2 : axst := ltac2:(tb__ "0|2|
S1fU2S74S4S5S1ScA2M0S2aS4G0S0G0S2S1ScUcS1eS22A1M1A4S0G0S2S1ScUbG1A4S0G0S2S1ScU5S20A4S0G0S2S1ScU6S21A4S0G0S2S1ScUfS25A4S0G0S2S1ScU1fSdZ9A1A4S0G0S2S1ScU10SdZaA1A4S0G0S2S1ScU8SdS36A1A4S0G0S2S1ScU9S3bA4S0G0S2S1ScU1eS2cA4S3G0A1A3A3A3A3A3A3A3A3A3A3S38A3A3S4SeS23S22A1S0SeS10S25SdZ1A1A2S3SeA1A3A3P91A5").

Definition C_J2 : axst := ltac2:(tb__ "0|1|
S1fU1S77S4S5S1ScA2M0S29S4G0S0G0S2S1ScU10S1eS1cA1A4S0G0S2S1ScU6S21A4S0G0S2S1ScU5S20A4S3G0A1A3A3A3S2bA3A3S27S1cA1P91A5").

Definition C_K3 : axst := ltac2:(tb__ "0|2|
S1fU1S7aS4S5S1ScA2M0S29S4G0S0G0S2S1ScUbS1eS1cA1M1A4S0G0S2S1ScU10G1A4S0G0S2S1ScUcSdZ20A1A4S0G0S2S1ScUdSdZ9A1A4S0G0S2S1ScU6S21A4S0G0S2S1ScU5S20A4S3G0A1A3A3A3A3A3A3S2bA3A3S23S1cA1P91A5").

Definition C_A3 : axst := ltac2:(tb__ "0|1|
S1fU1S72S4S5S1ScA2M0S29S4G0S0G0S2S1ScUbS1eS1cA1A4S0G0S2S1ScU6S21A4S0G0S2S1ScU5S20A4S3G0A1A3A3A3S2bA3A3S27S1cA1P91A5").

Definition C_D3 : axst := ltac2:(tb__ "0|2|
S1fU1S75S4S5S1ScA2M0S29S4G0S0G0S2S1ScUbS1eS22A1M1A4S0G0S2S1ScUcG1A4S0G0S2S1ScU5S20A4S0G0S2S1ScU6S21A4S0G0S2S1ScUdS25A4S0G0S2S1ScU10SdZ9A1A4S0G0S2S1ScU11SdZaA1A4S0G0S2S1ScU1dSdS36A1A4S0G0S2S1ScU1eS3bA4S0G0S2S1ScUfS2cA4S3G0A1A3A3A3A3A3A3A3A3A3A3S2bA3A3S4SeS23S22A1S0SeS10S25SdZ1A1A2S3SeA1A3A3P91A5").

Definition C_X : axst := ltac2:(tb__ "0|1|
S1fU0S7bS0S5S1ScA2M0S2S1ScU6S21A4S3G0A1A3S3SeA1P91A5").

Definition P_ret : axst := ltac2:(tb__ "0|1|
S68S18S7dS6bS6dS69A1S0S5S1ScA2M0S2S1ScUaSfP8cA1A4S3G0A1A3A2S6aS16S7ScA1S4S12S0S12S31S4fA1S0S12S32S0S12S30S3S13A1A1S3S12A1A3A3A3S66A3S39P96S8A9S33A2").
Definition Posts_pc : list leafA := ltac2:(tb__ "0|0|
S0S5fS60S49S87A2S3S5fA1A3").

Definition cuts_pc : list axst := ltac2:(tb__ "0|0|
S0S5eS28S0S5eS45S0S5eS3dS0S5eS40S0S5eS43S0S5eS46S0S5eS3eS0S5eS41S0S5eS44S0S5eS47S0S5eS3fS0S5eS42S0S5eS48S3S5eA1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exits_pc : list axst := [P_ret].

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Definition check_pc__runs : ltac2:(tb__ "0|0|
S6SbS6S5fA1A1A1") := ltac2:(tb__ "0|0|
S88S64S2fS35S4bA4").
Lemma check_pc : ltac2:(tb__ "0|0|
S6fS9S5cS64S2fS35S69S4bS50A6SaA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUEL_pc cutpcs_pc NF cuts_pc exits_pc check_pc__runs); [unfold check_pc__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem parse_corner_sum : ltac2:(tb__ "0|0|
S86OF_;S80S1aS6S83Q40A1A1S82S64R4R3A3S81S64S69R4A3S85S64R6S7fS64R5S28R4R3A5S7eS64R5S69R4R3S4aA6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_pc rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_pc cutpcs_pc NF cuts_pc exits_pc (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_pc) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_pc.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply exit_postA. in_nth 0.
  - left; reflexivity.
Qed.

Definition vcuts_pc : list vnodeA := ltac2:(tb__ "0|3|
S0S5aS5bS28Z5aSdZ0A1M0A3S0S5aS5bS45Z50S11S63S24S1cA3M1A3S0S5aS5bS3dZ46G0A3S0S5aS5bS40Z3cS11S63S24S22A3M2A3S0S5aS5bS43Z32G0A3S0S5aS5bS46Z2dG1A3S0S5aS5bS3eZ28G0A3S0S5aS5bS41Z23G2A3S0S5aS5bS44Z1eG0A3S0S5aS5bS47Z19G1A3S0S5aS5bS3fZ14G0A3S0S5aS5bS42ZfG2A3S0S5aS5bS48Z5G0A3S3S5aA1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition vexits_pc : list vnodeA := ltac2:(tb__ "0|0|
S0S5aS5bS49Z1SdZ0A1A3S3S5aA1A3").

Lemma echeck_pc : ltac2:(tb__ "0|0|
S6fS9S5dS64S2fS35S69S58S59A6SaA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUEL_pc cutpcs_pc NF vcuts_pc vexits_pc check_pc__runs); [unfold check_pc__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem parse_corner_sum_ex : ltac2:(tb__ "0|0|
S80S1aS6S83Q40A1A1S81S64S69R3A3S84S64S7fS64R4S28R3R2A5S7eS64R4S69R3R2S4aA6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_pc rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_pc with (vna_state (mkVNA Pre_pc 90 (SLit 0))).
  apply (cfg_complete_autoA segs FUEL_pc cutpcs_pc NF vcuts_pc vexits_pc (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_pc) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbv; congruence.
  - exact echeck_pc.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply (eexit_postA segs J NF rho vcuts_pc Posts_pc (mkVNA P_ret 1 (SLit 0))). in_nth 0.
  - left; reflexivity.
Qed.
