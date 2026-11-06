(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "app"; "prod"; "false"; "None"; "bool"; "list"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SVar"; "SPUle"; "cell"; "sobj"; "mkCell"; "SAlu"; "FcsrFrm0"; "mkSS"; "DUnknown"; "SPBranch"; "mkObj"; "valuation"; "SPAlign"; "SPUlt"; "holds"; "ss_facts"; "SExt"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "pB"; "v173"; "v172"; "v174"; "vE"; "CI"; "sd_state"; "vI"; "skip_facts"; "vL"; "X_sd"; "base_facts"; "cur_lt"; "O_out"; "O_pp"; "O_stk"; "O_txt"; "vB"; "Pre_sd"; "rem"; "stk_cells"; "two40"; "C1"; "CN"; "Cs"; "F8_pp"; "F_sd"; "NXC"; "NXP"; "P_none"; "P_num"; "X_t1"; "X_t2"; "X_t3"; "chain_facts"; "cur_le"; "cut_fregs"; "gW"; "post_fregs"; "post_objs"; "sh_cur"; "sh_pp"; "x_facts"; "Ce"; "Cen"; "Cm"; "Cp"; "Cx"; "FUEL_sd"; "Posts_sd"; "chain_cuts"; "chain_pcs"; "cutpcs_sd"; "cuts_sd"; "exits_sd"; "fcallee_saved"; "g_pp"; "sd_state_txt"; "two26"; "two47"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "setregs"; "cut_regs"; "post_regs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "A_globals"; "shb"; "F8x"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_OR"; "BC_LTU"; "BC_NE"; "@Corelib.Init.Logic"; "False"; "eq"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "seq"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double.ScanDoubleAddr"; "sd_L1"; "sd_Le"; "sd_Lm"; "sd_Lp"; "sd_Ls"; "sd_Lx"; "sd_ret"; "pow10_tab"; "sd_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "ok_frameA"; "stableA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "pow"; "@stdpp.bitvector.definitions"; "bv"].
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

Module ScanDoubleAddr.
  Definition sd_entry : Z := 0x9a4cc.
  Definition sd_L1 : Z := 0x9a534.
  Definition sd_Ls : Z := 0x9a5c4.
  Definition sd_Lm : Z := 0x9aa18.
  Definition sd_Le : Z := 0x9ab94.
  Definition sd_Lx : Z := 0x9ac08.
  Definition sd_Lp : Z := 0x9aca8.
  Definition sd_ret : Z := 0x9ab7c.
  Definition pow10_tab : Z := 0x239c0.
End ScanDoubleAddr.
Import ScanDoubleAddr.

Definition FUEL_sd : nat := 500%nat.

Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition cut_fregs : list sv := ltac2:(tb__ "0|0|
S74S1SbS1S8SbL_;S5bR1A1SeS81S76U3cR1A2A1A1SeS81S76U8cR1A2A1A1X8x2Lr;S75U0U20A2A4").
Definition post_fregs : list sv := cut_fregs.
Definition NXC : positive := 200%positive.
Definition NXP : positive := 174%positive.

Definition vB : sv := SVar 15.
Definition vI : sv := SVar 16.
Definition vE : sv := SVar 17.
Definition vL : sv := SVar 18.
Definition pB (off : sv) : sv := SAlu ALU_ADD vB off.
Definition two40 : Z := 2 ^ 40.
Definition two26 : Z := 2 ^ 26.
Definition two47 : Z := 2 ^ 47.

Definition base_facts : list sprop := ltac2:(tb__ "0|4|
S0ScSfS2bS28A2S0ScSfS28S2dA2S0ScSfS2dSdS5eA1A2S0ScSfS35SdS5fA1M0A2S0ScSfSdZ1A1S35A2S0ScS1aPcM1Z3M2A2S0ScS1aPeM3G2A2S0ScS1aPaZ4A2S0ScSfSeG1A1G0A2S0ScSfSeG3A1G0A2S3ScA1A3A3A3A3A3A3A3A3A3A3").

Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18SePaA1SdN30A1SdZ0A1Vcells;S16A5").
Definition O_pp (c0 : sv) : sobj := ltac2:(tb__ "0|2|
S18SePcA1SdZ0A1M0SdZ8M1A1S0S10S12G0G1Vc0;A3S3S10A1A3S16A5").
Definition O_txt (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S35SdZ0A1S2dVcells;S16A5").
Definition O_out (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18SePeA1SdZ0A1SdZ8A1Vcells;S16A5").
Definition X_sd : list (sv * sv) := ltac2:(tb__ "0|2|
S0S5SbSbA2M0S2SbSbSePcA1SdZ8A1M1A4S0G0S2SbSbS35S2dA4S0G0S2SbSbSePeA1G1A4S0G0S2SbSbSdS7eA1SdZb8A1A4S3G0A1A3A3A3A3").

Definition Pre_sd : axst := ltac2:(tb__ "0|2|
S68S15S7fS62S66S0S5S1SbA2M0S2S1SbUbS24S28A1A4S3G0A1A3A2S65S14S7SbA1S4S11S0S11S33S3S10A1M1A1S0S11S32S24S2bA1A1S0S11S34G1A1S0S11S31G1A1S3S11A1A3A3A3A3S69A3S2fS61S6A9S2eA2").

Definition cur_lt (c : sv) : list sprop := ltac2:(tb__ "0|0|
S0ScS1bVc;S28A2S0ScS1bVc;S2dA2S0ScSfS2bVc;A2S0ScSfVc;SdS39A1A2S0ScS17S6fS24Vc;A1S24S28A1A3S3ScA1A3A3A3A3A3").
Definition cur_le (c : sv) : list sprop := ltac2:(tb__ "0|0|
S0ScSfS2bVc;A2S0ScSfVc;S28A2S0ScSfVc;SdS39A1A2S3ScA1A3A3A3").

Definition v172 : sv := SVar 172.
Definition v173 : sv := SVar 173.
Definition v174 : sv := SVar 174.

Definition stk_cells : list cell := ltac2:(tb__ "0|1|
S0S10S12SdN8A1Z8M0SePbA1A3S0S10S12SdN10A1G0SeP1cA1A3S0S10S12SdN18A1G0SeP1dA1A3S0S10S12SdN20A1G0SeP26A1A3S0S10S12SdN28A1G0SeP27A1A3S0S10S12SdN30A1G0SeP28A1A3S3S10A1A3A3A3A3A3A3").
Definition g_pp : positive := 125%positive.
Definition F8_pp : list sprop := F8x g_pp (SVar 12).
Definition sh_pp : sv := ltac2:(tb__ "0|0|
S13S6cSeS5cA1S6aA3").

Definition sd_state (pc : Z) (regs : list (nat * sv)) (fregs : list (nat * sv)) (c0 : sv) (out : list cell)
           (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S68S15Vpc;S62S63S61A1S4S5S1SbA2M0S0G0S2S1SbU2S13S6cSePaA1SdN30A1A3A4S0G0S2S1SbU8SeP6cA1A4S0G0S2S1SbU9SeP6dA1A4S0G0S2S1SbU12SeP76A1A4S0G0S2S1SbU13SeP77A1A4S0G0S2S1SbU14SeP78A1A4S0G0S2S1SbUaSePcA1A4S0G0S2S1SbUbS24S28A1A4S0G0S2S1SbUcSePeA1A4S0G0S2S1SbU10S4dA4S0G0S2S1SbU11S6aA4S3G0A1A3A3A3A3A3A3A3A3A3A3A3Vregs;A3A2S62S48Vfregs;A2S14S7SbA1S4S11S0S11S33S38A1S0S11S32Vc0;A1S0S11S34S3S10A1A1S0S11S31Vout;A1S3S11A1A3A3A3A3S69A3S4ScVfacts;S4ScS3dS2fA3A3S3fS6A9S2eA2").

Definition C1 : axst := ltac2:(tb__ "0|3|
S2aS77S0S5S1SbA2M0S2S1SbUdS24S26A1M1A4S0G0S2S1SbUeG1A4S0G0S2S1SbUfSdZ20A1A4S0G0S2S1SbU5SdZ9A1A4S3G0A1M2A3A3A3A3G2S24S2bA1S3S10A1S30S26A1A6").

Definition skip_facts : list sprop := ltac2:(tb__ "0|0|
S0ScS1bS26S28A2S0ScSfS2bS26A2S0ScSfS26SdS39A1A2S3ScA1A3A3A3").
Definition Cs : axst := ltac2:(tb__ "0|2|
S2aS7bS0S5S1SbA2M0S2S1SbUdS24S25A1A4S0G0S2S1SbU5S27A4S3G0A1M1A3A3G1S24S26A1S3S10A1S4ScS30S25A1S4ScS0ScSfS27SdZ1A1A2S3ScA1A3S2cA3A3A6").

Definition Cm : axst := ltac2:(tb__ "0|5|
S2aS79S0S5S1SbA2M0S2S1SbUdS24S25A1M1A4S0G0S2S1SbUeG1A4S0G0S2S1SbU9SePafA1A4S0G0S2S1SbU8SePb0A1A4S0G0S2S1SbU1cSePb1A1M2A4S0G0S2S1SbU7SePb2A1M3A4S0G0S2S1SbUfSePb3A1A4S0G0S2S1SbU6SePb4A1A4S0G0S2S1SbU1dSdZ9A1A4S0G0S2S1SbU1eSdZ13A1A4S0G0S2S1SbU1fSdZaA1A4S0G0S2S1SbU5S27A4S3G0A1M4A3A3A3A3A3A3A3A3A3A3A3A3G4S24S26A1S3S10A1S4ScS30S25A1S4ScS0ScSfS27SdZ1A1A2S0ScSfG2S25A2S0ScSfG3S25A2S3ScA1A3A3A3S2cA3A3A6").

Definition Ce_of (esign : Z) : axst := ltac2:(tb__ "0|6|
S2aS78S0S5S1SbA2M0S2S1SbUdS24S25A1M1A4S0G0S2S1SbUfG1A4S0G0S2S1SbUeSePb5A1M2A4S0G0S2S1SbU8SdZaA1A4S0G0S2S1SbU1dSdVesign;A1A4S0G0S2S1SbU1fSdZ1869fA1A4S0G0S2S1SbU1eSdZ9A1A4S0G0S2S1SbU1cSePb1A1M3A4S0G0S2S1SbU7SePb2A1M4A4S0G0S2S1SbU6SePb4A1A4S0G0S2S1SbU5S27A4S3G0A1M5A3A3A3A3A3A3A3A3A3A3A3G5S24S26A1S3S10A1S4ScS30S25A1S4ScS0ScSfS27SdZ1A1A2S0ScSfG2SdZf423fA1A2S0ScSfG3S28A2S0ScSfG4S28A2S3ScA1A3A3A3A3S2cA3A3A6").
Definition Ce : axst := Ce_of 1.
Definition Cen : axst := Ce_of 18446744073709551615.

Definition x_facts : list sprop := ltac2:(tb__ "0|2|
S0ScS17S6dSePb7A1M0SdS8bS8cZ2Z1eA2M1A1A1A3S0ScS17S6dSdG1A1G0A3S3ScA1A3A3").
Definition Cx : axst := ltac2:(tb__ "0|3|
S2aS7cS0S5S1SbA2M0S2S1SbUdSePb7A1M1A4S0G0S2S1SbUeG1A4S0G0S2S1SbUbS24S25A1A4S0G0S2S1SbU5S27A4S3G0A1M2A3A3A3A3G2S24S26A1S3S10A1S4ScS47S25A1S4ScS0ScSfS27SdZ1A1A2S3ScA1A3S4ScS4eS2cA3A3A3A6").

Definition Cp : axst := ltac2:(tb__ "0|3|
S2aS7aS0S5S1SbA2M0S2S1SbUeSePb8A1A4S0G0S2S1SbUdSePb7A1A4S0G0S2S1SbUbM1S24S25A1A4S0G0S2S1SbU5S27A4S3G0A1M2A3A3A3A3S0G0S2S1SbG1SdZ0A1A4G2A3S24S26A1S3S10A1S4ScS47S25A1S4ScS0ScSfS27SdZ1A1A2S3ScA1A3S4ScS4eS2cA3A3A3A6").

Definition gW : positive := 190%positive.
Definition sh_cur : sv := ltac2:(tb__ "0|0|
S13S6cSeS49A1S6aA3").
Definition rem : sv := SAlu ALU_SUB vE v173.
Definition chain_facts (k : Z) : list sprop := ltac2:(tb__ "0|2|
S4ScS30S25A1S4ScS0ScSfS13S6cS25SdS8aVk;Z1M0A2A1A3M1S28A2S0ScSfG1S2dA2S0ScSfS27SdG0A1A2S3ScA1A3A3A3S4ScS6bS49S24S25A1A2S2cA3A3A3").
Definition CI (k : Z) (pc : Z) : axst := ltac2:(tb__ "0|2|
S2aVpc;S0S5S1SbA2M0S2S1SbUdS24S25A1A4S0G0S2S1SbUfS4cA4S0G0S2S1SbU6S37A4S0G0S2S1SbU5S27A4S3G0A1M1A3A3A3A3G1S24S26A1S3S10A1S46Vk;A1A6").

Definition sd_state_txt (pc : Z) (regs : list (nat * sv)) (fregs : list (nat * sv)) (c0 : sv) (txt out : list cell)
           (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S68S15Vpc;S62S63S61A1S4S5S1SbA2M0S0G0S2S1SbU2S13S6cSePaA1SdN30A1A3A4S0G0S2S1SbU8SeP6cA1A4S0G0S2S1SbU9SeP6dA1A4S0G0S2S1SbU12SeP76A1A4S0G0S2S1SbU13SeP77A1A4S0G0S2S1SbU14SeP78A1A4S0G0S2S1SbUaSePcA1A4S0G0S2S1SbUbS24S28A1A4S0G0S2S1SbUcSePeA1A4S0G0S2S1SbU10S4dA4S0G0S2S1SbU11S6aA4S3G0A1A3A3A3A3A3A3A3A3A3A3A3Vregs;A3A2S62S48Vfregs;A2S14S7SbA1S4S11S0S11S33S38A1S0S11S32Vc0;A1S0S11S34Vtxt;A1S0S11S31Vout;A1S3S11A1A3A3A3A3S69A3S4ScVfacts;S4ScS3dS2fA3A3S3fS6A9S2eA2").
Definition CN (k : Z) (pc : Z) : axst := ltac2:(tb__ "0|4|
S5dVpc;S0S5S1SbA2M0S2S1SbUdS24S25A1A4S0G0S2S1SbUfS4cA4S0G0S2S1SbU7S37A4S0G0S2S1SbU6S37A4S0G0S2S1SbU5S27A4S3G0A1M1A3A3A3A3A3G1S24S26A1S0S10S12S25Z1SePbfA1M2A3S3S10A1M3A3G3S0ScS1fS17S70S13S6eS1eS6Q8G2A3SdZ20A1A3SdZ6eA1A3A1S46Vk;A1A3A7").
Definition chain_cuts : list axst := ltac2:(tb__ "0|2|
S0S20S29Z1M0Z9a728A2S0S20S29Z2M1Z9a768A2S0S20S29Z3Z9a7a8A2S0S20S29Z4Z9a7e8A2S0S20S29Z5Z9a828A2S0S20S29Z6Z9a868A2S0S20S29Z7Z9a8a8A2S0S20S3bG0Z9a62cA2S0S20S3bG1Z9a66cA2S3S20A1A3A3A3A3A3A3A3A3A3").
Definition chain_pcs : list Z := ltac2:(tb__ "0|0|
S0S60Z9a728S0S60Z9a768S0S60Z9a7a8S0S60Z9a7e8S0S60Z9a828S0S60Z9a868S0S60Z9a8a8S0S60Z9a62cS0S60Z9a66cS3S60A1A3A3A3A3A3A3A3A3A3").

Definition F_sd : list sprop := ltac2:(tb__ "0|0|
S0ScSfS2bS26A2S0ScSfS26S28A2S3ScA1A3A3").
Definition post_objs (out : list cell) : list sobj := ltac2:(tb__ "0|0|
S4S11S0S11S33S38A1S0S11S32S24S26A1A1S0S11S34S3S10A1A1S0S11S31Vout;A1S3S11A1A3A3A3A3S69A3").
Definition P_none : axst := ltac2:(tb__ "0|1|
S68S15S7dS62S64S61A1S0S5S1SbA2M0S2S1SbUaSdZ0A1A4S3G0A1A3A2S4aS14S7SbA1S4bS3S10A1A1S4ScS3eS2fA3S40S6A9S2eA2").
Definition P_num : axst := ltac2:(tb__ "0|1|
S68S15S7dS62S64S61A1S0S5S1SbA2M0S2S1SbUaSdZ1A1A4S3G0A1A3A2S4aS14S7SbA1S4bS0S10S12SdZ0A1Z8SePadA1A3S3S10A1A3A1S4ScS3eS2fA3S40S6A9S2eA2").
Definition Posts_sd : list leafA := ltac2:(tb__ "0|0|
S0S22S23S41S80A2S0S22S23S42S80A2S3S22A1A3A3").

Definition cuts_sd : list axst := ltac2:(tb__ "0|0|
S4S20S0S20S36S0S20S3aS0S20S3cS0S20S51S0S20S4fS0S20S50S0S20S53S0S20S52S3S20A1A3A3A3A3A3A3A3A3S56A3").

Definition cuts_sd0 : list axst := ltac2:(tb__ "0|0|
S0S20S36S0S20S3aS0S20S3cS3S20A1A3A3A3").
Definition cutpcs_sd : list Z := ltac2:(tb__ "0|0|
S4S60S0S60S77S0S60S7bS0S60S79S0S60S78S0S60S7cS0S60S7aS3S60A1A3A3A3A3A3A3S57A3").

Definition sd_trap : Z := 0x9ad2c.
Definition X_t1 : axst := Eval vm_compute in nth 0 (leavesA_at FUEL_sd cutpcs_sd Cen sd_trap) Pre_sd.
Definition X_t2 : axst := Eval vm_compute in nth 1 (leavesA_at FUEL_sd cutpcs_sd Cen sd_trap) Pre_sd.
Definition X_t3 : axst := Eval vm_compute in nth 2 (leavesA_at FUEL_sd cutpcs_sd Cen sd_trap) Pre_sd.
Definition exits_sd : list axst := ltac2:(tb__ "0|0|
S0S20S41S0S20S42S0S20S43S0S20S44S0S20S45S3S20A1A3A3A3A3A3").

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymSoundW.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import UbsanArith.

Lemma check_sd : ltac2:(tb__ "0|0|
S72S8S84S67S54S58S61S59S5aA6SaA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma contra_t1 : ltac2:(tb__ "0|0|
S19S73ScS1cR1A1S1dS21S43A1A1A3S71F_;Frho;").
Proof.
  intros rho HF. concrete_facts HF.
  pose proof (Forall_pick _ _ 0 _ HF eq_refl) as H0. cbn beta in H0.
  apply (trap_ne_false_u rho _) in H0; [exact H0|].
  pick_facts HF [11]%nat. rewrite eval_var. zfacts; lia.
Qed.
Lemma contra_t2 : ltac2:(tb__ "0|0|
S19S73ScS1cR1A1S1dS21S44A1A1A3S71F_;Frho;").
Proof.
  intros rho HF. concrete_facts HF.
  pose proof (Forall_pick _ _ 0 _ HF eq_refl) as H0. cbn beta in H0.
  apply (trap_ne_false_u rho _) in H0; [exact H0|].
  pick_facts HF [13]%nat. rewrite eval_var. zfacts; lia.
Qed.
Lemma contra_t3 : ltac2:(tb__ "0|0|
S19S73ScS1cR1A1S1dS21S45A1A1A3S71F_;Frho;").
Proof.
  intros rho HF. concrete_facts HF.
  pose proof (Forall_pick _ _ 0 _ HF eq_refl) as H0. cbn beta in H0.
  apply (trap_ne_false_u rho _) in H0; [exact H0|].
  rewrite <- zv_sound. cbn [zv ext_width_ok Z.of_N and_hmask].
  pick_facts HF [2; 3; 13]%nat. zfacts; lia.
Qed.

Theorem scan_double_sum : ltac2:(tb__ "0|0|
S83OF_;S87S19S9S8dQ40A1A1S88S67R4R3A3S89S67S61R4A3S82S67R6S86S67R5S36R4R3A5S85S67R5S61R4R3S55A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_sd rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_sd cutpcs_sd NF cuts_sd exits_sd (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_sd) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_sd.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply exit_postA. in_nth 0.
    + apply exit_postA. in_nth 1.
    + apply (exit_contraA segs ok _ X_t1). intros r tp' tr md _ HF. exact (contra_t1 r HF).
    + apply (exit_contraA segs ok _ X_t2). intros r tp' tr md _ HF. exact (contra_t2 r HF).
    + apply (exit_contraA segs ok _ X_t3). intros r tp' tr md _ HF. exact (contra_t3 r HF).
  - left; reflexivity.
Qed.

