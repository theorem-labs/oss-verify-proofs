(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "bool"; "true"; "Some"; "option"; "app"; "false"; "list"; "prod"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "cell"; "sobj"; "SPUle"; "mkCell"; "SAlu"; "ss_facts"; "valuation"; "DUnknown"; "FcsrFrm0"; "SPAlign"; "holds"; "mkObj"; "mkSS"; "sprop_below"; "ss_next"; "sv_eqb"; "c_off"; "c_val"; "ob_base"; "ob_cells"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "mkLeafA"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSplit"; "AXRebase"; "AXUnbase"; "AXSelect"; "AXMerge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2"; "z0"; "vOut"; "E1c"; "E2c"; "E3c"; "vB"; "vL"; "Pre_pc"; "R1"; "R2"; "R3"; "s1"; "s2"; "s3"; "vT"; "E1"; "E2"; "E3"; "FUEL_pc"; "O_out12"; "O_stk"; "O_txt"; "P_ret"; "T1n"; "T1u"; "T2n"; "T2u"; "T3n"; "T3u"; "X_pc"; "X_tA"; "X_tB2"; "X_tB3"; "cutpcs_pc"; "oEnd"; "pB"; "pc_base_facts"; "spo"; "v132"; "vXO"; "xf_call"; "xfb_call"; "C_J1"; "C_J2"; "Posts_pc"; "cur_le"; "pc_state"; "two40"; "vTL"; "BAD"; "cuts_pc"; "exits_pc"; "frm_cells"; "pEndB"; "pp_val"; "stk_cells"; "two47"; "vcuts_pc"; "vexits_pc"; "xFRM"; "xOUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2.SI"; "Pre_si"; "P_none"; "P_num"; "Posts_si"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "cut_regs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "A_globals"; "mkA"; "leavesA_at"; "shb"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.PureCallB"; "T_call"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@Stdlib.Lists.List"; "forallb"; "find"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2.ParseCornerAddr"; "pc_J1"; "pc_J2"; "pc_entry"; "pc_ret"; "ra1"; "si_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "rel_offset"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform CfgGlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import PureCallB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_int.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module SI. Include Lib_scan_int. End SI.

Module ParseCornerAddr.
  Definition pc_entry : Z := 0x9affc.
  Definition pc_J1 : Z := 0x9b120.
  Definition pc_J2 : Z := 0x9b1a8.
  Definition pc_ret : Z := 0x9b234.
  Definition pc_trap : Z := 0x9b238.
  Definition fix_trap : Z := 0xa495c.
  Definition si_entry : Z := 0xa014c.
  Definition ra1 : Z := 0x9b0c0.
  Definition ra2 : Z := 0x9b190.
  Definition ra3 : Z := 0x9b1f4.
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
S15S87SfPaA1SeVk;A1A3").
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.
Definition vXO : sv := SVar 56.

Definition pc_base_facts : list sprop := ltac2:(tb__ "0|4|
S0S10S13S5bS3fA2S0S10S13S47SeS68A1M0A2S0S10S13S69G0A2S0S10S13S3fG0A2S0S10S13S3eSeS71A1M1A2S0S10S13SeZ1A1S3eA2S0S10S13SfPeA1G0A2S0S10S13SfP21A1G0A2S0S10S13SfP22A1G0A2S0S10S1aP23Z2A2S0S10S1aPaM2Z4A2S0S10S13SeZ10000A1SfG2A1M3A2S0S10S13G3G1A2S0S10S13S3aG1A2S0S10S1aP38Z3A2S0S10S13S60S3aA2S0S10S13S15S87S3aSeZcA1A3G1A2S3S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1cSfPaA1SeN70A1SeZ0A1Vcells;S18A5").
Definition O_txt : sobj := ltac2:(tb__ "0|0|
S1cS3eSeZ0A1S3fS3S11A1S18A5").
Definition O_out12 (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1cS3aSeZ0A1SeZcA1Vcells;S18A5").

Definition xFRM : sv * sv := ltac2:(tb__ "0|0|
S2SdSdS5eN60A1SeZ10A1A4").

Definition xOUT : sv * sv := ltac2:(tb__ "0|0|
S2SdSdS60S15S88S15S87S3aSeZcA1A3S60A3A4").
Definition X_pc : list (sv * sv) := ltac2:(tb__ "0|1|
S0SbSdSdA2M0S2SdSdS3eS3fA4S0G0S75S0G0S74S3G0A1A3A3A3").

Definition Pre_pc : axst := ltac2:(tb__ "0|2|
S82S1dS94S7cS7fS0SbS1SdA2M0S2S1SdUaS5cS47A1A4S3G0A1A3A2S7bS19ScSdA1S8S12S0S12S4dS3S11A1M1A1S0S12S4eS0S12S4cG1A1S3S12A1A3A3A3S81A3S5dS7aS9A9S56A2").

Definition stk_cells : list cell := ltac2:(tb__ "0|1|
S0S11S14SeN48A1Z8M0SfP2bA1A3S0S11S14SeN40A1G0SfP2aA1A3S0S11S14SeN38A1G0SfP29A1A3S0S11S14SeN30A1G0SfP28A1A3S0S11S14SeN28A1G0SfP27A1A3S0S11S14SeN20A1G0SfP26A1A3S0S11S14SeN18A1G0SfP1dA1A3S0S11S14SeN10A1G0SfP1cA1A3S0S11S14SeN8A1G0SfPbA1A3S3S11A1A3A3A3A3A3A3A3A3A3").

Definition cutpcs_pc : list Z := ltac2:(tb__ "0|0|
S0S86S97S0S86S92S0S86S93S3S86A1A3A3A3").

Definition BAD : axst := Pre_pc.
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S8cS26Vk;S83S4bS5aVS;Vpc;A4S6aA4").

Definition pEndB : sv := ltac2:(tb__ "0|0|
S15S87S69S5cS47A1A3").
Definition frm_cells (cur : sv) : list cell := ltac2:(tb__ "0|1|
S8S11S0S11S14SeN58A1Z8M0S5cVcur;A1A3S0S11S14SeN50A1G0S6eA3S3S11A1A3A3S70A3").
Definition v132 : sv := SVar 132.
Definition cur_le (w : sv) : list sprop := ltac2:(tb__ "0|0|
S0S10S13S47Vw;A2S0S10S13Vw;S5bA2S0S10S13Vw;SeS68A1A2S3S10A1A3A3A3").

Definition pc_state (pc : Z) (regs : list (nat * sv)) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|1|
S82S1dVpc;S7cS7dS7aA1S8SbS1SdA2M0S0G0S2S1SdU2S5eN60A1A4S0G0S2S1SdU8SfP22A1A4S0G0S2S1SdU9S15S87S3aSeZ4A1A3A4S0G0S2S1SdU16S84A4S3G0A1A3A3A3A3Vregs;A3A2S7bS19ScSdA1S8S12S0S12S4dS6dS5fA1A1S0S12S4eS0S12S4cS3S11A1A1S3S12A1A3A3A3S81A3S8S10Vfacts;S5dA3Vnx;S9A9S56A2").

Definition C_J1 : axst := ltac2:(tb__ "0|1|
S67S92S0SbS1SdA2M0S2S1SdU1SeS96A1A4S0G0S2S1SdUaSfP85A1A4S0G0S2S1SdUdSfP86A1A4S0G0S2S1SdU12SfP21A1A4S0G0S2S1SdU13S15S87S3aSeZ8A1A3A4S0G0S2S1SdU14S3aA4S0G0S2S1SdU15SfP87A1A4S0G0S2S1SdU17SfP88A1A4S3G0A1A3A3A3A3A3A3A3A3S66S5fA1P91A4").

Definition C_J2 : axst := ltac2:(tb__ "0|1|
S67S93S0SbS1SdA2M0S2S1SdU1SfP89A1A4S0G0S2S1SdUaSfP85A1A4S0G0S2S1SdU12SfP8aA1A4S0G0S2S1SdU13SfP8bA1A4S0G0S2S1SdU14SfP8cA1A4S0G0S2S1SdU15SfP87A1A4S0G0S2S1SdU17SfP88A1A4S3G0A1A3A3A3A3A3A3A3S66S5fA1P91A4").

Definition xf_call (vi : bool) : list axform := ltac2:(tb__ "0|9|
S0S32S34U0M0SeN60M1A1A2S0S32S34U1M2SeN5cM3A1A2S0S32S34U2M4SeN58M5A1A2S0S32S34U3M6SeN50A1A2S0S32S36G6G5A2S0S32S4S32Lvi;Vvi;S36G4G3A2S36G2G1A2X4x2S0S32S37S4SaS1A1Lvi;Vvi;S0S1G0S0S1G6S0S1U5M7S0S1G4S0S1G2S0S1U4S0S1U6S0S1U7S0S1U8S3S1A1A3A3A3A3M8A3A3A3A3A3S0S1G0S0S1G6S0S1G7S0S1G2S0S1G4G8A3A3A3A3A3X4x2A1S3S32A1A3A3A3A3A3A3A3").

Definition xfb_call (vi : bool) : list axform := ltac2:(tb__ "0|6|
S0S32S35U0M0A1S0S32S35U1M1A1S0S32S35U3M2A1S0S32S37S4SaS1A1Lvi;Vvi;S0S1G0S0S1U6M3S0S1G2S0S1G1S0S1U7S0S1U2S0S1U8S0S1U4S0S1U5S3S1A1A3A3A3A3A3A3M4A3A3A3S0S1G0S0S1G2S0S1G3G4A3A3A3X4x2A1S0S32S38G0A1M5S0S32G5S0S32G5S0S32G5S3S32A1A3A3A3A3A3A3A3A3").

Definition s_call (E : axst) (cur : sv) : wsub := ltac2:(tb__ "0|1|
S8SbS85SdA2M0S0G0S2S85SdPfS3eA4S0G0S2S85SdP10Vcur;A4S0G0S2S85SdP11S5bA4S0G0S2S85SdP12S3fA4S0G0S2S85SdP13S5eN60A1A4S3G0A1A3A3A3A3A3Sa1PaS27VE;A1S27S76A1A3A3").

Definition pp_val (E : axst) : sv := ltac2:(tb__ "0|1|
S7S12A1SdLx;S90S12S12S20S23R1A1SfPaA1A2Lo;S25S27VE;A1A1A3S12S7S11A1SdLx;S90S11S11S20S21R1A1SeN58A1A2Lc;S24R1A1A3S11S22R1A1Lc;SeZ0A1M0X7x2Lo;G0X7x2").
Definition cur_off (E : axst) : sv := ltac2:(tb__ "0|0|
S7SdA1SdLx;Sa3S3eS6fVE;A1A2SdR1Loff;SeZ0A1X7x2").

Definition E1 : axst := Eval vm_compute in leaf_at Pre_pc si_entry 0.
Definition E1c : axst := Eval vm_compute in optAp (apply_axforms E1 (xf_call true)).
Definition s1 : wsub := Eval vm_compute in s_call E1c (cur_off E1).
Definition R1 : list sobj := Eval vm_compute in optR (entails_frA E1c SI.Pre_si s1).
Definition T1n : axst := Eval vm_compute in optAp (apply_axforms (T_call SI.Pre_si E1c s1 R1 SI.P_none) (xfb_call true)).
Definition T1u : axst := Eval vm_compute in optAp (apply_axforms (T_call SI.Pre_si E1c s1 R1 SI.P_num) (xfb_call true)).

Definition E2 : axst := Eval vm_compute in leaf_at C_J1 si_entry 0.
Definition E2c : axst := Eval vm_compute in optAp (apply_axforms E2 (xf_call false)).
Definition s2 : wsub := Eval vm_compute in s_call E2c (cur_off E2).
Definition R2 : list sobj := Eval vm_compute in optR (entails_frA E2c SI.Pre_si s2).
Definition T2n : axst := Eval vm_compute in optAp (apply_axforms (T_call SI.Pre_si E2c s2 R2 SI.P_none) (xfb_call false)).
Definition T2u : axst := Eval vm_compute in optAp (apply_axforms (T_call SI.Pre_si E2c s2 R2 SI.P_num) (xfb_call false)).

Definition E3 : axst := Eval vm_compute in leaf_at C_J2 si_entry 0.
Definition E3c : axst := Eval vm_compute in optAp (apply_axforms E3 (xf_call false)).
Definition s3 : wsub := Eval vm_compute in s_call E3c (cur_off E3).
Definition R3 : list sobj := Eval vm_compute in optR (entails_frA E3c SI.Pre_si s3).
Definition T3n : axst := Eval vm_compute in optAp (apply_axforms (T_call SI.Pre_si E3c s3 R3 SI.P_none) (xfb_call false)).
Definition T3u : axst := Eval vm_compute in optAp (apply_axforms (T_call SI.Pre_si E3c s3 R3 SI.P_num) (xfb_call false)).

Definition X_tA : axst := Eval vm_compute in nth 0 (leavesA_at FUEL_pc cutpcs_pc T1u pc_trap) BAD.
Definition X_tB2 : axst := Eval vm_compute in nth 0 (leavesA_at FUEL_pc cutpcs_pc T2u fix_trap) BAD.
Definition X_tB3 : axst := Eval vm_compute in nth 0 (leavesA_at FUEL_pc cutpcs_pc T3u fix_trap) BAD.

Definition P_ret : axst := ltac2:(tb__ "0|2|
S82S1dS95S7cS7eS7aA1S0SbS1SdA2M0S2S1SdUaSfP8cA1A4S3G0A1A3A2S7bS19ScSdA1S8S12S0S12S4dS3S11A1M1A1S0S12S4eS0S12S4cG1A1S3S12A1A3A3A3S81A3S5dP96S9A9S56A2").
Definition Posts_pc : list leafA := ltac2:(tb__ "0|0|
S0S28S2aS4fSa2A2S3S28A1A3").

Definition cuts_pc : list axst := ltac2:(tb__ "0|0|
S0S26S40S0S26S50S0S26S51S0S26S63S0S26S52S0S26S53S0S26S64S0S26S54S0S26S55S3S26A1A3A3A3A3A3A3A3A3A3").
Definition exits_pc : list axst := ltac2:(tb__ "0|0|
S0S26S48S0S26S49S0S26S4aS0S26S57S0S26S58S0S26S59S0S26S4fS3S26A1A3A3A3A3A3A3A3").

Lemma check_pc : ltac2:(tb__ "0|0|
S2bS4S30S80S4bS5aS7aS6bS6cA6S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma site1 : ltac2:(tb__ "0|5|
S2cS2bS7S26A1M0S33S48S61S5A1A2S6S26S3bA2A3S2cS2bS7SaS12A1M1A1S8eS3bS76S44A3S6G1S41A2A3S2cS2bS4S8dS3bS76S44S41S8bS28S26S29S79A4A5S5A3S2cS2bS4S8fS10S1eS1fS27S3bA1M2A1M3A1S16G2A1A3S5A3S2cS2bS4S91S7aG3A2S5A3S2cS2bG0S33S89S76S3bS44S41S77A5S62S5A1M4A2S6S26S50A2A3S2bG0S33S89S76S3bS44S41S78A5G4A2S6S26S51A2A3A2A2A2A2A2A2").
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma site2 : ltac2:(tb__ "0|5|
S2cS2bS7S26A1M0S33S49S61S9A1A2S6S26S3cA2A3S2cS2bS7SaS12A1M1A1S8eS3cS76S45A3S6G1S42A2A3S2cS2bS4S8dS3cS76S45S42S8bS28S26S29S79A4A5S5A3S2cS2bS4S8fS10S1eS1fS27S3cA1M2A1M3A1S16G2A1A3S5A3S2cS2bS4S91S7aG3A2S5A3S2cS2bG0S33S89S76S3cS45S42S77A5S62S9A1M4A2S6S26S52A2A3S2bG0S33S89S76S3cS45S42S78A5G4A2S6S26S53A2A3A2A2A2A2A2A2").
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma site3 : ltac2:(tb__ "0|5|
S2cS2bS7S26A1M0S33S4aS61S9A1A2S6S26S3dA2A3S2cS2bS7SaS12A1M1A1S8eS3dS76S46A3S6G1S43A2A3S2cS2bS4S8dS3dS76S46S43S8bS28S26S29S79A4A5S5A3S2cS2bS4S8fS10S1eS1fS27S3dA1M2A1M3A1S16G2A1A3S5A3S2cS2bS4S91S7aG3A2S5A3S2cS2bG0S33S89S76S3dS46S43S77A5S62S9A1M4A2S6S26S54A2A3S2bG0S33S89S76S3dS46S43S78A5G4A2S6S26S55A2A3A2A2A2A2A2A2").
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma contra_tA : ltac2:(tb__ "0|0|
S17S8aS10S1bR1A1S16S27S57A1A1A3S2dF_;Frho;").
Proof. intros rho HF. concrete_facts HF. pick_facts HF [0; 18]%nat. zfacts; lia. Qed.
Lemma contra_tB2 : ltac2:(tb__ "0|0|
S17S8aS10S1bR1A1S16S27S58A1A1A3S2dF_;Frho;").
Proof. intros rho HF. concrete_facts HF. pick_facts HF [0; 23]%nat. zfacts; lia. Qed.
Lemma contra_tB3 : ltac2:(tb__ "0|0|
S17S8aS10S1bR1A1S16S27S59A1A1A3S2dF_;Frho;").
Proof. intros rho HF. concrete_facts HF. pick_facts HF [0; 19]%nat. zfacts; lia. Qed.

Theorem parse_corner_sum : ltac2:(tb__ "0|0|
Sa0OF_;S9aS17SaS9dQ40A1A1S9cS80R4R3A3S9bS80S7aR4A3S9fS80R6S99S80R5S40R4R3A5S98S80R5S7aR4R3S65A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_pc rho tp w Hw) | intros w Hw; exact Hw |].
  set (JG := withGA (fun r => agree_below NF rho r) J).
  assert (HokG : ok_frameA segs ok JG) by (intros r t tr ms md msv' [_ HJ]; eapply Hok; eauto).
  assert (HstG : stableA segs NF JG) by (apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]).
  assert (SUM : forall rhoE rho1 tp1, triple segs ok (SPA segs (frozenJ JG rhoE) SI.Pre_si rho1 tp1)
                  (LQA segs (frozenJ JG rhoE) (ss_next (ax_S SI.Pre_si)) rho1 tp1 SI.Posts_si)).
  { intros rhoE rho1 tp1. apply SI.scan_int_sum; [apply frozenJ_ok_frameA; exact HokG | apply (frozenJ_stableA segs NF NF); exact HstG]. }
  apply (cfg_soundA segs FUEL_pc cutpcs_pc NF cuts_pc exits_pc JG ok (LQA segs J NF rho tp Posts_pc) tp HokG HstG check_pc).
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
    + destruct site1 as (Hxf & He & Hc & Hfb & Hn & Hbn & Hbu). apply Pos.leb_le in Hn.
      apply (call_exitJ segs ok JG NF cuts_pc _ E1 E1c SI.Pre_si (xf_call true) s1 R1 SI.Posts_si rhoE tp HstG Hn Hxf (SUM rhoE) He Hc Hfb).
      intros L HinL. destruct HinL as [<-|[<-|[]]]; [exists (xfb_call true), T1n; split; [exact Hbn | in_nth 1] | exists (xfb_call true), T1u; split; [exact Hbu | in_nth 2]].
    + destruct site2 as (Hxf & He & Hc & Hfb & Hn & Hbn & Hbu). apply Pos.leb_le in Hn.
      apply (call_exitJ segs ok JG NF cuts_pc _ E2 E2c SI.Pre_si (xf_call false) s2 R2 SI.Posts_si rhoE tp HstG Hn Hxf (SUM rhoE) He Hc Hfb).
      intros L HinL. destruct HinL as [<-|[<-|[]]]; [exists (xfb_call false), T2n; split; [exact Hbn | in_nth 4] | exists (xfb_call false), T2u; split; [exact Hbu | in_nth 5]].
    + destruct site3 as (Hxf & He & Hc & Hfb & Hn & Hbn & Hbu). apply Pos.leb_le in Hn.
      apply (call_exitJ segs ok JG NF cuts_pc _ E3 E3c SI.Pre_si (xf_call false) s3 R3 SI.Posts_si rhoE tp HstG Hn Hxf (SUM rhoE) He Hc Hfb).
      intros L HinL. destruct HinL as [<-|[<-|[]]]; [exists (xfb_call false), T3n; split; [exact Hbn | in_nth 7] | exists (xfb_call false), T3u; split; [exact Hbu | in_nth 8]].
    + apply (exit_contraA segs ok _ X_tA). intros r tp' tr md _ HF. exact (contra_tA r HF).
    + apply (exit_contraA segs ok _ X_tB2). intros r tp' tr md _ HF. exact (contra_tB2 r HF).
    + apply (exit_contraA segs ok _ X_tB3). intros r tp' tr md _ HF. exact (contra_tB3 r HF).
    + apply exit_postA. in_nth 0.
  - left; reflexivity.
Qed.

Definition z0 : sv := SLit 0.
Definition vcuts_pc : list vnodeA := ltac2:(tb__ "0|3|
S0S2eS2fS40Z5aS39A3S0S2eS2fS50Z50M0S39A3S0S2eS2fS51G0S39A3S0S2eS2fS63Z46S39A3S0S2eS2fS52Z3cM1S39A3S0S2eS2fS53G1S39A3S0S2eS2fS64Z32S39A3S0S2eS2fS54Z28M2S39A3S0S2eS2fS55G2S39A3S3S2eA1A3A3A3A3A3A3A3A3A3").
Definition vexits_pc : list vnodeA := ltac2:(tb__ "0|1|
S0S2eS2fS48Z55S39A3S0S2eS2fS49Z41S39A3S0S2eS2fS4aZ2dS39A3S0S2eS2fS57Z0M0S39A3S0S2eS2fS58G0S39A3S0S2eS2fS59G0S39A3S0S2eS2fS4fZ1S39A3S3S2eA1A3A3A3A3A3A3A3").

Lemma echeck_pc : ltac2:(tb__ "0|0|
S2bS4S31S80S4bS5aS7aS72S73A6S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem parse_corner_sum_ex : ltac2:(tb__ "0|0|
S9aS17SaS9dQ40A1A1S9bS80S7aR3A3S9eS80S99S80R4S40R3R2A5S98S80R4S7aR3R2S65A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_pc rho tp w Hw) | intros w Hw; exact Hw |].
  set (JG := withGA (fun r => agree_below NF rho r) J).
  assert (HstG : stableA segs NF JG) by (apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]).
  assert (SUM : forall rhoE rho1 tp1, etriple segs (SPA segs (frozenJ JG rhoE) SI.Pre_si rho1 tp1)
                  (LQA segs (frozenJ JG rhoE) (ss_next (ax_S SI.Pre_si)) rho1 tp1 SI.Posts_si)).
  { intros rhoE rho1 tp1. apply SI.scan_int_sum_ex. apply (frozenJ_stableA segs NF NF). exact HstG. }
  change Pre_pc with (vna_state (mkVNA Pre_pc 90 z0)).
  apply (cfg_complete_autoA segs FUEL_pc cutpcs_pc NF vcuts_pc vexits_pc JG (LQA segs J NF rho tp Posts_pc) tp HstG).
  - intros n Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbv; congruence.
  - exact echeck_pc.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
    + destruct site1 as (Hxf & He & Hc & Hfb & Hn & Hbn & Hbu). apply Pos.leb_le in Hn.
      apply (call_eexitJ segs JG NF vcuts_pc _ (mkVNA E1 85 z0) E1c SI.Pre_si (xf_call true) s1 R1 SI.Posts_si rhoE tp HstG Hn Hxf (SUM rhoE) He Hc Hfb).
      intros L HinL. destruct HinL as [<-|[<-|[]]];
        [exists (xfb_call true), T1n, 80; split; [exact Hbn | split; [in_nth 1 | cbn; lia]]
        | exists (xfb_call true), T1u, 80; split; [exact Hbu | split; [in_nth 2 | cbn; lia]]].
    + destruct site2 as (Hxf & He & Hc & Hfb & Hn & Hbn & Hbu). apply Pos.leb_le in Hn.
      apply (call_eexitJ segs JG NF vcuts_pc _ (mkVNA E2 65 z0) E2c SI.Pre_si (xf_call false) s2 R2 SI.Posts_si rhoE tp HstG Hn Hxf (SUM rhoE) He Hc Hfb).
      intros L HinL. destruct HinL as [<-|[<-|[]]];
        [exists (xfb_call false), T2n, 60; split; [exact Hbn | split; [in_nth 4 | cbn; lia]]
        | exists (xfb_call false), T2u, 60; split; [exact Hbu | split; [in_nth 5 | cbn; lia]]].
    + destruct site3 as (Hxf & He & Hc & Hfb & Hn & Hbn & Hbu). apply Pos.leb_le in Hn.
      apply (call_eexitJ segs JG NF vcuts_pc _ (mkVNA E3 45 z0) E3c SI.Pre_si (xf_call false) s3 R3 SI.Posts_si rhoE tp HstG Hn Hxf (SUM rhoE) He Hc Hfb).
      intros L HinL. destruct HinL as [<-|[<-|[]]];
        [exists (xfb_call false), T3n, 40; split; [exact Hbn | split; [in_nth 7 | cbn; lia]]
        | exists (xfb_call false), T3u, 40; split; [exact Hbu | split; [in_nth 8 | cbn; lia]]].
    + apply (eexit_contraA segs _ X_tA). intros r tp' tr md _ HF. exact (contra_tA r HF).
    + apply (eexit_contraA segs _ X_tB2). intros r tp' tr md _ HF. exact (contra_tB2 r HF).
    + apply (eexit_contraA segs _ X_tB3). intros r tp' tr md _ HF. exact (contra_tB3 r HF).
    + apply (eexit_postA segs J NF rho vcuts_pc Posts_pc (mkVNA P_ret 1 z0)). in_nth 0.
  - left; reflexivity.
Qed.
