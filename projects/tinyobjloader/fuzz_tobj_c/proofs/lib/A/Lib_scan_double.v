(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "app"; "prod"; "None"; "false"; "bool"; "list"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SVar"; "SPUle"; "cell"; "sobj"; "mkCell"; "DUnknown"; "FcsrFrm0"; "SAlu"; "SPBranch"; "mkObj"; "mkSS"; "SPAlign"; "SPUlt"; "SPNot"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "pB"; "v173"; "v172"; "v174"; "vE"; "sd_state"; "CI"; "vI"; "skip_facts"; "vL"; "cur_lt"; "X_sd"; "base_facts"; "vB"; "O_out"; "O_pp"; "O_stk"; "O_txt"; "Pre_sd"; "two40"; "C1"; "CN"; "Cs"; "F_sd"; "NXP"; "P_none"; "P_num"; "chain_facts"; "cur_le"; "gW"; "post_fregs"; "post_objs"; "rem"; "sh_cur"; "stk_cells"; "x_facts"; "Ce"; "Cen"; "Cm"; "Cp"; "Cx"; "F8_pp"; "FUEL_sd"; "NXC"; "Posts_sd"; "chain_cuts"; "chain_pcs"; "cut_fregs"; "cutpcs_sd"; "cuts_sd"; "exits_sd"; "fcallee_saved"; "g_pp"; "sh_pp"; "two26"; "two47"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "setregs"; "post_regs"; "cut_regs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "mkA"; "A_globals"; "shb"; "F8x"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "BC_EQ"; "BC_LTU"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double.ScanDoubleAddr"; "sd_L1"; "sd_Le"; "sd_Lm"; "sd_Lp"; "sd_Ls"; "sd_Lx"; "sd_ret"; "pow10_tab"; "sd_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "ok_frameA"; "stableA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "pow"; "@stdpp.bitvector.definitions"; "bv"].
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

Module ScanDoubleAddr.
  Definition sd_entry : Z := 0x9bf30.
  Definition sd_L1 : Z := 0x9bf8c.
  Definition sd_Ls : Z := 0x9c010.
  Definition sd_Lm : Z := 0x9c3ec.
  Definition sd_Le : Z := 0x9c560.
  Definition sd_Lx : Z := 0x9c5b4.
  Definition sd_Lp : Z := 0x9c644.
  Definition sd_ret : Z := 0x9c550.
  Definition pow10_tab : Z := 0x239a0.
End ScanDoubleAddr.
Import ScanDoubleAddr.

Definition FUEL_sd : nat := 500%nat.

Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition cut_fregs : list sv := ltac2:(tb__ "0|0|
S75S1SbS1S8SbL_;S53R1A1SeS73S68U3cR1A2A1A1SeS73S68U8cR1A2A1A1X8x2Lr;S76U0U20A2A4").
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
S0ScSfS27S24A2S0ScSfS24S29A2S0ScSfS29SdS56A1A2S0ScSfS2dSdS57A1M0A2S0ScSfSdZ1A1S2dA2S0ScS19PcM1Z3M2A2S0ScS19PeM3G2A2S0ScS19PaZ4A2S0ScSfSeG1A1G0A2S0ScSfSeG3A1G0A2S3ScA1A3A3A3A3A3A3A3A3A3A3").

Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17SePaA1SdN30A1SdZ0A1Vcells;S13A5").
Definition O_pp (c0 : sv) : sobj := ltac2:(tb__ "0|2|
S17SePcA1SdZ0A1M0SdZ8M1A1S0S10S12G0G1Vc0;A3S3S10A1A3S13A5").
Definition O_txt (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17S2dSdZ0A1S29Vcells;S13A5").
Definition O_out (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17SePeA1SdZ0A1SdZ8A1Vcells;S13A5").
Definition X_sd : list (sv * sv) := ltac2:(tb__ "0|2|
S0S5SbSbA2M0S2SbSbSePcA1SdZ8A1M1A4S0G0S2SbSbS2dS29A4S0G0S2SbSbSePeA1G1A4S0G0S2SbSbSdS70A1SdZb8A1A4S3G0A1A3A3A3A3").

Definition Pre_sd : axst := ltac2:(tb__ "0|2|
S60S18S71S5aS5eS0S5S1SbA2M0S2S1SbUbS20S24A1A4S3G0A1A3A2S5dS14S6SbA1S4S11S0S11S30S3S10A1M1A1S0S11S2fS20S27A1A1S0S11S31G1A1S0S11S2eG1A1S3S11A1A3A3A3A3S61A3S2cS59S7A9S2bA2").

Definition cur_lt (c : sv) : list sprop := ltac2:(tb__ "0|0|
S0ScS1aVc;S24A2S0ScS1aVc;S29A2S0ScSfS27Vc;A2S0ScSfVc;SdS33A1A2S0ScS16S67S20Vc;A1S20S24A1A3S3ScA1A3A3A3A3A3").
Definition cur_le (c : sv) : list sprop := ltac2:(tb__ "0|0|
S0ScSfS27Vc;A2S0ScSfVc;S24A2S0ScSfVc;SdS33A1A2S3ScA1A3A3A3").

Definition v172 : sv := SVar 172.
Definition v173 : sv := SVar 173.
Definition v174 : sv := SVar 174.

Definition stk_cells : list cell := ltac2:(tb__ "0|1|
S0S10S12SdN8A1Z8M0SePbA1A3S0S10S12SdN10A1G0SeP1cA1A3S0S10S12SdN18A1G0SeP1dA1A3S0S10S12SdN20A1G0SeP26A1A3S0S10S12SdN28A1G0SeP27A1A3S0S10S12SdN30A1G0SeP28A1A3S3S10A1A3A3A3A3A3A3").
Definition g_pp : positive := 125%positive.
Definition F8_pp : list sprop := F8x g_pp (SVar 12).
Definition sh_pp : sv := ltac2:(tb__ "0|0|
S15S64SeS54A1S62A3").

Definition sd_state (pc : Z) (regs : list (nat * sv)) (fregs : list (nat * sv)) (c0 : sv) (out : list cell)
           (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S60S18Vpc;S5aS5cS59A1S4S5S1SbA2M0S0G0S2S1SbU2S15S64SePaA1SdN30A1A3A4S0G0S2S1SbU8SeP6cA1A4S0G0S2S1SbU9SeP6dA1A4S0G0S2S1SbU12SeP76A1A4S0G0S2S1SbU13SeP77A1A4S0G0S2S1SbU14SeP78A1A4S0G0S2S1SbUaSePcA1A4S0G0S2S1SbUbS20S24A1A4S0G0S2S1SbUcSePeA1A4S0G0S2S1SbU10S55A4S0G0S2S1SbU11S62A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3Vregs;A3A2S5aS4fVfregs;A2S14S6SbA1S4S11S0S11S30S42A1S0S11S2fVc0;A1S0S11S31S3S10A1A1S0S11S2eVout;A1S3S11A1A3A3A3A3S61A3S4ScVfacts;S4ScS49S2cA3A3S4bS7A9S2bA2").

Definition C1 : axst := ltac2:(tb__ "0|3|
S25S69S0S5S1SbA2M0S2S1SbUdS20S22A1M1A4S0G0S2S1SbUeG1A4S0G0S2S1SbUfSdZ20A1A4S0G0S2S1SbU5SdZ9A1A4S3G0A1M2A3A3A3A3G2S20S27A1S3S10A1S2aS22A1A6").

Definition skip_facts : list sprop := ltac2:(tb__ "0|0|
S0ScS1aS22S24A2S0ScSfS27S22A2S0ScSfS22SdS33A1A2S3ScA1A3A3A3").
Definition Cs : axst := ltac2:(tb__ "0|2|
S25S6dS0S5S1SbA2M0S2S1SbUdS20S21A1A4S0G0S2S1SbU5S23A4S3G0A1M1A3A3G1S20S22A1S3S10A1S4ScS2aS21A1S4ScS0ScSfS23SdZ1A1A2S3ScA1A3S28A3A3A6").

Definition Cm : axst := ltac2:(tb__ "0|5|
S25S6bS0S5S1SbA2M0S2S1SbUdS20S21A1M1A4S0G0S2S1SbUeG1A4S0G0S2S1SbUfSePafA1A4S0G0S2S1SbU9SePb0A1A4S0G0S2S1SbU6SePb1A1M2A4S0G0S2S1SbU7SePb2A1M3A4S0G0S2S1SbU1dSePb3A1A4S0G0S2S1SbU1cSePb4A1A4S0G0S2S1SbU1eSdZ9A1A4S0G0S2S1SbU1fSdZ12A1A4S0G0S2S1SbU8SdZaA1A4S0G0S2S1SbU5S23A4S3G0A1M4A3A3A3A3A3A3A3A3A3A3A3A3G4S20S22A1S3S10A1S4ScS2aS21A1S4ScS0ScSfS23SdZ1A1A2S0ScSfG2S21A2S0ScSfG3S21A2S3ScA1A3A3A3S28A3A3A6").

Definition Ce_of (esign : Z) : axst := ltac2:(tb__ "0|6|
S25S6aS0S5S1SbA2M0S2S1SbUdS20S21A1M1A4S0G0S2S1SbUfG1A4S0G0S2S1SbUeSePb5A1M2A4S0G0S2S1SbU8SdZ186a0A1A4S0G0S2S1SbU1dSdVesign;A1A4S0G0S2S1SbU1fSdZaA1A4S0G0S2S1SbU1eSdZ9A1A4S0G0S2S1SbU6SePb1A1M3A4S0G0S2S1SbU7SePb2A1M4A4S0G0S2S1SbU1cSePb4A1A4S0G0S2S1SbU5S23A4S3G0A1M5A3A3A3A3A3A3A3A3A3A3A3G5S20S22A1S3S10A1S4ScS2aS21A1S4ScS0ScSfS23SdZ1A1A2S0ScSfG2SdZf423fA1A2S0ScSfG3S24A2S0ScSfG4S24A2S3ScA1A3A3A3A3S28A3A3A6").
Definition Ce : axst := Ce_of 1.
Definition Cen : axst := Ce_of 18446744073709551615.

Definition x_facts : list sprop := ltac2:(tb__ "0|2|
S0ScS16S65SePb7A1M0SdS80S81Z2Z1eA2M1A1A1A3S0ScS16S65SdG1A1G0A3S3ScA1A3A3").
Definition Cx : axst := ltac2:(tb__ "0|2|
S25S6eS0S5S1SbA2M0S2S1SbUdSePb7A1A4S0G0S2S1SbUbS20S21A1A4S0G0S2S1SbU5S23A4S3G0A1M1A3A3A3G1S20S22A1S3S10A1S4ScS3cS21A1S4ScS0ScSfS23SdZ1A1A2S3ScA1A3S4ScS43S28A3A3A3A6").

Definition Cp : axst := ltac2:(tb__ "0|3|
S25S6cS0S5S1SbA2M0S2S1SbUeSePb8A1A4S0G0S2S1SbUdSePb7A1A4S0G0S2S1SbUbM1S20S21A1A4S0G0S2S1SbU5S23A4S3G0A1M2A3A3A3A3S0G0S2S1SbG1SdZ0A1A4G2A3S20S22A1S3S10A1S4ScS3cS21A1S4ScS0ScSfS23SdZ1A1A2S3ScA1A3S4ScS43S28A3A3A3A6").

Definition gW : positive := 190%positive.
Definition sh_cur : sv := ltac2:(tb__ "0|0|
S15S64SeS3dA1S62A3").
Definition rem : sv := SAlu ALU_SUB vE v173.
Definition chain_facts (k : Z) : list sprop := ltac2:(tb__ "0|2|
S4ScS2aS21A1S4ScS0ScSfS15S64S21SdS7fVk;Z1M0A2A1A3M1S24A2S0ScSfG1S29A2S0ScSfS23SdG0A1A2S3ScA1A3A3A3S4ScS63S3dS20S21A1A2S28A3A3A3").
Definition CI (k : Z) (pc : Z) : axst := ltac2:(tb__ "0|2|
S25Vpc;S0S5S1SbA2M0S2S1SbUdS20S21A1A4S0G0S2S1SbUfS41A4S0G0S2S1SbU6S40A4S0G0S2S1SbU5S23A4S3G0A1M1A3A3A3A3G1S20S22A1S3S10A1S3bVk;A1A6").

Definition CN (k : Z) (pc : Z) : axst := ltac2:(tb__ "0|3|
S25Vpc;S0S5S1SbA2M0S2S1SbUdS20S21A1A4S0G0S2S1SbUfS41A4S0G0S2S1SbU7S40A4S0G0S2S1SbU6SePbfA1M1A4S0G0S2S1SbU5S23A4S3G0A1M2A3A3A3A3A3G2S20S22A1S3S10A1S0ScS1bS16S66G1SdZ69A1A3A1S3bVk;A1A3A6").
Definition chain_cuts : list axst := ltac2:(tb__ "0|2|
S0S1dS26Z1M0Z9c160A2S0S1dS26Z2M1Z9c198A2S0S1dS26Z3Z9c1d0A2S0S1dS26Z4Z9c208A2S0S1dS26Z5Z9c240A2S0S1dS26Z6Z9c278A2S0S1dS26Z7Z9c2b0A2S0S1dS35G0Z9c090A2S0S1dS35G1Z9c0c8A2S3S1dA1A3A3A3A3A3A3A3A3A3").
Definition chain_pcs : list Z := ltac2:(tb__ "0|0|
S0S58Z9c160S0S58Z9c198S0S58Z9c1d0S0S58Z9c208S0S58Z9c240S0S58Z9c278S0S58Z9c2b0S0S58Z9c090S0S58Z9c0c8S3S58A1A3A3A3A3A3A3A3A3A3").

Definition F_sd : list sprop := ltac2:(tb__ "0|0|
S0ScSfS27S22A2S0ScSfS22S24A2S3ScA1A3A3").
Definition post_objs (out : list cell) : list sobj := ltac2:(tb__ "0|0|
S4S11S0S11S30S42A1S0S11S2fS20S22A1A1S0S11S31S3S10A1A1S0S11S2eVout;A1S3S11A1A3A3A3A3S61A3").
Definition P_none : axst := ltac2:(tb__ "0|1|
S60S18S6fS5aS5bS59A1S0S5S1SbA2M0S2S1SbUaSdZ0A1A4S3G0A1A3A2S3eS14S6SbA1S3fS3S10A1A1S4ScS37S2cA3S38S7A9S2bA2").
Definition P_num : axst := ltac2:(tb__ "0|1|
S60S18S6fS5aS5bS59A1S0S5S1SbA2M0S2S1SbUaSdZ1A1A4S3G0A1A3A2S3eS14S6SbA1S3fS0S10S12SdZ0A1Z8SePadA1A3S3S10A1A3A1S4ScS37S2cA3S38S7A9S2bA2").
Definition Posts_sd : list leafA := ltac2:(tb__ "0|0|
S0S1eS1fS39S72A2S0S1eS1fS3aS72A2S3S1eA1A3A3").

Definition cuts_sd : list axst := ltac2:(tb__ "0|0|
S4S1dS0S1dS32S0S1dS34S0S1dS36S0S1dS46S0S1dS44S0S1dS45S0S1dS48S0S1dS47S3S1dA1A3A3A3A3A3A3A3A3S4dA3").
Definition exits_sd : list axst := ltac2:(tb__ "0|0|
S0S1dS39S0S1dS3aS3S1dA1A3A3").
Definition cuts_sd0 : list axst := ltac2:(tb__ "0|0|
S0S1dS32S0S1dS34S0S1dS36S3S1dA1A3A3A3").
Definition cutpcs_sd : list Z := ltac2:(tb__ "0|0|
S4S58S0S58S69S0S58S6dS0S58S6bS0S58S6aS0S58S6eS0S58S6cS3S58A1A3A3A3A3A3A3S4eA3").

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymSoundW.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.

Lemma check_sd : ltac2:(tb__ "0|0|
S74S8S79S5fS4aS50S59S51S52A6SaA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Theorem scan_double_sum : ltac2:(tb__ "0|0|
S78OF_;S7cS1cS9S82Q40A1A1S7dS5fR4R3A3S7eS5fS59R4A3S77S5fR6S7bS5fR5S32R4R3A5S7aS5fR5S59R4R3S4cA6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_sd rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_sd cutpcs_sd NF cuts_sd exits_sd (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_sd) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_sd.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[]]].
    + apply exit_postA. in_nth 0.
    + apply exit_postA. in_nth 1.
  - left; reflexivity.
Qed.

