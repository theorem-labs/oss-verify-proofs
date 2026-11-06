(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "app"; "bool"; "list"; "None"; "false"; "prod"; "true"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "sobj"; "SPUle"; "SVar"; "cell"; "SAlu"; "FcsrFrm0"; "mkSS"; "DUnknown"; "mkCell"; "mkObj"; "valuation"; "SPAlign"; "SPEq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "A_globals"; "mkA"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "setregs"; "cut_regs"; "post_regs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_scale2d"; "v120"; "vP"; "Pre_sc"; "v121"; "vN"; "FUEL_sc"; "O_pts"; "O_stk"; "X_sc"; "base_facts"; "cutpcs_sc"; "C1"; "P_sc"; "Posts_sc"; "cuts_sc"; "szb"; "NXC"; "NXP"; "cut_fregs"; "exits_sc"; "fcallee_saved"; "inv"; "post_fregs"; "sc_state"; "two31"; "two47"; "vcuts_sc"; "vexits_sc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "mkLeafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_scale2d.TessScale2dAddr"; "sc_L1"; "sc_entry"; "sc_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"].
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

Module TessScale2dAddr.
  Definition sc_entry : Z := 0xadf68.
  Definition sc_L1 : Z := 0xadfa4.
  Definition sc_ret : Z := 0xae038.
End TessScale2dAddr.
Import TessScale2dAddr.

Definition FUEL_sc : nat := 300%nat.

Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition cut_fregs : list sv := ltac2:(tb__ "0|0|
S54S2ScS2S5ScL_;S3aR1A1S11S52S4cU3cR1A2A1A1S11S52S4cU8cR1A2A1A1X5x2Lr;S55U0U20A2A4").
Definition post_fregs : list sv := cut_fregs.
Definition NXC : positive := 175%positive.
Definition NXP : positive := 180%positive.

Definition vP : sv := SVar 12.
Definition vN : sv := SVar 13.
Definition szb : sv := SAlu ALU_SLL vN (SLit 4).
Definition two31 : Z := 2 ^ 31.
Definition two47 : Z := 2 ^ 47.
Definition base_facts : list sprop := ltac2:(tb__ "0|1|
S0SeS10SdZ1A1M0S2aA2S0SeS10S2aSdS3eA1A2S0SeS10G0S27A2S0SeS10S27SdS3fA1A2S0SeS1aPcZ3A2S1SeA1A3A3A3A3A3").
Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S11PaA1SdN10A1SdZ0A1Vcells;S16A5").
Definition O_pts : sobj := ltac2:(tb__ "0|0|
S18S27SdZ0A1S35S1S12A1S16A5").
Definition X_sc : list (sv * sv) := ltac2:(tb__ "0|1|
S0S9ScScA2M0S3ScScS27S35A4S1G0A1A3").

Definition Pre_sc : axst := ltac2:(tb__ "0|0|
S1eS15S57S25S24S14S7ScA1S4SfS0SfS2dS1S12A1A1S0SfS2cS1SfA1A3A3S1dA3S2fS20S8A9S2eA2").

Definition v120 : sv := SVar 120.
Definition v121 : sv := SVar 121.
Definition inv : list sprop := ltac2:(tb__ "0|1|
S0SeS10SdZ1A1M0S26A2S0SeS10S26S2aA2S0SeS1bS13S46S29S13S47S26G0A3A3S13S46S13S47S2aG0A3G0A3A2S0SeS10G0S29A2S0SeS10S29SdZffffffffA1A2S1SeA1A3A3A3A3A3").

Definition sc_state (pc : Z) (regs : list (nat * sv)) (fregs : list (nat * sv)) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S1eS15Vpc;S21S22S20A1S4S9S2ScA2M0S0G0S3S2ScU2S13S46S11PaA1SdN10A1A3A4S0G0S3S2ScUaS27A4S0G0S3S2ScUcS1fA4S1G0A1A3A3A3Vregs;A3A2S21S38S0G0S3S2ScUfSdZ0A1A4Vfregs;A3A2S14S7ScA1S4SfS0SfS2dS0S12S17SdN8A1Z8S11PbA1A3S1S12A1A3A1S0SfS2cS1SfA1A3A3S1dA3S4SeVfacts;S2fA3S36S8A9S2eA2").

Definition C1 : axst := ltac2:(tb__ "0|2|
S3dS56S0S9S2ScA2M0S3S2ScUdS26A4S0G0S3S2ScUeS29A4S1G0A1M1A3A3G1S3bA4").

Definition P_sc : axst := ltac2:(tb__ "0|0|
S1eS15S58S23S20A1S3cS14S7ScA1S4SfS0SfS2dS0S12S17SdN8A1Z8S11PbA1A3S1S12A1A3A1S0SfS2cS1SfA1A3A3S1dA3S2fS37S8A9S2eA2").
Definition Posts_sc : list leafA := ltac2:(tb__ "0|0|
S0S49S4aS32S5cA2S1S49A1A3").

Definition cuts_sc : list axst := ltac2:(tb__ "0|0|
S0S48S28S0S48S31S1S48A1A3A3").
Definition exits_sc : list axst := [P_sc].
Definition cutpcs_sc : list Z := [sc_L1].

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Definition check_sc__runs : ltac2:(tb__ "0|0|
S6SbS6S49A1A1A1") := ltac2:(tb__ "0|0|
S5dS1cS2bS30S34A4").
Lemma check_sc : ltac2:(tb__ "0|0|
S4bS5S44S1cS2bS30S20S34S39A6SaA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUEL_sc cutpcs_sc NF cuts_sc exits_sc check_sc__runs); [unfold check_sc__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem scale2d_sum : ltac2:(tb__ "0|0|
S5bOF_;S4fS19S6S53Q40A1A1S51S1cR4R3A3S50S1cS20R4A3S5aS1cR6S4eS1cR5S28R4R3A5S4dS1cR5S20R4R3S33A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_sc rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_sc cutpcs_sc NF cuts_sc exits_sc (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_sc) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_sc.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply exit_postA. in_nth 0.
  - left; reflexivity.
Qed.

Definition vcuts_sc : list vnodeA := ltac2:(tb__ "0|0|
S0S42S43S28Z1eSdZ0A1A3S0S42S43S31Z14S26A3S1S42A1A3A3").
Definition vexits_sc : list vnodeA := ltac2:(tb__ "0|0|
S0S42S43S32Z1SdZ0A1A3S1S42A1A3").

Lemma echeck_sc : ltac2:(tb__ "0|0|
S4bS5S45S1cS2bS30S20S40S41A6SaA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUEL_sc cutpcs_sc NF vcuts_sc vexits_sc check_sc__runs); [unfold check_sc__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem scale2d_sum_ex : ltac2:(tb__ "0|0|
S4fS19S6S53Q40A1A1S50S1cS20R3A3S59S1cS4eS1cR4S28R3R2A5S4dS1cR4S20R3R2S33A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_sc rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_sc with (vna_state (mkVNA Pre_sc 30 (SLit 0))).
  apply (cfg_complete_autoA segs FUEL_sc cutpcs_sc NF vcuts_sc vexits_sc (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_sc) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. destruct Hin as [<-|[<-|[]]]; cbv; congruence.
  - exact echeck_sc.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply (eexit_postA segs J NF rho vcuts_sc Posts_sc (mkVNA P_sc 1 (SLit 0))). in_nth 0.
  - left; reflexivity.
Qed.
