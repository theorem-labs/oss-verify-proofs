(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "prod"; "pair"; "bool"; "false"; "None"; "app"; "list"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SVar"; "sstate"; "SLit"; "sobj"; "SAlu"; "SPBranch"; "FcsrFrm0"; "mkSS"; "SPUle"; "DUnknown"; "cell"; "mkObj"; "valuation"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "mkVN"; "check_cfg"; "check_ecfg"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy.States"; "mc_cut"; "N14"; "O_dst"; "O_src"; "P_retA"; "P_retB"; "C_48"; "C_54"; "C_58"; "C_L1"; "C_a4"; "C_al"; "C_c1"; "C_c2"; "C_c3"; "C_e18"; "Pre_memcpy"; "B120"; "B121"; "J120"; "src_cur"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "NPOST"; "post_regs"; "cut_regs"; "pre_regs"; "setregs"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "list_set"; "mkLeaf"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy"; "FUELC"; "Posts_memcpy"; "Pre_memcpy"; "cutpcs_memcpy"; "cuts_memcpy"; "exits_memcpy"; "vcuts_memcpy"; "vexits_memcpy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section States.
Variable base : Z.

Definition N14 : sprop := SPUle (SVar 14) (SLit two62).
Definition O_dst : sobj := ltac2:(tb__ "0|0|
S18SdPcA1SfZ0A1SdPeA1S1S17A1S16A5").
Definition O_src : sobj := ltac2:(tb__ "0|0|
S18SdPdA1SfZ0A1SdPeA1S1S17A1S16A5").

Definition Pre_memcpy : sstate := ltac2:(tb__ "0|0|
S14Vbase;S3bS37S13S7ScA1S0S10S23S0S10S24S1S10A1A3A3S0SbS22S1SbA1A3S36S6A9").

Definition J120 : sprop := ltac2:(tb__ "0|0|
S15S11S3dSdP78A1SdP79A1A3SdPeA1A2").
Definition B120 : sprop := SPUle (SVar 120) (SLit two62).
Definition B121 : sprop := SPUle (SVar 121) (SLit two62).

Definition src_cur (cs : Z) : sv := ltac2:(tb__ "0|2|
S5ScL_;S20Vcs;Z0A2S11S3dSdPdA1M0SdP78A1M1A3S11S3dS11S3dG0SfVcs;A1A3G1A3X5x2").

Definition mc_cut (pc : Z) (cs : Z) (extra : list (nat * sv)) (facts : list sprop) : sstate := ltac2:(tb__ "0|2|
S14Vpc;S3cS3aS36A1S8S3S2ScA2M0S0G0S4S2ScUaSdPcA1M1A4S0G0S4S2ScUbS35Vcs;A1A4S0G0S4S2ScUcSdP79A1A4S0G0S4S2ScUdS11S3dG1SdP78A1A3A4S1G0A1A3A3A3A3Vextra;A3A2S37S13S7ScA1S0S10S23S0S10S24S1S10A1A3A3S8SbVfacts;S0SbS34S0SbS32S0SbS33S0SbS22S1SbA1A3A3A3A3A3P87S6A9").

Definition C_L1 : sstate := ltac2:(tb__ "0|2|
S21S1fVbase;Z18A2Z0S0S3S2ScA2M0S4S2ScUeS11S3dSdPdA1S11S3dSdP78A1SfZ1A1M1A3A3A4S0G0S4S2ScUfG1A4S1G0A1A3A3S0SbS15G1SdP79A1A2S1SbA1A3A4").

Definition C_48 : sstate := ltac2:(tb__ "0|0|
S21S1fVbase;Z50A2Z0S1S3S2ScA2A1S1SbA1A4").
Definition C_e18 : sstate := ltac2:(tb__ "0|0|
S21S1fVbase;Z120A2Z0S1S3S2ScA2A1S1SbA1A4").

Definition C_al : sstate := ltac2:(tb__ "0|2|
S21S1fVbase;Z12cA2Z0S0S3S2ScA2M0S4S2ScUeSfZfA1M1A4S1G0A1A3S0SbS12S3eG1SdP79A1A3S1SbA1A3A4").

Definition C_c2 : sstate := ltac2:(tb__ "0|2|
S21S1fVbase;Za4A2ZeS0S3S2ScA2M0S4S2ScUfSfZ11A1M1A4S1G0A1A3S0SbS12S3eG1SdP79A1A3S1SbA1A3A4").
Definition C_c3 : sstate := ltac2:(tb__ "0|2|
S21S1fVbase;Z1acA2ZfS0S3S2ScA2M0S4S2ScUfSfZ12A1M1A4S1G0A1A3S0SbS12S3eG1SdP79A1A3S1SbA1A3A4").
Definition C_c1 : sstate := ltac2:(tb__ "0|2|
S21S1fVbase;Z240A2ZdS0S3S2ScA2M0S4S2ScUfSfZ10A1M1A4S1G0A1A3S0SbS12S3eG1SdP79A1A3S1SbA1A3A4").

Definition C_58 : sstate := ltac2:(tb__ "0|0|
S21S1fVbase;Z60A2Z0S1S3S2ScA2A1S0SbS12S3eSdP79A1SfZ10A1A3S1SbA1A3A4").
Definition C_a4 : sstate := ltac2:(tb__ "0|1|
S21S1fVbase;Z2acA2Z0S1S3S2ScA2A1S0SbS15SfZ10A1SdP79A1M0A2S0SbS12S3eG0SfZ20A1A3S1SbA1A3A3A4").
Definition C_54 : sstate := ltac2:(tb__ "0|0|
S21S1fVbase;Z15cA2Z0S1S3S2ScA2A1S0SbS12S3eSdP79A1SfZ10A1A3S1SbA1A3A4").

Definition P_retA : sstate := ltac2:(tb__ "0|0|
S14S1fVbase;Z3d0A2S42ScS39S36A1UaSdPcA1A4S37S13S7ScA1S0S10S23S0S10S24S1S10A1A3A3S0SbS22S1SbA1A3S38S6A9").
Definition P_retB : sstate := ltac2:(tb__ "0|0|
S14S1fVbase;Z400A2S42ScS39S36A1UaSdPcA1A4S37S13S7ScA1S0S10S23S0S10S24S1S10A1A3A3S0SbS22S1SbA1A3S38S6A9").
Definition Posts_memcpy : list leaf := ltac2:(tb__ "0|0|
S0S40S43S25S41A2S0S40S43S26S41A2S1S40A1A3A3").

Definition cuts_memcpy : list sstate := ltac2:(tb__ "0|0|
S0SeS31S0SeS2aS0SeS27S0SeS30S0SeS2cS0SeS2eS0SeS2fS0SeS2dS0SeS29S0SeS2bS0SeS28S1SeA1A3A3A3A3A3A3A3A3A3A3A3").
Definition exits_memcpy : list sstate := ltac2:(tb__ "0|0|
S0SeS25S0SeS26S1SeA1A3A3").
Definition cutpcs_memcpy : list Z := map ss_pc (tl cuts_memcpy).

Definition vcuts_memcpy : list vnode := ltac2:(tb__ "0|5|
S0S1bS1cS31ZaSfZ0A1M0A3S0S1bS1cS2aZ9SdP79A1M1A3S0S1bS1cS27Z8M2G0A3S0S1bS1cS30G2G0A3S0S1bS1cS2cZ7M3G1A3S0S1bS1cS2eG3G1A3S0S1bS1cS2fG3G1A3S0S1bS1cS2dG3G1A3S0S1bS1cS29Z6M4G0A3S0S1bS1cS2bG4G0A3S0S1bS1cS28G4G0A3S1S1bA1A3A3A3A3A3A3A3A3A3A3A3").
Definition vexits_memcpy : list vnode := ltac2:(tb__ "0|2|
S0S1bS1cS25Z0M0SfG0A1M1A3S0S1bS1cS26G0G1A3S1S1bA1A3A3").

End States.

Definition FUELC : nat := 3000%nat.

Section Generic.
Variable segs : list Segment.
Variable base : Z.
Hypothesis check_memcpy : ltac2:(tb__ "0|0|
S3fS5S1dVsegs;S49S4cVbase;A1S36S4dVbase;A1S4eVbase;A1A6SaA3").
Hypothesis echeck_memcpy : ltac2:(tb__ "0|0|
S3fS5S1eVsegs;S49S4cVbase;A1S36S4fVbase;A1S50Vbase;A1A6SaA3").

Lemma cuts_memcpy_strict : ltac2:(tb__ "0|0|
S3fS5S54SeS1aS4dVbase;A1A3S6A3").
Proof using . reflexivity. Qed.

Theorem memcpy_sum : ltac2:(tb__ "0|0|
S53OF_;S9S45A1S44OF_;F_;S19S48Vsegs;R3R2A3S52Vsegs;R4S47Vsegs;R3S4bVbase;A1R2A4S46Vsegs;R3S36R2S4aVbase;A1A5A4F_;Frho;FK;Fok;").
Proof using check_memcpy.
  intros ok K rho Hok.
  apply (cfg_sound segs FUELC (cutpcs_memcpy base) NF (cuts_memcpy base) (exits_memcpy base)
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho (Posts_memcpy base)) Hok).
  - rewrite cuts_memcpy_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_memcpy.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[]]].
    + apply exit_post; [left; reflexivity | exact HagE].
    + apply exit_post; [right; left; reflexivity | exact HagE].
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Theorem memcpy_sum_ex : ltac2:(tb__ "0|0|
S9S45A1S44OF_;F_;S19S51Vsegs;S47Vsegs;R2S4bVbase;A1R1A4S46Vsegs;R2S36R1S4aVbase;A1A5A3Frho;FK;").
Proof using echeck_memcpy.
  intros K rho.
  change (Pre_memcpy base) with (vn_state (mkVN (Pre_memcpy base) 10 (SLit 0))).
  apply (cfg_complete_auto segs FUELC (cutpcs_memcpy base) NF (vcuts_memcpy base) (vexits_memcpy base)
           (fun rho' => agree_below NF rho rho') K (LQ segs K NF rho (Posts_memcpy base))).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_memcpy.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[<-|[]]].
    + apply eexit_post; [left; reflexivity | exact HgE].
    + apply eexit_post; [right; left; reflexivity | exact HgE].
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
End Generic.

