(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "false"; "None"; "bool"; "prod"; "true"; "list"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sprop"; "sv"; "sobj"; "SLit"; "SPAlign"; "cell"; "sstate"; "FcsrFrm0"; "mkSS"; "DUnknown"; "SAlu"; "SPUle"; "mkObj"; "mkCell"; "valuation"; "SExt"; "SPBranch"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "NPOST"; "cut_regs"; "post_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "mkVN"; "check_cfg"; "check_ecfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyHdr.States"; "F_al"; "N14h"; "O_srcH"; "C0_mh"; "C1_mh"; "HV"; "O_dst0"; "O_dstH"; "P_mh"; "Pre_mh"; "B120h"; "B121h"; "F_c1"; "J120h"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyHdr"; "FUELH"; "Posts_mh"; "Pre_mh"; "cutpcs_mh"; "cuts_mh"; "exits_mh"; "vcuts_mh"; "vexits_mh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@Stdlib.Lists.List"; "existsb"].
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

Definition HV : positive := 16%positive.
Definition N14h : sprop := SPUle (SVar 14) (SLit two62).

Definition F_al : list sprop := ltac2:(tb__ "0|2|
S0ScS10PcZ2M0A2S0ScS10PdG0A2S0ScS10PeM1Z4A2S0ScS17SfZ10A1SbG1A1A2S1ScA1A3A3A3A3").
Definition O_dst0 : sobj := ltac2:(tb__ "0|0|
S18SbPcA1SfZ0A1SbPeA1S1S11A1S15A5").
Definition O_dstH : sobj := ltac2:(tb__ "0|1|
S18SbPcA1SfZ0A1M0SbPeA1S0S11S19G0Z4S1bS8Q20SbS2eA1A3A3S1S11A1A3S15A5").
Definition O_srcH : sobj := ltac2:(tb__ "0|1|
S18SbPdA1SfZ0A1M0SbPeA1S0S11S19G0Z4SbS2eA1A3S1S11A1A3S15A5").

Definition Pre_mh : sstate := ltac2:(tb__ "0|0|
S14Vbase;S21S1fS13S5SdA1S0SeS2fS0SeS2bS1SeA1A3A3S0ScS2aS29A3S1eS4A9").

Definition C0_mh : sstate := ltac2:(tb__ "0|1|
S14S3aVbase;Z12cA2S20S21S0S7S2SdA2M0S3S2SdUdSbPcA1A4S0G0S3S2SdUeSfZfA1A4S0G0S3S2SdUfSfZ0A1A4S1G0A1A3A3A3A2S1fS13S5SdA1S0SeS2fS0SeS2bS1SeA1A3A3S0ScS2aS29A3S1eS4A9").

Definition J120h : sprop := ltac2:(tb__ "0|0|
S17S16S38SbP78A1SbP79A1A3SbPeA1A2").
Definition B120h : sprop := SPUle (SVar 120) (SLit two62).
Definition B121h : sprop := SPUle (SVar 121) (SLit two62).
Definition F_c1 : list sprop := ltac2:(tb__ "0|3|
S0ScS1cS39SfZfA1SbP79M0A1A3S0ScS10P78M1Z4M2A2S0ScS10G0G2A2S0ScS17SfZ10A1SbG1A1A2S0ScS36S0ScS33S0ScS34S1ScA1A3A3A3A3A3A3A3").
Definition C1_mh : sstate := ltac2:(tb__ "0|3|
S14S3aVbase;Z12cA2S20S23S1eA1S0S7S2SdA2M0S3S2SdUaSbPcA1M1A4S0G0S3S2SdUbS16S38SbPdA1SbP78A1M2A3A4S0G0S3S2SdUcSbP79A1A4S0G0S3S2SdUdS16S38G1G2A3A4S0G0S3S2SdUeSfZfA1A4S1G0A1A3A3A3A3A3A2S1fS13S5SdA1S0SeS30S0SeS2bS1SeA1A3A3SaScS35S0ScS2aS29A3A3P87S4A9").

Definition P_mh : sstate := ltac2:(tb__ "0|1|
S14S3aVbase;Z3d0A2S20S24S1eA1S0S7S2SdA2M0S3S2SdUaSbPcA1A4S1G0A1A3A2S1fS13S5SdA1S0SeS30S0SeS2bS1SeA1A3A3S0ScS2aS29A3S22S4A9").
Definition Posts_mh : list leaf := ltac2:(tb__ "0|0|
S0S40S42S31S41A2S1S40A1A3").

Definition cuts_mh : list sstate := ltac2:(tb__ "0|0|
S0S12S32S0S12S2cS0S12S2dS1S12A1A3A3A3").
Definition exits_mh : list sstate := [P_mh].
Definition cutpcs_mh : list Z := [base + 0x12c].

Definition vcuts_mh : list vnode := ltac2:(tb__ "0|1|
S0S25S26S32ZaSfZ0A1M0A3S0S25S26S2cZ9G0A3S0S25S26S2dZ7SbP79A1A3S1S25A1A3A3A3").
Definition vexits_mh : list vnode := ltac2:(tb__ "0|1|
S0S25S26S31Z0M0SfG0A1A3S1S25A1A3").
End States.

Definition FUELH : nat := 300%nat.

Section Generic.
Variable segs : list Segment.
Variable base : Z.
Hypothesis check_mh : ltac2:(tb__ "0|0|
S37S6S27Vsegs;S43S46Vbase;A1S1eS47Vbase;A1S48Vbase;A1A6S8A3").
Hypothesis echeck_mh : ltac2:(tb__ "0|0|
S37S6S28Vsegs;S43S46Vbase;A1S1eS49Vbase;A1S4aVbase;A1A6S8A3").

Lemma cuts_mh_strict : ltac2:(tb__ "0|0|
S37S6S4eS12S1dS47Vbase;A1A3S4A3").
Proof using . reflexivity. Qed.

Theorem memcpy_hdr_sum : ltac2:(tb__ "0|0|
S4dOF_;S9S3cA1S3bOF_;F_;S1aS3fVsegs;R3R2A3S4cVsegs;R4S3eVsegs;R3S45Vbase;A1R2A4S3dVsegs;R3S1eR2S44Vbase;A1A5A4F_;Frho;FK;Fok;").
Proof using check_mh.
  intros ok K rho Hok.
  apply (cfg_sound segs FUELH (cutpcs_mh base) NF (cuts_mh base) (exits_mh base)
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho (Posts_mh base)) Hok).
  - rewrite cuts_mh_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_mh.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[]].
    apply exit_post; [left; reflexivity | exact HagE].
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Theorem memcpy_hdr_sum_ex : ltac2:(tb__ "0|0|
S9S3cA1S3bOF_;F_;S1aS4bVsegs;S3eVsegs;R2S45Vbase;A1R1A4S3dVsegs;R2S1eR1S44Vbase;A1A5A3Frho;FK;").
Proof using echeck_mh.
  intros K rho.
  change (Pre_mh base) with (vn_state (mkVN (Pre_mh base) 10 (SLit 0))).
  apply (cfg_complete_auto segs FUELH (cutpcs_mh base) NF (vcuts_mh base) (vexits_mh base)
           (fun rho' => agree_below NF rho rho') K (LQ segs K NF rho (Posts_mh base))).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_mh.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[]].
    apply eexit_post; [left; reflexivity | exact HgE].
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
End Generic.
