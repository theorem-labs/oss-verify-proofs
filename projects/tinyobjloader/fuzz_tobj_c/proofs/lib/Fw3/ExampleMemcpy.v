(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "nil"; "prod"; "bool"; "pair"; "list"; "true"; "false"; "None"; "app"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "sprop"; "sstate"; "SLit"; "sobj"; "SAlu"; "SPBranch"; "valuation"; "FcsrFrm0"; "mkSS"; "SPUle"; "DUnknown"; "cell"; "mkObj"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "baseP"; "baseU"; "segsP"; "segsU"; "FUELC"; "Posts_memcpy"; "Pre_memcpy"; "cutpcs_memcpy"; "cuts_memcpy"; "pre_fregs"; "exits_memcpy"; "vcuts_memcpy"; "vexits_memcpy"; "NPOST"; "post_regs"; "cut_regs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "mkVN"; "check_cfg"; "check_ecfg"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.States"; "mc_cut"; "N14"; "O_dst"; "O_src"; "P_retA"; "P_retB"; "C_48"; "C_54"; "C_58"; "C_L1"; "C_a4"; "C_al"; "C_c1"; "C_c2"; "C_c3"; "C_e18"; "Pre_memcpy"; "B120"; "B121"; "J120"; "src_cur"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "list_set"; "RsSymJump"; "mkLeaf"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "add"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.Conventions"; "callee_saved"; "pre_reg"; "@Stdlib.Lists.List"; "existsb"; "fold_left"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Plain.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Ubsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition segsP : list Segment := Plain.M.loaded_segments.
Definition segsU : list Segment := Ubsan.M.loaded_segments.
Definition baseP : Z := 0x26b94.
Definition baseU : Z := 0x272d4.

Section Conventions.

Definition NF : positive := 100%positive.
Definition NPOST : positive := 140%positive.

Definition pre_reg (r : nat) : sv := ltac2:(tb__ "0|1|
S0SdLr;Vr;SeS5aS5cU14Vr;A2A1A1M0S0S0SdLn;R1SePbA1S0S0SdLn0;R1SePaA1S0S0SdLn1;R1G0S0S0SdLn2;R1G0S0S0SdLn3;R1G0S0S0SdLn4;R1G0S0S0SdLn5;R1G0S0S0SdLn6;R1G0S0S0SdLn7;R1G0S0S0SdLn8;R1SePcA1S0S0SdLn9;R1SePdA1S0S0SdLn10;R1SePeA1S0G0Ln11;X0x2Ln10;X0x2Ln9;X0x2Ln8;X0x2Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition pre_regs : list sv := map pre_reg (seq 0 32).
Definition pre_fregs : list sv := ltac2:(tb__ "0|0|
S5dS0SdS0SeS5aS5cU3cR1A2A1A1Lr;S5eU0U20A2A4").

Definition callee_saved (r : nat) : bool :=
  match r with
  | 1 | 2 | 3 | 4 | 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true
  | _ => false
  end%nat.

Definition cut_regs (base : positive) : list sv := ltac2:(tb__ "0|0|
S5dS0SdS0S4SdL_;S5fR1A1S60R1A1SeS5bVbase;S5aR1A1A2A1X4x2Lr;S5eU0U20A2A4").
Definition post_regs (base : positive) : list sv := cut_regs base.

End Conventions.

Definition setregs (rs : list sv) (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|2|
S62S6SdA1M0S3S0SdA2M1G0G1S57SdR2SbS0SdR1A3ScS0SdR1A3A4Lp;Lacc;Vl;Vrs;A5").

Section States.
Variable base : Z.

Definition two62 : Z := 2 ^ 62.
Definition N14 : sprop := SPUle (SVar 14) (SLit two62).
Definition O_dst : sobj := ltac2:(tb__ "0|0|
S1bSePcA1S11Z0A1SePeA1S2S1aA1S19A5").
Definition O_src : sobj := ltac2:(tb__ "0|0|
S1bSePdA1S11Z0A1SePeA1S2S1aA1S19A5").

Definition Pre_memcpy : sstate := ltac2:(tb__ "0|0|
S17Vbase;S2eS27S16S9SdA1S1S12S38S1S12S39S2S12A1A3A3S1SfS37S2SfA1A3S1dS8A9").

Definition J120 : sprop := ltac2:(tb__ "0|0|
S18S13S4cSeP78A1SeP79A1A3SePeA1A2").
Definition B120 : sprop := SPUle (SVar 120) (SLit two62).
Definition B121 : sprop := SPUle (SVar 121) (SLit two62).

Definition src_cur (cs : Z) : sv := ltac2:(tb__ "0|2|
S4SdL_;S35Vcs;Z0A2S13S4cSePdA1M0SeP78A1M1A3S13S4cS13S4cG0S11Vcs;A1A3G1A3X4x2").

Definition mc_cut (pc : Z) (cs : Z) (extra : list (nat * sv)) (facts : list sprop) : sstate := ltac2:(tb__ "0|2|
S17Vpc;S2fS2dS1dA1SaS3S0SdA2M0S1G0S5S0SdUaSePcA1M1A4S1G0S5S0SdUbS4aVcs;A1A4S1G0S5S0SdUcSeP79A1A4S1G0S5S0SdUdS13S4cG1SeP78A1A3A4S2G0A1A3A3A3A3Vextra;A3A2S27S16S9SdA1S1S12S38S1S12S39S2S12A1A3A3SaSfVfacts;S1SfS49S1SfS47S1SfS48S1SfS37S2SfA1A3A3A3A3A3P87S8A9").

Definition C_L1 : sstate := ltac2:(tb__ "0|2|
S36S34Vbase;Z18A2Z0S1S3S0SdA2M0S5S0SdUeS13S4cSePdA1S13S4cSeP78A1S11Z1A1M1A3A3A4S1G0S5S0SdUfG1A4S2G0A1A3A3S1SfS18G1SeP79A1A2S2SfA1A3A4").

Definition C_48 : sstate := ltac2:(tb__ "0|0|
S36S34Vbase;Z50A2Z0S2S3S0SdA2A1S2SfA1A4").
Definition C_e18 : sstate := ltac2:(tb__ "0|0|
S36S34Vbase;Z120A2Z0S2S3S0SdA2A1S2SfA1A4").

Definition C_al : sstate := ltac2:(tb__ "0|2|
S36S34Vbase;Z12cA2Z0S1S3S0SdA2M0S5S0SdUeS11ZfA1M1A4S2G0A1A3S1SfS14S4dG1SeP79A1A3S2SfA1A3A4").

Definition C_c2 : sstate := ltac2:(tb__ "0|2|
S36S34Vbase;Za4A2ZeS1S3S0SdA2M0S5S0SdUfS11Z11A1M1A4S2G0A1A3S1SfS14S4dG1SeP79A1A3S2SfA1A3A4").
Definition C_c3 : sstate := ltac2:(tb__ "0|2|
S36S34Vbase;Z1acA2ZfS1S3S0SdA2M0S5S0SdUfS11Z12A1M1A4S2G0A1A3S1SfS14S4dG1SeP79A1A3S2SfA1A3A4").
Definition C_c1 : sstate := ltac2:(tb__ "0|2|
S36S34Vbase;Z240A2ZdS1S3S0SdA2M0S5S0SdUfS11Z10A1M1A4S2G0A1A3S1SfS14S4dG1SeP79A1A3S2SfA1A3A4").

Definition C_58 : sstate := ltac2:(tb__ "0|0|
S36S34Vbase;Z60A2Z0S2S3S0SdA2A1S1SfS14S4dSeP79A1S11Z10A1A3S2SfA1A3A4").
Definition C_a4 : sstate := ltac2:(tb__ "0|1|
S36S34Vbase;Z2acA2Z0S2S3S0SdA2A1S1SfS18S11Z10A1SeP79A1M0A2S1SfS14S4dG0S11Z20A1A3S2SfA1A3A3A4").
Definition C_54 : sstate := ltac2:(tb__ "0|0|
S36S34Vbase;Z15cA2Z0S2S3S0SdA2A1S1SfS14S4dSeP79A1S11Z10A1A3S2SfA1A3A4").

Definition P_retA : sstate := ltac2:(tb__ "0|0|
S17S34Vbase;Z3d0A2S57SdS2cS1dA1UaSePcA1A4S27S16S9SdA1S1S12S38S1S12S39S2S12A1A3A3S1SfS37S2SfA1A3S2bS8A9").
Definition P_retB : sstate := ltac2:(tb__ "0|0|
S17S34Vbase;Z400A2S57SdS2cS1dA1UaSePcA1A4S27S16S9SdA1S1S12S38S1S12S39S2S12A1A3A3S1SfS37S2SfA1A3S2bS8A9").
Definition Posts_memcpy : list leaf := ltac2:(tb__ "0|0|
S1S56S59S3aS58A2S1S56S59S3bS58A2S2S56A1A3A3").

Definition cuts_memcpy : list sstate := ltac2:(tb__ "0|0|
S1S10S46S1S10S3fS1S10S3cS1S10S45S1S10S41S1S10S43S1S10S44S1S10S42S1S10S3eS1S10S40S1S10S3dS2S10A1A3A3A3A3A3A3A3A3A3A3A3").
Definition exits_memcpy : list sstate := ltac2:(tb__ "0|0|
S1S10S3aS1S10S3bS2S10A1A3A3").
Definition cutpcs_memcpy : list Z := map ss_pc (tl cuts_memcpy).

Definition vcuts_memcpy : list vnode := ltac2:(tb__ "0|5|
S1S30S31S46ZaS11Z0A1M0A3S1S30S31S3fZ9SeP79A1M1A3S1S30S31S3cZ8M2G0A3S1S30S31S45G2G0A3S1S30S31S41Z7M3G1A3S1S30S31S43G3G1A3S1S30S31S44G3G1A3S1S30S31S42G3G1A3S1S30S31S3eZ6M4G0A3S1S30S31S40G4G0A3S1S30S31S3dG4G0A3S2S30A1A3A3A3A3A3A3A3A3A3A3A3").
Definition vexits_memcpy : list vnode := ltac2:(tb__ "0|2|
S1S30S31S3aZ0M0S11G0A1M1A3S1S30S31S3bG0G1A3S2S30A1A3A3").

End States.

Definition FUELC : nat := 3000%nat.

Section Generic.
Variable segs : list Segment.
Variable base : Z.
Hypothesis check_memcpy : ltac2:(tb__ "0|0|
S4bS4S32Vsegs;S22S25Vbase;A1S1dS26Vbase;A1S28Vbase;A1A6S7A3").
Hypothesis echeck_memcpy : ltac2:(tb__ "0|0|
S4bS4S33Vsegs;S22S25Vbase;A1S1dS29Vbase;A1S2aVbase;A1A6S7A3").

Lemma cuts_memcpy_strict : ltac2:(tb__ "0|0|
S4bS4S61S10S1cS26Vbase;A1A3S8A3").
Proof using . reflexivity. Qed.

Theorem memcpy_sum : ltac2:(tb__ "0|0|
S55OF_;S6S4fA1S4eOF_;F_;S15S52Vsegs;R3R2A3S54Vsegs;R4S51Vsegs;R3S24Vbase;A1R2A4S50Vsegs;R3S1dR2S23Vbase;A1A5A4F_;Frho;FK;Fok;").
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
S6S4fA1S4eOF_;F_;S15S53Vsegs;S51Vsegs;R2S24Vbase;A1R1A4S50Vsegs;R2S1dR1S23Vbase;A1A5A3Frho;FK;").
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

Lemma check_memcpy_P : ltac2:(tb__ "0|0|
S4bS4S32S20S22S25S1eA1S1dS26S1eA1S28S1eA1A6S7A3").
Proof. vm_compute. reflexivity. Qed.
Lemma echeck_memcpy_P : ltac2:(tb__ "0|0|
S4bS4S33S20S22S25S1eA1S1dS29S1eA1S2aS1eA1A6S7A3").
Proof. vm_compute. reflexivity. Qed.
Lemma check_memcpy_U : ltac2:(tb__ "0|0|
S4bS4S32S21S22S25S1fA1S1dS26S1fA1S28S1fA1A6S7A3").
Proof. vm_compute. reflexivity. Qed.
Lemma echeck_memcpy_U : ltac2:(tb__ "0|0|
S4bS4S33S21S22S25S1fA1S1dS29S1fA1S2aS1fA1A6S7A3").
Proof. vm_compute. reflexivity. Qed.

Theorem memcpy_sum_P : ltac2:(tb__ "0|0|
S55OF_;S6S4fA1S4eOF_;F_;S15S52S20R3R2A3S54S20R4S51S20R3S24S1eA1R2A4S50S20R3S1dR2S23S1eA1A5A4F_;Frho;FK;Fok;").
Proof. exact (memcpy_sum segsP baseP check_memcpy_P). Qed.
Theorem memcpy_sum_ex_P : ltac2:(tb__ "0|0|
S6S4fA1S4eOF_;F_;S15S53S20S51S20R2S24S1eA1R1A4S50S20R2S1dR1S23S1eA1A5A3Frho;FK;").
Proof. exact (memcpy_sum_ex segsP baseP echeck_memcpy_P). Qed.
Theorem memcpy_sum_U : ltac2:(tb__ "0|0|
S55OF_;S6S4fA1S4eOF_;F_;S15S52S21R3R2A3S54S21R4S51S21R3S24S1fA1R2A4S50S21R3S1dR2S23S1fA1A5A4F_;Frho;FK;Fok;").
Proof. exact (memcpy_sum segsU baseU check_memcpy_U). Qed.
Theorem memcpy_sum_ex_U : ltac2:(tb__ "0|0|
S6S4fA1S4eOF_;F_;S15S53S21S51S21R2S24S1fA1R1A4S50S21R2S1dR1S23S1fA1A5A3Frho;FK;").
Proof. exact (memcpy_sum_ex segsU baseU echeck_memcpy_U). Qed.
