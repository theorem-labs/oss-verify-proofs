(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "memcpy_entryA"; "Posts_memcpyA"; "Posts_mhA"; "Pre_memcpyA"; "Pre_mhA"; "cuts_memcpyA"; "cuts_mhA"; "liftA"; "exits_memcpyA"; "exits_mhA"; "vcuts_memcpyA"; "vcuts_mhA"; "vexits_memcpyA"; "vexits_mhA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy"; "FUELC"; "cutpcs_memcpy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyHdr"; "FUELH"; "cutpcs_mh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "check_ecfgA"; "mkVNA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vn_rank"; "vn_state"; "vn_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "lf_reason"; "lf_state"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemcpy MuslMemcpyHdr CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition memcpy_entryA : Z := 0xddf74.

Definition liftA (S : sstate) : axst := mkA S [].
Definition liftLA (L : leaf) : leafA := ltac2:(tb__ "0|0|
S28SdS2dVL;A1A1S2cVL;A1A2").
Definition liftVA (n : vnode) : vnodeA := ltac2:(tb__ "0|0|
S25SdS2aVn;A1A1S29Vn;A1S2bVn;A1A3").

Definition Pre_memcpyA : axst := liftA (Pre_memcpy memcpy_entryA).
Definition Posts_memcpyA : list leafA := map liftLA (Posts_memcpy memcpy_entryA).
Definition cuts_memcpyA : list axst := map liftA (cuts_memcpy memcpy_entryA).
Definition exits_memcpyA : list axst := map liftA (exits_memcpy memcpy_entryA).
Definition vcuts_memcpyA : list vnodeA := map liftVA (vcuts_memcpy memcpy_entryA).
Definition vexits_memcpyA : list vnodeA := map liftVA (vexits_memcpy memcpy_entryA).

Definition check_memcpyA__runs : ltac2:(tb__ "0|0|
S2S5S2S27A1A1A1") := ltac2:(tb__ "0|0|
S26S0S1cS1dS6A1SbA4").
Lemma check_memcpyA : ltac2:(tb__ "0|0|
S14S3S23S0S1cS1dS6A1S1SbSeA6S4A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUELC (cutpcs_memcpy memcpy_entryA) NF cuts_memcpyA exits_memcpyA check_memcpyA__runs); [unfold check_memcpyA__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Lemma echeck_memcpyA : ltac2:(tb__ "0|0|
S14S3S24S0S1cS1dS6A1S1S10S12A6S4A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUELC (cutpcs_memcpy memcpy_entryA) NF vcuts_memcpyA vexits_memcpyA check_memcpyA__runs); [unfold check_memcpyA__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem memcpy_sumA : ltac2:(tb__ "0|0|
S22OF_;S18S15S2S1bQ40A1A1S1aS0R4R3A3S19S0S1R4A3S21S0R6S17S0R5S9R4R3A5S16S0R5S1R4R3S7A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_memcpyA rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELC (cutpcs_memcpy memcpy_entryA) NF cuts_memcpyA exits_memcpyA (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_memcpyA) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_memcpyA.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[]]].
    + apply exit_postA. in_nth 0.
    + apply exit_postA. in_nth 1.
  - left; reflexivity.
Qed.

Theorem memcpy_sumA_ex : ltac2:(tb__ "0|0|
S18S15S2S1bQ40A1A1S19S0S1R3A3S20S0S17S0R4S9R3R2A5S16S0R4S1R3R2S7A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_memcpyA rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_memcpyA with (vna_state (liftVA (mkVN (Pre_memcpy memcpy_entryA) 10 (SLit 0)))).
  apply (cfg_complete_autoA segs FUELC (cutpcs_memcpy memcpy_entryA) NF vcuts_memcpyA vexits_memcpyA (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_memcpyA) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. unfold vcuts_memcpyA, vcuts_memcpy in Hin. cbn [map] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbv; congruence|]). destruct Hin.
  - exact echeck_memcpyA.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[]]].
    + apply (eexit_postA segs J NF rho vcuts_memcpyA Posts_memcpyA (liftVA (mkVN (P_retA memcpy_entryA) 0 (SLit 0)))). in_nth 0.
    + apply (eexit_postA segs J NF rho vcuts_memcpyA Posts_memcpyA (liftVA (mkVN (P_retB memcpy_entryA) 0 (SLit 0)))). in_nth 1.
  - left; reflexivity.
Qed.

Definition Pre_mhA : axst := liftA (Pre_mh memcpy_entryA).
Definition Posts_mhA : list leafA := map liftLA (Posts_mh memcpy_entryA).
Definition cuts_mhA : list axst := map liftA (cuts_mh memcpy_entryA).
Definition exits_mhA : list axst := map liftA (exits_mh memcpy_entryA).
Definition vcuts_mhA : list vnodeA := map liftVA (vcuts_mh memcpy_entryA).
Definition vexits_mhA : list vnodeA := map liftVA (vexits_mh memcpy_entryA).

Definition check_mhA__runs : ltac2:(tb__ "0|0|
S2S5S2S27A1A1A1") := ltac2:(tb__ "0|0|
S26S0S1eS1fS6A1ScA4").
Lemma check_mhA : ltac2:(tb__ "0|0|
S14S3S23S0S1eS1fS6A1S1ScSfA6S4A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUELH (cutpcs_mh memcpy_entryA) NF cuts_mhA exits_mhA check_mhA__runs); [unfold check_mhA__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Lemma echeck_mhA : ltac2:(tb__ "0|0|
S14S3S24S0S1eS1fS6A1S1S11S13A6S4A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUELH (cutpcs_mh memcpy_entryA) NF vcuts_mhA vexits_mhA check_mhA__runs); [unfold check_mhA__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem memcpy_hdr_sumA : ltac2:(tb__ "0|0|
S22OF_;S18S15S2S1bQ40A1A1S1aS0R4R3A3S19S0S1R4A3S21S0R6S17S0R5SaR4R3A5S16S0R5S1R4R3S8A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mhA rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELH (cutpcs_mh memcpy_entryA) NF cuts_mhA exits_mhA (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_mhA) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_mhA.
  - intros E rhoE HinE. destruct HinE as [<-|[]]. apply exit_postA. in_nth 0.
  - left; reflexivity.
Qed.

Theorem memcpy_hdr_sumA_ex : ltac2:(tb__ "0|0|
S18S15S2S1bQ40A1A1S19S0S1R3A3S20S0S17S0R4SaR3R2A5S16S0R4S1R3R2S8A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mhA rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mhA with (vna_state (liftVA (mkVN (Pre_mh memcpy_entryA) 10 (SLit 0)))).
  apply (cfg_complete_autoA segs FUELH (cutpcs_mh memcpy_entryA) NF vcuts_mhA vexits_mhA (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_mhA) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. unfold vcuts_mhA, vcuts_mh in Hin. cbn [map] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbv; congruence|]). destruct Hin.
  - exact echeck_mhA.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    apply (eexit_postA segs J NF rho vcuts_mhA Posts_mhA (liftVA (mkVN (P_mh memcpy_entryA) 0 (SLit 0)))). in_nth 0.
  - left; reflexivity.
Qed.
