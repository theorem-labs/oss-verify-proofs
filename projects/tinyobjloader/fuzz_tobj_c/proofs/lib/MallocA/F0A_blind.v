(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "None"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rl"; "rw"; "@Corelib.Init.Logic"; "eq"; "not"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind.Blind"; "JW"; "blind_rel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "ok_frameA"; "stableA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Corelib.Init.Specif"; "sumbool"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import RtCells.
Import ListNotations.
Open Scope Z_scope.

Section Blind.
Variable segs : list Segment.

Definition blind_rel (Zn TZ : Z -> Prop) (rp rho : valuation) : Prop := ltac2:(tb__ "0|8|
SbS1S9S12Q40M0A1M1S8Vrho;R1A2S8Vrp;R1A2A3Fi;SbS1S9S2S12Q8A1M2A1S7Vrho;R1A2S7Vrp;R1A2A3Fl;SbS0SaVZn;R1A1M3A1S9S4G2A1M4S16Vsegs;S6Vrho;A1M5R2A3S16Vsegs;S6Vrp;A1R2A3M6A3F_;Fz;SbS0G3SaS9G4G6S3G2A1M7A3A1SaS9G4S16Vsegs;G5R3A3G7A3A1F_;F_;Fz;G1SaVTZ;S13G0R1A2A1A1S9G4S6Vrho;R2A2S6Vrp;R2A2A3F_;Fa;A2A2A2A2").
Definition JW (Zn TZ : Z -> Prop) (J : jpredA) : jpredA := ltac2:(tb__ "0|0|
S5S2S12Q40A1A1S2S15A1S14ScS5S5SbVJ;R1R4R3R2A4SeVZn;VTZ;R1R5A4A2Lrp;A2Lmd;Ltr;Ltp;Lrho;").

Lemma blind_rel_refl : ltac2:(tb__ "0|1|
S0OF_;M0G0S5SeR3R2R1R1A4Frho;FTZ;FZn;").
Proof. intros Zn TZ rho. repeat split; intros; auto. Qed.
Lemma JW_intro : ltac2:(tb__ "0|1|
S0OF_;M0G0SfS5S2S12Q40A1A1S2S15A1S14R5R4R3R2R1A4SdR8R7R6R5R4R3R2A7F_;Fmd;Ftr;Ftp;Frho;FJ;FTZ;FZn;").
Proof. intros Zn TZ J rho tp tr md H. exists rho. split; [exact H | apply blind_rel_refl]. Qed.

Lemma JW_elim : ltac2:(tb__ "0|1|
S0OF_;M0G0SfS5S2S12Q40A1A1S2S15A1S14SdR7R6R5R4R3R2R1A7ScS5S5SbR7R1R5R4R3A4SeR9R8R1R6A4A2Lrp;A2F_;Fmd;Ftr;Ftp;Frho;FJ;FTZ;FZn;").
Proof. intros Zn TZ J rho tp tr md H. exact H. Qed.

Lemma JW_change : ltac2:(tb__ "0|7|
S0OFx;M0G0SfS5S5S2S12Q40M1A1M2A1S2S15A1S14S1S9G2S8R5R1A2S8R6R1A2A3Fi;S1S9S2S12Q8A1M3A1S7R6R1A2S7R7R1A2A3Fl;S0SaRbR1A1A1S9S4G3A1M4S16Vsegs;S6R8A1R2A3S16Vsegs;S6R9A1R2A3A3F_;Fz;S0RcR1A1SaS9G4S16Vsegs;S6RaA1M5R2A3S3G3A1M6A3A1SaS9G4S16Vsegs;G5R3A3G6A3A1F_;F_;Fz;G2SaRcS13G1R1A2A1A1S9G4S6RaR2A2S6RbR2A2A3F_;Fa;SdRdRcRbRaR8R7R6A7SdReRdRcRaR9R8R7A7F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FJ;FTZ;FZn;").
Proof.
  intros Zn TZ J rho rho' tp tr md Hw Hl Hout Hin Hrm (rp & HJ & Rw & Rl & Rout & Rin & Rrm).
  exists rp. split; [exact HJ|]. repeat split.
  - intros i. rewrite Hw. apply Rw.
  - intros l. rewrite Hl. apply Rl.
  - intros z Hz. rewrite (Hout z Hz). apply Rout. exact Hz.
  - intros z Hz Hp. apply (Hin z Hz). apply (Rin z Hz). exact Hp.
  - intros a Ha. rewrite (Hrm a Ha). exact (Rrm a Ha).
Qed.
Lemma JW_mono : ltac2:(tb__ "0|2|
S0OF_;M0G0G0SfS5S2S12Q40A1A1S2S15A1S14S0R9R1A1R9R2A1F_;Fz;S0S19RaR1A1M1SaG1A1A2Fz;SdRaR8R7R6R5R4R3A7SdRaR9R8R7R6R5R4A7F_;F_;F_;Fmd;Ftr;Ftp;Frho;FJ;FTZ;FZ2;FZ1;").
Proof.
  intros Z1 Z2 TZ J rho tp tr md Hsub Hdec (rp & HJ & Rw & Rl & Rout & Rin & Rrm).
  exists rp. split; [exact HJ|]. repeat split; [exact Rw | exact Rl | | | exact Rrm].
  - intros z Hz. apply Rout. intros H1. apply Hz. apply Hsub. exact H1.
  - intros z Hz Hp. destruct (Hdec z) as [H1|H1]; [exact (Rin z H1 Hp)|]. rewrite (Rout z H1). exact Hp.
Qed.

Lemma JW_map : ltac2:(tb__ "0|3|
S0OF_;M0G0SfSfS5S2S12Q40A1A1M1G1S2S15A1M2G2S14S14S5RaR1R7R5R3A4RaR2R7R5R3A4F_;Frp;SdRcRbRaR8R7R5R3A7SdRdRcRaR9R7R5R3A7F_;F_;Fmd';Fmd;Ftr';Ftr;Ftp';Ftp;Frho;FJ';FJ;FTZ;FZn;").
Proof. intros Zn TZ J J' rho tp tp' tr tr' md md' H (rp & HJ & R). exists rp. split; [exact (H rp HJ) | exact R]. Qed.

Lemma JW_stable : ltac2:(tb__ "0|1|
S1S0OF_;M0G0SfS11Vsegs;R4R1A3S11Vsegs;R5SdR4R3R2A3A3F_;FJ;FTZ;FZn;Fn;").
Proof.
  intros n Zn TZ J HS rho rho' tp tr md md' (Aw & Al & Am) Hme (rp & HJ & Rw & Rl & Rout & Rin & Rrm).
  exists (mkVal (rw rho') (rl rho') (rm rp)). split.
  - apply (HS rp (mkVal (rw rho') (rl rho') (rm rp)) tp tr md md'); [|exact Hme | exact HJ].
    split; [intros i Hi; cbn [rw]; rewrite <- (Rw i); apply Aw; exact Hi|]. split; [intros l; cbn [rl]; rewrite <- (Rl l); apply Al | intros a; reflexivity].
  - assert (Em : rm rho' = rm rho) by (apply FunctionalExtensionality.functional_extensionality; intros a; symmetry; apply Am).
    repeat split; cbn [rw rl rm]; try reflexivity; rewrite Em; [exact Rout | exact Rin | exact Rrm].
Qed.
Lemma JW_okf : ltac2:(tb__ "0|1|
S17OF_;S0OF_;M0G0SfS10Vsegs;R4R1A3S10Vsegs;R5SdR4R3R2A3A3F_;FJ;FTZ;FZn;Fok;").
Proof. intros ok Zn TZ J H rho tp tr ms md msv' (rp & HJ & _). exact (H rp tp tr ms md msv' HJ). Qed.
Lemma JW_okpf : ltac2:(tb__ "0|1|
S17OF_;S0OF_;M0G0SfS18Vsegs;R4R1A3S18Vsegs;R5SdR4R3R2A3A3F_;FJ;FTZ;FZn;Fok;").
Proof. intros ok Zn TZ J H rho tp tr ms md x8 (rp & HJ & _). exact (H rp tp tr ms md x8 HJ). Qed.
End Blind.
