(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "prod"; "option"; "Some"; "None"; "pair"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "FdEntry"; "with_fds"; "m_vmmaps"; "m_vm_lazy"; "VmMaps"; "vm_limit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "POISON_PARTIAL_A"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_frames"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_depot"; "aa_geom"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "frame_flag"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "depot_inv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition segsA : list Segment := Asan.M.loaded_segments.

Definition law_view_stmt (AInvA : AA -> valuation -> list word -> Model -> Prop) : Prop := ltac2:(tb__ "0|1|
S17S15S15S2S0Q40A1M0A1S9VAInvA;R5R4R2R1A4G0S12S4S0Q8A1A1S24S10S16R5A1R1A3S24S10S16R6A1R1A3A3Fa;VAInvA;R7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").

Theorem AInvA_view : law_view_stmt (AInvA segsA).
Proof.
  intros A rho rho' tp md HA Hrd.
  assert (E : view segsA (rm rho') = view segsA (rm rho)).
  { apply functional_extensionality. intros z.
    destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    - rewrite !view_in by lia. apply Hrd.
    - rewrite !view_out by lia. reflexivity.
    - rewrite !view_out by lia. reflexivity. }
  unfold AInvA in *. rewrite E. exact HA.
Qed.

Definition law_fds_stmt (AInvA : AA -> valuation -> list word -> Model -> Prop) : Prop := ltac2:(tb__ "0|1|
S17S15S2S0Q40A1M0A1S9S2S3G0SaA2A1VAInvA;R5R4R3R2A4VAInvA;R6R5R4SbR2R3A2A4F_;Ffds;Fmd;Ftp;Frho;FA;").

Lemma paid_with_fds : ltac2:(tb__ "0|1|
S2S3S0Q40A1M0SaA2A1S9S2G0A1S12S8S23SbR3R2A2R1A2S23R2R1A2A3Ftp;Fmd;Ffds;").
Proof. intros fds md tp. destruct md; reflexivity. Qed.
Lemma m_vmmaps_with_fds' : ltac2:(tb__ "0|0|
S2S3S0Q40A1SaA2A1S9S12SeScSbR2R1A2A1ScR1A1A3Fmd;Ffds;").
Proof. intros fds md. destruct md; reflexivity. Qed.

Lemma m_vm_lazy_with_fds' : ltac2:(tb__ "0|1|
S2S3S0Q40A1M0SaA2A1S9S12S2S3G0G0A2A1SdSbR2R1A2A1SdR1A1A3Fmd;Ffds;").
Proof. intros fds md. destruct md; reflexivity. Qed.

Theorem AInvA_fds : law_fds_stmt (AInvA segsA).
Proof.
  intros A rho tp md fds (HG & HR & HF & HRest & HM & HI3 & HB).
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [|exact (conj HI3 HB)].
  unfold model_inv, vm_geom, ledger_inv in HM |- *. rewrite paid_with_fds, m_vmmaps_with_fds', m_vm_lazy_with_fds'.
  destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  refine (conj V1 (conj V2 (conj V3 (conj V4 (conj V5 (conj V6 (conj V7 (conj L1 (conj L2 (conj L3 (conj L4 (conj _ (conj L6 (conj L7 (conj L8 L9))))))))))))))).
  eapply depot_vm_mat; [apply m_vmmaps_with_fds' | apply m_vm_lazy_with_fds' | exact L5].
Qed.

Theorem AInvA_budget : ltac2:(tb__ "0|1|
S17S15S2S0Q40A1A1S9S1fS10R4R3R2R1A5S13S20S23R2R3A2S1eR5A1A2S13S12S8SfScR2A1A1S27A3S13S20Z0M0S1bR5A1A2S13S20G0S1aR5A1A2S20G0S19R5A1A2A2A2A2A2F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (_ & _ & _ & _ & _ & HD & _). unfold depot_wf in HD.
  destruct HM as (_ & PB & VL & V0 & K0 & F0 & _ & _ & _ & _ & _ & _ & DN & PC & _).
  split; [|split; [exact VL | split; [exact V0 | split; [exact K0 | exact F0]]]].

  eapply Z.le_trans; [pose proof (prim_credit_nonneg A) as PCN; apply (Z.le_trans _ (paid md tp + prim_credit A)); [clear -PCN; lia | exact PB]|].
  apply budgetD_le_budget; [| |exact DN|exact PC|exact K0|exact F0].
  - exact (dep_cost_bound_mem _ _ HD).
  - exact (dm_F_NFBLK _ _ HD).
Qed.

Theorem AInvA_depot : ltac2:(tb__ "0|0|
S17S15S2S0Q40A1A1S9S1fS10R4R3R2R1A5S2aS10S1cR5A1R4R2R3A5F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (_ & _ & _ & _ & _ & HD & _). unfold depot_wf in HD.
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DV & _).
  split; [|exact DV].
  eapply depot_mem_frame; [|exact HD]. intros a Ha. symmetry. apply maskv_out.
  pose proof (geom_nums _ HG) as (F1 & F2 & _). rewrite FS_total_val in F2. pose proof (topG_range (aa_geom A)) as TG.
  pose proof (Sh_in_band (ag_fsb (aa_geom A) + FS_frames_off) ltac:(rewrite FS_frames_off_val; unfold IMG_HI in F1; lia)) as SB1.
  assert (SU : Sh (ag_fsb (aa_geom A) + 11571200) <= SHADOW_BAND_HI).
  { unfold Sh, SHADOW_OFF, SHADOW_BAND_HI, HIGH_SHADOW_END. pose proof (Z.div_le_upper_bound (ag_fsb (aa_geom A) + 11571200) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  destruct Ha as [Hs|[(b & Hb & Hab)|(b & Hb & Hab)]].
  - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. unfold IMG_HI in F1.
    apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_kFlagsOffset_val; [lia | lia |].
    left. unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in SB1. lia.
  - destruct HI3 as (_ & _ & _ & _ & X5 & _).
    destruct (X5 (b, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists b; split; [reflexivity | exact Hb]))
      as (DI & _ & _ & _ & SF & _). cbn [fst snd] in DI, SF. unfold sepZ in SF. cbn [fst snd] in SF.
    destruct DI as (_ & _ & _ & _ & WB). rewrite FS_total_val in SF. unfold NBSZ in *.
    apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_kFlagsOffset_val; [clear -SF Hab; lia | clear -SF Hab; lia |].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -WB Hab SB1 SU. lia.
  - destruct HI3 as (_ & _ & _ & _ & X5 & _).
    destruct (X5 (b, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b; split; [reflexivity | exact Hb]))
      as (DI & _ & _ & _ & SF & _). cbn [fst snd] in DI, SF. unfold sepZ in SF. cbn [fst snd] in SF.
    destruct DI as (_ & _ & _ & _ & WB). rewrite FS_total_val in SF. unfold FBSZ in *.
    apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_kFlagsOffset_val; [clear -SF Hab; lia | clear -SF Hab; lia |].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -WB Hab SB1 SU. lia.
Qed.

Theorem AInvA_flag : ltac2:(tb__ "0|4|
S17S15S2S0Q40M0A1A1S9S3S8S8A2M1S1fS10R5R4R3R2A5S26G1R2S18R6A1A3S12S4S0Q8M2A1M3A1S16R6S1G0S28S1dR7A1R3A2A2A2S5G3S1G2Z1A2A2A3F_;F_;Ffs;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md [f s] HA Hin. pose proof HA as (HG & HR & HF & HRest & HM).
  destruct (aa_frames_fact _ A _ _ HF Hin) as (c & pos & u & v & Hc & Hs & Eb & Hnotin & Hpos & Hf & Hnth). cbn [fst snd] in Hs, Hf.
  pose proof (fs_geom_nums (aa_geom A) c pos HG Hc Hpos) as M. cbn zeta in M.
  rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. pose proof (topG_range (aa_geom A)).
  assert (Efl : frame_flag (aa_geom A) (f, s) = fs_flags (ag_fsb (aa_geom A)) c + pos).
  { unfold frame_flag. cbn [fst snd]. unfold fs_flag_addr. rewrite Hs, fs_class_of_size_ok by lia. rewrite Hf, fs_pos_frame by lia. reflexivity. }
  rewrite Efl. destruct HF as (Flen & Fcls & Fhint & Fflags & Ffree & Fsh).
  specialize (Fflags c pos ltac:(unfold FS_NCLASSES; lia) Hpos). unfold restrictv in Fflags.
  rewrite fs_footb_true2 in Fflags by (rewrite FS_kFlagsOffset_val, FS_total_val; lia).
  rewrite (busyb_of_split A c u pos f v Eb) in Fflags.
  rewrite view_in in Fflags by lia.
  eapply rd_off_image; [lia | exact Fflags].
Qed.

Theorem AInvA_frame_shadow : ltac2:(tb__ "0|2|
S17S15S2S0Q40M0A1A1S9S8S8S8S1fS10R7R6R5R4A5S26S3S8S8A2S7S8S8R4R3A4S18R8A1A3S13S20S25R5A1R3A2S22R3S25S21R5R4A2A1A2A2S14S12S4S0Q8A1M1A1S16R9S1G0R4A2A2S6G1A1A3A1F_;F_;F_;Fz;Fs;Ff;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md f s z HA Hin Hz. pose proof HA as (HG & HR & HF & HRest & HM).
  destruct (aa_frames_fact _ A _ _ HF Hin) as (c & pos & u & v & Hc & Hs & Eb & Hnotin & Hpos & Hf & Hnth). cbn [fst snd] in Hs, Hf.
  pose proof (fs_geom_nums (aa_geom A) c pos HG Hc Hpos) as M. cbn zeta in M.
  rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. pose proof (topG_range (aa_geom A)).
  subst f s. destruct HF as (Flen & Fcls & Fhint & Fflags & Ffree & Fsh).
  rewrite FS_frames_off_val, FS_total_val in Fsh.
  assert (R1 : Sh (ag_fsb (aa_geom A) + 36864) <= Sh (fs_frame (ag_fsb (aa_geom A)) c pos)) by (apply Sh_mono; lia).
  assert (R2 : Sh (fs_frame (ag_fsb (aa_geom A)) c pos + fs_frame_size c) <= Sh (ag_fsb (aa_geom A) + 11571200)) by (apply Sh_mono; lia).
  assert (R : Sh (ag_fsb (aa_geom A) + 36864) <= z < Sh (ag_fsb (aa_geom A) + 11571200)) by lia.
  destruct (Fsh z R) as [b Hb]. unfold restrictv in Hb.
  rewrite fs_footb_true3 in Hb by (rewrite FS_frames_off_val, FS_total_val; exact R).
  rewrite view_in in Hb by (unfold Sh, SHADOW_OFF in *; lia).
  rewrite (rd_off_image (rm rho) z b ltac:(unfold Sh, SHADOW_OFF in *; lia) Hb). discriminate.
Qed.

Definition POISON_PARTIAL_A : Z := 0xeec4d.
Theorem AInvA_poison_partial : ltac2:(tb__ "0|2|
S17S15S2S0Q40A1A1S9S1fS10R4R3R2R1A5S12S4S0Q8M0A1M1A1S29S10S16R4A1S11A3S5G1S1G0Z1A2A2A3F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (_ & _ & _ & _ & _ & _ & _ & _ & (HX & _)).
  unfold rtc_extra in HX. apply Forall_inv_tail in HX. apply Forall_inv in HX.
  specialize (HX 0%nat ltac:(cbn; lia)). cbn [c_addr c_w c_val Z.of_nat] in HX. rewrite Z.add_0_r in HX.
  rewrite maskv_out in HX.
  - exact HX.
  - pose proof (geom_nums _ HG) as (F1 & F2 & _). rewrite FS_total_val in F2. pose proof (topG_range (aa_geom A)) as TG.
    pose proof (Sh_in_band (ag_fsb (aa_geom A) + FS_frames_off) ltac:(rewrite FS_frames_off_val; unfold IMG_HI in F1; lia)) as SB1.
    unfold IMG_HI in F1.
    apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_kFlagsOffset_val; [lia | lia |].
    left. unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in SB1. lia.
Qed.
