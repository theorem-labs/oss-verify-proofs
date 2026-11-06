(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From Stdlib Require Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Madvise.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7 F0A_hbN_leaf dq.

(* [comment removed for export] *)
Module F0A_hbN_skel.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sv"; "eval"; "sobj"; "agree_below"; "obj_range"; "ranges_disjoint"; "rm"; "ss_next"; "ss_objs"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dn.F0A_hbN_skel.Skel"; "JH1"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "true"; "bool"; "prod"; "false"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dn.F0A_hbN_skel"; "KEEPXh"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "modulo"; "pow"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "VSXh"; "hv_C5"; "hv_EMd"; "hv_EUd"; "VS0h"; "hbfam_ok"; "hbvar_ok"; "hf_LA"; "hf_S0"; "hf_SC"; "hv_E5"; "hv_EMx"; "hv_EUs"; "hv_EUx"; "hv_LR"; "hv_PT"; "hv_SX"; "hv_XF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "Model"; "TASK_SIZE"; "event"; "map_has"; "map_remove"; "page_size"; "region_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "shadow_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "keepsM"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MadviseA"; "madvise_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states"; "vMS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail"; "ELEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_sh_zone"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA SysCallA MmapFixedA MmapNodesA MunmapSymA MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11.
Import ListNotations.
Open Scope Z_scope.

Definition KEEPXh (rS r : valuation) : Prop := ltac2:(tb__ "0|0|
S1eS27S1eR1S28A3ScS13Q40A1S1Vr;R2A2S1VrS;R2A2A3F_;Fv;").

Section Skel.
Context {Q : assn} (X : trk Q).
Variable nW : nat.
Variables (A' : AA) (Kc : KcA) (rho1' : valuation).
Variables (ch : sec_chunk) (f : nat) (l : bool).
Variable TZ : Z -> Prop.
Variables (E : axst) (cf : hbfam) (cv : hbvar).
Hypothesis FOK : ltac2:(tb__ "0|0|
S2dVE;Vf;Vcf;A3").
Hypothesis VOK : ltac2:(tb__ "0|0|
S2eS31Vcf;A1Vf;Vl;Vcv;A4").
Definition JH1 : jpredA := ltac2:(tb__ "0|0|
S56S10S5bVch;A1VTZ;S57VnW;S58S1bVA';VKc;Vrho1';A6A4").
Variables (JP JH2 : jpredA).
Hypothesis HJ1 : JOK X JH1.
Hypothesis HJP : JOK X JP.
Hypothesis HJ2 : JOK X JH2.
Variables (ENV0 ENVX : valuation -> Prop).
Hypothesis ENV0_keep : ltac2:(tb__ "0|0|
S0S0VENV0;R2A1S49S48S2cA1R3R2A3VENV0;R3A1F_;F_;Fr';Fr;").
Hypothesis ENVX_keep : ltac2:(tb__ "0|0|
S0S0VENVX;R2A1S21R3R2A2VENVX;R3A1F_;F_;Fr';Fr;").
Variables (nlitM nlitU : Z).
Variables (rhoE : valuation) (tpE : list word).

Hypothesis G_entry : ltac2:(tb__ "0|0|
S20S11S10S12VE;VrhoE;VtpE;R1A6SdS0S0SbS11S10S12S30Vcf;A1R1VtpE;R3A6VENV0;R1A1A2Lr2;A2F_;Fw;").
Hypothesis G_scan : ltac2:(tb__ "0|0|
S16S13Q40A1A1S0VENVX;R1A1S3aVQ;VX;S11S10S12S38Vcv;A1R2R3A5A3F_;Fr4;S0VENV0;R1A1S3aVQ;VX;S11S10S12S2fVcf;A1R2R4A5A3F_;Fr;F_;Ftp;").
Hypothesis G_c5 : ltac2:(tb__ "0|0|
S0S16S13Q40A1A1S20VENVX;R3A1S11S10S12S32Vcv;A1R4R3R2A6S11S10S12S29Vcv;A1R5R4R3A6F_;F_;Fw;Ftp;Fr;").
Hypothesis G_eus : ltac2:(tb__ "0|0|
S0S16S13Q40A1A1S20VENVX;R3A1S11S10S12S34Vcv;A1R4R3R2A6SeF_;F_;Fw;Ftp;Fr;").
Hypothesis G_shd : ltac2:(tb__ "0|1|
S0S16S13Q40A1M0A1S20VENVX;R3A1S11S10S12S33Vcv;A1R4R3R2A6SdS0S0SbS11S10S12S2aVcv;A1R1R5R4A6S1eScG0S1R2R1A2S1R7R1A2A3Fv;A2Lr2;A2F_;F_;Fw;Ftp;Fr;").
Hypothesis G_madv_num : ltac2:(tb__ "0|1|
S0VENVX;R1A1SbScS1fS14Q40S3R2S5aA2A2VnlitM;A3SbScS1fS25VnlitM;Z1000A2Z0M0A3SbS22G0VnlitM;A2S22VnlitM;S26Z2Z3eA2A2A2A2A2F_;Fr;").
Hypothesis G_madv_pre : ltac2:(tb__ "0|1|
S0S16S13Q40A1M0A1VENVX;R2A1S53S10S12S12S2aVcv;A1R3R2G0S18L_;VnlitM;A8F_;Ftp;Fr;").
Hypothesis G_du : ltac2:(tb__ "0|1|
S0S16S13Q40A1M0A1S20VENVX;R3A1S11S10S12S35Vcv;A1R4R3R2A6SdS0S0SbS11S10VJP;S2bVcv;A1R1R5R4A6S1eScG0S1R2R1A2S1R7R1A2A3Fv;A2Lr2;A2F_;F_;Fw;Ftp;Fr;").
Hypothesis G_mun_num : ltac2:(tb__ "0|2|
S0VENVX;R1A1SbScS13Q40M0A1S3R2S59A2S15G0VnlitU;A2A3SbScS1fS25VnlitU;Z1000A2Z0M1A3SbS22G1VnlitU;A2S22VnlitU;S26Z2Z3eA2A2A2A2A2F_;Fr;").
Hypothesis G_mun_pre : ltac2:(tb__ "0|d|
S0S16S13Q40M0A1M1A1VENVX;R2A1S16S3fA1M2S4cS3dS55S10R6R5S2bVcv;A1M3S17G2S4eR3S4fR2R1A2A4A5VJP;R7R6R4R2A4S4dR4U0A2G1SbScS1fS25S14G0R1A2M4S42A2Z0A3SbS24S23G4VnlitU;A2M5S3eA2SbScS19S40S3cS3bR4A1A1M6R1S15G0VnlitU;A2M7A3S18A3SbG1S27S1aG1G1A2S17G1G1R2R1A4S3cS3bR5A1A1A3ScG1R2G7A3F_;Fs;SbScS19S43S41G6R1A2R1G7A3S18A3SbS4S27S4R1SaS44G3A1A1A3S7S6RbR2A2S17S1fS1fS14G0R3A2M8S23G8VnlitU;A2A4A2F_;Fo;SbS1aS2S2A2M9S1fS27G9R2S45G3A1A3SbS24S14G0S3RcS1cS2S2R3A3A2A2MaR2A2S22R2S23GaS14G0S3RcS1dS2S2R3A3A2A2A2A2A2SfSbS24S14G0R5A2MbS14G0S47S14G0S3RdS46G3A1A2A2R3A2A2McA2S22GcS23GbVnlitU;A2A2A2A1F_;F_;Fy;Frr;VJH2;S52R9S51S8R9A1R1G7A3A2S54G4G5R8A3R6S50R4R1G7A3A4A2A2A2A2A2A2A2Ta;F_;F_;Fmd;Fms;Ftr;F_;Ftp;Fr;").
Hypothesis G_qsz : ltac2:(tb__ "0|0|
S0S16S13Q40A1A1S20VENVX;R3A1S11S10VJH2;S36Vcv;A1R4R3R2A6S11S10VJH2;S37Vcv;A1R5R4R3A6F_;F_;Fw;Ftp;Fr;").
Hypothesis G_exit : ltac2:(tb__ "0|0|
S0S16S13Q40A1A1S20VENVX;R3A1S11S10VJH2;S39Vcv;A1R4R3R2A6VQ;R3A1F_;F_;Fw;Ftp;Fr;").

Lemma KEEPXh_refl : ltac2:(tb__ "0|0|
S0S21R1R1A2Fr;"). Proof. intros r v _. reflexivity. Qed.
Lemma KEEPXh_trans : ltac2:(tb__ "0|1|
S0S0S0S21R3R2A2M0G0S21R5R3A2F_;F_;Fr3;Fr2;Fr1;"). Proof. intros r1 r2 r3 H1 H2 v Hv. rewrite (H2 v Hv). exact (H1 v Hv). Qed.
Lemma KEEPXh_keepsM : ltac2:(tb__ "0|0|
S0S0S49S48S28A1R2R1A3S21R3R2A2F_;Fr';Fr;").
Proof. intros r r' [_ HM] v Hv. apply (HM v (SVar v)). unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv]. Qed.
Lemma VSXh_lt : ltac2:(tb__ "0|0|
S1eS27S1eR1S28A3S4bR2PcfA2F_;Fv;").
Proof. intros v Hv. unfold VSXh, VS0h in Hv. cbn in Hv. repeat (destruct Hv as [<-|Hv]; [reflexivity|]). destruct Hv. Qed.
Lemma KEEPXh_agree : ltac2:(tb__ "0|0|
S1eS0S0S5R3R2R1A3S4aPcfR4A2S21R4R3A2F_;F_;Fr';Fr;Fk;").
Proof. intros k r r' (Hw & _) Hk v Hv. symmetry. apply Hw. pose proof (VSXh_lt v Hv). lia. Qed.
Lemma KEEPXh_same : ltac2:(tb__ "0|0|
S0S0S1eScS13Q40A1S1R2R1A2S1R3R1A2A3Fv;S21R3R2A2F_;Fr';Fr;"). Proof. intros r r' H v _. apply H. Qed.
Hypothesis C5_next207 : ltac2:(tb__ "0|0|
S4aPcfS9S44S29Vcv;A1A1A1A2").

Theorem hb_skeleton : ltac2:(tb__ "0|0|
S3aVQ;VX;S11S10S12VE;VrhoE;VtpE;A5A3").
Proof.
  apply (tr_glue X _ JH1 (hf_S0 cf) tpE ENV0 G_entry). intros r2 EN2.
  apply (seg_PA X E f cf FOK JH1 r2 tpE HJ1). intros r3 K3.
  apply (G_scan tpE); [|exact (ENV0_keep r2 r3 EN2 K3)]. intros rS ENS.

  apply (seg_PB X _ f l cv VOK JH1 rS tpE HJ1). intros r1 K1. pose proof (ENVX_keep _ _ ENS (KEEPXh_keepsM _ _ K1)) as EN1.
  apply (tr_conseq X _ (SPA segsA JH1 (hv_C5 cv) r1 tpE)); [intros w Hw; exact (G_c5 r1 tpE w EN1 Hw)|].
  apply (seg_memset X _ f l cv VOK JH1 r1 tpE HJ1). intros r2' Hag. pose proof (ENVX_keep _ _ EN1 (KEEPXh_agree _ _ _ Hag C5_next207)) as EN2'.
  apply (seg_PC X _ f l cv VOK JH1 r2' tpE HJ1).
  { intros r3' K3'. apply (tr_pure X _ False); [|intros []]. intros w Hw. exact (G_eus r3' tpE w (ENVX_keep _ _ EN2' (KEEPXh_keepsM _ _ K3')) Hw). }
  intros r3' K3'. pose proof (ENVX_keep _ _ EN2' (KEEPXh_keepsM _ _ K3')) as EN3'.

  apply (tr_conseq X _ (SPA segsA JH1 (hv_EMx cv) r3' tpE)); [intros w Hw; exact (SPA_axforms segsA JH1 _ r3' _ _ tpE w (v_EMx _ f l cv VOK) Hw)|].
  apply (tr_glue X _ JH1 (hv_EMd cv) tpE ENVX).
  { intros w Hw. destruct (G_shd r3' tpE w EN3' Hw) as (r4 & H4 & RW4). exists r4. split; [exact H4 | exact (ENVX_keep _ _ EN3' (KEEPXh_same _ _ RW4))]. }
  intros r4 EN4. destruct (G_madv_num r4 EN4) as (NM1 & NM2 & NM3).
  pose proof (v_EMdnode _ f l cv VOK) as (N1 & N2 & N3 & N4 & N5 & N6 & N7). apply Pos.leb_le in N7.
  apply (tr_madvise X JH1 JH1 (hv_EMd cv) r4 tpE (fun _ => true) EBEG ELEN nlitM HJ1 N7 N1 N2 N3 N4 NM1 NM2 NM3 N5 (G_madv_pre r4 tpE EN4)).
  unfold madvise_post. rewrite (v_AM _ f l cv VOK). set (r5 := set_rm r4 _). set (tp5 := tp_dontneed _ _ _ tpE).
  assert (EN5 : ENVX r5) by (apply (ENVX_keep _ _ EN4); apply KEEPXh_same; intros v; reflexivity).
  apply (seg_PD X _ f l cv VOK JH1 r5 tp5 HJ1). intros r6 K6. pose proof (ENVX_keep _ _ EN5 (KEEPXh_keepsM _ _ K6)) as EN6.

  apply (tr_conseq X _ (SPA segsA JH1 (hv_EUx cv) r6 tp5)); [intros w Hw; exact (SPA_axforms segsA JH1 _ r6 _ _ tp5 w (v_EUx _ f l cv VOK) Hw)|].
  apply (tr_glue X _ JP (hv_EUd cv) tp5 ENVX).
  { intros w Hw. destruct (G_du r6 tp5 w EN6 Hw) as (r7 & H7 & RW7). exists r7. split; [exact H7 | exact (ENVX_keep _ _ EN6 (KEEPXh_same _ _ RW7))]. }
  intros r7 EN7. destruct (G_mun_num r7 EN7) as (NU1 & NU2 & NU3).
  pose proof (v_EUdnode _ f l cv VOK) as (U1 & U2 & U3 & U4 & U5 & U6). apply Pos.leb_le in U6.
  apply (tr_munmap X JP JH2 (hv_EUd cv) r7 tp5 vH vMS nlitU HJP U6 U1 U2 U3 U4 NU1 NU2 NU3 (G_mun_pre r7 tp5 EN7)).
  rewrite (v_AU _ f l cv VOK). set (r8 := set_rm r7 _). set (tp8 := tp_forget _ _ tp5).
  assert (EN8 : ENVX r8) by (apply (ENVX_keep _ _ EN7); apply KEEPXh_same; intros v; reflexivity).

  apply (seg_PE X _ f l cv VOK JH2 r8 tp8 HJ2). intros r9 K9. pose proof (ENVX_keep _ _ EN8 (KEEPXh_keepsM _ _ K9)) as EN9.
  apply (tr_conseq X _ (SPA segsA JH2 (hv_PT cv) r9 tp8)); [intros w Hw; exact (G_qsz r9 tp8 w EN9 Hw)|].
  apply (seg_PT X _ f l cv VOK JH2 r9 tp8 HJ2). intros r10 K10.
  apply (tr_done X). intros w Hw. exact (G_exit r10 tp8 w (ENVX_keep _ _ EN9 (KEEPXh_keepsM _ _ K10)) Hw).
Qed.
End Skel.
End F0A_hbN_skel.

(* [comment removed for export] *)
Module F0A_hbN_madv.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sobj"; "valuation"; "eval"; "obj_range"; "ranges_disjoint"; "reg_sv"; "ss_objs"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "aa_geom"; "ag_spacebeg"; "aa_sec"; "ag_ctx"; "ag_thread"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_tail"; "TPIN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail"; "MB"; "EBEG"; "ELEN"; "ME"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_sh_zone"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "modulo"; "pow"; "sub"; "@Corelib.Init.Datatypes"; "Some"; "false"; "list"; "option"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MadviseA"; "madvise_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue"; "fam_ok"; "@Stdlib.Lists.List"; "In"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import PaidMunmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SysCallA MmapA MmapFixedA MmapFixedA2 MmapNodesA MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_env.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_tail.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section MadvPre.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (rho1 : valuation) (i : nat) (ch : sec_chunk) (f : nat) (TZ : Z -> Prop).
Hypothesis HZT : ltac2:(tb__ "0|0|
S2S1cVch;R1A2VTZ;R2A1F_;Fz;").
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Let JH : jpredA := ltac2:(tb__ "0|0|
S29S17S1cVch;A1VTZ;S2aVnW;S2bS23VA;VKc;Vrho1;A6A4").
Hypothesis HI : ltac2:(tb__ "0|0|
S0S25ScA1S2eScSfVA;A1Vi;A3S22ScVch;A2A3").
Hypothesis CH : CHFh ch.
Hypothesis HFAM : ltac2:(tb__ "0|0|
S2cVf;SeSdVA;A1A1Vh;Vmsz;A4").
Hypothesis HPIN : ltac2:(tb__ "0|3|
S1S0S13Q40M0A1M1S3Vrho1;P97A2S12G0S11SdVA;A1M2A1A2A3S1S0G1S3Vrho1;P98A2S12G0S10G2A1A2A3S0G1S3Vrho1;P9bA2S12G0SeG2A1A2A3A2A2").
Variable EMd : axst.
Hypothesis NA0 : ltac2:(tb__ "0|0|
S0SbS9S15VEMd;A1ZaA2S19A3").
Hypothesis NAX : ax_X EMd = [].
Let nlit : Z := ltac2:(tb__ "0|0|
S21S1bVh;Vmsz;A2S18Vh;A1A2").

Lemma madv_num : ltac2:(tb__ "0|1|
S5S16Vch;R1A2S1S0S2S14Q40S6R2S1aA2A2Vnlit;A3S1S0S2S1fVnlit;Z1000A2Z0M0A3S1S1dG0Vnlit;A2S1dVnlit;S20Z2Z3eA2A2A2A2A2F_;Fr;").
Proof.
  intros r (EH & EM). destruct CH as (CH1 & CH2 & CH3 & CH4 & CH5). fold h msz in CH1, CH2, CH3, CH4, CH5.
  destruct (mrange_facts h msz ltac:(lia) CH1 CH2 CH3) as (M1 & M2 & M3 & M4 & M5). fold nlit in M5.
  assert (EB : eval r EBEG = Z_to_bv 64 (MB h)) by (apply eval_EBEG; [unfold vH; cbn [eval]; exact EH | lia]).
  assert (EE : eval r EEND = Z_to_bv 64 (ME h msz)) by (apply eval_EEND; [unfold vH; cbn [eval]; exact EH | unfold vMS; cbn [eval]; exact EM | lia | lia | lia]).
  pose proof (Z.div_pos msz 8 ltac:(lia) ltac:(lia)) as MD0. pose proof (Z.div_lt_upper_bound msz 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as MD1.
  pose proof (Sh_in_band h ltac:(lia)) as SB1. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in SB1.
  assert (SHE : Sh (h + msz) = Sh h + msz / 8) by (apply Sh_add8; [exact (mod8_of_4096 _ CH1) | exact (mod8_of_4096 _ CH2)]).
  split; [|split; [exact M5 | unfold nlit; lia]].
  unfold ELEN. rewrite (U_sub r _ _ (ME h msz) (MB h) EE EB ltac:(lia) ltac:(lia)). unfold nlit. apply Z.mod_small. lia.
Qed.

Lemma madv_pre : ltac2:(tb__ "0|2|
S5S24S13Q40A1M0A1S16Vch;R2A2S4S2dS4R1SaS15VEMd;A1A1A3S8S7R5R2A2S26S2S2S18Vh;A1M1S1eG1Vnlit;A2A4A2F_;Fo;S28S17VJH;VJH;VEMd;R4R3G0S27L_;Vnlit;A8F_;F_;Ftp;Fr;").
Proof.
  intros r tp (EH & EM) DISJ. unfold madvise_pre. intros tr ms md Hsp HJ. cbv zeta.
  destruct CH as (CH1 & CH2 & CH3 & CH4 & CH5). fold h msz in CH1, CH2, CH3, CH4, CH5. destruct HPIN as (P151 & P152 & P155).
  destruct (mrange_facts h msz ltac:(lia) CH1 CH2 CH3) as (M1 & M2 & M3 & M4 & M5). fold nlit in M5.
  assert (EB : eval r EBEG = Z_to_bv 64 (MB h)) by (apply eval_EBEG; [unfold vH; cbn [eval]; exact EH | lia]).
  pose proof (Z.div_pos msz 8 ltac:(lia) ltac:(lia)) as MD0. pose proof (Z.div_lt_upper_bound msz 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as MD1.
  pose proof (Sh_in_band h ltac:(lia)) as SB1. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in SB1.
  assert (SHE : Sh (h + msz) = Sh h + msz / 8) by (apply Sh_add8; [exact (mod8_of_4096 _ CH1) | exact (mod8_of_4096 _ CH2)]).
  destruct (pending_argsA segsA r tp EMd tr ms md Hsp) as (G0 & _). rewrite NA0, EB in G0. rewrite G0. rewrite (u64_lit (MB h)) by lia.
  rewrite tp_dontneed_keep.
  destruct HJ as (rp & (Hag & HA & HUW & HLV & HK & Htp & HBD & Htop) & (BW & BL & BOUT & BIN & BRM)).

  set (rpK := rho_sets rp [(156%positive, Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize))]).
  assert (ERM : rm rpK = rm rp) by (unfold rpK; apply rm_rho_sets).
  assert (OTH : forall v, v <> 156%positive -> rw rpK v = rw rp v) by (intros v Hv; unfold rpK; rewrite rho_sets_other; [reflexivity | cbn; intros [E|[]]; congruence]).
  assert (RP : forall v, (v < GW)%positive -> rw rp v = rw rho1 v) by (intros v Hv; symmetry; exact (proj1 Hag v Hv)).
  assert (HK0 : K0 Kc A rpK tp tr md).
  { split; [|split; [exact HK|split; [|split]]].
    - pose proof (AInvA_Q A rp tp md HA) as HQ. unfold AInvQ in *. rewrite ERM. exact HQ.
    - unfold tp_ok in *. rewrite OTH by discriminate. exact Htp.
    - unfold top_high in *. unfold V_DEPTH in *. rewrite !OTH by discriminate. exact Htop.
    - unfold rigidQ. rewrite !OTH by discriminate. rewrite !RP by (unfold GW; lia). split; [exact P151|]. split; [exact P152|]. split; [exact P155|].
      unfold rpK. apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]. }
  destruct (kq_facts segsA (K0 Kc) (K0_laws Kc HKc) A rpK tp _ _ HK0) as [HG _ _ _ _ _ _ _ _ _ _ _ _].
  pose proof (geom_old _ HG) as GO. destruct GO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSB & _).
  assert (FSH : (LOW_SHADOW_BEG <= Sh h /\ Sh h + msz / 8 <= SHADOW_GAP_BEG) \/ (HIGH_SHADOW_BEG <= Sh h /\ Sh h + msz / 8 <= HIGH_SHADOW_END)).
  { rewrite <- SHE. unfold Sh, SHADOW_OFF, LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END in *.
    pose proof (Z.div_pos h 8 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound (h + msz) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as D1.
    destruct f as [|[|f']]; cbn [fam_ok] in HFAM.
    - left. pose proof (Z.div_le_upper_bound (h + msz) 8 268430848 ltac:(lia) ltac:(lia)). lia.
    - right. pose proof (Z.div_le_lower_bound h 8 2199291686912 ltac:(lia) ltac:(lia)). lia.
    - right. pose proof (Z.div_le_lower_bound h 8 2199291686912 ltac:(lia) ltac:(lia)). lia. }
  destruct (ks_madvise_ok segsA (K0 Kc) (K0_sec Kc HKc) A rpK tp tr md HK0 (Z_to_bv 64 (MB h)) nlit) as [GATE LAZY].
  { rewrite u64_lit by lia. unfold PG. exact M1. } { unfold PG. exact M5. } { unfold nlit. lia. }
  { rewrite u64_lit by lia. unfold nlit. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END in *. lia. }
  rewrite (u64_lit (MB h)) in LAZY by lia.
  split; [unfold page_size; exact M1|]. split; [unfold nlit; lia|]. split; [exact GATE|]. split; [exact LAZY|]. split; [exact DISJ|].
  split; [intros rr y Hin; rewrite NAX in Hin; destruct Hin|].

  set (aw := Z_to_bv 64 (MB h)). set (nw := Z_to_bv 64 nlit).
  set (r4 := set_rm r (splice (rm r) (rereserve_bytes tp) aw nw)). set (v2 := view segsA (rm r)). set (v4 := view segsA (rm r4)).
  assert (INR : forall z, 0 <= z < 2 ^ 64 -> SysStep.in_range aw nw (Z_to_bv 64 z) = true <-> MB h <= z < MB h + nlit).
  { intros z Hz. rewrite SysStep.in_range_spec. unfold aw, nw. rewrite !u64_lit by (unfold nlit; lia). tauto. }
  assert (PAID : forall z, MB h <= z < MB h + nlit -> rm r (Z_to_bv 64 z) <> None -> page_mem (page_base (Z_to_bv 64 z)) tp = true).
  { intros z Hz Hd. destruct (smatch_pendingA_mem segsA r tp EMd tr ms md Hsp) as (_ & _ & HMF).
    assert (OUT : outside_all r (ss_objs (ax_S EMd)) (Z_to_bv 64 z)).
    { apply Forall_forall. intros o Ho. pose proof (DISJ o Ho) as D. unfold SymState.ranges_disjoint in D. cbn [fst snd] in D. cbv zeta. rewrite u64_lit by (unfold nlit in Hz; lia). lia. }
    pose proof (HMF _ OUT) as E. rewrite vms_mem in E. pose proof (LAZY (Z_to_bv 64 z) ltac:(rewrite u64_lit by (unfold nlit in Hz; lia); exact Hz)) as LZ.
    unfold hid in E. rewrite LZ in E. cbn [andb] in E. destruct (page_mem (page_base (Z_to_bv 64 z)) tp); [reflexivity|]. cbn [negb] in E. exfalso. apply Hd. rewrite <- E. reflexivity. }
  pose proof (ks_repr segsA (K0 Kc) (K0_sec Kc HKc) A rpK tp tr md HK0) as (SC1 & _). rewrite ERM in SC1.
  destruct (SC1 i ch HI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PSH). fold h msz in PSH. rewrite SHE in PSH.
  assert (INSH : forall z, MB h <= z < MB h + nlit -> chunk_sh_zone ch z) by (intros z Hz; unfold chunk_sh_zone; fold h msz; rewrite SHE; unfold nlit in Hz; lia).
  assert (PSH2 : forall z, MB h <= z < MB h + nlit -> exists b, v2 z = Some b).
  { intros z Hz. destruct (PSH z ltac:(unfold nlit in Hz; lia)) as [b Hb]. pose proof (BIN z (INSH z Hz) ltac:(rewrite Hb; discriminate)) as X. unfold v2. destruct (view segsA (rm r) z) as [b2|]; [eexists; reflexivity | exfalso; apply X; reflexivity]. }
  assert (V4IN : forall z, MB h <= z < MB h + nlit -> v4 z = Some (Z_to_bv 8 0)).
  { intros z Hz. assert (Hz' : 0 <= z < 2 ^ 64) by (unfold nlit in Hz; lia). destruct (PSH2 z Hz) as [b Hb]. unfold v2 in Hb. rewrite view_in in Hb by lia.
    pose proof (rd_off_image (rm r) z b ltac:(lia) Hb) as Hm.
    unfold v4, r4. rewrite view_in by lia. unfold rd_of. cbn [rm set_rm]. unfold splice. rewrite (proj2 (INR z Hz') Hz). unfold rereserve_bytes.
    rewrite (PAID z Hz ltac:(rewrite Hm; discriminate)). reflexivity. }
  assert (V4OUT : forall z, ~ (MB h <= z < MB h + nlit) -> v4 z = v2 z).
  { intros z NZ. unfold v4, v2. apply view_agree. intros Hz. unfold r4. cbn [rm set_rm]. unfold splice.
    destruct (SysStep.in_range aw nw (Z_to_bv 64 z)) eqn:EI; [exfalso; exact (NZ (proj1 (INR z Hz) EI)) | reflexivity]. }
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  pose proof (JF_stable nW UStopLe false A Kc rho1 (stopJ_stable_le _) HKc) as HST.
  exists rp. split.
  - apply (HST rp rp tp tr md (madvise_dontneed_next md aw nw)); [split; [intros v0 _; reflexivity | split; [intros l0; reflexivity | intros x; reflexivity]] | | exact (conj Hag (conj HA (conj HUW (conj HLV (conj HK (conj Htp (conj HBD Htop)))))))].
    apply (mat_equiv_dontneed segsA md tp aw nw HMI). intros x Hx. apply LAZY. unfold aw, nw in Hx. rewrite !u64_lit in Hx by (unfold nlit; lia). exact Hx.
  - split; [intros v0; cbn [rw set_rm]; exact (BW v0)|]. split; [intros l0; cbn [rl set_rm]; exact (BL l0)|]. split.
    + intros z NZ. change (v4 z = view segsA (rm rp) z). rewrite V4OUT by (intros Hz; exact (NZ (INSH z Hz))). exact (BOUT z NZ).
    + split.
      * intros z HZ Hp. change (v4 z <> None). destruct (Z_le_dec (MB h) z) as [L1|L1]; [destruct (Z_lt_dec z (MB h + nlit)) as [L2|L2]|];
          [rewrite (V4IN z (conj L1 L2)); discriminate | rewrite V4OUT by lia; exact (BIN z HZ Hp) | rewrite V4OUT by lia; exact (BIN z HZ Hp)].
      * intros a0 NT. rewrite <- (BRM a0 NT). unfold r4. cbn [rm set_rm]. unfold splice.
        destruct (SysStep.in_range aw nw a0) eqn:EI; [|reflexivity]. exfalso. apply NT. apply HZT. apply INSH.
        pose proof (bv_unsigned_in_range _ a0) as RA. change (bv_modulus 64) with (2 ^ 64) in RA.
        apply (INR (bv_unsigned a0) RA). rewrite Z_to_bv_bv_unsigned. exact EI.
Qed.
End MadvPre.
End F0A_hbN_madv.

(* [comment removed for export] *)
Module F0A_hbN_nodes.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "proj1"; "conj"; "proj2"; "iff"; "not"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv_unsigned"; "bv"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "eval"; "valuation"; "sobj"; "obj_range"; "ranges_disjoint"; "rm"; "ss_objs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "div"; "pow"; "sub"; "mul"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "sc_map_beg"; "aa_geom"; "sc_map_size"; "aa_sec"; "ag_spacebeg"; "ag_ctx"; "ag_thread"; "aa_live"; "ag_pab"; "sc_size"; "@Corelib.Init.Datatypes"; "bool"; "list"; "pair"; "true"; "length"; "prod"; "Some"; "false"; "option"; "app"; "cons"; "fst"; "nat"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "Model"; "TASK_SIZE"; "event"; "map_has"; "map_remove"; "page_size"; "region_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayReserve"; "PG"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "round_up"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail"; "MB"; "ME"; "ELEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_sh_zone"; "chunk_zone"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MadviseA"; "madvise_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "shadow_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "hbvar_ok"; "hf_SC"; "hv_EMd"; "hv_EUd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.da.F0A_hbN_disj"; "hbdisj_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.F0A_hbN_scan"; "ENVXs"; "hbnums"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap"; "JH2"; "JPh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue"; "fam_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states"; "vMS"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SysCallA MmapFixedA MmapNodesA MunmapSymA MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_env F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require da.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_hbN_step OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_hbN_stepU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_scand OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.F0A_hbN_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.da.F0A_hbN_disj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dn.F0A_hbN_madv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Nodes.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (rho1 : valuation) (l1 l2 : list (Z * Z)) (p n : Z) (i : nat) (ch lst : sec_chunk) (f : nat) (l : bool) (TZ : Z -> Prop).
Variables (cf : hbfam) (cv : hbvar).
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Hypothesis HLV : ltac2:(tb__ "0|1|
S0S2aS2eSbSbA2M0A1S26VA;A1S32G0Vl1;S33G0S2bSbSbVp;Vn;A4Vl2;A3A3A3").
Hypothesis HPR : is_primary n = false.
Hypothesis HI : ltac2:(tb__ "0|0|
S0S31S1eA1S3aS1eS22VA;A1Vi;A3S2fS1eVch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S0SbVp;S15S15S1fVch;A1S46A2Z800A2A3").
Hypothesis HSZ : ltac2:(tb__ "0|0|
S0SbS28Vch;A1S15S49Vn;Z8A2Z1000A2A3").
Hypothesis HN : 1 <= n.
Hypothesis HNB : ltac2:(tb__ "0|0|
S16S15Z1800S38Vn;A1A2S21Vch;A1A2").
Hypothesis Hf : (f <= 2)%nat.
Hypothesis HFAM : ltac2:(tb__ "0|0|
S69Vf;S23S20VA;A1A1S1fVch;A1S21Vch;A1A4").
Hypothesis Hl : ltac2:(tb__ "0|1|
S0S31S1eA1S3aS1eS22VA;A1M0S3bS2dS1eG0A2U1A2A3S2fS1eVlst;A2A3").
Hypothesis HLI : ltac2:(tb__ "0|0|
S6S0S29Vl;S2cA3S0S35Vi;S3bS2dS1eS22VA;A1A2U1A2A3A2").
Hypothesis CH : CHFh ch.
Hypothesis BND : ltac2:(tb__ "0|1|
S2S16S15S1fVch;A1M0S21Vch;A1A2S48A2S16S47G0A2A2").
Hypothesis LSTOFF : ltac2:(tb__ "0|2|
S0S29Vl;S30A3S2S16S15S1fVlst;A1M0Z20A2S1fVch;A1M1A2S16S15G1S21Vch;A1A2G0A2A2F_;").
Hypothesis PABOFF : ltac2:(tb__ "0|2|
S2S16S15S27S20VA;A1A1M0S45A2S1fVch;A1M1A2S16S15G1S21Vch;A1A2G0A2A2").
Hypothesis NCB : ltac2:(tb__ "0|0|
S16S1cZ8S1dS2dS1eS22VA;A1A2A1A2S45A2").
Hypothesis HPIN : ltac2:(tb__ "0|4|
S1S0SaQ40M0A1M1ScVrho1;P97A2S8G0S25S20VA;A1M2A1A2A3S1S0G1ScVrho1;P98A2S8G0S24G2A1A2A3S1S0G1ScVrho1;P9bA2S8G0S23G2A1A2A3S1S0G1ScVrho1;PcA2S8G0Vp;A2A3S1S0G1ScVrho1;P69A2S8G0S38Vn;A1M3A2A3S0G1ScVrho1;P6aA2S8G0S19G3Z8A2A2A3A2A2A2A2A2").
Hypothesis HNUM : ltac2:(tb__ "0|0|
S64VA;Vp;Vn;Vi;Vch;A5").
Hypothesis F1 : FCH1 nW rho1.
Hypothesis SF : hbscanF_ok nW cf.
Hypothesis VOK : ltac2:(tb__ "0|0|
S5eS5fVcf;A1Vf;Vl;Vcv;A4").
Hypothesis DJ : ltac2:(tb__ "0|0|
S62VnW;Vl;Vcv;A3").
Hypothesis HZT_sh : ltac2:(tb__ "0|0|
SbS4dVch;R1A2VTZ;R2A1F_;Fz;").
Hypothesis HZTc : ltac2:(tb__ "0|0|
SbS4eVch;R1A2VTZ;R2A1F_;Fz;").
Let JH1 : jpredA := ltac2:(tb__ "0|0|
S5dS37S4dVch;A1VTZ;S67VnW;S68S30VA;VKc;Vrho1;A6A4").
Let JP : jpredA := ltac2:(tb__ "0|0|
S66VnW;VKc;VA;Vrho1;Vi;Vch;Vlst;Vl;VTZ;A9").
Let J2 : jpredA := ltac2:(tb__ "0|0|
S65VKc;VA;Vrho1;Vl1;Vl2;Vi;Vch;VTZ;A8").
Let ENVX : valuation -> Prop := ltac2:(tb__ "0|0|
S63VA;Vi;Vch;Vl;Vlst;A5").
Let HPIN3 : ltac2:(tb__ "0|3|
S1S0SaQ40M0A1M1ScVrho1;P97A2S8G0S25S20VA;A1M2A1A2A3S1S0G1ScVrho1;P98A2S8G0S24G2A1A2A3S0G1ScVrho1;P9bA2S8G0S23G2A1A2A3A2A2") := ltac2:(tb__ "0|b|
S4S0SaQ40M0A1M1ScVrho1;P97A2S8G0S25S20VA;A1M2A1A2A3M3S1S0G1ScVrho1;P98A2S8G0S24G2A1A2A3M4S0G1ScVrho1;P9bA2S8G0S23G2A1A2A3M5A2S3G3S1G4S1G5S1S0G1ScVrho1;PcA2S8G0Vp;A2A3S1S0G1ScVrho1;P69A2S8G0S38Vn;A1M6A2A3S0G1ScVrho1;P6aA2S8G0S19G6Z8A2A2A3A2A2M7A2M8A2M9VHPIN;A3S4G4G5S3G4G8S5G3G9VHPIN;A3MaA3S3G5G7S5G4G8GaA3A3A4A4").

Lemma N_madv_num : ltac2:(tb__ "0|2|
SfVENVX;R1A1S1S0SbS9Q40SeR2S4cA2A2S1bS4bVh;Vmsz;A2S4aVh;A1A2M0A3S1S0SbS18G0Z1000A2Z0M1A3S1S17G1G0A2S17G0S1aZ2Z3eA2A2A2A2A2F_;Fr;").
Proof. intros r (_ & E202 & E203 & _). exact (madv_num ch CH r (conj E202 E203)). Qed.

Lemma N_madv_pre : ltac2:(tb__ "0|1|
SfS2aSaQ40A1M0A1VENVX;R2A1S56S37VJH1;VJH1;S60Vcv;A1R3R2G0S2cL_;S1bS4bVh;Vmsz;A2S4aVh;A1A2A8F_;Ftp;Fr;").
Proof.
  intros r tp EX. pose proof EX as (P0 & E202 & E203 & _).
  pose proof (v_EMdnode _ f l cv VOK) as (_ & _ & NA0 & _ & _ & NAX & _).
  intros tr ms md Hsp HJ.
  pose proof (zenv_at nW Kc HKc A rho1 p n i ch f TZ HI HU HSZ HN HNB Hf HPIN cf SF r tp tr md HJ P0 F1) as ZE.
  exact (madv_pre nW Kc HKc A rho1 i ch f TZ HZT_sh HI CH HFAM HPIN3 (hv_EMd cv) NA0 NAX r tp (conj E202 E203)
           (DISJ4_hb nW A p n i ch l lst cv HNUM Hl HLI HI DJ r ZE EX) tr ms md Hsp HJ).
Qed.

Lemma N_mun_num : ltac2:(tb__ "0|2|
SfVENVX;R1A1S1S0SaQ40M0A1SeR2S6aA2S8G0Vmsz;A2A3S1S0SbS18Vmsz;Z1000A2Z0M1A3S1S17G1Vmsz;A2S17Vmsz;S1aZ2Z3eA2A2A2A2A2F_;Fr;").
Proof. intros r (_ & _ & E203 & _). destruct CH as (C1 & C2 & C3 & C4 & C5). split; [exact E203|]. split; [exact C2|]. unfold msz. fold h in C4, C5. clear -C3 C4 C5. lia. Qed.

Lemma N_mun_pre : ltac2:(tb__ "0|d|
SfS2aSaQ40M0A1M1A1VENVX;R2A1S2aS40A1M2S4fS3eS5cS37R6R5S61Vcv;A1M3S2bG2S51R3S52R2R1A2A4A5VJP;R7R6R4R2A4S50R4U0A2G1S1S0SbS18S9G0R1A2M4S43A2Z0A3S1S16S15G4Vmsz;A2M5S3fA2S1S0S29S41S3dS3cR4A1A1M6R1S8G0Vmsz;A2M7A3S2cA3S1G1S39S2eG1G1A2S2bG1G1R2R1A4S3dS3cR5A1A1A3S0G1R2G7A3F_;Fs;S1S0S29S44S42G6R1A2R1G7A3S2cA3S1S10S39S10R1S14S58G3A1A1A3S12S11RbR2A2S2bSbSbS9G0R3A2M8S15G8Vmsz;A2A4A2F_;Fo;S1S2eSdSdA2M9SbS39G9R2S59G3A1A3S1S16S9G0SeRcS34SdSdR3A3A2A2MaR2A2S17R2S15GaS9G0SeRcS36SdSdR3A3A2A2A2A2A2S7S1S16S9G0R5A2MbS9G0S5bS9G0SeRdS5aG3A1A2A2R3A2A2McA2S17GcS15GbVmsz;A2A2A2A1F_;F_;Fy;Frr;VJ2;S55R9S54S13R9A1R1G7A3A2S57G4G5R8A3R6S53R4R1G7A3A4A2A2A2A2A2A2A2Ta;F_;F_;Fmd;Fms;Ftr;F_;Ftp;Fr;").
Proof.
  intros r tp EX tr ms md Hsp HJP. pose proof EX as (P0 & E202 & E203 & _).
  pose proof (v_EUdnode _ f l cv VOK) as (_ & _ & NA0 & _ & NAX & _).
  assert (ZE : zenv nW A p n ch r).
  { destruct HJP as (rp & HJF & BR & _). destruct HJF as (Hag & HA & _ & _ & HK & Htp & _ & Htop).
    apply (zenv_rw nW A rho1 p n i ch HU HN HNB HPIN HNUM (FCHs_below_SF nW cf SF) F1 r).
    - intros v Hv. rewrite (proj1 BR v). symmetry. exact (proj1 Hag v Hv).
    - intros l0. rewrite (proj1 (proj2 BR) l0). symmetry. exact (proj1 (proj2 Hag) l0).
    - unfold top_high in *. unfold V_DEPTH in *. rewrite !(proj1 BR). exact Htop. }
  destruct CH as (C1 & C2 & C3 & C4 & C5).
  assert (CH4 : 0x646000 <= sc_map_beg ch /\ 0 < sc_map_size ch /\ sc_map_beg ch + sc_map_size ch < 2 ^ 47
                /\ (sc_map_beg ch + sc_map_size ch <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= sc_map_beg ch))
    by (split; [exact C4 | split; [clear -C3; lia | split; [exact C5 | exact BND]]]).
  exact (mun_pre nW Kc HKc A rho1 l1 l2 p n i ch lst l TZ HZTc HLV HPR HI HU Hl (proj1 HLI) (HLF_of A i ch HI l HLI)
           CH4 C1 LSTOFF PABOFF NCB HPIN3 (hv_EUd cv) NA0 NAX r tp E202
           (HDISJ_hb nW A p n i ch l lst cv HNUM Hl HLI HI DJ r ZE EX) tr ms md Hsp HJP).
Qed.
End Nodes.
End F0A_hbN_nodes.

(* [comment removed for export] *)
Module F0A_hbN_asm.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "ex"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "AA"; "aa_sec"; "aa_geom"; "ag_spacebeg"; "aa_live"; "sc_map_beg"; "sc_map_size"; "ag_ctx"; "ag_pab"; "ag_thread"; "@Corelib.Init.Datatypes"; "bool"; "nat"; "true"; "list"; "false"; "prod"; "length"; "app"; "Some"; "option"; "pair"; "cons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "rw"; "sprop_below"; "sprop_eqb"; "ss_facts"; "ss_next"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "cst_ok"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "JOK"; "trC"; "trS"; "TR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "F_depth"; "Wcan"; "chain_pre"; "free_depth"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_sh_zone"; "chunk_zone"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "div"; "mul"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_exit"; "TZh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap"; "JH2"; "JPh"; "DUZh"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "nth_error"; "In"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dn.F0A_hbN_asm"; "hbtag_ok"; "fam_allowed"; "hbcertF"; "hbcertV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_leaf"; "hbleaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "hbfam"; "hbvar"; "hbfam_ok"; "hbvar_ok"; "hf_S0"; "hf_SC"; "hv_C5"; "hv_XF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry"; "ZUH"; "T_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.F0A_hbN_scan"; "hbnums"; "ENVXs"; "FCH1"; "PIN0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones"; "zd_allb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayReserve"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue"; "fam_ok"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.da.F0A_hbN_disj"; "hbdisj_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_du"; "DUPIN"; "du_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_scand"; "hbscanV_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states"; "XO_hb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_tail"; "TPIN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln"; "HBIGNE_stmt"; "HBIGN_stmt"; "QFN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib"; "s_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundW SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv ReprGlue Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 RebuildM InvLaws SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2 SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_blind SegQS_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert F0A_hbN_env.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require da.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_leaf SegQtr SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_rebuildW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.F0A_rzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_pure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_scand OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.F0A_hbN_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dn.F0A_hbN_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_du OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.da.F0A_hbN_disj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.F0A_hbN_qsz OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dn.F0A_hbN_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_leaf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SysCallA MmapFixedA MmapNodesA MunmapSymA MadviseSpecA MadviseA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma TZh_sh : ltac2:(tb__ "0|0|
S9S8S0S3eR2R1A2S4dR4R3R2A3F_;Fz;Fch;FA;"). Proof. intros A ch z H. right. right. exact H. Qed.
Lemma TZh_ch : ltac2:(tb__ "0|0|
S9S8S0S3fR2R1A2S4dR4R3R2A3F_;Fz;Fch;FA;"). Proof. intros A ch z H. right. left. exact H. Qed.
Lemma TZh_tbl : ltac2:(tb__ "0|1|
S9S8S0S2S40S11SbR3A1A1M0R1A2S41R1S42G0S72A2A2A2S4dR4R3R2A3F_;Fz;Fch;FA;").
Proof. intros A ch z H. left. left. right. right. right. right. left. exact H. Qed.
Lemma TZh_DUZ : ltac2:(tb__ "0|0|
S9S14S8S0S1S1cS8A1S53S8SaR4A1R3A3S1bS8R2A2A3S40S44Z8S45S19S8SaR5A1A2A1A2S72A2S50R6R5R4R3A4S4dR7R5R4A3F_;F_;F_;Fz;Fch;Fi;FA;").
Proof.
  intros A i ch z HI NCB [H|[H|[H|H]]]; [exact (TZh_ch A ch z H) | exact (TZh_sh A ch z H) | |]; left; left; right; right; right.
  - left. unfold sec_junk_zone, SEC_INST in *. lia.
  - pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LTi.
    destruct H as [H|[H|[H|(lst & Hl & H)]]]; [left; unfold SEC_INST in *; lia | left; unfold SEC_INST in *; lia | right; left; unfold kPtrArrayReserve in *; lia |].
    right. right. left. apply Exists_exists. exists lst. split; [exact (nth_error_In _ _ Hl) | lia].
Qed.

Section Variant.
Context {Q : assn} (X : trk Q).
Variables (CST XGL : list (Z * Z)) (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (rho1 : valuation) (p n : Z) (i : nat) (ch lst : sec_chunk) (f : nat) (l : bool) (l1 l2 : list (Z * Z)).
Let TZ : Z -> Prop := TZh A ch.
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Let JH1 : jpredA := ltac2:(tb__ "0|0|
S4cS1fS3eVch;A1VTZ;S2fVnW;S32S17VA;VKc;Vrho1;A6A4").
Let JP : jpredA := ltac2:(tb__ "0|0|
S4fVnW;VKc;VA;Vrho1;Vi;Vch;Vlst;Vl;VTZ;A9").
Let J2 : jpredA := ltac2:(tb__ "0|0|
S4eVKc;VA;Vrho1;Vl1;Vl2;Vi;Vch;VTZ;A8").
Let ENVX : valuation -> Prop := ltac2:(tb__ "0|0|
S6cVA;Vi;Vch;Vl;Vlst;A5").
Hypothesis LF : ltac2:(tb__ "0|0|
S5aVCST;VXGL;VnW;VA;Vrho1;Vp;Vn;Vi;Vch;A9").
Hypothesis Hf : (f <= 2)%nat.
Hypothesis HFAM : ltac2:(tb__ "0|0|
S74Vf;ScSbVA;A1A1SeVch;A1SfVch;A1A4").
Hypothesis Hl : ltac2:(tb__ "0|1|
S1S1cS8A1S53S8SaVA;A1M0S55S19S8G0A2U1A2A3S1bS8Vlst;A2A3").
Hypothesis HLI : ltac2:(tb__ "0|0|
S7S1S13Vl;S15A3S1S14Vi;S55S19S8SaVA;A1A2U1A2A3A2").
Variables (E : axst) (cf : hbfam) (cv : hbvar).
Hypothesis FOK : ltac2:(tb__ "0|0|
S63VE;Vf;Vcf;A3").
Hypothesis VOK : ltac2:(tb__ "0|0|
S64S66Vcf;A1Vf;Vl;Vcv;A4").
Hypothesis TOK : ltac2:(tb__ "0|0|
S1S13S82S6aVnW;Vf;VE;S65Vcf;A1A4A1S15A3").
Hypothesis ZOK : ltac2:(tb__ "0|0|
S2S1S13S6fVnW;S69S27S4aVE;A1A1A3S15A3S1S13S6fVnW;S69S7cA3S15A3A2").
Hypothesis FCH : ltac2:(tb__ "0|1|
S2S1S13S51S20S20S52S20S24R1A1S25S4aVE;A1A1A3Lg;S1aS20S35S34VnW;A1A1S33S36A1A3M0A3S15A3S1S13S51S20S23S5fA1G0A3S15A3A2").
Hypothesis SF : hbscanF_ok nW cf.
Hypothesis SV : ltac2:(tb__ "0|0|
S7bVnW;Vcf;Vf;Vl;Vcv;A5").
Hypothesis QZ : hbqsz_ok nW cv.
Hypothesis DJ : ltac2:(tb__ "0|0|
S78VnW;Vl;Vcv;A3").
Hypothesis HLV : ltac2:(tb__ "0|1|
S1S16S18S0S0A2M0A1SdVA;A1S1aG0Vl1;S1eG0S1dS0S0Vp;Vn;A4Vl2;A3A3A3").
Hypothesis DUOK : ltac2:(tb__ "0|0|
S1S13S7aVl;Vcv;A2S15A3").
Hypothesis C5N : ltac2:(tb__ "0|0|
S84PcfS26S4aS67Vcv;A1A1A1A2").
Hypothesis HNUM : ltac2:(tb__ "0|0|
S6bVA;Vp;Vn;Vi;Vch;A5").
Hypothesis F1 : FCH1 nW rho1.
Hypothesis HJ1 : JOK X JH1.
Hypothesis HJP : JOK X JP.
Hypothesis HJ2 : JOK X J2.

Hypothesis GX : ltac2:(tb__ "0|0|
S21S16S3cQ40A1A1S3aVENVX;R3A1S46S1fVJ2;S68Vcv;A1R4R3R2A6VQ;R3A1F_;F_;Fw;Ftp;Fr;").

Lemma HPIN6 : ltac2:(tb__ "0|4|
S2S1S3cQ40M0A1M1S22Vrho1;P97A2S3bG0S12SbVA;A1M2A1A2A3S2S1G1S22Vrho1;P98A2S3bG0S10G2A1A2A3S2S1G1S22Vrho1;P9bA2S3bG0ScG2A1A2A3S2S1G1S22Vrho1;PcA2S3bG0Vp;A2A3S2S1G1S22Vrho1;P69A2S3bG0S7eVn;A1M3A2A3S1G1S22Vrho1;P6aA2S3bG0S43G3Z8A2A2A3A2A2A2A2A2").
Proof. destruct (lf_pins _ _ _ _ _ _ _ _ _ LF) as (P1 & P2 & P3 & P4 & P5 & P6 & _). exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 P6))))). Qed.
Lemma HLTF : ltac2:(tb__ "0|1|
S2S1S13Vl;S15A3S1S14Vi;S55S19S8SaVA;A1A2U1A2M0A3F_;S1S13Vl;S17A3S76Vi;G0A2F_;A2").
Proof.
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite (lf_hi _ _ _ _ _ _ _ _ _ LF); discriminate)) as LTi.
  split; [exact (proj1 HLI)|]. intros El. destruct (Nat.eq_dec i (length (aa_sec A) - 1)) as [E0|N0]; [rewrite (proj2 HLI E0) in El; discriminate | lia].
Qed.

Lemma ENVX_parts : ltac2:(tb__ "0|0|
S21VENVX;R1A1S2S6eVA;R2A2S2S7dVch;R2A2S79VA;Vi;Vch;Vlst;Vl;R2A6A2A2F_;Fr;").
Proof.
  intros r (P0 & XV). pose proof P0 as (E200 & E201 & E195). pose proof XV as (E202 & E203 & XF).
  split; [exact P0|]. split; [exact (conj E202 E203)|].
  unfold DUPIN. split; [exact E200|]. split; [exact E201|]. split; [exact E195|]. split; [exact E202|]. split; [exact E203|].
  intros El. destruct (XF El) as (E204 & E205 & _). exact (conj E204 E205).
Qed.

Theorem hb_variant : ltac2:(tb__ "0|0|
S21S16S3cQ40A1A1S2eVQ;VX;S46S1fVJH1;VE;R2R1A5A3FtpE;FrhoE;").
Proof.
  intros rhoE tpE.
  pose proof LF as [HPR HI HU HSZ HN HNB CH BND PABO NCB _ LST PINS ZT ZC ZL NQ NQS NOC RO LQ0 HSB].
  pose proof HPIN6 as HP6. destruct HLTF as [HLT HLF].
  refine (hb_skeleton X nW A Kc rho1 ch f l TZ E cf cv FOK VOK JP J2 HJ1 HJP HJ2 (ENV0s A) ENVX (ENV0s_keep A)
            (fun r r' EN K => ENVXs_keep A rho1 p n i ch HP6 l lst r r' EN K) (ME h msz - MB h) msz rhoE tpE _ _ _ _ _
            (N_madv_num A i ch lst l CH)
            (N_madv_pre nW Kc HKc A rho1 p n i ch lst f l TZ cf cv HI HU HSZ HN HNB Hf HFAM Hl HLI CH HP6 HNUM F1 SF VOK DJ (TZh_sh A ch)) _
            (N_mun_num A i ch lst l CH)
            (N_mun_pre nW Kc HKc A rho1 l1 l2 p n i ch lst f l TZ cf cv HLV HPR HI HU HN HNB Hl HLI CH BND (fun El => LST lst Hl (HLF El)) PABO NCB HP6 HNUM F1 SF VOK DJ (TZh_ch A ch)) _ GX C5N).
  - intros w Hw. destruct (G_entry nW Kc HKc (stopJ_stable_le _) A rho1 p n i ch f TZ HI HU HSZ HN HNB HFAM HP6 E (hf_S0 cf) TOK ZOK FCH rhoE tpE w Hw) as (r2 & H2 & PN).
    exists r2. split; [exact H2|]. unfold ENV0s, PIN0.
    split; [exact (PN _ _ (or_introl eq_refl))|]. split; [exact (PN _ _ (or_intror (or_introl eq_refl))) | exact (PN _ _ (or_intror (or_intror (or_introl eq_refl))))].
  - intros tp. exact (G_scan_hb nW Kc HKc (stopJ_stable_le _) A rho1 p n i ch f TZ HI HU HSZ HN HNB Hf HFAM HP6 (TZh_sh A ch) (TZh_tbl A ch) E cf FOK SF X HJ1 l lst cv tp Hl HLI SV).
  - intros r tp w EN Hw. exact (G_c5 nW Kc A rho1 ch TZ (hf_SC cf) f l cv VOK CH r tp w (proj1 (proj2 (ENVX_parts r EN))) Hw).
  - intros r tp w EN Hw. exact (G_eus nW Kc A rho1 ch TZ (hf_SC cf) f l cv VOK CH r tp w (proj1 (proj2 (ENVX_parts r EN))) Hw).
  - intros r tp w EN Hw. exact (G_shd nW Kc A rho1 ch TZ (TZh_sh A ch) (hf_SC cf) f l cv VOK CH r tp w (proj1 (proj2 (ENVX_parts r EN))) Hw).
  - intros r tp w EN Hw.
    exact (G_du nW Kc HKc A rho1 p n i ch lst l TZ HI HU HSZ HN HNB Hl HLT HLF HP6 (fun z => TZh_DUZ A i ch z HI NCB) (TZh_tbl A ch) (hf_SC cf) f cv VOK DUOK r tp w (proj2 (proj2 (ENVX_parts r EN))) Hw).
  - intros r tp w _ Hw. destruct PINS as (_ & _ & _ & _ & _ & _ & P123 & _).
    exact (G_qsz_hb nW Kc A rho1 p n i ch l1 l2 TZ (hf_SC cf) f l cv VOK QZ HU HN HNB HP6 HNUM (FCHs_below_SF nW cf SF) F1 LQ0 ZT P123 r tp w Hw).
Qed.
End Variant.

Section LeafNums.
Variables (CST XGL : list (Z * Z)) (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (rho1 : valuation) (p n : Z) (i : nat) (ch : sec_chunk) (f : nat).
Hypothesis LF : ltac2:(tb__ "0|0|
S5aVCST;VXGL;VnW;VA;Vrho1;Vp;Vn;Vi;Vch;A9").
Hypothesis Hf : (f <= 2)%nat.
Variable E : axst.
Hypothesis FCH : ltac2:(tb__ "0|1|
S2S1S13S51S20S20S52S20S24R1A1S25S4aVE;A1A1A3Lg;S1aS20S35S34VnW;A1A1S33S36A1A3M0A3S15A3S1S13S51S20S23S5fA1G0A3S15A3A2").
Lemma leaf_nums : ltac2:(tb__ "0|0|
S21S16S3cQ40A1A1S3aS46S1fS2fVnW;S32S17VA;VKc;Vrho1;A6VE;R3R2R1A6S2S6bVA;Vp;Vn;Vi;Vch;A5S6dVnW;Vrho1;A2A2F_;Fw;FtpE;FrhoE;").
Proof.
  intros rhoE tpE [tr [ms md]] H. pose proof LF as [HPR HI HU HSZ HN HNB CH BND PABO NCB _ LST PINS ZT ZC ZL NQ NQS NOC RO LQ0 HSB].
  destruct PINS as (P1 & P2 & P3 & P4 & P5 & P6 & _).
  split.
  - set (bs := [(200%positive, Z_to_bv 64 (ag_pab (aa_geom A))); (201%positive, Z_to_bv 64 (Z.of_nat (length (aa_sec A)))); (195%positive, Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize))]).
    set (rB := rho_sets rhoE bs).
    pose proof (JF_stable nW UStopLe false A Kc rho1 (stopJ_stable_le _) HKc) as HST. change GW with NPRE in HST.
    assert (HJB : JW segsA (chunk_sh_zone ch) (fun _ => True) (JF nW UStopLe false A Kc rho1) rB tpE tr md).
    { apply (JW_stable segsA NPRE (chunk_sh_zone ch) (fun _ => True) _ HST rhoE rB tpE tr md md); [|apply mat_equiv_refl | apply JW_intro; exact (proj2 H)].
      unfold rB. apply agree_below_rho_sets. intros v x Hin. cbn in Hin. unfold NPRE. repeat (destruct Hin as [Ein|Hin]; [injection Ein as <- _; lia|]). destruct Hin. }
    assert (NDB : List.NoDup (map fst bs)) by (cbn; repeat constructor; cbn; intuition discriminate).
    refine (hbnums_at nW Kc HKc A rho1 p n i ch f (fun _ => True) HI HU HSZ HN Hf (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 P6))))) rB tpE tr md HJB _).
    unfold PIN0. split; [exact (rho_sets_get bs rhoE _ _ NDB (or_introl eq_refl))|].
    split; [exact (rho_sets_get bs rhoE _ _ NDB (or_intror (or_introl eq_refl))) | exact (rho_sets_get bs rhoE _ _ NDB (or_intror (or_intror (or_introl eq_refl))))].
  - unfold FCH1, FCHs. apply Forall_forall. intros g Hg.
    pose proof (SPA_facts_hold segsA _ rhoE E tpE _ H) as HFa.
    pose proof (proj1 (forallb_forall _ _) (proj1 FCH) g Hg) as X0. apply existsb_exists in X0 as (g' & Hg' & Eg). apply sprop_eqb_sound in Eg. subst g'.
    pose proof (proj1 (Forall_forall _ _) HFa g Hg') as HG0. destruct (proj2 H) as (Hag & _).
    exact (proj2 (holds_agree GW rho1 rhoE g Hag (proj1 (forallb_forall _ _) (proj2 FCH) g Hg)) HG0).
Qed.
End LeafNums.

Section JOKs.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (rho1 : valuation) (l1 l2 : list (Z * Z)) (i : nat) (ch lst : sec_chunk) (l : bool) (TZ : Z -> Prop).
Lemma JF_st : ltac2:(tb__ "0|0|
S49S1fS5fS2fVnW;S32S17VA;VKc;Vrho1;A6A3").
Proof. pose proof (JF_stable nW UStopLe false A Kc rho1 (stopJ_stable_le _) HKc) as HST. change GW with NPRE in HST. exact HST. Qed.
Lemma JOK1_C : ltac2:(tb__ "0|0|
S39S2bR1S2cR1A1S4cS1fS3eVch;A1VTZ;S2fVnW;S32S17VA;VKc;Vrho1;A6A4A3FQ;").
Proof. intros Q. rewrite trC_JOK. exact (JW_stable segsA NPRE _ TZ _ JF_st). Qed.
Lemma JOKP_C : ltac2:(tb__ "0|0|
S39S2bR1S2cR1A1S4fVnW;VKc;VA;Vrho1;Vi;Vch;Vlst;Vl;VTZ;A9A3FQ;").
Proof. intros Q. rewrite trC_JOK. exact (JPh_stable nW Kc HKc A rho1 i ch lst l TZ). Qed.
Lemma JOK2_C : ltac2:(tb__ "0|0|
S39S2bR1S2cR1A1S4eVKc;VA;Vrho1;Vl1;Vl2;Vi;Vch;VTZ;A8A3FQ;").
Proof. intros Q. rewrite trC_JOK. exact (JH2_stable Kc HKc A rho1 l1 l2 i ch TZ). Qed.
Section Sound.
Variable ok : world -> Prop.
Hypothesis HOK : ltac2:(tb__ "0|0|
S48S1fVok;S47VKc;A1A3").
Hypothesis HOKP : ltac2:(tb__ "0|0|
S77S1fVok;S47VKc;A1A3").
Lemma JOK1_S : ltac2:(tb__ "0|0|
S39S2bR1S2dVok;R1A2S4cS1fS3eVch;A1VTZ;S2fVnW;S32S17VA;VKc;Vrho1;A6A4A3FQ;").
Proof.
  intros Q. rewrite trS_JOK. split; [exact (JW_okf segsA ok _ TZ _ (JF_okf nW UStopLe false ok A Kc rho1 HOK))|]. split; [|exact (JW_stable segsA NPRE _ TZ _ JF_st)].
  apply (JW_okpf segsA ok _ TZ). apply (okp_via ok Kc _ HOKP). intros r tp tr md (_ & _ & _ & _ & HK & _). exact HK.
Qed.
Lemma JOKP_S : ltac2:(tb__ "0|0|
S39S2bR1S2dVok;R1A2S4fVnW;VKc;VA;Vrho1;Vi;Vch;Vlst;Vl;VTZ;A9A3FQ;").
Proof. intros Q. rewrite trS_JOK. exact (conj (JPh_okf nW Kc A rho1 i ch lst l TZ ok HOK) (conj (JPh_okpf nW Kc A rho1 i ch lst l TZ ok HOKP) (JPh_stable nW Kc HKc A rho1 i ch lst l TZ))). Qed.
Lemma JOK2_S : ltac2:(tb__ "0|0|
S39S2bR1S2dVok;R1A2S4eVKc;VA;Vrho1;Vl1;Vl2;Vi;Vch;VTZ;A8A3FQ;").
Proof. intros Q. rewrite trS_JOK. exact (conj (JH2_okf Kc A rho1 l1 l2 i ch TZ ok HOK) (conj (JH2_okpf Kc A rho1 l1 l2 i ch TZ ok HOKP) (JH2_stable Kc HKc A rho1 l1 l2 i ch TZ))). Qed.
End Sound.
End JOKs.

Record hbcertF (nW f : nat) (E : axst) (cf : hbfam) : Prop := mkCF {
  cF_fok : hbfam_ok E f cf;
  cF_tok : s_ok (T_entry nW f E (hf_S0 cf)) = true;
  cF_zok : zd_allb nW ZUH (ss_objs (ax_S E)) = true /\ zd_allb nW ZUH XO_hb = true;
  cF_fch : forallb (fun g => existsb (sprop_eqb g) (ss_facts (ax_S E))) (chain_pre (Wcan nW) ++ F_depth free_depth) = true
           /\ forallb (sprop_below NPRE) (chain_pre (Wcan nW) ++ F_depth free_depth) = true;
  cF_sf : hbscanF_ok nW cf
}.
Record hbcertV (nW f : nat) (l : bool) (cf : hbfam) (cv : hbvar) : Prop := mkCV {
  cV_vok : hbvar_ok (hf_SC cf) f l cv;
  cV_sv : hbscanV_ok nW cf f l cv;
  cV_dj : hbdisj_ok nW l cv;
  cV_qz : hbqsz_ok nW cv;
  cV_du : du_chk l cv = true;
  cV_c5 : (207 <=? ss_next (ax_S (hv_C5 cv)))%positive = true;
  cV_x : hbexit_ok nW (hv_XF cv)
}.

Definition fam_allowed (khi : bool) (f : nat) : Prop := ltac2:(tb__ "0|0|
S13OLkhi;Vkhi;S3S1S14Vf;U1A3S1S14Vf;U2A3A2S1S14Vf;U0A3X13x2").
Definition hbtag_ok (nW : nat) (khi : bool) (E : axst) : Prop := ltac2:(tb__ "0|0|
S14S57Vkhi;R1A2S6S61S61S2S58VnW;R3VE;R1A4S13S6S62S62S59VnW;R5R2R3R1A5Lcv;A2Fl;A2Lcf;A2F_;Ff;").

Lemma fam_of_class : ltac2:(tb__ "0|1|
S16S18S0S0A2A1M0G0S14S9S21S0S0S14S8S13S14S5aRbRaR9R8R7R6R5R4R3A9S60R3R7R6A3S74R3ScSbRaA1A1SeR5A1SfR5A1A4S75R4U2A2S57R6R5A2F_;F_;F_;F_;Ff;Fkhi;Fch;Fi;Fn;Fp;Frho1;FA;FnW;FXGL;FCST;").
Proof.
  intros CST XGL nW A rho1 p n i ch khi f LF HC HF Hf. pose proof (lf_hu _ _ _ _ _ _ _ _ _ LF) as HU. pose proof (lf_hnb _ _ _ _ _ _ _ _ _ LF) as HNB.
  pose proof (lf_hn _ _ _ _ _ _ _ _ _ LF) as HN. pose proof (lf_sb _ _ _ _ _ _ _ _ _ LF) as HSB. pose proof (N8_facts n HN) as (N1 & _).
  unfold fam_allowed, cls_hyp, PG, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  destruct khi; destruct f as [|[|[|f']]]; cbn [fam_ok] in HF; try lia; try (left; reflexivity); try (right; reflexivity); try reflexivity.
Qed.

Section Tag.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S28VCST;R1A2S3S28S5bR2A2S2S40S5cR2A2S41R2S5dA2A2A2S4F_;F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S28VCST;R1A2S5S5eR2A1A1F_;Fa;").
Variables (nW : nat) (khi : bool) (E : axst).
Hypothesis TAG : ltac2:(tb__ "0|0|
S56VnW;Vkhi;VE;A3").
Variables (A0 : AA) (Kc : KcA) (rho : valuation) (tp : list word) (p n t : Z) (jv : junkF) (keep : Z -> Prop).
Hypothesis HKc : Kc_ok Kc.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S1S0S3dQ40S22Vrho;PcA2A2Vp;A3").
Hypothesis Hn13 : ltac2:(tb__ "0|0|
S1S0S3dQ40S22Vrho;PdA2A2Vn;A3").
Hypothesis HL : ltac2:(tb__ "0|0|
S54S18S0S0A2S1dS0S0Vp;Vn;A4SdVA0;A1A3").
Hypothesis HCLS : ltac2:(tb__ "0|0|
S60Vkhi;Vp;Vn;A3").
Hypothesis Hii : aa_internal_inited A0 = true.
Hypothesis HBIG : kQuarantineMax < n.
Hypothesis HR : ltac2:(tb__ "0|0|
S31Vrho;S70VA0;Vrho;Vp;Vn;Vt;Vjv;A6A2").
Hypothesis HJMIN : ltac2:(tb__ "0|0|
S1S0S71Vjv;A1S73A3").
Hypothesis HKEEP : ltac2:(tb__ "0|0|
S0S3S37VCST;VA0;R1A3S38VCST;VXGL;VA0;R1A4A2Vkeep;R2A1F_;Fa;").
Let Q : assn := ltac2:(tb__ "0|0|
S81VCST;VXGL;VnW;VA0;VKc;Vrho;Vtp;A7").
Variable X : trk Q.
Hypothesis XJ1 : ltac2:(tb__ "0|0|
S9S21S8S0OF_;S2bVQ;VX;S4cS1fS3eR2A1R1S2fVnW;S32S17R4VKc;R3A6A4A3FTZ;Fch;Frho1;FA;").
Hypothesis XJP : ltac2:(tb__ "0|0|
S9S21S14S8S8S13S0OF_;S2bVQ;VX;S4fVnW;VKc;R7R6R5R4R3R2R1A9A3FTZ;Fl;Flst;Fch;Fi;Frho1;FA;").
Hypothesis XJ2 : ltac2:(tb__ "0|1|
S9S21S16S18S0S0A2A1M0G0S14S8S0OF_;S2bVQ;VX;S4eVKc;R7R6R5R4R3R2R1A8A3FTZ;Fch;Fi;Fl2;Fl1;Frho1;FA;").

Theorem hb_run : ltac2:(tb__ "0|0|
S9S21S21S16S3cQ40A1A1S30VA0;R4A2S83Vkeep;S70VA0;Vrho;Vp;Vn;Vt;Vjv;A6R4A3S2eVQ;VX;S46S1fS2fVnW;S32S17R6VKc;R5A6VE;R4R3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';").
Proof.
  intros A' rho1' rhoE tpE HDO HLK.
  apply (tr_pure X _ (exists i ch, hbleaf CST XGL nW A' rho1' p n i ch)).
  { intros [tr [ms md]] Hw. exact (leaf_facts CST XGL HCST HXGL HCSTQ nW Kc HKc A0 rho p n t jv keep A' rho1' Hp12 HL (cls_hyp_blk khi p n HCLS) Hii HBIG HJMIN HDO HLK E rhoE tpE tr ms md Hw). }
  intros (i & ch & LF). pose proof LF as [HPR HI HU HSZ HN HNB CH BND PABO NCB FAM LST PINS ZT ZC ZL NQ NQS NOC RO LQ0 HSB].
  destruct FAM as (f & Hf & HFAM). pose proof (fam_of_class CST XGL nW A' rho1' p n i ch khi f LF HCLS HFAM Hf) as FA.
  destruct (TAG f FA) as (cf & CF & CVS).
  pose proof (proj1 (nth_error_Some (aa_sec A') i) ltac:(rewrite HI; discriminate)) as LTi.
  destruct (nth_error (aa_sec A') (length (aa_sec A') - 1)) as [lst|] eqn:Hl; [|exfalso; apply nth_error_None in Hl; lia].
  set (l := if Nat.eq_dec i (length (aa_sec A') - 1) then true else false).
  assert (HLI : l = true <-> i = (length (aa_sec A') - 1)%nat) by (unfold l; destruct (Nat.eq_dec i (length (aa_sec A') - 1)); split; intros; first [assumption | reflexivity | discriminate | contradiction]).
  destruct (CVS l) as (cv & CV).
  assert (HL' : In (p, n) (aa_live A')) by (destruct HDO as (_ & _ & _ & _ & _ & EL & _); rewrite EL; exact HL).
  destruct (in_split _ _ HL') as (l1 & l2 & HLV).
  apply (tr_pure X _ (hbnums A' p n i ch /\ FCH1 nW rho1')).
  { intros w Hw. exact (leaf_nums CST XGL nW Kc HKc A' rho1' p n i ch f LF Hf E (cF_fch _ _ _ _ CF) rhoE tpE w Hw). }
  intros (HNUM & F1).
  apply (tr_conseq X _ (SPA segsA (JW segsA (chunk_sh_zone ch) (TZh A' ch) (JF nW UStopLe false A' Kc rho1')) E rhoE tpE)).
  { intros w [Hs HJ]. split; [exact Hs | apply JW_intro; exact HJ]. }
  destruct PINS as (P1 & P2 & P3 & P4 & P5 & P6 & P123 & PB). destruct CH as (C1 & C2 & C3 & C4 & C5).
  apply (hb_variant X CST XGL nW Kc HKc A' rho1' p n i ch lst f l l1 l2 LF Hf HFAM Hl HLI E cf cv (cF_fok _ _ _ _ CF) (cV_vok _ _ _ _ _ CV) (cF_tok _ _ _ _ CF) (cF_zok _ _ _ _ CF)
           (cF_fch _ _ _ _ CF) (cF_sf _ _ _ _ CF) (cV_sv _ _ _ _ _ CV) (cV_qz _ _ _ _ _ CV) (cV_dj _ _ _ _ _ CV) HLV (cV_du _ _ _ _ _ CV) (proj1 (Pos.leb_le _ _) (cV_c5 _ _ _ _ _ CV)) HNUM F1
           (XJ1 _ _ _ _) (XJP _ _ _ _ _ _ _) (XJ2 _ _ _ _ _ _ _)).
  intros r tp0 w ((E200 & _ & E195) & _) Hw.
  assert (CHB : sc_map_beg ch mod 8 = 0 /\ sc_map_size ch mod 8 = 0 /\ IMG_HI <= sc_map_beg ch /\ 0 <= sc_map_size ch /\ sc_map_beg ch + sc_map_size ch < 2 ^ 47
                /\ (sc_map_beg ch + sc_map_size ch <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= sc_map_beg ch)).
  { split; [exact (mod8_of_4096 _ C1)|]. split; [exact (mod8_of_4096 _ C2)|]. split; [unfold IMG_HI; lia|]. split; [lia|]. exact (conj C5 BND). }
  exact (G_exit CST XGL HCST HXGL HCSTF nW (hv_XF cv) (cV_x _ _ _ _ _ CV) A0 Kc rho tp p n t jv keep A' rho1' l1 l2 i ch HKc Hp12 Hn13 HR HDO HLK HKEEP HLV
           (conj P1 (conj P2 (conj P3 (conj P4 PB)))) ZT ZC ZL
           CHB
           NQ NQS (NOC l1 l2 HLV) RO r tp0 w E195 E200 Hw).
Qed.
End Tag.

Theorem hb_tag : ltac2:(tb__ "0|1|
S16S18S0S0A2A1M0G0S29R2A1S2aR2A1S0S28R5R1A2S3S28S5bR2A2S2S40S5cR2A2S41R2S5dA2A2A2S4F_;F_;Fa;S0S28R6R1A2S5S5eR2A1A1F_;Fa;S14S13S4bS56R3R2R1A3S80RaR9R3R4R2A5F_;FE;Fkhi;FnW;F_;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTF HCSTQ nW khi E TAG. unfold HBIGN_stmt, contN.
  intros ok A0 Kc rho tp p n t jv keep HKc HOK HOKP Hp12 Hn13 HL HCLS Hii HBIG HTJV HR HJMIN HKEEP A' rho1' rhoE tpE HDO HLK.
  refine (hb_run CST XGL HCST HXGL HCSTF HCSTQ nW khi E TAG A0 Kc rho tp p n t jv keep HKc Hp12 Hn13 HL HCLS Hii HBIG HR HJMIN HKEEP (trS ok _) _ _ _ A' rho1' rhoE tpE HDO HLK);
    intros; [apply JOK1_S | apply JOKP_S | apply JOK2_S]; assumption.
Qed.
Theorem hb_tagE : ltac2:(tb__ "0|1|
S16S18S0S0A2A1M0G0S29R2A1S2aR2A1S0S28R5R1A2S3S28S5bR2A2S2S40S5cR2A2S41R2S5dA2A2A2S4F_;F_;Fa;S0S28R6R1A2S5S5eR2A1A1F_;Fa;S14S13S4bS56R3R2R1A3S7fRaR9R3R4R2A5F_;FE;Fkhi;FnW;F_;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTF HCSTQ nW khi E TAG. unfold HBIGNE_stmt, econtN.
  intros A0 Kc rho tp p n t jv keep HKc Hp12 Hn13 HL HCLS Hii HBIG HTJV HR HJMIN HKEEP A' rho1' rhoE tpE HDO HLK.
  refine (hb_run CST XGL HCST HXGL HCSTF HCSTQ nW khi E TAG A0 Kc rho tp p n t jv keep HKc Hp12 Hn13 HL HCLS Hii HBIG HR HJMIN HKEEP (trC _) _ _ _ A' rho1' rhoE tpE HDO HLK);
    intros; [apply JOK1_C | apply JOKP_C | apply JOK2_C]; assumption.
Qed.
End F0A_hbN_asm.

(* [comment removed for export] *)
Module SegQIF_exit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@Corelib.Init.Datatypes"; "prod"; "nat"; "bool"; "cons"; "list"; "pair"; "true"; "app"; "nil"; "option"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "it_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "sv"; "SExt"; "holds"; "sobj"; "sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "aa_cache_inited"; "cs_cache"; "aa_q_global"; "aa_q_thread"; "mkQB"; "aa_geom"; "ag_spacebeg"; "ageom"; "cs_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "RTC_A"; "cells_ok"; "rtc_cells"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "lt"; "add"; "mul"; "pow"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "QW"; "@Stdlib.Lists.List"; "In"; "Forall2"; "existsb"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel"; "drainA"; "drain_grows"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env"; "qienvF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs"; "VSM"; "ZUM"; "m_Ly"; "mcert"; "REFOBJ_KO"; "S7"; "XROs"; "ZD_KO"; "dst_cellsM"; "m_Lx"; "vCHq"; "zhiM"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "max_count"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "qienv"; "zloQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.SegQIF_glue"; "ENVM"; "zbMq"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "in_zone"; "zdesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "pre_facts"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith"; "QIV"; "vb_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue"; "dspec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SegQIF_cont"; "DZM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib"; "ro_cond"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQIF_env SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dq.SegQCF_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.SegQCF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dt.SegQIF_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.SegQIF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dv.SegQIF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SegQF_ri OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SegQIF_cont.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma K0_id_boundM : ltac2:(tb__ "0|1|
S5dS1cS12SaS39Q40A1A1SaS5aA1S59S0S0S5eR8A1S3S2dZ1R3A2S2dR3Z1eA2A2S2S8S1dR9A1ScA3S3fRbRaR9R8R7R6A6S36S0R5SdS0S25S34RbR6A2M0A1S1eG0A1A3A3S3S2dZ0R6A2S2fR6S32Z2Z1cA2A2A2F_;F_;F_;F_;F_;Fx;Fc;Fmd;Ftr;Ftp;Fr;FA;FKc;").
Proof.
  intros Kc A r tp tr md c x HKc Hc HCI HK Hx. pose proof HK as (HA & _).
  pose proof (K0_laws Kc HKc) as HL. destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [_ _ _ _ _ _ HCLS _ _ _ _ _ _].
  pose proof (HCLS HCI c Hc) as CV. pose proof (cv_bounds _ _ _ _ _ CV) as (_ & B2 & B3 & _).
  pose proof HA as (_ & _ & _ & HRest & _). cbn zeta in HRest. destruct HRest as (_ & _ & Hprim & _ & (HQP & _) & _). destruct Hprim as (_ & _ & _ & PC).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.RebuildD.entry_cls_pureQ _ A c Hc (PC c Hc) HQP) as (_ & _ & _ & _ & _ & _ & HIDS & _).
  destruct (HIDS x ltac:(rewrite app_assoc; apply in_or_app; left; exact Hx)) as (X0 & _ & X2).
  pose proof (Size_facts c Hc) as (SZ & _). unfold cls_of in B2, B3. unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in B3. lia.
Qed.

Lemma dst_cellsM_in : ltac2:(tb__ "0|1|
S0S7S58R1S33R2A1A2S36S6S6S0S7A2M0S15A2SbG0S15SbS0S7S31Z4S2eR2A1A2U4A4S16ScQ20S4bR2A1A3A4S49R3A1A3F_;Fi;Fn;").
Proof.
  intros n i Hi. unfold dst_cellsM. apply (proj1 (in_rev _ _)). apply in_map_iff. exists i. split; [reflexivity|]. unfold idxs. apply in_seq. lia.
Qed.

Section ExitM.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Variables (n : Z) (g vb : bool) (D : mdata).
Hypothesis HC : ltac2:(tb__ "0|0|
S44Vn;Vg;Vvb;VD;A4").

Lemma qif_x1 : ltac2:(tb__ "0|8|
S1cS0S0S0S7S6S0S0A2M0SaG0A1SaS1bA1M1G1S12SaS39Q40A1M2A1S4fS2G1S20RcA1SeS1bA1A3S2S8S1dRdA1ScA3S3eVA0;ReA2S2G1S1fRfA1S9S1bS21ReS9G0RaR9A3RdA3SdS1bR8R7A3A3A3S3S2dZ1S11RbA1M3A2S2dG3Z1eA2A2S2S0S53S11RcA1A1Vn;A3S2S0S2eS10S0S1eS34R12S11RdA1M4A2A1A2A1S50G4A1A3S2S8S3cS11ReA1M5S34R13G5A2A2Vg;A3S56Vn;R14S11RfA1RbA4S3aS1aS3dS3fVKc;A1M6VA0;Vrho0;S3bR15S11R10A1A2R14R12R11S9G0R10RfA3ReRdAaS4aVD;A1RcRbRaA6S5S12S12S3S3aS1aS3dG6VA0;Vrho0;S3bR17S11R12A1A2R16R14R13S9G0R12R11A3R10RfAaS43VD;A1R1RdRcA6S3S1S2G2S14R2R1A2S14RfR1A2A3Fi;S0S4S3S2dS51S23S22R18A1A1S11R13A1A2M7R1A2S2fR1S30G7Z80A2A2A2A1S2SfS39Q8A1A1S26S1aS13R3A1R2A3S26S1aS13R10A1R2A3A3F_;Fz;A2A2Lrho3;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it its tmp' rest rho tp [tr [ms md]] HTH HCI HQP HGL C1 Hn HFULL HGR (E200 & E201 & E221 & E222 & E223 & E224 & E225 & ECH) H.
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (c := it_cls it) in *. set (A1 := drainA A c) in *.
  assert (EG : aa_geom A = aa_geom A0) by (destruct HQP as (ESB & _); unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A1 rho tp _ _ HK) as [HG HRIG _ _ _ HLEN HCLS _ _ _ _ _ _]. change (aa_geom A1) with (aa_geom A) in HG, HRIG.
  destruct HRIG as (E151 & E152 & E155 & E156).
  assert (HLA : (Z.to_nat c < length (aa_cls A))%nat) by (unfold A1, drainA in HLEN; cbn [aa_cls] in HLEN; rewrite length_list_upd in HLEN; lia).
  pose proof (HCLS HCI c C1) as CV1. change (aa_geom A1) with (aa_geom A) in CV1. unfold A1 in CV1. rewrite (drainA_clsM A c HLA) in CV1.
  set (cs := cls_of A c) in *. set (SB := ag_spacebeg (aa_geom A)) in *. set (nf := Z.of_nat (length (cs_free_array cs))) in *.
  destruct (kchunks_facts c C1) as (KC & KMX & _). rewrite Hn in KC, KMX.
  assert (NF0 : 0 <= nf) by (unfold nf; lia). assert (HFL : length (cs_cache cs) = (Z.to_nat n + Z.to_nat n)%nat) by lia.
  assert (KEEP : drain_keep c cs = Z.to_nat n) by (unfold drain_keep; rewrite Hn, HFL; lia).
  assert (EFA1 : cs_free_array (drain_cs c cs) = cs_free_array cs ++ skipn (Z.to_nat n) (cs_cache cs)) by (unfold drain_cs; cbn [cs_free_array]; rewrite KEEP; reflexivity).
  assert (LFA1 : Z.of_nat (length (cs_free_array (drain_cs c cs))) = nf + n) by (rewrite EFA1, length_app, length_skipn, HFL; unfold nf; lia).
  assert (EMF1 : cs_mapped_free_array (drain_cs c cs) = if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs).
  { unfold drain_cs. cbn [cs_mapped_free_array]. fold cs in HGR. rewrite HGR. unfold kFreeArrayMapSize. destruct g; reflexivity. }
  pose proof (cv_fa_bounds _ _ _ _ _ CV1) as (FC1 & FC2 & FC3). rewrite LFA1 in FC2. rewrite EMF1 in FC1, FC2, FC3. unfold kFreeArrayMapSize in FC1.
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _ & _). fold SB in S1, S2.
  pose proof (topG_range (aa_geom A)) as TG. unfold HIGH_SHADOW_END, kFreeArraySize in *. rewrite kSpaceSize_val in S2.
  assert (RIv : region_info SB c = SB + 2 ^ 37 + 128 * c) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (FAv : free_array SB c = SB + c * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  assert (GIF : cs_mapped_free_array cs <= (if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs) <= cs_mapped_free_array cs + 262144) by (case g; lia).
  assert (MF0 : 0 <= cs_mapped_free_array cs <= 536870912) by (clear - FC1 FC2 FC3 NF0 KC GIF; lia).
  assert (ERI : bv_unsigned (eval rho vRI) = SB + 2 ^ 37 + 128 * c) by (unfold vRI; cbn [eval]; rewrite E225; fold SB; rewrite RIv, u64_lit by lia; reflexivity).
  assert (Edst : bv_unsigned (eval rho dstM) = SB + c * 2 ^ 32 + 3758096384 + 4 * nf).
  { unfold dstM. rewrite U_add, U_add, U_add, !U_sll_lit. unfold vSB, vNF. cbn [eval]. rewrite E200, E155, E221. fold SB nf. rewrite !u64_lit by lia. change (32 mod 64) with 32. change (2 mod 64) with 2.
    unfold M64v. rewrite (Z.mod_small (c * 2 ^ 32)) by lia. rewrite (Z.mod_small (c * 2 ^ 32 + 3758096384)) by lia. rewrite (Z.mod_small (SB + (c * 2 ^ 32 + 3758096384))) by lia.
    rewrite (Z.mod_small (nf * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. lia. }

  set (xi := fun i : nat => nth (Z.to_nat n + i) (cs_cache cs) 0).
  assert (XIN : forall i, (i < Z.to_nat n)%nat -> nth_error (cs_cache cs) (Z.to_nat n + i) = Some (xi i)) by (intros i Hi; unfold xi; apply nth_error_nth'; lia).
  assert (HXI : forall i, (i < Z.to_nat n)%nat -> 0 <= xi i < 2 ^ 28).
  { intros i Hi. apply (K0_id_boundM Kc A1 rho tp tr md c (xi i) HKc C1 HCI HK). unfold A1. rewrite (drainA_clsM A c HLA). fold cs. rewrite EFA1.
    apply in_or_app. left. apply in_or_app. right. apply (nth_error_In _ i). rewrite nth_error_skipn. exact (XIN i Hi). }
  pose proof (cv_ri_au _ _ _ _ _ CV1) as K_au. pose proof (cv_ri_mu _ _ _ _ _ CV1) as K_mu. pose proof (cv_bounds _ _ _ _ _ CV1) as (_ & BAU & BMU & _).
  assert (K_dst : forall i, (i < Z.to_nat n)%nat -> cell_ok (view segsA (rm rho)) (mkACell (free_array SB c + 4 * nf + 4 * Z.of_nat i) 4 (xi i))).
  { intros i Hi. pose proof (cv_fa_cells _ _ _ _ _ CV1 (length (cs_free_array cs) + i) (xi i)
                               ltac:(rewrite EFA1; rewrite nth_error_app2 by lia; replace (length (cs_free_array cs) + i - length (cs_free_array cs))%nat with i by lia; rewrite nth_error_skipn; exact (XIN i Hi))) as X0.
    fold SB in X0. rewrite Nat2Z.inj_add in X0. fold nf in X0. replace (free_array SB c + 4 * (nf + Z.of_nat i)) with (free_array SB c + 4 * nf + 4 * Z.of_nat i) in X0 by lia. exact X0. }
  fold SB in K_au, K_mu. rewrite FAv in K_dst. cbn [cs_allocated_user cs_mapped_user drain_cs] in BAU, BMU. unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in BMU.

  set (R := map carve_obj [riOS n g; dstOS n]). set (rho3 := rho_absorb rho R (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (keepN (m_Lx D) 2) R vRI 0 128 _ Hsm (c_Lxobjs n g vb D HC) ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite ERI; lia) ltac:(rewrite ERI; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (keepN (m_Lx D) 2) R dstM 0 (4 * n) (dst_cellsM n) Hsm (c_Lxobjs n g vb D HC) ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside, dst_cellsM; apply Forall_rev; apply Forall_map_in; intros i Hi; apply In_idxs in Hi; cbn; lia) ltac:(rewrite Edst; lia) ltac:(rewrite Edst; lia)) as [AV2 PR2].
  fold rho3 v3 in AV1, PR1, AV2, PR2. rewrite ERI in AV1, PR1. rewrite Edst in AV2, PR2.
  set (ri := SB + 2 ^ 37 + 128 * c) in *. set (da := SB + c * 2 ^ 32 + 3758096384 + 4 * nf) in *.
  assert (Enf1 : eval rho (SAlu ALU_ADD vNF (SLit n)) = Z_to_bv 64 (nf + n)) by (apply (ev_add_lit rho vNF nf n); [unfold vNF; cbn [eval]; exact E221 | lia | lia | lia]).
  assert (Emf1 : eval rho (if g then SAlu ALU_ADD vMFA (SLit 262144) else vMFA) = Z_to_bv 64 (if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs)).
  { case g; [apply (ev_add_lit rho vMFA (cs_mapped_free_array cs) 262144); [unfold vMFA; cbn [eval]; exact E222 | lia | lia | lia] | unfold vMFA; cbn [eval]; exact E222]. }
  assert (C0 : cell_ok v3 (mkACell (ri + 0) 8 0)) by exact (av_cell v3 ri 0 8 _ _ rho (fun j => AV1 _ _ _ j (or_introl eq_refl)) eq_refl).
  assert (C16 : cell_ok v3 (mkACell (ri + 16) 8 (nf + n))) by exact (av_cell v3 ri 16 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_introl eq_refl))) Enf1).
  assert (C24 : cell_ok v3 (mkACell (ri + 24) 8 (if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs))) by exact (av_cell v3 ri 24 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) Emf1).
  assert (C32 : cell_ok v3 (mkACell (ri + 32) 8 (cs_allocated_user cs))) by exact (av_cell v3 ri 32 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) E223).
  assert (C40 : cell_ok v3 (mkACell (ri + 40) 8 0)) by exact (av_cell v3 ri 40 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) eq_refl).
  assert (C48 : cell_ok v3 (mkACell (ri + 48) 8 (cs_mapped_user cs))) by exact (av_cell v3 ri 48 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) E224).
  assert (C56 : cell_ok v3 (mkACell (ri + 56) 8 0)) by exact (av_cell v3 ri 56 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) eq_refl).
  assert (C68 : cell_ok v3 (mkACell (ri + 68) 1 0)) by exact (av_cell v3 ri 68 1 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) eq_refl).
  assert (Cd3 : forall i, (i < Z.to_nat n)%nat -> cell_ok v3 (mkACell (da + 4 * Z.of_nat i) 4 (xi i))).
  { intros i Hi. apply (av_cell v3 da (4 * Z.of_nat i) 4 (SExt true 32 (vCHq i)) (xi i) rho (fun j => AV2 _ _ _ j (dst_cellsM_in n i Hi))).
    unfold vCHq. cbn [eval]. rewrite (ECH i Hi). fold cs. fold (xi i). apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3.sext32_small. pose proof (HXI i Hi). lia. }
  set (P := fun z : Z => (ri <= z < ri + 128) \/ (da <= z < da + 4 * n)).
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (INRG : forall x, in_ranges rho R x -> P (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold P. destruct Ho as [<-|[<-|[]]]; unfold carve_obj, riOS, dstOS, carved in Hz; rewrite obj_range_mk in Hz by lia; cbn [fst snd] in Hz; rewrite ?ERI, ?Edst in Hz; fold ri da in Hz; lia. }
  destruct (absorb_out rho R (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (VD : forall z, da <= z < da + 4 * n -> v3 z = v z).
  { intros z Hz. set (i := Z.to_nat ((z - da) / 4)).
    pose proof (Z.div_pos (z - da) 4 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_lt_upper_bound (z - da) 4 n ltac:(lia) ltac:(lia)) as D1.
    pose proof (Z.div_mod (z - da) 4 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (z - da) 4 ltac:(lia)) as MB.
    assert (Hi : (i < Z.to_nat n)%nat) by (unfold i; lia).
    apply (cell_ok_same v v3 _ (K_dst i Hi) (Cd3 i Hi)). cbn [c_addr c_w]. unfold i. rewrite Z2Nat.id by lia. lia. }
  assert (VO : forall z, ~ (ri <= z < ri + 128) -> v3 z = v z).
  { intros z Hz. destruct (Z_le_dec da z) as [L1|L1]; [destruct (Z_lt_dec z (da + 4 * n)) as [L2|L2]; [exact (VD z (conj L1 L2))|]|]; apply FR; unfold P; lia. }
  assert (HK3 : K0 Kc A1 rho3 tp tr md).
  { apply (K0_ri_blind Kc A1 rho rho3 tp tr md c HKc C1 HCI); try (intros; reflexivity); try exact HK.
    all: change (ag_spacebeg (aa_geom A1)) with SB; rewrite ?RIv; fold ri; fold v3 v.
    all: unfold A1; rewrite ?(drainA_clsM A c HLA); fold cs; rewrite ?LFA1, ?EMF1; cbn [cs_allocated_user cs_mapped_user drain_cs].
    all: unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted.
    - exact VO.
    - intros z Hz. exact (PR1 z ltac:(lia)).
    - intros a0 Ha0. apply FRrm. unfold P, ri, da. rewrite u64_lit by (unfold IMG_LO, IMG_HI in Ha0; lia). unfold IMG_LO, IMG_HI in Ha0. lia.
    - exact C0.
    - exact C16.
    - exact C24.
    - exact C32.
    - exact C40.
    - exact C48.
    - exact C56.
    - exact C68. }
  assert (PDZ : forall z, P z -> DZ A1 c z).
  { intros z Hz. unfold DZ. cbv zeta. change (aa_geom A1) with (aa_geom A). fold SB. rewrite RIv, FAv. unfold kRegionInfoStride, kFreeArraySize. unfold P, ri, da in Hz.
    destruct Hz as [Hz|Hz]; [right; left; lia | right; right; left; clear - Hz FC2 FC3 NF0 KC GIF; lia]. }
  destruct (CR_drain (K0 Kc) HL (K0_secband Kc) A1 a s (it :: its) tmp' rest c HTH HCI HGL C1 rho tp tr md v v3 n0 nd HK) as (HCB3 & HRM3); [ | | exact HCB | exact HRM | ].
  { intros z Hz. apply FR. intros HP. exact (Hz (PDZ z HP)). }
  { intros z HB Hd. rewrite FR; [exact Hd|]. unfold P, ri, da. unfold bandz, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HB. lia. }
  assert (HF3 : FRM A0 rho0 rho3).
  { apply (FRM_absorb_QFP A0 rho0 rho rho3 P PD ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)); [| exact FR | exact FRrm | exact HFRM].
    intros z Hz. split; [exact (DZ_QFPM A1 A0 c z C1 EG (PDZ z Hz))|]. unfold P, ri, da in Hz. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. lia. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (m_Lx D) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho (m_Lx D) (keepN (m_Lx D) 2) R tp tr ms md (c_Lxobjs n g vb D HC) HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  exists rho3. split; [|split; [intros i; reflexivity|]].
  - split; [exact (proj1 HU)|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact HK3|]. split; [exact HCB3|]. split; [exact HRM3 | exact HF3].
  - intros z Hz. apply VO. rewrite RIv in Hz. exact Hz.
Qed.
End ExitM.

Lemma cell_ok_tr : ltac2:(tb__ "0|0|
S27S27S0S7S0S0S3S2dR4R1A2S2fR1S30R4S2eR3A1A2A2A2S2SfS39Q8A1A1R6R2A1R7R2A1A3F_;Fz;S28R6S29R4R3R2A3A2S28R6S29R5R4R3A3A2F_;F_;Fv;Fk;Fa;Fm';Fm;").
Proof. intros m m' a k v HE H j Hj. cbn [c_addr c_w RtCells.c_val] in *. rewrite HE by lia. exact (H j Hj). Qed.

Lemma qienv_F : ltac2:(tb__ "0|0|
S1cS6S0S0A2S12S0S0S54R5R4R3R2R1A5S40R6R5R4R3R2A5F_;Fst;Ft;Fr;Fit;FA;").
Proof. intros A it r t st [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17]. constructor; try assumption. lia. Qed.

Lemma inz_KO : ltac2:(tb__ "0|0|
S1cS6S0S0A2S12S0S0S40R5R4R3R2R1A5S8S60R7R5A2S4dS19S17R6A1S5fS65A1A3S37S18S5cS5bR7S57R9R8A2S55S4cS42R3A1A5S45R3A1S48R3A1A5F_;F_;Fvb;F_;Fst;Ft;Fr;Fit;FA;").
Proof.
  intros A it r t st QE vb HTOP HFp.
  apply (in_zone_ext_list r (zbQ (ag_thread (aa_geom A)) (ag_ctx (aa_geom A)) (ag_spacebeg (aa_geom A)) (fst it) (it_ab it) (topG (aa_geom A))
                                 (ag_thread (aa_geom A) + 208 + 80 * it_cls it) (ag_thread (aa_geom A) + 208 + 80 * it_cls it) (Sh (fst it))) zloQ zhiQ (if vb then ALLZ else removelast ALLZ)).
  - unfold REFOBJ_KO, ZD_KO. apply Forall2_app; [|apply Forall2_app; [|apply Forall2_app]].
    + apply (inz_ishF A it r t st QE). destruct vb; cbn; tauto.
    + apply (inz_fixF A it r); [destruct vb; cbn; tauto | destruct vb; cbn; tauto | exact HTOP | exact HFp].
    + apply (inz_rtiF A it r t st QE); destruct vb; cbn; tauto.
    + pose proof (inz_itmF A it r t st QE vb (if vb then ALLZ else removelast ALLZ) ltac:(intros z Hz; destruct vb; cbn in Hz |- *; tauto) ltac:(intros ->; cbn; tauto)) as X.
      unfold N_itmF, ZD_itmF in X. cbn [map app] in X. apply Forall2_cons_iff in X as [_ X].
      unfold N_itmF. destruct vb; cbn [tl app map] in X |- *; exact X.
  - unfold ZD_KO, ZD_fix, ZD_rti. destruct vb; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; (split; [cbn; tauto | split; [reflexivity | split; reflexivity]]).
Qed.

Lemma inVSM : ltac2:(tb__ "0|0|
S1S2S8S38S1S68R1A1S41A3ScA3S36S1R2S41A3F_;Fv;").
Proof. intros v H. apply existsb_exists in H as (x & Hx & E). apply Pos.eqb_eq in E. subst x. exact Hx. Qed.
Lemma UZ57 : ltac2:(tb__ "0|0|
S8S7S36S7R1S9S7U5S9S7U7SeS7A1A3A3A3S36S7R2S42R3A1A3F_;Fz;Fvb;").
Proof. intros vb z Hz. destruct vb; cbn in Hz |- *; tauto. Qed.

Lemma ro_XRO : ltac2:(tb__ "0|5|
S1cS12S8S24S2bS26S1aS13R3A1A2S2cS2aR1A2A2S4dS64S67R5R4A2S4eS52S6S6S6S6S15S0A2M0S0A2M1SaS6S6S0S7A2S15A2A1M2A2M3S0A2M4S52G3G4Lk;R1G1G2G1G4Lp;R2G0S0G0G4Lp0;R2S15S0SbG3S0SbG1G2SbG0S0SbS15S0R2R1A4R3A4R5A4Z0A4Llo;Lb;X6x1Lhi;Lp0;X6x1Lcs;Lp;X6x1Lk;S47R3A1A4A3F_;FG;Fg;Frho;FA0;").
Proof.
  intros A0 rho g G HR. unfold XROs, pgbS, cfcS, cfbS. destruct g; cbn [map]; repeat apply Forall_cons; try apply Forall_nil; apply (ro_cond_intro A0 (mkSC 0 0 0));
    try (unfold PG; lia); try reflexivity; try (unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia).
  all: try (intros z Hz; split; [right; right; unfold qrtc2_zone; lia | unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; lia]).
  all: repeat apply Forall_cons; try apply Forall_nil.
  all: cbv beta iota; eexists; (split; [reflexivity|]); rtc_cellx HR.
Qed.

Section OutM.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Variables (n : Z) (g vb : bool) (D : mdata).
Hypothesis HC : ltac2:(tb__ "0|0|
S44Vn;Vg;Vvb;VD;A4").

Lemma qif_out : ltac2:(tb__ "0|8|
S1cS0S0S0S7S6S0S0A2M0SaG0A1SaS1bA1M1G1S12S12SaS39Q40A1M2A1S4fS0S0S2G1S20RfA1SeS1bA1A3S2S8S1dR10A1ScA3S0S35R12R1A2S35VA0;R2A2F_;Fz;S3eVA0;R12A2S2G1S1fR13A1S9S1bS21R12S9G0ReRdA3R11A3SdS1bRcRbA3A3A3S2S0S53S11RfA1A1Vn;A3S2S0S2eS10S0S1eS34R15S11R10A1M3A2A1A2A1S50G3A1A3S2S8S3cS11R11A1M4S34R16G4A2A2Vg;A3S2S8Vvb;S63R12A1A3S40R18R13ReRbRaA5S0S4S66R1aS11R15A1M5R1A3A1S2SfS39Q8A1A1S26S1aS13R12A1R2A3S26S1aS13R11A1R2A3A3F_;Fz;S56Vn;R1aG5R11A4S62R12R16S34R1bS11R16A1A2ReRdA5S3aS1aS3dS3fVKc;A1M6VA0;Vrho0;S3bR1cS11R17A1A2R1bR19R18S9G0R17R16A3R15R14AaS43VD;A1R13R11R10A6S5S12S12S3S3aS1aS3dG6VA0;Vrho0;S3bR1eS11R19A1A2M7R1dR1bR1aS9G0R19R18A3R17R16AaS46Vvb;A1R1R13R12A6S3S54G7R19R1R11R10A5S3S1S36S1R1S41A3S4S2S1R2PceA3A1S4S2S1R3PcfA3A1S2G2S14R5R4A2S14R19R4A2A3F_;F_;F_;Fv;S3S1S69R1S61A2S2G2S14R3R2A2S14R17R2A2A3F_;Fv;S2S27S26S1aS13R1A1A2S26S1aS13R15A1A2A3A2A2A2A2Lrho7;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fst;Ft;Fw;Ftp;FrhoB;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it its tmp' rest rho rhoB tp [tr [ms md]] t st HTH HCI HQW HQP HGL Hn HFULL HGR EVB QEB HVW HENV HQV H0.
  pose proof HENV as (E200 & E201 & E221 & E222 & E223 & E224 & E225 & ECH).
  assert (EG : aa_geom A = aa_geom A0) by (destruct HQP as (ESB & _); unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  pose proof (K0_laws Kc HKc) as HL. set (c := it_cls it) in *. set (A1 := drainA A c) in *.
  set (J := JRI (K0 Kc) A0 rho0 A1 a n0 nd (it :: its) tmp' rest).
  pose proof (JRI_stable (K0 Kc) HL A0 rho0 A1 a n0 nd (it :: its) tmp' rest) as HSTB.
  destruct (proj2 H0) as (HK1 & HCB1 & HRM1 & HFRM1). cbn [w_tr w_cfg cfg_model fst snd] in HK1, HCB1, HRM1, HFRM1.
  destruct (kq_facts segsA (K0 Kc) HL A1 rho tp _ _ HK1) as [HG HRIG HRTC _ HST HLEN HCLS _ _ _ _ HKTOP _]. change (aa_geom A1) with (aa_geom A) in HG, HRIG, HRTC, HST.
  destruct HRIG as (E151 & E152 & E155 & E156).
  destruct (geoM_nums A it rhoB t st QEB) as (C1 & FAv & S1 & S14 & TG & UF & R1 & ABU). cbv zeta in FAv, S1, S14, UF, R1. fold c in C1, FAv, UF, R1.
  pose proof (qf_nums A it rhoB t st QEB) as (T0 & T1 & C0 & C1' & _ & _ & _). pose proof (qf_wins A it rhoB t st QEB) as (WTI & WCI & WTB & WCB & WTC & WTS & WCS).
  pose proof (qf_Sh A it rhoB t st QEB) as (SH0 & SH1 & L0 & L1).
  destruct (kchunks_facts c C1) as (KC & KMX & _). rewrite Hn in KC, KMX.
  assert (HLA : (Z.to_nat c < length (aa_cls A))%nat) by (unfold A1, drainA in HLEN; cbn [aa_cls] in HLEN; rewrite length_list_upd in HLEN; lia).
  pose proof (HCLS HCI c C1) as CV1. change (aa_geom A1) with (aa_geom A) in CV1. unfold A1 in CV1. rewrite (drainA_clsM A c HLA) in CV1.
  set (cs := cls_of A c) in *. set (SB := ag_spacebeg (aa_geom A)) in *. set (T := ag_thread (aa_geom A)) in *. set (pce := T + 208 + 80 * c).
  assert (HFL : length (cs_cache cs) = (Z.to_nat n + Z.to_nat n)%nat) by lia.
  assert (KEEP : drain_keep c cs = Z.to_nat n) by (unfold drain_keep; rewrite Hn, HFL; lia).
  assert (LCA1 : Z.of_nat (length (cs_cache (drain_cs c cs))) = n) by (unfold drain_cs; cbn [cs_cache]; rewrite KEEP, length_firstn, HFL; lia).
  pose proof (cv_max _ _ _ _ _ CV1) as C_max. pose proof (cv_size _ _ _ _ _ CV1) as C_sz. pose proof (cv_count _ _ _ _ _ CV1) as C_cnt. unfold pc_entry in C_max, C_sz, C_cnt.
  fold T pce in C_max, C_sz, C_cnt. rewrite <- KMX in C_max. rewrite LCA1 in C_cnt.

  pose proof QEB as [_ _ _ _ _ _ QCVB _ _ QTB QSTB _ _ _ _ QPR _]. fold c cs in QCVB.
  set (xi := fun i : nat => nth (Z.to_nat n + i) (cs_cache cs) 0).
  assert (XIN : forall i, (i < Z.to_nat n)%nat -> nth_error (cs_cache cs) (Z.to_nat n + i) = Some (xi i)) by (intros i Hi; unfold xi; apply nth_error_nth'; lia).
  assert (NDZ_T : forall z, pce + 4 <= z < T + 4096 -> ~ DZM A c z).
  { intros z Hz HZ. unfold DZM in HZ. cbv zeta in HZ. fold SB T in HZ. rewrite FAv in HZ.
    assert (SHL : 0x7fff8000 <= Sh (SB + c * 2 ^ 32 + 3758096384)) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos (SB + c * 2 ^ 32 + 3758096384) 8 ltac:(unfold HIGH_SHADOW_END in S1; lia) ltac:(lia)); lia).
    unfold SHADOW_BAND_HI, HIGH_SHADOW_END in *. fold SB T in WTS, WTB. unfold pce in Hz. clear - Hz HZ C1 S1 WTS WTB SHL. lia. }
  assert (C_chk : forall i, (i < Z.to_nat n)%nat -> cell_ok (view segsA (rm rho)) (mkACell (pce + 16 + 4 * (n + Z.of_nat i)) 4 (xi i))).
  { intros i Hi. pose proof (cv_chunks _ _ _ _ _ QCVB (Z.to_nat n + i)%nat (xi i) (XIN i Hi)) as X0. unfold pc_entry in X0. fold T pce in X0.
    replace (pce + 16 + 4 * Z.of_nat (Z.to_nat n + i)) with (pce + 16 + 4 * (n + Z.of_nat i)) in X0 by lia.
    apply (cell_ok_tr (view segsA (rm rhoB))); [|exact X0]. intros z Hz. apply HVW. apply NDZ_T. unfold pce in Hz. cbn [Z.of_nat] in Hz. lia. }
  assert (HT15 : view segsA (rm rho) (fst it - 15) = Some (Z_to_bv 8 t)).
  { rewrite HVW; [exact (proj2 QTB)|]. apply (floc_outM A it rhoB t st QEB). unfold FLM. right; right; right; right; right; left.
    pose proof QEB as [_ _ _ _ QGEO _ _ _ _ _ _ _ _ _ _ _ _]. unfold qgeo in QGEO. destruct QGEO as (_ & _ & _ & RZ & _ & EU & _). lia. }
  assert (HSTC : cell_ok (view segsA (rm rho)) (mkACell (T + 2784) 8 st)).
  { apply (cell_ok_tr (view segsA (rm rhoB))); [|exact (proj2 QSTB)]. intros z Hz. apply HVW. apply NDZ_T. cbn [Z.of_nat] in Hz. lia. }

  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  set (tO := T_out n g vb (m_Ly D)).
  assert (HT : SPA segsA TJ (s_C tO) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H0) | exact I]).
  set (dsD := DSO n g pce).
  assert (EcbC : eval rho cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply ev_add_lit; [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (Eent : eval rho entQ = Z_to_bv 64 pce).
  { apply bv_eq. unfold entQ, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC. cbn [eval]. rewrite E200, !u64_lit by (unfold pce; lia). unfold M64v.
    rewrite (Z.mod_small (c * 80)) by lia. rewrite Z.mod_small by lia. unfold pce. lia. }
  assert (HR : cells_ok (view segsA (rm rho)) (rtc_cells RTC_A (aa_geom A))) by exact HRTC.
  assert (ZT : forall z, T + 208 <= z < T + 2768 -> QRD A0 z /\ ~ (SHADOW_BAND_LO <= z < SHADOW_BAND_HI)).
  { intros z Hz. split; [left; right; left; rewrite <- EG; fold T; lia|]. fold T in WTB. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. clear - Hz WTB. lia. }
  assert (PCEB : 0 <= pce /\ pce + 4096 < 2 ^ 62) by (unfold pce; clear - T0 T1 TG C1; lia).
  assert (ROC : Forall (ro_cond A0 rho) dsD).
  { unfold dsD, DSO. apply Forall_app. split.
    - exact (ro_XRO A0 rho g (aa_geom A) HR).
    - cbn [map]. repeat apply Forall_cons; try apply Forall_nil.
      +
        unfold chkS, ro_cond. split; [exact Eent|]. split; [unfold pce; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold pce; lia|].
        split; [unfold cells_inside, chk_cells; apply Forall_map_in; intros i Hi; apply In_idxs in Hi; cbn; lia|].
        split; [intros z Hz; apply ZT; unfold pce in Hz; lia|].
        intros z Hz. set (i := Z.to_nat ((z - (pce + 16 + 4 * n)) / 4)).
        pose proof (Z.div_pos (z - (pce + 16 + 4 * n)) 4 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_lt_upper_bound (z - (pce + 16 + 4 * n)) 4 n ltac:(lia) ltac:(lia)) as D1.
        pose proof (Z.div_mod (z - (pce + 16 + 4 * n)) 4 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (z - (pce + 16 + 4 * n)) 4 ltac:(lia)) as MB.
        assert (Hi : (i < Z.to_nat n)%nat) by (unfold i; lia).
        exists (16 + 4 * (n + Z.of_nat i)), 4%nat, (vCHq i), (xi i).
        split; [unfold chk_cells; apply in_map_iff; exists i; split; [reflexivity | unfold idxs; apply in_seq; lia]|].
        split; [unfold i; rewrite Z2Nat.id by lia; cbn [Z.of_nat]; lia|].
        split; [unfold vCHq; cbn [eval]; exact (ECH i Hi)|].
        replace (pce + (16 + 4 * (n + Z.of_nat i))) with (pce + 16 + 4 * (n + Z.of_nat i)) by lia. exact (C_chk i Hi).
      + unfold mcS. apply (ro_cond_intro A0 (mkSC 0 0 0)); [exact Eent | clear - PCEB; lia | clear; lia | clear; lia | clear; lia | clear - PCEB; lia | | | reflexivity | ].
        * unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil. cbn. clear. lia.
        * intros z Hz. apply ZT. unfold pce in Hz. clear - Hz C1. lia.
        * repeat apply Forall_cons; try apply Forall_nil. exists (2 * n). split; [reflexivity | exact C_max].
      + unfold cntS. apply (ro_cond_intro A0 (mkSC 0 0 0)); [exact Eent | clear - PCEB; lia | clear; lia | clear; lia | clear; lia | clear - PCEB; lia | | | reflexivity | ].
        * unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil. cbn. clear. lia.
        * intros z Hz. apply ZT. unfold pce in Hz. clear - Hz C1. lia.
        * repeat apply Forall_cons; try apply Forall_nil. exists n. split; [reflexivity|]. replace (pce + 0) with pce by lia. exact C_cnt.
      + unfold szMS. apply (ro_cond_intro A0 (mkSC 0 0 0)); [exact Eent | clear - PCEB; lia | clear; lia | clear; lia | clear; lia | clear - PCEB; lia | | | reflexivity | ].
        * unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil. cbn. clear. lia.
        * intros z Hz. apply ZT. unfold pce in Hz. clear - Hz C1. lia.
        * repeat apply Forall_cons; try apply Forall_nil. exists (Size c). split; [cbn [eval]; exact E201 | exact C_sz]. }
  assert (HOBJ : ss_objs (ax_S (s_C tO)) = keepN (s_C tO) (s_k tO) ++ map dobj dsD) by exact (c_outobjs n g vb D HC pce).
  set (vals := [Z_to_bv 64 n; Z_to_bv 64 (2 * n)]).
  set (rho3 := rho_absorb rho (map dobj dsD) (vms md tp ms)) in *.
  set (rho4 := rho_sets rho3 (combine (s_bs tO) vals)).
  assert (OT : forall v, v <> 206%positive -> v <> 207%positive -> rw rho4 v = rw rho v).
  { intros v N6 N7. unfold rho4. rewrite rho_sets_other; [reflexivity|]. unfold tO, T_out, vals. cbn [s_bs combine map fst In]. intros [X0|[X0|[]]]; congruence. }
  assert (NDB : List.NoDup (map fst (combine (s_bs tO) vals))) by (unfold tO, T_out, vals; cbn [s_bs combine map fst]; repeat constructor; cbn [In]; intuition congruence).
  assert (G206 : rw rho4 206%positive = Z_to_bv 64 n) by (apply (rho_sets_get _ rho3 _ _ NDB); unfold tO, T_out, vals; cbn [s_bs combine In]; tauto).
  assert (G207 : rw rho4 207%positive = Z_to_bv 64 (2 * n)) by (apply (rho_sets_get _ rho3 _ _ NDB); unfold tO, T_out, vals; cbn [s_bs combine In]; tauto).
  destruct (s_step (K0 Kc) HL A0 rho0 (zbMq A it) zloQ zhiM (ZUM vb) (zsepMq A it rhoB t st QEB vb EVB) tO J dsD vals A1 rho tp tr ms md
              (c_out n g vb D HC) HSTB HQW HOBJ eq_refl HT HK1 HFRM1 ROC) as (rho5 & H5 & V5 & RM5 & AG5 & EV5).
  { intros HK3 HF3 EV3. fold rho3 in HK3, HF3, EV3. fold rho3. fold rho4.
    assert (HK4 : K0 Kc A1 rho4 tp tr md).
    { apply (kq_stable segsA (K0 Kc) HL A1 rho3 rho4 tp tr md md); [|apply mat_equiv_refl | exact HK3]. split; [|split].
      - intros v Hv. symmetry. unfold QNPRE in Hv. apply OT; lia.
      - intros l0. unfold rho4. rewrite (proj1 (rho_sets_rl_rm _ rho3)). reflexivity.
      - intros x. unfold rho4. rewrite (proj2 (rho_sets_rl_rm _ rho3)). reflexivity. }
    assert (ERM4 : rm rho4 = rm rho3) by (unfold rho4; apply rm_rho_sets).
    assert (HQV4 : QIV rho4 it (cls_of A1 c) t st).
    { unfold A1. rewrite (drainA_clsM A c HLA). fold cs. unfold QIV in HQV |- *. cbv zeta in HQV |- *. fold c cs in HQV |- *.
      destruct HQV as (V165 & V200 & V201 & V202 & V203 & V204 & V205 & _ & _ & V209 & V210).
      rewrite LCA1, <- KMX, G206, G207. rewrite (OT 165%positive), (OT 200%positive), (OT 201%positive), (OT 202%positive), (OT 203%positive), (OT 204%positive), (OT 205%positive), (OT 209%positive), (OT 210%positive) by discriminate.
      cbn [cs_mapped_user drain_cs]. repeat split; assumption. }
    assert (QE4 : qienv A1 it rho4 t st).
    { apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip.qienv_of_K (K0 Kc) HL A1 a s n0 nd it its tmp' rest rho4 tp tr md t st HTH HCI HGL QPR); [| exact HK4 | rewrite ERM4, EV3; exact HCB1 | exact HQV4 | exact (proj1 QTB) | rewrite ERM4, EV3; exact HT15 | exact (proj1 QSTB) | rewrite ERM4, EV3; exact HSTC].
      fold c. unfold A1. rewrite (drainA_clsM A c HLA). fold cs. rewrite LCA1, <- KMX. lia. }
    pose proof (qienv_F A1 it rho4 t st QE4) as QF4.
    assert (HTOP4 : top_high A1 rho4) by (unfold top_high in *; rewrite !OT by (unfold V_DEPTH; lia); exact HKTOP).
    assert (HFpre1 : Forall (holds rho) (pre_facts DEPTH_R)).
    { pose proof (SPA_facts_hold segsA _ rho (m_Ly D) tp _ H0) as HFa. apply Forall_forall. intros f Hf.
      pose proof (proj1 (forallb_forall _ _) (c_Lypre n g vb D HC) f Hf) as X. apply existsb_exists in X as (f' & Hf' & E). apply sprop_eqb_sound in E. subst f'. exact (proj1 (Forall_forall _ _) HFa f Hf'). }
    assert (HFpre4 : Forall (holds rho4) (pre_facts DEPTH_R)).
    { apply Forall_forall. intros f0 Hf0. apply (holds_agree_vals NPRE rho rho4 f0); [| exact (proj1 (forallb_forall _ _) pre_facts_below f0 Hf0) | exact (proj1 (Forall_forall _ _) HFpre1 f0 Hf0)].
      split; [intros v Hv; symmetry; apply OT; unfold NPRE in *; lia | intros l0; unfold rho4; rewrite (proj1 (rho_sets_rl_rm _ rho3)); reflexivity]. }
    pose proof (qe_E A1 it rho4 t st QE4) as (_ & _ & _ & Erie & Eent4 & Eslot & _). change (aa_geom A1) with (aa_geom A) in Erie, Eent4, Eslot. fold c SB T in Erie, Eent4, Eslot. fold pce in Eent4, Eslot.
    unfold A1 in Eslot. rewrite (drainA_clsM A c HLA) in Eslot. fold cs in Eslot. rewrite LCA1 in Eslot.
    split; [split; [exact HK3 | split; [rewrite EV3; exact HCB1 | split; [rewrite EV3; exact HRM1 | exact HF3]]]|].
    split.
    { pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip.carve_itm A1 it rho4 t st QE4 vb ltac:(intros X0; rewrite EVB in X0; unfold vb_of in X0; apply negb_true_iff in X0; apply Z.eqb_neq in X0; exact X0)) as CI.
      unfold N_itm in CI. cbn [app] in CI. apply Forall_cons_iff in CI as [CI0 CI]. apply Forall_cons_iff in CI as [_ CI]. apply Forall_cons_iff in CI as [CI2 CI]. apply Forall_cons_iff in CI as [CI3 _].
      unfold tO, T_out, N_OUT. cbn [s_N]. repeat apply Forall_cons; try apply Forall_nil; [exact CI0 | exact CI2 | exact CI3]. }
    split.
    { unfold tO, T_out, N_OUT, ZD_OUT, rieS0, entG, slotG. cbn [s_N s_ZDn map carve_obj]. repeat apply Forall2_cons; try apply Forall2_nil; unfold in_zone.
      all: split; [apply UZ57; cbn; tauto|]. all: split; [cbn; lia|]. all: split; [cbn; lia|]. all: right.
      all: unfold carved; rewrite obj_range_mk by lia; unfold zbMq; cbn [fst snd zbM zbQ]; fold SB T c; fold pce; unfold UE in *; rewrite ?Erie, ?Eent4, ?Eslot; lia. }
    split.
    { exact (in_zone_same rho4 _ _ _ _ _ (REFOBJ_KO vb) (ZD_KO vb) (c_outK n g vb D HC) (inz_KO A1 it rho4 t st QF4 vb HTOP4 HFpre4)). }
    intros _. unfold tO, T_out, F_OUT. cbn [s_F]. repeat apply Forall_cons; try apply Forall_nil.
    - cbn [holds branch_taken eval]. rewrite G207. intros HB. unfold bv_eqb in HB. apply Z.eqb_eq in HB. rewrite !u64_lit in HB by lia. lia.
    - cbn [holds eval]. rewrite G206, G207, !u64_lit by lia. lia.
    - cbn [holds eval]. rewrite G207, !u64_lit by lia. lia. }
  fold rho3 in RM5, EV5. fold rho4 in V5, AG5.
  assert (VV5 : forall v, In v VSM -> rw rho5 v = rw rho4 v).
  { intros v Hv. rewrite (V5 v (SVar v)); [reflexivity|]. unfold tO, T_out. cbn [s_M]. unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv]. }
  assert (ERM5 : view segsA (rm rho5) = view segsA (rm rho)) by (rewrite RM5; exact EV5).
  exists rho5. split; [exact H5|]. split; [|split; [intros v Hv N6 N7; rewrite (VV5 v Hv); exact (OT v N6 N7) | split; [|exact ERM5]]].
  -
    destruct (proj2 H5) as (HK5 & HCB5 & _). cbn [w_tr w_cfg cfg_model fst snd] in HK5, HCB5.
    assert (HQV5 : QIV rho5 it (cls_of A1 c) t st).
    { unfold A1. rewrite (drainA_clsM A c HLA). fold cs. unfold QIV in HQV |- *. cbv zeta in HQV |- *. fold c cs in HQV |- *.
      destruct HQV as (V165 & V200 & V201 & V202 & V203 & V204 & V205 & _ & _ & V209 & V210).
      rewrite (VV5 165%positive (inVSM 165%positive eq_refl)), (VV5 200%positive (inVSM 200%positive eq_refl)), (VV5 201%positive (inVSM 201%positive eq_refl)), (VV5 202%positive (inVSM 202%positive eq_refl)), (VV5 203%positive (inVSM 203%positive eq_refl)),
              (VV5 204%positive (inVSM 204%positive eq_refl)), (VV5 205%positive (inVSM 205%positive eq_refl)), (VV5 206%positive (inVSM 206%positive eq_refl)), (VV5 207%positive (inVSM 207%positive eq_refl)), (VV5 209%positive (inVSM 209%positive eq_refl)), (VV5 210%positive (inVSM 210%positive eq_refl)).
      rewrite LCA1, <- KMX, G206, G207. rewrite (OT 165%positive), (OT 200%positive), (OT 201%positive), (OT 202%positive), (OT 203%positive), (OT 204%positive), (OT 205%positive), (OT 209%positive), (OT 210%positive) by discriminate.
      cbn [cs_mapped_user drain_cs]. repeat split; assumption. }
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip.qienv_of_K (K0 Kc) HL A1 a s n0 nd it its tmp' rest rho5 tp tr md t st HTH HCI HGL QPR); [| exact HK5 | exact HCB5 | exact HQV5 | exact (proj1 QTB) | rewrite ERM5; exact HT15 | exact (proj1 QSTB) | rewrite ERM5; exact HSTC].
    fold c. unfold A1. rewrite (drainA_clsM A c HLA). fold cs. rewrite LCA1, <- KMX. lia.
  - intros v Hv. rewrite <- (proj1 AG5 v Hv). apply OT; unfold NPRE in Hv; lia.
Qed.
End OutM.
End SegQIF_exit.

