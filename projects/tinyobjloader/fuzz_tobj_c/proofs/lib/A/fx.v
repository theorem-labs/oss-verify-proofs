(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFw fn ea Musl_wl_out DrvExitStates.

(* [comment removed for export] *)
Module DrvFp.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "nil"; "bool"; "option"; "Some"; "true"; "nat"; "prod"; "cons"; "pair"; "app"; "length"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "sv"; "sstate"; "sprop"; "SLit"; "rl"; "ss_objs"; "cell"; "holds"; "ob_dflt"; "rw"; "DList"; "ob_base"; "ob_cells"; "ob_hi"; "ob_lo"; "agree_below"; "obj_holds"; "obj_range"; "odefault"; "outside_all"; "rm"; "smatch"; "SAlu"; "SVar"; "dflt_writable"; "is_arr"; "mkObj"; "sprop_below"; "ss_facts"; "ss_lenient"; "swf"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "FdChannel"; "WriteEv"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface"; "MSG_REF"; "facts_fp"; "Pre_ref"; "Posts_ref"; "P_ref"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvFp.Fp"; "Kwr"; "Kf"; "EVSr"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "ax_base"; "mkLeafA"; "sym_runA"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvFp.Fp.Inst"; "rho_wl"; "Jp"; "oext"; "f6"; "rho_fin"; "WLF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err.WLerrS"; "Pre_wl2"; "D"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "set_rl"; "obj_nolist"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw"; "ch2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err.WLerr"; "Kw"; "MSG"; "Posts_wl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.DrvFpStates"; "CUTS_FP"; "FUEL_FP"; "O_b2e"; "unlist_at"; "XP1"; "XP2"; "splits_fp"; "unk_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "beval"; "cells_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates"; "axc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "to_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundI SymSoundM SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj SymCall SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SysA MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import SpecConsts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFw DrvFpIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.DrvFpStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma obj_holds_unlist : ltac2:(tb__ "0|0|
S10S61S11S46SdS24S1aR2A1S1cR1A1A3SdS0S18A1S1eR3A1S1S18A1A3S22S33R6R5R4A4S22S33R7R6S74R5A1A4F_;F_;F_;Fl;Fo;Fms;Frho;").
Proof.
  intros rho ms o l Hd Hc (Hb & Hw & Hcl & Hdf & Hi). unfold unk_obj, obj_holds. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi].
  split; [exact Hb|]. split; [intros off Hoff _; apply Hw; [exact Hoff | rewrite Hd; reflexivity]|].
  split; [constructor|]. split; [|exact I].
  intros off Hoff _. cbn. rewrite Hd in Hdf. cbn in Hdf. eexists. apply Hdf; [exact Hoff|].
  rewrite Hc. intros X. apply Exists_exists in X as (c & Hin & _). destruct Hin.
Qed.

Lemma smatch_unlist_at : ltac2:(tb__ "0|0|
S10S13S6S11S46S7S0S3bA1S62A2SdS3S11A1S6bS11S17R5A1R4A3S4S11R3A2A3SdS24S1aR4A1S1cR3A1A3SdS0S18A1S1eR5A1S1S18A1A3SdS2S30S70R8R7A2A1S5A3S27S33RaR9R5A4S27S33RbS70RaR9A2R6A4F_;F_;F_;F_;F_;Fw;Fl;Fo;Fi;FS;Frho;").
Proof.
  intros rho S i o l [tr [ms md]] Hn Hd Hc Hwf Hsm.
  pose proof (nth_error_split3 _ _ _ Hn) as Esplit.
  unfold unlist_at in Hwf |- *. rewrite Hn in Hwf |- *.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hcsr & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  assert (RNG : obj_range rho (unk_obj o) = obj_range rho o) by reflexivity.
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hcsr|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs set_objs]. destruct Hm as (Hall & Hpd & Hfr). rewrite Esplit in Hall, Hpd, Hfr.
  split; [|split].
  - apply Forall_app in Hall as [HA HB]. inversion HB; subst. apply Forall_app. split; [exact HA|].
    constructor; [eapply obj_holds_unlist; eauto | assumption].
  - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd. rewrite map_app in Hpd |- *. cbn [map] in Hpd |- *. rewrite RNG. exact Hpd.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. rewrite Forall_app in Hout |- *. destruct Hout as [HA HB].
    split; [exact HA|]. inversion HB; subst. constructor; [rewrite <- RNG; assumption | assumption].
Qed.

Section Fp.
Variable ok : assn.
Variable J0 : jpredA.

Definition EVSr (k : nat) : list event := ltac2:(tb__ "0|1|
S4cS31Q8A1M0S3bS3eS64A1S4eG0Vk;S41A3A4").
Definition Kwr (k : nat) : jpredA := ltac2:(tb__ "0|1|
S10S0S31Q40A1A1S0S3bA1M0S3aSfG0G0SeVJ0;R5R4R1R2A4SdG0R3SaS3bR1S4bVk;A1A3A3A2Ltr0;A2Lmd;Ltr;Lt;Lr;").

Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd2 : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S0S3bA1S3aVJ0;R4R3R2R1A4SdS3S3cA1S3fS40R2A1S64A2S4S3cS3dS64A1A2A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HokK : ltac2:(tb__ "0|0|
S6S38S33Vok;S49R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S6S7aS33Vok;S49R1A1A3Fk;").

Definition Kf (r1 : valuation) (tp : list word) (k : nat) : jpredA := ltac2:(tb__ "0|1|
S10S0S31Q40A1A1M0S0S3bA1S3aSeSdG0R3Vtp;A3S49Vk;Vr1;R3R2R1A5A2Lmd;Ltr;Lt;L_;").
Lemma J0_mat : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S0S3bA1S3aS3aS88S33R4R2R1A4VJ0;R6R5R4R3A4VJ0;R7R6R5R3A4F_;F_;Fmd';Fmd;Ftr;Ft;Fr;").
Proof. intros r t tr md md' Hme HJ. eapply Hst0; [apply agree_below_refl | exact Hme | exact HJ]. Qed.
Lemma Kf_stable : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S6S46S39S33R1S4aR4R3R2A3A3Flvl;Fk;Ftp;Fr1;").
Proof.
  intros r1 tp k lvl r r' t tr md md' Hag Hme [Ht (tr0 & HJ & Htr)]. split; [exact Ht|].
  exists tr0. split; [eapply J0_mat; eauto | exact Htr].
Qed.
Lemma Kf_okK : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S6S38S33Vok;S4aR3R2R1A3A3Fk;Ftp;Fr1;").
Proof. intros r1 tp k r t tr ms md msv' [_ HK]. exact (HokK k r1 t tr ms md msv' HK). Qed.
Lemma Kf_okP : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S6S7aS33Vok;S4aR3R2R1A3A3Fk;Ftp;Fr1;").
Proof. intros r1 tp k r t tr ms md x8 [_ HK]. exact (HokP k r1 t tr ms md x8 HK). Qed.
Lemma Kw0_of_J0 : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S0S3bA1S3aVJ0;R4R3R2R1A4S49U0R5R4R3R2A5F_;Fmd;Ftr;Ft;Fr;").
Proof. intros r t tr md HJ. exists tr. split; [exact HJ|]. unfold EVSr. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma okK_J0 : ok_frameA segs ok J0.
Proof. intros r t tr ms md msv' HJ. exact (HokK 0%nat r t tr ms md msv' (Kw0_of_J0 _ _ _ _ HJ)). Qed.

Section Inst.
Variable W : axst. Variables S6 Cs : sstate. Variable o8 : sobj. Variable bl : list bexp. Variable s : wsub. Variable R : list sobj.
Variables T Tf F : axst. Variables G1 G2 G2u G3 : sstate. Variable sp : wsub. Variable EX : list sprop.
Hypothesis HrunW : ltac2:(tb__ "0|1|
SdS3S0S4fA1M0A1S54S75S6eS6dS43S5A5S4G0S8S4fS53VW;S79A2S1S4fA1A3A2A3").
Hypothesis HnW : ss_next (ax_S W) = 116%positive.
Hypothesis HXW : ax_X W = X_ref.
Hypothesis HbW : ltac2:(tb__ "0|0|
SdS12S52VW;A1S15S34A1A3").
Hypothesis HfW : ltac2:(tb__ "0|0|
SdS0S14A1S2eS50VW;A1A1SaS14VEX;S42A3A3").
Hypothesis Hsplits : ltac2:(tb__ "0|0|
SdS3S13A1S73S50VW;A1A1S4S13VS6;A2A3").
Hypothesis Hfinish : finish_fp S6 = Cs.
Hypothesis Hnl6 : state_nolist S6 = true.
Hypothesis Hrl5 : state_has_rl 5 S6 = false.
Hypothesis Ho8 : ltac2:(tb__ "0|0|
SdS3S11A1S6bS11S17VS6;A1U3A3S4S11Vo8;A2A3").
Hypothesis Ho8lo : ob_lo o8 = SLit (-464).
Hypothesis Ho8hi : ob_hi o8 = SLit (-426).
Hypothesis Ho8w : ltac2:(tb__ "0|0|
SdS2S2aS1aVo8;A1A1S5A3").
Hypothesis Ho8a : ltac2:(tb__ "0|0|
SdS2S2bS1aVo8;A1A1ScA3").
Hypothesis Hcb : ltac2:(tb__ "0|2|
SdS3S0S76A1M0A1S78S1eVo8;A1S15N1d0M1A1Z0S8cS8bN1aaG1A2A1A4S4G0Vbl;A2A3").
Hypothesis Hbl : ltac2:(tb__ "0|1|
S10SdS0S31Q8A1M0A1S4cS76G0S77R1A1Vbl;A4S41A3Fr;").
Hypothesis HswfC : swf Cs = true.
Hypothesis HnC : ss_next Cs = 116%positive.
Hypothesis Hn6 : ss_next S6 = 116%positive.
Hypothesis HnL : ss_next (obj_to_list S6 3 5) = 116%positive.
Let C : axst := ax_setS W Cs.
Hypothesis Hefr : ltac2:(tb__ "0|1|
SdS3S0S11A1M0A1S86VC;S5dVs;A3S4G0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
SdS2S85VC;S5dVs;VR;S8S51S5eS1S51A1A3A5S5A3").
Hypothesis S13 : wsub_get s 13 = SLit 38.
Hypothesis S15 : wsub_get s 15 = SLit 0.
Hypothesis HT : ltac2:(tb__ "0|0|
SdS51S87Vs;S5dS5eVC;VR;A5VT;A3").
Hypothesis HnT : ss_next (ax_S T) = 141%positive.
Hypothesis HTf : ltac2:(tb__ "0|0|
SdS51S84S42VT;A2VTf;A3").
Hypothesis HlTf : ltac2:(tb__ "0|0|
SdS2S2fS50VTf;A1A1ScA3").
Hypothesis HnTf : ss_next (ax_S Tf) = 141%positive.
Hypothesis HrunF : ltac2:(tb__ "0|1|
SdS3S0S4fA1M0A1S54S75S6eS6dVTf;S5A5S4G0S8S4fS53VF;S79A2S1S4fA1A3A2A3").
Hypothesis HbF : ltac2:(tb__ "0|0|
SdS12S52VF;A1S15S34A1A3").
Hypothesis Hxp1 : ltac2:(tb__ "0|0|
SdS3S13A1S7bS50VF;A1S71A2S4S13VG1;A2A3").
Hypothesis HobjsG1 : ltac2:(tb__ "0|1|
SdS0S11A1S17VG1;A1M0SaS11S4eS11UfG0A3S8S11S6fS1S11A1A3A3A3").
Hypothesis HnG1 : ss_next G1 = 141%positive.
Hypothesis Hdrop : drop1 G1 = G2.
Hypothesis HG2o : ltac2:(tb__ "0|0|
SdS3S11A1S6bS11S17VG2;A1U1A3S4S11S2cS28S7eS29PaA1S15N1d0A1A3S15Z0A1S15Z26A1S1S18A1S1cP5A1A5A2A3").
Hypothesis Hunl : unlist_at G2 1 = G2u.
Hypothesis HnG2u : ss_next G2u = 141%positive.
Hypothesis HswfG2u : swf G2u = true.
Hypothesis Hxp2 : ltac2:(tb__ "0|0|
SdS3S13A1S7bVG2u;S72A2S4S13VG3;A2A3").
Hypothesis HnG3 : ss_next G3 = 141%positive.
Hypothesis HnlG3 : state_nolist G3 = true.
Hypothesis Hent : ltac2:(tb__ "0|0|
SdS2S56S7fVG3;A1S45Vsp;A3S5A3").
Hypothesis Hspid : ltac2:(tb__ "0|0|
SdS2S83Vsp;S48A2S5A3").

Definition f6 (r : valuation) : positive -> list byte := ltac2:(tb__ "0|1|
S46S2S0S31Q8A1M0A1L_;S7cR1P6A2S1G0A1S16Vr;R1A2X2x2Ll;").
Definition rho_wl (r : valuation) : valuation := ltac2:(tb__ "0|0|
S80S5fVr;S5aVr;A1A2P5S41A3").
Lemma rho_wl_5 : ltac2:(tb__ "0|0|
S10SdS0S31Q8A1A1S16S57R1A1P5A2S41A3Fr;"). Proof. intros r. reflexivity. Qed.
Lemma rho_wl_6 : ltac2:(tb__ "0|1|
S10SdS0S31Q8A1M0A1S16S57R1A1P6A2S1G0A1A3Fr;"). Proof. intros r. reflexivity. Qed.
Lemma rho_wl_set : ltac2:(tb__ "0|0|
S10SdS10S57R1A1S5fR1S46S2S0S31Q8A1A1L_;S7cR1P5A2S41S5aR2R1A2X2x2Ll;A2A3Fr;").
Proof. intros r. reflexivity. Qed.

Definition WLF (r : valuation) : Prop := ltac2:(tb__ "0|3|
SeSdS0S31Q8A1M0A1M1S16Vr;P5A2S41A3SeSdG1S16Vr;P6A2S1G0A1A3SeSdS47S32Q40M2S1bVr;PdA2A2Z26A3SdS47S32G2S1bVr;PfA2A2Z0A3A2A2A2").
Definition Jp (r1 : valuation) (tp : list word) : jpredA := ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S0S3bA1S3aSeS5cR4A1S4aVr1;Vtp;U0R4R3R2R1A7A2Lmd;Ltr;Lt;Lr;").

Lemma Jp_stable : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S39S33P5cS58R2R1A2A3Ftp;Fr1;").
Proof.
  intros r1 tp r r' t tr md md' Hag Hme [(A5 & A6 & A13 & A15) HK].
  split; [| eapply (Kf_stable r1 tp 0%nat 92%positive); [exact Hag | exact Hme | exact HK]].
  destruct Hag as (Hw & Hl & _). unfold WLF.
  rewrite <- (Hl 5%positive), <- (Hl 6%positive), <- (Hw 13%positive ltac:(lia)), <- (Hw 15%positive ltac:(lia)).
  repeat split; assumption.
Qed.

Lemma Kw_Jp_Kf : ltac2:(tb__ "0|1|
S10S0S31Q40A1A1M0S6S10G0S0S3bA1S3aS65S58R7R6A2S41S1S31Q8A1A1R5R4R3R2R1A8S4aR8R7R6R5R4R3R2A7F_;Fmd;Ftr;Ft;Fr;Fk;Ftp;Fr1;").
Proof.
  intros r1 tp k r t tr md (tr0 & [_ [Ht (tr00 & HJ & ->)]] & ->). split; [exact Ht|].
  exists tr00. split; [exact HJ|]. unfold WLerr.TRk, WLerr.MSG, EVSr. cbn [firstn map app]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma MSG_len : ltac2:(tb__ "0|1|
SdS6SbS31Q8A1M0S66S41S1G0A1A2A2U26A3").
Proof. reflexivity. Qed.

Lemma wl_call : ltac2:(tb__ "0|4|
S10S0S31Q40A1A1M0S10G0S69S33Vok;S35S33S58R4R3A2M1S5dR2R1A5S36S33S65G1S41S1S31Q8A1M2A1M3SbG2S66S41G3A2A2A4P5cR2R1S67A6A4Ftp2;Frho2;Ftp;Fr1;").
Proof.
  intros r1 tp rho2 tp2.
  apply triple_SPA_pure. intros tr md [(A5 & A6 & A13 & A15) _].
  apply (triple_SPA_conseq_J segs ok _ (Jp r1 tp)); [intros t md0 (HJ & _ & _); exact HJ|].
  apply (WLerr.wl2_sum ok (Jp r1 tp) rho2 tp2 MSG_REF [] A5 A6).
  - rewrite A13. reflexivity.
  - rewrite A15. reflexivity.
  - rewrite MSG_len. unfold max_write_total. lia.
  - apply Jp_stable.
  - intros k r t tr0 ms md0 msv' HK HMI Hh Hp Hstep.
    exact (Kf_okK r1 tp k r t tr0 ms md0 msv' (Kw_Jp_Kf r1 tp k r t tr0 md0 HK) HMI Hh Hp Hstep).
  - intros k r t tr0 ms md0 x8 HK Hp Ho.
    exact (Kf_okP r1 tp k r t tr0 ms md0 x8 (Kw_Jp_Kf r1 tp k r t tr0 md0 HK) Hp Ho).
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd2 _ _ _ _ HJ).
  - rewrite MSG_REF_len. lia.
Qed.

Lemma wl_call_ex : ltac2:(tb__ "0|4|
S10S0S31Q40A1A1M0S10G0S68S33S35S33S58R4R3A2M1S5dR2R1A5S36S33S65G1S41S1S31Q8A1M2A1M3SbG2S66S41G3A2A2A4P5cR2R1S67A6A3Ftp2;Frho2;Ftp;Fr1;").
Proof.
  intros r1 tp rho2 tp2 w Hw. pose proof Hw as [Hsm [(A5 & A6 & A13 & A15) HK]].
  apply (WLerr.wl2_sum_ex (Jp r1 tp) rho2 tp2 MSG_REF [] A5 A6).
  - rewrite A13. reflexivity.
  - rewrite A15. reflexivity.
  - rewrite MSG_len. unfold max_write_total. lia.
  - apply Jp_stable.
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd2 _ _ _ _ HJ).
  - rewrite MSG_REF_len. lia.
  - exact Hw.
Qed.

Lemma SPA_splits : ltac2:(tb__ "0|0|
S37S10S0S31Q40A1A1S6aS35S33R4VW;R3R2R1A6S35S33R5S55VW;VS6;A2R4R3R2A6F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w Hsp. pose proof Hsplits as H. unfold splits_fp, obindW in H.
  destruct (split_obj_at (ax_S W) 0 (SLit (-584))) as [S1|] eqn:E1; [|discriminate].
  destruct (split_obj_at S1 1 (SLit (-552))) as [S2|] eqn:E2; [|discriminate].
  destruct (split_obj_at S2 2 (SLit (-464))) as [S3|] eqn:E3; [|discriminate].
  destruct (split_obj_at S3 3 (SLit (-426))) as [S4|] eqn:E4; [|discriminate].
  destruct (split_obj_at S4 5 (SLit (FERR + 120))) as [S5|] eqn:E5; [|discriminate].
  pose proof (SPA_split segs J rho W 0 (SLit (-584)) S1 tp w E1 Hsp) as H1.
  pose proof (SPA_split segs J rho (ax_setS W S1) 1 (SLit (-552)) S2 tp w E2 H1) as H2.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS W S1) S2) 2 (SLit (-464)) S3 tp w E3 H2) as H3.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS W S1) S2) S3) 3 (SLit (-426)) S4 tp w E4 H3) as H4.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS (ax_setS W S1) S2) S3) S4) 5 (SLit (FERR + 120)) S5 tp w E5 H4) as H5.
  exact (SPA_split segs J rho (ax_setS (ax_setS (ax_setS (ax_setS (ax_setS W S1) S2) S3) S4) S5) 6 (SLit (FERR + 124)) S6 tp w H H5).
Qed.

Lemma facts_rho_wl : ltac2:(tb__ "0|0|
S10S4dS14S19R1A1S42A3S4dS14S19S57R2A1A1S42A3F_;Fr;").
Proof.
  intros r H. apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) H p Hp) as X.
  unfold facts_fp in Hp. destruct Hp as [<-|[<-|[<-|[<-|[]]]]]; exact X.
Qed.
Lemma fb_facts : ltac2:(tb__ "0|0|
SdS2S6cS14S2dS48A1S42A3S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition oext (o : sobj) : sv * sv * sv := ltac2:(tb__ "0|0|
S9S7S12S12A2S12S9S12S12S1dVo;A1S20Vo;A1A4S1fVo;A1A4").
Lemma obj_to_list_exts : ltac2:(tb__ "0|1|
S13S6S46SdS0S7S7S12S12A2S12A2M0A1S4cS11G0S59S17S8aR3R2R1A3A1A4S4cS11G0S59S17R3A1A4A3Fl;Fi;FS;").
Proof.
  intros S i l. unfold obj_to_list. destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|reflexivity].
  cbn [ss_objs set_objs].
  transitivity (map oext (firstn i (ss_objs S) ++ o :: skipn (Datatypes.S i) (ss_objs S))); [rewrite !map_app; reflexivity|].
  rewrite <- (nth_error_split3 _ _ _ Hn). reflexivity.
Qed.
Lemma obj_range_ext_rl : ltac2:(tb__ "0|0|
S10S46S0S31Q8A1A1F_;S11S11SdS12S1dR1A1S1dR2A1A3SdS12S20R2A1S20R3A1A3SdS12S1fR3A1S1fR4A1A3SdS2S60R5A1S5A3SdS7S47S47A2S23S5fR8R7A2R5A2S23R8R6A2A3F_;F_;F_;F_;Fo';Fo;Ff;Frho;").
Proof.
  intros rho f o o' E1 E2 E3 Hnl. unfold obj_nolist in Hnl.
  apply andb_prop in Hnl as [Hnl _]. apply andb_prop in Hnl as [Hnl _]. apply andb_prop in Hnl as [Hnl Hhi]. apply andb_prop in Hnl as [Hb Hlo].
  unfold obj_range, obj_lo_of, obj_hi_of, soff. rewrite E1, E2, E3. rewrite !(eval_set_rl rho f) by assumption. reflexivity.
Qed.
Lemma outside_all_oext_rl : ltac2:(tb__ "0|2|
S10S46S0S31Q8A1A1F_;S0S11A1M0G0S31Q40A1SdS0S7S7S12S12A2S12A2M1A1S4cS11G1S59R2A4S4cS11G1S59R3A4A3SdS2S6cS11S60R4A3S5A3S25R7R5R3A3S25S5fR8R7A2R5R4A3F_;F_;F_;Fx;Fobjs';Fobjs;Ff;Frho;").
Proof.
  intros rho f objs. induction objs as [|o t IH]; intros [|o' t'] x Hm Hnl Hout.
  - constructor.
  - cbn [map] in Hm. exfalso. inversion Hm.
  - cbn [map] in Hm. exfalso. inversion Hm.
  - cbn [map] in Hm. injection Hm as Eb El Eh Ht. cbn [forallb] in Hnl. apply andb_prop in Hnl as [Ho Hnt]. inversion Hout; subst.
    constructor; [| apply IH; assumption]. cbn zeta in *. rewrite (obj_range_ext_rl rho f o o' Eb El Eh Ho). assumption.
Qed.

Lemma reshape : ltac2:(tb__ "0|1|
S10S0S31Q40A1A1S10S6aS4dS14S19R2A1S42A3S35S33S4aR5R4U0M0A3VW;R3R4R2A6S35S33S4aR6R5G0A3VC;S57R4A1R5R3A6F_;F_;Fw;Frho;Ftp;Fr1;").
Proof.
  intros r1 tp rho w HF Hsp.
  pose proof (SPA_splits _ rho tp w Hsp) as H6.
  unfold C. rewrite <- (ax_setS_twice W S6 Cs).
  eapply (SPA_morphX (Kf r1 tp 0) (Kf r1 tp 0) (ax_setS W S6) Cs rho (rho_wl rho) tp w).
  - cbn [ax_X ax_base ax_setS]. rewrite HXW, HbW, HnC. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - cbn [ax_base ax_setS]. rewrite HbW. reflexivity.
  - cbn [ax_X ax_setS]. rewrite HXW. intros r [<-|[<-|[]]]; cbn [fst snd]; rewrite rho_wl_set; split; apply eval_set_rl; reflexivity.
  - cbn [ax_S ax_setS]. intros x Hout Hrm. split; [|reflexivity].
    rewrite <- Hfinish. unfold finish_fp. cbn [ss_objs app_obj]. apply outside_all_app_iff. split.
    +
      rewrite rho_wl_set. apply (outside_all_oext_rl rho _ (ss_objs S6)); [apply obj_to_list_exts | | exact Hout].
      pose proof Hnl6 as X. unfold state_nolist in X. apply andb_prop in X as [X _]. apply andb_prop in X as [_ X]. exact X.
    + cbn [app]. unfold outside_all. constructor; [|constructor]. cbn zeta. unfold obj_range, obj_lo_of, obj_hi_of, O_b2e; cbn [ob_base ob_lo ob_hi eval fst snd].
      rewrite !soff_lit_small by lia. lia.
  - intros Hsm. rewrite <- Hfinish. unfold finish_fp.
    pose proof (smatch_set_rl segs rho (f6 rho) S6 (virt tp w) Hnl6 Hsm) as H5.
    pose proof (smatch_obj_to_list segs _ S6 (virt tp w) 3 5 o8 (-464) (-426) bl H5 Ho8 Ho8lo Ho8hi
                  ltac:(lia) ltac:(lia) Ho8w Ho8a Hcb Hrl5) as H7.
    rewrite Hbl in H7. change (rho_set_rl (set_rl rho (f6 rho)) 5 MSG_REF) with (rho_wl rho) in H7.
    unfold app_obj, O_b2e.
    apply (smatch_carve_rom segs (rho_wl rho) (obj_to_list S6 3 5) (virt tp w) 0 0 6 (ss_next (obj_to_list S6 3 5)) H7).
    + rewrite <- Hfinish in HswfC. exact HswfC.
    + lia. + lia. + lia.
    + rewrite rho_wl_6. reflexivity.
    + intros k Hk. exfalso. lia.
    + apply Forall_forall. intros o _. unfold ranges_disjoint. cbn [fst snd]. lia.
  - intros HK. exact HK.
  - exact H6.
Qed.

Lemma W_facts : ltac2:(tb__ "0|0|
S37S10S0S31Q40A1A1S6aS35S33R4VW;R3R2R1A6S4dS14S19R4A1S42A3F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w Hsp. pose proof (SPA_facts_hold segs J rho W tp w Hsp) as HF. rewrite HfW in HF.
  apply Forall_app in HF as [_ HF]. exact HF.
Qed.

Definition rho_fin (rho0 rho3 : valuation) (ms : machine_state) (md : Model) (tp : list word) : valuation := ltac2:(tb__ "0|0|
S82S5fS81Vrho3;S8S11S6fS1S11A1A3S89Vmd;Vtp;Vms;A3A3S16Vrho0;A1A2Vsp;A2").

Lemma cleanup : ltac2:(tb__ "0|2|
S10S0S31Q40A1A1M0S0S3bA1M1S3aOFx2;Fx1;Fx0;Fx;S10S10G0G1S61S3aS10S10G0G1S3aRcR5R3R2R1A4RdR5R4R3R2A4F_;Fmd';Ftr';Ft;Fr';Fr;S35S33R8VF;R6R5S9G1S62R4S63R3R2A2A4A6S35S33R9S45S5bR8R7R4R3R6A5R6S9G1S62R5S63R4R3A2A4A6F_;F_;Fmd;Fms;Ftr;Ftp;Frho3;Frho0;FJ;").
Proof.
  intros J rho0 rho3 tp tr ms md HJi Hsp.
  pose proof (SPA_x_sub segs J rho3 F [] tp _ ltac:(intros r Hr; destruct Hr) Hsp) as H0.
  assert (E0 : ax_setX F [] = axc (ax_S F)) by (unfold ax_setX, axc; rewrite HbF; reflexivity). rewrite E0 in H0.
  assert (H1 : SPA segs J (axc G1) rho3 tp (tr, mkCfg ms md)).
  { apply (SPA_morph J J (axc (ax_S F)) G1 rho3 rho3 tp _ eq_refl); [cbn [ax_base axc]; rewrite HnG1; reflexivity | | intros HK; exact HK | exact H0].
    intros Hsm. exact (smatch_xforms segs XP1 rho3 (ax_S F) G1 _ Hxp1 Hsm). }
  pose proof (SPA_unobj segs J rho3 (axc G1) (firstn 15 (ss_objs G1)) [O_b2e] tp tr ms md
                HobjsG1 H1 ltac:(intros HK; exact (HJi _ _ _ _ _ HK))) as H2.
  cbn zeta in H2. cbn [ax_S axc] in H2. pose proof Hdrop as Hd. unfold drop1 in Hd. rewrite Hd in H2.
  set (rho4 := rho_absorb rho3 [O_b2e] (vms md tp ms)) in H2.
  change (ax_setS (axc G1) G2) with (axc G2) in H2.
  assert (H2u : SPA segs J (axc G2u) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_morph J J (axc G2) G2u rho4 rho4 tp _ eq_refl); [cbn [ax_base axc]; rewrite HnG2u; reflexivity | | intros HK; exact HK | exact H2].
    intros Hsm. rewrite <- Hunl. eapply (smatch_unlist_at rho4 G2 1 _ 5 _ HG2o eq_refl eq_refl); [rewrite Hunl; exact HswfG2u | exact Hsm]. }
  assert (H3 : SPA segs J (axc G3) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_morph J J (axc G2u) G3 rho4 rho4 tp _ eq_refl); [cbn [ax_base axc]; rewrite HnG3; reflexivity | | intros HK; exact HK | exact H2u].
    intros Hsm. exact (smatch_xforms segs XP2 rho4 G2u G3 _ Hxp2 Hsm). }
  assert (H4 : SPA segs J (axc G3) (set_rl rho4 (rl rho0)) tp (tr, mkCfg ms md)).
  { apply (SPA_morph J J (axc G3) G3 rho4 (set_rl rho4 (rl rho0)) tp _ eq_refl); [cbn [ax_base axc]; rewrite HnG3; reflexivity | | intros HK; apply (HJi _ _ _ _ _ HK) | exact H3].
    intros Hsm. exact (smatch_set_rl segs rho4 (rl rho0) G3 _ HnlG3 Hsm). }
  unfold rho_fin. destruct H4 as [Hsm4 HK4]. split; [| apply (HJi _ _ _ _ _ HK4)].
  eapply smatchA_entails; [exact Hent | exact Hsm4].
Qed.

Lemma rho_fin_agree : ltac2:(tb__ "0|1|
S10S10S10S0S31Q40A1M0A1S61S3aS21S48R6R5A3S46S7dR1S48A2SdG0S1bR7R2A2S1bR8R2A2A3F_;Fi;G0SdS3S31Q8A1A1S26R7R1A2S26R8R1A2A3Fa;S21S48R9S5bR9R7R5R4R6A5A3F_;F_;F_;Fmd;Fms;Ftp;Frho3;Frho1;Frho0;").
Proof.
  intros rho0 rho1 rho3 tp ms md Hag01 Hrw Hrm. destruct Hag01 as (A & B & Cc).
  unfold rho_fin. split; [|split].
  - intros i Hi. cbn [rw rho_sub set_rl rho_absorb].
    rewrite (wsub_get_id sp NF i Hspid Hi). cbn. rewrite (Hrw i Hi). apply A. exact Hi.
  - intros l. reflexivity.
  - intros a. cbn [rm rho_sub set_rl rho_absorb].
    destruct (in_ranges_dec rho3 [O_b2e] a) as [Hin|Hnin]; [| rewrite Hrm; apply Cc].
    exfalso. destruct Hin as (o & [<-|[]] & Hr). unfold obj_range, obj_lo_of, obj_hi_of, O_b2e in Hr. cbn [ob_base ob_lo ob_hi eval fst snd] in Hr.
    rewrite !soff_lit_small in Hr by lia. lia.
Qed.

Theorem fp_sum_inst : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S69S33Vok;S35S33VJ0;S43R2R1A5S36S33S49U26A1S48R2R1S44A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply (runA_tr segs ok FUEL_FP CUTS_FP Pre_ref _ J0 rho tp); [exact HrunW | reflexivity | apply okK_J0 | exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply (triple_pre ok _ _ _ (fun w Hw => W_facts J0 rho1 tp w Hw)). intros HF1.
  eapply triple_conseq with (P := SPA segs (Kf rho1 tp 0) C (rho_wl rho1) tp); [ | intros w Hw; exact Hw |].
  { intros w Hw. apply (reshape rho1 tp rho1 w HF1). destruct Hw as [Hsm HJ]. split; [exact Hsm|]. split; [reflexivity|]. apply Kw0_of_J0. exact HJ. }
  apply (call_soundA segs ok (Kf rho1 tp 0) (Jp rho1 tp) (WLerr.Kw (Jp rho1 tp) MSG_REF [] (length (WLerr.MSG MSG_REF [])))
           (Kf rho1 tp 38) C WLerrS.Pre_wl2 s R WLerr.Posts_wl _ (rho_wl rho1) tp Hefr).
  - exact Hchk.
  - intros rho2 tp2. apply wl_call.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval].
    split; [apply rho_wl_5|]. split; [apply rho_wl_6|]. split; reflexivity.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite MSG_len in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite HT.
    apply triple_SPA_pure. intros tr md [Et _]. subst tpL.
    apply (triple_SPA_conseq_J segs ok _ (Kf rho1 tp 38)); [intros t md0 (HJ & _ & _); exact HJ|].
    assert (HF' : Forall (holds rho') facts_fp).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S C)) (rho_wl rho1) rho' p Hag'
               ltac:(unfold C; cbn [ax_S ax_setS]; rewrite HnC; apply (sprop_below_mono NF); [unfold NF; lia | exact (proj1 (forallb_forall _ _) fb_facts p Hp)]))).
      exact (proj1 (Forall_forall _ _) (facts_rho_wl rho1 HF1) p Hp). }
    eapply triple_conseq with (P := SPA segs (Kf rho1 tp 38) Tf rho' tp); [ | intros w Hw; exact Hw |].
    { intros w [Hsm HJ]. split; [|exact HJ]. rewrite <- HTf. apply smatchA_add_facts; [exact Hsm | exact HF' | rewrite HnT; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }
    eapply (runA_tr segs ok FUEL_FP CUTS_FP Tf _ (Kf rho1 tp 38) rho' tp); [exact HrunF | exact HlTf | apply Kf_okK | apply Kf_stable |].
    intros L2 rho3 [<-|[]] Hag3. cbn [la_state]. rewrite HnTf in Hag3.
    intros n Hg w [Hsm3 HK3]. destruct w as [tr3 [ms3 md3]].
    pose proof (cleanup (Kf rho1 tp 38) rho rho3 tp tr3 ms3 md3 ltac:(intros r r' t tr' md' HK; exact HK) (conj Hsm3 HK3)) as [HsmP HKP].
    assert (HagF : agree_below NF rho (rho_fin rho rho3 ms3 md3 tp)).
    { apply (rho_fin_agree rho rho1 rho3 tp ms3 md3 Hag1).
      - intros i Hi. destruct Hag3 as (A3 & _ & _). destruct Hag' as (A' & _ & _).
        assert (Hi' : (i < 141)%positive) by (unfold NF in Hi; lia).
        assert (Hi'' : (i < 116)%positive) by (unfold NF in Hi; lia).
        rewrite <- (A3 i Hi'). unfold C in A'. cbn [ax_S ax_setS] in A'. rewrite HnC in A'. rewrite <- (A' i Hi''). reflexivity.
      - intros a. destruct Hag3 as (_ & _ & C3). destruct Hag' as (_ & _ & C'). rewrite <- (C3 a), <- (C' a). reflexivity. }
    apply Hg.
    exists (mkLeafA P_ref RsCut), (rho_fin rho rho3 ms3 md3 tp). split; [left; reflexivity|]. split; [exact HagF|].
    split; [exact HsmP|]. cbn [la_state w_tr w_cfg cfg_model]. destruct HKP as [_ (tr0 & HJ0 & ->)].
    exists tr0. split; [|reflexivity].
    eapply Hst0; [ | apply mat_equiv_refl | exact HJ0].
    eapply agree_below_trans; [apply agree_below_sym; exact Hag1 | exact HagF].
Qed.

Theorem fp_sum_ex_inst : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S68S33S35S33VJ0;S43R2R1A5S36S33S49U26A1S48R2R1S44A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply (erunA_tr segs FUEL_FP CUTS_FP Pre_ref _ J0 rho tp); [exact HrunW | reflexivity | exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply (etriple_pre _ _ _ (fun w Hw => W_facts J0 rho1 tp w Hw)). intros HF1.
  eapply etriple_conseq with (P := SPA segs (Kf rho1 tp 0) C (rho_wl rho1) tp); [ | intros w Hw; exact Hw |].
  { intros w Hw. apply (reshape rho1 tp rho1 w HF1). destruct Hw as [Hsm HJ]. split; [exact Hsm|]. split; [reflexivity|]. apply Kw0_of_J0. exact HJ. }
  apply (call_completeA segs (Kf rho1 tp 0) (Jp rho1 tp) (WLerr.Kw (Jp rho1 tp) MSG_REF [] (length (WLerr.MSG MSG_REF [])))
           (Kf rho1 tp 38) C WLerrS.Pre_wl2 s R WLerr.Posts_wl _ (rho_wl rho1) tp Hefr).
  - exact Hchk.
  - intros rho2 tp2. apply wl_call_ex.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval].
    split; [apply rho_wl_5|]. split; [apply rho_wl_6|]. split; reflexivity.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite MSG_len in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite HT.
    intros w0 [Hsm0 [Et HK0]]. subst tpL. revert w0 Hsm0 HK0.
    assert (HF' : Forall (holds rho') facts_fp).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S C)) (rho_wl rho1) rho' p Hag'
               ltac:(unfold C; cbn [ax_S ax_setS]; rewrite HnC; apply (sprop_below_mono NF); [unfold NF; lia | exact (proj1 (forallb_forall _ _) fb_facts p Hp)]))).
      exact (proj1 (Forall_forall _ _) (facts_rho_wl rho1 HF1) p Hp). }
    assert (HE : etriple segs (SPA segs (Kf rho1 tp 38) Tf rho' tp) (LQA segs (Kwr 38) NF rho tp Posts_ref)).
    { eapply (erunA_tr segs FUEL_FP CUTS_FP Tf _ (Kf rho1 tp 38) rho' tp); [exact HrunF | exact HlTf | apply Kf_stable |].
      intros L2 rho3 [<-|[]] Hag3. cbn [la_state]. rewrite HnTf in Hag3.
      intros w [Hsm3 HK3]. destruct w as [tr3 [ms3 md3]]. exists (tr3, mkCfg ms3 md3). split; [apply wsteps_refl|].
      pose proof (cleanup (Kf rho1 tp 38) rho rho3 tp tr3 ms3 md3 ltac:(intros r r' t tr' md' HK; exact HK) (conj Hsm3 HK3)) as [HsmP HKP].
      assert (HagF : agree_below NF rho (rho_fin rho rho3 ms3 md3 tp)).
      { apply (rho_fin_agree rho rho1 rho3 tp ms3 md3 Hag1).
        - intros i Hi. destruct Hag3 as (A3 & _ & _). destruct Hag' as (A' & _ & _).
          assert (Hi' : (i < 141)%positive) by (unfold NF in Hi; lia).
          assert (Hi'' : (i < 116)%positive) by (unfold NF in Hi; lia).
          rewrite <- (A3 i Hi'). unfold C in A'. cbn [ax_S ax_setS] in A'. rewrite HnC in A'. rewrite <- (A' i Hi''). reflexivity.
        - intros a. destruct Hag3 as (_ & _ & C3). destruct Hag' as (_ & _ & C'). rewrite <- (C3 a), <- (C' a). reflexivity. }
      exists (mkLeafA P_ref RsCut), (rho_fin rho rho3 ms3 md3 tp). split; [left; reflexivity|]. split; [exact HagF|].
      split; [exact HsmP|]. cbn [la_state w_tr w_cfg cfg_model]. destruct HKP as [_ (tr0 & HJ0 & ->)].
      exists tr0. split; [|reflexivity].
      eapply Hst0; [ | apply mat_equiv_refl | exact HJ0].
      eapply agree_below_trans; [apply agree_below_sym; exact Hag1 | exact HagF]. }
    intros w0 Hsm0 HK0. apply HE. split; [| split; [reflexivity | exact HK0]].
    rewrite <- HTf. apply smatchA_add_facts; [exact Hsm0 | exact HF' | rewrite HnT; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
Qed.
End Inst.

Theorem ref_sum : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S69S33Vok;S35S33VJ0;S43R2R1A5S36S33S49U26A1S48R2R1S44A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  destruct shapeW_r as (HnW & HXW & HbW & HfW & _).
  destruct shapeC_r as (Hnl6 & Hrl5 & Ho8 & Hlo & Hhi & Hw8 & Ha8 & Hcb & HswfC & HnC & Hn6 & HnL).
  destruct shapeS_r as (S13 & S15). destruct shapeT_r as (HnT & HlTf & HnTf).
  destruct shapeF_r as (_ & HnF & HbF & HoG1 & HnG1 & HnG2u & HnG3 & HnlG3 & Hspid & HG2o).
  apply (fp_sum_inst W_r S6_r Cs_r O8_r BL_r s_r R_r T_r Tf_r F_r G1_r G2_r G2u_r G3_r sp_r EX_r runW_r HnW HXW HbW HfW splits_r finish_r
           Hnl6 Hrl5 Ho8 Hlo Hhi Hw8 Ha8 Hcb BL_r_val HswfC HnC Hn6 HnL efr_r chk_r S13 S15 T_r_eq HnT Tf_r_eq HlTf HnTf runF_r HbF
           xp1_r HoG1 HnG1 drop1_r HG2o unlist_r HnG2u ltac:(rewrite <- unlist_r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) xp2_r HnG3 HnlG3 ent_r Hspid).
Qed.

Theorem ref_sum_ex : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S68S33S35S33VJ0;S43R2R1A5S36S33S49U26A1S48R2R1S44A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  destruct shapeW_r as (HnW & HXW & HbW & HfW & _).
  destruct shapeC_r as (Hnl6 & Hrl5 & Ho8 & Hlo & Hhi & Hw8 & Ha8 & Hcb & HswfC & HnC & Hn6 & HnL).
  destruct shapeS_r as (S13 & S15). destruct shapeT_r as (HnT & HlTf & HnTf).
  destruct shapeF_r as (_ & HnF & HbF & HoG1 & HnG1 & HnG2u & HnG3 & HnlG3 & Hspid & HG2o).
  apply (fp_sum_ex_inst W_r S6_r Cs_r O8_r BL_r s_r R_r T_r Tf_r F_r G1_r G2_r G2u_r G3_r sp_r EX_r runW_r HnW HXW HbW HfW splits_r finish_r
           Hnl6 Hrl5 Ho8 Hlo Hhi Hw8 Ha8 Hcb BL_r_val HswfC HnC Hn6 HnL efr_r chk_r S13 S15 T_r_eq HnT Tf_r_eq HlTf HnTf runF_r HbF
           xp1_r HoG1 HnG1 drop1_r HG2o unlist_r HnG2u ltac:(rewrite <- unlist_r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) xp2_r HnG3 HnlG3 ent_r Hspid).
Qed.
End Fp.
End DrvFp.

(* [comment removed for export] *)
Module Asan_memsetZ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "bool"; "true"; "app"; "None"; "Some"; "false"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "cell"; "mkCell"; "sprop"; "sobj"; "DUnknown"; "mkObj"; "SPUle"; "SAlu"; "FcsrFrm0"; "SPBranch"; "mkSS"; "DImage"; "SPAlign"; "SPNot"; "DZero"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "tv"; "dst"; "vLd"; "vBd"; "cur"; "gl"; "gs"; "F8of"; "vOd"; "O_rtc3"; "hi_fact"; "lastd"; "lo_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "la_state"; "entailsA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "vN"; "shp"; "add"; "O_rtc2"; "P_ret"; "shpk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_XOR"; "BC_GEU"; "BC_LTU"; "BC_NE"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.Asan_memsetZ"; "E_real"; "E_reg"; "R_reg"; "mid_state"; "s_reg"; "E_L_bk"; "E_L_in"; "FT"; "P_ms"; "R_real"; "X_ms"; "l_regs"; "objs_ms"; "s_real"; "spm"; "CL"; "CL_0"; "E_reg_hi"; "E_reg_lo"; "FUELS"; "Pre_ms1"; "T1"; "T3"; "base_ms"; "cutpcs_ms"; "F_L"; "O_cstk"; "O_dst"; "O_frame"; "O_realms"; "O_rest"; "Pre_ms0"; "cuts_ms"; "exits_ms"; "frame_cells"; "mid_regs"; "s_L_bk"; "s_L_in"; "vDp"; "vcuts_ms"; "vexits_ms"; "xor_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.Asan_memsetZ.AMSZAddr"; "l_head"; "musl_memset"; "ms_entry"; "ms_ret"; "ra_real"; "ra_reg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "NPOST"; "post_regs"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "segs"; "ACEIL"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "Pre_rip_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module AMSZAddr.
  Definition ms_entry : Z := 0x5cce8.
  Definition ms_ret : Z := 0x5cda8.
  Definition ra_reg : Z := 0x5ced0.
  Definition ra_real : Z := 0x5cd84.
  Definition l_head : Z := 0x5cea4.
  Definition musl_memset : Z := 0xde378.
End AMSZAddr.
Import AMSZAddr.

Definition X_ms : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SdSdA2M0S1SdSdS24S23A4S3G0A1A3").

Definition O_realms : sobj := ltac2:(tb__ "0|1|
S15SfZ0A1SfZe9af0A1M0SfZe9af8A1S0S10S11G0Z8SfS71A1A3S3S10A1A3S14A5").

Definition frame_cells : list cell := ltac2:(tb__ "0|1|
S0S10S11SfN38A1Z8M0SeP29A1A3S0S10S11SfN30A1G0SeP28A1A3S0S10S11SfN28A1G0SeP27A1A3S0S10S11SfN20A1G0SeP26A1A3S0S10S11SfN18A1G0SeP1dA1A3S0S10S11SfN10A1G0SeP1cA1A3S0S10S11SfN8A1G0SePbA1A3S3S10A1A3A3A3A3A3A3A3").
Definition O_frame (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S15SePaA1SfN850A1SfZ0A1Vcs;S14A5").
Definition spm : sv := add (SVar 10) (SLit (-2128)).
Definition O_cstk : sobj := ltac2:(tb__ "0|0|
S15S54SfN50A1SfZ0A1S3S10A1S14A5").

Definition vDp : sv := SVar 95.
Definition O_rest : sobj := ltac2:(tb__ "0|0|
S15SePaA1S6cSfN8a0A1S3S10A1S14A5").
Definition O_dst (d : odefault) : sobj := ltac2:(tb__ "0|0|
S15S22SfZ0A1S33S3S10A1Vd;A5").
Definition objs_ms (fr : list cell) (d : odefault) : list sobj := ltac2:(tb__ "0|0|
S7S13S0S13S62Vfr;A1S0S13S60S0S13S64S0S13S61Vd;A1S0S13S2aS0S13S36S0S13S63S3S13A1A3A3A3A3A3A3A3S80A3").

Definition base_ms : list sprop := ltac2:(tb__ "0|5|
S0S12S16S35S29S33A2S23A2S0S12S16S29S23A2S0S12S16S33S23A2S0S12S16S23SfS43Z2M0Z28A2A1M1A2S0S12S16SfZ1000A1S24A2S0S12S16S35S24S23A2SfS45S43G0Z2fA2Z8A2A1M2A2S0S12S16S24G2A2S0S12S1cPfZ3A2S0S12S16SfZ1A1S33A2S0S12S16S33G1A2S0S12S1cPaM3Z4A2S0S12S16SfS44S7fZ900A2A1SeG3A1M4A2S0S12S16G4SfS43G0Z3fA2A1A2S3S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xor_fact : sprop := ltac2:(tb__ "0|0|
S1dS19S41S17S3fS22SfZffffffffffffffffA1A3S33A3A1").
Definition FT : list sprop := xor_fact :: base_ms.

Definition Pre_ms0 : axst := ltac2:(tb__ "0|1|
S7dS1aS72S78S79S0S4S2SdA2M0S1S2SdUaS22A4S0G0S1S2SdUbSfZ0A1A4S0G0S1S2SdUcS33A4S3G0A1A3A3A3A2S77S18S8SdA1S52S3S10A1S14A2S5dS76SaA9S50A2").
Definition Pre_ms1 : axst := ltac2:(tb__ "0|0|
S3bS0S12S6fS3S12A1A3S65A2").
Definition P_ms : axst := ltac2:(tb__ "0|1|
S7dS1aS73S78S7bS76A1S0S4S2SdA2M0S1S2SdUaS22A4S3G0A1A3A2S77S18S8SdA1S52S3S10A1S1eA2S5dS7aSaA9S50A2").
Definition Posts_ms : list leafA := ltac2:(tb__ "0|0|
S0S2fS32S4eS8cA2S3S2fA1A3").

Definition mid_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|15|
S78S79S7S4S2SdA2M0S0G0S1S2SdU1M1S21G1A1A4S0G0S1S2SdU2S54A4S0G0S1S2SdU5M2S21G2A1A4S0G0S1S2SdU6M3S21G3A1A4S0G0S1S2SdU7M4S21G4A1A4S0G0S1S2SdU8SePaA1A4S0G0S1S2SdU9M5S21G5A1A4S0G0S1S2SdUaM6S21G6A1A4S0G0S1S2SdUbM7S21G7A1A4S0G0S1S2SdUcM8S21G8A1A4S0G0S1S2SdUdM9S21G9A1A4S0G0S1S2SdUeMaS21GaA1A4S0G0S1S2SdUfMbS21GbA1A4S0G0S1S2SdU10McS21GcA1A4S0G0S1S2SdU11MdS21GdA1A4S0G0S1S2SdU12MeS21GeA1A4S0G0S1S2SdU13MfS21GfA1A4S0G0S1S2SdU14S54A4S0G0S1S2SdU15M10S21G10A1A4S0G0S1S2SdU1cM11S21G11A1A4S0G0S1S2SdU1dM12S21G12A1A4S0G0S1S2SdU1eM13S21G13A1A4S0G0S1S2SdU1fM14S21G14A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition mid_state (pc : Z) (l : list (nat * sv)) (facts : list sprop) (d : odefault) : axst := ltac2:(tb__ "0|0|
S7dS1aVpc;S69Vl;A1S77S18S8SdA1S52S68Vd;A2S7S12Vfacts;S4dA3PbeSaA9S50A2").

Definition E_reg : axst := ltac2:(tb__ "0|1|
S49S89S0S4S2SdA2M0S1S2SdU1SfS75A1A4S0G0S1S2SdUaS22A4S0G0S1S2SdUbS33A4S0G0S1S2SdU9S22A4S0G0S1S2SdU15SfZ0A1A4S0G0S1S2SdU12S33A4S3G0A1A3A3A3A3A3A3S3S12A1S14A4").
Definition E_reg_hi : axst := ltac2:(tb__ "0|0|
S3bS0S12S2bS24A1S3S12A1A3S47A2").
Definition E_reg_lo : axst := ltac2:(tb__ "0|0|
S3bS0S12S2dS24S23A2S3S12A1A3S47A2").

Definition E_real : axst := ltac2:(tb__ "0|1|
S49S71S0S4S2SdA2M0S1S2SdU1SfS74A1A4S0G0S1S2SdUaS22A4S0G0S1S2SdUbSfZ0A1A4S0G0S1S2SdUcS33A4S3G0A1A3A3A3A3S3S12A1S14A4").

Definition F_L : list sprop := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.F_L vBd vLd lastd.
Definition l_regs (a3 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2SdA2M0S1S2SdUaS22A4S0G0S1S2SdUbSfZ0A1A4S0G0S1S2SdUcS33A4S0G0S1S2SdUdVa3;A4S0G0S1S2SdUeS34S26A1A4S3G0A1A3A3A3A3A3").
Definition CL_0 : axst := ltac2:(tb__ "0|0|
S49S70S51S34S25A1A1S3S12A1S14A4").
Definition CL : axst := ax_add_facts F_L CL_0.
Definition E_L_in : axst := ltac2:(tb__ "0|1|
S49S70S51S34S27A1M0A1S7S12S28S27P8eS22A3S7S12S28S26P8dS2cA3S0S12S1dS19S40G0S34S26A1A3A1S3S12A1A3A3A3S14A4").
Definition E_L_bk : axst := ltac2:(tb__ "0|1|
S49S70S51S38S25Z1A2M0A1S7S12S5fS0S12S19S42G0S34S26A1A3S3S12A1A3A3S14A4").

Definition s_reg : wsub := ltac:(let x := eval vm_compute in ((16%positive, vLd) :: infer_sub 1 (ax_S E_reg) (ax_S Pre_rip)) in exact x).
Definition s_real : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 (ax_S E_real) (ax_S Pre_mszA)) in exact x).
Definition R_reg : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_reg_hi Pre_rip s_reg with Some R => R | None => [] end) in exact x).
Definition R_real : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_real Pre_mszA s_real with Some R => R | None => [] end) in exact x).
Definition T1 : axst := ltac2:(tb__ "0|0|
S3bS4dS88S4aS81S37S47S48A5A2").
Definition T3 : axst := ltac2:(tb__ "0|0|
S3bS4dS88S53S83S8bS84A1S46S4fA5A2").

Definition cuts_ms : list axst := ltac2:(tb__ "0|0|
S0S2eS5aS0S2eS5bS0S2eS5cS0S2eS55S3S2eA1A3A3A3A3").
Definition exits_ms : list axst := ltac2:(tb__ "0|0|
S0S2eS4eS0S2eS47S0S2eS46S0S2eS4cS0S2eS4bS3S2eA1A3A3A3A3A3").
Definition cutpcs_ms : list Z := ltac2:(tb__ "0|0|
S0S20S89S0S20S71S0S20S70S3S20A1A3A3A3").
Definition FUELS : nat := 600%nat.

Definition s_L_in : wsub := ltac2:(tb__ "0|1|
S0S4S1fSdA2M0S1S1fSdP8cS27A4S3G0A1A3").
Definition s_L_bk : wsub := ltac2:(tb__ "0|1|
S0S4S1fSdA2M0S1S1fSdP8cS35S25SfZ1A1A2A4S3G0A1A3").

Lemma fr_reg_hi : ltac2:(tb__ "0|1|
S3dScSbS13A1M0A1S87S57S81S4aA3S9G0S48A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_reg_lo : ltac2:(tb__ "0|1|
S3dScSbS13A1M0A1S87S58S82S4aA3S9G0S48A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_reg_hi : ltac2:(tb__ "0|0|
S3dS5S86S57S81S4aS48S7cS2fS2eS30S8aA4A5S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_reg_lo : ltac2:(tb__ "0|0|
S3dS5S86S58S82S4aS48S7cS2fS2eS30S8aA4A5S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_real : ltac2:(tb__ "0|1|
S3dScSbS13A1M0A1S87S46S83S53A3S9G0S4fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_real : ltac2:(tb__ "0|0|
S3dS5S86S46S83S53S4fS7cS2fS2eS30S85A4A5S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition vcuts_ms : list vnodeA := ltac2:(tb__ "0|1|
S0S39S3aS5aZc8SfZ0A1A3S0S39S3aS5bZ4fSfS43Z2Z3fA2M0A1A3S0S39S3aS5cZ27SfS44G0Z8A2A1A3S0S39S3aS55Z64S25A3S3S39A1A3A3A3A3").
Definition vexits_ms : list vnodeA := ltac2:(tb__ "0|4|
S0S39S3aS4eZ0SfS45S43Z2M0Z40A2Z1M1A2A1A3S0S39S3aS47Z50SfS43G0Z3fA2M2A1A3S0S39S3aS46Z28SfS44G2Z8A2A1A3S0S39S3aS4cZ65M3S27A3S0S39S3aS4bG3S35S25SfG1A1A2A3S3S39A1A3A3A3A3A3").
Lemma echeck_ms : ltac2:(tb__ "0|0|
S3dS5S8dS7eS59S5eS76S6dS6eA6S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check_ms : ltac2:(tb__ "0|0|
S3dS5S3cS7eS59S5eS76S66S67A6S6A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELS cutpcs_ms NF vcuts_ms vexits_ms cuts_ms exits_ms eq_refl eq_refl echeck_ms). Qed.

Lemma ent_L_in : ltac2:(tb__ "0|0|
S3dS5S31S4cS56S6bA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_L_bk : ltac2:(tb__ "0|0|
S3dS5S31S4bS56S6aA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Asan_memsetZ.

(* [comment removed for export] *)
Module DrvExitStates2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "sym_runA"; "mkLeafA"; "ax_X"; "ax_base"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "Some"; "option"; "true"; "list"; "pair"; "bool"; "prod"; "false"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sv"; "SLit"; "sobj"; "ss_next"; "ss_lenient"; "reg_sv"; "ss_facts"; "ss_pc"; "DRom"; "cell"; "mkObj"; "mkSS"; "sprop"; "ss_fcsr"; "ss_fregs"; "ss_objs"; "ss_regs"; "ss_resv"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_out.WLoutS"; "Pre_wl2"; "D"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvExitStates"; "CUTS_X"; "W_2"; "W_3"; "W_4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "facts_exit"; "exit_ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExitStates2"; "C_2"; "C_3"; "C_4"; "Tf_2"; "Tf_3"; "Tf_4"; "obind"; "s_2"; "s_3"; "s_4"; "R_2"; "R_3"; "R_4"; "splits"; "F_2"; "F_3"; "F_4"; "T_2"; "T_3"; "T_4"; "O_b2z"; "S5_2"; "S5_3"; "S5_4"; "app_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.PFAddr"; "SBUF"; "FILE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Musl_wl_out.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvExitStates.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvExitStates.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition obind {A B} (o : option A) (f : A -> option B) : option B :=
  match o with Some x => f x | None => None end.

Definition O_b2z : sobj := ltac2:(tb__ "0|1|
S1fS16Z0A1M0G0G0SaS1eA1S1dP6A1A5").
Definition app_obj (S : sstate) (o : sobj) : sstate := ltac2:(tb__ "0|0|
S20S1cVS;A1S25VS;A1S23VS;A1S22VS;A1S26VS;A1S13S17S24VS;A1S9S17Vo;SaS17A1A3A3S1bVS;A1S18VS;A1S19VS;A1A9").

Definition splits (m : Z) (S : sstate) : option sstate := ltac2:(tb__ "0|0|
S3dS14S14S33VS;U0S16N88A1A3S14S3dS14S14S33R1U1S16N68A1A3S14S3dS14S14S33R1U5S16S58S51Z78A2A1A3S14S3dS14S14S33R1U6S16S58S51Z7cA2A1A3S14S33R1U8S16S58S50Vm;A2A1A3LS4;A4LS3;A4LS2;A4LS1;A4").

Definition finish (S5 : sstate) : sstate := ltac2:(tb__ "0|0|
S4fS5dVS5;U8P5A3S4bA2").

Definition wl_sub_head (m : Z) : wsub := ltac2:(tb__ "0|2|
S9S11S2aS15A2M0SfS2aS15PcS16S50A1A4S9G0SfS2aS15PdS16Vm;A1A4S9G0SfS2aS15PeS16Z0A1M1A4S9G0SfS2aS15PfG1A4SaG0A1A3A3A3A3").

Definition S5_2 : sstate := Eval vm_compute in (match splits 2 (ax_S W_2) with Some s => s | None => ax_S W_2 end).
Lemma splits_2 : ltac2:(tb__ "0|0|
S0ScS14A1S44Z2S4S2eA1A2SbS14S4cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_2s : sstate := Eval vm_compute in (finish S5_2).
Lemma finish_2 : finish S5_2 = C_2s. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_2 : axst := ax_setS W_2 C_2s.
Definition s_2 : wsub := Eval vm_compute in (wl_sub_head 2 ++ infer_sub 10 C_2s (ax_S WLoutS.Pre_wl2)).
Definition R_2 : list sobj := Eval vm_compute in (match entails_frA C_2 WLoutS.Pre_wl2 s_2 with Some R => R | None => [] end).
Lemma efr_2 : ltac2:(tb__ "0|1|
S0ScSeS17A1M0A1S56S37S28S3eA3SbG0S41A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_2 : ltac2:(tb__ "0|0|
S0S10S55S37S28S3eS41S9S2S29SaS2A1A3A5SdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_2 : axst := Eval vm_compute in (import_postA s_2 WLoutS.Pre_wl2 WLoutS.D C_2 R_2).
Lemma T_2_eq : ltac2:(tb__ "0|0|
S0S2S57S3eS28S29S37S41A5S48A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Tf_2 : axst := Eval vm_compute in (ax_add_facts facts_exit T_2).
Lemma Tf_2_eq : ltac2:(tb__ "0|0|
S0S2S54S35S48A2S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_F2__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S2cU7d0S2dS3aSdA5").
Local Strategy expand [run_F2__R].
Definition F_2 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1X Tf_2 (ro1__)))) run_F2__R).
Lemma run_F2 : ltac2:(tb__ "0|1|
S0ScSeS3A1M0A1S5S2cU7d0S2dS3aSdA5SbG0S9S3S6S45S52A2SaS3A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_F2__R <: run_F2__R = Some [mkLeafA F_2 RsCut]). Qed.

Definition S5_3 : sstate := Eval vm_compute in (match splits 4 (ax_S W_3) with Some s => s | None => ax_S W_3 end).
Lemma splits_3 : ltac2:(tb__ "0|0|
S0ScS14A1S44Z4S4S2fA1A2SbS14S4dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_3s : sstate := Eval vm_compute in (finish S5_3).
Lemma finish_3 : finish S5_3 = C_3s. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_3 : axst := ax_setS W_3 C_3s.
Definition s_3 : wsub := Eval vm_compute in (wl_sub_head 4 ++ infer_sub 10 C_3s (ax_S WLoutS.Pre_wl2)).
Definition R_3 : list sobj := Eval vm_compute in (match entails_frA C_3 WLoutS.Pre_wl2 s_3 with Some R => R | None => [] end).
Lemma efr_3 : ltac2:(tb__ "0|1|
S0ScSeS17A1M0A1S56S38S28S3fA3SbG0S42A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_3 : ltac2:(tb__ "0|0|
S0S10S55S38S28S3fS42S9S2S29SaS2A1A3A5SdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_3 : axst := Eval vm_compute in (import_postA s_3 WLoutS.Pre_wl2 WLoutS.D C_3 R_3).
Lemma T_3_eq : ltac2:(tb__ "0|0|
S0S2S57S3fS28S29S38S42A5S49A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Tf_3 : axst := Eval vm_compute in (ax_add_facts facts_exit T_3).
Lemma Tf_3_eq : ltac2:(tb__ "0|0|
S0S2S54S35S49A2S3bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_F3__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S2cU7d0S2dS3bSdA5").
Local Strategy expand [run_F3__R].
Definition F_3 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1X Tf_3 (ro2__)))) run_F3__R).
Lemma run_F3 : ltac2:(tb__ "0|1|
S0ScSeS3A1M0A1S5S2cU7d0S2dS3bSdA5SbG0S9S3S6S46S52A2SaS3A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_F3__R <: run_F3__R = Some [mkLeafA F_3 RsCut]). Qed.

Definition S5_4 : sstate := Eval vm_compute in (match splits 6 (ax_S W_4) with Some s => s | None => ax_S W_4 end).
Lemma splits_4 : ltac2:(tb__ "0|0|
S0ScS14A1S44Z6S4S30A1A2SbS14S4eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_4s : sstate := Eval vm_compute in (finish S5_4).
Lemma finish_4 : finish S5_4 = C_4s. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_4 : axst := ax_setS W_4 C_4s.
Definition s_4 : wsub := Eval vm_compute in (wl_sub_head 6 ++ infer_sub 10 C_4s (ax_S WLoutS.Pre_wl2)).
Definition R_4 : list sobj := Eval vm_compute in (match entails_frA C_4 WLoutS.Pre_wl2 s_4 with Some R => R | None => [] end).
Lemma efr_4 : ltac2:(tb__ "0|1|
S0ScSeS17A1M0A1S56S39S28S40A3SbG0S43A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_4 : ltac2:(tb__ "0|0|
S0S10S55S39S28S40S43S9S2S29SaS2A1A3A5SdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_4 : axst := Eval vm_compute in (import_postA s_4 WLoutS.Pre_wl2 WLoutS.D C_4 R_4).
Lemma T_4_eq : ltac2:(tb__ "0|0|
S0S2S57S40S28S29S39S43A5S4aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Tf_4 : axst := Eval vm_compute in (ax_add_facts facts_exit T_4).
Lemma Tf_4_eq : ltac2:(tb__ "0|0|
S0S2S54S35S4aA2S3cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_F4__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S2cU7d0S2dS3cSdA5").
Local Strategy expand [run_F4__R].
Definition F_4 : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => ((leaf1X Tf_4 (ro3__)))) run_F4__R).
Lemma run_F4 : ltac2:(tb__ "0|1|
S0ScSeS3A1M0A1S5S2cU7d0S2dS3cSdA5SbG0S9S3S6S47S52A2SaS3A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_F4__R <: run_F4__R = Some [mkLeafA F_4 RsCut]). Qed.

Lemma F_at : ltac2:(tb__ "0|2|
S2S34S2R1S9S2S45S9S2S46S9S2S47SaS2A1A3A3A3A3S1S0S2bS1cS4R2A1M0A1M1S36A3S1S0ScS59A1S53S2cG1A2SbS59S5aA2A3S1S0S15S1aG0Z11A2S16Z5eA1A3S0S15S1aG0ZaA2S16Z0A1A3A2A2A2F_;FF;").
Proof. intros F [<-|[<-|[<-|[]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma Tf_shape : ltac2:(tb__ "0|1|
S2S34S2R1S9S2S3aS9S2S3bS9S2S3cSaS2A1A3A3A3A3S1S0S10S19S4R2A1M0A1S12A3S0S2aS18G0A1P7dA3A2F_;FT;").
Proof. intros T [<-|[<-|[<-|[]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C_shape : ltac2:(tb__ "0|2|
S2S34S2R1S9S2S37S9S2S38S9S2S39SaS2A1A3A3A3A3S1S0S2aS18S4R2A1M0A1S5cA3S1S0SeS11S15S15A2M1A1S7R2A1SaG1A1A3S1S0S15S8R2A1S16S5bA1A3S0S10S27G0A1SdA3A2A2A2F_;FC;").
Proof. intros C [<-|[<-|[<-|[]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma W_shape : ltac2:(tb__ "0|2|
S2S34S2R1S9S2S2eS9S2S2fS9S2S30SaS2A1A3A3A3A3S1S0S2aS18S4R2A1M0A1S5cA3S1S0SeS11S15S15A2M1A1S7R2A1SaG1A1A3S1S0S15S8R2A1S16S5bA1A3S1S0S10S19G0A1S12A3S0SeS21A1S1bG0A1S35A3A2A2A2A2F_;FW;").
Proof. intros W [<-|[<-|[<-|[]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma s_vals : ltac2:(tb__ "0|2|
S31S2bS34S11S31S2bA2M0SfS31S2bR2R1A4S9G0SfS31S2bS3eZ2A4S9G0SfS31S2bS3fZ4A4S9G0SfS31S2bS40Z6A4SaG0A1A3A3A3A3S1S0S15S32R3PcA2S16S50A1A3S1S0S15S32R3PdA2S16R2A1A3S1S0S15S32R3PeA2S16Z0A1M1A3S0S15S32R3PfA2G1A3A2A2A2F_;Fm;Fs;").
Proof. intros s m H; repeat (destruct H as [H|H]; [injection H as <- <-; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2|]); destruct H. Qed.
End DrvExitStates2.

(* [comment removed for export] *)
Module DrvExit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "False"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "Some"; "option"; "true"; "false"; "app"; "nat"; "length"; "prod"; "pair"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "WriteEv"; "ExitEv"; "m_fs"; "FdEntry"; "FdChannel"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "sv"; "SLit"; "ss_next"; "sstate"; "ss_lenient"; "ob_dflt"; "rl"; "dflt_writable"; "is_arr"; "ob_cells"; "ob_hi"; "ob_lo"; "reg_sv"; "smatch"; "sprop"; "ss_objs"; "swf"; "agree_below"; "holds"; "rw"; "ss_pc"; "sprop_below"; "ss_facts"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "mkLeafA"; "sym_runA"; "ax_base"; "ax_X"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "BLit"; "cells_bytes"; "beval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.PFAddr"; "SBUF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "PEND"; "facts_exit"; "Pre_exitP"; "supportedP"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "w_tr"; "etriple"; "triple"; "w_cfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit.Exit"; "Kf"; "ch1"; "Kw"; "EVS"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_out.WLoutS"; "Pre_wl2"; "D"; "@Stdlib.ZArith.BinInt.Z"; "add"; "sub"; "to_nat"; "of_nat"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit.Exit.Flush"; "Jp"; "rho_wl"; "WLF"; "f6"; "@Stdlib.Lists.List"; "nth_error"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvExitStates"; "CUTS_X"; "FUEL_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExitStates2"; "S5_2"; "S5_3"; "S5_4"; "C_2s"; "C_3s"; "C_4s"; "splits"; "T_2"; "T_3"; "T_4"; "Tf_2"; "Tf_3"; "Tf_4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_out.WLout"; "Kw"; "MSG"; "Posts_wl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "rho_set_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "state_nolist"; "set_rl"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "virt"; "mat_equiv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.PArith.BinPos.Pos"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundI SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj SymCall SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SysA MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import SpecConsts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Musl_wl_out.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvExitStates.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvExitStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExitStates2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma SPA_morph : ltac2:(tb__ "0|1|
S4eS4eS3bS22S1dS1dS4S11Q40A1A1S51S0S4SfS1fS1fA2M0A1S3fR6A1S7G0A1A3S0S5S36S21R6A1S3eR7A1A2SaA3S2cS37R6S39R8A1S8aR4R3A2A4S2cS37R6R8S8aR5R4A2A4F_;RbR7R5S52R4A1S86S55R4A1A1A4RbR7R6S52R5A1S86S55R5A1A1A4F_;S4cS37RcRaR8R6R5A6S4cS37RcS40RbRaA2R8R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;FS';FA;FJ';FJ;").
Proof.
  intros J J' A S' rho rho' tp w HX Hb HS HJ [(Hsm & HMI & Hwf & Hsh & Hhz) Hk].
  split; [|apply HJ; exact Hk].
  split; [apply HS; exact Hsm|]. split; [exact HMI|].
  split; [unfold axwf; cbn [ax_S ax_X ax_base ax_setS]; rewrite HX; cbn [forallb]; exact Hb|].
  split; [|exact Hhz]. unfold shadow_ok. cbn [ax_X ax_setS]. rewrite HX. constructor.
Qed.

Lemma smatch_splits : ltac2:(tb__ "0|0|
S4bS22S22S1dSfS4S14A1S87A2S0S9S22A1S76R5R4A2S8S22R3A2A3S2cS37R3R5R2A4S2cS37R4R5R3A4F_;F_;Fw;Frho;FS5;FS;Fm;").
Proof.
  intros m S S5 rho w H Hsm. unfold splits, obind in H.
  destruct (split_obj_at S 0 (SLit (-136))) as [S1|] eqn:E1; [|discriminate].
  destruct (split_obj_at S1 1 (SLit (-104))) as [S2|] eqn:E2; [|discriminate].
  destruct (split_obj_at S2 5 (SLit (FILE + 120))) as [S3|] eqn:E3; [|discriminate].
  destruct (split_obj_at S3 6 (SLit (FILE + 124))) as [S4|] eqn:E4; [|discriminate].
  eapply smatch_split; [exact H|]. eapply smatch_split; [exact E4|]. eapply smatch_split; [exact E3|].
  eapply smatch_split; [exact E2|]. eapply smatch_split; [exact E1|]. exact Hsm.
Qed.

Lemma agree_below_sym : ltac2:(tb__ "0|0|
S4aS1dS1dS30R3R2R1A3S30R4R2R3A3F_;Frho';Frho;Fn;").
Proof.
  intros n rho rho' (A & B & C). split; [intros i Hi; symmetry; apply A; exact Hi|].
  split; [intros l; symmetry; apply B | intros a; symmetry; apply C].
Qed.

Section Exit.
Variable ok : assn.
Variable J0 : jpredA.
Variable Spec : list event -> Prop.
Variables n c : Z.

Definition ch1 : word := Z_to_bv 64 1.
Definition EVS (k : nat) : list event := ltac2:(tb__ "0|1|
S5bS11Q8A1M0S14S16S58A1S5dG0Vk;S46Vn;A1A3A4").

Definition Kw (k : nat) : jpredA := ltac2:(tb__ "0|1|
S1dS4S11Q40A1A1S4S14A1M0S15S2G0G0S1VJ0;R5R4R1R2A4S0G0R3ScS14R1S5aVk;A1A3A3A2Ltr0;A2Lmd;Ltr;Lt;Lr;").

Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S4S14A1S15VJ0;R4R3R2R1A4S0S9S19A1S1bS1cR2A1S58A2S8S19S1aS58A1A2A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HokK : ltac2:(tb__ "0|0|
SdS4fS37Vok;S59R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
SdS89S37Vok;S59R1A1A3Fk;").
Hypothesis Hokh : ok_halted ok Spec.
Hypothesis Hspec : ltac2:(tb__ "0|1|
S1dS4S11Q40M0A1A1S4S14A1S15VJ0;R4R3R2R1A4VSpec;ScS14R3ScS14S5bS11Q8A1S14S16S58A1S46Vn;A1A4S6S14S17S12G0Vc;A2S18R2A1A2S7S14A1A3A3A3A1F_;Fmd;Ftr;Ft;Fr;").

Definition Kf (r1 : valuation) (tp : list word) (k : nat) : jpredA := ltac2:(tb__ "0|1|
S1dS4S11Q40A1A1M0S4S14A1S15S1S0G0R3Vtp;A3S59Vk;Vr1;R3R2R1A5A2Lmd;Ltr;Lt;L_;").

Lemma J0_mat : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S4S14A1S15S15S8bS37R4R2R1A4VJ0;R6R5R4R3A4VJ0;R7R6R5R3A4F_;F_;Fmd';Fmd;Ftr;Ft;Fr;").
Proof. intros r t tr md md' Hme HJ. eapply Hst0; [apply agree_below_refl | exact Hme | exact HJ]. Qed.

Lemma Kf_stable : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1SdS4aS50S37R1S57R4R3R2A3A3Flvl;Fk;Ftp;Fr1;").
Proof.
  intros r1 tp k lvl r r' t tr md md' Hag Hme [Ht (tr0 & HJ & Htr)]. split; [exact Ht|].
  exists tr0. split; [eapply J0_mat; eauto | exact Htr].
Qed.
Lemma Kf_okK : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1SdS4fS37Vok;S57R3R2R1A3A3Fk;Ftp;Fr1;").
Proof. intros r1 tp k r t tr ms md msv' [_ HK]. exact (HokK k r1 t tr ms md msv' HK). Qed.
Lemma Kf_okP : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1SdS89S37Vok;S57R3R2R1A3A3Fk;Ftp;Fr1;").
Proof. intros r1 tp k r t tr ms md x8 [_ HK]. exact (HokP k r1 t tr ms md x8 HK). Qed.

Lemma Kw0_of_J0 : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S4S14A1S15VJ0;R4R3R2R1A4S59U0R5R4R3R2A5F_;Fmd;Ftr;Ft;Fr;").
Proof. intros r t tr md HJ. exists tr. split; [exact HJ|]. unfold EVS. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma okK_J0 : ok_frameA segs ok J0.
Proof. intros r t tr ms md msv' HJ. exact (HokK 0%nat r t tr ms md msv' (Kw0_of_J0 _ _ _ _ HJ)). Qed.
Lemma okP_J0 : ok_pframeA segs ok J0.
Proof. intros r t tr ms md x8 HJ. exact (HokP 0%nat r t tr ms md x8 (Kw0_of_J0 _ _ _ _ HJ)). Qed.

Section Plain.
Variables P E : axst.
Hypothesis HPEND : PEND n = [].
Hypothesis Hrun : ltac2:(tb__ "0|1|
S0S9S4S3aA1M0A1S3dS5eS6fS6eVP;SaA5S8G0S6S3aS3cVE;S82A2S7S3aA1A3A2A3").
Hypothesis HnP : ltac2:(tb__ "0|0|
S0S4aS21S39VP;A1A1S56A3").
Hypothesis HlP : ltac2:(tb__ "0|0|
S0S5S23S39VP;A1A1SbA3").
Hypothesis Hi : ltac2:(tb__ "0|0|
S0S9S65A1S83S5eS33S39VE;A1A1A2S8S65S66A2A3").
Hypothesis H17 : ltac2:(tb__ "0|0|
S0S1fS2bS39VE;A1Z11A2S20Z5eA1A3").
Hypothesis H10 : ltac2:(tb__ "0|0|
S0S1fS2bS39VE;A1ZaA2S20Vc;A1A3").
Hypothesis HnE : ltac2:(tb__ "0|0|
S0S4aS21S39VE;A1A1S56A3").
Hypothesis Hc : 0 <= c < 256.

Lemma plain_sum : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S54S37Vok;S4cS37VJ0;VP;R2R1A5S51S3L_;A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply (runA_tr segs ok FUEL_X CUTS_X P _ J0 rho tp); [exact Hrun | exact HlP | apply okK_J0 | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply (triple_exitA segs ok Spec J0 E rho1 tp c okK_J0 okP_J0 Hokh); [rewrite HnE; exact Hst0 | exact Hi | left; exact H17 | exact H10 | exact Hc |].
  intros tr md HJ. pose proof (Hspec _ _ _ _ HJ) as X. rewrite HPEND in X. cbn [map app] in X. exact X.
Qed.

Lemma plain_sum_ex : ltac2:(tb__ "0|2|
S1dS4S11Q40M0A1A1S53S37S4cS37VJ0;VP;R2R1A5S51S2S4S14A1M1G1S2S15S15S1VJ0;R5R4R2R1A4S0G1S52R3A1ScS14R2ScS14S5bS11Q8A1S14S16S58A1S46Vn;A1A4S6S14S17S12G0Vc;A2S18R1A1A2S7S14A1A3A3A3A3A2Lmd;A2Ltr;A2Lw';A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply (erunA_tr segs FUEL_X CUTS_X P _ J0 rho tp); [exact Hrun | exact HlP | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  eapply etriple_conseq; [intros w Hw; exact Hw | | apply (etriple_exitA segs J0 E rho1 tp c); [rewrite HnE; exact Hst0 | exact Hi | left; exact H17 | exact H10 | exact Hc]].
  intros w' (tr & md & HJ & Hw). exists tr, md. split; [| rewrite HPEND; cbn [map app]; exact Hw].
  eapply Hst0; [apply agree_below_sym; rewrite <- HnP; exact Hag1 | apply mat_equiv_refl | exact HJ].
Qed.
End Plain.

Section Flush.
Variable m : Z.
Variable W : axst.
Variables S5 Cs : sstate.
Variable o8 : sobj.
Variable bl : list bexp.
Variable s : wsub.
Variable R : list sobj.
Variables T Tf F : axst.

Variable P : axst.
Hypothesis Hc0 : c = 0.
Hypothesis HrunW : ltac2:(tb__ "0|1|
S0S9S4S3aA1M0A1S3dS5eS6fS6eVP;SaA5S8G0S6S3aS3cVW;S82A2S7S3aA1A3A2A3").
Hypothesis HnP : ltac2:(tb__ "0|0|
S0S4aS21S39VP;A1A1S56A3").
Hypothesis HlP : ltac2:(tb__ "0|0|
S0S5S23S39VP;A1A1SbA3").
Hypothesis HnW : ltac2:(tb__ "0|0|
S0S4aS21S39VW;A1A1S56A3").
Hypothesis HXW : ax_X W = [].
Hypothesis HbW : ltac2:(tb__ "0|0|
S0S1fS3eVW;A1S20S38A1A3").
Hypothesis HfW : ltac2:(tb__ "0|0|
S0S4S2dA1S35S39VW;A1A1S47A3").
Hypothesis Hsplits : ltac2:(tb__ "0|0|
S0S9S22A1S76Vm;S39VW;A1A2S8S22VS5;A2A3").
Hypothesis Hfinish : finish S5 = Cs.
Hypothesis Hnl : state_nolist S5 = true.
Hypothesis Hrl5 : state_has_rl 5 S5 = false.
Hypothesis Ho8 : ltac2:(tb__ "0|0|
S0S9S1eA1S6bS1eS2eVS5;A1U8A3S8S1eVo8;A2A3").
Hypothesis Ho8lo : ltac2:(tb__ "0|0|
S0S1fS2aVo8;A1S20S45A1A3").
Hypothesis Ho8hi : ltac2:(tb__ "0|0|
S0S1fS29Vo8;A1S20S61S45Vm;A2A1A3").
Hypothesis Ho8w : ltac2:(tb__ "0|0|
S0S5S26S24Vo8;A1A1SaA3").
Hypothesis Ho8a : ltac2:(tb__ "0|0|
S0S5S27S24Vo8;A1A1SbA3").
Hypothesis Hcb : ltac2:(tb__ "0|1|
S0S9S4S41A1M0A1S43S28Vo8;A1S20S45A1Z0S63S62S61S45Vm;A2S45A2A1A4S8G0Vbl;A2A3").
Hypothesis Hbl : ltac2:(tb__ "0|1|
S1dS0S4S11Q8A1M0A1S5bS41G0S44R1A1Vbl;A4S46Vn;A1A3Fr;").
Hypothesis Hm1 : ltac2:(tb__ "0|0|
S0S4bS64SeS11Q8A1S46Vn;A1A2A1Vm;A3").
Hypothesis Hm2 : 1 <= m <= 6.
Hypothesis HswfC : swf Cs = true.
Hypothesis HnC : ss_next Cs = NF.
Let C : axst := ax_setS W Cs.
Hypothesis Hefr : ltac2:(tb__ "0|1|
S0S9S4S1eA1M0A1S8eVC;S5fVs;A3S8G0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S5S8dVC;S5fVs;VR;S6S3bS60S7S3bA1A3A5SaA3").
Hypothesis S12 : ltac2:(tb__ "0|0|
S0S1fS88Vs;PcA2S20S45A1A3").
Hypothesis S13 : ltac2:(tb__ "0|0|
S0S1fS88Vs;PdA2S20Vm;A1A3").
Hypothesis S14 : wsub_get s 14 = SLit 0.
Hypothesis S15 : wsub_get s 15 = SLit 0.
Hypothesis HT : ltac2:(tb__ "0|0|
S0S3bS8fVs;S5fS60VC;VR;A5VT;A3").
Hypothesis HnT : ss_next (ax_S T) = 125%positive.
Hypothesis HTf : ltac2:(tb__ "0|0|
S0S3bS8cS47VT;A2VTf;A3").
Hypothesis HlTf : ltac2:(tb__ "0|0|
S0S5S23S39VTf;A1A1SbA3").
Hypothesis HrunF : ltac2:(tb__ "0|1|
S0S9S4S3aA1M0A1S3dS5eU7d0S6eVTf;SaA5S8G0S6S3aS3cVF;S82A2S7S3aA1A3A2A3").
Hypothesis HiF : ltac2:(tb__ "0|0|
S0S9S65A1S83S5eS33S39VF;A1A1A2S8S65S66A2A3").
Hypothesis H17F : ltac2:(tb__ "0|0|
S0S1fS2bS39VF;A1Z11A2S20Z5eA1A3").
Hypothesis H10F : ltac2:(tb__ "0|0|
S0S1fS2bS39VF;A1ZaA2S20Z0A1A3").

Definition f6 (r : valuation) : positive -> list byte := ltac2:(tb__ "0|1|
S4aS5S4S11Q8A1M0A1L_;S90R1P6A2S7G0A1S25Vr;R1A2X5x2Ll;").
Definition rho_wl (r : valuation) : valuation := ltac2:(tb__ "0|0|
S81S85Vr;S6aVr;A1A2P5S46Vn;A1A3").

Lemma rho_wl_5 : ltac2:(tb__ "0|0|
S1dS0S4S11Q8A1A1S25S68R1A1P5A2S46Vn;A1A3Fr;"). Proof. intros r. reflexivity. Qed.
Lemma rho_wl_6 : ltac2:(tb__ "0|1|
S1dS0S4S11Q8A1M0A1S25S68R1A1P6A2S7G0A1A3Fr;"). Proof. intros r. reflexivity. Qed.

Definition WLF (r : valuation) : Prop := ltac2:(tb__ "0|3|
S1S0S4S11Q8A1M0A1M1S25Vr;P5A2S46Vn;A1A3S1S0G1S25Vr;P6A2S7G0A1A3S1S0S4bS13Q40M2S32Vr;PdA2A2Vm;A3S0S4bS13G2S32Vr;PfA2A2Z0A3A2A2A2").
Definition Jp (r1 : valuation) (tp : list word) : jpredA := ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S4S14A1S15S1S69R4A1S57Vr1;Vtp;U0R4R3R2R1A7A2Lmd;Ltr;Lt;Lr;").

Lemma Jp_stable : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S50S37P5cS67R2R1A2A3Ftp;Fr1;").
Proof.
  intros r1 tp r r' t tr md md' Hag Hme [(A5 & A6 & A13 & A15) HK].
  split; [| eapply (Kf_stable r1 tp 0%nat 92%positive); [exact Hag | exact Hme | exact HK]].
  destruct Hag as (Hw & Hl & _). unfold WLF.
  rewrite <- (Hl 5%positive), <- (Hl 6%positive), <- (Hw 13%positive ltac:(lia)), <- (Hw 15%positive ltac:(lia)).
  repeat split; assumption.
Qed.

Lemma Kw_Jp_Kf : ltac2:(tb__ "0|1|
S1dS4S11Q40A1A1M0SdS1dG0S4S14A1S15S7dS67R7R6A2S46Vn;A1S7S11Q8A1A1R5R4R3R2R1A8S57R8R7R6R5R4R3R2A7F_;Fmd;Ftr;Ft;Fr;Fk;Ftp;Fr1;").
Proof.
  intros r1 tp k r t tr md (tr0 & [_ [Ht (tr00 & HJ & ->)]] & ->). split; [exact Ht|].
  exists tr00. split; [exact HJ|]. unfold WLout.TRk, WLout.MSG, EVS. cbn [firstn map]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma MSG_len : ltac2:(tb__ "0|2|
S0SdSeS11Q8A1M0S7eS46Vn;A1M1S7G0A1A2A2SeG0G1A2A3").
Proof. unfold WLout.MSG. rewrite app_nil_r. reflexivity. Qed.

Lemma wl_call : ltac2:(tb__ "0|5|
S1dS4S11Q40A1A1M0S1dG0S54S37Vok;S4cS37S67R4R3A2M1S5fR2R1A5S4dS37S7dG1S46Vn;A1M2S7S11Q8A1M3A1M4SeG3S7eG2G4A2A2A4P5cR2R1S7fA6A4Ftp2;Frho2;Ftp;Fr1;").
Proof.
  intros r1 tp rho2 tp2.
  apply triple_SPA_pure. intros tr md [(A5 & A6 & A13 & A15) _].
  apply (triple_SPA_conseq_J segs ok _ (Jp r1 tp)); [intros t md0 (HJ & _ & _); exact HJ|].
  apply (WLout.wl2_sum ok (Jp r1 tp) rho2 tp2 (PEND n) [] A5 A6).
  - rewrite A13. symmetry. exact Hm1.
  - rewrite A15. reflexivity.
  - rewrite MSG_len. unfold max_write_total. lia.
  - apply Jp_stable.
  - intros k r t tr0 ms md0 msv' HK HMI Hh Hp Hstep.
    exact (Kf_okK r1 tp k r t tr0 ms md0 msv' (Kw_Jp_Kf r1 tp k r t tr0 md0 HK) HMI Hh Hp Hstep).
  - intros k r t tr0 ms md0 x8 HK Hp Ho.
    exact (Kf_okP r1 tp k r t tr0 ms md0 x8 (Kw_Jp_Kf r1 tp k r t tr0 md0 HK) Hp Ho).
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd _ _ _ _ HJ).
  - lia.
Qed.

Lemma wl_call_ex : ltac2:(tb__ "0|5|
S1dS4S11Q40A1A1M0S1dG0S53S37S4cS37S67R4R3A2M1S5fR2R1A5S4dS37S7dG1S46Vn;A1M2S7S11Q8A1M3A1M4SeG3S7eG2G4A2A2A4P5cR2R1S7fA6A3Ftp2;Frho2;Ftp;Fr1;").
Proof.
  intros r1 tp rho2 tp2 w Hw. pose proof Hw as [Hsm [(A5 & A6 & A13 & A15) HK]].
  apply (WLout.wl2_sum_ex (Jp r1 tp) rho2 tp2 (PEND n) [] A5 A6).
  - rewrite A13. symmetry. exact Hm1.
  - rewrite A15. reflexivity.
  - rewrite MSG_len. unfold max_write_total. lia.
  - apply Jp_stable.
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd _ _ _ _ HJ).
  - lia.
  - exact Hw.
Qed.

Lemma reshape : ltac2:(tb__ "0|1|
S1dS4S11Q40A1A1S1dS51S4cS37S57R4R3U0M0A3VW;R2R3R1A6S4cS37S57R5R4G0A3VC;S68R3A1R4R2A6F_;Fw;Frho;Ftp;Fr1;").
Proof.
  intros r1 tp rho w Hsp.
  unfold C. eapply (SPA_morph (Kf r1 tp 0) (Kf r1 tp 0) W Cs rho (rho_wl rho)); [exact HXW | rewrite HnC, HbW; reflexivity | | intros HK; exact HK | exact Hsp].
  intros Hsm. rewrite <- Hfinish. unfold finish.
  pose proof (smatch_splits m (ax_S W) S5 rho (virt tp w) Hsplits Hsm) as H5.
  pose proof (smatch_set_rl segs rho (f6 rho) S5 (virt tp w) Hnl H5) as H6.
  pose proof (smatch_obj_to_list segs _ S5 (virt tp w) 8 5 o8 SBUF (SBUF + m) bl H6 Ho8 Ho8lo Ho8hi
                ltac:(unfold SBUF; lia) ltac:(unfold SBUF; lia) Ho8w Ho8a Hcb Hrl5) as H7.
  rewrite Hbl in H7. change (rho_set_rl (set_rl rho (f6 rho)) 5 (PEND n)) with (rho_wl rho) in H7.
  apply (smatch_carve_rom segs (rho_wl rho) (obj_to_list S5 8 5) (virt tp w) 0 0 6 (ss_next (obj_to_list S5 8 5)) H7).
  - rewrite <- Hfinish in HswfC. exact HswfC.
  - lia.
  - lia.
  - lia.
  - rewrite rho_wl_6. reflexivity.
  - intros k Hk. exfalso. lia.
  - apply Forall_forall. intros o _. unfold ranges_disjoint. cbn [fst snd]. lia.
Qed.

Lemma facts_rho_wl : ltac2:(tb__ "0|0|
S1dS5cS2dS31R1A1S47A3S5cS2dS31S68R2A1A1S47A3F_;Fr;").
Proof.
  intros r H. apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) H p Hp) as X.
  unfold facts_exit in Hp. destruct Hp as [<-|[<-|[<-|[<-|[<-|[]]]]]]; exact X.
Qed.

Lemma fb_facts : ltac2:(tb__ "0|0|
S0S5S6dS2dS34S56A1S47A3SaA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma flush_sum : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S54S37Vok;S4cS37VJ0;VP;R2R1A5S51S3L_;A4Ftp;Frho;").
Proof.
  intros rho tp.

  eapply (runA_tr segs ok FUEL_X CUTS_X P _ J0 rho tp); [exact HrunW | exact HlP | apply okK_J0 | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply triple_factsA. rewrite HfW. intros HF1.
  pose proof (facts_rho_wl rho1 HF1) as HFw.

  eapply triple_conseq with (P := SPA segs (Kf rho1 tp 0) C (rho_wl rho1) tp); [ | intros w Hw; exact Hw |].
  { intros w Hw. apply reshape. destruct Hw as [Hsm HJ]. split; [exact Hsm|]. split; [reflexivity|]. apply Kw0_of_J0. exact HJ. }

  apply (call_soundA segs ok (Kf rho1 tp 0) (Jp rho1 tp) (WLout.Kw (Jp rho1 tp) (PEND n) [] (length (WLout.MSG (PEND n) [])))
           (Kf rho1 tp (length (PEND n))) C WLoutS.Pre_wl2 s R WLout.Posts_wl _ (rho_wl rho1) tp Hefr).
  - exact Hchk.
  - intros rho2 tp2. apply wl_call.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval].
    split; [apply rho_wl_5|]. split; [apply rho_wl_6|]. split; [| reflexivity].
    apply Z_to_bv_small. rewrite two64. lia.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite MSG_len in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite HT.
    apply triple_SPA_pure. intros tr md [Et _]. subst tpL.
    apply (triple_SPA_conseq_J segs ok _ (Kf rho1 tp (length (PEND n)))); [intros t md0 (HJ & _ & _); exact HJ|].

    assert (HF' : Forall (holds rho') facts_exit).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S C)) (rho_wl rho1) rho' p Hag'
               ltac:(unfold C; cbn [ax_S ax_setS]; rewrite HnC; exact (proj1 (forallb_forall _ _) fb_facts p Hp)))).
      exact (proj1 (Forall_forall _ _) HFw p Hp). }
    eapply triple_conseq with (P := SPA segs (Kf rho1 tp (length (PEND n))) Tf rho' tp); [ | intros w Hw; exact Hw |].
    { intros w [Hsm HJ]. split; [|exact HJ]. rewrite <- HTf. apply smatchA_add_facts; [exact Hsm | exact HF' | rewrite HnT; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }

    eapply (runA_tr segs ok 2000%nat CUTS_X Tf _ (Kf rho1 tp (length (PEND n))) rho' tp); [exact HrunF | exact HlTf | apply Kf_okK | apply Kf_stable |].
    intros L2 rho3 [<-|[]] Hag3. cbn [la_state].
    apply (triple_exitA segs ok Spec (Kf rho1 tp (length (PEND n))) F rho3 tp 0 (Kf_okK _ _ _) (Kf_okP _ _ _) Hokh (Kf_stable _ _ _ _) HiF (or_introl H17F) H10F ltac:(lia)).
    intros tr2 md2 [_ (tr0 & HJ0 & ->)]. pose proof (Hspec _ _ _ _ HJ0) as X. rewrite Hc0 in X.
    unfold EVS. rewrite firstn_all, <- app_assoc. exact X.
Qed.

Lemma flush_sum_ex : ltac2:(tb__ "0|2|
S1dS4S11Q40M0A1A1S53S37S4cS37VJ0;VP;R2R1A5S51S2S4S14A1M1G1S2S15S15S1VJ0;R5R4R2R1A4S0G1S52R3A1ScS14R2ScS14S5bS11Q8A1S14S16S58A1S46Vn;A1A4S6S14S17S12G0Vc;A2S18R1A1A2S7S14A1A3A3A3A3A2Lmd;A2Ltr;A2Lw';A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply (erunA_tr segs FUEL_X CUTS_X P _ J0 rho tp); [exact HrunW | exact HlP | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply etriple_factsA. rewrite HfW. intros HF1.
  pose proof (facts_rho_wl rho1 HF1) as HFw.
  eapply etriple_conseq with (P := SPA segs (Kf rho1 tp 0) C (rho_wl rho1) tp); [ | intros w Hw; exact Hw |].
  { intros w Hw. apply reshape. destruct Hw as [Hsm HJ]. split; [exact Hsm|]. split; [reflexivity|]. apply Kw0_of_J0. exact HJ. }
  apply (call_completeA segs (Kf rho1 tp 0) (Jp rho1 tp) (WLout.Kw (Jp rho1 tp) (PEND n) [] (length (WLout.MSG (PEND n) [])))
           (Kf rho1 tp (length (PEND n))) C WLoutS.Pre_wl2 s R WLout.Posts_wl _ (rho_wl rho1) tp Hefr).
  - exact Hchk.
  - intros rho2 tp2. apply wl_call_ex.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval].
    split; [apply rho_wl_5|]. split; [apply rho_wl_6|]. split; [| reflexivity].
    apply Z_to_bv_small. rewrite two64. lia.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite MSG_len in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite HT.
    intros w0 [Hsm0 [Et HK0]]. subst tpL. revert w0 Hsm0 HK0.
    assert (HF' : Forall (holds rho') facts_exit).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S C)) (rho_wl rho1) rho' p Hag'
               ltac:(unfold C; cbn [ax_S ax_setS]; rewrite HnC; exact (proj1 (forallb_forall _ _) fb_facts p Hp)))).
      exact (proj1 (Forall_forall _ _) HFw p Hp). }
    assert (HE : etriple segs (SPA segs (Kf rho1 tp (length (PEND n))) Tf rho' tp)
              (fun w' => exists tr md, J0 rho tp tr md /\ w_tr w' = tr ++ map (WriteEv ch1) (PEND n) ++ [ExitEv (Z_to_bv 64 c) (m_fs md)])).
    { eapply (erunA_tr segs 2000%nat CUTS_X Tf _ (Kf rho1 tp (length (PEND n))) rho' tp); [exact HrunF | exact HlTf | apply Kf_stable |].
      intros L2 rho3 [<-|[]] Hag3. cbn [la_state].
      eapply etriple_conseq; [intros w Hw; exact Hw | | apply (etriple_exitA segs (Kf rho1 tp (length (PEND n))) F rho3 tp 0 (Kf_stable _ _ _ _) HiF (or_introl H17F) H10F ltac:(lia))].
      intros w' (tr2 & md2 & [_ (tr0 & HJ0 & ->)] & Hw). exists tr0, md2. split.
      - eapply Hst0; [apply agree_below_sym; rewrite <- HnP; exact Hag1 | apply mat_equiv_refl | exact HJ0].
      - rewrite Hw. unfold EVS. rewrite firstn_all, <- app_assoc, Hc0. reflexivity. }
    intros w0 Hsm0 HK0. apply HE. split; [| split; [reflexivity | exact HK0]]. rewrite <- HTf. apply smatchA_add_facts; [exact Hsm0 | exact HF' | rewrite HnT; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
Qed.
End Flush.

Lemma o8_2 : ltac2:(tb__ "0|4|
S2S1eS1eS1S0S9S1eA1S6bS1eS2eS70A1U8A3S8S1eR1A2A3S1S0S1fS2aR1A1S20S45A1M0A3S1S0S1fS29R1A1S20S61S45Z2A2M1A1A3S1S0S5S26S24R1A1M2A1SaA3S1S0S5S27G2A1SbA3S0S9S4S41A1M3A1S43S28R1A1G0Z0S63S62G1S45A2A1A4S8G3S6S41S42Z30A1S6S41S42ZaA1S7S41A1A3A3A2A3A2A2A2A2A2Lo;A2").
Proof. eexists. split; [reflexivity|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma o8_3 : ltac2:(tb__ "0|6|
S2S1eS1eS1S0S9S1eA1S6bS1eS2eS71A1U8A3S8S1eR1A2A3S1S0S1fS2aR1A1S20S45A1M0A3S1S0S1fS29R1A1S20S61S45Z4A2M1A1A3S1S0S5S26S24R1A1M2A1SaA3S1S0S5S27G2A1SbA3S0S9S4S41A1M3A1S43S28R1A1G0Z0S63S62G1S45A2A1A4S8G3S6S41S42Z30A1M4S6S41S42ZaA1M5S6S41G4S6S41G5S7S41A1A3A3A3A3A2A3A2A2A2A2A2Lo;A2").
Proof. eexists. split; [reflexivity|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma o8_4 : ltac2:(tb__ "0|6|
S2S1eS1eS1S0S9S1eA1S6bS1eS2eS72A1U8A3S8S1eR1A2A3S1S0S1fS2aR1A1S20S45A1M0A3S1S0S1fS29R1A1S20S61S45Z6A2M1A1A3S1S0S5S26S24R1A1M2A1SaA3S1S0S5S27G2A1SbA3S0S9S4S41A1M3A1S43S28R1A1G0Z0S63S62G1S45A2A1A4S8G3S6S41S42Z30A1M4S6S41S42ZaA1M5S6S41G4S6S41G5S6S41G4S6S41G5S7S41A1A3A3A3A3A3A3A2A3A2A2A2A2A2Lo;A2").
Proof. eexists. split; [reflexivity|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma side_2 : ltac2:(tb__ "0|0|
S1S0S5S84S70A1SaA3S1S0S5S80P5S70A2SbA3S1S0S5S2fS73A1SaA3S1S0S4aS21S73A1S56A3S1S0S4aS21S39S77A1A1P7dA3S0S5S23S39S7aA1A1SbA3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma side_3 : ltac2:(tb__ "0|0|
S1S0S5S84S71A1SaA3S1S0S5S80P5S71A2SbA3S1S0S5S2fS74A1SaA3S1S0S4aS21S74A1S56A3S1S0S4aS21S39S78A1A1P7dA3S0S5S23S39S7bA1A1SbA3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma side_4 : ltac2:(tb__ "0|0|
S1S0S5S84S72A1SaA3S1S0S5S80P5S72A2SbA3S1S0S5S2fS75A1SaA3S1S0S4aS21S75A1S56A3S1S0S4aS21S39S79A1A1P7dA3S0S5S23S39S7cA1A1SbA3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Local Ltac in3 k := match k with 1 => exact (or_introl eq_refl) | 2 => exact (or_intror (or_introl eq_refl)) | 3 => exact (or_intror (or_intror (or_introl eq_refl))) end.

Theorem exit_sumP (ph : bool) : ltac2:(tb__ "0|0|
S6cSfS4bS4bA2S10S4bS4bVn;Vc;A4S49Vph;A1A3S1dS4S11Q40A1A1S54S37Vok;S4cS37VJ0;S48Vph;Vn;Vc;A3R2R1A5S51S3L_;A4Ftp;Frho;F_;").
Proof.
  intros Hin rho tp. destruct ph; unfold supportedP in Hin; [change (Pre_exitP true n c) with (Pre_exit n c) | change (Pre_exitP false n c) with (Pre_exit0 n c)].
  2:{
    destruct Hin as [E|[]]; injection E as En Ec.
    destruct E0_02_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit0 n c) true = Some [mkLeafA E0_02 RsCut]) by (rewrite <- En, <- Ec; exact run0_02).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E0_02) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum (Pre_exit0 n c) E0_02 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp). }
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as En Ec.
  - destruct E_00_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA E_00 RsCut]) by (rewrite <- En, <- Ec; exact run_00).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E_00) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum (Pre_exit n c) E_00 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp).
  - destruct E_02_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA E_02 RsCut]) by (rewrite <- En, <- Ec; exact run_02).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E_02) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum (Pre_exit n c) E_02 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp).
  - destruct E_10_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA E_10 RsCut]) by (rewrite <- En, <- Ec; exact run_10).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E_10) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum (Pre_exit n c) E_10 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp).
  - destruct o8_2 as (o & Ho & Hlo & Hhi & Hw & Ha & Hcb). destruct side_2 as (Hnl & Hrl & Hswf & HnC & HnT & HlTf).
    destruct (W_shape W_2 ltac:(in3 1)) as (HnW & HXW & HbW & HlW & HfW).
    destruct (F_at F_2 ltac:(in3 1)) as (_ & HiF & H17F & H10F).
    destruct (s_vals s_2 2 ltac:(in3 1)) as (_ & S13 & _ & S15).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA W_2 RsCut]) by (rewrite <- En, <- Ec; exact run_20).
    assert (Hbl : forall r, map (beval r) [BLit 48; BLit 10] = PEND n) by (intros r; rewrite <- En; reflexivity).
    assert (Hm1 : Z.of_nat (length (PEND n)) = 2) by (rewrite <- En; reflexivity).
    exact (flush_sum 2 W_2 S5_2 C_2s o _ s_2 R_2 T_2 Tf_2 F_2 (Pre_exit n c) (eq_sym Ec) Hrun' eq_refl eq_refl HnW HXW HbW HfW splits_2 finish_2 Hnl Hrl
             Ho Hlo Hhi Hw Ha Hcb Hbl Hm1 ltac:(lia) Hswf HnC efr_2 chk_2 S13 S15 T_2_eq HnT Tf_2_eq HlTf run_F2 HiF H17F H10F rho tp).
  - destruct o8_3 as (o & Ho & Hlo & Hhi & Hw & Ha & Hcb). destruct side_3 as (Hnl & Hrl & Hswf & HnC & HnT & HlTf).
    destruct (W_shape W_3 ltac:(in3 2)) as (HnW & HXW & HbW & HlW & HfW).
    destruct (F_at F_3 ltac:(in3 2)) as (_ & HiF & H17F & H10F).
    destruct (s_vals s_3 4 ltac:(in3 2)) as (_ & S13 & _ & S15).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA W_3 RsCut]) by (rewrite <- En, <- Ec; exact run_30).
    assert (Hbl : forall r, map (beval r) [BLit 48; BLit 10; BLit 48; BLit 10] = PEND n) by (intros r; rewrite <- En; reflexivity).
    assert (Hm1 : Z.of_nat (length (PEND n)) = 4) by (rewrite <- En; reflexivity).
    exact (flush_sum 4 W_3 S5_3 C_3s o _ s_3 R_3 T_3 Tf_3 F_3 (Pre_exit n c) (eq_sym Ec) Hrun' eq_refl eq_refl HnW HXW HbW HfW splits_3 finish_3 Hnl Hrl
             Ho Hlo Hhi Hw Ha Hcb Hbl Hm1 ltac:(lia) Hswf HnC efr_3 chk_3 S13 S15 T_3_eq HnT Tf_3_eq HlTf run_F3 HiF H17F H10F rho tp).
  - destruct o8_4 as (o & Ho & Hlo & Hhi & Hw & Ha & Hcb). destruct side_4 as (Hnl & Hrl & Hswf & HnC & HnT & HlTf).
    destruct (W_shape W_4 ltac:(in3 3)) as (HnW & HXW & HbW & HlW & HfW).
    destruct (F_at F_4 ltac:(in3 3)) as (_ & HiF & H17F & H10F).
    destruct (s_vals s_4 6 ltac:(in3 3)) as (_ & S13 & _ & S15).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA W_4 RsCut]) by (rewrite <- En, <- Ec; exact run_40).
    assert (Hbl : forall r, map (beval r) [BLit 48; BLit 10; BLit 48; BLit 10; BLit 48; BLit 10] = PEND n) by (intros r; rewrite <- En; reflexivity).
    assert (Hm1 : Z.of_nat (length (PEND n)) = 6) by (rewrite <- En; reflexivity).
    exact (flush_sum 6 W_4 S5_4 C_4s o _ s_4 R_4 T_4 Tf_4 F_4 (Pre_exit n c) (eq_sym Ec) Hrun' eq_refl eq_refl HnW HXW HbW HfW splits_4 finish_4 Hnl Hrl
             Ho Hlo Hhi Hw Ha Hcb Hbl Hm1 ltac:(lia) Hswf HnC efr_4 chk_4 S13 S15 T_4_eq HnT Tf_4_eq HlTf run_F4 HiF H17F H10F rho tp).
Qed.

Theorem exit_sumP_ex (ph : bool) : ltac2:(tb__ "0|2|
S6cSfS4bS4bA2S10S4bS4bVn;Vc;A4S49Vph;A1A3S1dS4S11Q40M0A1A1S53S37S4cS37VJ0;S48Vph;Vn;Vc;A3R2R1A5S51S2S4S14A1M1G1S2S15S15S1VJ0;R5R4R2R1A4S0G1S52R3A1ScS14R2ScS14S5bS11Q8A1S14S16S58A1S46Vn;A1A4S6S14S17S12G0Vc;A2S18R1A1A2S7S14A1A3A3A3A3A2Lmd;A2Ltr;A2Lw';A3Ftp;Frho;F_;").
Proof.
  intros Hin rho tp. destruct ph; unfold supportedP in Hin; [change (Pre_exitP true n c) with (Pre_exit n c) | change (Pre_exitP false n c) with (Pre_exit0 n c)].
  2:{
    destruct Hin as [E|[]]; injection E as En Ec.
    destruct E0_02_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit0 n c) true = Some [mkLeafA E0_02 RsCut]) by (rewrite <- En, <- Ec; exact run0_02).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E0_02) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum_ex (Pre_exit0 n c) E0_02 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp). }
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as En Ec.
  - destruct E_00_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA E_00 RsCut]) by (rewrite <- En, <- Ec; exact run_00).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E_00) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum_ex (Pre_exit n c) E_00 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp).
  - destruct E_02_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA E_02 RsCut]) by (rewrite <- En, <- Ec; exact run_02).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E_02) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum_ex (Pre_exit n c) E_02 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp).
  - destruct E_10_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA E_10 RsCut]) by (rewrite <- En, <- Ec; exact run_10).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E_10) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum_ex (Pre_exit n c) E_10 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp).
  - destruct o8_2 as (o & Ho & Hlo & Hhi & Hw & Ha & Hcb). destruct side_2 as (Hnl & Hrl & Hswf & HnC & HnT & HlTf).
    destruct (W_shape W_2 ltac:(in3 1)) as (HnW & HXW & HbW & HlW & HfW).
    destruct (F_at F_2 ltac:(in3 1)) as (_ & HiF & H17F & H10F).
    destruct (s_vals s_2 2 ltac:(in3 1)) as (_ & S13 & _ & S15).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA W_2 RsCut]) by (rewrite <- En, <- Ec; exact run_20).
    assert (Hbl : forall r, map (beval r) [BLit 48; BLit 10] = PEND n) by (intros r; rewrite <- En; reflexivity).
    assert (Hm1 : Z.of_nat (length (PEND n)) = 2) by (rewrite <- En; reflexivity).
    exact (flush_sum_ex 2 W_2 S5_2 C_2s o _ s_2 R_2 T_2 Tf_2 F_2 (Pre_exit n c) (eq_sym Ec) Hrun' eq_refl eq_refl HnW HXW HbW HfW splits_2 finish_2 Hnl Hrl
             Ho Hlo Hhi Hw Ha Hcb Hbl Hm1 ltac:(lia) Hswf HnC efr_2 chk_2 S13 S15 T_2_eq HnT Tf_2_eq HlTf run_F2 HiF H17F H10F rho tp).
  - destruct o8_3 as (o & Ho & Hlo & Hhi & Hw & Ha & Hcb). destruct side_3 as (Hnl & Hrl & Hswf & HnC & HnT & HlTf).
    destruct (W_shape W_3 ltac:(in3 2)) as (HnW & HXW & HbW & HlW & HfW).
    destruct (F_at F_3 ltac:(in3 2)) as (_ & HiF & H17F & H10F).
    destruct (s_vals s_3 4 ltac:(in3 2)) as (_ & S13 & _ & S15).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA W_3 RsCut]) by (rewrite <- En, <- Ec; exact run_30).
    assert (Hbl : forall r, map (beval r) [BLit 48; BLit 10; BLit 48; BLit 10] = PEND n) by (intros r; rewrite <- En; reflexivity).
    assert (Hm1 : Z.of_nat (length (PEND n)) = 4) by (rewrite <- En; reflexivity).
    exact (flush_sum_ex 4 W_3 S5_3 C_3s o _ s_3 R_3 T_3 Tf_3 F_3 (Pre_exit n c) (eq_sym Ec) Hrun' eq_refl eq_refl HnW HXW HbW HfW splits_3 finish_3 Hnl Hrl
             Ho Hlo Hhi Hw Ha Hcb Hbl Hm1 ltac:(lia) Hswf HnC efr_3 chk_3 S13 S15 T_3_eq HnT Tf_3_eq HlTf run_F3 HiF H17F H10F rho tp).
  - destruct o8_4 as (o & Ho & Hlo & Hhi & Hw & Ha & Hcb). destruct side_4 as (Hnl & Hrl & Hswf & HnC & HnT & HlTf).
    destruct (W_shape W_4 ltac:(in3 3)) as (HnW & HXW & HbW & HlW & HfW).
    destruct (F_at F_4 ltac:(in3 3)) as (_ & HiF & H17F & H10F).
    destruct (s_vals s_4 6 ltac:(in3 3)) as (_ & S13 & _ & S15).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA W_4 RsCut]) by (rewrite <- En, <- Ec; exact run_40).
    assert (Hbl : forall r, map (beval r) [BLit 48; BLit 10; BLit 48; BLit 10; BLit 48; BLit 10] = PEND n) by (intros r; rewrite <- En; reflexivity).
    assert (Hm1 : Z.of_nat (length (PEND n)) = 6) by (rewrite <- En; reflexivity).
    exact (flush_sum_ex 6 W_4 S5_4 C_4s o _ s_4 R_4 T_4 Tf_4 F_4 (Pre_exit n c) (eq_sym Ec) Hrun' eq_refl eq_refl HnW HXW HbW HfW splits_4 finish_4 Hnl Hrl
             Ho Hlo Hhi Hw Ha Hcb Hbl Hm1 ltac:(lia) Hswf HnC efr_4 chk_4 S13 S15 T_4_eq HnT Tf_4_eq HlTf run_F4 HiF H17F H10F rho tp).
Qed.

Definition supported : list (Z * Z) := supportedP true.

End Exit.
End DrvExit.

