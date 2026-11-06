(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetD1rAlPf.v, with its module paths changed; 22 of its 65 lines of code are new or changed and 9 lines of the source are left out. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset (asan image A), the PROOFS of the three link statements of
   lib/A/PresetD1rAl.v at the program interface's frame names (lib/A/PresetCfnA.v section 5): ablocks_cf,
   afn_pre_cf and ajournal_cf are ABBREVIATIONS of a Theorem Labs lane's lib/Reusable/YCbqG.v forms (the journal of record,
   blob 83da015952be of the engine fold) at ARx := ARcf tfibsegs B, CfParams_preset and PST := the kit's prh_pst, so each
   link holds by unfolding:
     ablocks_link_A_holds   ablocks_cf is cgif's ablocks (definitional);
     afn_pre_link_A_holds   the nine conjuncts of YCbqG.afn_pre_x, in its order;
     ajournal_link_A_holds  seven of the seventeen conjuncts of YCbqG.ajournal_x at FP = [] and own = []: the image
                            clause's `~ Exists (in_zr a) prh_pst` is read through PresetCfnA.v's ledger_img (the same
                            five cells, at the widths image A's descriptors give: 8, 8, 8, 8 and g_ran_out's 1), and
                            its `fp_spares [] a` holds since the empty footprint opens no sink (YCbq.sink_closed_nil).
   The loop statement (lib/A/PresetD1rA.v loop_L_x_A) takes none of the links as a premise: its proof cites these.
   This file needs no driver file of the A core. B twin: lib/AU/PresetD1rBlPf.v (lane CwLoopB writes both).
   Nothing in this file is a proof of a function (rule 24: composition / driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1rAl.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Module PCA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The seven ledger cells of the journal's PST are PresetCfnA.v's ledger_img (both name the generated PrhImg of image A',
   whose fields are computed here). #102: the kit's prh_pst (PRH_Base.v:448-451, f97c8b2f046b) gains g_most and
   g_own_ran_out, and the interface's ledger_img gains the same two cells. *)
Lemma prh_pst_ledger_img_A : forall a, Exists (in_zr a) (@PRH_Base.prh_pst PCA.preset_prh_img) -> PCA.ledger_img a.
Proof.
intros a Hx. apply Exists_exists in Hx as ([lo n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
unfold PRH_Base.prh_pst in Hin.
unfold PCA.ledger_img, PCA.G_RAN_OUT, PCA.G_LIVE, PCA.G_PEAK, PCA.G_COUNT, PCA.G_FAIL_AT, PCA.G_MOST, PCA.G_OWN_RAN_OUT.
cbv [PCA.preset_prh_img PRH_Img.prh_img_A PRH_Base.pi_g_live PRH_Base.pi_g_peak PRH_Base.pi_g_count PRH_Base.pi_g_fail
  PRH_Base.pi_g_ran_out PRH_Base.pi_g_most PRH_Base.pi_g_own_ran_out PRH_Base.pi_gz_live PRH_Base.pi_gz_peak
  PRH_Base.pi_gz_count PRH_Base.pi_gz_fail PRH_Base.pi_gz_ran_out PRH_Base.pi_gz_most PRH_Base.pi_gz_own_ran_out] in Hin |- *.
try change (Z.of_nat 8) with 8 in Hin. try change (Z.of_nat 1) with 1 in Hin.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; injection E as <- <-; lia.
Qed.

Section s.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Variable B : asyms.

Lemma ablocks_link_A_holds : ablocks_link_A B PCA.ablocks_cf.
Proof. intros ly S. reflexivity. Qed.

Lemma afn_pre_link_A_holds : afn_pre_link_A B PCA.afn_pre_cf.
Proof.
intros STK ly S Hp W regs mem md ch HAR Hret Hra Hgp Htp Hstk Hpres Hch HQ.
unfold PCA.afn_pre_cf, YCbqG.afn_pre_x.
exact (conj HAR (conj Hret (conj Hra (conj Hgp (conj Htp (conj Hstk (conj Hpres (conj Hch HQ)))))))).
Qed.

Lemma ajournal_link_A_holds : ajournal_link_A B PCA.ajournal_cf.
Proof.
intros STK sp0 ly S Hp W mem md ly' S' Hp' W' mem' md' k HJ.
unfold PCA.ajournal_cf, YCbqG.ajournal_x in HJ.
destruct HJ as (HAR & Hle & _ & _ & _ & Hfr & _ & _ & Hout & _ & Himg & _ & _ & Hpres & _ & _ & HQ).
split; [exact HAR|]. split; [exact Hle|]. split; [rewrite Hfr; reflexivity|].
split; [exact Hout|]. split; [|split; [exact Hpres | exact (proj1 HQ)]].
intros a Hi Hns He Hl. apply Himg; [exact Hi | exact Hns | exact He | |].
- intros Hx. exact (Hl (prh_pst_ledger_img_A a Hx)).
- apply YCbq.fp_spares_closed. exact YCbq.sink_closed_nil.
Qed.
(* the same at any wild budget WS (clause 4b of the kit's batch): the slot post's journal is ajournal_cfw at the post's WS; the
   link reads none of the wild conjunct *)
Lemma ajournal_link_A_holds_w : forall WS : list (list Z), ajournal_link_A B
  (fun sg B0 STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k =>
     PCA.ajournal_cfw sg B0 STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS).
Proof.
intros WS STK sp0 ly S Hp W mem md ly' S' Hp' W' mem' md' k HJ.
cbv beta in HJ. unfold PCA.ajournal_cfw in HJ.
destruct HJ as (HAR & Hle & _ & _ & _ & Hfr & _ & _ & Hout & _ & Himg & _ & _ & Hpres & _ & _ & HQ).
split; [exact HAR|]. split; [exact Hle|]. split; [rewrite Hfr; reflexivity|].
split; [exact Hout|]. split; [|split; [exact Hpres | exact (proj1 HQ)]].
intros a Hi Hns He Hl. apply Himg; [exact Hi | exact Hns | exact He | |].
- intros Hx. exact (Hl (prh_pst_ledger_img_A a Hx)).
- apply YCbq.fp_spares_closed. exact YCbq.sink_closed_nil.
Qed.
End s.
