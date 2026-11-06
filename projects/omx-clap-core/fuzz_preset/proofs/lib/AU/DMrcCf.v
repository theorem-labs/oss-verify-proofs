(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMrcCf.v (commit ce1a656b52b7, file sha256 34cb71a3c1a9) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 1 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcCf.v (commit 3d8ad2aeb77e, H4 cf instance set (reply-rccf); file sha256 ed1a443b63e0) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMrcCf.v at commit 2c35faeeaec, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4; F1 row R3, re-hide twin): H4's read record under the re-hide
   DMrcRhOk.rc_reads_rh and the RChunk walk top at the re-hide twin DMrcRhOk.rchunk_ok_rh_t at cgif's image and the cf
   cut relation YGcfInstDrainR.ARXr_cf, with the loosened post relation DMrcSecCf.ARXsl_cf, AOX := aowned B and
   DRq := YGcfInstDrainR.DRq_cf B, assembled from the cf layer's transports.
   rule 24: proves function __asan::QuarantineCallback::Recycle (0x348fc; RChunk secondary cut / map reads) at cgif's cf relation,
   re-hide twin, instance of H4's own transports; released-proof lookup `proof-index '__asan::Allocator::Recycle'
   'QuarantineCallback::Recycle'` (index v5 built 2026-10-30T04:38:19Z): 0 released; rule-24 check R24CheckRcCf
   CONFIRM.

   WHAT.  [rc_reads_cf]: for every B with TfibSyms B and every IOK, Hp with YGcfInstBase.IOK_ok B IOK, the row
   ERRB_QAPART and the unit's recycle charge bound DMrcSecCf.REC_LE give DMrcRhOk.rc_reads_rh at the cf instance,
   ARXsl_cf and RMAXD_cf (rc_reads_rh takes no NMAXD / LMAXD: its body names neither, so DMrcRhOk's Section does not
   abstract them).  [rchunk_ok_rh_cf] is DMrcRhOk.rchunk_ok_rh applied to it: DMrcRhOk.rchunk_ok_rh_t at NMAXD_cf /
   LMAXD_cf / RMAXD_cf (its own premises nmaxd_ok / lmaxd_ok / rmaxd_ok / drq_sizes stay its premises).
   [rchunk_ok_rh_cf_closed] discharges those four: rmaxd_ok / nmaxd_ok / lmaxd_ok by computation over the cf layer's
   constants, and drq_sizes by [DS_cf] (the cf layer's drq_sizes_cf).
   The two secondary READ fields are [SC_cf] / [SM_cf], i.e. DMrcSecCutCf.rc_sec_cut_of_cf (rc_sec_cut_t) and
   DMrcSecMaprCf.rc_sec_mapr_of_cf (rc_sec_mapr_t).

   HOW.  The fields of rc_reads_rh, one by one:
   - rc_head_t, rc_model_t, rc_split_t: YGcfInstRcPrim.rc_head_cf / rc_model_cf / rc_split_cf;
   - rc_prim_fh_t: DMrcFhCf.rc_prim_fh_of_cut over YGcfInstRcPrim.rc_fh_cut_facts_cf, whose image premise
     YGcfDIface.IMG_COVER holds at cgif's image ([img_cover_cgif]: the cf ledger's alc_img places segments 000 and
     003 of tfibsegs in the image window, through the layer's YGcfDIface.img_cover_of_ledger_cf; the proof of
     YF0x.img_cover_of_ledger with ALedger_cf for ALedger);
   - rc_prim_step_t: YGcfInstRcPrim.rc_prim_step_cf at RMAXD := RMAXD_cf = kFreeArrayOffset (its HRMAX by unfolding
     RMAXD_cf); its cd_model_cf is DMwalkIF.cd_model by definition (the two bodies are the same text over the same
     constants: [cd_model_of_cf] is an implication proved by conversion, `exact H`);
   - rc_prim_room_t: YGcfInstRcPrim.rc_prim_room_cf;
   - rc_prim_mach_rh_t ([rc_prim_mach_rh_cf]): DMrcPrim.rchunk_prim_m at the cf instance (its TfibSyms B, rc_prim_reads
     and cdealloc_g_t are the field's own premises), lifted to amreal' at RZ_cf by YG0dH.amreal_amreal', its call post
     weakened to acall_post_x_rh by YGcfRehidePost.acall_post_x_rh_of (the primary arm re-hides nothing);
   - rc_sec_step_g over ARXsl_cf: DMrcSecCf.rc_sec_step_sl_of_cf;
   - rc_sec_pre_rh_t ([rc_sec_pre_rh_cf]): at the call the cut relation's ARcfR gives the hull of the map in the
     allowance (abudget_ok_cf's asecA at the live extent YGcfInstRcSec.KFACTS names), the slot real and the map at
     least kMaxSize + kPage (the chunk's chunk_ok_cf: YGcfRehideAR.SREAL_of_pre / M2_of_pre), and the map apart from
     every secondary extent of the post state (YGcfInstRcSec.APART2 at rsX2 = YFg8.X2v, DMrcSecCf.X2_eq);
   - rc_sec_rehide_all_t ([rc_sec_rehide_all_cf]): YGcfRehideAR.ARcfR_rehide, its premises in DMrcRh.rc_sec_rehide_t's
     order; ARXsl_cf gives its ARcfR_sl premise, and IOK and xs_mapped_cf (which reads neither the world nor the
     memory) carry over to ARXr_cf at the re-hidden world. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstBase YGcfDIface YGcfInstDrainR. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YGcfInstRcPrim.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMwalkIF DMrcReads DMrcSecReads DMrcFhCf DMrcSecCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMrcSecCutCf DMrcSecMaprCf DMrcPrim DMrcRh DMrcRhOk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFg8.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG03cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YGcfInstRcSec. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRehideAR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

(* The secondary bounds and the class bound of the cf instance. *)
Local Notation NMAXD_cf := YGcfInstDrainR.NMAXD_cf.
Local Notation LMAXD_cf := YGcfInstDrainR.LMAXD_cf.
Local Notation RMAXD_cf := YGcfInstDrainR.RMAXD_cf.

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfImgRows.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : YGcfNames.CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The two secondary READ fields, from the theorems that prove them (DMrcSecCutCf.v, DMrcSecMaprCf.v).           *)
Lemma SC_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp, YGcfInstBase.IOK_ok B IOK ->
  DMrcSecReads.rc_sec_cut_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp).
Proof. exact DMrcSecCutCf.rc_sec_cut_of_cf. Qed.
Lemma SM_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  DMrcSecReads.rc_sec_mapr_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp).
Proof. exact DMrcSecMaprCf.rc_sec_mapr_of_cf. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The image premise of rc_fh_cut_facts_cf at cgif's image: the cf ledger places the first and the last loaded      *)
(* segment in the image window, which so covers [TFIB_IMG_LO, TFIB_IMG_END).                                       *)
Lemma img_cover_preset : YGcfDIface.IMG_COVER (IM := AImg_cgif).
Proof.
intros ly S md L. change (img_cover ly). unfold img_cover.
apply (YGcfDIface.img_cover_of_ledger_cf im_segs TFIB_IMG_LO TFIB_IMG_END ly S md); [| |exact L].
- exists AsanUbsan.AsanUbsan_segment_000. split; [left; reflexivity | cbn; unfold TFIB_IMG_LO; lia].
- exists AsanUbsan.AsanUbsan_segment_003. split; [do 3 right; left; reflexivity | cbn; unfold TFIB_IMG_END; lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The model premise: the cf layer's cd_model_cf is DMwalkIF.cd_model's text, so the two are equal by definition.   *)
Lemma cd_model_of_cf : forall R S c off, YGcfInstRcPrim.cd_model_cf R S c off -> DMwalkIF.cd_model R S c off.
Proof. intros R S c off H. exact H. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The primary step field at RMAXD_cf.                                                                              *)
Lemma rc_prim_step_preset : forall (B : asyms) IOK Hp,
  DMrcReads.rc_prim_step_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp) (aowned B) (YGcfInstDrainR.DRq_cf B kQuarantineMax)
    RMAXD_cf.
Proof.
intros B IOK Hp inst ly X k ks zs cbp W regs mem md off mem' md' PRE DR Hb AG VIS NEW HK CONST Ev El Ee.
assert (HR : kFreeArrayOffset <= RMAXD_cf) by (unfold RMAXD_cf; lia).
destruct (YGcfInstRcPrim.rc_prim_step_cf B IOK Hp kQuarantineMax RMAXD_cf HR inst ly X k ks zs cbp W regs mem md off mem' md'
  PRE DR Hb AG VIS NEW HK CONST Ev El Ee) as (A1 & A2 & A3 & A4 & A5).
split; [exact A1|]. split; [exact (cd_model_of_cf _ _ _ _ A2)|].
split; [exact A3|]. split; [exact A4 | exact A5].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The primary arm at the re-hide twin: DMrcPrim.rchunk_prim_m at the cf instance, lifted to amreal' at RZ_cf        *)
(* (YG0dH.amreal_amreal'), its call post weakened to acall_post_x_rh (YGcfRehidePost.acall_post_x_rh_of).           *)
Lemma rc_prim_mach_rh_cf : forall (B : asyms) IOK Hp,
  DMrcRhOk.rc_prim_mach_rh_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp) (aowned B)
    (YGcfInstDrainR.DRq_cf B kQuarantineMax) RMAXD_cf.
Proof.
intros B IOK Hp TB RP CDG inst ly X k ks zs cbp W regs mem md off PRE RX Hb.
eapply YG0dH.amreal'_mono; [| exact (YG0dH.amreal_amreal' tfibsegs YGcfRehidePost.RZ_cf _ _ _ _
  (DMrcPrim.rchunk_prim_m B TB _ (aowned B) _ RMAXD_cf RP CDG inst ly X k ks zs cbp W regs mem md off PRE RX Hb))].
intros r0 W' c' (regs' & mem' & md' & Hc & HP & HT).
exists regs', mem', md'. split; [exact Hc|].
split; [exact (YGcfRehidePost.acall_post_x_rh_of B _ (aowned B) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) | exact HT].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The re-hide's pre-state premises at the call (DMrcRh's HULL / SREAL / M1 / M2), from the cut relation.             *)
Lemma rc_sec_pre_rh_cf : forall (B : asyms) IOK Hp,
  DMrcRhOk.rc_sec_pre_rh_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp).
Proof.
intros B IOK Hp inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hk Hst.
pose proof (proj1 (proj2 (proj1 PRE))) as MR.
pose proof (@YGcfInstRcSec.KFACTS rc ci cp AImg_cgif B ly X Hp k r o sm W mem md MR Hk Hb Hsm) as (_ & EL & _ & _ & GI & _).
pose proof (proj1 (Forall_forall _ _) (YG03cf.wfr_chunks _ _ _ _ _ (YGcfInstDrainR.amr_wfr _ _ _ _ _ (proj1 MR))) k Hk) as CK.
assert (EL' : YFg8.LEN sm = YGcfInstRcSec.LEN k) by exact EL.
split.
{ (* the hull of the live map is in the allowance: abudget_ok_cf's asecA at the live extent *)
  pose proof MR as (_ & _ & (_ & SA & _) & _). rewrite EL'. exact (proj2 (SA _ GI)). }
split; [exact (YGcfRehideAR.SREAL_of_pre X k r o sm CK Hb Hsm)|].
split; [|exact (YGcfRehideAR.M2_of_pre X k r o sm CK Hb Hsm)].
(* every secondary extent of the post state is apart from the dead map *)
apply Forall_forall. intros e He. rewrite <- DMrcSecCf.X2_eq in He.
apply YGcfRehideAR.zdisjoint_sym_rh. rewrite EL'.
exact (YGcfInstRcSec.APART2 (IM := AImg_cgif) B ly X Hp k r o sm i W mem md MR Hk Hb Hsm e He).
Qed.

(* The re-hide keeps the cut relation, at every call: YGcfRehideAR.ARcfR_rehide from ARXsl_cf's ARcfR_sl; IOK and
   xs_mapped_cf read neither the world nor the memory. This unit's world carries w_H8 (YA0n.v), so the re-hidden world
   takes a proof of it: HW8 in DMrcRh.rc_sec_rehide_t, YGcfRehideAR.rh_H8 in ARcfR_rehide. ARcfR reads the world only
   through w_H and w_A, so the two goals are convertible. *)
Lemma rc_sec_rehide_all_cf : forall (B : asyms) IOK Hp,
  DMrcRhOk.rc_sec_rehide_all_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp) (DMrcSecCf.ARXsl_cf B IOK Hp).
Proof.
intros B IOK Hp inst ly X k r sm i W2' mem' md' sm2 HO HA HW8 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 (HI & HSL & HX) H12.
split; [exact HI|]. split; [|exact HX].
exact (YGcfRehideAR.ARcfR_rehide tfibsegs B ly _ Hp W2' mem' md' (YFg8.MAP ly r) (YFg8.LEN sm) r sm2 HO HA
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 HSL H12).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* H4's read record under the re-hide at cgif's cf relation.                                                        *)
Theorem rc_reads_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  YGcfInstBase.IOK_ok B IOK -> YGcfImgRows.ERRB_QAPART -> DMrcSecCf.REC_LE ->
  DMrcRhOk.rc_reads_rh B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp) (DMrcSecCf.ARXsl_cf B IOK Hp) (aowned B)
    (YGcfInstDrainR.DRq_cf B kQuarantineMax) RMAXD_cf.
Proof.
intros B TB IOK Hp HIOK EAP RLE.
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- split; [|split; [|split; [|split]]].
  + exact (YGcfInstRcPrim.rc_head_cf B kQuarantineMax).
  + exact (YGcfInstRcPrim.rc_model_cf B kQuarantineMax).
  + exact (DMrcFhCf.rc_prim_fh_of_cut B TB _ _ (YGcfInstRcPrim.rc_fh_cut_facts_cf B IOK Hp kQuarantineMax HIOK img_cover_preset)).
  + exact (rc_prim_step_preset B IOK Hp).
  + intros inst ly X k ks zs cbp W regs mem md off PRE RX Hb G.
    exact (YGcfInstRcPrim.rc_prim_room_cf B IOK Hp kQuarantineMax inst ly X k ks zs cbp W regs mem md off PRE RX Hb G).
- exact (rc_prim_mach_rh_cf B IOK Hp).
- exact (SC_cf B TB IOK Hp HIOK).
- exact (SM_cf B TB IOK Hp).
- exact (DMrcSecCf.rc_sec_step_sl_of_cf B TB IOK Hp EAP RLE).
- exact (YGcfInstRcPrim.rc_split_cf B kQuarantineMax).
- exact (rc_sec_pre_rh_cf B IOK Hp).
- exact (rc_sec_rehide_all_cf B IOK Hp).
Qed.

(* The RChunk walk top at the re-hide twin at cgif's cf relation: DMrcRhOk.rchunk_ok_rh on the record. *)
Theorem rchunk_ok_rh_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  YGcfInstBase.IOK_ok B IOK -> YGcfImgRows.ERRB_QAPART -> DMrcSecCf.REC_LE ->
  DMwalkIFRh.rchunk_ok_rh_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp) (aowned B)
    (YGcfInstDrainR.DRq_cf B kQuarantineMax) NMAXD_cf LMAXD_cf RMAXD_cf.
Proof.
intros B TB IOK Hp HIOK EAP RLE.
exact (DMrcRhOk.rchunk_ok_rh B _ (DMrcSecCf.ARXsl_cf B IOK Hp) _ _ NMAXD_cf LMAXD_cf RMAXD_cf
  (rc_reads_cf B TB IOK Hp HIOK EAP RLE)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The size premises of rchunk_ok_rh_t at the cf instance: rmaxd_ok / nmaxd_ok / lmaxd_ok by computation over the cf *)
(* layer's constants (review RevRcCf F1), and drq_sizes of DRq_cf from YGcfInstDrainR.drq_sizes_cf.                 *)
Lemma DS_cf : forall (B : asyms), DMwalkIF.drq_sizes (YGcfInstDrainR.DRq_cf B kQuarantineMax) NMAXD_cf LMAXD_cf.
Proof. intros B. exact (YGcfInstDrainR.drq_sizes_cf B kQuarantineMax ltac:(unfold kMaxSize, kQuarantineMax; lia)). Qed.

(* rchunk_ok_rh_cf with its size premises discharged: the walk top at the re-hide twin under the frame, the view and
   H3's contract. *)
Theorem rchunk_ok_rh_cf_closed : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  YGcfInstBase.IOK_ok B IOK -> YGcfImgRows.ERRB_QAPART -> DMrcSecCf.REC_LE ->
  DMiface.di_frame_t (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp) (aowned B) ->
  DMwalkIF.di_rview_x_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp) (YGcfInstDrainR.DRq_cf B kQuarantineMax) RMAXD_cf ->
  DMwalkIF.cdealloc_g_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp) (aowned B) RMAXD_cf ->
  DMwalkIFRh.rchunk_m_rh_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp) (aowned B) (YGcfInstDrainR.DRq_cf B kQuarantineMax).
Proof.
intros B TB IOK Hp HIOK EAP RLE DF DV CDG.
exact (rchunk_ok_rh_cf B TB IOK Hp HIOK EAP RLE TB YGcfInstDrainR.nmaxd_ok_cf YGcfInstDrainR.lmaxd_ok_cf
  YGcfInstDrainR.rmaxd_ok_cf (DS_cf B) DF DV CDG).
Qed.
End d.
Print Assumptions rchunk_ok_rh_cf_closed.
