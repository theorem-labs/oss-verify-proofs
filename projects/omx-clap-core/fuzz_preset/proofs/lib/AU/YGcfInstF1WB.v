(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31: the ALLOCATE part of lib/AU/YGcfInstF1WB.v at a working branch 7a128776b225
   (round 6g; build of record the internal file zf-fuzz-preset-7a128776b2.build-20261030T181859Z.log), relocated onto round
   misstop-3c ae35a5e5462 with the same names and proof texts: the depot field that preset's B' Allocate top
   (lib/AU/AllocGtopPresetMB.v, section c, hypothesis HDEP) takes, with every image hypothesis discharged at preset's
   image B' (asan-ubsan, #102 pin d663f82d).  The twin at B' of lib/A/YGcfInstF1WA.v's if_depot_cf_at_A:
   - [IMG_COVER_B]: YGcfDIface.IMG_COVER at B' (the image window from the ledger, over B''s segment table);
   - [dep_fp_a_B] / [dep_keep_a_B]: YGcfInstDepot's image premises for Allocate's call, from AU/AGix.v
     (footprint_DZONE, const_kept, depot_mem_ok_agree, depot_ids_bound, DZONE_range, aview_agree);
   - [depot_spec_a_B]: the released depot contract at B' (AU/AFemBx.depot_spec_x_B);
   - [if_depot_cf_at_B]: YGcfInstDepot.if_depot_cf at B', for any walk relation that gives ARcf at B''s segments;
   - [HDEP_B]: the same at the layer's walk relation ARXq_cf B IOK Hp and universe U_cf B, the exact text of
     AllocGtopPresetMB's HDEP; [HDEP_TfibB]: closed at B''s symbol record YD2l.TfibB (as_dhash TfibB := tfib_dhash).
   The source file's Deallocate and errno parts (dep_fp_d_B, dep_keep_d_B, depot_spec_d_B, di_depot_cf_at_B,
   errno_img_cf_B, errno_seg_B, errno_nstatic_B, de_depot_cf_at_B) are not relocated here: they are not on the
   Allocate path, and errno_img_cf_B needs AU/ErrnoApartB.v, which this round does not carry.
   The instances are B''s AU/AGif2cgif.AImg_cgif and AU/AGif0cgif.AGImg_cgif.
   rule 24: no function proved (kind: instance discharge at preset's image B' from preset's proved lemmas; the depot
   function's contract is AU/AFemBx's). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGis AGif0cgif AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGix AFemBx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot YGcfDIface YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstDepot.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The image window from the ledger (YGcfDIface.IMG_COVER at B').                                                *)
Section img.
Theorem IMG_COVER_B : YGcfDIface.IMG_COVER.
Proof.
intros ly S md L. change (img_cover ly). split.
- destruct (alc_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _].
  cbn in H. unfold TFIB_IMG_LO. lia.
- destruct (alc_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
  cbn in H. unfold TFIB_IMG_END. lia.
Qed.
End img.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. What StackDepotPut may write lies in the depot zone (YGcfInstDepot.dep_fp_img at B').                         *)
Section fp.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Theorem dep_fp_a_B : dep_fp_img B ag_dzone.
Proof.
intros ly a LY IMG TSD FP.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd B TS)).
exact (AGix.footprint_DZONE B ly TS LY IMG HTSD a FP).
Qed.
End fp.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The constant cells and the depot's memory facts carried to a memory that keeps the zone
   (YGcfInstDepot.dep_keep_img at B'; AU/CLdepotcgif.sub_a's ds_keep script).                                      *)
Section keep.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Theorem dep_keep_a_B : dep_keep_img B (fun ly a => ag_dzone ly a \/ ag_czone ly a).
Proof.
intros ly S W mem0 mem LY IMG TSD DF CST DEP MEQ.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd B TS)).
split.
- apply (AGix.const_kept B ly TS LY IMG HTSD W mem0 mem CST). intros x Hx. apply MEQ. right. exact Hx.
- apply (AGix.depot_mem_ok_agree B ly TS LY IMG HTSD S (aview tfibsegs (w_H W) mem0)).
  + pose proof (AGix.depot_ids_bound B ly TS LY IMG HTSD S DF). lia.
  + intros a Ha. pose proof (AGix.DZONE_range B ly TS LY IMG HTSD a Ha) as Ra.
    apply (AGix.aview_agree W mem0 mem a Ra). apply MEQ. rewrite unsigned_lit_small by exact Ra. left. exact Ha.
  + exact DEP.
Qed.
End keep.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The released depot contract at B' (AU/AFemBx.depot_spec_x_B), at Allocate's entry pc.                        *)
Section spec.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Theorem depot_spec_a_B : (forall t, as_dhash B t = tfib_dhash t) ->
CLdepot.depot_spec_x im_segs ag_depot_put im_tp im_img_cover B.
Proof. intros HDH. exact (AFemBx.depot_spec_x_B B TS HDH). Qed.
End spec.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. YGcfInstDepot's Allocate depot field at image B', every image hypothesis discharged, for any walk relation
   over ARcf.                                                                                                       *)
Section h.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Variable Hp : list Z.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Hypothesis HAR : forall inst ly S W mem md, ARX inst ly S W mem md -> ARcf im_segs B ly S Hp W mem md.
Hypothesis HDH : forall t, as_dhash B t = tfib_dhash t.

Theorem if_depot_cf_at_B :
CLdepot.depot_field im_segs ag_depot_put im_tp B ARX (YGcfInstBase.cf_tr_ok B) ag_dzone
  (fun ly a => ag_dzone ly a \/ ag_czone ly a).
Proof. exact (if_depot_cf B Hp ARX HAR IMG_COVER_B (dep_keep_a_B B TS) (dep_fp_a_B B TS) (depot_spec_a_B B TS HDH)). Qed.
End h.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. The field at the layer's walk relation YGcfInstBase.ARXq_cf B IOK Hp and universe U_cf B (U_cf B is cf_tr_ok B
   by definition, YGcfInstBase.v:597): the text of lib/AU/AllocGtopPresetMB.v's hypothesis HDEP.  ARXq_cf's first
   conjunct is ARX_cf (YGcfInstBase.v:480-482), whose second conjunct is ARcf (YGcfInstBase.v:67-69).  Then closed at
   B''s symbol record YD2l.TfibB.                                                                                  *)
Section rec.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Variable IOK : Z -> Prop.
Hypothesis HDH : forall t, as_dhash B t = tfib_dhash t.
Theorem HDEP_B : forall Hp, CLdepot.depot_field im_segs ag_depot_put im_tp B (YGcfInstBase.ARXq_cf B IOK Hp)
  (YGcfInstBase.U_cf B) ag_dzone (fun ly a => ag_dzone ly a \/ ag_czone ly a).
Proof.
intros Hp.
exact (if_depot_cf_at_B B TS Hp (YGcfInstBase.ARXq_cf B IOK Hp) (fun inst ly S W mem md H => proj1 (proj2 (proj1 H))) HDH).
Qed.
End rec.

Theorem HDEP_TfibB : forall (IOK : Z -> Prop) Hp,
CLdepot.depot_field im_segs ag_depot_put im_tp YD2l.TfibB (YGcfInstBase.ARXq_cf YD2l.TfibB IOK Hp)
  (YGcfInstBase.U_cf YD2l.TfibB) ag_dzone (fun ly a => ag_dzone ly a \/ ag_czone ly a).
Proof. intros IOK Hp. exact (HDEP_B YD2l.TfibB YD2l.TfibB_syms IOK (fun t => eq_refl) Hp). Qed.
End a.
