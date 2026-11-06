(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B' (asan-ubsan, #102 pin d663f82d7f48, unstripped twin c90d4fa54d43): the
   walk of check_reject_clean (CrcB.v check_reject_clean_holds_B) at the B' instance with its callee fuzz_alloc_live
   DISCHARGED (h-pre-b1's request through h-rw-pre-5, 19:3xZ; the image-B' twin of h-hreply-s5-rf's A' file
   lib/A/Prog/Crc102InstLive.v, origin/cold/h-hreply-s5-rf-p102-n10-crca 3506a663d1f0). Lane CrcBp of h-rw-pre-5.
   rule 24: no function proved. rule 24: proves no function (kind: merge).
   check_reject_clean_holds_B_inst_live is check_reject_clean_holds_B at
   - B := YD2l.TfibB (blob 95803a8b9493), PI := prh_img_B, PA := PI_prog_B, RL := prh_room_live_a8 at CfParams_preset;
   - ARx := ARcf /\ xs_placed_cf at CfParams_preset over PI_prog_B's segments: THE relation of c-omx-alloc's instance
     corollary fuzz_alloc_live_holds_B_inst (origin/cold/c-omx-alloc-acc102 78c92e0f7d3a,
     lib/B/Prog/FuzzAllocAccInstB102.v 3b59f132b2db, on int102 since 8862cc5bd2f), word for word (its ARcfx);
   with:
   - LAWS by YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (the A' file's discharge, here at B's segments);
   - FLIVE by FuzzAllocAccInstB102.fuzz_alloc_live_holds_B_inst (the tfuzz_alloc_live_specX, f97c8b2f046b :110, no
     image premise);
   - EMPTY_RO / EMPTY_ZS by CrcBRomRefute.v cr_empty_ro_B / cr_empty_zs_B (vm_compute at TfibB);
   - IMGV at ARcf /\ xs_placed_cf from the same fact at ARcf ALONE (the relation implies ARcf), so the premise left is
     stated at h-mani-a8's own relation.
   The two premises left: BCMP, the bcmp row with the memnorm keep (YGcallMxmn.v:265 abcmp_realizes_xm) at the
   listing's __wrap_bcmp and this relation (owner c-libc-stdio, its bcmp row; the A' file leaves the same one), and
   cr_img_shadow_vis_B at ARcf (CrcB.v; image B's CfImg_B bounds; owner h-mani-a8: tfib_img_shadow_vis_cf_B,
   lib/AU/AImgShadowVisCfB.v on cold/h-mani-a8-alloc102, pending). No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YCbqG YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YGcallcf YG0lawscf YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import CrcB CrcBRomRefute.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzAllocAccInstB102.
Import ListNotations.
Open Scope Z_scope.

Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ xs_placed_cf ly S).
Theorem check_reject_clean_holds_B_inst_live : forall SK : YI16.sink_head,
  YGcallMxmn.abcmp_realizes_xm SEGS TB ARcfx (@pa_sigma _ B_prog_listing PI_prog_B AS___wrap_bcmp) ->
  cr_img_shadow_vis_B (fun ly S Hp W mem md => ARcf (cp := CP) SEGS TB ly S Hp W mem md) ->
  tcheck_reject_clean_specX (cp := CP) (PI := prh_img_B) (RL := prh_room_live_a8 (cp := CP)) (PA := PI_prog_B)
    TB ARcfx SK.
Proof.
intros SK BCMP IV.
eapply (check_reject_clean_holds_B (RL := prh_room_live_a8 (cp := CP)) TB ARcfx SK).
- exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)).
- exact (FuzzAllocAccInstB102.fuzz_alloc_live_holds_B_inst (SK := SK)).
- exact BCMP.
- exact cr_empty_ro_B.
- intros ly S Hp W mem md a [HAR _] Ha. exact (IV ly S Hp W mem md a HAR Ha).
- exact cr_empty_zs_B.
Qed.
End L.

(* ---- the Qed report: the elaborated statement, every implicit shown, and the assumptions ---- *)
Set Printing Implicit.
Unset Printing Notations.
Print check_reject_clean_holds_B_inst_live.
Unset Printing Implicit.
Set Printing Notations.
Print Assumptions check_reject_clean_holds_B_inst_live.
