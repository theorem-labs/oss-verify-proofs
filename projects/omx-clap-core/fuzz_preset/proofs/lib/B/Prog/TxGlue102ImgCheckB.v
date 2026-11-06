(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the CALLER-WINDOW call kit over YCbqG.v's journal
   ajournal_x (allocator invariant a parameter ARx, ghost head set Hp after S, program statics PST), generic: no image
   class, no address, no ledger. Credit: WalkS4, lib/A/Prog/PRW_CallerJ.v at 85a188622c5 (statements and proofs taken
   from there; changes below). Donors there: cj_kept from cgif_file_fuzzer lib/YC20.v:311-325 tlzw_kept and
   lib/YC8n.v:272-287 tlzw_kept_of_journal (origin/release/pau-projects-recipes), generalised to ajournal_x's keep
   clauses; aj_call_xW from YCbqGcall.v aj_call_x (cgif YCbq.v:1845-1883 aj_call, origin/ossv/recipes).
   What a walk of a function in the caller-window form needs:
   - fwin_x / fpostW_x / fpostWF_x: lib/A/PRH_Base.v's fwin / fpostW / fpostWF (K0) restated with the image segs and
     the statics PST as parameters, same bodies: PRH_Base.fpostW B ARx SK STK d FP .. is
     fpostW_x (SK := SK) pa_segs B prh_pst ARx STK d FP .. by unfolding (this file does not Require lib/A).
   - START: ajournal_x_init_W, the widened journal (STK + e) (sp + e) at the entry state.
   - CALL of a caller-window callee: aj_call_xW / aj_call_xWF (callee state in mkst form), aj_call_xW_sp /
     aj_call_xWF_sp (the entry form of YCbqGcall.v's aj_call_x_sp: st_ok, ss_resv, the machine state ms).
     The footprint side condition is YCbqG.v's own fp_sub_x (h-hpreset-7 9052c7a7d74 :688-691), whose fourth
     disjunct `sp0 - STK <= a < sp0` is the caller's window: WalkS4's fp_sub_xW is that predicate, so this file
     no longer states one and ajournal_x_sub_W (the name WalkS4's callers use) is YCbqG's ajournal_x_sub.
   - vrd_call_W: h-verbs-3's lib/A/VrdArm.v call rule (6d4cddbdff5), premise shape kept, as a corollary of
     aj_call_xW_sp at e1 := - o.
   - aj_call_xWF_d: WalkH6's caller-window float call rule (h-walk-identity's S8aCallW.v aj_call_xWF), verbatim: no
     fwin_x for the callee and no window-kept clause on either side.
   - END: cj_kept (the keep clauses of ajournal_x relative to the entry, the walker's window and its written cells OR
     exempted) across stretches (cj_kept_exec) and calls (cj_kept_of_journal), chained (cj_kept_trans), closed by
     fpostW_x_of_kept / fpostWF_x_of_kept; fpostW_x_of_apost: apost_base_x is fpostW_x at e = 0.
   Numerals: 16, 4096, 8, 4 and 2 ^ 64 are LENGTH; 0 is LENGTH (the empty window e = 0) or DERIVED (event count);
   register numbers 1, 3, 4 (ra, gp, tp) are WORD. No address literal; no image constant. *)
(* Modified by Theorem Labs, 2026-10: the kit over a world relation R (suffix R). A free or realloc of a live block can
   hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle with its journal at that
   relation (YCbqG.v ajournal_xR). cj_keptR is cj_kept with the world conjunct R W W2 (a copy of the body; the guard
   cj_kept_R_wle shows by reflexivity that cj_kept is cj_keptR at wle). The R forms of cj_kept_refl / cj_kept_exec /
   ajournal_x_init_W take R and its reflexivity, of cj_kept_trans / ajournal_x_sub_W R and its transitivity, of
   cj_kept_of_journal / fpostW_x_of_apost / fpostW_x_of_kept / fpostWF_x_of_kept R alone; the call rules
   aj_call_xWR / aj_call_xW_spR / aj_call_xWFR / aj_call_xWF_spR / vrd_call_WR / aj_call_xWF_dR take R and both laws
   first, then the plain rule's binders, with the journals, the callee's post (fpostW_xR / fpostWF_xR) and the
   conclusion at R. Each plain lemma is its R form at wle (wle_refl / wle_trans); its statement is unchanged.
   fpostW_x_R_lift: a plain fpostW_x (journal at wle) is fpostW_xR at every R that contains wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCbqGcallW.v; 1356 of its 1435 lines of code are new or changed and 732 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Tx102Glue.v, with its module paths and module names changed; 76 of its 110 lines of code are new or changed and 1401 lines of the source are left out. *)
(* fuzz_preset, the IMAGE CHECK of the #102 tx glue's per-instance image bounds, at image B': file TxGlue102ImgCheckB.
   OWNER a Theorem Labs lane (the kit owner / S10's owner). This is the B' half of lib/A/Prog/TxGlue102ImgCheck.v, MOVED, NOT WRITTEN:
   its (2) IMAGE B' and (3) NEGATIVE CONTROL (Section b, lines 108-205) and their read-outs (lines 209, 211-215), byte
   for byte from blob c0f5f4a5e1b2 at the cut 7cdbb61b5fa0. It was split out so that no
   A-tree file Requires lib.B (a Theorem Labs lane's shadow audit; a Theorem Labs lane ruled 06:42Z: move the B' checks to the B tree).
   The text under check, the instances, what each part checks and the numerals are as TxGlue102ImgCheck.v's header
   states them. The Requires are TxGlue102ImgCheck.v's own, in its order, less the A'-only modules (lib/A
   Listing_prog / PAImg_prog / AD2l / AImgShadowVisCf, which the moved text does not read). Rule 24: proves no
   function (kind: check). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YI00 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0ncf YGcfAmx2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Listing_prog PAImg_prog Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB AImgShadowVisCfB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Tx102Glue TxStr102Glue.
(* stdpp, through the LPS modules, shadows several list names; the list lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
#[local] Existing Instance CfParams_preset.

(* ======== (2) IMAGE B' ======== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {PI : PrhImg} {RL : PrhRoomLive}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Notation LB := Listing_prog.B_prog_listing.
#[local] Notation PBB := (PAImg_prog.PI_prog_B (rc := rc)).
#[local] Notation SEGSB := (@pa_segs _ LB PBB).
#[local] Notation BB := YD2l.TfibB.

Lemma pa_hi_ok_B : @pa_hi _ LB PBB <= 2 ^ 31.
Proof. change (@pa_hi _ LB PBB) with 0x601000. lia. Qed.
Lemma cf_img_ok_B : 0 <= @cf_img_lo CfImgB.CfImg_B /\ @cf_img_top CfImgB.CfImg_B <= 2 ^ 31.
Proof. change (@cf_img_lo CfImgB.CfImg_B) with 0x10000. change (@cf_img_top CfImgB.CfImg_B) with 0x601000. lia. Qed.
Lemma img_box_B : 4096 <= @pa_lo _ LB PBB /\ @pa_hi _ LB PBB <= kLowMemEnd.
Proof. change (@pa_lo _ LB PBB) with 0x10000. change (@pa_hi _ LB PBB) with 0x601000. unfold kLowMemEnd. lia. Qed.
Lemma img_cf_box_B : @cf_img_lo CfImgB.CfImg_B <= @pa_lo _ LB PBB /\ @pa_hi _ LB PBB <= @cf_img_top CfImgB.CfImg_B.
Proof.
change (@cf_img_lo CfImgB.CfImg_B) with 0x10000. change (@cf_img_top CfImgB.CfImg_B) with 0x601000.
change (@pa_lo _ LB PBB) with 0x10000. change (@pa_hi _ LB PBB) with 0x601000. lia.
Qed.
Lemma pal_uar_img_B : @cf_img_lo CfImgB.CfImg_B <= as_uar_cell BB /\ as_uar_cell BB + 4 <= @cf_img_top CfImgB.CfImg_B.
Proof.
change (@cf_img_lo CfImgB.CfImg_B) with 0x10000. change (@cf_img_top CfImgB.CfImg_B) with 0x601000.
change (as_uar_cell BB) with 0xab700. lia.
Qed.

Variable ARx : alayout -> astate -> list Z -> world SEGSB -> (word -> option byte) -> Model -> Prop.
Hypothesis HARx : forall ly S Hp W mem md, ARx ly S Hp W mem md -> ARcf SEGSB BB ly S Hp W mem md.
Hypothesis LAWS : AR_laws_x SEGSB BB ARx cf_head.
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow BB).

(* img_shadow_vis_x at B': h-mani-a8's B' instance, restated over ARx *)
Lemma img_shadow_vis_x_B : forall ly S Hp W mem md a, ARx ly S Hp W mem md ->
  @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B -> aview SEGSB (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a HAR Ha.
exact (AImgShadowVisCfB.tfib_img_shadow_vis_cf_B SEGSB BB YD2l.TfibB_syms ly S Hp W mem md a (HARx _ _ _ _ _ _ HAR) Ha).
Qed.

(* the same text instantiates at B' *)
Definition s10_src_img_B :=
  s10_src_img (ci := CfImgB.CfImg_B) (L := LB) (PA := PBB) BB ARx LAWS zs_aligned img_shadow_vis_x_B img_box_B
    img_cf_box_B.

(* THE B' TAIL [0x600000, 0x600010): inside the instance's kept_img bounds and its CfImg bounds, image bytes of B''s
   segments, and above image A's top *)
Lemma b_tail_covered : forall a, 0x600000 <= a < 0x600010 ->
  @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B /\ @pa_lo _ LB PBB <= a < @pa_hi _ LB PBB /\
  in_img SEGSB a /\ ~ (YImgTop.IMG_LO <= a < YImgTop.IMG_TOP).
Proof.
intros a Ha.
assert (E : existsb (fun sg => (Z.of_N (seg_base sg) <=? 0x600000) && (0x600010 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))
  SEGSB = true) by (change SEGSB with B.Img0.rsegs; vm_compute; reflexivity).
apply existsb_exists in E as (sg & Hin & Hb). apply andb_prop in Hb as (H1 & H2). apply Z.leb_le in H1, H2.
change (@cf_img_lo CfImgB.CfImg_B) with 0x10000. change (@cf_img_top CfImgB.CfImg_B) with 0x601000.
change (@pa_lo _ LB PBB) with 0x10000. change (@pa_hi _ LB PBB) with 0x601000.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP.
split; [lia|]. split; [lia|]. split; [|lia].
unfold in_img. exists sg. split; [exact Hin | lia].
Qed.

(* ... and their shadow is visible at every state of the walk, by the text's own premise at B' *)
Lemma b_tail_shadow_visible : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> 0x600000 <= a < 0x600010 ->
  aview SEGSB (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a HAR Ha. apply (img_shadow_vis_x_B ly S Hp W mem md a HAR). exact (proj1 (b_tail_covered a Ha)).
Qed.

(* ======== (3) THE NEGATIVE CONTROL: the A-constant forms at image B' ======== *)
(* N1. S10's old pa_box (S10TxState.v b7d596ea70bc:149) at B', with S10's own A-instance proof (S10TxString.v
   966080da4b30:159-160): the second `change` is refused, pa_hi of PI_prog_B is not A's IMG_TOP *)
Fail Example s10_pa_box_old_at_B : YImgTop.IMG_LO <= @pa_lo _ LB PBB /\ @pa_hi _ LB PBB <= YImgTop.IMG_TOP :=
  ltac:(change (@pa_lo _ _ PBB) with YImgTop.IMG_LO; change (@pa_hi _ _ PBB) with YImgTop.IMG_TOP;
        split; apply Z.le_refl).
(* ... and no proof of it exists *)
Lemma s10_pa_box_old_false_at_B : ~ (YImgTop.IMG_LO <= @pa_lo _ LB PBB /\ @pa_hi _ LB PBB <= YImgTop.IMG_TOP).
Proof. change (@pa_hi _ LB PBB) with 0x601000. unfold YImgTop.IMG_TOP. lia. Qed.

(* N2. the range of S10's old img_shadow_vis_x (S10TxState.v :143, [IMG_LO, IMG_TOP)) does not reach the B' tail *)
Fail Example s10_vis_old_covers_B_tail : forall a, 0x600000 <= a < 0x600010 -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP :=
  ltac:(intros a Ha; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; lia).
Lemma s10_vis_old_misses_B_tail : forall a, 0x600000 <= a < 0x600010 -> ~ (YImgTop.IMG_LO <= a < YImgTop.IMG_TOP).
Proof. intros a Ha. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP. lia. Qed.

(* N3. the #102 text with image A's CfImg bounds at PI_prog_B: its img_cf_box has no proof *)
Fail Example img_cf_box_B_at_A_bounds :
  @cf_img_lo CfImgA.CfImg_A <= @pa_lo _ LB PBB /\ @pa_hi _ LB PBB <= @cf_img_top CfImgA.CfImg_A :=
  ltac:(change (@cf_img_lo CfImgA.CfImg_A) with 0x10000; change (@cf_img_top CfImgA.CfImg_A) with 0x600000;
        change (@pa_lo _ LB PBB) with 0x10000; change (@pa_hi _ LB PBB) with 0x601000; lia).
Lemma img_cf_box_B_at_A_bounds_false :
  ~ (@cf_img_lo CfImgA.CfImg_A <= @pa_lo _ LB PBB /\ @pa_hi _ LB PBB <= @cf_img_top CfImgA.CfImg_A).
Proof. change (@cf_img_top CfImgA.CfImg_A) with 0x600000. change (@pa_hi _ LB PBB) with 0x601000. lia. Qed.

(* N4. ... and the B' premises do not fit the text at A's CfImg: the instantiation is refused *)
Fail Definition s10_src_img_B_at_A_bounds :=
  s10_src_img (ci := CfImgA.CfImg_A) (L := LB) (PA := PBB) BB ARx LAWS zs_aligned img_shadow_vis_x_B img_box_B
    img_cf_box_B.
End b.

(* ---- the read-outs: the B' instantiation's type, what it and the closed image facts rest on ---- *)
Check s10_src_img_B.
Print Assumptions s10_src_img_B.
Print Assumptions img_cf_box_B.
Print Assumptions b_tail_covered.
Print Assumptions b_tail_shadow_visible.
Print Assumptions s10_pa_box_old_false_at_B.
