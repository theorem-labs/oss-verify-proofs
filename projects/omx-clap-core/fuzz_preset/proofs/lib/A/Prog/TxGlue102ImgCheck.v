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
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Tx102Glue.v, with its module paths and module names changed; 37 of its 65 lines of code are new or changed and 1407 lines of the source are left out. *)
(* fuzz_preset, the IMAGE CHECK of the #102 tx glue's per-instance image bounds, at image A' and at image B'.
   OWNER h-hpreset-7 (K0 / S10's owner), branch cold/h-hpreset-7-s10-perinst. This file changes no other file.
   THE TEXT UNDER CHECK is the #102 tx glue that S10's #102 move cites (a Theorem Labs lane's ruling 19:36Z), taken by path, unchanged:
   - lib/A/Prog/Tx102Glue.v ec9d6e6a0914 (owner h-rw-pre-5, lane BTxValueB): s10_src_img, the route of a read-only
     literal, under its Section hypotheses img_shadow_vis_x (:1041), img_box (:1044) and img_cf_box (:1045);
   - lib/A/Prog/TxStr102Glue.v bff94397b16a (owner h-rw-pre-5, lane TxStrBp): the same three (:528, :530, :531), and
     pa_hi_ok (:486), cf_img_ok (:488) and pal_uar_img (:509); it passes the three to s10_src_img (:1271).
   Both from h-rw-pre-5's INT102-READY commits: TxStr102Glue.v from cold/h-rw-pre-5-r102-txstrB dcab39c6a1ce,
   Tx102Glue.v from cold/h-rw-pre-5-r102-txB 02fc33de3e82 (the same two blobs as at 5c998d4b8b0c, where this check
   first took them). Every bound there is the instance's pa_lo / pa_hi or the CfImg's cf_img_lo / cf_img_top; none is
   YImgTop's IMG_LO / IMG_TOP, and there is no pa_box.
   WHAT THIS FILE CHECKS:
   (1) IMAGE A': every image premise above holds at PI_prog_A / CfImg_A / TfibB (lib/A/AD2l.v); img_shadow_vis_x by
       h-mani-a8's instance (lib/A/AImgShadowVisCf.v tfib_img_shadow_vis_cf); s10_src_img instantiates there
       (s10_src_img_A).
   (2) IMAGE B': the same at PI_prog_B / CfImg_B / TfibB (lib/Reusable/YD2l.v); img_shadow_vis_x by h-mani-a8's B'
       instance (lib/AU/AImgShadowVisCfB.v 18b6de6fa4e8 tfib_img_shadow_vis_cf_B, by path from
       cold/h-mani-a8-alloc102 22d71cc04fb0); s10_src_img instantiates there (s10_src_img_B). The bytes
       [0x600000, 0x600010) - B''s last PT_LOAD above A's top (lib/Reusable/YImgTop.v d2a97d3111ce:25-26) - are inside
       the B' bounds, are image bytes, and have a visible shadow at every state (b_tail_covered, b_tail_shadow_visible).
   (3) NEGATIVE CONTROL: S10's old-pin A-constant forms at image B' fail, and so does the #102 text with image A's
       CfImg bounds at PI_prog_B. Each `Fail` prints its error in the build log; each refutation lemma (..._false_at_B,
       ..._misses_B_tail) shows that no proof of the old form exists. The old forms are quoted from
       cold/h-hpreset-7-walk-S10-acc abe7dfed0746: pa_box (S10TxState.v b7d596ea70bc:149), S10's own A-instance proof
       of it (S10TxString.v 966080da4b30:159-160, pa_box_A), and the range of img_shadow_vis_x (S10TxState.v :143).
   (2) and (3) are lib/B/Prog/TxGlue102ImgCheckB.v: moved there byte for byte so that no A-tree file Requires lib.B
   (a Theorem Labs lane's shadow audit; a Theorem Labs lane's ruling 06:42Z). This file no longer Requires lib.B, lib.AU, YImgTop or YD2l.
   The instances' bounds are named by their fields; a numeral appears only as the value a field reduces to, in a
   `change` of an instance proof. Numerals: 0x600000 / 0x600010 (ADDRESS: the B' tail range under test, from
   YImgTop.v's comment); 0x10000 / 0x600000 / 0x601000 / 0xaaec0 / 0xab700 (DERIVED: the values of pa_lo, pa_hi,
   cf_img_lo, cf_img_top and as_uar_cell at the two instances); 4096, 4, 2 ^ 31 (LENGTH / DERIVED: the premises' own
   constants). Rule 24: proves no function (kind: check). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Listing_prog PAImg_prog AD2l CfImgA AImgShadowVisCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Tx102Glue TxStr102Glue.
(* stdpp, through the LPS modules, shadows several list names; the list lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
#[local] Existing Instance CfParams_preset.

(* ======== (1) IMAGE A' ======== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {PI : PrhImg} {RL : PrhRoomLive}.
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Notation LA := Listing_prog.A_prog_listing.
#[local] Notation PAA := (PAImg_prog.PI_prog_A (rc := rc)).
#[local] Notation SEGSA := (@pa_segs _ LA PAA).
#[local] Notation BA := AD2l.TfibB.

Lemma pa_hi_ok_A : @pa_hi _ LA PAA <= 2 ^ 31.
Proof. change (@pa_hi _ LA PAA) with 0x600000. lia. Qed.
Lemma cf_img_ok_A : 0 <= @cf_img_lo CfImgA.CfImg_A /\ @cf_img_top CfImgA.CfImg_A <= 2 ^ 31.
Proof. change (@cf_img_lo CfImgA.CfImg_A) with 0x10000. change (@cf_img_top CfImgA.CfImg_A) with 0x600000. lia. Qed.
Lemma img_box_A : 4096 <= @pa_lo _ LA PAA /\ @pa_hi _ LA PAA <= kLowMemEnd.
Proof. change (@pa_lo _ LA PAA) with 0x10000. change (@pa_hi _ LA PAA) with 0x600000. unfold kLowMemEnd. lia. Qed.
Lemma img_cf_box_A : @cf_img_lo CfImgA.CfImg_A <= @pa_lo _ LA PAA /\ @pa_hi _ LA PAA <= @cf_img_top CfImgA.CfImg_A.
Proof.
change (@cf_img_lo CfImgA.CfImg_A) with 0x10000. change (@cf_img_top CfImgA.CfImg_A) with 0x600000.
change (@pa_lo _ LA PAA) with 0x10000. change (@pa_hi _ LA PAA) with 0x600000. lia.
Qed.
Lemma pal_uar_img_A : @cf_img_lo CfImgA.CfImg_A <= as_uar_cell BA /\ as_uar_cell BA + 4 <= @cf_img_top CfImgA.CfImg_A.
Proof.
change (@cf_img_lo CfImgA.CfImg_A) with 0x10000. change (@cf_img_top CfImgA.CfImg_A) with 0x600000.
change (as_uar_cell BA) with 0xaaec0. lia.
Qed.

(* the allocator relation of a walk: any relation that implies ARcf (ARcf itself, or ARcfx = ARcf /\ placed) *)
Variable ARx : alayout -> astate -> list Z -> world SEGSA -> (word -> option byte) -> Model -> Prop.
Hypothesis HARx : forall ly S Hp W mem md, ARx ly S Hp W mem md -> ARcf SEGSA BA ly S Hp W mem md.
(* not image bounds: the allocator laws and the zero-shadow alignment stay the instance's premises *)
Hypothesis LAWS : AR_laws_x SEGSA BA ARx cf_head.
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow BA).

(* img_shadow_vis_x at A': h-mani-a8's instance, restated over ARx *)
Lemma img_shadow_vis_x_A : forall ly S Hp W mem md a, ARx ly S Hp W mem md ->
  @cf_img_lo CfImgA.CfImg_A <= a < @cf_img_top CfImgA.CfImg_A -> aview SEGSA (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a HAR Ha.
exact (AImgShadowVisCf.tfib_img_shadow_vis_cf SEGSA BA AD2l.TfibB_syms ly S Hp W mem md a (HARx _ _ _ _ _ _ HAR) Ha).
Qed.

(* the text instantiates at A' *)
Definition s10_src_img_A :=
  s10_src_img (ci := CfImgA.CfImg_A) (L := LA) (PA := PAA) BA ARx LAWS zs_aligned img_shadow_vis_x_A img_box_A
    img_cf_box_A.
End a.

(* ---- the read-outs: the A' instantiation's type, what it rests on (B''s: lib/B/Prog/TxGlue102ImgCheckB.v) ---- *)
Check s10_src_img_A.
Print Assumptions s10_src_img_A.
