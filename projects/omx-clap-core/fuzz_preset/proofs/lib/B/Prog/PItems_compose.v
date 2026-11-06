(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_head.v; 120 of its 156 lines of code are new or changed and 1270 lines of the source are left out. *)
(* Theorem Labs, 2026-10: parse_items' image-B walk COMPOSED AT THE INSTANCE: VrdUnit's step_PI for the kit's text
   step_PI for the kit's record text tparse_items_specX (walk-S5b ae985686b11, lib/A/PRH_FnParse.v blob dcff6bfa302a; kit
   (sha256 494eefc5b155; internal record)), at PIi := prh_img_B, cp := CfParams_preset, L := B_prog_listing, PA := PI_prog_B,
   PL := PL_prog_B. PItems_top.v's pi_step_PI is applied with every segment step it takes discharged by its Qed lemma:
     EPI          pi_epi_holds          (PItems_entry.v)
     CLOSE2       pi_close2_holds       (PItems_head.v)
     FREE         pi_free_holds         (PItems_body_free.v; image facts from PItems_img.v,
                                         PIF_QS from PItems_entry.v pi_post_stable)
     STEP_VAL     pv_step_val           (PItems_value_top.v; the two cursor-kept statements from
                                         PItems_kept.v pi_cur_kept_callR / pi_curmem_kept_callR; its grow
                                         step is PItems_body_loop.v pil_grow_step, imported by PItems_value_sep.v)
     STEP_BODY    pi_body_holds         (PItems_body.v)
     STEP_HEAD    pi_head_holds         (PItems_head.v)
     STEP_ENTRY   pi_entry_holds        (PItems_entry.v)
     STEP_LOOP    pi_loop_holds         (PItems_body_loop.v; image facts from PItems_img.v)
     STEP_KEY     pi_key_holds          (PItems_body_key.v; image facts from PItems_img.v)
   EVERY segment step is discharged. pi_key_holds carries ONE named obligation, KEY_OBL (PItems_body_key.v
   pik_free_obl), stated only at the two missing-colon hand-offs: (a) the free's run event - owned by the kit, lands with
   tparse_string_specX's run-event restatement + the run_at-over-append lemma; (b) the class-24 live count - owner the
   batch, lands with iface_room_pos at the call + counts_of_room_pos_rl (or PackTreeTight).
   The remaining Section hypotheses are the callee texts and the instance laws, each with its owner:
     LAWS   AR_laws_x pa_segs B ARx cf_head          the instance (ARcf)
     PAL    PALib B                                  the instance (the witness lib/B/PALibB.v at TfibB)
     HSH / HZS / HIMG  pi_hshadow_law / pi_zs_law / pi_img_law     the instance (PItems_inst.v pii_hsh_x / pii_hzs_x / pii_himg_x)
     AMEMSET  the checked memset's intrinsic contract              the frame-class walk
     TSKW   the kit's tskip_ws_specX                      a Theorem Labs lane (skip_ws_holds, a working branch)
     TGROW  the kit's tgrow_specX                          the grow lane
     TFREE  the kit's tfuzz_free_specX                     the alloc lane (FuzzFreeB.v)
     TPSTR  the kit's tparse_string_specX                  the parse_string lane
   Nothing that rests on prh_univ_closure is green at the instance yet (the universe at TfibB lacks
   pj_free's sites); the closure is a premise of the texts, not a hypothesis here.
   Rule 24: proves no function in this file (kind: composition). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YCbqG YGcallMx YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
PItems_pres PItems_top PItems_kept PItems_img PItems_entry PItems_head PItems_body PItems_body_free PItems_value_top
PItems_body_loop PItems_body_key.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require skip_ws_mn.


Section compose. Context {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Notation Lb := B_prog_listing.
#[local] Notation PIb := (@PI_prog_B rc).
#[local] Notation PLb := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ Lb PIb).

Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
(* The batch kit (03fcabb582d0): the cursor set of the texts *)
Variable CW : list (list Z).

Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the depot holds no repeat in every ARx state (the cursor free's admission): AR_laws_x's field 25
   alx_depot_nodup on the kit's cut (YCbqG.v), read off LAWS inside PItems_body_free.v; at ARcf the engine proves it
   (YGcallcf.ARcf_depot_nodup) *)
Hypothesis PAL : PALib (L := Lb) (PI := PIb) B.
Hypothesis HSH : pi_hshadow_law (L := Lb) (PA := PIb) B ARx cf_head.
Hypothesis HZS : pi_zs_law (L := Lb) (PA := PIb) B ARx.
Hypothesis HIMG : pi_img_law (L := Lb) (PA := PIb) B ARx.
Hypothesis AMEMSET : forall fy : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS B ARx OSet (@pa_sigma _ Lb PIb AS___asan_memset).
(* skip_ws is PROVED on B' (lib/B/Prog/skip_ws_mn.v skip_ws_holds; the kit's tskip_ws_specX is the one in
   lib/A/PRH_FnReader.v (sha256 90e5c28192cc; internal record), character for character), so TSKW is a citation below, not a
   hypothesis *)
Hypothesis TGROW : forall (fy : YK11.FPState) (CTX0' : list (list Z)) ,
  tgrow_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK CTX0'.
Hypothesis TFREE : forall fy : YK11.FPState, tfuzz_free_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK.
Hypothesis TPSTR : forall (fy : YK11.FPState) (CTX0' CW' : list (list Z)),
  tparse_string_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK CTX0' CW'.
(* the key block's former named obligation KEY_OBL (PItems_body_key.v pik_free_obl) is GONE in form (b): the free
   hand-off's class-24 count is derived from pi_live and pi_ent's count premise, and the run-event half is no longer
   asked (PItems_body_key.v (sha256 5799614aa816; internal record)) *)

Let EPI := pi_epi_holds B ARx SK cf_head LAWS.
Let TSKW : forall fy : YK11.FPState, tskip_ws_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK :=
  fun fy => skip_ws_mn.skip_ws_holds (fx := fy) (HL := cf_head) SK B ARx LAWS (YC1fP.palib_core B PAL).
(* the segments read the callees' event lists (cf_head) as the grammar traces' events (PresetReqAt.HEAD): equal at
   the preset's CfParams (alloc.c's HEAD is 16) *)
Let PHD : cf_head = PresetReqAt.HEAD := eq_refl.

(* VrdUnit's step_PI at the instance *)
Theorem pi_step_PI_B : forall d,
  ((d < PjGrammar.MAXD)%nat -> pi_PV (L := Lb) (PA := PIb) B ARx SK CTX0 CW (Nat.succ d)) ->
  pi_PI (L := Lb) (PA := PIb) B ARx SK CTX0 CW d.
Proof.
apply (pi_step_PI (L := Lb) (PA := PIb) (PL := PLb) B ARx SK CTX0 CW).
- exact EPI.
- intros d. exact (pi_close2_holds B ARx SK d CTX0 CW cf_head LAWS (EPI d)).
- intros d. exact (pi_free_holds SK B ARx LAWS EPI TFREE pii_frpi pii_fs0 pii_fsite pii_pstro
    ltac:(intros; eapply pi_post_stable) PHD d CTX0 CW).
- exact (pv_step_val SK B ARx CTX0 CW LAWS HSH pii_hw AMEMSET TSKW
    (pi_cur_kept_callR (L := Lb) (PA := PIb) B ARx LAWS HSH HZS HIMG pii_pstro)
    (pi_curmem_kept_callR (L := Lb) (PA := PIb) B ARx LAWS HSH HZS HIMG pii_pstro) (fun fy => TGROW fy CTX0) PHD).
- intros d N. exact (pi_key_holds SK B ARx LAWS EPI TSKW TPSTR PHD pii_frpi pii_fr0 pii_s0str pii_pstro pii_pstimg
    pii_hw HSH HZS HIMG d CTX0 CW N).
- intros d N. exact (pi_body_holds SK B ARx LAWS d CTX0 CW N).
- intros d. exact (pi_loop_holds SK B ARx LAWS EPI TGROW pii_frpi pii_s0g pii_pstro pii_pstimg PHD HSH HZS HIMG
    d CTX0 CW).
- intros d. exact (pi_head_holds B ARx SK d CTX0 CW cf_head LAWS).
- intros d Hh _ fy CTX.
  exact (pi_entry_holds (fx := fy) B ARx cf_head LAWS PAL SK d CTX0 CW Hh
    HSH HZS HIMG preset_head_wide CTX).
Qed.

End compose.

(* ---- AT THE B INSTANCE: B := YD2l.TfibB, ARx := YG0ncf.ARcf rsegs TfibB. The instance laws are DISCHARGED
   by lib/B/PALibB.v (sha256 a42c120123e9; internal record) (taken by path; owner 12:28Z):
   LAWS by exvi_eh_laws, PAL by exvi_eh_palib (the head fact is preset_head_wide, = exvi_eh_head). What remains is the
   shadow laws HSH / HZS / HIMG, AMEMSET (frame-class walk) and the callee texts TGROW / TFREE / TPSTR.
   skip_ws is a citation (skip_ws_mn.v), and the key block's former obligation KEY_OBL is gone in form (b). ---- *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.

Section inst. Context {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Notation Lb := B_prog_listing.
#[local] Notation PIb := (@PI_prog_B rc).
#[local] Notation PLb := PL_prog_B.
#[local] Notation TB := YD2l.TfibB.
#[local] Notation ARI := (YG0ncf.ARcf (cp := CfParams_preset) rsegs YD2l.TfibB).

Theorem pi_step_PI_TfibB : forall (SK : YI16.sink_head) (CTX0 CW : list (list Z)),
  pi_hshadow_law (L := Lb) (PA := PIb) TB ARI cf_head ->
  pi_zs_law (L := Lb) (PA := PIb) TB ARI ->
  pi_img_law (L := Lb) (PA := PIb) TB ARI ->
  (forall fy : YK11.FPState,
     YGcallMxmn.aintrin_realizes_xm (fx := fy) (@pa_segs _ Lb PIb) TB ARI OSet (@pa_sigma _ Lb PIb AS___asan_memset)) ->
  (forall (fy : YK11.FPState) (CTX0' : list (list Z)) ,
     tgrow_specX (fx := fy) (L := Lb) (PA := PIb) TB ARI SK CTX0') ->
  (forall fy : YK11.FPState, tfuzz_free_specX (fx := fy) (L := Lb) (PA := PIb) TB ARI SK) ->
  (forall (fy : YK11.FPState) (CTX0' CW' : list (list Z)),
     tparse_string_specX (fx := fy) (L := Lb) (PA := PIb) TB ARI SK CTX0' CW') ->
  forall d,
  ((d < PjGrammar.MAXD)%nat -> pi_PV (L := Lb) (PA := PIb) TB ARI SK CTX0 CW (Nat.succ d)) ->
  pi_PI (L := Lb) (PA := PIb) TB ARI SK CTX0 CW d.
Proof.
intros SK CTX0 CW HSH HZS HIMG AMS TGR TFR TPS.
exact (pi_step_PI_B TB ARI SK CTX0 CW PALibB.exvi_eh_laws PALibB.exvi_eh_palib HSH HZS HIMG AMS TGR TFR TPS).
Qed.

End inst.

(* ---- AT THE RELATION for the image-B TFIB closure (16:3xZ): ARx := ARcfx = (ARcf pa_segs TfibB
   /\ xs_placed_cf), RL := prh_room_live_a8 - the relation of a Theorem Labs lane's bridge interface, the image-B tx_put walk's rows and
   FuzzFreeB.v's fuzz_free_holds_B. Discharged here:
     LAWS   by YGcallcf.AR_laws_x_xs pa_segs TfibB (YG0lawscf.AR_laws_ok_cf pa_segs TfibB) - unconditional, the same
            term FuzzFreeB.v:340 uses (no transfer from PALibB.v's ARcf laws is needed);
     PAL    by PALibB.exvi_eh_palib (PALib does not mention ARx);
     TFREE  by FuzzFreeB.fuzz_free_holds_B (lib/B/Prog/FuzzFreeB.v:971), its image binding TS by YD2l.TfibB_syms;
            its other premises AFREE (the free row in its keep form, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep)
            / AUNPOISON / pal_pst_ok / pal_unpoison become premises here.
   fuzz_free_holds_B is at image B's call-memory instance CfImgB.CfImg_B, so this Section is too.
   pi_step_PI_TfibB (at ARcf) above is kept as it is. ---- *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallcf YG0lawscf YGcfHp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzFreeB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.

Section instx. Context {rc : YM05.RunCeil}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Notation Lb := B_prog_listing.
#[local] Notation PIb := (@PI_prog_B rc).
#[local] Notation PLb := PL_prog_B.
#[local] Notation TB := YD2l.TfibB.
#[local] Notation RLa8 := PRH_Base.prh_room_live_a8.
#[local] Notation ARX := (fun ly S Hp W mem md =>
  YG0ncf.ARcf (cp := CfParams_preset) (@pa_segs _ Lb PIb) YD2l.TfibB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

Theorem pi_step_PI_TfibBx : forall (SK : YI16.sink_head) (CTX0 CW : list (list Z)),
  pi_hshadow_law (L := Lb) (PA := PIb) TB ARX cf_head ->
  pi_zs_law (L := Lb) (PA := PIb) TB ARX ->
  pi_img_law (L := Lb) (PA := PIb) TB ARX ->
  (forall fy : YK11.FPState,
     YGcallMxmn.aintrin_realizes_xm (fx := fy) (@pa_segs _ Lb PIb) TB ARX OSet (@pa_sigma _ Lb PIb AS___asan_memset)) ->
  (forall (fy : YK11.FPState) (CTX0' : list (list Z)) ,
     tgrow_specX (fx := fy) (RL := RLa8) (L := Lb) (PA := PIb) TB ARX SK CTX0') ->
  (forall (fy : YK11.FPState) (CTX0' CW' : list (list Z)),
     tparse_string_specX (fx := fy) (RL := RLa8) (L := Lb) (PA := PIb) TB ARX SK CTX0' CW') ->
  (* fuzz_free_holds_B's own premises (the fuzz_free walk's stand-ins) *)
  (forall fy : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) (@pa_segs _ Lb PIb) TB) ->
  (forall fy : YK11.FPState, YGcfHp.aunpoison_realizes_cf (fx := fy) (@pa_segs _ Lb PIb) TB) ->
  (forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
     ~ Exists (in_zr a) (as_owned_static TB) /\ ~ (as_errno TB <= a < as_errno TB + 4)) ->
  @pa_sigma _ Lb PIb AS___asan_unpoison_memory_region = cf_pc_unpoison ->
  forall d,
  ((d < PjGrammar.MAXD)%nat -> pi_PV (RL := RLa8) (L := Lb) (PA := PIb) TB ARX SK CTX0 CW (Nat.succ d)) ->
  pi_PI (RL := RLa8) (L := Lb) (PA := PIb) TB ARX SK CTX0 CW d.
Proof.
intros SK CTX0 CW HSH HZS HIMG AMS TGR TPS AF AU PST UNP.
exact (pi_step_PI_B (RL := RLa8) TB ARX SK CTX0 CW
  (YGcallcf.AR_laws_x_xs (@pa_segs _ Lb PIb) TB (YG0lawscf.AR_laws_ok_cf (@pa_segs _ Lb PIb) TB))
  PALibB.exvi_eh_palib HSH HZS HIMG AMS TGR
  (fun fy => FuzzFreeB.fuzz_free_holds_B (fx := fy) (SK := SK) TB (AF fy) (AU fy) PALibB.exvi_eh_palib PST UNP
     YD2l.TfibB_syms)
  TPS).
Qed.

End instx.
