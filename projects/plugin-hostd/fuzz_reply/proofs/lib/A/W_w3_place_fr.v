(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the placement premises of W3's ARx walks check_no_loss (W_check_no_loss.v
   Section c) and check_shape_ends (W_cshe_top.v Section c), discharged at the pinned placement PB_fr (W_img.v), the
   start-up instance B := TfibB (AD2l.v, TfibB_syms) and the free table K0's CTX_AFREE (ACk0.v), in the form of
   W_w1_place.v / W_rom_place_fr.v.  Each statement is the walk's Section text, with PI := PB_fr, B := TfibB,
   CTX_AFREE := ACk0.CTX_AFREE and, for HEND5S, ARx := top_x's ARX (ARcf at CfParams_reply with Hp = [], spelled out
   as W_shadow_pin_x.v ashp_str2_1_fr_cf spells it, so this file does not import top_x).  Names: <walk>_<premise>_fr.
     check_no_loss:    CNLAP, HGR, HGRR, ROMNS, HCTX_cnl_free.
     check_shape_ends: HCTX_cshe_l2, HCTX_cshe_l3, PLACEG0, PLACEG32, HGR, HGRR, ROMNS, HEND5R, HEND5S, HGS.
     list_drop (W_list_drop_top.v Section ec, the caller-context walk check_no_loss's gesture_model takes): HCTX.
   The objects and literals at PB_fr: g_gone 0x5d8860 (1), g_nout 0x5d88c0 (8), g_out 0x5d8b40 (8), g_s 0x5d88e0 (384),
   " end" 0x20f00 (5), "param_gesture" 0x20f20 (13), "begin" 0x20f40 (5), "end" 0x20f60 (3); the shadow GOT slot
   A_OBJ 0 0x9d9d0 and the shadow cell A_OBJ 32 0xa60b8 (8 each); errno 0x5d93cc (AF0m TFIB_ERRNO); check_no_loss at
   0x85958, check_shape_ends at 0x853b0, list_drop at 0x85814.  The free sites' return addresses are the
   functions' own (ACej.v TRACES_check_no_loss [[0x53f2c; 0x85ac0]], TRACES_check_shape_ends [[0x53f2c; 0x8551c];
   [0x53f2c; 0x8562c]], TRACES_list_drop [[0x53f2c; 0x85874]]; the *_trace_fr remarks check each against its TRACES
   row), and each singleton [ra] is a row of ACk0.v CTX_AFREE (its edges (CTX_check_no_loss, 0x85ac0, CTX_AFREE,
   K0Lit), (CTX_check_shape_ends, 0x8551c / 0x8562c, CTX_AFREE, K0Lit), (CTX_list_drop, 0x85874, CTX_AFREE, K0Lit)).
   ACej.v and ACk0.v here are byte-identical to a working branch ed7e2968f0d's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YG00 YG0a YG01 YG0f YG0n YG0d YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_tbl W_kit W_img W_journal W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AF0l AF0m AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACej ACk0 W_LLVMFuzzerTestOneInput_G.
(* Require without Import: cshe_ro, the read-only-byte facts of the image and the shadow-pin decider, cited qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_check_shape_ends W_rom_place_fr W_shadow_pin
W_shadow_pin_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* the ASan image's sink instance, as top_x names it *)
#[local] Existing Instance AE2k.tfib_sink_head.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* Replace each object address the goal names at PB_fr by its value (W_w1_place.v w1_vals). *)
Local Ltac w3_vals := repeat match goal with |- context [@pa_val ?T ?L PB_fr ?n] =>
  let v := eval vm_compute in (@pa_val T L PB_fr n) in change (@pa_val T L PB_fr n) with v end.

(* ------------------------------------------------------------------ the instance's facts, decided *)
(* errno of the start-up instance (AF0m.v ts_errno; TFIB_ERRNO = TFIB_ERRNO_A = 0x5d93cc) *)
Lemma w3_tfib_errno : as_errno TfibB = TFIB_ERRNO_A.
Proof. exact (AF0m.ts_errno TfibB TfibB_syms). Qed.

(* gx_ok of a list G of ranges: every byte in a segment, and every range apart from each of the instance's owned
   statics (AF0m.v Tfib_owned_static), both decided *)
Lemma w3_gx_ok_b : forall G, forallb (rng_all (segin SEGS)) G = true ->
  forallb (fun r => forallb (fun o => (fst o + snd o <=? fst r) || (fst r + snd r <=? fst o))
    AF0m.Tfib_owned_static) G = true ->
  (* QMm W0': gx_ok's third clause, the same decided apartness against AF0m.Tfib_kept *)
  forallb (fun r => forallb (fun o => (fst o + snd o <=? fst r) || (fst r + snd r <=? fst o))
    AF0m.Tfib_kept) G = true ->
  gx_ok SEGS TfibB G.
Proof.
intros G Hi Ho Hk a Ha. split; [apply segin_ok; exact (rng_all_in _ G a Hi Ha)|].
split.
- rewrite (AF0m.ts_owned TfibB TfibB_syms). intros Hex.
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz). rewrite forallb_forall in Ho.
  exact (apart_of_b AF0m.Tfib_owned_static (fst r) (snd r) (Ho r Hr) a Hex Hz).
- rewrite (AF0m.ts_kept TfibB TfibB_syms). intros Hex.
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz). rewrite forallb_forall in Hk.
  exact (apart_of_b AF0m.Tfib_kept (fst r) (snd r) (Hk r Hr) a Hex Hz).
Qed.

(* gx_rt of a list G of ranges: every range apart from errno's 4 bytes, the shadow GOT slot and the shadow cell *)
Lemma w3_gx_rt_b : forall G,
  forallb (fun r => (fst r + snd r <=? TFIB_ERRNO_A) || (TFIB_ERRNO_A + 4 <=? fst r)) G = true ->
  forallb (fun r => (fst r + snd r <=? VAL (A_OBJ 0)) || (VAL (A_OBJ 0) + 8 <=? fst r)) G = true ->
  forallb (fun r => (fst r + snd r <=? VAL (A_OBJ 32)) || (VAL (A_OBJ 32) + 8 <=? fst r)) G = true ->
  gx_rt (PI := PB_fr) TfibB G.
Proof.
intros G He H0 H32 a Ha. rewrite w3_tfib_errno.
exact (conj (apart_of_b G _ _ He a Ha) (conj (apart_of_b G _ _ H0 a Ha) (apart_of_b G _ _ H32 a Ha))).
Qed.

(* ------------------------------------------------------------------ check_no_loss (W_check_no_loss.v Section c) *)
(* CNLAP (W_check_no_loss.v:340) *)
Lemma check_no_loss_CNLAP_fr : cnl_objs_apart (PI := PB_fr).
Proof.
unfold cnl_objs_apart. cbv zeta. w3_vals.
split; [reflexivity|].
repeat match goal with |- _ /\ _ => split; [lia|] end.
intros a Ha Hr. apply W_rom_place_fr.fr_rom_range in Hr. lia.
Qed.

(* HGR (W_check_no_loss.v:342) *)
Lemma check_no_loss_HGR_fr : gx_ok SEGS TfibB (cnl_ro (PI := PB_fr)).
Proof. apply w3_gx_ok_b; vm_compute; reflexivity. Qed.

(* HGRR (W_check_no_loss.v:343) *)
Lemma check_no_loss_HGRR_fr : gx_rt (PI := PB_fr) TfibB (cnl_ro (PI := PB_fr)).
Proof. apply w3_gx_rt_b; vm_compute; reflexivity. Qed.

(* ROMNS (W_check_no_loss.v:346): no read-only byte is errno's (_G.v c_rom_noerr), and an owned read-only byte is
   pinned (_G.v c_rom_pinned, over AF0m's Tfib_const_abs cells) *)
Lemma check_no_loss_ROMNS_fr : forall a, in_rom SEGS a -> ~ (as_errno TfibB <= a < as_errno TfibB + 4) /\
  (Exists (in_zr a) (as_owned_static TfibB) -> rom_pinned SEGS TfibB a).
Proof.
intros a Ha. split; [exact (proj1 (c_rom_noerr TfibB w3_tfib_errno a Ha)) | exact (c_rom_pinned TfibB TfibB_syms a Ha)].
Qed.

(* HCTX_cnl_free (W_check_no_loss.v:360): the free at 0x85abc returns to 0x85ac0 = check_no_loss + 0x168 *)
Lemma check_no_loss_HCTX_cnl_free_fr : In [BASE + AF_fr_check_no_loss + 0x168] CTX_AFREE.
Proof.
assert (E : [BASE + AF_fr_check_no_loss + 0x168] = [0x85ac0]) by (vm_compute; reflexivity).
rewrite E. unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]).
Qed.
(* that return address is check_no_loss's own: its free trace (pc0 0x53f2c) is ACej.v TRACES_check_no_loss's row *)
Remark check_no_loss_HCTX_cnl_free_trace_fr : In [0x53f2c; BASE + AF_fr_check_no_loss + 0x168] TRACES_check_no_loss.
Proof. vm_compute. left. reflexivity. Qed.

(* ------------------------------------------------------------------ list_drop (W_list_drop_top.v Section ec) *)
(* HCTX (W_list_drop_top.v Section ec): list_drop's free returns to 0x85874 = list_drop + 0x60 *)
Lemma list_drop_HCTX_fr : In [BASE + AF_fr_list_drop + 0x60] CTX_AFREE.
Proof.
assert (E : [BASE + AF_fr_list_drop + 0x60] = [0x85874]) by (vm_compute; reflexivity).
rewrite E. unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]).
Qed.
Remark list_drop_HCTX_trace_fr : In [0x53f2c; BASE + AF_fr_list_drop + 0x60] TRACES_list_drop.
Proof. vm_compute. left. reflexivity. Qed.

(* ------------------------------------------------------------------ check_shape_ends (W_cshe_top.v Section c) *)
(* HCTX_cshe_l2 (W_cshe_top.v:98): loop 2's free at 0x85518 returns to 0x8551c = check_shape_ends + 0x16c *)
Lemma check_shape_ends_HCTX_cshe_l2_fr : In [BASE + AF_fr_check_shape_ends + 0x16c] CTX_AFREE.
Proof.
assert (E : [BASE + AF_fr_check_shape_ends + 0x16c] = [0x8551c]) by (vm_compute; reflexivity).
rewrite E. unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]).
Qed.
Remark check_shape_ends_HCTX_cshe_l2_trace_fr :
  In [0x53f2c; BASE + AF_fr_check_shape_ends + 0x16c] TRACES_check_shape_ends.
Proof. vm_compute. left. reflexivity. Qed.

(* HCTX_cshe_l3 (W_cshe_top.v:99): loop 3's free at 0x85628 returns to 0x8562c = check_shape_ends + 0x27c *)
Lemma check_shape_ends_HCTX_cshe_l3_fr : In [BASE + AF_fr_check_shape_ends + 0x27c] CTX_AFREE.
Proof.
assert (E : [BASE + AF_fr_check_shape_ends + 0x27c] = [0x8562c]) by (vm_compute; reflexivity).
rewrite E. unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]).
Qed.
Remark check_shape_ends_HCTX_cshe_l3_trace_fr :
  In [0x53f2c; BASE + AF_fr_check_shape_ends + 0x27c] TRACES_check_shape_ends.
Proof. vm_compute. right. left. reflexivity. Qed.

(* PLACEG0 / PLACEG32 (W_cshe_top.v:119-120) *)
Lemma check_shape_ends_PLACEG0_fr : VAL A_g_gone + 1 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= VAL A_g_gone.
Proof. w3_vals. lia. Qed.
Lemma check_shape_ends_PLACEG32_fr : VAL A_g_gone + 1 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= VAL A_g_gone.
Proof. w3_vals. lia. Qed.

(* HGR / HGRR (W_cshe_top.v:121-122) *)
Lemma check_shape_ends_HGR_fr : gx_ok SEGS TfibB (W_check_shape_ends.cshe_ro (PI := PB_fr)).
Proof. apply w3_gx_ok_b; vm_compute; reflexivity. Qed.
Lemma check_shape_ends_HGRR_fr : gx_rt (PI := PB_fr) TfibB (W_check_shape_ends.cshe_ro (PI := PB_fr)).
Proof. apply w3_gx_rt_b; vm_compute; reflexivity. Qed.

(* ROMNS (W_cshe_top.v:123), check_no_loss's text *)
Lemma check_shape_ends_ROMNS_fr : forall a, in_rom SEGS a -> ~ (as_errno TfibB <= a < as_errno TfibB + 4) /\
  (Exists (in_zr a) (as_owned_static TfibB) -> rom_pinned SEGS TfibB a).
Proof. exact check_no_loss_ROMNS_fr. Qed.

(* HEND5R (W_cshe_top.v:125): " end\0" (0x20f00, 5 bytes) lies in the "r--" segment [0x10000, 0x30000) *)
Lemma check_shape_ends_HEND5R_fr : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom SEGS a.
Proof.
intros a Ha. apply W_rom_place_fr.fr_rom000.
let v := eval vm_compute in (VAL A_lit_end5) in change (VAL A_lit_end5) with v in Ha.
lia.
Qed.

(* HEND5S (W_cshe_top.v:126) at top_x's ARX: " end" (0x20f00, 4 bytes), shadow 0x7fffc1e0 = 5, decided over the
   start-up tables (W_shadow_pin_fr.v ashp_end5_4_fr's check) through W_shadow_pin_x.tfib_shp_x; the laws as top_x's
   ARX_laws proves them *)
Lemma check_shape_ends_HEND5S_fr :
  ashp_x (fun ly S Hp (W : world SEGS) mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) SEGS TfibB ly S Hp W mem md /\ Hp = [])
    (VAL A_lit_end5) 4.
Proof.
assert (Hc : W_shadow_pin.shp_check AF0m.Tfib_const_shadow AF0m.Tfib_zero_shadow (VAL A_lit_end5) 4 = true)
  by (vm_compute; reflexivity).
assert (L : AR_laws_x SEGS TfibB
  (fun ly S Hp (W : world SEGS) mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) SEGS TfibB ly S Hp W mem md /\ Hp = [])
  (@cf_head CfParams_reply)).
{ apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) SEGS TfibB (AR_laws_ok_cf (cp := CfParams_reply) SEGS TfibB)). }
exact (W_shadow_pin_x.tfib_shp_x TfibB TfibB_syms _ L _ _ Hc).
Qed.

(* HGS (W_cshe_top.v:127): g_s is image, not read-only (W_rom_place_fr.v g_s_rom_fr), apart from g_gone / g_nout /
   g_out *)
Lemma check_shape_ends_HGS_fr : forall a, VAL (A_OBJ 22) <= a < VAL (A_OBJ 22) + 384 -> in_img SEGS a /\
  ~ in_rom SEGS a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).
Proof.
intros a Ha. split.
{ apply segin_ok. apply (rng_all_in (segin SEGS) [(VAL (A_OBJ 22), 384)]); [vm_compute; reflexivity|].
  apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact Ha. }
split; [exact (W_rom_place_fr.g_s_rom_fr a Ha)|].
let v := eval vm_compute in (VAL (A_OBJ 22)) in change (VAL (A_OBJ 22)) with v in Ha.
w3_vals. repeat split; lia.
Qed.
End a.
