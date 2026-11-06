(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_final.v; 44 of its 66 lines of code are new or changed and 17 lines of the source are left out. *)
(* Theorem Labs, 2026-10: THE CLOSED PAIR parse_value / parse_items on image B' (the 21:2xZ job; re-closed on the kit
   21:2xZ job; re-closed on the batch kit tip 03fcabb582d0, 04:3xZ). The batch kit's record texts tparse_value_specX and
   tparse_items_specX (lib/A/PRH_FnParse.v (sha256 54c89f77d32e; internal record), with the cursor set CW) at the relation: B := YD2l.TfibB, ARx := ARcfx = ARcf /\ xs_placed_cf,
   RL := prh_room_live_a8, the B' listing B_prog_listing / PI_prog_B, CfImg_B, CfParams_preset, prh_img_B.
   The mutual recursion closes by the kit's lib/A/VrdUnit.v vrd_unit_closed (downward induction on MAXD - d):
     step_PI  parse_items at d from parse_value at d + 1 below MAXD   PItems_final.v pi_step_PI_final (Qed)
     step_PV  parse_value at d from parse_items at the SAME depth d    PV_STEP below (PvB_Inst.v)
   PV_STEP is parse_value's per-depth instance theorem PvB_Inst.pvInst_step_PV at every float state. Everything else is
   a callee's text or an allocator stand-in, each with its owner:
     AMS  __asan_memset's m-form intrinsic contract                         the frame-class walk
     TGR  the batch kit's tgrow_specX                                                 the grow lane
     TPS  the batch kit's tparse_string_specX                                         the parse_string lane
     AF / AU  the free row in its keep form (YGcfMallocComposeKeep.afree_realizes_cf_rh_keep) / aunpoison_realizes_cf,
              fuzz_free_holds_B's own premises
   (parse_value's own callee rows TLIT / TPSTR / FMALLOC / ASM0 / CPY enter through PV_STEP's discharge, as that lemma's
   own premises; on the batch kit its two kit interims are gone: the batch kit's prh_oks and prh_refused_peak close them.)
   Rule 24: this file proves parse_items and parse_value at the instance (kind: composition of two walks), given
   the premises named above. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YM05 YI16 YC4aP YPsym YGcfNames YG0f YG0n YG0d YD2l YG0ncf YCbqG YA0n YG00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YGcfHp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnReader PRH_FnParse CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require VrdUnit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_top PItems_final.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_Inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Img0.
Local Open Scope Z_scope.

Section pair. Context {rc : YM05.RunCeil}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance CfImg_B.
#[local] Notation Lb := B_prog_listing.
#[local] Notation PIb := (@PI_prog_B rc).
#[local] Notation TB := YD2l.TfibB.
#[local] Notation RLa8 := PRH_Base.prh_room_live_a8.
#[local] Notation ARX := (fun ly S Hp W mem md =>
  YG0ncf.ARcf (cp := CfParams_preset) (@pa_segs _ Lb PIb) YD2l.TfibB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).
Variable SK : YI16.sink_head.

(* the two texts at depth d, at every float state, every entry CTX, every closure CTX0 and every cursor set CW *)
Definition pp_PV (d : nat) : Prop :=
  forall (fy : YK11.FPState) (CTX CTX0 CW : list (list Z)),
    tparse_value_specX (fx := fy) (RL := RLa8) (L := Lb) (PA := PIb) TB ARX SK d CTX CTX0 CW.
Definition pp_PI (d : nat) : Prop :=
  forall (fy : YK11.FPState) (CTX CTX0 CW : list (list Z)),
    tparse_items_specX (fx := fy) (RL := RLa8) (L := Lb) (PA := PIb) TB ARX SK d CTX CTX0 CW.

Hypothesis AMS : forall fy : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fy) (@pa_segs _ Lb PIb) TB ARX OSet (@pa_sigma _ Lb PIb AS___asan_memset).
Hypothesis TGR : forall (fy : YK11.FPState) (CTX0' : list (list Z)),
  tgrow_specX (fx := fy) (RL := RLa8) (L := Lb) (PA := PIb) TB ARX SK CTX0'.
Hypothesis TPS : forall (fy : YK11.FPState) (CTX0' CW' : list (list Z)),
  tparse_string_specX (fx := fy) (RL := RLa8) (L := Lb) (PA := PIb) TB ARX SK CTX0' CW'.
Hypothesis AF : forall fy : YK11.FPState,
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) (@pa_segs _ Lb PIb) TB.
Hypothesis AU : forall fy : YK11.FPState, YGcfHp.aunpoison_realizes_cf (fx := fy) (@pa_segs _ Lb PIb) TB.
(* ---- parse_value's own callee rows (PvB_Inst.v Section i, its kept hypotheses, verbatim but at EVERY
   float state, since parse_items calls parse_value at whatever float state the run reached) ---- *)
(* The kit's literal text; owner: literal's lane *)
Hypothesis TLIT : forall fy : YK11.FPState,
  tliteral_specX (fx := fy) (RL := RLa8) (PI := prh_img_B) (PA := PIb) TB ARX SK.
(* frame class 0's contract in the m-form at ARcf; owner: the frame-class walk *)
Hypothesis ASM0 : forall fy : YK11.FPState,
  YGcallMxmn.astack_malloc_realizes_xm (fx := fy) (@pa_segs _ Lb PIb) TB (YG0ncf.ARcf (cp := CfParams_preset) (@pa_segs _ Lb PIb) TB) 0.
(* The kit's fuzz_malloc text; owner: S1MallocB's lane (lib/B/Prog/FuzzMallocB.v) *)
Hypothesis FMALLOC : forall fy : YK11.FPState,
  PRH_FnAlloc.tfuzz_malloc_specX (fx := fy) (cp := CfParams_preset) (RL := RLa8) (PI := prh_img_B) (PA := PIb) TB ARX SK.
(* __asan_memcpy's row in the m-form at ARcf *)
Hypothesis CPY : forall fx1 : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fx1) (@pa_segs _ Lb PIb) TB (YG0ncf.ARcf (cp := CfParams_preset) (@pa_segs _ Lb PIb) TB)
    OCpy (@pa_sigma _ Lb PIb AS___asan_memcpy).
(* VrdUnit's step_PV, at the same depth: parse_value's per-depth instance theorem (PvB_Inst.v pvInst_step_PV)
   at every float state *)
Lemma PV_STEP : forall d, pp_PI d -> pp_PV d.
Proof.
intros d HPI fy CTX CTX0 CW.
exact (@PvB_Inst.pvInst_step_PV fy rc SK (TLIT fy) (fun CTX0' CW' => TPS fy CTX0' CW') (ASM0 fy) (FMALLOC fy) CPY
  d (fun CTX' CTX0' CW' => HPI fy CTX' CTX0' CW') CTX CTX0 CW).
Qed.

(* VrdUnit's step_PI over the fully quantified families, from PItems_final.v *)
Lemma pp_step_PI : forall d, ((d < PjGrammar.MAXD)%nat -> pp_PV (Nat.succ d)) -> pp_PI d.
Proof.
intros d HPV fy CTX CTX0 CW.
exact (pi_step_PI_final SK CTX0 CW AMS TGR TPS AF AU d
  (fun Hlt fy' CTX' => HPV Hlt fy' CTX' CTX0 CW) fy CTX).
Qed.

(* THE CLOSED PAIR at every depth *)
Theorem pv_pi_closed : forall d, pp_PV d /\ pp_PI d.
Proof. exact (VrdUnit.vrd_unit_closed pp_PV pp_PI pp_step_PI PV_STEP). Qed.

End pair.
