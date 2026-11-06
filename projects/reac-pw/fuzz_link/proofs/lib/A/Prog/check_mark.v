(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v; 57 of its 96 lines of code are new or changed and 270 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/check_refused.v, with its module names changed; 11 of its 39 lines of code are new or changed and 68 lines of the source are left out. *)
(* check_mark on image A (fuzz_link.asan 0x88450, listing offset AF_check_mark = 0x6284; listing
   (internal path) (internal record, sha256 02dda35ead16)): its contract
   lib/A/Prog/check_mark_c.v `check_mark_acontract` is check_write_c.v's `check_rc_acontract` at this entry, and
   check_write.v's walk `check_rc_aproof` runs at both listing offsets (the two listings have the same instruction words
   but the two jal of the abort path, which reach the same targets).

   Section hypotheses: LAWS, LV (LinkVals) are the image instance's facts (LAWS is YG0q.AR_laws_ok at the image's
   segments: check_mark_aproof_img).

   Proves check_mark (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable LinkSyms LinkList LinkPa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem LinkWalk check_write_c check_mark_c check_write.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.

Theorem check_mark_aproof : forall rlo rhi, check_mark_acontract SK SEGS rlo rhi B.
Proof.
intros rlo rhi. unfold check_mark_acontract.
replace CHECK_MARK_A with (pa_val A_TEXT + AF_check_mark) by (rewrite (lv_text LV); reflexivity).
exact (check_rc_aproof SK B LAWS AF_check_mark (or_intror eq_refl) rlo rhi).
Qed.
End w.

(* LAWS discharged on the image's segments (lib/Reusable/YG0q.v AR_laws_ok) *)
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem check_mark_aproof_img : forall B, LinkVals -> pa_segs = AB1v.tfibsegs ->
  forall rlo rhi, check_mark_acontract SK pa_segs rlo rhi B.
Proof.
intros B LV Hsegs.
assert (LAWS : AR_laws pa_segs B) by (rewrite Hsegs; exact (YG0q.AR_laws_ok AB1v.tfibsegs B)).
exact (check_mark_aproof SK B LAWS LV).
Qed.
End img.

Print Assumptions check_mark_aproof.
Print Assumptions check_mark_aproof_img.
