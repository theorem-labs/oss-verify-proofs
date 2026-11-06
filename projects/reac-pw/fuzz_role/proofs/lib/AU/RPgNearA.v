(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgSlots.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632 for fuzz_qdisc's image A) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_cfg_apply_state 0x82ed4 against lib/A/RPgCSpec.v's rl_cfg_apply_state_specX on the concrete image lib/A/Img0.v rsegs, with the plumbing of lib/A/RPgCfgChanges.v; the plain walk it replaces is lib/Prog/reac_role_cfg_apply_state.v (a split on the beq). The leaf's post is RPgCSpec's rl_post (the float state fx kept, no extra bytes E); qdisc's region of the divisor constant, its arithmetic lemmas and its three branches are dropped. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgCfgApply.v; 18 of its 33 lines of code are new or changed and 42 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgNearA.v; 14 of its 38 lines of code are new or changed and 9 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgNearA.v at 92636bfca57; rl_pod_nearest_A becomes rl_pod_nearest_B at reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan), in the form of proofs/reac-pw/fuzz_rate/lib/AU/RtPgNearB.v at 7e722b95884: the walk lib/AU/RPgNearW.v, the lift lib/AU/RPgNear.v, the image lib/AU/Img0.v and the addresses of lib/AU/RPgNearImg.v; the five soft-float callee contracts the walk takes at image B's symbol map are the instances of lib/CJ/RL/I/InstB.v (image A's were those of InstA.v), so the Section hypotheses are image A's. *)
(* pod_nearest(f, out) of reac-pw/fuzz_role's ASan image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0), 0x82eb4, proved against lib/A/RPgCSpec.v's
   rl_pod_nearest_specX: the walk (lib/AU/RPgNearW.v pod_nearest_B_holds, the machine-level contract
   lib/AU/RPgNearC.v pod_nearest_B_contract from the binary128 value facts, closed by lib/Prog/NearSFClose.v
   near_sf_facts_ok, and the soft-float callees' CJ contracts at image B, lib/CJ/RL/I/InstB.v, taken at
   RPgNearImg.N_img, which has IImgB.N_img's keys and values) composed with the lift (lib/AU/RPgNear.v
   rl_pod_nearest_B_of). Its Section hypotheses are those of the lift: the meter's laws MTL, the runtime's AR laws
   LAWS, and the two cells of the runtime's symbol record the code reads, the .got slot (HGOT) and the
   shadow-offset cell (HSC). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YK11 YK14 YK0s YK15 YK18 YK0i YK1b YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgNearImg RPgNearC RPgNearW RPgNear.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.I Require InstB.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require NearSFClose.
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HGOT : as_got_shadow B = RPgNearImg.B_GOT_SHADOW.
Hypothesis HSC : as_shadow_cell B = RPgNearImg.B_SHADOW_CELL.

Theorem rl_pod_nearest_B : rl_pod_nearest_specX rsegs B MT RPgNearImg.B_POD_NEAREST.
Proof using MTL LAWS HGOT HSC.
exact (RPgNear.rl_pod_nearest_B_of B MT MTL LAWS HGOT HSC
  (RPgNearW.pod_nearest_B_holds NearSFClose.near_sf_facts_ok
     InstB.N_extendsftf2_contract InstB.N_letf2_contract InstB.N_floatditf_contract
     InstB.N_subtf3_contract InstB.N_getf2_contract)).
Qed.
End d.
End b.

Check rl_pod_nearest_B.
Print Assumptions rl_pod_nearest_B.
About rl_pod_nearest_B.
