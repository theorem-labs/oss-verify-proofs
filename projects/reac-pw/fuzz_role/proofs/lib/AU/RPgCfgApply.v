(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgSlots.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632 for fuzz_qdisc's image A) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_cfg_apply_state 0x82ed4 against lib/A/RPgCSpec.v's rl_cfg_apply_state_specX on the concrete image lib/A/Img0.v rsegs, with the plumbing of lib/A/RPgCfgChanges.v; the plain walk it replaces is lib/Prog/reac_role_cfg_apply_state.v (a split on the beq). The leaf's post is RPgCSpec's rl_post (the float state fx kept, no extra bytes E); qdisc's region of the divisor constant, its arithmetic lemmas and its three branches are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCfgApply.v at 8063f9199d5; derived by derive_y.py (frozen b7b132fb12a7) for reac-pw/fuzz_role's asan-ubsan image (fuzz_role.asan-ubsan): modules lib.A.Img0 / RPgCfgChanges -> lib.AU.Img0 / RPgCfgChanges (lib/A/RPgBase.v and RPgCSpec.v stay shared), the addresses moved to that image (the two strings by their bytes), the top rl_cfg_apply_state_A -> rl_cfg_apply_state_B; the comments below restated by hand at that image. The Modified-by lines above describe how lib/A/RPgCfgApply.v was made and quote that file's asan-image values. *)
(* reac_role_cfg_apply_state, 0x83114, 28 bytes, 7 instructions (fuzz_role.asan-ubsan, unstripped sha256
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a; the pinned b255d4935da5 has the same bytes):
     0x83114 beq a0,a1,0x83124;
     0x83118 auipc a0,0xfff9e; 0x8311c addi a0,a0,0x468 (a0 = 0x21580, "role_reestablish_pending"); 0x83120 ret;
     0x83124 auipc a0,0xfff9e; 0x83128 addi a0,a0,0x49c (a0 = 0x215c0, "applied"); 0x8312c ret.
   A pure leaf: no sp move, no store, no load, no shadow check; the auipc / addi pairs only form the two addresses.
   The engine stops at the beq at once; it is split and its condition turned into (cur =? req). Each side runs to
   its `ret` with a0 the string's address. No region, so no byte is written and the post's memory clause holds at
   every address. The same 28 bytes are the asan image's 0x82ed4 except the two addi immediates (there 0x668 /
   0x69c, to 0x21540 / 0x21580); the strings' bytes, "role_reestablish_pending" and "applied" with the NUL, are
   equal in the two images. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Theorem rl_cfg_apply_state_B : rl_cfg_apply_state_specX rsegs B MT A_CFG_APPLY A_STR_APPLIED A_STR_PENDING.
Proof using MTL LAWS.
unfold rl_cfg_apply_state_specX, rl_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cur req
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 Hcur H11 Hreq.
pose proof cfg_wx as Hwx. pose proof cfg_segs_low as Hsegs.
pose proof (cfg_entry A_CFG_APPLY W regs memc ltac:(unfold A_CFG_APPLY; lia)) as HS.
remember (Ereg regs rt_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs rt_extra) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 req) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
clear HE.
assert (SHOK : sh_ok rsegs RTBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
by (intros; reflexivity).
unfold cfg_at. change (w64 A_CFG_APPLY) with (Z_to_bv 64 A_CFG_APPLY).
(* 0x83114 beq a0,a1: the engine stops at it at once *)
cfg_branch Hb.
- (* TAKEN (cur = req): 0x83124 auipc / 0x83128 addi form 0x215c0 ("applied"); stop at 0x8312c ret *)
rewrite branch_eq_U, (U_atom E 10 cur E10 Hcur), (U_atom E 11 req E11 Hreq) in Hb.
cfg_run awr_ok_tac. cfg_keep cfg_kwr_ro.
cfg_leaf ltac:(intros a Ha _ _; exact (KE a Ha (fun x => x)))
ltac:(rewrite Hb; first [reflexivity | vm_compute; reflexivity]).
- (* not taken (cur <> req): 0x83118 auipc / 0x8311c addi form 0x21580 ("role_reestablish_pending"); stop at
     0x83120 ret *)
rewrite branch_eq_U, (U_atom E 10 cur E10 Hcur), (U_atom E 11 req E11 Hreq) in Hb.
cfg_run awr_ok_tac. cfg_keep cfg_kwr_ro.
cfg_leaf ltac:(intros a Ha _ _; exact (KE a Ha (fun x => x)))
ltac:(rewrite Hb; first [reflexivity | vm_compute; reflexivity]).
Qed.
End d.
End b.
