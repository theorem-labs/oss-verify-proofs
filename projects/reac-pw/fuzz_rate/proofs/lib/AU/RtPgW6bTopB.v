(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 174 of its 211 lines of code are new or changed and 253 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aTail.v at e261793226b4; ported to reac-pw/fuzz_rate's image A: module paths changed (images.Asan for lib/A/Img0, RtPgBase / RtPgCSpec / RtPgSteps / RtPgW6aBase for the RPg files, RtPgSteps' rts_wx / rts_segs_low / same_io_wvb / regs_kept_of_st_ok / rts_post for RPgCfgChanges' and RPgSteps' facts and w6_post); rate's pcs and the cell [R+0x138] for [R+0xf0]; rate's tail stores in.n to s8 (`mv s8,a1`) instead of the cell [R+0xf8], so the s1-based region is read-only, the post has three stored values and s8 in place of s9; the frame facts use the kit's AR_laws_ok instead of a LAWS hypothesis. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aTail.v, with its module paths and module names changed; 405 of its 470 lines of code are new or changed and 146 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bC4.v; 1003 of its 1068 lines of code are new or changed and 405 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aC2h.v at 616508a91de2 (its helpers
   c2_all256, c2_notin, c2_nz, c2_regv and c2_kio, renamed c5_*; the engine usage of its entry states and runs) and
   proofs/reac-pw/fuzz_role/lib/A/RPgW6cTail.v at 527e8d2097d9 (the memcpy call into e.body and the e-byte
   assembly), for reac-pw/fuzz_rate's image A and ent_build's case 5; everything else is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bC5.v, with its module paths and module names changed; 13 of its 27 lines of code are new or changed and 1054 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bTop.v, with its module paths and module names changed; 8 of its 29 lines of code are new or changed and 6 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bTop.v at 32f84792c2a6; for image B
   (fuzz_rate.asan-ubsan): the piece is RtPgSegB.rsb_piece_W6b_stmt, closed from lib/AU/RtPgW6bB.v's chain and image
   B's four case lemmas; the memcpy and strlen hypotheses are at image B's entries 0x518b8 and 0x421ec. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the walk piece
   rsb_piece_W6b_stmt of lib/AU/RtPgSegB.v (ent_build's cases 1, 4, 5 and 9 inside LLVMFuzzerTestOneInput 0x8076c,
   from the case entries 0x81900, 0x81774, 0x81968, 0x81a94 to the join J 0x820dc), closed: lib/AU/RtPgW6bB.v's chain
   w6bb_piece_of applied to the four case lemmas w6bb_c1 (RtPgW6bC1B.v), w6bb_c4 (RtPgW6bC4B.v), w6bb_c5
   (RtPgW6bC5B.v) and w6bb_c9 (RtPgW6bC9B.v). Proves no function (kind: segment lemma).
   Its hypotheses are the runtime's: the meter's laws, __asan_memcpy at 0x518b8 (the kernel's aintrin_realizes OCpy)
   and the strlen wrapper at 0x421ec (astrlen_realizes, the image-parametric definition of lib/A/Rt/StrlenDef.v; no
   image-A constant of that file is used); the assembly discharges them. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgSegB RtPgW6bBaseB RtPgW6bB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW6bC1B RtPgW6bC4B RtPgW6bC5B RtPgW6bC9B.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require Import StrlenDef.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.

(* image B's loaded segments, as RtPgStepsB names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
(* __asan_memcpy at 0x518b8 and the strlen wrapper's trampoline at 0x421ec *)
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6BB_MEMCPY.
Hypothesis ASTRLEN : astrlen_realizes rsegs B W6BB_STRLEN.

Theorem w6bb_piece : rsb_piece_W6b_stmt rsegs B MT.
Proof.
exact (w6bb_piece_of B MT MTL (w6bb_c1 B MT MTL AMEMCPY ASTRLEN) (w6bb_c4 B MT MTL) (w6bb_c5 B MT MTL AMEMCPY)
  (w6bb_c9 B MT MTL AMEMCPY)).
Qed.
End t.

Print Assumptions w6bb_piece.
