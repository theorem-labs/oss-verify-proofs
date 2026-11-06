(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACey.v lines 190-246 (rfc_post, trfc_specX) in the Section form of lib/YC7y.v lines 4-18, 26-32 and 69-113 at c8557374ad2e to libreac/fuzz_knock: rfc_post -> kn_post_init / kn_post_heard / kn_post_step, trfc_specX -> tknock_init_specX / tknock_heard_specX / tknock_step_specX, tfibsegs -> the Section variable segs, A_read_frameconfig -> the parameter a, LAY_FrameConfig -> LAY_Knock, the parse_frameN result -> knock_step_f (reac_knock_step_c.v lines 11-18 restated over Z), the 32-byte destination dst -> the 40-byte struct kp in the caller's frame, written through awr_byte's in_frames case by In (cid, pos) own for any frame class cid (knock's harness frame is class 1), its addressability carried by afobj (APgBase.v) and kp <> 0; the stack struct st, the heap blocks Bb, the CTX_read_frameconfig premise and the malloc budget are dropped, because knock's three callees allocate nothing and call only the memset intrinsic; TRFC_STK = 112 + ASTACK -> T_init_STK = 48 + ESTACK (addi sp,sp,-48 at 0x7f44c), T_heard_STK = 16 (addi sp,sp,-16 at 0x7f4e8), T_step_STK = 16 (addi sp,sp,-16 at 0x7f570); EV_RFC = 6 -> EV_init = EV_heard = EV_step = 0; RFC_COST MT N -> 0 in mo_le; the file states no image-end or RELRO address. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgCSpec.v at origin/ossv/recipes 6ebe35ba632 (the
   Section form of its lines 32-164) and proofs/libreac/fuzz_grant/lib/A/ACfn.v at origin/ossv/recipes 2638f9235e2
   (lines 50-61 and 87-116: tfib_lib_post_x, tfib_lib_pre_xf, tfib_lib_contract_xf) for reac-pw/fuzz_role, image A and
   image B: knock's three callee contracts become the contracts of role's ten program callees, with one post shape
   rl_post that leaves the float state open (role's parse and pod_nearest change float registers); the harness
   contract is grant's exists-fx' form over abstract segs, sink, read-only range and harness constants; the two
   middle segments of LLVMFuzzerTestOneInput are stated over role's shared Pod model. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCSpec.v at 0de5d668c87e for reac-pw/fuzz_rate
   (image A and image B): module paths changed; the prefix rl_ becomes rt_ (rl_post -> rt_cpost, rl_pre -> rt_cpre,
   rl_himg -> rt_himg, rl_seg_post / rl_seg_pre -> rt_seg_post / rt_seg_pre, rl_lib_x -> rt_lib_x); role's ten callee
   contracts are replaced by rate's fifteen, stated over rate's shared Pod model (Pod/Rate.v, RateCfg.v, RateCsv.v,
   Nearest.v); two of them take a side-stack frame of their own (a class parameter) and let runtime-owned bytes change;
   role's two middle segments become rate's three (rate_build_contract, rate_check_contract, rate_csv_contract), the
   image record gains the cuts, live lists, write ranges and tables of the third block and the third segment; the
   lessons role's walks found in its texts (rom_view; the input's amem_range, shadow_hull_vis, 0 < src and
   src + left <= 2^63; the fresh-block premises) are kept from the start. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/DiscoAsanT.v at origin/ossv/recipes
   09c6822d886; its H_RO_stmt (ro_unowned of the read ranges, globs_marked, img_shadow_vis) becomes rt_img_facts over
   the image record's lists (rt_ro_ranges, new) and range; rt_img_static and rt_static_of_img_facts are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCSpec.v, with its module paths and module names changed; 14 of its 33 lines of code are new or changed and 538 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgNearA.v at 92636bfca57b; the module paths name reac-pw/fuzz_rate, rl_pod_nearest_A becomes rt_pod_nearest_A against lib/A/RtPgCSpec.v's rt_pod_nearest_specX, and the image is reac-pw/fuzz_rate's image A (fuzz_rate.asan). *)
(* pod_nearest(f, out) of reac-pw/fuzz_rate's ASan image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a), 0x83dc0, proved against lib/A/RtPgCSpec.v's
   rt_pod_nearest_specX: the walk (lib/A/RtPgNearW.v pod_nearest_A_holds, the machine-level contract
   lib/A/RtPgNearC.v pod_nearest_A_contract from the binary128 value facts, closed by lib/Prog/NearSFClose.v
   near_sf_facts_ok, and the soft-float callees' CJ contracts at image A, lib/CJ/RL/I/InstA.v) composed with the
   lift (lib/A/RtPgNear.v rt_pod_nearest_A_of). Its Section hypotheses are those of the lift: the meter's laws MTL,
   the runtime's AR laws LAWS, and the two cells of the runtime's symbol record the code reads, the .got slot
   (HGOT) and the shadow-offset cell (HSC). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YK11 YK14 YK0s YK15 YK18 YK0i YK1b YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import Img0 RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgNearC RtPgNearW RtPgNear.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require NearSFClose.
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HGOT : as_got_shadow B = RtPgNearC.A_GOT_SHADOW.
Hypothesis HSC : as_shadow_cell B = RtPgNearC.A_SHADOW_CELL.

Theorem rt_pod_nearest_A : rt_pod_nearest_specX rsegs B MT RtPgNearC.A_POD_NEAREST.
Proof using MTL LAWS HGOT HSC.
exact (RtPgNear.rt_pod_nearest_A_of B MT MTL LAWS HGOT HSC
  (RtPgNearW.pod_nearest_A_holds NearSFClose.near_sf_facts_ok)).
Qed.
End d.
End b.

Check rt_pod_nearest_A.
Print Assumptions rt_pod_nearest_A.
