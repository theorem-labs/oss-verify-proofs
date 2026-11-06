(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88 (the register readers rx_reg_atom / rx_reg_lit and the tactics rx_atom / rx_lit, kept as e01e_reg_atom / e01e_reg_lit / e01e_atom / e01e_lit), proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxEntry.v at 09c6822d8861 (eb_land_m32 and eb_denot_and_m32, kept as e01e_land_m32 and e01e_denot_and_m32; the plan of gb_entry_a) and proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxFrame.v at 09c6822d8861 (val_mem_of_rd32, kept as e01e_val_mem_rd32) [Apache-2.0 OR MIT, used under Apache-2.0]; module paths changed to reac_pw.fuzz_rate, the walk of part ENT of reac-pw/fuzz_rate's segment S_E01 below is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgE01E.v, with its module names changed; 22 of its 48 lines of code are new or changed and 254 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): SEGMENT S_E01 of the walk
   of LLVMFuzzerTestOneInput (ENTRY 0x80714 -> C1 0x809e0), lib/A/RtPgSeg.v S_E01, from its four parts
   (lib/A/RtPgE01D.v e01_chain): ENT (RtPgE01E: the prologue, the GOT loads, __asan_stack_malloc_3(448)), PRO
   (RtPgE01P: the frame's header, its 56 shadow bytes, the size test), HDR (RtPgE01H: the seven header reads in their
   eight input-length arms) and CALL (RtPgE01M: malloc(19744) and the cut C1). Proves no function (kind: segment
   lemma).

   THE SECTION HYPOTHESES (each is a fact the closing discharges; none is an axiom): the allocator's laws and its
   malloc operation at the image's trampoline 0x52bb4 with the call site's trace, the side stack's class-3 frame law
   at 0x3d2c8 and the fake-stack progress law, the four runtime cells the GOT names (0x9be70 -> 0xa4c38 the shadow
   offset, 0x9bec8 -> 0xa4c40 the option byte), the harness's stack / event / live budgets, the empty input's
   address (0 < A_EMPTY < kLowMemEnd), the static law of the read-only data (RtPgSeg rh_static_law) and the
   read-only range lying in the image. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg RtPgE01D.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgE01E RtPgE01P RtPgE01H RtPgE01M.
From OSSVerify.reac_pw.fuzz_rate.images Require Asan.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HAPI : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM3 : astack_malloc_realizes rsegs B 3.
Hypothesis HBsm3 : pc_stack_malloc (as_code B) 3 = E01_SM3.
Hypothesis AMALLOC : amalloc_realizes rsegs B.
Hypothesis HBmalloc : pc_wrap_malloc (as_code B) = E01_MALLOC.
Hypothesis HTRACE : e01_trace_stmt B RA_LLVMF.
Hypothesis HGOT : as_got_shadow B = 0x9be70.
Hypothesis HSC : as_shadow_cell B = 0xa4c38.
Hypothesis HGOTU : as_got_uar B = 0x9bec8.
Hypothesis HUAR : as_uar_cell B = 0xa4c40.
Hypothesis HSTK : 0x1f0 + ASTACK <= LLVMF_STK.
Hypothesis HEV : 1 <= EV_LIB.
Hypothesis HLIVE : Layout.PP_SIZE <= LIVE_LIB.
Hypothesis HEMPTY : 0 < A_EMPTY < kLowMemEnd.
Hypothesis HSTATIC : rh_static_law rsegs B RLO RHI.
Hypothesis HRELRO : forall a, RLO <= a < RHI -> in_img rsegs a.

Theorem rt_S_E01 : S_E01 rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
apply e01_chain;
[ eapply RtPgE01E.e01_ent_ok | eapply RtPgE01P.e01_pro_ok | eapply RtPgE01H.e01_hdr_ok | eapply RtPgE01M.e01_call_ok ];
eassumption.
Qed.
End b.

Print Assumptions rt_S_E01.
About rt_S_E01.
