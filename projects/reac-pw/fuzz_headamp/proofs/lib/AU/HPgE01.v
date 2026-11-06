(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 for reac-pw/fuzz_headamp image A: every address relocated (role image A -> headamp image A); pp in its own env slot (atom 35, the value of the cell R+0xf0: s11 holds the input cursor here), so the entry and resume states, the shadow entry, the alias fact and the len region name atom 35 for role's 27; the cells move by the slot map (R+0xb8 -> R+0xd8, R+0xe0 -> R+0x100, R+0xe8 -> R+0x108) and the index register is a7 (role a6); pa_i_memset_at removed, the call is lib/A/HPgIntrin.v hd_memset_at; kept_run / same_io_wvb from lib/A/HPgPropKit.v / HPgSteps.v; module paths. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgPropIntB.v; 586 of its 649 lines of code are new or changed and 389 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgE01.v at 800a94bc01d1 (the arithmetic, register and save readers, the P1a / P1b entries), proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (field_of_region, st_ok_region_nth) and proofs/reac-pw/fuzz_headamp/lib/A/HPgCalls.v at 0b1fb19172b (hc_frame_call); restated at image B's pcs, frame size 0x220, cells and class-4 call, with the four float saves stepped by YK0o.fp_step_fsd. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgE01P.v; 26 of its 47 lines of code are new or changed and 628 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): segment E01 of the walk of
   LLVMFuzzerTestOneInput (0x80c40), ENTRY 0x80c40 -> C1 0x80fcc (lib/AU/HPgE01D.v hqu_S_E01_stmt at image B's
   segments), from its four proved parts: lib/AU/HPgE01P.v e01u_pro_ok (the prologue and the class-4 frame call),
   lib/AU/HPgE01H.v e01u_hdr_ok (the frame's header, its 116 shadow bytes and the size test), lib/AU/HPgE01B.v
   e01u_body_ok (the two harness bytes and the malloc request), lib/AU/HPgE01M.v e01u_call_ok (the malloc(pp) call),
   chained by lib/AU/HPgE01C.v hqu_E01_chain. Proves no function on its own (kind: segment lemma of
   LLVMFuzzerTestOneInput's walk).

   The Section hypotheses are the callee facts and harness constants the parts take, each of the exact type of the
   file or lane that discharges it:
   - ASM4 (astack_malloc_realizes rsegs B 4): the class-4 frame function's law, image B's port of
     plugin-hostd/fuzz_command lib/A/Rt/RtSM4.v + RtSM4T.v (image A's port: lib/A/Rt/RtSM4.v stack_malloc4_contract);
   - HSM4, HBmalloc, HGOT, HSC, HGU, HUC: image B's symbol record (the class-4 entry 0x3cd2c, malloc's wrapper 0x530e0,
     the two .got words and the two runtime cells the prologue reads; image A's form: lib/A/Rt/RtSM4.v
     stack_malloc4_entry);
   - errno_low, ML, AMALLOC: the kernel's runtime facts at image B (YCbq api_env, model_laws, amalloc_realizes);
   - HTRACE: the allocation trace of the malloc(pp) site (HPgE01D.e01u_trace_stmt);
   - HSTK, HEV, HLIVE, HAE: the harness constants (the entry's stack window covers the 0x220-byte frame, its 16-byte
     alignment slack and the callees' stack; one event and 19744 live bytes of the harness's budget; the empty
     input's address). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSegM HPgE01D HPgE01C.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgE01P HPgE01H HPgE01B HPgE01M.
Import ListNotations.
Local Open Scope Z_scope.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x230 + ASTACK <= LLVMF_STK.
Hypothesis errno_low : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM4 : astack_malloc_realizes rsegs B 4.
Hypothesis HSM4 : pc_stack_malloc (as_code B) 4 = E01U_SM4.
Hypothesis HGOT : as_got_shadow B = E01U_GOT_SH.
Hypothesis HSC : as_shadow_cell B = E01U_SHC.
Hypothesis HGU : as_got_uar B = E01U_GOT_UAR.
Hypothesis HUC : as_uar_cell B = E01U_UAR.
Hypothesis HAE : 0 < A_EMPTY < kLowMemEnd.
Hypothesis AMALLOC : amalloc_realizes rsegs B.
Hypothesis HBmalloc : pc_wrap_malloc (as_code B) = E01U_MALLOC.
Hypothesis HTRACE : e01u_trace_stmt B RA_LLVMF.
Hypothesis HEV : 1 <= EV_LIB.
Hypothesis HLIVE : Layout.PP_SIZE <= LIVE_LIB.

Theorem hqu_E01_ok : hqu_S_E01_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
apply hqu_E01_chain.
- apply HPgE01P.e01u_pro_ok; assumption.
- apply HPgE01H.e01u_hdr_ok; assumption.
- apply HPgE01B.e01u_body_ok; assumption.
- apply HPgE01M.e01u_call_ok; assumption.
Qed.
Print Assumptions hqu_E01_ok.
End p.

Print Assumptions hqu_E01_ok.
