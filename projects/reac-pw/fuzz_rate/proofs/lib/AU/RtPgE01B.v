(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88 (the register readers rx_reg_atom / rx_reg_lit and the tactics rx_atom / rx_lit, kept as e01e_reg_atom / e01e_reg_lit / e01e_atom / e01e_lit), proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxEntry.v at 09c6822d8861 (eb_land_m32 and eb_denot_and_m32, kept as e01e_land_m32 and e01e_denot_and_m32; the plan of gb_entry_a) and proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxFrame.v at 09c6822d8861 (val_mem_of_rd32, kept as e01e_val_mem_rd32) [Apache-2.0 OR MIT, used under Apache-2.0]; module paths changed to reac_pw.fuzz_rate, the walk of part ENT of reac-pw/fuzz_rate's segment S_E01 below is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01E.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's code of part ENT (the frame 0x220, the GOT words 0x9c1c8 / 0x9c170 and their
   cells 0xa4f40 / 0xa4f38, s2 = p, s4 = the shadow offset), the class-4 call __asan_stack_malloc_4 (its flag pointer
   word at F + 0x3f8), the harness records of lib/AU (rhb_ / rsb_ / rtsb_ names), the names e01e_ renamed e01eb_. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgE01EB.v, with its module names changed; 25 of its 52 lines of code are new or changed and 258 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's parts (lib/AU/RtPgE01*B.v), the class-4 frame law and image B's GOT cells,
   malloc trampoline and frame bound in the Section hypotheses. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): SEGMENT S_E01 of the walk
   of LLVMFuzzerTestOneInput (ENTRY 0x8076c -> C1 0x80ae4), lib/AU/RtPgSegB.v S_E01, from its four parts
   (lib/AU/RtPgE01DB.v e01b_chain): ENT (RtPgE01EB: the prologue, the GOT loads, __asan_stack_malloc_4(704)), PRO
   (RtPgE01PB: the frame's header, its 88 shadow bytes, the size test), HDR (RtPgE01HB: the seven header reads in
   their eight input-length arms, each after its pointer-overflow test) and CALL (RtPgE01MB: malloc(19744) and the cut
   C1). Proves no function (kind: segment lemma).

   THE SECTION HYPOTHESES (each is a fact the closing discharges; none is an axiom): the allocator's laws and its
   malloc operation at the image's trampoline 0x52c0c with the call site's trace, the side stack's class-4 frame law
   at 0x3d300 (lib/AU/Rt/StackMalloc4.v stack_malloc4_contract) and the fake-stack progress law, the four runtime
   cells the GOT names (0x9c170 -> 0xa4f38 the shadow offset, 0x9c1c8 -> 0xa4f40 the option byte), the harness's
   stack / event / live budgets, the empty input's address (0 < A_EMPTY < kLowMemEnd), the static law of the
   read-only data (RtPgSegB rhb_static_law) and the read-only range lying in the image. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB RtPgE01DB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgE01EB RtPgE01PB RtPgE01HB RtPgE01MB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Local Open Scope Z_scope.
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HAPI : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM4 : astack_malloc_realizes rsegs B 4.
Hypothesis HBsm4 : pc_stack_malloc (as_code B) 4 = E01B_SM4.
Hypothesis AMALLOC : amalloc_realizes rsegs B.
Hypothesis HBmalloc : pc_wrap_malloc (as_code B) = E01B_MALLOC.
Hypothesis HTRACE : e01b_trace_stmt B RA_LLVMF.
Hypothesis HGOT : as_got_shadow B = 0x9c170.
Hypothesis HSC : as_shadow_cell B = 0xa4f38.
Hypothesis HGOTU : as_got_uar B = 0x9c1c8.
Hypothesis HUAR : as_uar_cell B = 0xa4f40.
Hypothesis HSTK : 0x230 + ASTACK <= LLVMF_STK.
Hypothesis HEV : 1 <= EV_LIB.
Hypothesis HLIVE : Layout.PP_SIZE <= LIVE_LIB.
Hypothesis HEMPTY : 0 < A_EMPTY < kLowMemEnd.
Hypothesis HSTATIC : rhb_static_law rsegs B RLO RHI.
Hypothesis HRELRO : forall a, RLO <= a < RHI -> in_img rsegs a.

Theorem rtb_S_E01 : S_E01 rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
apply e01b_chain;
[ eapply RtPgE01EB.e01b_ent_ok | eapply RtPgE01PB.e01b_pro_ok | eapply RtPgE01HB.e01b_hdr_ok
| eapply RtPgE01MB.e01b_call_ok ];
eassumption.
Qed.
End b.

Print Assumptions rtb_S_E01.
About rtb_S_E01.
