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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgE01B.v, with its module paths and module names changed; 13 of its 45 lines of code are new or changed and 20 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's parts (lib/AU/RtPgE01*B.v), the class-4 frame law and image B's GOT cells,
   malloc trampoline and frame bound in the Section hypotheses. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgE01B.v at 48db065d2b9c; for reac-pw/fuzz_role
   image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, role B's parts (lib/AU/RPgE01E.v, RPgE01P.v,
   RPgE01H.v, RPgE01M.v), image B's GOT cells 0x9aad0 / 0xa3678 / 0x9ab28 / 0xa3680, frame entry 0x3cc74, malloc
   trampoline 0x524c0 and frame bound 0x210 in the Section hypotheses; the theorem named e01_ok as image A's; the
   fake-stack progress law derived from the model laws (no hypothesis), the static law and the read-only range
   dropped (role's one header byte reads no constant). *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): SEGMENT S_E01 of the walk
   of LLVMFuzzerTestOneInput (ENTRY 0x80020 -> C1 0x802c4), lib/AU/RPgHarn.v S_E01, from its four parts
   (lib/AU/RPgE01D.v e01b_chain): ENT (RPgE01E: the prologue, the GOT loads, __asan_stack_malloc_4(704)), PRO
   (RPgE01P: the frame's header, its 88 shadow bytes, the size test), HDR (RPgE01H: the one header read in its
   input-length arms, after its pointer-overflow test and behind its instrumented check) and CALL (RPgE01M:
   malloc(19744) and the cut C1). Proves no function (kind: segment lemma).

   THE SECTION HYPOTHESES (each is a fact the closing discharges; none is an axiom): the allocator's laws and its
   malloc operation at the image's trampoline 0x524c0 with the call site's trace, the side stack's class-4 frame law
   at 0x3cc74 (lib/AU/Rt/StackMalloc4.v stack_malloc4_contract), the four runtime cells the GOT names (0x9aad0 ->
   0xa3678 the shadow offset, 0x9ab28 -> 0xa3680 the option byte), the harness's stack / event / live budgets and
   the empty input's address (0 < A_EMPTY < kLowMemEnd). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgHarn RPgE01D.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgE01E RPgE01P RPgE01H RPgE01M.
Import ListNotations.
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the frame bound: the real frame (R - S is -0x200 or -0x210) and the allocator's stack below it *)
Hypothesis HSTK : 0x210 + ASTACK <= LLVMF_STK.
(* the side stack's class-4 frame law (lib/AU/Rt/StackMalloc4.v stack_malloc4_contract) *)
Hypothesis ASM4 : astack_malloc_realizes rsegs B 4.
Hypothesis ML : model_laws (as_universe B).
Hypothesis HAPI : api_env rsegs B.
(* the symbol record's cells and code entries *)
Hypothesis HGOT : as_got_shadow B = 0x9aad0.
Hypothesis HSC : as_shadow_cell B = 0xa3678.
Hypothesis HGU : as_got_uar B = 0x9ab28.
Hypothesis HUC : as_uar_cell B = 0xa3680.
Hypothesis HBsm : pc_stack_malloc (as_code B) 4 = 0x3cc74.
(* the empty input's address (the harness's caller passes it when n = 0) *)
Hypothesis HAE : 0 < A_EMPTY < kLowMemEnd.
(* the malloc(pp) call *)
Hypothesis AMALLOC : amalloc_realizes rsegs B.
Hypothesis HBmalloc : pc_wrap_malloc (as_code B) = 0x524c0.
Hypothesis HTRACE : e01b_trace_stmt B RA_LLVMF.
Hypothesis HEV : 1 <= EV_LIB.
Hypothesis HLIVE : Layout.PP_SIZE <= LIVE_LIB.

Theorem e01_ok : S_E01 rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
apply e01b_chain;
[ eapply RPgE01E.e01b_ent_ok | eapply RPgE01P.e01b_pro_ok | eapply RPgE01H.e01b_hdr_ok
| eapply RPgE01M.e01b_call_ok ];
eassumption.
Qed.
End b.
