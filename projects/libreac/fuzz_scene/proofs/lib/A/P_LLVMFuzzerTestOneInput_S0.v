(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S0 of the ASan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput
   (fuzz_scene.asan): the entry 0x82878 .. the cut C1 0x82b78 of lib/A/P_LLVMFuzzerTestOneInput_seg.v.  The
   statement `seg_S0_stmt` is a Theorem Labs lane's, PASSED and unchanged; this file only proves it (`scene_seg_S0`). *)

(*   The walk, on the position-abstract kit (lib/A/Prog/{PaRun,PaShadow,ScenePaLib,SceneFrame,SceneACj*}):
   - `s0_entry`: the entry state from afn_pre (the GOT words of the shadow base and of the use-after-return flag,
     and the flag cell, whose value 1 is al_const's -- ENTRY-REVIEW.md R4: the flag is read, never assumed);
   - the prologue and the 13-word save area 0x82878-0x828b8; sp1 = (sp - 224) & -32 becomes atom 60;
   - the GOT reads, the flag test 0x828e0 (decided: flag = 1) and __asan_stack_malloc_8(9408) at 0x828ec through
     a Theorem Labs lane's `aj_stack_malloc_sz_at` (lib/A/J_StackSzPf.v) at class 8; the real-stack arm 0x82904-0x82924 is
     dead because `bnez s7` 0x82900 is decided by the fake frame's range (F >= 4096);
   - a Theorem Labs lane's `frame_setup SEGS VAL B 8 9408` (lib/A/P_check_step_frame.v) for the frame and frame-shadow regions;
   - the frame header and the 28 inline shadow stores 0x82928-0x829dc, __asan_set_shadow_f8(shF + 0x1c, 1113) at
     0x829e0 through `aj_set_shadow_at` (lib/A/J_StackSzPf.v), the 35 stores 0x829ec-0x82a74;
   - the early return `bnez a1` 0x82a78 (a1 = n >> 26) refuted from n < 2 ^ 26;
   - the input parse 0x82a7c-0x82b28 / 0x830c4-0x83140, the mac unpoison 0x82b1c and the 6-turn mac loop
     0x82b2c-0x82b60, in twelve cases n = 0 .. 10 (s5 pinned to the literal) and n >= 11;
   - `s0_c1`: the cut C1 assembled once from what each case establishes at 0x82b78.
   ASan report branches: every shadow check of the walk (0x82a90, 0x82ac4, 0x830d0, 0x83104, 0x83130 in the parse,
   0x82b3c in the mac loop; their slow paths and __asan_report_load1 calls are 0x8314c-0x83198 and 0x82b68-0x82b74)
   is a check of the token executor, which takes the not-taken edge and leaves a `range_addressable` obligation;
   each obligation is discharged by `obl_of_block` on the input block (tactic s0_obl), so no report branch is
   taken -- none is stepped over.

   Premises (Section e), each the hypothesis of the same name in lib/A/P_LLVMFuzzerTestOneInput.v, with its owner:
   TL, TLF, ML, FFL (a Theorem Labs lane, the glue); stack_malloc_8_sz (a Theorem Labs lane); ASHF8 (two Theorem Labs lanes).  The
   walk constants WK are bound by HWRLO / HWRHI (a Theorem Labs lane's text, verbatim) and by HWENT / HWEMP / HWSTK, which
   are the statement's HA_LLVMF, HA_EMPTY and HSTK in terms of WK; the composition discharges all five.  AR_laws
   is AR_laws_ok and stack_malloc_progressP is a field of ML (ENTRY-REVIEW.md R4); the two journal steps are
   a Theorem Labs lane's proved lemmas (a working branch d1cfd1a8204, lib/A/J_StackSzPf.v).

   SPLIT (a Theorem Labs lane, 2026-10-29), for build speed; the statement and the Section are this file's as before.
   The proof is in P_LLVMFuzzerTestOneInput_S0_kit.v (lines 1-608 of the one-file version: the leaves, the
   Ltacs, s0_entry, s0_c1) and in P_LLVMFuzzerTestOneInput_S0_n0 .. _n11.v (the walk and one input-length case
   each), which compile in parallel; `s0_cases` (the kit) assembles them. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00 YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz StackFreeDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import
PaRun PaShadow PaStep PaJournal SceneSyms SceneList SceneAddr SceneCode ScenePa ScenePaLib
SceneBase SceneFrame SceneRo SceneImg YC1g YC1h YC45 YC85 YC88 YC4b YC81 YC1i ACbf SceneACja SceneACjr ACj1.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import SceneAsanTop.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx J_StackSz P_check_step_frame P_LLVMFuzzerTestOneInput_seg.
(* A Theorem Labs lane (at d1cfd1a8204): the two caller-side journal steps J_StackSz.v states, PROVED. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import J_StackSzPf.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Rt Require Import StackMalloc8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_S0_kit
P_LLVMFuzzerTestOneInput_S0_n0 P_LLVMFuzzerTestOneInput_S0_n1 P_LLVMFuzzerTestOneInput_S0_n2 P_LLVMFuzzerTestOneInput_S0_n3 P_LLVMFuzzerTestOneInput_S0_n4 P_LLVMFuzzerTestOneInput_S0_n5 P_LLVMFuzzerTestOneInput_S0_n6 P_LLVMFuzzerTestOneInput_S0_n7 P_LLVMFuzzerTestOneInput_S0_n8 P_LLVMFuzzerTestOneInput_S0_n9 P_LLVMFuzzerTestOneInput_S0_n10 P_LLVMFuzzerTestOneInput_S0_n11.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* gate 6h / the sink widening (a Theorem Labs lane, 2026-10-29 01:57Z): the sink head is a Section variable whose type is written
   fully qualified (lib/U/Reusable/YI16.v has the same short name), passed BY NAME to every term that takes it.  The
   composition instantiates it with scene's own head (lib/A/P_LLVMFuzzerTestOneInput.v:150-151, ofl_head 0x5f6e90). *)
Context (SK : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head). #[local] Existing Instance SK.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).

Section e.
Variable B : asyms.
Hypothesis TL : PALib (L := scene_listing) (PI := PI_scene) B.
Hypothesis TLF : PALibF (L := scene_listing) (PI := PI_scene) B.

(* ---- the runtime contracts and framework laws this segment needs.  Each is the hypothesis of the same
   name in lib/A/P_LLVMFuzzerTestOneInput.v, with the owner that file names. ---- *)
(* A Theorem Labs lane: the glue's instances. *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP SEGS B.
(* A Theorem Labs lane (968ea35e8f5 proves it; this lane TAKES it). *)
Hypothesis stack_malloc_8_sz : astack_malloc_sz_realizes SEGS B PC_STACK_MALLOC_8 CID8.
(* Two Theorem Labs lanes: __asan_set_shadow_f8. *)
Hypothesis ASHF8 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_f8) 0xf8.

(* ---- the walk's constants.  The two read-only-window bindings are a Theorem Labs lane's text (03:35Z ruling), verbatim
   in every segment lane; the composition discharges all five from the record it builds. ---- *)
Variable WK : swalk.
Hypothesis HWRLO : sw_rlo WK = pa_relro_lo.
Hypothesis HWRHI : sw_rhi WK = pa_relro_hi.
(* S0 starts at the contract's entry, reads the n = 0 argument and calls the class-8 side-stack allocator:
   P_LLVMFuzzerTestOneInput.v's HA_LLVMF, HA_EMPTY (0x5d5e60) and HSTK (LLVMF_SPDROP + ASTACK <= LLVMF_STK) in terms
   of WK. *)
Hypothesis HWENT : sw_entry WK = BASE + AF_LLVMFuzzerTestOneInput.
Hypothesis HWEMP : 4096 <= sw_empty WK <= 140737479966720.
Hypothesis HWSTK : 240 + ASTACK <= sw_stk WK.

Theorem scene_seg_S0 : @seg_S0_stmt fx rc SK SEGS B ameter_triv WK scene_geom_asan.
Proof.
apply s0_cases;
[ eapply s0_case_n0
| eapply s0_case_n1
| eapply s0_case_n2
| eapply s0_case_n3
| eapply s0_case_n4
| eapply s0_case_n5
| eapply s0_case_n6
| eapply s0_case_n7
| eapply s0_case_n8
| eapply s0_case_n9
| eapply s0_case_n10
| eapply s0_case_n11
];
eassumption.
Qed.
End e.
End b.
