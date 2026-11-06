(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (ASAN-UBSAN). The CLOSED class-8 stack-free
   leaf. It composes proofs that already exist and walks no code:
   - stack_free_8_closed: a Theorem Labs lane's sce_stack_free_8_B (lib/AU/Rt/StackFree8Tbl.v, the tables of __asan_stack_free_8 at
     PC_STACK_FREE_8 0x3f5b4, over the shared walk lib/Reusable/StackFree8.v) with its three Section hypotheses as
     premises, with the same types and in the same order: AR_laws, and the two leaf summaries at this image's
     PC_MEM_TO_SHADOW 0x3f604 and PC_POISON_SHADOW 0x55be4 (a Theorem Labs lane's lib/AU/Rt/StackMalloc8Tbl.v).
   - stack_free_8_discharged: the same conclusion with the two leaf summaries discharged by
     lib/AU/RT_mem_to_shadow.v's scene_mem_to_shadow (at M2S_ENTRY = 0x3f604) and lib/AU/RT_poison_shadow.v's
     scene_poison_shadow (at PS_ENTRY = 0x55be4). Both take AR_laws and TfibSyms B, so its premises are AR_laws and
     TfibSyms: facts about B's certificate.
   The conclusion is a Theorem Labs lane's: `astack_free_realizes tfibsegs B PC_STACK_FREE_8 CID8`. The glue states this row as
   (a working branch c1b5da89d39 lib/AU/G_Close.v:182-183)
   `StackFreeDef.astack_free_realizes SEGS B (SIGMA SS___asan_stack_free_8) 8`; the two are equal by conversion only:
   SEGS = pa_segs PI_scene = scene_segs = AsanUbsan.M.loaded_segments = tfibsegs (AU/YB1v.v:12); SIGMA = pa_sigma
   PI_scene = scene_sigma, and scene_sigma SS___asan_stack_free_8 = 0x3f5b4 = PC_STACK_FREE_8
   (a working branch 82cb6676c06 lib/AU/Prog/SceneImg.v:61, SceneAddr.v:32); CID8 = 8
   (StackMalloc8Tbl.v:66). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05 StackFreeDef AsStackLeaf.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB1v YF0m.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Rt Require Import StackMalloc8Tbl StackFree8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require RT_mem_to_shadow RT_poison_shadow.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem stack_free_8_closed : forall (B : asyms),
AR_laws tfibsegs B ->
mem_to_shadow_realizes tfibsegs B PC_MEM_TO_SHADOW ->
poison_shadow_realizes tfibsegs B PC_POISON_SHADOW ->
astack_free_realizes tfibsegs B PC_STACK_FREE_8 CID8.
Proof.
intros B LAWS MTS_SUM PS_SUM.
exact (StackFree8Tbl.sce_stack_free_8_B B LAWS MTS_SUM PS_SUM).
Qed.

Theorem stack_free_8_discharged : forall (B : asyms),
AR_laws tfibsegs B ->
TfibSyms B ->
astack_free_realizes tfibsegs B PC_STACK_FREE_8 CID8.
Proof.
intros B LAWS TB.
apply stack_free_8_closed.
- exact LAWS.
- exact (RT_mem_to_shadow.scene_mem_to_shadow B LAWS TB).
- exact (RT_poison_shadow.scene_poison_shadow B LAWS TB).
Qed.

End d.
