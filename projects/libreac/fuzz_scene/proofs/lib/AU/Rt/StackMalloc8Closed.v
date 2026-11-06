(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (ASAN-UBSAN). The CLOSED class-8 stack-malloc
   leaf. It composes proofs that already exist and walks no code:
   - stack_malloc_8_sz_closed: m8_of_segs (lib/AU/Rt/StackMalloc8Cuts.v) applied to the four segment lemmas
     sm8_segA_holds .. sm8_segD_holds (lib/AU/Rt/StackMalloc8SegA.v .. SegD.v). Its premises are the union of the
     segment lemmas' Section hypotheses, with the same types, in the order of a Theorem Labs lane's ZChk8C check: AR_laws, the two
     certificate fields as_tp / as_tsd, the 21 start-up cells of B's as_const that Seg A reads, and the two leaf
     summaries at this image's PC_MEM_TO_SHADOW 0x3f604 and PC_POISON_SHADOW 0x55be4.
   - stack_malloc_8_sz_discharged: the same conclusion with the two leaf summaries discharged by
     lib/AU/RT_mem_to_shadow.v's scene_mem_to_shadow (at M2S_ENTRY = 0x3f604) and lib/AU/RT_poison_shadow.v's
     scene_poison_shadow (at PS_ENTRY = 0x55be4). Both take AR_laws and TfibSyms B, so its premises are AR_laws,
     TfibSyms, the two fields and the 21 cells: facts about B's certificate.
   The conclusion is the type the consumers take as the Hypothesis stack_malloc_8_sz (StackMalloc8Cuts.v:223-229),
   written as the glue writes it (a working branch c1b5da89d39 lib/AU/G_Close.v:179-180:
   `astack_malloc_sz_realizes SEGS B StackMalloc8Tbl.PC_STACK_MALLOC_8 StackMalloc8Tbl.CID8`); the glue's local
   abbreviation SEGS = pa_segs PI_scene = scene_segs = AsanUbsan.M.loaded_segments, which is tfibsegs (AU/YB1v.v:12). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05 AsStackSz AsStackLeaf.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB1v YF0m.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Rt Require Import StackMalloc8Tbl StackMalloc8Cuts.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Rt Require
StackMalloc8SegA StackMalloc8SegB StackMalloc8SegC StackMalloc8SegD.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require RT_mem_to_shadow RT_poison_shadow.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem stack_malloc_8_sz_closed : forall (B : asyms),
AR_laws tfibsegs B ->
as_tp B = SM8_TP ->
as_tsd B = SM8_TSD ->
(forall ly, In (c8 (ATp 0) (AF 0)) (as_const B ly)) ->
(forall ly, In (c8 (ATp (-88)) (ATsd 0)) (as_const B ly)) ->
(forall ly, In (z8 (ATp (-8)) SM8_DTV) (as_const B ly)) ->
(forall ly, In (c8 (ATp 8) (AD 0)) (as_const B ly)) ->
(forall ly, In (c8 (AD 24) (ATp 0)) (as_const B ly)) ->
(forall ly, In (c8 (ATsd 0) (AC 0)) (as_const B ly)) ->
(forall ly, In (c8 (AC 152) (AT 0)) (as_const B ly)) ->
(forall ly, In (z8 (AT 48) SM8_T_TLS_BEG) (as_const B ly)) ->
(forall ly, In (z8 (AT 56) SM8_T_TLS_END) (as_const B ly)) ->
(forall ly, In (z8 (ANum SM8_TLS_GOT) 1) (as_const B ly)) ->
(forall ly, In (z8 (ANum (SM8_TLS_GOT + 8)) SM8_TLS_GOT_OFF) (as_const B ly)) ->
(forall ly, In (z8 (ANum SM8_REAL_TGA) SM8_TGA) (as_const B ly)) ->
(forall ly, In (z8 (ANum (SM8_DTV + 8)) (SM8_TP + 2048)) (as_const B ly)) ->
(forall ly, In (z1 (ANum SM8_ASAN_INITED) 1) (as_const B ly)) ->
(forall ly, In (z1 (ANum SM8_TSD_KEY_INITED) 1) (as_const B ly)) ->
(forall ly, In (z4 (ANum (SM8_TSD_KEY_INITED + 4)) 0) (as_const B ly)) ->
(forall ly, In (z8 (ANum SM8_GOT_CFLAGS) SM8_CFLAGS) (as_const B ly)) ->
(forall ly, In (z1 (ANum SM8_CFLAG_TGA) 1) (as_const B ly)) ->
(forall ly, In (z8 (ANum SM8_GOT_VERB) SM8_VERB) (as_const B ly)) ->
(forall ly, In (z4 (ANum SM8_VERB) 0) (as_const B ly)) ->
(forall ly, In (z8 (ANum SM8_GOT_DTLS) SM8_DTLS_TPOFF) (as_const B ly)) ->
mem_to_shadow_realizes tfibsegs B PC_MEM_TO_SHADOW ->
poison_shadow_realizes tfibsegs B PC_POISON_SHADOW ->
astack_malloc_sz_realizes tfibsegs B StackMalloc8Tbl.PC_STACK_MALLOC_8 StackMalloc8Tbl.CID8.
Proof.
intros B LAWS HC_tp HC_tsd HC_fake_stack HC_tsd_slot HC_dtv HC_dtls HC_dtls_dtv1 HC_tsd_main HC_ctx_thread
HC_thread_tls_beg HC_thread_tls_end HC_tls_got_mod HC_tls_got_off HC_real_tga HC_dtv1 HC_asan_inited
HC_tsd_key_inited HC_tsd_key HC_got_cflags HC_cflag_tga HC_got_verb HC_verb HC_got_dtls HMTS HPS.
apply m8_of_segs;
[ apply StackMalloc8SegA.sm8_segA_holds
| apply StackMalloc8SegB.sm8_segB_holds
| apply StackMalloc8SegC.sm8_segC_holds
| apply StackMalloc8SegD.sm8_segD_holds ]; assumption.
Qed.

Theorem stack_malloc_8_sz_discharged : forall (B : asyms),
AR_laws tfibsegs B ->
TfibSyms B ->
as_tp B = SM8_TP ->
as_tsd B = SM8_TSD ->
(forall ly, In (c8 (ATp 0) (AF 0)) (as_const B ly)) ->
(forall ly, In (c8 (ATp (-88)) (ATsd 0)) (as_const B ly)) ->
(forall ly, In (z8 (ATp (-8)) SM8_DTV) (as_const B ly)) ->
(forall ly, In (c8 (ATp 8) (AD 0)) (as_const B ly)) ->
(forall ly, In (c8 (AD 24) (ATp 0)) (as_const B ly)) ->
(forall ly, In (c8 (ATsd 0) (AC 0)) (as_const B ly)) ->
(forall ly, In (c8 (AC 152) (AT 0)) (as_const B ly)) ->
(forall ly, In (z8 (AT 48) SM8_T_TLS_BEG) (as_const B ly)) ->
(forall ly, In (z8 (AT 56) SM8_T_TLS_END) (as_const B ly)) ->
(forall ly, In (z8 (ANum SM8_TLS_GOT) 1) (as_const B ly)) ->
(forall ly, In (z8 (ANum (SM8_TLS_GOT + 8)) SM8_TLS_GOT_OFF) (as_const B ly)) ->
(forall ly, In (z8 (ANum SM8_REAL_TGA) SM8_TGA) (as_const B ly)) ->
(forall ly, In (z8 (ANum (SM8_DTV + 8)) (SM8_TP + 2048)) (as_const B ly)) ->
(forall ly, In (z1 (ANum SM8_ASAN_INITED) 1) (as_const B ly)) ->
(forall ly, In (z1 (ANum SM8_TSD_KEY_INITED) 1) (as_const B ly)) ->
(forall ly, In (z4 (ANum (SM8_TSD_KEY_INITED + 4)) 0) (as_const B ly)) ->
(forall ly, In (z8 (ANum SM8_GOT_CFLAGS) SM8_CFLAGS) (as_const B ly)) ->
(forall ly, In (z1 (ANum SM8_CFLAG_TGA) 1) (as_const B ly)) ->
(forall ly, In (z8 (ANum SM8_GOT_VERB) SM8_VERB) (as_const B ly)) ->
(forall ly, In (z4 (ANum SM8_VERB) 0) (as_const B ly)) ->
(forall ly, In (z8 (ANum SM8_GOT_DTLS) SM8_DTLS_TPOFF) (as_const B ly)) ->
astack_malloc_sz_realizes tfibsegs B StackMalloc8Tbl.PC_STACK_MALLOC_8 StackMalloc8Tbl.CID8.
Proof.
intros B LAWS TB. intros.
apply stack_malloc_8_sz_closed; try assumption.
- exact (RT_mem_to_shadow.scene_mem_to_shadow B LAWS TB).
- exact (RT_poison_shadow.scene_poison_shadow B LAWS TB).
Qed.

End d.
