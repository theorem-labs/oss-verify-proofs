(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan). The class-8 stack-malloc contract
   `astack_malloc_sz_realizes tfibsegs B PC_STACK_MALLOC_8 CID8` (lib/Reusable/AsStackSz.v), closed: this file
   composes the four proved segments of lib/A/Rt/StackMalloc8Seg{A,B,C,D}.v through StackMalloc8Cuts.v's
   `m8_of_segs`, and proves nothing new about any function.

   Two theorems:
   - `stack_malloc_8_sz_closed`: the premises are the union of the four segment lemmas' premises, in the order
     of a Theorem Labs lane's composition check (CHAIN-CHECK-asan.md, 2026-10-29): AR_laws, the two certificate fields as_tp /
     as_tsd, the 21 cells of B's as_const that Seg A reads (StackMalloc8SegA.v:310-349), and the two callee
     summaries of lib/Reusable/AsStackLeaf.v (MemToShadow for Seg C, PoisonShadow for Seg D).
   - `stack_malloc_8_sz_discharged`: the two summary premises are discharged by a Theorem Labs lane's proved summaries
     (lib/A/RT_mem_to_shadow.v `scene_mem_to_shadow` at M2S_ENTRY = PC_MEM_TO_SHADOW = 0x3f5d8, and
     lib/A/RT_poison_shadow.v `scene_poison_shadow` at PS_ENTRY = PC_POISON_SHADOW = 0x55bb8), which need
     A/AF0m.v's TfibSyms B. Its premises are AR_laws, TfibSyms, the two fields and the 21 cells: facts about B's
     certificate only. No Axiom, no Admitted, no admit. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 AsStackSz.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m RT_mem_to_shadow RT_poison_shadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import StackMalloc8Tbl StackMalloc8Cuts.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require
StackMalloc8SegA StackMalloc8SegB StackMalloc8SegC StackMalloc8SegD.
Import ListNotations.
Open Scope Z_scope.

Theorem stack_malloc_8_sz_closed {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) :
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
astack_malloc_sz_realizes tfibsegs B PC_STACK_MALLOC_8 CID8.
Proof.
intros LAWS HC_tp HC_tsd HC_fake_stack HC_tsd_slot HC_dtv HC_dtls HC_dtls_dtv1 HC_tsd_main HC_ctx_thread
HC_thread_tls_beg HC_thread_tls_end HC_tls_got_mod HC_tls_got_off HC_real_tga HC_dtv1 HC_asan_inited
HC_tsd_key_inited HC_tsd_key HC_got_cflags HC_cflag_tga HC_got_verb HC_verb HC_got_dtls HMTS HPS.
apply m8_of_segs;
[ eapply StackMalloc8SegA.sm8_segA_holds
| eapply StackMalloc8SegB.sm8_segB_holds
| eapply StackMalloc8SegC.sm8_segC_holds
| eapply StackMalloc8SegD.sm8_segD_holds ];
eassumption.
Qed.

Theorem stack_malloc_8_sz_discharged {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) :
AR_laws tfibsegs B ->
AF0m.PcapSyms B ->
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
astack_malloc_sz_realizes tfibsegs B PC_STACK_MALLOC_8 CID8.
Proof.
intros LAWS TB HC_tp HC_tsd HC_fake_stack HC_tsd_slot HC_dtv HC_dtls HC_dtls_dtv1 HC_tsd_main HC_ctx_thread
HC_thread_tls_beg HC_thread_tls_end HC_tls_got_mod HC_tls_got_off HC_real_tga HC_dtv1 HC_asan_inited
HC_tsd_key_inited HC_tsd_key HC_got_cflags HC_cflag_tga HC_got_verb HC_verb HC_got_dtls.
apply stack_malloc_8_sz_closed; try assumption.
- change PC_MEM_TO_SHADOW with RT_mem_to_shadow.M2S_ENTRY.
  apply RT_mem_to_shadow.scene_mem_to_shadow; assumption.
- change PC_POISON_SHADOW with RT_poison_shadow.PS_ENTRY.
  apply RT_poison_shadow.scene_poison_shadow; assumption.
Qed.
