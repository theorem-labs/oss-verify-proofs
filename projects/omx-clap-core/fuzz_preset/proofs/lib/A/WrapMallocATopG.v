(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/WrapMallocATopG.v, with its module paths changed; 6 of its 30 lines of code are new or changed and 20 lines of the source are left out. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image A (asan, pin 1be0f53d96cb): the walk of __wrap_malloc as
   a Theorem Labs lane's keep record wrap_malloc_walk_keep_cf (lib/Reusable/YGcfMallocComposeKeep.v) at ARX := ARXq_A B
   (WrapMallocAQ.v: the layer's ARXq_cf at preset's IOK, the relation of a Theorem Labs lane's A' Allocate contract
   aalloc_realizes_cf_em_m_A, so the two compose with no bridge; a Theorem Labs lane's ruling, 2026-10-31 03:33Z) and
   K := K_A. Field wmk_call is WrapMallocAM1Q.wm_call_q (frame ikeep_mn_cf); field wmk_ret is WrapMallocARetG.wm_ret_q,
   the generic return segment wm_ret_gen at ARXq_A. The unwinder premise is discharged by A's tfib_unwind_ok. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcfRmodel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG RGtop YAkMemnorm YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
WrapMallocAConsts WrapMallocADefs WrapMallocAQ WrapMallocAM1Q WrapMallocARetG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFl4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* The walk as a Theorem Labs lane's keep record: the plain record with the memnorm keep in each segment's post.
   YGcfMallocComposeKeep.wrap_malloc_walk_cf_of_keep gives the plain record wrap_malloc_walk_cf from it. *)
Theorem wrap_malloc_walk_keep_cf_A : forall B, TfibSyms B -> cf_pc_allocate = PC_ALLOCATE ->
  YGcfMallocComposeKeep.wrap_malloc_walk_keep_cf tfibsegs B cf_malloc_max 8 1 1 (ARXq_A B) K_A.
Proof.
intros B TB Hpc. constructor.
- exact (wm_call_q B TB AFl4.tfib_unwind_ok Hpc).
- exact (wm_ret_q B TB cf_malloc_max 8 1 1).
Qed.
End T.
