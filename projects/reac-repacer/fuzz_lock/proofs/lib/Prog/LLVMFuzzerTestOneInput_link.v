(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput_link.v, with its module paths and module names changed; 14 of its 44 lines of code are new or changed and 9 lines of the source are left out. *)
(* fuzz_lock's LLVMFuzzerTestOneInput in fuzz_lock.plain with its callees' contracts discharged by their walks, in the
   form of libreac/fuzz_decode's lib/Prog/LLVMFuzzerTestOneInput_link.v (release 25e3d17bdb50). The libc strlen
   contract (strlen_c.v, which rp_lock_lookup's walk takes) is a premise here; LLVMFuzzerTestOneInput_halts.v
   discharges it with strlen.v's strlen_holds. Written by Theorem Labs.
   *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import
memcpy memchr bcmp strlen_c rp_lock_lookup_c rp_lock_lookup cno_segs cl_segs
check_no_overread_c check_no_overread check_lookup_c check_lookup
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput.
Import ListNotations.
Local Open Scope Z_scope.

Section L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis STRLEN : strlen_contract.

Theorem LLVMFuzzerTestOneInput_holds : LLVMFuzzerTestOneInput_sr_contract B API.
Proof.
  intros BI. pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  assert (MALPC : ms_malloc B = CNO_MALLOC) by exact HMAL.
  assert (FREEPC : ms_free B = CNO_FREE) by exact HFRE.
  assert (MALPC' : ms_malloc B = CL_MALLOC) by exact HMAL.
  assert (FREEPC' : ms_free B = CL_FREE) by exact HFRE.
  assert (FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API)
    by (intros fx'; exact (proj1 (proj2 (FA fx')))).
  pose proof (rp_lock_lookup_holds STRLEN memchr_holds bcmp_holds) as RP. pose proof memcpy_holds as MC.
  assert (CNO : forall fx' : YK11.FPState, @check_no_overread_contract fx' rc B API).
  { intros fx'. destruct (FA fx') as (M' & _ & _ & _ & _ & _ & CT' & _).
    eapply (check_no_overread_holds (fx := fx')); eassumption. }
  assert (CL : forall fx' : YK11.FPState, @check_lookup_contract fx' rc B API).
  { intros fx'. destruct (FA fx') as (M' & _ & _ & _ & _ & _ & CT' & _).
    pose proof bcmp_holds as BC.
    eapply (check_lookup_holds (fx := fx')); eassumption. }
  exact (LLVMFuzzerTestOneInput_holds_of B API ERRNO_LOW SINK CNO CL BI).
Qed.

End L.
