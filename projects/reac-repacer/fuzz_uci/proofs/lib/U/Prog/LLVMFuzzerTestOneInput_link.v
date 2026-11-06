(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the per-callee bundle on the UBSan image, the UBSan twin of
   lib/Prog/LLVMFuzzerTestOneInput_link.v at this image's values (malloc 0x13f74, free 0x13e34), as libreac/fuzz_decode's
   released lib/U/Prog/LLVMFuzzerTestOneInput_link.v. It takes the frame allocator apart and hands the harness-body
   walk (lib/U/Prog/LLVMFuzzerTestOneInput.v) every contract it assumes: malloc and free from the allocator, and this
   program's check_no_overread and check_value (each given memcpy from the kit's walk and rp_uci_int, which they call)
   and check_clamp (which calls rp_hot_clamp). fuzz_uci links no calloc. The walk has no instructions of its own here. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import
memcpy rp_uci_int rp_hot_clamp check_clamp check_no_overread_c check_no_overread check_value_c check_value
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

Theorem LLVMFuzzerTestOneInput_holds : LLVMFuzzerTestOneInput_sr_contract B API.
Proof.
  intros BI. pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  assert (MALPC : ms_malloc B = 0x13f74) by exact HMAL.
  assert (FREEPC : ms_free B = 0x13e34) by exact HFRE.
  assert (MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API) by (intros fx'; exact (proj1 (FA fx'))).
  assert (FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API)
    by (intros fx'; exact (proj1 (proj2 (FA fx')))).
  destruct (FA fx) as (_ & _ & _ & _ & _ & _ & CT & _ & BND & _).
  pose proof memcpy_holds as MC. pose proof rp_uci_int_holds as RUI.
  assert (CNO : forall fx' : YK11.FPState, @check_no_overread_contract fx' rc B API).
  { intros fx'. pose proof (MALLOC fx') as MALLOC'. eapply (check_no_overread_holds (fx := fx')); eassumption. }
  assert (CV : forall fx' : YK11.FPState, @check_value_contract fx' rc B API).
  { intros fx'. pose proof (MALLOC fx') as MALLOC'. eapply (check_value_holds (fx := fx')); eassumption. }
  exact (LLVMFuzzerTestOneInput_holds_of B API MALLOC FREE ERRNO_LOW SINK BND CT CNO CV check_clamp_holds BI).
Qed.

End L.
