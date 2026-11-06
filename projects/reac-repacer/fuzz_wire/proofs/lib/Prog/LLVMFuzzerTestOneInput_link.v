(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput_link.v (6874bc78b1f) at fuzz_wire's
   module paths and callees. *)
(* The per-callee bundle of fuzz_wire plain (as libreac/fuzz_decode's released lib/Prog/LLVMFuzzerTestOneInput_link.v).
   It takes the frame allocator apart and hands the harness-body walk (lib/Prog/LLVMFuzzerTestOneInput.v) every
   contract it assumes: malloc (0x14484) and free (0x14344) from the allocator, memcpy from the kit's walk, the seven
   checks check_forward, check_ret, check_downstream, check_meter, check_counter, check_width and check_read (each given
   the rp_* callees it calls), and check_copy (given malloc, free, rp_copy_untag, memcpy and bcmp). fuzz_wire links no
   calloc. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import
memcpy memmove memset bcmp reac_frame_clean_len reac_frame_is_reac rp_fwd_class rp_ret_accept rp_ds_accept
rp_meter_counter rp_counter rp_frame_channels rp_slot_width rp_slot_read rp_copy_untag
check_forward_c check_forward check_ret_c check_ret check_downstream_c check_downstream check_meter_c check_meter
check_counter_c check_counter check_width_c check_width check_read_c check_read check_copy_c check_copy cc_segs
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
  enough (H : llvm_binds B API -> LLVMFuzzerTestOneInput_sr_contract B API) by (intros BI; exact (H BI BI)).
  intros BI. pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  assert (MALPC : ms_malloc B = CC_MALLOC) by exact HMAL.
  assert (FREEPC : ms_free B = CC_FREE) by exact HFRE.
  assert (MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API) by (intros fx'; exact (proj1 (FA fx'))).
  assert (FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API)
    by (intros fx'; exact (proj1 (proj2 (FA fx')))).
  destruct (FA fx) as (_ & _ & _ & _ & _ & _ & CT & _ & BND & _).
  pose proof memcpy_holds as MC. pose proof bcmp_holds as BCMP.
  pose proof (check_forward_holds rp_fwd_class_holds) as CF.
  pose proof (check_ret_holds rp_ret_accept_holds) as CR.
  pose proof (check_downstream_holds rp_ds_accept_holds) as CD.
  pose proof (check_meter_holds rp_meter_counter_holds) as CM.
  pose proof (check_counter_holds rp_counter_holds) as CN.
  pose proof (rp_frame_channels_holds reac_frame_clean_len_holds) as FCH.
  pose proof (check_width_holds FCH) as CW.
  pose proof (check_read_holds memset_holds (rp_slot_read_holds (rp_slot_width_holds FCH))) as CRD.
  pose proof (rp_copy_untag_holds (memmove_holds memcpy_holds) reac_frame_is_reac_holds) as CU.
  assert (CC : forall fx' : YK11.FPState, @check_copy_contract fx' rc B API).
  { intros fx'. pose proof (MALLOC fx') as MALLOC'. eapply (check_copy_holds (fx := fx')); eassumption. }
  (* the walk's Section hypotheses, in order: MALLOC FREE ERRNO_LOW SINK BND CT MC CF CR CD CM CN CW CRD CC *)
  eapply LLVMFuzzerTestOneInput_holds_of; eassumption.
Qed.

End L.
