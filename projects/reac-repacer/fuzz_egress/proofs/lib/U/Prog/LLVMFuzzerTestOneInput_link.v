(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_egress: the per-callee bundle on the UBSan image, as
   libreac/fuzz_decode's released lib/U/Prog/LLVMFuzzerTestOneInput_link.v. It takes the frame allocator apart
   and hands the harness-body walk (lib/U/Prog/LLVMFuzzerTestOneInput.v) every contract it assumes: malloc and
   free from the allocator, memset and memcpy from the kit's walks, and this program's four callees --
   check_restamp (which calls rp_restamp, memcpy, bcmp and the allocator), check_mute (rp_mute, which calls
   memset), check_gate (rp_slot_width, which calls rp_frame_channels, which calls reac_frame_clean_len; and
   want_width) and check_inject (want_width, rp_slot_write, memcpy, bcmp and the allocator).
   fuzz_egress links no calloc. The walk has no instructions of its own here. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import
memset memcpy bcmp reac_frame_clean_len rp_frame_channels rp_slot_width rp_slot_write want_width rp_restamp
rp_mute check_restamp_c check_restamp check_mute_c check_mute check_gate_c check_gate check_inject_c check_inject
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
  assert (MALPC : ms_malloc B = 0x14240) by exact HMAL.
  assert (FREEPC : ms_free B = 0x14100) by exact HFRE.
  assert (MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API) by (intros fx'; exact (proj1 (FA fx'))).
  assert (FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API)
    by (intros fx'; exact (proj1 (proj2 (FA fx')))).
  destruct (FA fx) as (_ & _ & _ & _ & _ & _ & CT & _ & BND & _).
  pose proof memset_holds as MSET. pose proof memcpy_holds as MCPY. pose proof bcmp_holds as BC.
  pose proof reac_frame_clean_len_holds as RFCL.
  pose proof (rp_frame_channels_holds RFCL) as RFC.
  pose proof (rp_slot_width_holds RFC) as RSW.
  pose proof want_width_holds as WW.
  pose proof (rp_slot_write_holds RSW) as RSWR.
  pose proof (check_gate_holds RSW WW) as CG.
  pose proof rp_restamp_holds as RST.
  pose proof (rp_mute_holds MSET) as RPM.
  assert (CRS : forall fx' : YK11.FPState, @check_restamp_contract fx' rc B API).
  { intros fx'. pose proof (MALLOC fx') as MALLOC'. eapply (check_restamp_holds (fx := fx')); eassumption. }
  assert (CM : forall fx' : YK11.FPState, @check_mute_contract fx' rc B API).
  { intros fx'. pose proof (MALLOC fx') as MALLOC'. eapply (check_mute_holds (fx := fx')); eassumption. }
  assert (CI : forall fx' : YK11.FPState, @check_inject_contract fx' rc B API).
  { intros fx'. pose proof (MALLOC fx') as MALLOC'. eapply (check_inject_holds (fx := fx')); eassumption. }
  apply LLVMFuzzerTestOneInput_holds_of; assumption.
Qed.

End L.
