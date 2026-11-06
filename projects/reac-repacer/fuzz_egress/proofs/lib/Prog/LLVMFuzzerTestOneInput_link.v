(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_link.v
   at bc49657c087a; module path and this unit's callees. *)
(* The per-callee bundle, as libreac/fuzz_decode's released lib/Prog/LLVMFuzzerTestOneInput_link.v. It takes the
   frame allocator apart and hands the harness-body walk (LLVMFuzzerTestOneInput.v) every contract it assumes:
   malloc and free from the allocator; memset and memcpy from the kit's walks; check_gate from check_gate_holds over
   rp_slot_width_holds (over rp_frame_channels_holds and reac_frame_clean_len_holds) and want_width_holds;
   check_restamp, check_mute and check_inject from their *_holds over the allocator, memcpy, bcmp, rp_restamp,
   rp_mute (over memset), want_width and rp_slot_write. fuzz_egress links no calloc. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import
memcpy memset bcmp want_width reac_frame_clean_len rp_frame_channels rp_slot_width rp_slot_write rp_restamp rp_mute
check_gate check_restamp_c check_restamp check_mute_c check_mute check_inject_c check_inject
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
  assert (MALPC : ms_malloc B = 0x14010) by exact HMAL.
  assert (FREEPC : ms_free B = 0x13ed0) by exact HFRE.
  assert (MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API) by (intros fx'; exact (proj1 (FA fx'))).
  assert (FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API)
    by (intros fx'; exact (proj1 (proj2 (FA fx')))).
  pose proof memcpy_holds as MCP. pose proof memset_holds as MSH. pose proof bcmp_holds as BC.
  pose proof want_width_holds as WW. pose proof rp_restamp_holds as RST. pose proof (rp_mute_holds MSH) as RPM.
  pose proof (rp_slot_width_holds (rp_frame_channels_holds reac_frame_clean_len_holds)) as SW.
  pose proof (rp_slot_write_holds SW) as RSW.
  pose proof (check_gate_holds SW WW) as CG.
  assert (CR : forall fx' : YK11.FPState, @check_restamp_contract fx' rc B API).
  { intros fx'. destruct (FA fx') as (_ & _ & _ & _ & _ & _ & CT' & _).
    exact (@check_restamp_holds fx' rc B API SEGS MALPC FREEPC ERRNO_LOW AX CT' (MALLOC fx') FREE MCP RST BC). }
  assert (CM : forall fx' : YK11.FPState, @check_mute_contract fx' rc B API).
  { intros fx'. destruct (FA fx') as (_ & _ & _ & _ & _ & _ & CT' & _).
    exact (@check_mute_holds fx' rc B API SEGS MALPC FREEPC ERRNO_LOW AX CT' (MALLOC fx') FREE MCP RPM BC). }
  assert (CI : forall fx' : YK11.FPState, @check_inject_contract fx' rc B API).
  { intros fx'. destruct (FA fx') as (_ & _ & _ & _ & _ & _ & CT' & _).
    exact (@check_inject_holds fx' rc B API SEGS MALPC FREEPC ERRNO_LOW AX CT' (MALLOC fx') FREE MCP WW RSW BC). }
  exact (LLVMFuzzerTestOneInput_holds_of B API MALLOC FREE ERRNO_LOW SINK MSH MCP CG CR CM CI BI).
Qed.

End L.
