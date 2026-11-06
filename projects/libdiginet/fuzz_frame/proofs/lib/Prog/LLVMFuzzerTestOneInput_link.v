(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_link.v
   at bc49657c087a; module path and this unit's callees. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/LLVMFuzzerTestOneInput_link.v, with its module paths changed; 33 of its 59 lines of code are new or changed and 23 lines of the source are left out. *)
(* The plain slot contract of fuzz_frame's LLVMFuzzerTestOneInput from the contracts of its callees, in the form
   of libreac/fuzz_decode's lib/Prog/LLVMFuzzerTestOneInput_link.v (bf7779f81ed7). malloc and free are the
   allocator contracts of llvm_frame (frame_allocator); the image links no calloc. The other callees are taken
   through their contracts: memcpy, memset, diginet_frame_parse, check_parse_refusal, check_parse_fields,
   check_announce, and check_round_trip for every allocator that llvm_frame and llvm_binds describe
   (check_round_trip_all). slot_sr_all_of_callees is Statement.v slot_sr_all, the premise of
   plain_halts_of_llvm (LLVMFuzzerTestOneInput_halts.v), under these contracts.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import memcpy_c memset_c diginet_frame_parse_c
  check_parse_refusal_c check_parse_fields_c check_round_trip_c check_announce_c
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput Statement LLVMFuzzerTestOneInput_end
  LLVMFuzzerTestOneInput_halts.
From OSSVerify.libdiginet.fuzz_frame Require Statements.
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
Hypothesis MC : memcpy_contract.
Hypothesis MSET : memset_contract.
Hypothesis PARSE : diginet_frame_parse_contract.
Hypothesis CPR : check_parse_refusal_contract.
Hypothesis CPF : check_parse_fields_contract.
Hypothesis CRT : forall fx' : YK11.FPState, @check_round_trip_contract fx' rc B API.
Hypothesis CA : check_announce_contract.

Theorem LLVMFuzzerTestOneInput_holds : LLVMFuzzerTestOneInput_sr_contract B API.
Proof.
  assert (MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API) by (intros fx'; exact (proj1 (FA fx'))).
  assert (FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API)
    by (intros fx'; exact (proj1 (proj2 (FA fx')))).
  exact (LLVMFuzzerTestOneInput_holds_of B API MALLOC FREE ERRNO_LOW SINK MC MSET PARSE CPR CPF CRT CA).
Qed.

End L.

(* check_round_trip's contract for every allocator of the slot: the walk of check_round_trip may use the
   allocator contracts, the errno bound and the image words of llvm_frame and llvm_binds. *)
Definition check_round_trip_all : Prop :=
  forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B),
    (forall fx' : FPState, @frame_allocator rc fx' B API) -> errno_addr B + 4 <= @alloc_ceiling rc ->
    llvm_binds B API -> @check_round_trip_contract fx rc B API.

Theorem slot_sr_all_of_callees :
  memcpy_contract -> memset_contract -> diginet_frame_parse_contract -> check_parse_refusal_contract ->
  check_parse_fields_contract -> check_round_trip_all -> check_announce_contract -> slot_sr_all.
Proof.
  intros MC MSET PARSE CPR CPF CRT CA rc fx LS B API SH SK FR BI.
  pose proof FR as (HA & Hel & _).
  exact (LLVMFuzzerTestOneInput_holds B API HA Hel (llvm_sink_env rc B API SH SK BI FR) MC MSET PARSE CPR CPF
    (fun fx' => CRT rc fx' B API HA Hel BI) CA BI).
Qed.

Theorem plain_halts_holds_of_walks :
  memcpy_contract -> memset_contract -> diginet_frame_parse_contract -> check_parse_refusal_contract ->
  check_parse_fields_contract -> check_round_trip_all -> check_announce_contract -> Statements.plain_halts.
Proof.
  intros MC MSET PARSE CPR CPF CRT CA. apply plain_halts_of_llvm.
  exact (slot_sr_all_of_callees MC MSET PARSE CPR CPF CRT CA).
Qed.
