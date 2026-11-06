(* the premises slot_sr_all and slot_sr_cf_all of fuzz_frame's UBSan top, and ubsan_halts, from the contracts of the callees of LLVMFuzzerTestOneInput. *)
(* In the form of libreac/fuzz_decode's lib/U/Prog/LLVMFuzzerTestOneInput_link.v and the link of its
   LLVMFuzzerTestOneInput_cgt.v (bf7779f81ed7). The walks LLVMFuzzerTestOneInput.v and
   LLVMFuzzerTestOneInput_cg.v take the callee contracts as Section hypotheses; here they are put in:
   - malloc and free: the allocator contracts of llvm_frame (frame_allocator), and for the crash-free walk the
     crash-free contracts of slot_sr_cf_all (malloc through malloc_ag_of_cf with llvm_limlaw);
   - memcpy and memset: the kit's walks U/Prog/memcpy.v, memset.v;
   - diginet_frame_parse, check_parse_refusal, check_parse_fields, check_announce: their contracts
     (U/Prog/<fn>_c.v), Section hypotheses of this file;
   - check_round_trip: its contract (U/Prog/check_round_trip_c.v) and its crash-free contract
     (U/Prog/check_round_trip_ccf.v) for every allocator that satisfies llvm_frame and llvm_binds (and, for the
     crash-free one, the crash-free allocator contracts and llvm_limlaw), Section hypotheses CRT and CRT_CF.
     llvm_binds gives the walk of check_round_trip the addresses of malloc and free and AllocExtra; llvm_frame
     gives the errno bound and frame_allocator (ctx_owned).
   The image links no calloc (llvm_frame: ms_calloc B = None), so no calloc contract is used. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract Img0 FrameAPI SlotAgree AgreeLift.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import memcpy memset memcpy_c memset_c
  diginet_frame_parse_c check_parse_refusal_c check_parse_fields_c check_round_trip_c check_round_trip_ccf
  check_announce_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_cfb LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_end Statement LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_halts.
From OSSVerify.libdiginet.fuzz_frame Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Section W.
Hypothesis PARSE : diginet_frame_parse_contract.
Hypothesis CPR : check_parse_refusal_contract.
Hypothesis CPF : check_parse_fields_contract.
Hypothesis CA : check_announce_contract.
Hypothesis CRT : forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B) (SH : sink_head)
    (SK : sink_syms),
  llvm_frame rc B API SH SK -> llvm_binds B API -> @check_round_trip_contract fx rc B API.
Hypothesis CRT_CF : forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B) (SH : sink_head)
    (SK : sink_syms),
  llvm_frame rc B API SH SK -> llvm_binds B API ->
  (forall fx' : FPState, @malloc_contract_cf fx' rc B API) ->
  (forall fx' : FPState, @free_contract_cf fx' rc B API) ->
  llvm_limlaw B API ->
  @check_round_trip_contract_cf fx rc B API.

(* Premise 2 of lib/Prog/TopLink.md. *)
Theorem slot_sr_holds : slot_sr_all.
Proof.
  intros rc fx LS B API SH SK FR BI. pose proof FR as (HA & Hel & _).
  assert (MALLOC : forall fx' : FPState, @malloc_contract fx' rc B API) by (intros fx'; exact (proj1 (HA fx'))).
  assert (FREE : forall fx' : FPState, @free_contract fx' rc B API)
    by (intros fx'; exact (proj1 (proj2 (HA fx')))).
  assert (CRTB : forall fx' : FPState, @check_round_trip_contract fx' rc B API)
    by (intros fx'; exact (CRT rc fx' B API SH SK FR BI)).
  pose proof (llvm_sink_env rc B API SH SK BI FR) as SINK.
  pose proof memcpy_holds as MC. pose proof memset_holds as MSET.
  eapply (LLVMFuzzerTestOneInput_holds_of B API); eassumption.
Qed.

(* Premise 3 of lib/Prog/TopLink.md. *)
Theorem slot_sr_cf_holds : slot_sr_cf_all.
Proof.
  intros rc fx LS B API SH SK FR MCF FCF LIM BI. pose proof FR as (HA & Hel & _).
  assert (MALLOC : forall fx' : FPState, @malloc_contract_ag fx' rc B API)
    by (intros fx'; exact (malloc_ag_of_cf B API LIM (MCF fx'))).
  assert (CRTB : forall fx' : FPState, @check_round_trip_contract_cf fx' rc B API)
    by (intros fx'; exact (CRT_CF rc fx' B API SH SK FR BI MCF FCF LIM)).
  pose proof (llvm_sink_env rc B API SH SK BI FR) as SINK.
  pose proof memcpy_holds as MC. pose proof memset_holds as MSET.
  eapply (LLVMFuzzerTestOneInput_holds_of_cf B API); eassumption.
Qed.

(* ubsan_halts from the walks: lib/U/Prog/LLVMFuzzerTestOneInput_halts.v with premise 2. *)
Theorem ubsan_halts_holds_of_walks : Statements.ubsan_halts.
Proof. exact (ubsan_halts_of_llvm slot_sr_holds). Qed.

End W.
