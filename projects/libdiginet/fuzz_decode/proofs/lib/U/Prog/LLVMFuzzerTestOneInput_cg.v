(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the cut-free (SRcf) twin of LLVMFuzzerTestOneInput_holds_of
   (LLVMFuzzerTestOneInput.v), as libreac/fuzz_decode's released lib/U/Prog/LLVMFuzzerTestOneInput_cg.v is the twin of
   its LLVMFuzzerTestOneInput.v: llvm_sr_of_parts_cf (LLVMFuzzerTestOneInput_top_cg.v) given the cf early path
   (llvm_early_cf), the cf front (llvm_front_holds_cf, malloc at the agree room), the evt loops as they are
   (llvm_loops_evt) and check_refusal's evt contract. malloc and free are the agree side's malloc_contract_ag and
   free_contract_cf; the callee contracts are the same Section hypotheses as in LLVMFuzzerTestOneInput.v, discharged
   in LLVMFuzzerTestOneInput_cgt.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Contract Img0 SlotAgree AgreeLift.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import
memcpy_c memset_c spec_msg_step_c diginet_cursor_init_c diginet_msg_next_c diginet_personality_of_c
diginet_decoder_init_c diginet_decoder_next_c check_cursor_step_c check_cursor_message_c check_events_step_c
check_events_fields_c check_refusal_c
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_mid LLVMFuzzerTestOneInput_decoder
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_cfb LLVMFuzzerTestOneInput_early_cg LLVMFuzzerTestOneInput_front_cg
LLVMFuzzerTestOneInput_top_cg.
Import ListNotations.
Open Scope Z_scope.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract_ag fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Context (OWED : owed_segment) (MC : memcpy_contract) (MS : memset_contract) (SMS : spec_msg_step_contract)
  (CI : diginet_cursor_init_contract) (MN : diginet_msg_next_contract)
  (PO : diginet_personality_of_contract) (DI : diginet_decoder_init_contract)
  (DN : diginet_decoder_next_contract)
  (CCS : check_cursor_step_contract) (CCM : check_cursor_message_contract)
  (CES : check_events_step_contract) (CEF : check_events_fields_contract) (CR : check_refusal_contract).

Theorem LLVMFuzzerTestOneInput_holds_of_cf : LLVMFuzzerTestOneInput_sr_contract_cf B API.
Proof.
  apply (llvm_sr_of_parts_cf B API FREE ERRNO_LOW SINK).
  - intros j stk empty L A regs mem md ra p n b.
    exact (llvm_early_cf B API SINK j stk empty L A regs mem md ra p n b).
  - intros stk empty L0 A0 regs0 mem0 md0 ra p n pl b.
    exact (llvm_front_holds_cf B API MALLOC ERRNO_LOW MC stk empty L0 A0 regs0 mem0 md0 ra p n pl b).
  - exact (llvm_loops_evt OWED CI MN SMS MS CCS CCM PO DI DN CES CEF).
  - exact CR.
Qed.

End M.
