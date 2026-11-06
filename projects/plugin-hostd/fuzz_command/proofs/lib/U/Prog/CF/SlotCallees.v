From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU VerbsB CommandB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_c send_message_c check_words_c check_round_trip_c rec_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import check_reply_c check_arity_c check_refusal_c strnlen_c memcpy_c strspn_c strcspn_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import Slot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The callees of LLVMFuzzerTestOneInput (ubsan 0x14060), each at its agreed contract: the Kind B ones for every
   run ceiling and float state, the Kind A ones as stated. *)
Definition cmd_callees (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) : Prop :=
  (forall (rc : RunCeil) (fx : FPState), @send_message_contract fx rc B (API rc)) /\
  (forall (rc : RunCeil) (fx : FPState), @check_words_contract fx rc B (API rc)) /\
  (forall (rc : RunCeil) (fx : FPState), @check_round_trip_contract fx rc B (API rc)) /\
  (forall (rc : RunCeil) (fx : FPState), @rec_clear_contract fx rc B (API rc)) /\
  check_reply_contract /\ check_arity_contract /\ check_refusal_contract /\
  strnlen_contract /\ memcpy_contract /\ strspn_contract /\ strcspn_contract.
