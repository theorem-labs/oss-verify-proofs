From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import
ManifestModel ManifestMem Ledger ManifestB names_c check_no_overread_c check_reject_clean_starved_c
check_round_trip_c StatementPlain.
Import ListNotations.
Local Open Scope Z_scope.

Definition at_frame (P : forall B : malloc_syms, (forall rc : RunCeil, AllocAPI B) -> Prop) : Prop :=
  forall B API LS SH SK ra empty, frame_facts B API LS SH SK ra empty -> P B API.

Definition kindb_callees : Prop :=
  at_frame (fun B API => forall (rc : RunCeil) (fx : FPState), @check_no_overread_contract fx rc B (API rc)) /\
  at_frame (fun B API => forall (rc : RunCeil) (fx : FPState), @names_contract fx rc B (API rc)) /\
  at_frame (fun B API => forall (rc : RunCeil) (fx : FPState), @check_reject_clean_starved_contract fx rc B (API rc)) /\
  at_frame (fun B API => forall (rc : RunCeil) (fx : FPState), @check_round_trip_contract fx rc B (API rc)).
