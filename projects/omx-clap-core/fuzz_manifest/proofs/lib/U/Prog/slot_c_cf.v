From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import
ManifestModel ManifestMem Ledger ManifestB names_c check_no_overread_c check_reject_clean_starved_c
check_round_trip_c StatementUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import SlotAgree.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import
names_c_cf check_no_overread_c_cf check_reject_clean_starved_c_cf check_round_trip_c_cf StatementUbsanCg.
Import ListNotations.
Local Open Scope Z_scope.

(* The cut-free twin of slot_c.v: the Kind B callees of the slot in their cut-free contracts (<f>_c_cf.v), at every
   agreement frame (StatementUbsanCg.frame_facts_cg with the cut-free allocator contracts and LIMLAW). *)
Definition at_frame_cg (P : forall B : malloc_syms, (forall rc : RunCeil, AllocAPI B) -> Prop) : Prop :=
  forall B API LS SH SK ra empty, frame_facts_cg B API LS SH SK ra empty ->
    (forall (rc : RunCeil) (fx : FPState), @malloc_contract_cf fx rc B (API rc)) ->
    (forall (rc : RunCeil) (fx : FPState), @free_contract_cf fx rc B (API rc)) ->
    (forall (rc : RunCeil) L A mem md, aa_MR (API rc) L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md)) ->
    P B API.

Definition kindb_callees_cf : Prop :=
  at_frame_cg (fun B API => forall (rc : RunCeil) (fx : FPState), @check_no_overread_contract_cf fx rc B (API rc)) /\
  at_frame_cg (fun B API => forall (rc : RunCeil) (fx : FPState), @names_contract_cf fx rc B (API rc)) /\
  at_frame_cg (fun B API => forall (rc : RunCeil) (fx : FPState), @check_reject_clean_starved_contract_cf fx rc B (API rc)) /\
  at_frame_cg (fun B API => forall (rc : RunCeil) (fx : FPState), @check_round_trip_contract_cf fx rc B (API rc)).
