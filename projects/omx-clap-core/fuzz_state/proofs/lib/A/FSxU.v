(* JOIN of the two proved halves: fuzz_state's U-form stack_malloc contracts, derived from fuzz_preset's AR-parametric
   x-form contracts (lib/A/FCm0s.v, FCm1s.v, FCm3s.v over the frame-area interface lib/Reusable/FCiface.v) through the
   proved bridge lib/A/FSifaceU.v (ARU with the poisoned-head argument ignored is an fs_iface instance, and the pre of
   astack_malloc_realizes_x at ARU_nohp U is FSupoison.ecall_preU conjunct for conjunct, its post FSupoisonU's post
   verbatim).  Each theorem is FSupoisonU.astack_malloc_realizesU's statement unchanged, so FSH_Rt's three stack_malloc
   fields can later be discharged through this x route (see FSRT-SWITCH.md).  This file proves no function of its own: it
   composes FCm<k>s.stack_malloc<k>_contract_x (instantiated at ARx := FSifaceU.ARU_nohp U with FSifaceU.fs_iface_ARU)
   with FSifaceU.astack_malloc_realizesU_of_x.  No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YM05 YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonU FSifaceU FCm0s FCm1s FCm3s.
Import ListNotations.
Local Open Scope Z_scope.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem stack_malloc0_contractU_x : forall B, AR_laws tfibsegs B -> TfibSyms B ->
FSupoisonU.astack_malloc_realizesU tfibsegs B 0.
Proof.
intros B LAWS TB.
apply (FSifaceU.astack_malloc_realizesU_of_x tfibsegs B 0). intros U.
exact (FCm0s.stack_malloc0_contract_x B (FSifaceU.ARU_nohp tfibsegs B U)
(FSifaceU.fs_iface_ARU tfibsegs B LAWS U) TB).
Qed.

Theorem stack_malloc1_contractU_x : forall B, AR_laws tfibsegs B -> TfibSyms B ->
FSupoisonU.astack_malloc_realizesU tfibsegs B 1.
Proof.
intros B LAWS TB.
apply (FSifaceU.astack_malloc_realizesU_of_x tfibsegs B 1). intros U.
exact (FCm1s.stack_malloc1_contract_x B (FSifaceU.ARU_nohp tfibsegs B U)
(FSifaceU.fs_iface_ARU tfibsegs B LAWS U) TB).
Qed.

Theorem stack_malloc3_contractU_x : forall B, AR_laws tfibsegs B -> TfibSyms B ->
FSupoisonU.astack_malloc_realizesU tfibsegs B 3.
Proof.
intros B LAWS TB.
apply (FSifaceU.astack_malloc_realizesU_of_x tfibsegs B 3). intros U.
exact (FCm3s.stack_malloc3_contract_x B (FSifaceU.ARU_nohp tfibsegs B U)
(FSifaceU.fs_iface_ARU tfibsegs B LAWS U) TB).
Qed.

End x.
