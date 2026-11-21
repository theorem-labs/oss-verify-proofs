(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import ITree Nodes InitMem RunConst CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF AcctCore ITreeA NodesA ModelX SysStepF CTreeA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Spec Require Import Monad CMonad CMonadX Stdio Driver Prog ProgA ProgAC AsanProgDeps AsanHandoff.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Spec Require DriverC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg AProto CProto CProtoX AMalloc_iface AUri_kit ADriver_iface ATsafeMain.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require AF_atexit_proof.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit Require Import AsanMain.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section Asm.
  Variable A0 : (nat -> Z) -> alw.

  Definition RNG0 (V : nat -> Z) (mo : Model) : footprint := fp_ok (m_vm_lazy (MX mo [])) (A0 V).

  Definition adrv_stmt {rc : runConstT} : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      amain_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
      implMAC (RNG0 V mo) (progA_mainC AAllocAsan ASTAGE (argv_Z (in_argv inp)))
              (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) TTC ms.

  Definition A0_init_stmt : Prop :=
    forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of ASHOFF V asan_vis) p -> A0 V p.

  Section Decomposed.
    Context {rc : runConstT}.
    Variable apat : alayout -> footprint -> ProcInput -> APS -> machine_state -> Prop.
    Hypothesis APAT : forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      amain_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
      exists L, apat L (RNG0 V mo) inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ms.
    Hypothesis AMAINC : forall L RNG inp s0 ms,
      apat L RNG inp s0 ms ->
      implMAC RNG (DriverC.main_model (ioA AAllocAsan) amalloc_M afree_M ASTAGE (alloc_initA AAllocAsan) (runAC AAllocAsan)
                                      (alloc_countA AAllocAsan) (argv_Z (in_argv inp))) s0
              (fun code s' RNG' ms' => aat_exit code s' RNG' ms') ms.

    Lemma adrv_of_parts : adrv_stmt.
    Proof.
      unfold adrv_stmt. intros en inp w V m ms mo Hv Hi HM HA.
      destruct (APAT en inp w V m ms mo Hv Hi HM HA) as [L HP].
      unfold progA_mainC. eapply implMAC_bind.
      - exact (AMAINC L _ inp _ ms HP).
      - cbv beta. intros code s' RNG' ms' HE. unfold DriverC.exit_model. apply implMAC_lift.
        apply (aexit_from_aat_exit AF_atexit_proof.funcs_on_exit_proofA code s' RNG' ms' TTC). exact HE.
    Qed.
  End Decomposed.
End Asm.

Theorem asan_implC_of_adrv : (forall rc : runConstT, @adrv_stmt ATsafeMain.A0 rc) -> asan_implC_stmt ASTAGE.
Proof. intros H rc en inp w V m ms mo Hv Hi HM HA. exact (H rc en inp w V m ms mo Hv Hi HM HA). Qed.
