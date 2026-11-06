(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
Require OSSVerify.coturn.FuzzStunClient.images.Plain.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec FPA_asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import
  AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanPlanImages FContractAsan AsanMainLib
  StartupHSMainAsan MainGlueDefs MainGlue AsanMainClosedE AsanTopGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP. Import APS.
Open Scope Z_scope.
#[local] Notation LIM := target_alloc_limit.

Section TopE.
  Hypothesis FCA : F_contract_asan ASEGS FPA_asan.
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.
  Hypothesis ITm_ok : itab_sound ASEGS ITm.
  Variable TREE : nat -> nat -> mtree.
  Hypothesis TREES : forall h ch i, HS_mainA h = Some ch -> (i < 6)%nat ->
    mtree_ok KCm BFUELm FUELm ITm 0 0 (HSA HS_mainA h) (root_class i) (TREE h i) = true.

  Theorem asan_spec_E : asan_spec_stmt.
  Proof.
    intros sp brk mb rnd inp Hent Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hent as (Hsp & Hbrk & Hmb & Hfit).
    destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & [Huid Hgid] & Hnofile & Hsig & Hhw & Habort & Hva & Hur).
    (* [comment removed for export] *)
    rewrite (init_config_inp _ _ _ _ _ _ _ _ inp Habort Hva).
    change target_alloc_limit with LIM.
    eapply (asan_realizes_spec_E FCA sp rnd brk mb (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp)
              (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp));
      try eassumption; exact TREES.
  Qed.
End TopE.
