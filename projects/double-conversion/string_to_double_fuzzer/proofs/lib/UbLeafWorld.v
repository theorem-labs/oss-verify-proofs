(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import UbStartupDefs.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  Spec UbStartup UbMainEntry UbReadBase UbWorld UbTargetPre UbPilotOOM_defs UbPilotOOM.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require UbW65x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Section FPW_1. Context {fx : PropExec.FPState}.


Section LeafWorld.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpns : path_has_slash path = false.   (* [comment removed for export] *)
  Hypothesis Hpnd : path_is_dirref path = false.   (* [comment removed for export] *)
  Hypothesis Hplen : (length path <= 4095)%nat.

  (* [comment removed for export] *)
  Definition vm_small (VM : VmMaps) (gm : word) : Prop :=
    vm_reserved VM = segments_reserved RSEGS /\ vm_limit VM = LIM   (* [comment removed for export] *)
    /\ (length (vm_maps VM) <= 4)%nat
    /\ In (gm, Z_to_bv 64 69632) (vm_maps VM)
    /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 69632)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
    /\ seps (vm_maps VM).                                   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition after_malloc (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->                    (* [comment removed for export] *)
      read_pre sp0 (p1 sp0 a0s path envv) mb gm (canary_w rdraw) (secret_w rdraw) R M ->   (* [comment removed for export] *)
      world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned (secret_w rdraw)) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb gm -> vm_small VM gm ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32688) M (seg_rom RSEGS))
                              (model_pre path VM stdin0 fs0 tid)) K.

  (* [comment removed for export] *)
  Lemma brk_ok_sem : forall K, after_malloc K ->
    brk_ok_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 (t_alt2 (t_die msg_oom fs0) K).
  Proof using Hva Hve Hvsp Htid ME Hbrk Hfile Hpne Hpns Hpnd Hplen.
    intros K AM. exact (UbW65x.brk_ok_sem sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen K AM).
  Qed.

  (* [comment removed for export] *)
  Lemma mmap_ok_sem : forall K, after_malloc K ->
    mmap_ok_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
  Proof using Hva Hve Hvsp Htid ME Hbrk Hfile Hpne Hpns Hpnd Hplen.
    intros K AM. exact (UbW65x.mmap_ok_sem sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen K AM).
  Qed.
End LeafWorld.

End FPW_1.
