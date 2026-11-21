(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's validity hypotheses; the process input's new fields; the reader fact of the output channels). *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefStartupDefs.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  Spec RefStartup RefMainEntry RefReadBase RefWorld RefTargetPre RefPilotOOM_defs RefPilotOOM RefLim.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require RefW65x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Section FPW_1. Context {fx : PropExec.FPState}.


Section LeafWorld.
  Context {AL : AllocLim}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
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
  Local Notation INP := (mkProcInputA [a0s; path] envv fs0 stdin0) (only parsing).
  Local Notation uid := (ia_uid stdin0) (only parsing).
  Local Notation hw := (ia_hwcap stdin0) (only parsing).
  Hypothesis ME : main_entry sp0 INP mbase rdraw tid regs0 mem0.
  Hypothesis Hvl : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) INP.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpns : path_has_slash path = false.   (* [comment removed for export] *)
  Hypothesis Hpnd : path_is_dirref path = false.   (* [comment removed for export] *)
  Hypothesis Hplen : (length path <= 4095)%nat.
  Hypothesis Hcr : ia_channel_reader stdin0 = true.   (* LPS 727298f3: the stderr write's channel reader *)

  (* [comment removed for export] *)
  Definition vm_small (VM : VmMaps) (gm : word) : Prop :=
    (exists VX, vm_reserved VM = segments_reserved RSEGS ++ VX /\ (length VX <= 2)%nat /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 2 ^ 30)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) VX) /\ (2 ^ 31 <= vm_limit VM)%Z   
    /\ (length (vm_maps VM) <= 4)%nat
    /\ In (gm, Z_to_bv 64 69632) (vm_maps VM)
    /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 69632)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
    /\ seps (vm_maps VM).                                   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition after_malloc (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->                    (* [comment removed for export] *)
      read_pre sp0 (p1 INP rdraw) mb gm (canary_w rdraw) (secret_w rdraw) R M ->   (* [comment removed for export] *)
      world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned (secret_w rdraw)) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb gm -> vm_small VM gm ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x325c8) M (seg_rom RSEGS))
                              (model_pre path VM stdin0 fs0 tid)) K.

  (* [comment removed for export] *)
  Lemma brk_ok_sem : forall K, after_malloc K ->
    brk_ok_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 (t_alt2 (t_die msg_oom fs0) K).
  Proof using All.
    intros K AM. exact (RefW65x.brk_ok_sem sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hvl Hlau Hbrk Hplen Hcr K AM).
  Qed.

  (* [comment removed for export] *)
  Lemma mmap_ok_sem : forall K, after_malloc K ->
    mmap_ok_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
  Proof using All.
    intros K AM. exact (RefW65x.mmap_ok_sem sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hvl Hlau Hbrk Hplen Hcr K AM).
  Qed.
End LeafWorld.

End FPW_1.
(* [comment removed for export] *)
