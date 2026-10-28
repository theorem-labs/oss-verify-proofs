(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import H0Lim.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  Spec HUMainEntryDefs HUReadBase HUWorld HUTargetPre HUPilotOOM_defs HUPilotOOM ExistsRun PhaseG.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HUW65x.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

Section LeafWorld.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Variable lim : Z.                              (* [comment removed for export] *)
  Hypothesis lim_ge : (LIM <= lim)%Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hplen : (length path <= 4095)%nat.
  (* [comment removed for export] *)
  Hypothesis Hhi0 : exists s : Z, (bv_unsigned sp0 + 192 <= s < 2 ^ 47 - 32)%Z /\ (s mod 8 = 0)%Z /\ mem0 (Z_to_bv 64 s) = Some (Z_to_bv 8 0).
  (* [comment removed for export] *)
  Variable mode : bool.
  Variable Q : config -> Prop.

  (* [comment removed for export] *)
  Definition vm_small (VM : VmMaps) (gm : word) : Prop :=
    vm_reserved VM = segments_reserved RSEGS /\ (LIM <= vm_limit VM)%Z   (* [comment removed for export] *)
    /\ (length (vm_maps VM) <= 4)%nat
    /\ In (gm, Z_to_bv 64 69632) (vm_maps VM)
    /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 69632)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
    /\ seps (vm_maps VM).                                   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition after_malloc (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb bw gm can sec : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->                    (* [comment removed for export] *)
      bv_unsigned bw = brkv ->                               (* [comment removed for export] *)
      read_pre sp0 (p1 sp0 a0s path envv) mb bw gm can sec R M ->
      world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned can) (bv_unsigned sec) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb bw gm -> vm_small VM gm ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe19e0) M (seg_rom RSEGS))
                               (model_pre path VM stdin0 fs0 tid)).

  (* [comment removed for export] *)
  Lemma brk_ok_sem : forall K, after_malloc K ->
    brk_ok_branch_M sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim mode Q K.     (* [comment removed for export] *)
  Proof using lim_ge Hva Hve Hvsp Htid Hbrk Hfile Hpne Hplen Hhi0.
    intros K AM. exact (HUW65x.brk_ok_sem sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim lim_ge Hva Hve Hvsp Htid Hbrk Hplen Hhi0 mode Q K AM).
  Qed.

  (* [comment removed for export] *)
End LeafWorld.
