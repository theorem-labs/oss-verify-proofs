(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Plain.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ModelAmb PropExec ShapeAlg Spec Spec04 S0ReadBase S0World.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require S0TargetPre.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require S0TargetPre.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec04 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0ReadBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0World OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0TargetPre.S0WorldVM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0TargetPre.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface AllocLayout0 AllocTight AllocCover.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition vm_small6 (VM : VmMaps) (gm : word) : Prop :=
  vm_reserved VM = segments_reserved Plain.M.loaded_segments /\ vm_limit VM = source_alloc_limit
  /\ (length (vm_maps VM) <= 4)%nat /\ In (gm, Z_to_bv 64 69632) (vm_maps VM)
  /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 69632)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
  /\ seps (vm_maps VM).

(* [comment removed for export] *)
Definition big_file_stmt : Prop :=
  forall (sp0 p1 mb gm : word) (R : bvmap 5 word) (M : word -> option byte)
         (area brkv mas hw : Z) (VM : VmMaps) (path content : list byte) (stdin0 : AmbIn) (fs0 : Fs) (tid : word),
    fs_lookup fs0 path = Some content -> (65536 <= Z.of_nat (length content))%Z ->
    area = (bv_unsigned mb + 4096)%Z ->
    read_pre sp0 p1 mb gm R M ->
    world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) hw M ->
    main_frame (bv_unsigned sp0) M ->
    vm_pre VM mb gm ->
    vm_small6 VM gm ->
    target_vmx (bv_unsigned sp0) (bv_unsigned gm) area brkv mas VM -> auxv0 (bv_unsigned sp0) M ->
    alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z ->
    realizes Plain.M.loaded_segments
             (mkCfg (mkst R (Z_to_bv 64 0x1359c) M (seg_rom Plain.M.loaded_segments)) (model_pre path VM stdin0 fs0 tid))
             (t_body04 content fs0).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition grow_entry_stmt (AI : AllocIface s0segs S0_layout) (AT : AllocTight s0segs S0_layout AI) : Prop :=
  forall (sp0 gm area brkv mas tid hw : Z) (M : word -> option byte) (VM : VmMaps) (MD : Model),
    world0 area gm brkv mas tid hw M -> 0x7fff80000000 <= sp0 <= 0x800000000000 ->
    target_vm gm area VM -> target_vmx sp0 gm area brkv mas VM -> auxv0 sp0 M -> atop_ok VM ->   (* [comment removed for export] *)
    m_vmmaps MD = VM -> m_halted MD = None -> m_vm_lazy MD = [] -> m_vm_materialized MD = [] ->
    exists (s : ai_AS AI) (pb : bid),
      ai_inv AI s [(pb, gm + 32, 65536)] M MD /\ at_tight AT s [(pb, gm + 32, 65536)] MD /\ ai_aux AI M sp0.

(* [comment removed for export] *)
Lemma atop_of_vmx : forall sp0 gm area brkv mas VM,
  target_vmx sp0 gm area brkv mas VM -> alloc_ceiling = (sp0 - 8388608)%Z -> (0 <= sp0 < 2 ^ 64)%Z -> atop_ok VM.
Proof.
  intros sp0 gm area brkv mas VM VX AC Hsp. unfold atop_ok, alloc_top.
  rewrite (target_vmx_init_sp _ _ _ _ _ _ VX). rewrite u64_lit by lia. unfold stack_max_size. lia.
Qed.

(* [comment removed for export] *)
Definition gw_ivs : list (Z * Z) :=
  [(0x10000,0x2a590); (0x2a591,0x2a5d9); (0x3a5d9,0x3a610); (0x5a6e8,0x5a708); (0x3a644,0x3a690); (0x3a698,0x3a6b0);
   (0x3a6b8,0x3a6d0); (0x3a6e0,0x3a6f0); (0x3a6f8,0x5a6e8); (0x5a720,0x5a950); (0x5a958,0x5a960); (0x5a971,0x5a978);
   (0x5a980,0x5a988); (0x5a998,0x5a9a0); (0x5a9a8,0x5a9d8); (0x5a9e0,0x5a9e8); (0x5ad90,0x5c000)]%Z.

Lemma gw_ivs_incl : incl gw_ivs img_clear_ivs.
Proof. unfold gw_ivs, img_clear_ivs. intros x Hx. cbn in Hx |- *. tauto. Qed.

(* [comment removed for export] *)
Definition oom_tail_stmt : Prop :=
  forall (sp0 : word) (model : Model) (tid hw : Z) (R : bvmap 5 word) (M : word -> option byte) (pc : Z),
    valid_sp sp0 -> m_halted model = None -> m_vm_lazy model = [] ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x3a6e0 ->
    stack_writable M sp0 -> Forall (fun iv => img_clear M (fst iv) (snd iv)) gw_ivs ->
    cell M 0x3a638 4 tid -> (0 < tid < 2 ^ 22)%Z -> cell M 0x3a618 8 0x3a618 ->
    cell M 0x5a950 8 run_guard -> cell M 0x5a9a0 8 4096 -> cell M 0x5a9d8 8 hw -> (0 <= hw < 2 ^ 64)%Z ->
    (pc = 0x137b0 \/ pc = 0x137f0)%Z ->
    realizes Plain.M.loaded_segments
             (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) model)
             (t_die msg_oom (m_fs model)).

(* [comment removed for export] *)
Definition refused_tail_stmt : Prop :=
  forall (sp0 : word) (model : Model) (tid hw : Z) (R : bvmap 5 word) (M : word -> option byte),
    valid_sp sp0 -> m_halted model = None -> m_vm_lazy model = [] ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x3a6e0 ->
    stack_writable M sp0 -> Forall (fun iv => img_clear M (fst iv) (snd iv)) gw_ivs ->
    cell M 0x3a638 4 tid -> (0 < tid < 2 ^ 22)%Z -> cell M 0x3a618 8 0x3a618 ->
    cell M 0x5a950 8 run_guard -> cell M 0x5a9a0 8 4096 -> cell M 0x5a9d8 8 hw -> (0 <= hw < 2 ^ 64)%Z ->
    realizes Plain.M.loaded_segments
             (mkCfg (mkst R (Z_to_bv 64 0x13790) M (seg_rom Plain.M.loaded_segments)) model)
             (t_die msg_refused (m_fs model)).

(* [comment removed for export] *)
Definition tight_cover_stmt (AI : AllocIface s0segs S0_layout) (AT : AllocTight s0segs S0_layout AI)
    (AC : AllocCover s0segs S0_layout AI) : Prop :=
  forall s LB m MD, ai_inv AI s LB m MD -> at_tight AT s LB MD ->
    ac_c21 AC C21_none s LB /\ exists K0, ac_vm AC K0 s MD /\ (80 <= K0)%nat.

End ACeilS1.
