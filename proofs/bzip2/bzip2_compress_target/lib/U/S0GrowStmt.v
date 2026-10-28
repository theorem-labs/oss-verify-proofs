(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ModelAmb PropExec ShapeAlg Spec Spec04 U.S0ReadBase U.S0World.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TargetPre.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TargetPre.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec04 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0World OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.S0WorldVM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocTight AllocCover.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition vm_small6 (VM : VmMaps) (gm : word) : Prop :=
  vm_reserved VM = segments_reserved Ubsan.M.loaded_segments /\ vm_limit VM = target_alloc_limit
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
    realizes Ubsan.M.loaded_segments
             (mkCfg (mkst R (Z_to_bv 64 0x135d4) M (seg_rom Ubsan.M.loaded_segments)) (model_pre path VM stdin0 fs0 tid))
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
  [(0x10000,0x34090); (0x34091,0x340d9); (0x440d9,0x44110); (0x641e8,0x64208); (0x44144,0x44190); (0x44198,0x441b0);
   (0x441b8,0x441d0); (0x441e0,0x441f0); (0x441f8,0x641e8); (0x64220,0x64450); (0x64458,0x64460); (0x64471,0x64478);
   (0x64480,0x64488); (0x64498,0x644a0); (0x644a8,0x644d8); (0x644e0,0x644e8); (0x64890,0x66000)]%Z.

Lemma gw_ivs_incl : incl gw_ivs img_clear_ivs.
Proof. unfold gw_ivs, img_clear_ivs. intros x Hx. cbn in Hx |- *. tauto. Qed.

(* [comment removed for export] *)
Definition oom_tail_stmt : Prop :=
  forall (sp0 : word) (model : Model) (tid hw : Z) (R : bvmap 5 word) (M : word -> option byte) (pc : Z),
    valid_sp sp0 -> m_halted model = None -> m_vm_lazy model = [] ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x441e0 ->
    stack_writable M sp0 -> Forall (fun iv => img_clear M (fst iv) (snd iv)) gw_ivs ->
    cell M 0x44138 4 tid -> (0 < tid < 2 ^ 22)%Z -> cell M 0x44118 8 0x44118 ->
    cell M 0x64450 8 run_guard -> cell M 0x644a0 8 4096 -> cell M 0x644d8 8 hw -> (0 <= hw < 2 ^ 64)%Z ->
    (pc = 0x137e8 \/ pc = 0x13828)%Z ->
    realizes Ubsan.M.loaded_segments
             (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) model)
             (t_die msg_oom (m_fs model)).

(* [comment removed for export] *)
Definition refused_tail_stmt : Prop :=
  forall (sp0 : word) (model : Model) (tid hw : Z) (R : bvmap 5 word) (M : word -> option byte),
    valid_sp sp0 -> m_halted model = None -> m_vm_lazy model = [] ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x441e0 ->
    stack_writable M sp0 -> Forall (fun iv => img_clear M (fst iv) (snd iv)) gw_ivs ->
    cell M 0x44138 4 tid -> (0 < tid < 2 ^ 22)%Z -> cell M 0x44118 8 0x44118 ->
    cell M 0x64450 8 run_guard -> cell M 0x644a0 8 4096 -> cell M 0x644d8 8 hw -> (0 <= hw < 2 ^ 64)%Z ->
    realizes Ubsan.M.loaded_segments
             (mkCfg (mkst R (Z_to_bv 64 0x137c8) M (seg_rom Ubsan.M.loaded_segments)) model)
             (t_die msg_refused (m_fs model)).

(* [comment removed for export] *)
Definition tight_cover_stmt (AI : AllocIface s0segs S0_layout) (AT : AllocTight s0segs S0_layout AI)
    (AC : AllocCover s0segs S0_layout AI) : Prop :=
  forall s LB m MD, ai_inv AI s LB m MD -> at_tight AT s LB MD ->
    ac_c21 AC C21_none s LB /\ exists K0, ac_vm AC K0 s MD /\ (80 <= K0)%nat.

End ACeilS1.
