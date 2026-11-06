(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg AllocIface PureModel.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocInv_auxv AllocBase AllocCalloc.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WithML.
Context {ML : MallocLayout}.

(* [comment removed for export] *)
Definition mallocng_globals (a : word) : Prop :=
  (bv_unsigned A_LOCK <= bv_unsigned a < bv_unsigned A_LOCK + 8 + CTX_SIZE) \/
  (bv_unsigned A_MALLOC_REPLACED <= bv_unsigned a < bv_unsigned A_MALLOC_REPLACED + 4).

(* [comment removed for export] *)
Definition mallocng_errno_slot (a : word) : Prop :=
  bv_unsigned A_ERRNO <= bv_unsigned a < bv_unsigned A_ERRNO + 4.

(* [comment removed for export] *)
Definition mallocng_grantable (a : word) : Prop :=
  0x1000 <= bv_unsigned a /\ ~ (IMG_LO <= bv_unsigned a < IMG_HI).

Definition mallocng_in_ro (a : word) : Prop := IMG_LO <= bv_unsigned a < RW_LO.
Definition mallocng_in_rw (a : word) : Prop := RW_LO <= bv_unsigned a < IMG_HI.

(* [comment removed for export] *)
Definition mallocng_env (sp0 : word) (argv envp : list (list byte)) (m : word -> option byte) : Prop :=
  rdn ml_segs m A_NEED_LOCKS 1 = Some [Z_to_bv 8 0] /\
  rdn ml_segs m A_PAGE_SIZE 8 = Some (Z_to_le_bytes 8 4096) /\
  (forall a : Z, IMG_LO <= a < RW_LO -> m (Z_to_bv 64 a) = None) /\
  aux_env sp0 argv envp m /\
  (forall a : Z, bv_unsigned A_GOT_SSP <= a < bv_unsigned A_GOT_SSP + 8 -> m (Z_to_bv 64 a) = None).

(* [comment removed for export] *)
Definition mallocng_mmap_threshold : Z := 131052.

(* [comment removed for export] *)
Definition mallocng_ceiling : Z := 0x7fff7f800000.
Definition mallocng_init_vm (brk : word) : VmMaps :=
  mkVmMaps (segments_reserved ml_segs) [] brk brk 0.

Definition mallocng_alloc_layout : AllocLayout := {|
  al_segs := ml_segs;
  al_rom := ml_rom;
  al_malloc_pc := PC_MALLOC;
  al_free_pc := PC_FREE;
  al_gp := A_TP;
  al_globals := mallocng_globals;
  al_errno_slot := mallocng_errno_slot;
  al_grantable := mallocng_grantable;
  al_ceiling := mallocng_ceiling;
  al_image_hi := IMG_HI;
  al_in_ro := mallocng_in_ro;
  al_in_rw := mallocng_in_rw;
  al_ret_ok := ret_ok;
  al_env := mallocng_env;
  al_init_vm := mallocng_init_vm;
  al_mmap_threshold := mallocng_mmap_threshold
|}.

(* [comment removed for export] *)
Definition mallocng_calloc_layout : CallocLayout := {| al_calloc_pc := PC_CALLOC |}.

End WithML.
