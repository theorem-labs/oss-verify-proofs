(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: moved out of lib/A/AsanTop.v unchanged (statements and proofs), so that the
   ASan+UBSan top lib/B/AsanUbsanTop.v no longer Requires a file of the asan image. *)
(* The image-neutral part of fuzz_identity's ASan statements, used by both lib/A/AsanTop.v and lib/B/AsanUbsanTop.v:
   - identity_plain_rz: the plain build's proved realization of SPECX at 2^34 (lib/AgreeTop.v plain_rz_of_contracts_R,
     with the plain entry-function contract of the ubsan agreement, Prog/Seg/Agree.v plain_slot_ag, at identity_shape);
   - asan_lim_source_le, lim_source_le_target: the budget inequalities of the agreement and halting statements.
   It Requires no sanitizer image; identity_shape comes from the shape file lib/A/HaltsSpecI.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_identity Require Statements Images.
From OSSVerify.libreac.fuzz_identity.images Require Plain.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YM09 YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots HaltsKitB.
Require Import
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ZImage
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ZTraceSpec
  OSSVerify.Proofs.libreac.fuzz_identity.lib.AllocSlots
  OSSVerify.Proofs.libreac.fuzz_identity.lib.AllocRoom
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ZComplete
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ZAllocator
  OSSVerify.Proofs.libreac.fuzz_identity.lib.Contract
  OSSVerify.Proofs.libreac.fuzz_identity.lib.FrameAPI
  OSSVerify.Proofs.libreac.fuzz_identity.lib.FrameSlotG
  OSSVerify.Proofs.libreac.fuzz_identity.lib.FrameProof
  OSSVerify.Proofs.libreac.fuzz_identity.lib.SlotTopG
  OSSVerify.Proofs.libreac.fuzz_identity.lib.Agree
  OSSVerify.Proofs.libreac.fuzz_identity.lib.AgreeTop
  OSSVerify.Proofs.libreac.fuzz_identity.lib.AgreeZlib
  OSSVerify.Proofs.libreac.fuzz_identity.lib.SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Agree.
Module SAg := OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg.Agree.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import HaltsSpecI.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

(* The plain side: as lib/AgreeFrame.v builds it for fuzz_identity's ubsan agreement (lib/Prog/Seg/AgreeTop.v), from
   the plain entry-function contract of that agreement (lib/Prog/Seg/Agree.v plain_slot_ag), at identity_shape. *)
Lemma identity_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=identity_shape) inp).
Proof.
  assert (Hp : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc identity_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      [] frame_RELRO (fun _ _ => True) j ENTRY RA_LIB EMPTY SLOT_STACK).
  { intros rc fx j Hj. exact (SAg.plain_slot_ag rc fx j Hj). }
  assert (HROOMp : forall data, @room_calls identity_shape (payload_len data) (calls data) SBD_AG)
    by (intros data; apply SAg.room_calls_ag).
  assert (HG : forall a, in_globals [] a -> in_globals frame_G a) by (intros a (lo & len & [] & _)).
  assert (GIL : G_local_c src0_msyms [] (fun _ _ => True)) by (intros j m m' _ _; exact I).
  assert (GI0 : forall mem, G_img_c src0_msyms [] mem -> (fun _ _ => True) 0%nat mem) by (intros mem _; exact I).
  assert (HC : zlib_runtime_contracts_R identity_shape (@RI_G identity_shape) [] frame_RELRO
    (fun j T m => T = [] /\ (fun _ _ => True) j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G identity_shape) [] frame_RELRO _ (fun _ => [])
      LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step identity_shape (fun _ _ => True))).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) [] frame_RELRO (fun _ _ => True) (fun _ => []) j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) [] frame_RELRO (fun _ _ => True) j
        LIBPC RA_LIB EMPTY LIB_STACK (Hp rc fx j Hj))). }
  exact (plain_rz_of_contracts_R identity_shape (@RI_G identity_shape) [] frame_RELRO
    (fun j T m => T = [] /\ (fun _ _ => True) j m) (fun _ => [])
    (driver_RI_AG identity_shape HROOMp) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs [] (fun _ _ => True) GIL) (fun mem H => conj eq_refl (GI0 mem H)) HC).
Qed.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.
