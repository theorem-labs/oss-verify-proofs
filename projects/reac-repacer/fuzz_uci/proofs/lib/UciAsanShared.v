(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_decode, by way of fuzz_grant's lib/A/AsanTop.v: the plain side is fuzz_decode's proved realization (built as its lib/AgreeFrame.v builds it for the ubsan agreement, with the plain slot contract of lib/Prog/LLVMFuzzerTestOneInput_gfr.v, at decode_shape), the halting corollary takes srealizes, module paths changed. *)
(* Modified by Theorem Labs: made from the plain part of libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/A/AsanTop.v (decode_plain_rz, asan_lim_source_le, lim_source_le_target) for reac-repacer/fuzz_uci, as the file both ASan images' AsanTop read: the plain realization is stated at fuzz_uci's checksum_shape (lib/ZTraceSpec.v), the shape both ASan cores state their driver theorem at, so the plain room is checksum_shape's (driver_RI_G and checksum_room_calls of lib/ZComplete.v, SBD of lib/Reusable/DriverSlots.v) in place of the agreement's SBD_AG; the plain slot contract is fuzz_uci's uci_slot_g_frame (lib/Prog/LLVMFuzzerTestOneInput_gfr.v); module paths changed. *)
(* The plain side of fuzz_uci's ASan statements: the plain build realizes SPECX at checksum_shape under the
   standard source budget (lib/AgreeTop.v plain_rz_of_contracts_R over the plain entry-function contract), and the two
   budget orderings the agreement and halting corollaries take. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_repacer.fuzz_uci Require Images.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require LLVMFuzzerTestOneInput_c Statement
  LLVMFuzzerTestOneInput_gfr.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Module PC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.LLVMFuzzerTestOneInput_c.
Module PS := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.Statement.
Module PG := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.LLVMFuzzerTestOneInput_gfr.

(* checksum_shape's room (sb_cap = CAPMAX) is inside the plain entry contract's (128 <= sb_cap <= CAPMAX). *)
Lemma checksum_room_llvm : forall b n, @lib_room checksum_shape b n -> PC.llvm_room b.
Proof.
  intros b n Hb. cbn in Hb. destruct Hb as (H1 & H2 & H3).
  unfold PC.llvm_room. rewrite H3. unfold CAPMAX. lia.
Qed.

(* The plain side: as lib/Prog/LLVMFuzzerTestOneInput_agree.v builds it for the ubsan agreement, at checksum_shape
   with checksum_shape's room. *)
Lemma uci_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=checksum_shape) inp).
Proof.
  assert (Hp : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc checksum_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      PC.llvm_G frame_RELRO PC.llvm_GI j ENTRY RA_LIB EMPTY SLOT_STACK).
  { apply PG.uci_slot_g_frame.
    - intros pl fs K. reflexivity.
    - exact checksum_room_llvm.
    - intros n b. reflexivity. }
  assert (HROOMp : forall data, @room_calls checksum_shape (payload_len data) (calls data) SBD)
    by (intros data; exact (checksum_room_calls (payload_len data) (calls data))).
  assert (HC : zlib_runtime_contracts_R checksum_shape (@RI_G checksum_shape) PC.llvm_G frame_RELRO
    (fun j T m => T = [] /\ PC.llvm_GI j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G checksum_shape) PC.llvm_G frame_RELRO _
      (fun _ => []) LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step checksum_shape PC.llvm_GI)).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) PC.llvm_G frame_RELRO PC.llvm_GI (fun _ => []) j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) PC.llvm_G frame_RELRO PC.llvm_GI j
        LIBPC RA_LIB EMPTY LIB_STACK (Hp rc fx j Hj))). }
  exact (plain_rz_of_contracts_R checksum_shape (@RI_G checksum_shape) PC.llvm_G frame_RELRO
    (fun j T m => T = [] /\ PC.llvm_GI j m) (fun _ => [])
    (driver_RI_G checksum_shape HROOMp) (fun a h => frame_G_src0 a (PS.llvm_G_inside a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs PC.llvm_G PC.llvm_GI (PS.llvm_GI_local src0_msyms))
    (fun mem H => conj eq_refl (PS.llvm_GI_img src0_msyms mem H)) HC).
Qed.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.
