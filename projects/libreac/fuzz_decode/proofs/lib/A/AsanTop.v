(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_decode, by way of fuzz_grant's lib/A/AsanTop.v: the plain side is fuzz_decode's proved realization (built as its lib/AgreeFrame.v builds it for the ubsan agreement, with the plain slot contract of lib/Prog/LLVMFuzzerTestOneInput_gfr.v, at decode_shape), the halting corollary takes srealizes, module paths changed. *)
(* fuzz_decode's four ASan statements from the ASan side TFIB_T and the ASan+UBSan side TFIB_TB (DecodeTFIB.v), in
   the form of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v (agreement) and lib/Halts_tfib.v (halting):
   - asan_agrees, asan_ubsan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved
     realization of SPECX at 2^34 (lib/AgreeTop.v plain_rz_of_contracts_R, with the plain entry-function contract of
     the ubsan agreement, Prog/LLVMFuzzerTestOneInput_gfr.v decode_slot_g_frame, at decode_shape), the statement's
     plain budget premise, TFIB_T (TFIB_TB) and t_eq_refl;
   - asan_halts, asan_ubsan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_T (TFIB_TB) and
     SPECX_shape_ok (HaltsSpecD.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_decode Require Statements Images.
From OSSVerify.libreac.fuzz_decode.images Require Plain Asan AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YM09 YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots HaltsKitB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeZlib AgreeShape.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require LLVMFuzzerTestOneInput_c Statement
  LLVMFuzzerTestOneInput_gfr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeShape DecodeTFIB HaltsSpecD.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Module DSt := OSSVerify.libreac.fuzz_decode.Statements.
Module DIm := OSSVerify.libreac.fuzz_decode.Images.
Module DPl := OSSVerify.libreac.fuzz_decode.images.Plain.
Module DAs := OSSVerify.libreac.fuzz_decode.images.Asan.
Module DAU := OSSVerify.libreac.fuzz_decode.images.AsanUbsan.
Module PC := OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog.LLVMFuzzerTestOneInput_c.
Module PS := OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog.Statement.
Module PG := OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog.LLVMFuzzerTestOneInput_gfr.

(* The plain side: as lib/AgreeFrame.v builds it for the ubsan agreement (lib/Prog/LLVMFuzzerTestOneInput_agree.v),
   at decode_shape. *)
Lemma decode_plain_rz : forall en inp, valid_entry DIm.plain en inp -> valid_input inp ->
  rz_run DIm.plain Budgets.Standard.lim_source en inp (SPECX (LS:=decode_shape) inp).
Proof.
  assert (Hp : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc decode_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      PC.llvm_G frame_RELRO PC.llvm_GI j ENTRY RA_LIB EMPTY SLOT_STACK).
  { apply PG.decode_slot_g_frame.
    - intros pl fs K. reflexivity.
    - intros b n H. exact (ag_room_g _ b n H).
    - intros n b. reflexivity. }
  assert (HROOMp : forall data, @room_calls decode_shape (payload_len data) (calls data) SBD_AG)
    by (intros data; exact (ag_room_calls _ (payload_len data) (calls data))).
  assert (HC : zlib_runtime_contracts_R decode_shape (@RI_G decode_shape) PC.llvm_G frame_RELRO
    (fun j T m => T = [] /\ PC.llvm_GI j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G decode_shape) PC.llvm_G frame_RELRO _
      (fun _ => []) LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step decode_shape PC.llvm_GI)).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) PC.llvm_G frame_RELRO PC.llvm_GI (fun _ => []) j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) PC.llvm_G frame_RELRO PC.llvm_GI j
        LIBPC RA_LIB EMPTY LIB_STACK (Hp rc fx j Hj))). }
  exact (plain_rz_of_contracts_R decode_shape (@RI_G decode_shape) PC.llvm_G frame_RELRO
    (fun j T m => T = [] /\ PC.llvm_GI j m) (fun _ => [])
    (driver_RI_AG decode_shape HROOMp) (fun a h => frame_G_src0 a (PS.llvm_G_inside a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs PC.llvm_G PC.llvm_GI (PS.llvm_GI_local src0_msyms))
    (fun mem H => conj eq_refl (PS.llvm_GI_img src0_msyms mem H)) HC).
Qed.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Section a.
Hypothesis TFIB : TFIB_T.

Theorem decode_asan_agrees_of_tfib : DSt.asan_agrees.
Proof.
  unfold DSt.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (decode_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold DIm.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    DPl.M.loaded_segments DPl.M.init_pc DPl.M.phdrs sp brk mb rnd
    decodesegs0 DAs.M.init_pc DAs.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=decode_shape) inp) (SPECX (LS:=decode_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem decode_asan_halts_of_tfib : DSt.asan_halts.
Proof.
  unfold DSt.asan_halts, DIm.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage decodesegs0 DAs.M.init_pc DAs.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused decodesegs0 DAs.M.init_pc DAs.M.phdrs
    target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=decode_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End a.

Section b.
Hypothesis TFIBB : TFIB_TB.

Theorem decode_asan_ubsan_agrees_of_tfib : DSt.asan_ubsan_agrees.
Proof.
  unfold DSt.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (decode_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold DIm.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    DPl.M.loaded_segments DPl.M.init_pc DPl.M.phdrs sp brk mb rnd
    decodesegsB0 DAU.M.init_pc DAU.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=decode_shape) inp) (SPECX (LS:=decode_shape) inp) inp
    asan_lim_source_le SWB HP (TFIBB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem decode_asan_ubsan_halts_of_tfib : DSt.asan_ubsan_halts.
Proof.
  unfold DSt.asan_ubsan_halts, DIm.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage decodesegsB0 DAU.M.init_pc DAU.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused decodesegsB0 DAU.M.init_pc
    DAU.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=decode_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIBB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End b.
