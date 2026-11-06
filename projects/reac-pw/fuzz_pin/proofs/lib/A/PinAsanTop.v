(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v (and
   their fuzz_scene form, cold/h-small-a3-sceport lib/A/SceneAsanTop.v) for fuzz_knock: the plain side is fuzz_knock's
   released realization (built as its lib/AgreeFrame.v builds it for the ubsan agreement, at AgreeKnock.ag_sil_shape,
   with the plain entry-function contract that lib/AgreeKnock.v gives it), module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/KnockAsanTop.v at origin/ossv/recipes 6ebe35ba632;
   taken for reac-pw/fuzz_pin image A: the plain side is fuzz_pin's released plain slot at the agreement shape
   (lib/AgreePin.v plain_slot_ag, over lib/Prog/PinSlotAG.v and lib/Prog/PinEnd.v segs_holds, the slot lib/AgreePin.v's
   ubsan_agrees_holds uses) in the role of knock's lib/Prog/KnockSlot.v knock_slot; pin_shape is ag_shape
   checksum_shape, AgreePin's AGS, in the role of AgreeKnock.ag_sil_shape; names knock_* -> pin_*, module paths changed. *)
(* fuzz_pin's asan_agrees, asan_halts, asan_ubsan_agrees and asan_ubsan_halts, each from ONE ASan-side obligation,
   in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v:
   - ASAN_T / ASAN_UBSAN_T: from every valid start, the ASan (ASan+UBSan) build realizes, with no cut
     (Reusable/YK18.v srealizes), the trace set SPECX at the shape of the released agreement (AZ03.v:20-26 TFIB_T);
   - the plain side is fuzz_pin's plain realization of SPECX at 2^34 (lib/AgreeTop.v plain_rz_of_contracts_R, with
     the plain entry-function contract of the ubsan agreement, lib/AgreePin.v plain_slot_ag, as lib/AgreePin.v's
     ubsan_agrees_holds uses it), used unchanged;
   - shape_strong_equiv_efs_relim (Reusable/YM09.v) brings the plain side down to the statements' 2^31 plain budget,
     whose premise gives the plain run's cut-freedom (A/RelimCut.v);
   - the halting statements: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over the same obligation and
     SPECX_shape_ok (A/HaltsSpecP.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_pw.fuzz_pin Require Statements Images.
From OSSVerify.reac_pw.fuzz_pin.images Require Plain Asan AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require AgreePin.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YM09 YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots HaltsKitB.
#[global] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeZlib AgreeShape.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import HaltsSpecP.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

(* The agreement shape of lib/AgreePin.v (its Local Abbreviation AGS): each library call returns 0 and writes nothing. *)
Definition pin_shape : lib_shape := ag_shape checksum_shape.

(* The plain side: as lib/AgreeFrame.v builds it for the ubsan agreement, with lib/AgreePin.v's G = [], GI = True and
   its plain entry-function contract at the agreement shape (AgreePin.plain_slot_ag). *)
Lemma pin_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=pin_shape) inp).
Proof.
  assert (Hp : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc pin_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      [] frame_RELRO (fun _ _ => True) j ENTRY RA_LIB EMPTY SLOT_STACK).
  { intros rc fx j Hj. exact (AgreePin.plain_slot_ag rc fx j Hj). }
  assert (HROOMp : forall data, @room_calls pin_shape (payload_len data) (calls data) SBD_AG)
    by (intros data; exact (ag_room_calls checksum_shape _ _)).
  assert (HG : forall a, in_globals [] a -> in_globals frame_G a) by (intros a (lo & len & [] & _)).
  assert (GIL : G_local_c src0_msyms [] (fun _ _ => True)) by (intros j m m' _ _; exact I).
  assert (GI0 : forall mem, G_img_c src0_msyms [] mem -> (fun _ _ => True) 0%nat mem) by (intros mem _; exact I).
  assert (HC : zlib_runtime_contracts_R pin_shape (@RI_G pin_shape) [] frame_RELRO
    (fun j T m => T = [] /\ (fun _ _ => True) j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G pin_shape) [] frame_RELRO _ (fun _ => [])
      LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step pin_shape (fun _ _ => True))).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) [] frame_RELRO (fun _ _ => True) (fun _ => []) j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) [] frame_RELRO (fun _ _ => True) j
        LIBPC RA_LIB EMPTY LIB_STACK (Hp rc fx j Hj))). }
  exact (plain_rz_of_contracts_R pin_shape (@RI_G pin_shape) [] frame_RELRO
    (fun j T m => T = [] /\ (fun _ _ => True) j m) (fun _ => [])
    (driver_RI_AG pin_shape HROOMp) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs [] (fun _ _ => True) GIL) (fun mem H => conj eq_refl (GI0 mem H)) HC).
Qed.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

(* The ASan-side obligations (cgif_file_fuzzer lib/A/AZ03.v:20-26 TFIB_T, for fuzz_pin's images and shape). *)
Definition ASAN_T : Prop :=
  forall sp brk mbase rnd inp,
  valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes Asan.M.loaded_segments
    (init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
    (SPECX (LS:=pin_shape) inp).

Definition ASAN_UBSAN_T : Prop :=
  forall sp brk mbase rnd inp,
  valid_sp sp -> valid_brk AsanUbsan.M.loaded_segments brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes AsanUbsan.M.loaded_segments
    (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd
       target_alloc_limit inp)
    (SPECX (LS:=pin_shape) inp).

Theorem asan_agrees_of_asan_side : ASAN_T -> Statements.asan_agrees.
Proof.
  intros TFIB. unfold Statements.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (pin_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=pin_shape) inp) (SPECX (LS:=pin_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem asan_ubsan_agrees_of_asan_side : ASAN_UBSAN_T -> Statements.asan_ubsan_agrees.
Proof.
  intros TFIB. unfold Statements.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (pin_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=pin_shape) inp) (SPECX (LS:=pin_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

(* The halting statements (Budgets.Standard.lim_source) from the same obligations, as cgif_file_fuzzer's
   lib/Halts_tfib.v does: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over ASAN_T / ASAN_UBSAN_T and
   SPECX_shape_ok (A/HaltsSpecP.v). *)
Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Theorem asan_halts_of_asan_side : ASAN_T -> Statements.asan_halts.
Proof.
  intros TFIB. unfold Statements.asan_halts, Images.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused Asan.M.loaded_segments Asan.M.init_pc
    Asan.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=pin_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.

Theorem asan_ubsan_halts_of_asan_side : ASAN_UBSAN_T -> Statements.asan_ubsan_halts.
Proof.
  intros TFIB. unfold Statements.asan_ubsan_halts, Images.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused AsanUbsan.M.loaded_segments
    AsanUbsan.M.init_pc AsanUbsan.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target
    (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=pin_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.

Print Assumptions asan_agrees_of_asan_side.
Print Assumptions asan_ubsan_agrees_of_asan_side.
Print Assumptions asan_halts_of_asan_side.
Print Assumptions asan_ubsan_halts_of_asan_side.
