(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v (and
   their fuzz_scene form, a working branch lib/A/SceneAsanTop.v) for fuzz_knock: the plain side is fuzz_knock's
   released realization (built as its lib/AgreeFrame.v builds it for the ubsan agreement, at AgreeKnock.ag_sil_shape,
   with the plain entry-function contract that lib/AgreeKnock.v gives it), module paths changed. *)
(* Modified by Theorem Labs, 2026-10: taken for reac-pw/fuzz_qdisc image A from proofs/libreac/fuzz_knock/lib/A/KnockAsanTop.v at
   origin/ossv/recipes 6ebe35ba632: the plain side is fuzz_qdisc's (lib/AgreeQdisc.v ag_sil_shape, lib/Prog/QdiscSlot.v
   qdisc_slot in the roles of AgreeKnock / KnockSlot), names knock_* -> qdisc_*, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_qdisc/lib/A/QdiscAsanTop.v at 56ce9edaafc, for reac-pw/fuzz_role image A:
   role_shape := AgreeShape.ag_shape ZTraceSpec.checksum_shape (the shape fuzz_role's ubsan agreement takes, as fuzz_pin's
   lib/AgreePin.v does); the plain entry-function slot at that shape is the named premise PLAIN_SLOT_AG (the plain-slot
   premise of lib/AgreeFrame.v ubsan_agrees_of_slots), which the agreement closings discharge, in place of a Require of a
   plain slot file; names qdisc_* -> role_*; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RoleAsanTop.v at fa745625e7d, for reac-pw/fuzz_headamp
   image A and image B: headamp_shape := AgreeShape.ag_shape ZTraceSpec.checksum_shape (fuzz_headamp's lib/ZTraceSpec.v,
   AgreeShape.v, AgreeFrame.v, AgreeTop.v, AgreeZlib.v and the other frame files used here are fuzz_role's up to module
   paths; lib/ZImage.v and lib/FrameAPI.v differ only by fuzz_headamp's addresses); PLAIN_SLOT_AG is the same premise at
   fuzz_headamp's frame names; names role_* -> headamp_*, HaltsSpecR -> HaltsSpecH; module paths changed. *)
(* fuzz_headamp's asan_agrees, asan_halts, asan_ubsan_agrees and asan_ubsan_halts, each from ONE ASan-side obligation,
   in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v:
   - ASAN_T / ASAN_UBSAN_T: from every valid start, the ASan (ASan+UBSan) build realizes, with no cut
     (Reusable/YK18.v srealizes), the trace set SPECX at the shape of the ubsan agreement (AZ03.v:20-26 TFIB_T);
   - the plain side is fuzz_headamp's plain realization of SPECX at 2^34 (lib/AgreeTop.v plain_rz_of_contracts_R) with the
     plain entry-function slot at headamp_shape. fuzz_headamp's slot (lib/Prog/HeadSlotAG.v at that shape) lands in the plain
     agreement file lib/AgreeHead.v as plain_slot_ag, of exactly the type PLAIN_SLOT_AG below (fuzz_pin's
     lib/AgreePin.v:81-83 plain_slot_ag at fuzz_headamp's names). The agreement statements here take PLAIN_SLOT_AG as
     their first premise; lib/A/AD2o.v (image B: lib/AU/YD2o.v) passes AgreeHead.plain_slot_ag, held as a Section
     Variable until lib/AgreeHead.v lands;
   - shape_strong_equiv_efs_relim (Reusable/YM09.v) brings the plain side down to the statements' 2^31 plain budget,
     whose premise gives the plain run's cut-freedom (A/RelimCut.v);
   - the halting statements: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over the same obligation and
     SPECX_shape_ok (A/HaltsSpecH.v); they need no plain side. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_pw.fuzz_headamp Require Statements Images.
From OSSVerify.reac_pw.fuzz_headamp.images Require Plain Asan AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YM09 YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots HaltsKitB.
#[global] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeZlib AgreeShape.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HaltsSpecH.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Definition headamp_shape : lib_shape := ag_shape checksum_shape.

(* The plain entry-function slot at headamp_shape: the plain-slot premise of AgreeFrame.ubsan_agrees_of_slots at G = [],
   GI = True, fuzz_headamp's plain zlib instance (src0_msyms, zlib_API, src0_sink_head, src0_sink, RA_LIB, EMPTY). *)
Definition PLAIN_SLOT_AG : Prop :=
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc headamp_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      [] frame_RELRO (fun _ _ => True) j ENTRY RA_LIB EMPTY SLOT_STACK.

Section plain_side.
Hypothesis headamp_plain_slot_ag : PLAIN_SLOT_AG.

(* The plain side: as lib/AgreeFrame.v builds it for the ubsan agreement, with G = [], GI = True and the plain slot
   headamp_plain_slot_ag. *)
Lemma headamp_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=headamp_shape) inp).
Proof.
  pose proof headamp_plain_slot_ag as Hp.
  assert (HROOMp : forall data, @room_calls headamp_shape (payload_len data) (calls data) SBD_AG)
    by (intros data; exact (ag_room_calls checksum_shape _ _)).
  assert (HG : forall a, in_globals [] a -> in_globals frame_G a) by (intros a (lo & len & [] & _)).
  assert (GIL : G_local_c src0_msyms [] (fun _ _ => True)) by (intros j m m' _ _; exact I).
  assert (GI0 : forall mem, G_img_c src0_msyms [] mem -> (fun _ _ => True) 0%nat mem) by (intros mem _; exact I).
  assert (HC : zlib_runtime_contracts_R headamp_shape (@RI_G headamp_shape) [] frame_RELRO
    (fun j T m => T = [] /\ (fun _ _ => True) j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G headamp_shape) [] frame_RELRO _ (fun _ => [])
      LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step headamp_shape (fun _ _ => True))).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) [] frame_RELRO (fun _ _ => True) (fun _ => []) j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) [] frame_RELRO (fun _ _ => True) j
        LIBPC RA_LIB EMPTY LIB_STACK (Hp rc fx j Hj))). }
  exact (plain_rz_of_contracts_R headamp_shape (@RI_G headamp_shape) [] frame_RELRO
    (fun j T m => T = [] /\ (fun _ _ => True) j m) (fun _ => [])
    (driver_RI_AG headamp_shape HROOMp) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs [] (fun _ _ => True) GIL) (fun mem H => conj eq_refl (GI0 mem H)) HC).
Qed.
End plain_side.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

(* The ASan-side obligations (cgif_file_fuzzer lib/A/AZ03.v:20-26 TFIB_T, for fuzz_headamp's images and shape). *)
Definition ASAN_T : Prop :=
  forall sp brk mbase rnd inp,
  valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes Asan.M.loaded_segments
    (init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
    (SPECX (LS:=headamp_shape) inp).

Definition ASAN_UBSAN_T : Prop :=
  forall sp brk mbase rnd inp,
  valid_sp sp -> valid_brk AsanUbsan.M.loaded_segments brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes AsanUbsan.M.loaded_segments
    (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd
       target_alloc_limit inp)
    (SPECX (LS:=headamp_shape) inp).

Theorem asan_agrees_of_asan_side : PLAIN_SLOT_AG -> ASAN_T -> Statements.asan_agrees.
Proof.
  intros PS TFIB. unfold Statements.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (headamp_plain_rz PS en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=headamp_shape) inp) (SPECX (LS:=headamp_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem asan_ubsan_agrees_of_asan_side : PLAIN_SLOT_AG -> ASAN_UBSAN_T -> Statements.asan_ubsan_agrees.
Proof.
  intros PS TFIB. unfold Statements.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (headamp_plain_rz PS en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=headamp_shape) inp) (SPECX (LS:=headamp_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

(* The halting statements (Budgets.Standard.lim_source) from the same obligations, in the shape of cgif_file_fuzzer's
   lib/Halts_tfib.v:32-40 (which applies halts_budgets_of_realizes to tfib_realizesX): halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over ASAN_T / ASAN_UBSAN_T and
   SPECX_shape_ok (A/HaltsSpecH.v). *)
Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Theorem asan_halts_of_asan_side : ASAN_T -> Statements.asan_halts.
Proof.
  intros TFIB. unfold Statements.asan_halts, Images.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused Asan.M.loaded_segments Asan.M.init_pc
    Asan.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=headamp_shape) inp). split.
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
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=headamp_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.

About asan_agrees_of_asan_side.
About asan_ubsan_agrees_of_asan_side.
About asan_halts_of_asan_side.
About asan_ubsan_halts_of_asan_side.
Print Assumptions asan_agrees_of_asan_side.
Print Assumptions asan_ubsan_agrees_of_asan_side.
Print Assumptions asan_halts_of_asan_side.
Print Assumptions asan_ubsan_halts_of_asan_side.
