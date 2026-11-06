(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_scene/lib/A/SceneAsanTop.v
   (a working branch e624b1e2c9a) for fuzz_disco: the plain side is fuzz_disco's released realization
   (built as its lib/AgreeFrame.v builds it for the ubsan agreement, with the plain entry-function contract
   Prog/DiscoEnd.v slot_ok at the arguments lib/DiscoAgree.v gives it), at the shape of that agreement,
   ag_shape checksum_shape; module paths changed. *)
(* fuzz_disco's four ASan statements, each from ONE ASan-side obligation per image, in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v:
   - ASAN_T / ASAN_UBSAN_T: from every valid start, the ASan (ASan+UBSan) build realizes, with no cut
     (Reusable/YK18.v srealizes), the trace set SPECX at the shape of the released agreement (AZ03.v:20-26 TFIB_T);
   - the plain side is the released plain realization of SPECX at 2^34 (lib/AgreeTop.v plain_rz_of_contracts_R, with
     the released plain entry-function contract of the ubsan agreement, Prog/DiscoEnd.v slot_ok), used unchanged;
   - shape_strong_equiv_efs_relim (Reusable/YM09.v) brings the plain side down to the statements' 2^31 plain budget,
     whose premise gives the plain run's cut-freedom (A/RelimCut.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_disco Require Statements Images.
From OSSVerify.libreac.fuzz_disco.images Require Plain Asan AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require FrameProof SlotTopG.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require LLVMFuzzerTestOneInput_c DiscoEnd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YM09 YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots HaltsKitB.
(* The plain sink instances YI5b.src0_sink_head (class YI16.sink_head) and YI5c.src0_sink (class YI14.sink_syms) are
   #[global] Instances, in scope in every file that Requires this one. Both are removed here for this file and every
   file that Requires it, so no sink instance is inferred in an ASan file; the plain slot call passes both explicitly. *)
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
#[global] Remove Hints YI5c.src0_sink : typeclass_instances.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeZlib AgreeShape.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import HaltsSpecD.
(* Removes the plain image's sink and shape instances (Reusable/PlainHintsOff.v): the plain side below gives them explicitly. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require PlainHintsOff.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Definition disco_shape : lib_shape := ag_shape checksum_shape.

(* The plain side: as lib/AgreeFrame.v builds it for the ubsan agreement, with DiscoAgree.v's G = [], GI = disco_GI. *)
Lemma disco_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=disco_shape) inp).
Proof.
  assert (HROOMp : forall data, @room_calls disco_shape (payload_len data) (calls data) SBD_AG)
    by (intros data; exact (ag_room_calls checksum_shape _ _)).
  assert (HG : forall a, in_globals [] a -> in_globals frame_G a) by (intros a (lo & len & [] & _)).
  assert (GIL : G_local_c src0_msyms [] lib.Prog.LLVMFuzzerTestOneInput_c.disco_GI) by (intros j m m' _ _; exact I).
  assert (GI0 : forall mem, G_img_c src0_msyms [] mem -> lib.Prog.LLVMFuzzerTestOneInput_c.disco_GI 0%nat mem)
    by (intros mem _; exact I).
  assert (HC : zlib_runtime_contracts_R disco_shape (@RI_G disco_shape) [] frame_RELRO
    (fun j T m => T = [] /\ lib.Prog.LLVMFuzzerTestOneInput_c.disco_GI j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G disco_shape) [] frame_RELRO _ (fun _ => [])
      LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step disco_shape lib.Prog.LLVMFuzzerTestOneInput_c.disco_GI)).
    intros fx j Hj.
    pose proof (Prog.DiscoEnd.slot_ok src0_msyms (@zlib_API) disco_shape src0_sink_head src0_sink
      RA_LIB EMPTY lib.SlotTopG.ms_segs_rsegs ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl eq_refl
      lib.FrameProof.errno_below_ceiling eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(split; vm_compute; reflexivity)
      lib.FrameProof.ctx_not_ro lib.FrameProof.frame_G_facts lib.FrameProof.frame_RELRO_facts (fun pl fs K => eq_refl)
      (fun n b => eq_refl) (ag_room_g checksum_shape) lib.FrameProof.zlib_frame_allocator rc fx j Hj) as HS.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) [] frame_RELRO lib.Prog.LLVMFuzzerTestOneInput_c.disco_GI
      (fun _ => []) j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) [] frame_RELRO
        lib.Prog.LLVMFuzzerTestOneInput_c.disco_GI j
        LIBPC RA_LIB EMPTY LIB_STACK HS)). }
  exact (plain_rz_of_contracts_R disco_shape (@RI_G disco_shape) [] frame_RELRO
    (fun j T m => T = [] /\ lib.Prog.LLVMFuzzerTestOneInput_c.disco_GI j m) (fun _ => [])
    (driver_RI_AG disco_shape HROOMp) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs [] lib.Prog.LLVMFuzzerTestOneInput_c.disco_GI GIL)
    (fun mem H => conj eq_refl (GI0 mem H)) HC).
Qed.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

(* The ASan-side obligations (cgif_file_fuzzer lib/A/AZ03.v:20-26 TFIB_T, for fuzz_disco's images and shape). *)
Definition ASAN_T : Prop :=
  forall sp brk mbase rnd inp,
  valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes Asan.M.loaded_segments
    (init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
    (SPECX (LS:=disco_shape) inp).

Definition ASAN_UBSAN_T : Prop :=
  forall sp brk mbase rnd inp,
  valid_sp sp -> valid_brk AsanUbsan.M.loaded_segments brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes AsanUbsan.M.loaded_segments
    (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd
       target_alloc_limit inp)
    (SPECX (LS:=disco_shape) inp).

Theorem asan_agrees_of_asan_side : ASAN_T -> Statements.asan_agrees.
Proof.
  intros TFIB. unfold Statements.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (disco_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=disco_shape) inp) (SPECX (LS:=disco_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem asan_ubsan_agrees_of_asan_side : ASAN_UBSAN_T -> Statements.asan_ubsan_agrees.
Proof.
  intros TFIB. unfold Statements.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (disco_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=disco_shape) inp) (SPECX (LS:=disco_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

(* The halting statements (Budgets.Standard.lim_source) from the same obligations, as cgif_file_fuzzer's
   lib/Halts_tfib.v does: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over ASAN_T / ASAN_UBSAN_T and
   SPECX_shape_ok (A/HaltsSpecD.v). *)
Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Theorem asan_halts_of_asan_side : ASAN_T -> Statements.asan_halts.
Proof.
  intros TFIB. unfold Statements.asan_halts, Images.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused Asan.M.loaded_segments Asan.M.init_pc
    Asan.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=disco_shape) inp). split.
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
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=disco_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.

Print Assumptions asan_agrees_of_asan_side.
Print Assumptions asan_ubsan_agrees_of_asan_side.
Print Assumptions asan_halts_of_asan_side.
Print Assumptions asan_ubsan_halts_of_asan_side.
