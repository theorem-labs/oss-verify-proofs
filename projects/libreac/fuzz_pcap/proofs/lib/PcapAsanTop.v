(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v (and its fuzz_grant form,
   a working branch 0bed23e5b69 lib/A/AsanTop.v, and its fuzz_scene form, a working branch e624b1e2c9a lib/A/SceneAsanTop.v)
   for fuzz_pcap: the plain side is fuzz_pcap's released realization (built as its lib/AgreeFrameO.v builds it for the
   ubsan agreement, at AgreePcap.ag_out_shape), module paths changed. Moved from lib/A/ to the lib/ root, where the
   donor keeps the file that names both ASan images (proofs/cgif/cgif_file_fuzzer/lib/Theorems.v): it is Required by
   the asan closer lib/A/PcapClose.v and by the asan-ubsan closer lib/B/PcapCloseB.v. *)
(* fuzz_pcap's asan_agrees and asan_ubsan_agrees, each from ONE ASan-side obligation, in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v:
   - ASAN_T / ASAN_UBSAN_T: from every valid start, the ASan (ASan+UBSan) build realizes, with no cut
     (Reusable/YK18.v srealizes), the trace set SPECX at the shape of the released agreement (AZ03.v:20-26 TFIB_T);
   - the plain side is the released plain realization of SPECX at 2^34 (lib/AgreeTop.v plain_rz_of_contracts_R, with
     the released plain entry-function contract of the ubsan agreement, AgreePcap.v:74-80 PSlot.slot_contract_ols with
     PHolds.pcap_entry), used unchanged;
   - shape_strong_equiv_efs_relim (A/YM09.v) brings the plain side down to the statements' 2^31 plain budget,
     whose premise gives the plain run's cut-freedom (A/RelimCut.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_pcap Require Statements Images.
From OSSVerify.libreac.fuzz_pcap.images Require Plain Asan AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AgreePcap.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots HaltsKitB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG OutForm FrameSlotO
  Agree AgreeTop AgreeZlib AgreeShape.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalk PInv PSlot PHolds.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import HaltsSpecP YM09.

(* G2 sink guard (a Theorem Labs lane sinksyms-guard.md (sha256 be14cbea8554; internal record)): no SK, sink symbols or sink laws may be resolved implicitly from the plain
   build's instances. Inert today: no term below resolves them by inference; it protects future edits. *)
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI5c.src0_sink : typeclass_instances.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Definition pcap_shape : lib_shape := AgreePcap.ag_out_shape.

(* The stack pointer's window, as both closers use it (lib/A/PcapClose.v, lib/B/PcapCloseB.v). *)
Lemma valid_sp_windowP : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* The plain side: as lib/AgreeFrameO.v builds it for the ubsan agreement, with AgreePcap.v's G = frame_G,
   GI = PInv.GI, f = PWalk.OUT and its plain slot contract (AgreePcap.v:74-80). *)
Lemma pcap_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=pcap_shape) inp).
Proof.
  assert (Hp : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_o fx rc pcap_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      PWalk.OUT frame_G frame_RELRO PInv.GI j ENTRY RA_LIB EMPTY SLOT_STACK).
  { intros rc fx j _.
    exact (@PSlot.slot_contract_ols fx rc src0_msyms (@zlib_API) src0_sink_head src0_sink RA_LIB EMPTY
      AgreePcap.ag_ff_plain pcap_shape PWalk.OUT (fun _ _ _ => eq_refl) (fun _ _ => eq_refl)
      (ag_room_g (out_shape PWalk.OUT))
      (PHolds.pcap_entry rc src0_msyms (@zlib_API) src0_sink_head src0_sink RA_LIB EMPTY AgreePcap.ag_ff_plain)
      PWalk.OUT_big j). }
  assert (HROOMp : forall data, @room_calls pcap_shape (payload_len data) (calls data) SBD_AG)
    by (intros data; exact (ag_room_calls (out_shape PWalk.OUT) _ _)).
  assert (HC : zlib_runtime_contracts_R pcap_shape (@RI_G pcap_shape) frame_G frame_RELRO
    (fun j T m => T = [] /\ PInv.GI j m) PWalk.OUT).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G pcap_shape) frame_G frame_RELRO _ PWalk.OUT
      LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step pcap_shape PInv.GI)).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) frame_G frame_RELRO PInv.GI PWalk.OUT j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_o src0_msyms (@zlib_API rc) (zlib_tables rc) PWalk.OUT frame_G frame_RELRO PInv.GI j
        LIBPC RA_LIB EMPTY LIB_STACK (Hp rc fx j Hj))). }
  exact (plain_rz_of_contracts_R pcap_shape (@RI_G pcap_shape) frame_G frame_RELRO
    (fun j T m => T = [] /\ PInv.GI j m) PWalk.OUT
    (driver_RI_AG pcap_shape HROOMp) frame_G_src0 frame_RELRO_src0
    (G_local_T_of_G src0segs frame_G PInv.GI (PSlot.GI_local src0_msyms eq_refl))
    (fun mem H => conj eq_refl (PSlot.GI_img src0_msyms mem eq_refl H)) HC).
Qed.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

(* The ASan-side obligations (cgif_file_fuzzer lib/A/AZ03.v:20-26 TFIB_T, for fuzz_pcap's images and shape). *)
Definition ASAN_T : Prop :=
  forall sp brk mbase rnd inp,
  valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes Asan.M.loaded_segments
    (init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
    (SPECX (LS:=pcap_shape) inp).

Definition ASAN_UBSAN_T : Prop :=
  forall sp brk mbase rnd inp,
  valid_sp sp -> valid_brk AsanUbsan.M.loaded_segments brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes AsanUbsan.M.loaded_segments
    (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd
       target_alloc_limit inp)
    (SPECX (LS:=pcap_shape) inp).

Theorem asan_agrees_of_asan_side : ASAN_T -> Statements.asan_agrees.
Proof.
  intros TFIB. unfold Statements.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (pcap_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=pcap_shape) inp) (SPECX (LS:=pcap_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem asan_ubsan_agrees_of_asan_side : ASAN_UBSAN_T -> Statements.asan_ubsan_agrees.
Proof.
  intros TFIB. unfold Statements.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (pcap_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=pcap_shape) inp) (SPECX (LS:=pcap_shape) inp) inp
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
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=pcap_shape) inp). split.
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
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=pcap_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.

Print Assumptions asan_agrees_of_asan_side.
Print Assumptions asan_ubsan_agrees_of_asan_side.
Print Assumptions asan_halts_of_asan_side.
Print Assumptions asan_ubsan_halts_of_asan_side.
