(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v (agreement) and lib/Halts_tfib.v (halting), by way of proofs/libreac/fuzz_grant/lib/A/AsanTop.v, for fuzz_command's ASan statements: the plain side is fuzz_command's released realization built as lib/AgreeFrame.v builds it from lib/AgreeCmd.v's slot, brought to the statement's plain budget by shape_strong_equiv_efs_relim; the halting proof takes srealizes (halts_budgets_of_srealizes); names and module paths changed. *)
(* fuzz_command's two ASan statements from the ASan side TFIB_T (CmdTFIB.v), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v (agreement) and lib/Halts_tfib.v (halting):
   - asan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved realization of SPECX
     at 2^34 (lib/AgreeTop.v plain_rz_of_contracts_R, with the plain slot of the ubsan agreement, lib/AgreeCmd.v
     ag_slot, at cmd_shape), the statement's plain budget premise, TFIB_T and t_eq_refl;
   - asan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_T and SPECX_shape_ok (HaltsSpecC.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.plugin_hostd.fuzz_command Require Statements Images.
From OSSVerify.plugin_hostd.fuzz_command.images Require Plain Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YM09 YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots HaltsKitB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG FrameProof SlotTopG
  Agree AgreeTop AgreeZlib SlotAgree AgreeShape.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require AgreeCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Slot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import CmdShape CmdTFIB HaltsSpecC.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

(* The plain side: as lib/AgreeFrame.v (ubsan_agrees_of_slots) builds it from the ingredients lib/AgreeCmd.v gives
   it (the AG slot ag_slot with ag_given_src0, the AG globals G_cmd and GI_cmd, ag_room_calls), at
   cmd_shape = ag_shape checksum_shape. *)
Lemma cmd_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=cmd_shape) inp).
Proof.
  assert (Hp : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc cmd_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      AG.Slot.G_cmd frame_RELRO AG.Slot.GI_cmd j ENTRY RA_LIB EMPTY SLOT_STACK).
  { intros rc fx j Hj.
    exact (AgreeCmd.ag_slot src0_msyms (@zlib_API) cmd_shape src0_sink_head src0_sink RA_LIB EMPTY
      AgreeCmd.ag_given_src0 AgreeCmd.debruijn_len_src0 rc fx j Hj). }
  assert (HROOMp : forall data, @room_calls cmd_shape (payload_len data) (calls data) SBD_AG)
    by (intros data; exact (ag_room_calls checksum_shape _ _)).
  assert (HG : forall a, in_globals AG.Slot.G_cmd a -> in_globals frame_G a) by (intros a Ha; exact Ha).
  assert (GIL : G_local_c src0_msyms AG.Slot.G_cmd AG.Slot.GI_cmd)
    by exact (AG.Slot.GI_cmd_local src0_msyms ms_segs_rsegs).
  assert (GI0 : forall mem, G_img_c src0_msyms AG.Slot.G_cmd mem -> AG.Slot.GI_cmd 0%nat mem)
    by exact (AG.Slot.GI_cmd_img src0_msyms ms_segs_rsegs).
  assert (HC : zlib_runtime_contracts_R cmd_shape (@RI_G cmd_shape) AG.Slot.G_cmd frame_RELRO
    (fun j T m => T = [] /\ AG.Slot.GI_cmd j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G cmd_shape) AG.Slot.G_cmd frame_RELRO _
      (fun _ => []) LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step cmd_shape AG.Slot.GI_cmd)).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) AG.Slot.G_cmd frame_RELRO AG.Slot.GI_cmd (fun _ => []) j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) AG.Slot.G_cmd frame_RELRO AG.Slot.GI_cmd j
        LIBPC RA_LIB EMPTY LIB_STACK (Hp rc fx j Hj))). }
  exact (plain_rz_of_contracts_R cmd_shape (@RI_G cmd_shape) AG.Slot.G_cmd frame_RELRO
    (fun j T m => T = [] /\ AG.Slot.GI_cmd j m) (fun _ => [])
    (driver_RI_AG cmd_shape HROOMp) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs AG.Slot.G_cmd AG.Slot.GI_cmd GIL) (fun mem H => conj eq_refl (GI0 mem H)) HC).
Qed.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Section a.
Hypothesis TFIB : TFIB_T.

Theorem cmd_asan_agrees_of_tfib : Statements.asan_agrees.
Proof.
  unfold Statements.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (cmd_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    cmdsegs0 Asan.M.init_pc Asan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=cmd_shape) inp) (SPECX (LS:=cmd_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem cmd_asan_halts_of_tfib : Statements.asan_halts.
Proof.
  unfold Statements.asan_halts, Images.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage cmdsegs0 Asan.M.init_pc Asan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused cmdsegs0 Asan.M.init_pc Asan.M.phdrs
    target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=cmd_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End a.
