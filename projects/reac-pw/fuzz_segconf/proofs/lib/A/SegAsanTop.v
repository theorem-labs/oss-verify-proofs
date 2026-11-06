(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v (agreement) and lib/Halts_tfib.v (halting), by way of proofs/libreac/fuzz_grant/lib/A/AsanTop.v, for fuzz_command's ASan statements: the plain side is fuzz_command's released realization built as lib/AgreeFrame.v builds it from lib/AgreeCmd.v's slot, brought to the statement's plain budget by shape_strong_equiv_efs_relim; the halting proof takes srealizes (halts_budgets_of_srealizes); names and module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AsanTop.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; cmd_shape -> seg_shape, CmdShape / CmdTFIB / HaltsSpecC -> SegShape / SegTFIB / HaltsSpecS, cmd_ -> seg_ in the lemma names; the plain side's slot is segconf's plain lane's lib/AgreeSeg.v plain_slot_ag (commit cfdd99183965, lines 51-64: the plain slot at ag_shape checksum_shape over the plain segment lemmas), taken as a Section hypothesis of exactly its statement in place of lib/AgreeCmd.v's ag_slot (the plain tree that holds it is merged at the close's last step); its G and GI are segconf's frame_G and SlotFR.GI_SLOT (longl[120] = 0), whose G_local_c / G_img_c facts are proved as lib/AgreeSeg.v proves them. *)
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
From OSSVerify.reac_pw.fuzz_segconf Require Statements Images.
From OSSVerify.reac_pw.fuzz_segconf.images Require Plain Asan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YM09 YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots HaltsKitB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG FrameProof SlotTopG
  Agree AgreeTop AgreeZlib SlotAgree AgreeShape.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotFR SlotInv.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Tac_slot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import SegShape SegTFIB HaltsSpecS.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

(* The plain side: as lib/AgreeFrame.v (ubsan_agrees_of_slots) builds it from the ingredients lib/AgreeCmd.v gives
   it (the AG slot ag_slot with ag_given_src0, the AG globals G_cmd and GI_cmd, ag_room_calls), at
   cmd_shape = ag_shape checksum_shape. *)
Section p.
(* segconf: the plain slot of segconf's ubsan agreement at the agreement shape, in the place of lib/AgreeCmd.v's
   ag_slot: G = frame_G (longl), GI = SlotFR.GI_SLOT. plain_slot_ag below is lib/AgreeSeg.v:51-58's statement at
   commit cfdd99183965, byte for byte (with that file's abbreviation AGS), a Section hypothesis until the
   plain tree is merged; AgreeSeg proves it from Prog/SegSlotAG.slot_of_lemmas_ag. *)
Local Abbreviation AGS := (ag_shape checksum_shape).
Hypothesis plain_slot_ag : forall CP : cut_preds,
  (forall (fx : FPState) (rc : RunCeil),
     OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.LLVMFuzzerTestOneInput_c.seg_lemmas
       src0_msyms (@zlib_API) RA_LIB EMPTY CP) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_g fx rc AGS src0_msyms (@zlib_API rc) src0_sink_head src0_sink frame_G frame_RELRO
    (GI_SLOT (ms_segs src0_msyms)) j ENTRY RA_LIB EMPTY SLOT_STACK.
(* the plain segment lemmas at the concrete instance and a cut record, plain_slot_ag's premise (Prog/SegEnd.segs_holds
   over the plain walks' segment statements, at the walks' cut record) *)
Variable CPp : cut_preds.
Hypothesis plain_segs : forall (fx : FPState) (rc : RunCeil),
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.LLVMFuzzerTestOneInput_c.seg_lemmas
    src0_msyms (@zlib_API) RA_LIB EMPTY CPp.
Lemma seg_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=seg_shape) inp).
Proof.
  assert (HROOMp : forall data, @room_calls seg_shape (payload_len data) (calls data) SBD_AG)
    by (intros data; exact (ag_room_calls checksum_shape _ _)).
  assert (GIL : G_local_c src0_msyms frame_G (SlotFR.GI_SLOT (ms_segs src0_msyms))).
  { intros j m m' Hm HG. unfold SlotFR.GI_SLOT, SlotFR.GIb in *. rewrite (Hm _ Tac_slot.sl_longl_nul_in). exact HG. }
  assert (GI0 : forall mem, G_img_c src0_msyms frame_G mem -> SlotFR.GI_SLOT (ms_segs src0_msyms) 0%nat mem).
  { intros mem Himg. unfold SlotFR.GI_SLOT, SlotFR.GIb. rewrite (Himg _ Tac_slot.sl_longl_nul_in).
    exact Tac_slot.sl_longl_nul. }
  assert (HC : zlib_runtime_contracts_R seg_shape (@RI_G seg_shape) frame_G frame_RELRO
    (fun j T m => T = [] /\ SlotFR.GI_SLOT (ms_segs src0_msyms) j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G seg_shape) frame_G frame_RELRO _
      (fun _ => []) LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step seg_shape (SlotFR.GI_SLOT (ms_segs src0_msyms)))).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) frame_G frame_RELRO (SlotFR.GI_SLOT (ms_segs src0_msyms))
      (fun _ => []) j LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) frame_G frame_RELRO
        (SlotFR.GI_SLOT (ms_segs src0_msyms)) j LIBPC RA_LIB EMPTY LIB_STACK (plain_slot_ag CPp plain_segs rc fx j Hj))). }
  exact (plain_rz_of_contracts_R seg_shape (@RI_G seg_shape) frame_G frame_RELRO
    (fun j T m => T = [] /\ SlotFR.GI_SLOT (ms_segs src0_msyms) j m) (fun _ => [])
    (driver_RI_AG seg_shape HROOMp) (fun a h => frame_G_src0 a h) frame_RELRO_src0
    (G_local_T_of_G src0segs frame_G (SlotFR.GI_SLOT (ms_segs src0_msyms)) GIL) (fun mem H => conj eq_refl (GI0 mem H)) HC).
Qed.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Section a.
Hypothesis TFIB : TFIB_T.

Theorem seg_asan_agrees_of_tfib : Statements.asan_agrees.
Proof.
  unfold Statements.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (seg_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    segsegs0 Asan.M.init_pc Asan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=seg_shape) inp) (SPECX (LS:=seg_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem seg_asan_halts_of_tfib : Statements.asan_halts.
Proof.
  unfold Statements.asan_halts, Images.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage segsegs0 Asan.M.init_pc Asan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused segsegs0 Asan.M.init_pc Asan.M.phdrs
    target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=seg_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End a.
End p.
