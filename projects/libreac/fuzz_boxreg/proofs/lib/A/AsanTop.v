(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_boxreg: the plain side is fuzz_boxreg's proved realization (built as its lib/Prog/LLVMFuzzerTestOneInput_agree.v and lib/AgreeFrame.v build it, at box_shape), the halting corollary takes srealizes, module paths changed. Section b (the two ASan+UBSan statements) is fuzz_decode's (a working branch 21b040f5808, lib/A/AsanTop.v) with its unit names changed. *)
(* fuzz_boxreg's four ASan statements from the ASan side TFIB_T and the ASan+UBSan side TFIB_TB (BoxTFIB.v), in
   the form of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/YZ03.v (agreement) and lib/Halts_tfib.v (halting):
   - asan_agrees, asan_ubsan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved
     realization of SPECX at 2^34 (lib/AgreeTop.v plain_rz_of_contracts_R, with the plain entry-function contract of
     the ubsan agreement, lib/Prog/LLVMFuzzerTestOneInput_gfr.v boxreg_slot_g_frame, at box_shape), the statement's
     plain budget premise, TFIB_T (TFIB_TB) and t_eq_refl;
   - asan_halts, asan_ubsan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_T (TFIB_TB) and
     SPECX_shape_ok (HaltsSpecB.v).
   Statement-level names are written with their full module paths. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_boxreg Require Statements Images.
From OSSVerify.libreac.fuzz_boxreg.images Require Plain Asan AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YM09 YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots HaltsKitB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeZlib SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Statement LLVMFuzzerTestOneInput_gfr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import BoxShape BoxTFIB HaltsSpecB.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YK11.fx0.
(* Guard, as lib/A/Prog/BoxPa.v:21 (a Theorem Labs lane's sweep 04:33Z, a Theorem Labs lane's sweep/results.md
   line 99): this file does not Require BoxPa, so without this line a plain-class argument left to instance search
   here would silently take the PLAIN build's sink values (0x4ed20). The plain side below names src0_sink_head /
   src0_sink EXPLICITLY (box_plain_rz, :56), which hint removal does not touch. *)
(* global on purpose: keeps the plain sink instances out of every importer of this file (knock-case defect, a Theorem Labs lane's 06:30Z sweep; a Theorem Labs lane 10:42Z) *)
#[global] Remove Hints YI5b.src0_sink_head YI5c.src0_sink YI5c.src0_sink_laws : typeclass_instances.

Module PS := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.Statement.
Module PG := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.LLVMFuzzerTestOneInput_gfr.
Module ST := OSSVerify.libreac.fuzz_boxreg.Statements.
Module IM := OSSVerify.libreac.fuzz_boxreg.Images.
Module IP := OSSVerify.libreac.fuzz_boxreg.images.Plain.
Module IA := OSSVerify.libreac.fuzz_boxreg.images.Asan.
Module IAU := OSSVerify.libreac.fuzz_boxreg.images.AsanUbsan.

(* The plain side: as lib/Prog/LLVMFuzzerTestOneInput_agree.v and lib/AgreeFrame.v build it for the ubsan agreement,
   at box_shape (A/BoxShapeAg.v: box_shape = ag_shape kept_shape). *)
Lemma box_room_calls : forall n k, @room_calls box_shape n k SBD_AG.
Proof.
  intros n k. induction k as [|k IH]; cbn [room_calls]; [exact I|].
  split; [|exact IH]. cbn. unfold SBD_AG. cbn. lia.
Qed.

Lemma box_room_llvm : forall b n, @lib_room box_shape b n -> llvm_room b.
Proof. intros b n (H1 & H2 & H3). cbn in *. unfold llvm_room. unfold CAP_AG, CAPMAX in *. lia. Qed.

Lemma box_plain_rz : forall en inp, valid_entry IM.plain en inp -> valid_input inp ->
  rz_run IM.plain Budgets.Standard.lim_source en inp (SPECX (LS:=box_shape) inp).
Proof.
  assert (Hp : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc box_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      llvm_G frame_RELRO llvm_GI j ENTRY RA_LIB EMPTY SLOT_STACK).
  { apply PG.boxreg_slot_g_frame.
    - intros pl fs K. reflexivity.
    - exact box_room_llvm.
    - intros n b. reflexivity. }
  assert (HROOMp : forall data, @room_calls box_shape (payload_len data) (calls data) SBD_AG)
    by (intros data; apply box_room_calls).
  assert (HC : zlib_runtime_contracts_R box_shape (@RI_G box_shape) llvm_G frame_RELRO
    (fun j T m => T = [] /\ llvm_GI j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G box_shape) llvm_G frame_RELRO _ (fun _ => [])
      LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step box_shape llvm_GI)).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) llvm_G frame_RELRO llvm_GI (fun _ => []) j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) llvm_G frame_RELRO llvm_GI j
        LIBPC RA_LIB EMPTY LIB_STACK (Hp rc fx j Hj))). }
  exact (plain_rz_of_contracts_R box_shape (@RI_G box_shape) llvm_G frame_RELRO
    (fun j T m => T = [] /\ llvm_GI j m) (fun _ => [])
    (driver_RI_AG box_shape HROOMp) (fun a h => frame_G_src0 a (PS.llvm_G_inside a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs llvm_G llvm_GI (PS.llvm_GI_local src0_msyms))
    (fun mem H => conj eq_refl (PS.llvm_GI_img src0_msyms mem H)) HC).
Qed.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Section a.
Hypothesis TFIB : TFIB_T.

Theorem box_asan_agrees_of_tfib : ST.asan_agrees.
Proof.
  unfold ST.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (box_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold IM.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    IP.M.loaded_segments IP.M.init_pc IP.M.phdrs sp brk mb rnd
    boxsegs0 IA.M.init_pc IA.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=box_shape) inp) (SPECX (LS:=box_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem box_asan_halts_of_tfib : ST.asan_halts.
Proof.
  unfold ST.asan_halts, IM.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage boxsegs0 IA.M.init_pc IA.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused boxsegs0 IA.M.init_pc IA.M.phdrs
    target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=box_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End a.

Section b.
Hypothesis TFIBB : TFIB_TB.

Theorem box_asan_ubsan_agrees_of_tfib : ST.asan_ubsan_agrees.
Proof.
  unfold ST.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (box_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold IM.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    IP.M.loaded_segments IP.M.init_pc IP.M.phdrs sp brk mb rnd
    boxsegsB0 IAU.M.init_pc IAU.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=box_shape) inp) (SPECX (LS:=box_shape) inp) inp
    asan_lim_source_le SWB HP (TFIBB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem box_asan_ubsan_halts_of_tfib : ST.asan_ubsan_halts.
Proof.
  unfold ST.asan_ubsan_halts, IM.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage boxsegsB0 IAU.M.init_pc IAU.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused boxsegsB0 IAU.M.init_pc
    IAU.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=box_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIBB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End b.
