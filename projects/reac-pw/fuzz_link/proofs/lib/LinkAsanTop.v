(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v (and its fuzz_grant form,
   a working branch lib/A/AsanTop.v, and its fuzz_scene form, a working branch e624b1e2c9a lib/A/SceneAsanTop.v)
   for fuzz_pcap: the plain side is fuzz_pcap's released realization (built as its lib/AgreeFrameO.v builds it for the
   ubsan agreement, at AgreePcap.ag_out_shape), module paths changed. Moved from lib/A/ to the lib/ root, where the
   donor keeps the file that names both ASan images (proofs/cgif/cgif_file_fuzzer/lib/Theorems.v): it is Required by
   the asan closer lib/A/PcapClose.v and by the asan-ubsan closer lib/B/PcapCloseB.v. *)
(* fuzz_link's asan_agrees and asan_halts, each from ONE ASan-side obligation, in the form of the file named above:
   - ASAN_T: from every valid start, the ASan build realizes, with no cut (Reusable/YK18.v srealizes), the trace set
     SPECX at link_shape, the library shape of the ASan driver's statement (lib/ZTraceSpec.v checksum_shape: each
     call returns 0 and writes nothing);
   - the plain side is fuzz_link's plain realization of SPECX at 2^34 (lib/AgreeTop.v plain_rz_of_contracts_R) at
     the frame's own instance, built as lib/FrameSlotMF.v builds plain_halts (shape mf_shape, resource invariant
     RI_mf, the slot's G and GI of lib/Prog/Slot/LHolds.v), from the plain slot contract
     (lib/Prog/LLVMFuzzerTestOneInput.v LLVMFuzzerTestOneInput_holds, each callee closed as
     lib/Prog/Slot/LTop.v closes plain_halts_holds) and the mwrite contract (lib/Prog/mwrite.v mwrite_proof);
   - mf_shape has checksum_shape's LIBK (lib/MemFileRI.v mf_shape), so the two SPECX are one trace set
     (specx_mf_link, by congruence through run_shape and lib_iter: a direct conversion of the two SPECX unfolds
     the driver's tree and does not finish);
   - shape_strong_equiv_efs_relim (A/YM09.v) brings the plain side down to the statements' 2^31 plain budget,
     whose premise gives the plain run's cut-freedom (A/RelimCut.v);
   - the halting statement from the same obligation, by halts_budgets_of_srealizes (Reusable/HaltsKitB.v) and
     SPECX_shape_ok (A/HaltsSpecL.v).
   The notice above names fuzz_pcap's two closers, lib/A/PcapClose.v and lib/B/PcapCloseB.v. This unit has
   neither, and no lib/B: the one file here that Requires this one is lib/A/LinkClose.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_pw.fuzz_link Require Statements Images.
From OSSVerify.reac_pw.fuzz_link.images Require Plain Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YO0i YO0f YO0d YO05 YO09 YO06 YO04
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YP09 HaltsKitB.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK0k.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import
  ZImage TraceHalting TraceHaltingB ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Img0 Contract FrameAPI
  FrameProof FrameSlotG SlotTopR SlotTopG Agree AgreeTop MemFileSink MemFile MemFileRI StdioExitMF MwriteExit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import mwrite_c LLVMFuzzerTestOneInput_c
  reac_link_alias_read_c reac_link_alias_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LHolds.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require LTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require LLVMFuzzerTestOneInput kernel index_of model_talk
  model_decide bcmp memset strcmp strlen snprintf snprintf_img check_socket check_refused check_bounds check_read
  check_write check_requests check_marks check_verdict reac_served_unmark_all mwrite reac_link_alias_read
  reac_link_alias_write memcpy.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import HaltsSpecL YM09.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Definition link_shape : lib_shape := ZTraceSpec.checksum_shape.

(* The plain side. *)
(* The netlink alias reader and writer, closed as lib/Prog/Slot/LTop.v closes them in plain_halts_holds. *)
Lemma link_alias_read_closed : reac_link_alias_read_contract.
Proof.
  exact (reac_link_alias_read.reac_link_alias_read_holds index_of.fuzz_if_nametoindex_holds memset.memset_holds
    LTop.nl_talk_closed).
Qed.
Lemma link_alias_write_closed : reac_link_alias_write_contract.
Proof.
  exact (reac_link_alias_write.reac_link_alias_write_holds index_of.fuzz_if_nametoindex_holds strlen.strlen_holds
    memset.memset_holds memcpy.memcpy_holds LTop.nl_talk_closed).
Qed.

(* The plain slot contract at the frame's own instance (src0_msyms, zlib_API, src0_sink_head, src0_sink), with the
   callee contracts lib/Prog/Slot/LTop.v plain_halts_of_lib passes to plain_halts_of_callees, in the same order. *)
Lemma link_plain_slot : LLVMFuzzerTestOneInput_contract src0_msyms (@zlib_API) src0_sink_head src0_sink.
Proof.
  exact (LLVMFuzzerTestOneInput.LLVMFuzzerTestOneInput_holds
    kernel.kernel_holds
    (model_talk.model_read_holds_talk index_of.index_of_holds)
    (model_talk.model_write_holds_talk index_of.index_of_holds)
    model_decide.model_decide_closed
    bcmp.bcmp_holds memset.memset_holds strcmp.strcmp_holds strlen.strlen_holds
    snprintf.snprintf_holds snprintf_img.snprintf_img_holds index_of.index_of_holds
    link_alias_read_closed link_alias_write_closed
    (reac_served_unmark_all.reac_served_unmark_all_closed link_alias_read_closed link_alias_write_closed)
    model_decide.reac_served_decide_closed
    check_socket.check_socket_holds check_refused.check_refused_holds check_bounds.check_bounds_holds
    check_read.check_read_holds check_write.check_write_holds check_requests.check_requests_holds
    check_marks.check_marks_holds check_write.check_mark_holds check_verdict.check_verdict_holds
    src0_msyms (@zlib_API) src0_sink_head src0_sink
    LTop.text_buf_src0 LTop.text_of_src0 (LTop.mark_quietly_src0 link_alias_read_closed link_alias_write_closed)).
Qed.

(* The plain realization of SPECX at mf_shape, as lib/FrameSlotMF.v plain_halts_of_frame_slot_mf_mwrite reaches
   plain_halts: the R form of the slot contract through RI_mf's step, the mwrite contract through
   MwriteExit.v mwrite_exit_of_contract, and lib/Prog/Slot/LHolds.v's G / GI facts. *)
Lemma link_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=mf_shape) inp).
Proof.
  apply (plain_rz_of_contracts_R mf_shape RI_mf llvm_G frame_RELRO (llvm_GI src0_msyms) (fun _ => [])
    driver_RI_mf (fun a h => frame_G_src0 a (llvm_G_frame a h)) frame_RELRO_src0
    llvm_GI_local llvm_GI_init llvm_GI_mf).
  intros rc. exists (@zlib_API rc).
  split; [apply zlib_allocator_extra|].
  split; [exact (mwrite_exit_of_contract (rc:=rc) (@zlib_API rc) zlib_allocator_extra mwrite.mwrite_proof)|].
  apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) RI_mf llvm_G frame_RELRO (llvm_GI src0_msyms)
    (fun _ => []) ENTRY RA_LIB EMPTY SLOT_STACK (RI_mf_step src0_msyms link_mf (llvm_GI src0_msyms) llvm_GI_mf)).
  intros fx j Hj. exact (link_plain_slot RA_LIB EMPTY frame_facts_src0 rc fx j Hj).
Qed.

(* mf_shape and link_shape have the same LIBK; they differ only in lib_room, which SPECX does not read. *)
Lemma LIBK_mf_link : forall pl fs K, @LIBK mf_shape pl fs K = @LIBK link_shape pl fs K.
Proof. reflexivity. Qed.
Lemma lib_iter_mf_link : forall pl j K fs,
  t_eq (lib_iter (LS:=mf_shape) pl j K fs) (lib_iter (LS:=link_shape) pl j K fs).
Proof.
  intros pl j K. induction j as [|j IH]; intros fs; cbn [lib_iter].
  - apply t_eq_refl.
  - rewrite LIBK_mf_link. apply (@LIBK_ext link_shape). intros l. cbv beta. apply IH.
Qed.
Lemma run_shape_mf_link : forall pl k fs,
  t_eq (run_shape (LS:=mf_shape) pl k fs) (run_shape (LS:=link_shape) pl k fs).
Proof.
  intros pl [|k] fs; cbn [run_shape].
  - apply t_eq_refl.
  - rewrite LIBK_mf_link. apply (@LIBK_ext link_shape). intros l. cbv beta. unfold YO05.wr.
    apply YK0k.t_emit_cong. apply lib_iter_mf_link.
Qed.
Lemma leaf_shapeX_mf_link : forall data fs r,
  t_eq (leaf_shapeX (LS:=mf_shape) data fs r) (leaf_shapeX (LS:=link_shape) data fs r).
Proof.
  intros data fs [d s]. unfold leaf_shapeX. cbn [fst]. destruct d; try apply t_eq_refl; apply run_shape_mf_link.
Qed.
Lemma specx_mf_link : forall inp, t_eq (SPECX (LS:=mf_shape) inp) (SPECX (LS:=link_shape) inp).
Proof.
  intros inp. unfold SPECX, SPECX_args.
  destruct (in_argv inp) as [|a0 [|p [|x l]]]; [apply t_eq_refl | apply t_eq_refl | | apply t_eq_refl].
  destruct (classify_open p (in_fs inp)) as [| |data]; [apply t_eq_refl | apply t_eq_refl |].
  apply YM02.t_alt2_congr; [apply t_eq_refl|].
  unfold SPECX_loaded. apply YM02.tset_congr. intros r. apply leaf_shapeX_mf_link.
Qed.

(* Sink guard: from here on, no sink head, sink symbols or sink laws may be resolved implicitly from the plain
   build's instances (the plain side above passes them by name). Inert today: no term below resolves them by
   inference; it protects later edits of the files that load this one. *)
#[global] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable.YI5c.src0_sink : typeclass_instances.
#[global] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[global] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

(* The ASan-side obligation. *)
Definition ASAN_T : Prop :=
  forall sp brk mbase rnd inp,
  valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes Asan.M.loaded_segments
    (init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
    (SPECX (LS:=link_shape) inp).

Theorem asan_agrees_of_asan_side : ASAN_T -> Statements.asan_agrees.
Proof.
  intros TFIB. unfold Statements.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (link_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=mf_shape) inp) (SPECX (LS:=link_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (specx_mf_link inp)).
Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Theorem asan_halts_of_asan_side : ASAN_T -> Statements.asan_halts.
Proof.
  intros TFIB. unfold Statements.asan_halts, Images.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused Asan.M.loaded_segments Asan.M.init_pc
    Asan.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=link_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.

Print Assumptions asan_agrees_of_asan_side.
Print Assumptions asan_halts_of_asan_side.
