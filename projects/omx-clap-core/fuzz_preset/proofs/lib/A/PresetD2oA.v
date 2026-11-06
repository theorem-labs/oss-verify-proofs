(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from TFIB_T_of_partsXF of proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v:29-85
   (the donor's asan image; its lib/YD2o.v:24-80 twin is the asan-ubsan one) for fuzz_preset's asan image. This file and
   lib/AU/PresetD2oB.v are the same text except for the image's segment list, symbol-record facts, relro names, interface file
   and TFIB statement.
   It states the ASSEMBLY of the closed ASan-side walk: from the program's function walks (the callee contracts and the
   harness walk of LLVMFuzzerTestOneInput) and the payload-room bridge, the asan build realizes SPECX from every
   valid start whose plain run is never refused at the agreement's budget (lib/A/PresetTFIB.v TFIB_T).
   Nothing in this file is a proof of a function (rule 24: no function proved; this is the composition / driver layer
   of a port).
   Changes from the donor's Section b (closedwalk-plan.md sections 1c, 2f):
   (1) the conclusion is preset's TFIB_T, which carries the plain no-refusal premise (owner ruling 20:25Z);
   (2) cgif's write callback `wfn` and its three library walks (TNEWGIFX / TADDFX / TCLOSEX) are dropped; in their
       place the statement takes the 14 callee contracts of the entry function (PresetCfnA.v section 6, afn_spec_cf)
       and the harness walk preset_lib_x_stmt (PresetCfnA.v section 6, the LLVMFuzzerTestOneInput row of
       PROGRAM-WALKS.md), each at every FPState, the harness walk also at every RunCeil (as the donor's TNEWGIFX),
       with the interface's two frame-area slots filled by h-mani-a8's definitions (lib/Reusable/YG0dcf.v
       astack_malloc_realizes_cf / astack_free_law_cf at CfParams_preset, lib/A/CfParamsPreset.v), in the form the
       closure PresetCfiA (lanes CwCfiA / CwCfiB) consumes;
   (3) cgif's sink is dropped (no sink head, no unlink, no YI0a);
   (4) NEW: the payload-room bridge (closedwalk-plan.md 2f): the plain no-refusal premise gives the program
       interface's PAYLOAD_ROOM for the payload the driver hands to the harness (lib/Reusable/YO06.v payload). The
       text is the driver walk's PROOM premise (lib/AU/PresetD1pB.v, lane CwD1pB);
   (5) the symbol record is a parameter B with its facts TfibSyms B (lib/A/AF0m.v), as in the donor's driver Sections
       (YD1q.v:37-38): the donor fixes TfibB in Section b only because its closed walks were stated at it, and
       preset's record is being restated (closedwalk-plan.md 1c: the alloc.c ledger cells, preset's universe);
   (6) PROVISIONAL (bodies pending, h-mani-a8 / h-hpreset-7): ablocks_cf, afn_pre_cf, ajournal_cf and apost_base_cf
       are universally quantified, with the types of PresetCfnA.v:265-276;
   (7) the relro window is the generated .data.rel.ro start .. .got end of lib/A/AB1w.v; the meter is the trivial one (lib/Reusable/YCbp.v
       ameter_triv) and the per-call meter allowances XM_LIB / XN_LIB are universally quantified (the trivial meter
       never reads them). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetD2oA.v, with its module paths and module names changed; 112 of its 140 lines of code are new or changed and 76 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: made from TFIB_T_of_partsXF of proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v:29-85
   (the donor's asan image; its lib/YD2o.v:24-80 twin is the asan-ubsan one) for fuzz_preset's asan image. This file and
   lib/AU/PresetD2oB.v are the same text except for the image's segment list, symbol record, program listing, interface file,
   loop-lane file and TFIB statement.
   It states the ASSEMBLY of the closed ASan-side walk: from the program's function walks (the callee contracts and the
   harness walk of LLVMFuzzerTestOneInput), the payload-room bridge and the links of the program interface's
   PROVISIONAL vocabulary, the asan build realizes SPECX from every valid start whose plain run is never refused at
   the agreement's budget (lib/A/PresetTFIB.v TFIB_T).
   Nothing in this file is a proof of a function (rule 24: no function proved; this is the composition / driver layer
   of a port).
   Changes from the donor's Section b (the internal file closedwalk-plan.md sections 1c, 2f):
   (1) the conclusion is preset's TFIB_T, which carries the plain no-refusal premise (owner ruling 20:25Z);
   (2) cgif's write callback `wfn` and its three library walks (TNEWGIFX / TADDFX / TCLOSEX) are dropped; in their
       place the statement takes the 14 callee contracts of the entry function (PresetCfnA.v section 6, afn_spec_cf)
       and the harness walk preset_lib_x_stmt (PresetCfnA.v section 6, the LLVMFuzzerTestOneInput row of
       the internal file PROGRAM-WALKS.md), each at every RunCeil and FPState (as the donor's TNEWGIFX), in the form the closure PresetCfiA
       (lanes CwCfiA / CwCfiB) consumes;
   (3) cgif's sink is dropped (no sink head, no unlink, no YI0a);
   (4) NEW: the payload-room bridge (the internal file closedwalk-plan.md 2f): the plain no-refusal premise gives the program
       interface's PAYLOAD_ROOM for the payload the driver hands to the harness (lib/Reusable/YO06.v payload); the
       text of the driver and loop lanes' premise (CwD1pA / CwD1pB, CwLoopA / CwLoopB);
   (5) the symbol record is the core copy's TfibB (lib/A/AD2l.v), as the donor's Section b fixes it, and the program listing
       of the interface's read-only premise is a Theorem Labs lane's A_prog_listing with its image class PI_prog_A (lib/A/PAImg_prog.v), passed
       explicitly;
   (6) on the interface of IfacePort 3f83c075b61f: its frame names (ablocks_cf, afn_pre_cf, ajournal_cf, apost_base_cf)
       are constants and fregs_kept_x is YCbqG's, so neither they nor links to them are premises (the driver walk
       uses the link proofs at the constants itself); the interface's Section v parameters sm (the harness model's)
       and iface_room_np (PROVISIONAL, the non-primary room) are universally quantified, and the three laws of
       iface_room_np that the driver walk takes (PresetCfnA.v section 3b: iface_room_np_init / _step / _tail; owner
       a Theorem Labs lane, bodies from room_live_cf) are premises;
   (7) NO run-level room premise (resume brief 03:48Z, design change 1): the sum `4 * N_LLVMF + 24 <= K_INIT` is
       gone, since `ROOM_cf_k init_state (4 * N_LLVMF + 24)` is unsatisfiable (K_INIT 14,335 against >= 9,696 room per
       call). The run's allocator room is a Theorem Labs lane's P8 (a working branch 4ec915e66b6,
       lib/Spec/PresetP8.v preset_room), a state predicate whose three premises (live = the model's hlive plus at most
       three driver chunks; a8's quar_bytes_ok_cf; fifo_ok by a8's fifo_ok_of_frees_follow from the coupling
       cf_frees_follow, lib/Reusable/YGcfFrees.v) are the interface's iface_room_at, which the driver walk establishes
       at the loop entry and the slot's post carries across each call; none of them is a premise of this assembly;
   (8) the meter is the trivial one (lib/Reusable/YCbp.v ameter_triv) and the per-call meter allowances XM_LIB /
       XN_LIB are universally quantified (the trivial meter never reads them);
   (9) #102 (no-DW interface, PresetCfnA.v, first at commit 8259b94c42ee; on the kit's batch):
       the program part is the interface's callee record preset_callee_contracts and the harness walk
       preset_lib_x_stmt at check_round_trip's two addresses A_MOD_AT / A_STAMP, each at every run ceiling and float
       state, at the image's code record ci := CfImg_A. Gone with the old pins: the fourteen afn_spec_cf records
       F_<f> (their pj_parse / pj_get / pj_get_str are not callees of LLVMFuzzerTestOneInput on #102), the run's data
       words DW and npj, and their bound (the kit's batch: clause 4a / 4b). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO09 YE01 YC5d YM05 YO06 YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AD2l Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetCfnA PresetTFIB.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* ---------------------------------------------------------------------- *)
(* 1. The statement. Donor: A/AD2o.v:83-84 (TFIB_T_of_partsXF : TFIB_T in Section b, whose parts are wfn and the
      three cgif library walks). *)
Definition TFIB_T_of_partsXF_A : Prop :=
forall
(* the interface's Section v parameters (PresetCfnA.v): the harness model's sm and the PROVISIONAL non-primary room *)
(sm : list Z -> Z * Z)
(iface_room_np : astate -> Prop)
(XM_LIB XN_LIB : Z -> Z)
(PAYLOAD_ROOM : list byte -> Prop)
(* check_round_trip's two literal addresses (PresetCfnA.v section 6, preset_lib_x_stmt's arguments) *)
(A_MOD_AT A_STAMP : Z),
(* the three laws of the PROVISIONAL non-primary room that the driver walk takes (PresetCfnA.v section 3b; owner
   a Theorem Labs lane, bodies from room_live_cf), at the image's record CfImg_A (lib/A/CfImgA.v) *)
iface_room_np_init iface_room_np ->
iface_room_np_step (ci := CfImg_A) (cp := CfParams_preset) iface_room_np ->
iface_room_np_tail (cp := CfParams_preset) iface_room_np ->
(* #102: the callee record (PresetCfnA.v section 6: the kit's sixteen texts, the frame-area allocation and its release), at
   every run ceiling and float state, in place of the old pins' fourteen afn_spec_cf records and their data words *)
(forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  preset_callee_contracts (rc := rc) (L := A_prog_listing) (PA := PI_prog_A (rc := rc)) (ci := CfImg_A) (fx := fx)
    TfibB A_MOD_AT A_STAMP) ->
(* the harness walk of LLVMFuzzerTestOneInput (PresetCfnA.v section 6), at every run ceiling and float state *)
(forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  preset_lib_x_stmt (rc := rc) (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
    (L := A_prog_listing) (PA := PI_prog_A (rc := rc)) (ci := CfImg_A) (fx := fx)
    sm iface_room_np TfibB ameter_triv XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP) ->
(* the payload-room bridge (the internal file closedwalk-plan.md 2f) *)
(forall (en_p : ExecEntry) (inp : ProcInput) (a0 p data : list byte),
  ~ run_scfg_budget_refused Shapes.Env.alloc_forced_only Images.plain Shapes.Budgets.Asan.lim_source en_p inp ->
  in_argv inp = [a0; p] -> Fs.fs_lookup (in_fs inp) p = Some data -> PAYLOAD_ROOM (payload data)) ->
TFIB_T.

(* ---------------------------------------------------------------------- *)
(* 2. The ROOM form, for the halts tops (asked by a Theorem Labs lane for A and a Theorem Labs lane for B; owner order 06:0xZ). The
      agrees top's outer premise `~ run_scfg_budget_refused .. Images.plain ..` exists only to give the interface's
      PAYLOAD_ROOM for the payload (the bridge premise of TFIB_T_of_partsXF_A). A halts statement has no plain run,
      so these forms take the payload's room DIRECTLY: the same parts as TFIB_T_of_partsXF_A minus the bridge, and in
      place of the no-refusal premise the room of this input's payload. TFIB_T_room_all_A covers every argv / file
      arm at once (an input whose argv is not [a0; p], or whose p is not in the file system, needs no room: the
      premise is then vacuous); TFIB_T_room_A is its argv = [a0; p], file-present arm. Both are proved in
      PresetD2oAPf.v from the same parts, through the driver walk stated over a premise NR (CwD1pA's
      tfib_drv_main_A) and a Theorem Labs lane's tfib_srealizesX_NR_A_holds (lib/A/PresetD1qNRA.v:82); TFIB_T_of_partsXF_A
      is the instance at the no-refusal NR and does not change. *)
(* init_config reads the FP state at the start-up one, as PresetTFIB.v's TFIB_T does *)
#[local] Existing Instance YK11.fx0.
(* the residual conclusions of the room forms, named so a closed export can state them *)
Definition TFIB_T_room_all_concl_A (PAYLOAD_ROOM : list byte -> Prop) : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk presetsegs0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(forall a0 p data : list byte, in_argv inp = [a0; p] -> Fs.fs_lookup (in_fs inp) p = Some data ->
  PAYLOAD_ROOM (payload data)) ->
srealizes presetsegs0
(init_config presetsegs0 Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).

Definition TFIB_T_room_concl_A (PAYLOAD_ROOM : list byte -> Prop) : Prop :=
forall sp brk mbase rnd inp (a0 p data : list byte),
valid_sp sp -> valid_brk presetsegs0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
in_argv inp = [a0; p] -> Fs.fs_lookup (in_fs inp) p = Some data -> PAYLOAD_ROOM (payload data) ->
srealizes presetsegs0
(init_config presetsegs0 Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).


Definition TFIB_T_room_all_A : Prop :=
forall
(* the interface's Section v parameters (PresetCfnA.v): the harness model's sm and the PROVISIONAL non-primary room *)
(sm : list Z -> Z * Z)
(iface_room_np : astate -> Prop)
(XM_LIB XN_LIB : Z -> Z)
(PAYLOAD_ROOM : list byte -> Prop)
(* check_round_trip's two literal addresses (PresetCfnA.v section 6, preset_lib_x_stmt's arguments) *)
(A_MOD_AT A_STAMP : Z),
(* the three laws of the PROVISIONAL non-primary room that the driver walk takes (PresetCfnA.v section 3b; owner
   a Theorem Labs lane, bodies from room_live_cf), at the image's record CfImg_A (lib/A/CfImgA.v) *)
iface_room_np_init iface_room_np ->
iface_room_np_step (ci := CfImg_A) (cp := CfParams_preset) iface_room_np ->
iface_room_np_tail (cp := CfParams_preset) iface_room_np ->
(* #102: the callee record (PresetCfnA.v section 6: the kit's sixteen texts, the frame-area allocation and its release), at
   every run ceiling and float state, in place of the old pins' fourteen afn_spec_cf records and their data words *)
(forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  preset_callee_contracts (rc := rc) (L := A_prog_listing) (PA := PI_prog_A (rc := rc)) (ci := CfImg_A) (fx := fx)
    TfibB A_MOD_AT A_STAMP) ->
(* the harness walk of LLVMFuzzerTestOneInput (PresetCfnA.v section 6), at every run ceiling and float state *)
(forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  preset_lib_x_stmt (rc := rc) (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
    (L := A_prog_listing) (PA := PI_prog_A (rc := rc)) (ci := CfImg_A) (fx := fx)
    sm iface_room_np TfibB ameter_triv XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP) ->
(* the room for THIS input's payload, given directly (every argv / file arm: if argv is not [a0; p] or p is not in
   the file system, the premise holds vacuously and asks nothing) *)
TFIB_T_room_all_concl_A PAYLOAD_ROOM.

Definition TFIB_T_room_A : Prop :=
forall
(* the interface's Section v parameters (PresetCfnA.v): the harness model's sm and the PROVISIONAL non-primary room *)
(sm : list Z -> Z * Z)
(iface_room_np : astate -> Prop)
(XM_LIB XN_LIB : Z -> Z)
(PAYLOAD_ROOM : list byte -> Prop)
(* check_round_trip's two literal addresses (PresetCfnA.v section 6, preset_lib_x_stmt's arguments) *)
(A_MOD_AT A_STAMP : Z),
(* the three laws of the PROVISIONAL non-primary room that the driver walk takes (PresetCfnA.v section 3b; owner
   a Theorem Labs lane, bodies from room_live_cf), at the image's record CfImg_A (lib/A/CfImgA.v) *)
iface_room_np_init iface_room_np ->
iface_room_np_step (ci := CfImg_A) (cp := CfParams_preset) iface_room_np ->
iface_room_np_tail (cp := CfParams_preset) iface_room_np ->
(* #102: the callee record (PresetCfnA.v section 6: the kit's sixteen texts, the frame-area allocation and its release), at
   every run ceiling and float state, in place of the old pins' fourteen afn_spec_cf records and their data words *)
(forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  preset_callee_contracts (rc := rc) (L := A_prog_listing) (PA := PI_prog_A (rc := rc)) (ci := CfImg_A) (fx := fx)
    TfibB A_MOD_AT A_STAMP) ->
(* the harness walk of LLVMFuzzerTestOneInput (PresetCfnA.v section 6), at every run ceiling and float state *)
(forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  preset_lib_x_stmt (rc := rc) (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
    (L := A_prog_listing) (PA := PI_prog_A (rc := rc)) (ci := CfImg_A) (fx := fx)
    sm iface_room_np TfibB ameter_triv XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP) ->
(* the argv = [a0; p], file-present arm, with its payload's room *)
TFIB_T_room_concl_A PAYLOAD_ROOM.
