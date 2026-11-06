(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from tfib_lib_x_all of proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v:21-141 (asan;
   its asan-ubsan twin is lib/YCfi.v:19-139), for fuzz_preset. This file (asan) and lib/AU/PresetCfiB.v (asan-ubsan)
   state the same closure over their own image (segments and asyms).
   It states the CLOSURE of the harness walk on the ASan side: from the walk of LLVMFuzzerTestOneInput
   (preset_lib_x_stmt, lib/A/PresetCfnA.v) and preset's set of parts to the program slot preset_lib_contract_x_all
   that the composition (PresetD2oA) takes. The proof is in PresetCfiAPf.v. Nothing in this file is a proof of a
   function (rule 24).
   Changes from the donor (closedwalk-plan.md section 1g):
   (1) the parts are preset's, not cgif's: the fourteen callee contracts of PresetCfnA.v section 6 in place of cgif's
       wfn / TNEWGIFX / TADDFX / TCLOSEX, and the frame-area part of the second allocator instance's API (AsanAPI_cf's
       aa_stack_malloc_cf / aa_stack_free_cf, lib/Reusable/YGcfNames.v) over h-mani-a8's DEFINED
       astack_malloc_realizes_cf / astack_free_law_cf (lib/Reusable/YG0dcf.v) at preset's unit parameters
       CfParams_preset (lib/A/CfParamsPreset.v, class set [0; 1; 3]), in place of cgif's class-2
       stack_malloc2_contract;
   (2) dropped: the sink (AIL, AUNLINKX, tfib_ROB, tfib_ro_segs_chk), cgif's meter numbers (XN0 and its five lemmas),
       and every link lemma whose consumer was cgif's harness walk (preset's walk states its own needs in
       preset_lib_x_stmt);
   (3) the alloc.c ledger cells are NOT owned statics: the journal exempts them once, through its PST argument
       (h-hpreset-7's lib/Reusable/YCbqG.v ajournal_x, PST := alloc.c's five statics); this closure never names them.
   PROVISIONAL (owner: h-hpreset-7 / h-mani-a8, merged sha pending): ablocks_cf, afn_pre_cf, ajournal_cf and
   apost_base_cf are universally quantified with PresetCfnA.v's types (lines 265-276); the composition instantiates
   them with YCbqG.v's afn_pre_x / ajournal_x / apost_base_x at ARx := ARcf tfibsegs TfibB. The closure uses none of
   their bodies. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetCfiA.v, with its module paths changed; 35 of its 62 lines of code are new or changed and 58 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: made from tfib_lib_x_all of proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v:21-141 (asan;
   its asan-ubsan twin is lib/YCfi.v:19-139), for fuzz_preset. This file (asan) and lib/AU/PresetCfiB.v (asan-ubsan)
   state the same closure over their own interface file (PresetCfnA / PresetCfnB).
   It states the CLOSURE of the harness walk on the ASan side: from the walk of LLVMFuzzerTestOneInput
   (preset_lib_x_stmt, lib/A/PresetCfnA.v) and preset's set of parts to the program slot preset_lib_contract_x_all
   that the composition (PresetD2oA) takes. The proof is in PresetCfiAPf.v. Nothing in this file is a proof of a
   function (rule 24).
   Changes from the donor (the internal file closedwalk-plan.md section 1g):
   (1) the parts are preset's, not cgif's: the fourteen callee contracts of PresetCfnA.v section 6 in place of cgif's
       wfn / TNEWGIFX / TADDFX / TCLOSEX, and the frame-area allocation part of the second allocator instance's API
       (AsanAPI_cf's aa_stack_malloc_cf, lib/Reusable/YGcfNames.v) over a Theorem Labs lane's DEFINED
       astack_malloc_realizes_cf (lib/Reusable/YG0dcf.v) at preset's unit parameters CfParams_preset
       (lib/A/CfParamsPreset.v, class set [0; 1; 3]), in place of cgif's class-2 stack_malloc2_contract. The release
       law astack_free_law_cf is not a part: a8 proves it (astack_free_law_ok_cf, lib/Reusable/YG0tcf.v);
   (2) dropped: the sink (AIL, AUNLINKX, tfib_ROB, tfib_ro_segs_chk), cgif's meter numbers (XN0 and its five lemmas),
       cgif's relro window literals (the interface reads the image's relro range from its listing class PAImg), and
       every link lemma whose consumer was cgif's harness walk (preset's walk states its own needs in
       preset_lib_x_stmt);
   (3) the alloc.c ledger cells are NOT owned statics: the journal exempts them once, through its PST argument
       (a Theorem Labs lane's lib/Reusable/YCbqG.v ajournal_x, PST := prh_pst, alloc.c's six statics and fuzz_preset.c's g_own_ran_out); this closure never names them.
   On the interface of IfacePort 3f83c075b61f (re-cut by lane CwD2): the frame names ablocks_cf / afn_pre_cf /
   ajournal_cf / apost_base_cf are the interface's constants (abbreviations of YCbqG's journal layer at ARcf) and
   fregs_kept_x is YCbqG's, so none is a parameter; N_LLVMF is gone with the per-call room sum; the interface's run
   room parameters sm (the harness model's) and iface_room_np (PROVISIONAL, the non-primary room) are universally
   quantified with PresetCfnA.v's Section v types. The closure uses none of their bodies.
   #102 (no-DW interface, PresetCfnA.v, first at commit 8259b94c42ee; on the kit's batch):
   the interface's slot takes ONE record of callee contracts, preset_callee_contracts (PresetCfnA.v section 6: the kit's
   sixteen texts at the record's ARx := iface_ARx, RL := prh_room_live_a8, PI := preset_prh_img, sink head and
   context iface_ctx0, plus the frame-area allocation pcc_stack_malloc and its release pcc_stack_free), and the harness
   walk preset_lib_x_stmt takes that record at every float state. So the closure's parts are the record and the walk;
   the fourteen afn_spec_cf records of the old pins (and A_pj_parse / pj_get / pj_get_str, gone from LLVMFuzzerTestOneInput
   on #102) are gone, and so is the run's data-word list DW (the kit's batch: clause 4a / 4b). *)

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset PresetCfnA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The closure, at preset's asan segments (tfibsegs, lib/A/AB1v.v, PresetCfnA's segs), every run
   ceiling rc, every code image ci, every image listing (L, PA), every asyms B (the composition takes B := TfibB) and
   preset's library shape (ZTraceSpec.checksum_shape, PresetCfnA.v section 7). Every class argument is passed by name:
   this tree loads #[global] instances of other builds. The parts: the callee record at every float state, and the
   harness walk (the PROGRAM-WALKS row of LLVMFuzzerTestOneInput) at every float state. *)
Definition tfib_lib_x_all_A : Prop :=
forall (rc : YM05.RunCeil) (ci : CfImg) (L : YP0b.ptable YPsym.asym) (PA : YC4aP.PAImg L) (B : asyms)
  (sm : list Z -> Z * Z) (iface_room_np : astate -> Prop)
  (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (PAYLOAD_ROOM : list byte -> Prop) (A_MOD_AT A_STAMP : Z),
(forall fx : YK11.FPState,
  preset_callee_contracts (rc := rc) (L := L) (PA := PA) (ci := ci) (fx := fx) B A_MOD_AT A_STAMP) ->
(forall fx : YK11.FPState,
  preset_lib_x_stmt (rc := rc) (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
    (L := L) (PA := PA) (ci := ci) (fx := fx)
    sm iface_room_np B MT XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP) ->
preset_lib_contract_x_all (rc := rc)
  (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) (L := L) (PA := PA) (ci := ci)
  sm iface_room_np B MT XM_LIB XN_LIB PAYLOAD_ROOM.
