(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/AU/PresetDrvTopBStmt.v, with its module paths changed; 2 of its 50 lines of code are new or changed and 2 lines of the source are left out. *)
(* Theorem Labs, 2026-10-29: fuzz_preset's asan-ubsan image on the #102 pins (image B', pin d663f82d7f488d30, twin
   c90d4fa54d43160b): the STATEMENTS of the closed driver's room export that the B' halts top (a Theorem Labs lane, lane
   bp-halts, a working branch 756a34e7c18c, a Theorem Labs lane's note, the internal file HALTS-TOP-Bp-PREMISES.md
   section STOP, rows S1 and S3) composes with. Definitions only; nothing here is proved.
   rule 24: no function proved. rule 24: proves no function (kind: statement).

   - TFIB_T_room_all_concl_B: the residual conclusion of the room forms, VERBATIM the old-pin text
     (a working branch 5f6a2b85e1b9, lib/AU/PresetD2oB.v:162-170). Its home is now this file: the B'
     composition (PresetD2oB / PresetD2pBPf, restated on #102) imports it from here.
   - np_live_B: the closure's closed choice of the interface's iface_room_np, VERBATIM the old-pin
     PresetD2pBPf.v:76 (a8's room_live_cf at preset's CfParams).
   - TFIB_T_room_all_B_closed_stmt: the export S1. Against the old-pin TFIB_T_room_all_B_closed (PresetD2pBPf.v:419,
     inside Section closed), the program SLOT is the input (the interface's preset_lib_contract_x_all at the B'
     listing B_prog_listing, its image class PI_prog_B, CfImg_B, TfibB', the trivial meter ameter_triv, at every run
     ceiling), in place of the old fourteen callee records F_<f> / C_<f>_B and H_preset_lib_x_stmt_B: the slot is
     proved from the texts and the harness walk by the halts top itself (HaltsClosedB.v preset_lib_contract_x_all_B).
     The run's data words DW, the old npj and H_dw_bound_B are gone (the kit's batch, the no-DW interface): the slot pre
     asks the instance universe's closure at the slot's context set, prh_univ_closure TfibB iface_ctx0 (state-free,
     proved at TfibB by PRH_Witness.prh_univ_closure_witness_B), and the call's wild room, which the driver supplies
     at each slot call. The allocator-instance
     rows the driver walk takes (amalloc / afree / aintrin_xm cpy / set / astack_malloc / aread_check) stay named
     Section hypotheses of the proof, as in the old-pin Section closed (PresetD2pBPf.v:83-95, restated on B').
   - PAYLOAD_ROOM_dec_stmt: S3, VERBATIM the old-pin Hypothesis (lib/AU/HaltsClosedB.v:226 of a Theorem Labs lane's donor
     2f1789b29f0). PAYLOAD_ROOM is a parameter of the interface (PresetCfnB.v:726): no file of the driver or of the
     interface fixes it, so its decidability is a property of the instance the top chooses. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO09 YM05 YO06 YCbqG YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2l YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB PresetCfnB PresetTFIBAU.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
Import ListNotations.
Open Scope Z_scope.

(* the image's CfImg record, as the interface's texts and the halts top take it *)
#[local] Existing Instance CfImg_B.
(* init_config reads the FP state at the start-up one, as PresetTFIBAU.v's TFIB_T_AU does *)
#[local] Existing Instance YK11.fx0.

(* THE NON-PRIMARY ROOM the closure chooses for the interface's iface_room_np (old-pin PresetD2pBPf.v:76) *)
Definition np_live_B : astate -> Prop := YGcfRoomLive.room_live_cf (cp := CfParams_preset).

(* the residual conclusion of the room forms (old-pin PresetD2oB.v:162-170, verbatim) *)
Definition TFIB_T_room_all_concl_B (PAYLOAD_ROOM : list byte -> Prop) : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk presetsegsAU brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(forall a0 p data : list byte, in_argv inp = [a0; p] -> Fs.fs_lookup (in_fs inp) p = Some data ->
  PAYLOAD_ROOM (payload data)) ->
srealizes presetsegsAU
(init_config presetsegsAU AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).

(* S1: THE CLOSED ROOM EXPORT on B', taking the B' program slot (the internal file HALTS-TOP-Bp-PREMISES.md section STOP, verbatim) *)
Definition TFIB_T_room_all_B_closed_stmt : Prop :=
forall (sm : list Z -> Z * Z) (XM_LIB XN_LIB : Z -> Z) (PAYLOAD_ROOM : list byte -> Prop),
  (forall rc : YM05.RunCeil,
     preset_lib_contract_x_all (rc := rc)
       (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
       (L := B_prog_listing) (PA := PI_prog_B (rc := rc)) (ci := CfImg_B)
       sm np_live_B TfibB ameter_triv XM_LIB XN_LIB PAYLOAD_ROOM) ->
  TFIB_T_room_all_concl_B PAYLOAD_ROOM.

(* S3: the payload room is decidable (old-pin Hypothesis PAYLOAD_ROOM_dec, verbatim, as a statement of its room) *)
Definition PAYLOAD_ROOM_dec_stmt (PAYLOAD_ROOM : list byte -> Prop) : Type :=
  forall d : list byte, {PAYLOAD_ROOM d} + {~ PAYLOAD_ROOM d}.

(* the elaborated statements (rule 17:10Z: implicit arguments shown, notations off) *)
Set Printing Implicit. Unset Printing Notations.
Print TFIB_T_room_all_concl_B.
Print TFIB_T_room_all_B_closed_stmt.
Print PAYLOAD_ROOM_dec_stmt.
Print np_live_B.
Unset Printing Implicit. Set Printing Notations.
