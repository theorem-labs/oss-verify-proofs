(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102 pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b): THE COMPOSED
   TOP of the B' driver with the walk of LLVMFuzzerTestOneInput. The driver of record's TFIB_T_closed_B_holds
   (lib/AU/PresetD2pBPf.v:257) at the walk's values - sm := ReaderRes.jr_strtod, a_mod_at / a_stamp :=
   Ent102InstB.ia_mod_at / ia_stamp, PAYLOAD_ROOM := (fun _ => True) (parent 07:2xZ) - with two of its Section
   hypotheses DISCHARGED:
     H_preset_lib_x_stmt_B  by lib/AU/Prog/Ent102SeamB.v preset_lib_x_stmt_B_holds (the seam; the walk's composed top
                            Ent102TopB.entry_B_walk);
     H_payload_room_B       by I: at PAYLOAD_ROOM := (fun _ => True) the bridge's conclusion is True (the walk's ec_pre
                            does not read PAYLOAD_ROOM, lib/AU/Ent102CutsB.v:257-293).
   This Section's hypotheses are exactly the driver's others, by the driver's names and statements (copied verbatim
   under the driver's two local instances, check_round_trip's text at the values above): the allocator rows, the read
   check, the six kit callee texts H_txt_* the driver still names; and the Section
   variables XM_LIB XN_LIB. The live real stack (#102) is no premise: the driver walk proves it from main's entry
   (lib/AU/PresetD1pBPfC.v H_stackup_main_B_holds).
   rule 24: no function proved (kind: composition; the function's walk is the cited Ent102TopB.entry_B_walk, through
   the seam Ent102SeamB). *)

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15 YK18 YA02 YM05 YO06 YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0n YG0d YC5d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf YG0d2cf YGcfRoomKeep YG0tcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP0b YPsym YC4aP YGcallMxmn YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB01 YF0m YD2l YCeg YD1w YD1x YD1k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetCfnB PresetTFIBAU.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1sitesB PresetD1preB PresetD1preBx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1qB PresetD1pB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetDrvTopBStmt PresetD2oB PresetD2oBPf PresetD2pB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD2pBPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Ent102InstB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Ent102SeamB.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section walked.
(* the driver's Section instances (lib/AU/PresetD2pBPf.v Section closed), so every hypothesis below elaborates to the
   driver's own text *)
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance CfImg_B.

(* A. The parts of the driver layer: the driver's hypotheses, verbatim. *)
Hypothesis H_amalloc_realizes_cf_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fx) (cp := CfParams_preset) tfibsegs TfibB.
Hypothesis H_afree_realizes_cf_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (cp := CfParams_preset) tfibsegs TfibB.
Hypothesis H_aintrin_realizes_xm_cpy_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OCpy (pc_wrap_memcpy (as_code TfibB)).
Hypothesis H_aintrin_realizes_xm_set_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OSet (pc_wrap_memset (as_code TfibB)).
Hypothesis H_astack_malloc_realizes_cfm_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (cid : Z),
  In cid (@cf_fs_classes CfParams_preset) -> astack_malloc_realizes_cfm (rc := rc) (fx := fx) tfibsegs TfibB cid.
Hypothesis H_aread_check_stmt_cf_B : forall rc : YM05.RunCeil, aread_check_stmt_cf (cp := CfParams_preset) TfibB.

(* B. The interface's Section parameters left free (sm, a_mod_at, a_stamp and PAYLOAD_ROOM are instantiated). *)
Variables XM_LIB XN_LIB : Z -> Z.

(* C. The program walks' hypotheses the driver still names, verbatim, check_round_trip's text at the B' literals. *)
Hypothesis H_txt_check_no_overread_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_check_no_overread_B fx rc.
Hypothesis H_txt_parse_noting_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_parse_noting_B fx rc.
Hypothesis H_txt_check_as_written_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_check_as_written_B fx rc.
Hypothesis H_txt_check_reject_clean_starved_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  txt_check_reject_clean_starved_B fx rc.
Hypothesis H_txt_check_round_trip_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  txt_check_round_trip_B fx rc Ent102InstB.ia_mod_at Ent102InstB.ia_stamp.
Hypothesis H_txt_pj_free_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_pj_free_B fx rc.

(* the driver's top's generalized type (its Section names are its binders, in Section order) *)
About PresetD2pBPf.TFIB_T_closed_B_holds.

(* THE COMPOSED TOP: the driver's slot hypothesis is the seam's theorem; the payload room is True *)
Theorem TFIB_T_closed_B_walked : TFIB_T_closed_B.
Proof.
exact (PresetD2pBPf.TFIB_T_closed_B_holds
  H_amalloc_realizes_cf_B H_afree_realizes_cf_B H_aintrin_realizes_xm_cpy_B H_aintrin_realizes_xm_set_B
  H_astack_malloc_realizes_cfm_B H_aread_check_stmt_cf_B
  ReaderRes.jr_strtod XM_LIB XN_LIB (fun _ : list byte => True) Ent102InstB.ia_mod_at Ent102InstB.ia_stamp
  H_txt_check_no_overread_B H_txt_parse_noting_B H_txt_check_as_written_B H_txt_check_reject_clean_starved_B
  H_txt_check_round_trip_B H_txt_pj_free_B
  (fun rc fx => Ent102SeamB.preset_lib_x_stmt_B_holds rc fx XM_LIB XN_LIB (fun _ : list byte => True))
  (fun _ _ _ _ _ _ _ _ => I)).
Qed.

(* the remaining Section hypotheses (by name) and the allowed axioms *)
Print Assumptions TFIB_T_closed_B_walked.
End walked.

(* the elaborated statement (implicit arguments shown, notations off): its Section names are now its binders *)
Set Printing Implicit. Unset Printing Notations.
Check TFIB_T_closed_B_walked.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions TFIB_T_closed_B_walked.
