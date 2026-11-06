(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102 pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4): THE COMPOSED
   TOP of the A' driver with the walk of LLVMFuzzerTestOneInput. The driver of record's TFIB_T_closed_A_holds
   (lib/A/PresetD2pAPf.v:251) at the walk's values - sm := ReaderRes.jr_strtod, a_mod_at / a_stamp :=
   Ent102InstA.ia_mod_at / ia_stamp, PAYLOAD_ROOM := (fun _ => True) - with two of its Section hypotheses DISCHARGED:
     H_preset_lib_x_stmt_A  by lib/A/Prog/Ent102SeamA.v preset_lib_x_stmt_A_holds (the seam; the walk's composed top
                            Ent102TopA.entry_A_walk);
     H_payload_room_A       by I: at PAYLOAD_ROOM := (fun _ => True) the bridge's conclusion is True (the walk's ec_pre
                            does not read PAYLOAD_ROOM, lib/A/Ent102CutsA.v:255-291).
   This Section's hypotheses are exactly the driver's others, by the driver's names and statements (at the values above):
   the allocator rows, the read check, the kit's six callee texts H_txt_* the driver still names; and the Section
   variables XM_LIB XN_LIB. The live real stack (#102) is no premise: the driver walk proves it from main's entry
   (lib/A/PresetD1pAPfC.v H_stackup_main_A_holds). The driver walk's start-up rows H_start_lazy_A / H_start_cells_A /
   H_start_pf_A (PresetD1pA.v section 4) are no premise either: lib/A/PresetD1pAPfC.v proves them.
   rule 24: no function proved (kind: composition; the function's walk is the cited Ent102TopA.entry_A_walk, through
   the seam Ent102SeamA). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK11 YM05 YG0d YG0f YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB1v AD2l CfImgA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetCfnA PresetD1preA PresetD1pA PresetD2pA PresetD2pAPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Ent102InstA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Ent102SeamA.

Section walked.
(* the driver's Section variables that stay (sm, a_mod_at, a_stamp and PAYLOAD_ROOM are instantiated) *)
Variables XM_LIB XN_LIB : Z -> Z.

(* THE SECOND ALLOCATOR INSTANCE at TfibB (the driver's section A; malloc and free in their keep forms, both at every
   float state, free primed) *)
Hypothesis H_amalloc_realizes_cf_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A)
    (cp := CfParamsPreset.CfParams_preset) AB1v.tfibsegs AD2l.TfibB.
Hypothesis H_afree_realizes_cf_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A)
    (cp := CfParamsPreset.CfParams_preset) AB1v.tfibsegs AD2l.TfibB.
Hypothesis H_aintrin_realizes_xm_cpy_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @YGcallMxmn.aintrin_realizes_xm fx AB1v.tfibsegs AD2l.TfibB
    (YG0ncf.ARcf (rc := rc) (ci := CfImgA.CfImg_A) (cp := CfParamsPreset.CfParams_preset) AB1v.tfibsegs AD2l.TfibB)
    YG0d.OCpy (YG0f.pc_wrap_memcpy (YG0f.as_code AD2l.TfibB)).
Hypothesis H_aintrin_realizes_xm_set_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @YGcallMxmn.aintrin_realizes_xm fx AB1v.tfibsegs AD2l.TfibB
    (YG0ncf.ARcf (rc := rc) (ci := CfImgA.CfImg_A) (cp := CfParamsPreset.CfParams_preset) AB1v.tfibsegs AD2l.TfibB)
    YG0d.OSet (YG0f.pc_wrap_memset (YG0f.as_code AD2l.TfibB)).
Hypothesis H_astack_malloc_realizes_cfm_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (cid : Z),
  In cid (@YGcfNames.cf_fs_classes CfParamsPreset.CfParams_preset) ->
  PresetCfnA.astack_malloc_realizes_cfm (rc := rc) (ci := CfImgA.CfImg_A) (fx := fx) AB1v.tfibsegs AD2l.TfibB cid.
(* THE READ INTERCEPTOR'S CHECK *)
Hypothesis H_aread_check_stmt_cf_A : forall rc : YM05.RunCeil,
  PresetD1preA.aread_check_stmt_cf (fx := YK11.fx0) (rc := rc) (ci := CfImgA.CfImg_A)
    (cp := CfParamsPreset.CfParams_preset) AD2l.TfibB.
(* THE SIX CALLEE TEXTS not discharged in the driver (the driver's section C), check_round_trip's at the walk's
   literals *)
Hypothesis H_txt_check_no_overread_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_check_no_overread_A fx rc.
Hypothesis H_txt_parse_noting_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_parse_noting_A fx rc.
Hypothesis H_txt_check_as_written_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_check_as_written_A fx rc.
Hypothesis H_txt_check_reject_clean_starved_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_check_reject_clean_starved_A fx rc.
Hypothesis H_txt_check_round_trip_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_check_round_trip_A fx rc Ent102InstA.ia_mod_at Ent102InstA.ia_stamp.
Hypothesis H_txt_pj_free_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_pj_free_A fx rc.

(* THE COMPOSED TOP: the driver's top with the harness slot proved by the walk (through the seam) and the payload room
   trivial *)
Theorem TFIB_T_closed_A_walked : PresetD2pA.TFIB_T_closed_A.
Proof.
exact (PresetD2pAPf.TFIB_T_closed_A_holds H_amalloc_realizes_cf_A H_afree_realizes_cf_A H_aintrin_realizes_xm_cpy_A
  H_aintrin_realizes_xm_set_A H_astack_malloc_realizes_cfm_A H_aread_check_stmt_cf_A
  ReaderRes.jr_strtod XM_LIB XN_LIB (fun _ => True) Ent102InstA.ia_mod_at Ent102InstA.ia_stamp
  H_txt_check_no_overread_A H_txt_parse_noting_A H_txt_check_as_written_A H_txt_check_reject_clean_starved_A
  H_txt_check_round_trip_A H_txt_pj_free_A
  (fun rc fx => Ent102SeamA.preset_lib_x_stmt_A_holds rc fx XM_LIB XN_LIB (fun _ => True))
  (fun _ _ _ _ _ _ _ _ => I)).
Qed.

(* inside the Section: the remaining hypotheses by name, and the allowed axioms *)
Print Assumptions TFIB_T_closed_A_walked.
End walked.

Set Printing Implicit.
Check TFIB_T_closed_A_walked.
Unset Printing Implicit.
