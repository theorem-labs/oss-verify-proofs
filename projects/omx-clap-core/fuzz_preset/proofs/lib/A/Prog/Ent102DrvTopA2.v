(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102 pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4): THE SECOND
   COMPOSED TOP of the A' driver. The first composed top Ent102DrvTopA.TFIB_T_closed_A_walked (lib/A/Prog/Ent102DrvTopA.v,
   the driver of record lib/A/PresetD2pAPf.v TFIB_T_closed_A_holds with the walk's slot) with four more of its Section
   hypotheses DISCHARGED BY CITATION of theorems already proved (on the kit's cut 7cdbb61b5fa0, or on the named branch of a
   file taken by path; nothing re-proved):
     H_aintrin_realizes_xm_cpy_A      a Theorem Labs lane's PRowCpy.prow_memcpy_icpt_xm_A (lib/A/PRowCpy.v:38) at B := TfibB,
                                      ARx := ARcf tfibsegs TfibB, laws YGcallcf.AR_laws_x_cf of YG0lawscf.AR_laws_ok_cf;
     H_aintrin_realizes_xm_set_A      a Theorem Labs lane's PRowSet.prow_memset_icpt_xm_A (lib/A/PRowSet.v:4393), the same way;
     H_astack_malloc_realizes_cfm_A   a Theorem Labs lane's FCm01xm.stack_malloc0_contract_xm / stack_malloc1_contract_xm
                                      (lib/A/FCm01xm.v:24, :32) and FCm3xm.stack_malloc3_contract_xm (lib/A/FCm3xm.v:21),
                                      one per class of cf_fs_classes CfParams_preset = [0; 1; 3], fs_iface by
                                      FCifaceCf.fs_iface_ARcf (as lib/A/FCxmCfx.v:33-36 does);
     H_txt_parse_noting_A             a Theorem Labs lane's PN102Top.tparse_noting_specX_A_iface (lib/A/Prog/PN102Top.v:162,
                                      lib/A/Prog/PN102*.v taken BY PATH from a working branch
                                      b8995aca942b, lib/B/Prog/PvB_Frees.v from a working branch
                                      c7276d935095), its callee premises cited: HLIVE PwAllocSurf.fuzz_alloc_live_holds
                                      (lib/A/Prog/PwAllocSurf.v:796), HRO the driver's
                                      PresetD2pAPf.txt_fuzz_alloc_ran_out_A_holds, HCRC
                                      Crc102InstLive.check_reject_clean_holds_A102_inst_live (lib/A/Prog/Crc102InstLive.v:35)
                                      at the driver's PresetD2pAPf.crc_bcmp_A_holds; its fourth, HPJ (the kit's
                                      tpj_parse_specX, no proof yet), is the NAMED Section hypothesis H_txt_pj_parse_A
                                      below, that text at the driver's
                                      parameters (PI := preset_prh_img, RL := prh_room_live_a8, PA := PI_prog_A,
                                      B := TfibB, ARx := iface_ARx, SK := preset_sink_head, CTX0 := iface_ctx0).
   This Section's hypotheses are exactly the first composed top's others, by its names and statements: the allocator
   rows H_amalloc_realizes_cf_A / H_afree_realizes_cf_A, the read check H_aread_check_stmt_cf_A, the
   callee texts
   H_txt_check_no_overread_A, H_txt_check_as_written_A, H_txt_check_reject_clean_starved_A, H_txt_check_round_trip_A,
   H_txt_pj_free_A; parse_noting's open callee text H_txt_pj_parse_A; and the Section
   variables XM_LIB XN_LIB. The live real stack (#102) is no premise: the driver walk proves it from main's entry
   (lib/A/PresetD1pAPfC.v H_stackup_main_A_holds, by the start-up lane's stack_up_main_W1_A over the kit's argH0). The
   driver walk's start-up rows H_start_lazy_A / H_start_cells_A / H_start_pf_A are no premise either:
   lib/A/PresetD1pAPfC.v proves them.
   rule 24: no function proved (kind: composition by citation). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK11 YM05 YG0d YG0f YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn FCifaceCf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB1v AD2l CfImgA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetCfnA PresetD1preA PresetD1pA PresetD2pA PresetD2pAPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base PRH_FnAlloc PRH_FnCheck PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Ent102InstA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRowCpy PRowSet FCm01xm FCm3xm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PwAllocSurf Crc102InstLive PN102Top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Ent102DrvTopA.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation RLc := (@PRH_Base.prh_room_live_a8 CfParamsPreset.CfParams_preset).

(* ---------------------------------------------------------------------- *)
(* 1. The discharges, each the cited theorem at the first composed top's statement. *)

Lemma drv2_aintrin_cpy_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @YGcallMxmn.aintrin_realizes_xm fx AB1v.tfibsegs AD2l.TfibB
    (YG0ncf.ARcf (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) AB1v.tfibsegs AD2l.TfibB)
    YG0d.OCpy (YG0f.pc_wrap_memcpy (YG0f.as_code AD2l.TfibB)).
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PRowCpy.prow_memcpy_icpt_xm_A AD2l.TfibB
  (YG0ncf.ARcf (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) AB1v.tfibsegs AD2l.TfibB) _
  (YGcallcf.AR_laws_x_cf (cp := CP) AB1v.tfibsegs AD2l.TfibB (YG0lawscf.AR_laws_ok_cf (cp := CP) AB1v.tfibsegs AD2l.TfibB))
  AD2l.TfibB_syms).
Qed.

Lemma drv2_aintrin_set_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @YGcallMxmn.aintrin_realizes_xm fx AB1v.tfibsegs AD2l.TfibB
    (YG0ncf.ARcf (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) AB1v.tfibsegs AD2l.TfibB)
    YG0d.OSet (YG0f.pc_wrap_memset (YG0f.as_code AD2l.TfibB)).
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PRowSet.prow_memset_icpt_xm_A AD2l.TfibB
  (YG0ncf.ARcf (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) AB1v.tfibsegs AD2l.TfibB) _
  (YGcallcf.AR_laws_x_cf (cp := CP) AB1v.tfibsegs AD2l.TfibB (YG0lawscf.AR_laws_ok_cf (cp := CP) AB1v.tfibsegs AD2l.TfibB))
  AD2l.TfibB_syms).
Qed.

(* the frame-area classes of CfParams_preset are [0; 1; 3] (CfParamsPreset.v): one cited contract per class *)
Lemma drv2_stack_malloc_cfm_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (cid : Z),
  In cid (@YGcfNames.cf_fs_classes CP) ->
  PresetCfnA.astack_malloc_realizes_cfm (rc := rc) (ci := CfImgA.CfImg_A) (fx := fx) AB1v.tfibsegs AD2l.TfibB cid.
Proof.
intros rc fx cid Hin. cbn in Hin. destruct Hin as [<- | [<- | [<- | []]]].
- exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.FCm01xm.stack_malloc0_contract_xm (fx := fx)
    AD2l.TfibB (YG0ncf.ARcf (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) AB1v.tfibsegs AD2l.TfibB)
    (FCifaceCf.fs_iface_ARcf (cp := CP) AB1v.tfibsegs AD2l.TfibB
       (YG0lawscf.AR_laws_ok_cf (cp := CP) AB1v.tfibsegs AD2l.TfibB))
    AD2l.TfibB_syms).
- exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.FCm01xm.stack_malloc1_contract_xm (fx := fx)
    AD2l.TfibB (YG0ncf.ARcf (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) AB1v.tfibsegs AD2l.TfibB)
    (FCifaceCf.fs_iface_ARcf (cp := CP) AB1v.tfibsegs AD2l.TfibB
       (YG0lawscf.AR_laws_ok_cf (cp := CP) AB1v.tfibsegs AD2l.TfibB))
    AD2l.TfibB_syms).
- exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.FCm3xm.stack_malloc3_contract_xm (fx := fx)
    AD2l.TfibB (YG0ncf.ARcf (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) AB1v.tfibsegs AD2l.TfibB)
    (FCifaceCf.fs_iface_ARcf (cp := CP) AB1v.tfibsegs AD2l.TfibB
       (YG0lawscf.AR_laws_ok_cf (cp := CP) AB1v.tfibsegs AD2l.TfibB))
    AD2l.TfibB_syms).
Qed.

(* parse_noting's callee premises HLIVE and HCRC, at the driver's parameters (the iface form of PN102Top.v:162) *)
Lemma drv2_fuzz_alloc_live_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_alloc_live_specX (fx := fx) (cp := CP) (PI := PresetCfnA.preset_prh_img) (RL := RLc)
    (PA := @PAImg_prog.PI_prog_A rc) AD2l.TfibB
    (@PresetCfnA.iface_ARx rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB)
    PresetCfnA.preset_sink_head.
Proof.
intros rc fx.
exact (PwAllocSurf.fuzz_alloc_live_holds (fx := fx) (rc := rc) (SK := PresetCfnA.preset_sink_head) AD2l.TfibB).
Qed.

Lemma drv2_check_reject_clean_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnCheck.tcheck_reject_clean_specX (fx := fx) (cp := CP) (PI := PresetCfnA.preset_prh_img) (RL := RLc)
    (PA := @PAImg_prog.PI_prog_A rc) AD2l.TfibB
    (@PresetCfnA.iface_ARx rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB)
    PresetCfnA.preset_sink_head.
Proof.
intros rc fx.
exact (Crc102InstLive.check_reject_clean_holds_A102_inst_live (fx := fx) (rc := rc) (RL := RLc)
  (PresetD2pAPf.crc_bcmp_A_holds rc fx)).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE SECOND COMPOSED TOP: the first composed top's remaining hypotheses, by its names and statements. *)
Section walked2.
Variables XM_LIB XN_LIB : Z -> Z.

(* THE SECOND ALLOCATOR INSTANCE at TfibB (malloc and free in their keep forms, both at every float state, free
   primed) *)
Hypothesis H_amalloc_realizes_cf_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A)
    (cp := CfParamsPreset.CfParams_preset) AB1v.tfibsegs AD2l.TfibB.
Hypothesis H_afree_realizes_cf_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A)
    (cp := CfParamsPreset.CfParams_preset) AB1v.tfibsegs AD2l.TfibB.
(* THE READ INTERCEPTOR'S CHECK *)
Hypothesis H_aread_check_stmt_cf_A : forall rc : YM05.RunCeil,
  PresetD1preA.aread_check_stmt_cf (fx := YK11.fx0) (rc := rc) (ci := CfImgA.CfImg_A)
    (cp := CfParamsPreset.CfParams_preset) AD2l.TfibB.
(* THE CALLEE TEXTS not discharged by a walk at the record's form, check_round_trip's at the walk's literals *)
Hypothesis H_txt_check_no_overread_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_check_no_overread_A fx rc.
(* parse_noting's open callee text (PN102Top.v HPJ), at the driver's parameters *)
Hypothesis H_txt_pj_parse_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CW : list (list Z)),
  PRH_FnPj.tpj_parse_specX (fx := fx) (cp := CP) (PI := PresetCfnA.preset_prh_img) (RL := RLc)
    (PA := @PAImg_prog.PI_prog_A rc) AD2l.TfibB
    (@PresetCfnA.iface_ARx rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB)
    PresetCfnA.preset_sink_head PresetCfnA.iface_ctx0 CW.
Hypothesis H_txt_check_as_written_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_check_as_written_A fx rc.
Hypothesis H_txt_check_reject_clean_starved_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_check_reject_clean_starved_A fx rc.
Hypothesis H_txt_check_round_trip_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_check_round_trip_A fx rc Ent102InstA.ia_mod_at Ent102InstA.ia_stamp.
Hypothesis H_txt_pj_free_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_pj_free_A fx rc.

(* H_txt_parse_noting_A by the parse_noting walk at its four callee premises *)
Lemma drv2_parse_noting_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState), PresetD2pAPf.txt_parse_noting_A fx rc.
Proof.
intros rc fx.
exact (PN102Top.tparse_noting_specX_A_iface (fx := fx) (rc := rc) (drv2_fuzz_alloc_live_A rc fx) (H_txt_pj_parse_A rc fx)
  (fun fy => PresetD2pAPf.txt_fuzz_alloc_ran_out_A_holds rc fy) (fun fy => drv2_check_reject_clean_A rc fy)).
Qed.

Theorem TFIB_T_closed_A_walked2 : PresetD2pA.TFIB_T_closed_A.
Proof.
exact (Ent102DrvTopA.TFIB_T_closed_A_walked XM_LIB XN_LIB
  H_amalloc_realizes_cf_A H_afree_realizes_cf_A drv2_aintrin_cpy_A drv2_aintrin_set_A drv2_stack_malloc_cfm_A
  H_aread_check_stmt_cf_A
  H_txt_check_no_overread_A drv2_parse_noting_A H_txt_check_as_written_A H_txt_check_reject_clean_starved_A
  H_txt_check_round_trip_A H_txt_pj_free_A).
Qed.

(* inside the Section: the remaining hypotheses by name, and the allowed axioms *)
Print Assumptions TFIB_T_closed_A_walked2.
End walked2.

Set Printing Implicit.
Check TFIB_T_closed_A_walked2.
Unset Printing Implicit.
