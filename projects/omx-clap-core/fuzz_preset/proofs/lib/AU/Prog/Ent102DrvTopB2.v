(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102 pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b): THE SECOND
   COMPOSED TOP of the B' driver. The first composed top Ent102DrvTopB.TFIB_T_closed_B_walked (lib/AU/Prog/Ent102DrvTopB.v,
   the driver of record lib/AU/PresetD2pBPf.v TFIB_T_closed_B_holds with the walk's slot) with four more of its Section
   hypotheses DISCHARGED BY CITATION of theorems already proved (on the kit's cut 7cdbb61b5fa0, or on the named branch of a
   file taken by path; nothing re-proved):
     H_aintrin_realizes_xm_cpy_B      a Theorem Labs lane's PRowCpy.prow_memcpy_icpt_xm_B (lib/AU/PRowCpy.v:40) at B := TfibB,
                                      ARx := ARcf tfibsegs TfibB, laws YGcallcf.AR_laws_x_cf of YG0lawscf.AR_laws_ok_cf;
     H_aintrin_realizes_xm_set_B      a Theorem Labs lane's PRowSet.prow_memset_icpt_xm_B (lib/AU/PRowSet.v:4377), the same way;
     H_astack_malloc_realizes_cfm_B   a Theorem Labs lane's FCm01xm.stack_malloc0_contract_xm / stack_malloc1_contract_xm
                                      (lib/AU/FCm01xm.v:25, :33) and FCm3xm.stack_malloc3_contract_xm (lib/AU/FCm3xm.v:22),
                                      one per class of cf_fs_classes CfParams_preset = [0; 1; 3], fs_iface by
                                      FCifaceCf.fs_iface_ARcf (as lib/AU/FCxmCfxB.v:45-48 does);
     H_txt_parse_noting_B             a Theorem Labs lane's PN102BTop.tparse_noting_specX_TfibB (lib/B/Prog/PN102BTop.v:133,
                                      lib/B/Prog/PN102B*.v and PvB_Frees.v taken BY PATH from
                                      a working branch c7276d935095) at CTX0 := iface_ctx0, its callee
                                      premises cited: HLIVE FuzzAllocAccInstB102.fuzz_alloc_live_holds_B_inst
                                      (lib/B/Prog/FuzzAllocAccInstB102.v:47), HRO the driver's
                                      PresetD2pBPf.txt_fuzz_alloc_ran_out_B_holds, HCRC
                                      CrcBInstLive.check_reject_clean_holds_B_inst_live (lib/B/Prog/CrcBInstLive.v:44) at
                                      the driver's PresetD2pBPf.crc_bcmp_B_holds and crc_img_shadow_vis_B_holds; its
                                      fourth, HPJ (the kit's tpj_parse_specX, no proof yet), is the NAMED Section hypothesis
                                      H_txt_pj_parse_B below, that text at the
                                      driver's parameters (PI := preset_prh_img, RL := prh_room_live_a8, PA := PI_prog_B,
                                      B := TfibB, ARx := iface_ARx, SK := preset_sink_head, CTX0 := iface_ctx0).
   This Section's hypotheses are exactly the first composed top's others, by its names and statements (the driver's
   text under the driver's two local instances): the allocator rows H_amalloc_realizes_cf_B / H_afree_realizes_cf_B,
   the read check H_aread_check_stmt_cf_B, the callee texts H_txt_check_no_overread_B,
   H_txt_check_as_written_B,
   H_txt_check_reject_clean_starved_B, H_txt_check_round_trip_B, H_txt_pj_free_B;
   parse_noting's open callee text H_txt_pj_parse_B; and the Section variables XM_LIB XN_LIB. The live real stack
   (#102) is no premise: the driver walk proves it from main's entry (lib/AU/PresetD1pBPfC.v H_stackup_main_B_holds,
   by the start-up lane's stack_up_main_W1_B over the kit's argH0).
   rule 24: no function proved (kind: composition by citation). *)

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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base PRH_FnAlloc PRH_FnCheck PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Ent102InstB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Ent102DrvTopB.
(* the cited theorems' files (Required; cited by full path below) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require FCifaceCf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PRowCpy PRowSet FCm01xm FCm3xm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzAllocAccInstB102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require CrcBInstLive PN102BTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section walked2.
(* the driver's Section instances (lib/AU/PresetD2pBPf.v Section closed), so every statement below elaborates to the
   driver's own text, as in Ent102DrvTopB.v *)
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance CfImg_B.

(* ---------------------------------------------------------------------- *)
(* 1. The discharges, each the cited theorem at the first composed top's statement. *)

Lemma drv2_aintrin_cpy_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PRowCpy.prow_memcpy_icpt_xm_B YD2l.TfibB
  (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs YD2l.TfibB) _
  (YGcallcf.AR_laws_x_cf (cp := CfParams_preset) tfibsegs YD2l.TfibB
     (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) tfibsegs YD2l.TfibB))
  YD2l.TfibB_syms).
Qed.

Lemma drv2_aintrin_set_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OSet (pc_wrap_memset (as_code TfibB)).
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PRowSet.prow_memset_icpt_xm_B YD2l.TfibB
  (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs YD2l.TfibB) _
  (YGcallcf.AR_laws_x_cf (cp := CfParams_preset) tfibsegs YD2l.TfibB
     (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) tfibsegs YD2l.TfibB))
  YD2l.TfibB_syms).
Qed.

(* the frame-area classes of CfParams_preset are [0; 1; 3] (CfParamsPreset.v): one cited contract per class *)
Lemma drv2_stack_malloc_cfm_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (cid : Z),
  In cid (@cf_fs_classes CfParams_preset) -> astack_malloc_realizes_cfm (rc := rc) (fx := fx) tfibsegs TfibB cid.
Proof.
intros rc fx cid Hin. cbn in Hin. destruct Hin as [<- | [<- | [<- | []]]].
- exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.FCm01xm.stack_malloc0_contract_xm (fx := fx)
    YD2l.TfibB (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs YD2l.TfibB)
    (FCifaceCf.fs_iface_ARcf (cp := CfParams_preset) tfibsegs YD2l.TfibB
       (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) tfibsegs YD2l.TfibB))
    YD2l.TfibB_syms).
- exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.FCm01xm.stack_malloc1_contract_xm (fx := fx)
    YD2l.TfibB (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs YD2l.TfibB)
    (FCifaceCf.fs_iface_ARcf (cp := CfParams_preset) tfibsegs YD2l.TfibB
       (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) tfibsegs YD2l.TfibB))
    YD2l.TfibB_syms).
- exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.FCm3xm.stack_malloc3_contract_xm (fx := fx)
    YD2l.TfibB (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs YD2l.TfibB)
    (FCifaceCf.fs_iface_ARcf (cp := CfParams_preset) tfibsegs YD2l.TfibB
       (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) tfibsegs YD2l.TfibB))
    YD2l.TfibB_syms).
Qed.

(* parse_noting's callee premises HLIVE and HCRC, at the driver's parameters (PN102BTop.v:133's premises at
   CTX0 := iface_ctx0, PI := preset_prh_img, ARx := iface_ARx, by conversion) *)
Lemma drv2_fuzz_alloc_live_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_alloc_live_specX (fx := fx) (cp := CfParams_preset) (PI := PresetCfnB.preset_prh_img)
    (RL := @PRH_Base.prh_room_live_a8 CfParams_preset) (PA := @PI_prog_B rc) YD2l.TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B YD2l.TfibB) PresetCfnB.preset_sink_head.
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.FuzzAllocAccInstB102.fuzz_alloc_live_holds_B_inst
  (fx := fx) (rc := rc) (SK := PresetCfnB.preset_sink_head)).
Qed.

Lemma drv2_check_reject_clean_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnCheck.tcheck_reject_clean_specX (fx := fx) (cp := CfParams_preset) (PI := PresetCfnB.preset_prh_img)
    (RL := @PRH_Base.prh_room_live_a8 CfParams_preset) (PA := @PI_prog_B rc) YD2l.TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B YD2l.TfibB) PresetCfnB.preset_sink_head.
Proof.
intros rc fx.
exact (CrcBInstLive.check_reject_clean_holds_B_inst_live (fx := fx) (rc := rc) PresetCfnB.preset_sink_head
  (PresetD2pBPf.crc_bcmp_B_holds rc fx) (PresetD2pBPf.crc_img_shadow_vis_B_holds rc)).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE SECOND COMPOSED TOP: the first composed top's remaining hypotheses, by its names and statements (the driver's
      text, verbatim). *)
(* the allocator rows and the read check *)
Hypothesis H_amalloc_realizes_cf_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fx) (cp := CfParams_preset) tfibsegs TfibB.
Hypothesis H_afree_realizes_cf_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (cp := CfParams_preset) tfibsegs TfibB.
Hypothesis H_aread_check_stmt_cf_B : forall rc : YM05.RunCeil, aread_check_stmt_cf (cp := CfParams_preset) TfibB.

(* the interface's Section parameters left free *)
Variables XM_LIB XN_LIB : Z -> Z.

(* the callee texts not discharged by a walk at the record's form, check_round_trip's at the B' literals *)
Hypothesis H_txt_check_no_overread_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_check_no_overread_B fx rc.
(* parse_noting's open callee text (PN102BTop.v HPJ), at the driver's parameters *)
Hypothesis H_txt_pj_parse_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CW : list (list Z)),
  PRH_FnPj.tpj_parse_specX (fx := fx) (cp := CfParams_preset) (PI := PresetCfnB.preset_prh_img)
    (RL := @PRH_Base.prh_room_live_a8 CfParams_preset) (PA := @PI_prog_B rc) YD2l.TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B YD2l.TfibB) PresetCfnB.preset_sink_head
    PresetCfnB.iface_ctx0 CW.
Hypothesis H_txt_check_as_written_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_check_as_written_B fx rc.
Hypothesis H_txt_check_reject_clean_starved_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  txt_check_reject_clean_starved_B fx rc.
Hypothesis H_txt_check_round_trip_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  txt_check_round_trip_B fx rc Ent102InstB.ia_mod_at Ent102InstB.ia_stamp.
Hypothesis H_txt_pj_free_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_pj_free_B fx rc.

(* H_txt_parse_noting_B by the parse_noting walk at its four callee premises *)
Lemma drv2_parse_noting_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_parse_noting_B fx rc.
Proof.
intros rc fx.
exact (PN102BTop.tparse_noting_specX_TfibB (fx := fx) (rc := rc) (ci := CfImg_B) (SK := PresetCfnB.preset_sink_head)
  PresetCfnB.iface_ctx0 (drv2_fuzz_alloc_live_B rc fx) (H_txt_pj_parse_B rc fx)
  (fun fy => PresetD2pBPf.txt_fuzz_alloc_ran_out_B_holds rc fy) (fun fy => drv2_check_reject_clean_B rc fy)).
Qed.

Theorem TFIB_T_closed_B_walked2 : TFIB_T_closed_B.
Proof.
exact (Ent102DrvTopB.TFIB_T_closed_B_walked
  H_amalloc_realizes_cf_B H_afree_realizes_cf_B drv2_aintrin_cpy_B drv2_aintrin_set_B drv2_stack_malloc_cfm_B
  H_aread_check_stmt_cf_B XM_LIB XN_LIB
  H_txt_check_no_overread_B drv2_parse_noting_B H_txt_check_as_written_B H_txt_check_reject_clean_starved_B
  H_txt_check_round_trip_B H_txt_pj_free_B).
Qed.

(* inside the Section: the remaining hypotheses by name, and the allowed axioms *)
Print Assumptions TFIB_T_closed_B_walked2.
End walked2.

(* the elaborated statement (implicit arguments shown, notations off): its Section names are now its binders *)
Set Printing Implicit. Unset Printing Notations.
Check TFIB_T_closed_B_walked2.
Unset Printing Implicit. Set Printing Notations.
