(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YD2p.v:11-17 (asan-ubsan; its asan twin is
   lib/A/AD2p.v:11-17) for fuzz_preset's asan-ubsan image.
   The PROOF of TFIB_T_closed_B (lib/AU/PresetD2pB.v), i.e. of preset's TFIB_T_AU (lib/AU/PresetTFIBAU.v): the donor applies
   TFIB_T_of_partsXF to cgif's three closed library walks; here every input that is not a theorem of this tree is a
   NAMED Section variable or hypothesis, one per obligation (the list, with owners and status, is
   preset-F note, the internal file OBLIGATIONS.md). Print Assumptions of TFIB_T_closed_B_holds, inside this
   Section, is exactly these names, the kernel's primitives and the allowed axioms the discharges cite. Nothing in
   this file is a proof of a function (rule 24:
   no function proved; this is the composition / driver layer of a port).
   ON THE MEMNORM INTERFACE (lane MnTop, a Theorem Labs lane, 2026-10-29; interface a working branch 3a622dfaff87,
   prefix and closed driver a working branch 8a59abdc84b7):
   - the driver walk is CwD1pB's tfib_drv_main_B_holds (lib/AU/PresetD1pBPfC.v), now over MnPrefix's
     memnorm twins (lib/AU/PresetD2runBRd0mnPf.v) and the PROVED loop premise PresetD1rBmn.H_memnorm_drv_B_holds; it
     carries no premise: the image rows and the three start-up rows (YGcfNilInit.ARcf_nil_init's start-up premises,
     PresetD1pB.v section 4; proved in lib/AU/PresetStartRowsB.v) are discharged inside it;
   - the memcpy / memset premises are in a Theorem Labs lane's KEEP form YGcallMxmn.aintrin_realizes_xm (the driver's AICPY and
     CwSites' printf results take it), H_aintrin_realizes_xm_cpy_B / _set_B in place of the plain aintrin_realizes_cf;
   - the ten program callees' contracts come from the B program bridge (lib/AU/Prog/PRW_AfnBridgeBProg.v,
     a working branch c6bc6e90d8f1) and the B bridge (lib/B/Prog/PRW_AfnBridgeB.v): check_bounded_alloc
     and check_reject_clean from a Theorem Labs lane's signed walks (pcc_check_bounded_alloc_of_walk,
     pcc_check_reject_clean_of_walk), the other eight from THE KIT'S TEXTS, which stay named premises (section 0b), each at
     the bridge's record prwB_F_<f> ctx fr bud DW.
   #102 (no-DW interface, PresetCfnB.v, first at commit 8259b94c42ee; on the kit's batch; driver relocation 2026-10-29):
   the program part is the interface's ONE callee record preset_callee_contracts
   (PresetCfnB.v section 6), assembled here by field name at the B' instance (B := TfibB, L := B_prog_listing,
   PA := PI_prog_B, ci := CfImg_B, RL := prh_room_live_a8, ARx := iface_ARx = ARcf /\ xs_placed_cf): the kit's texts
   themselves, no afn_spec_cf records, no bridge, no data words. Discharged by walks of this tree: check_bounded_alloc
   (a Theorem Labs lane CheckBoundedAllocBInst.check_bounded_alloc_holds_B_inst_xs, no premise), check_reject_clean
   (a Theorem Labs lane CrcBInstLive.check_reject_clean_holds_B_inst_live, premises BCMP B' and cr_img_shadow_vis_B), the four
   ledger accessors live / count / peak_reset / peak (lane BridgeB PRW_AfnBridgeB.pcc102_*, PwAllocSurfB's walks) and
   the frame release (a8's astack_free_law_ok_cf); and, by the premise-free theorems of this tree cited in part A0,
   read_members, fuzz_alloc_ran_out, fuzz_alloc_ran_out_reset, fuzz_alloc_most and check_reject_clean's two premises
   (BCMP B' and cr_img_shadow_vis_B). Named premises: the kit's texts of the other six callees (section 0b) and the
   frame-area allocation in its memnorm-keeping form (pcc_stack_malloc, astack_malloc_realizes_cfm; the bridge proves
   only the cf form).
   #102, THE LIVE REAL STACK (the interface's header item (13); a Theorem Labs lane's ruling 09:23Z): the slot pre's last
   conjunct, YGcallStackUp.astack_up_x at each harness call's state, is PROVED by the driver walk from main's entry
   (lane StackDrv: the loop's invariant, carried by every prefix leaf, seeded at main by the start-up lane's
   stack_up_main_W1_B over the kit's argH0; lib/AU/PresetD1pBPfC.v H_stackup_main_B_holds). No premise remains for it. *)

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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB01 YF0m YD2l YCeg YD1w YD1x YD1k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetCfnB PresetTFIBAU.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1sitesB PresetD1preB PresetD1preBx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1qB PresetD1pB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetDrvTopBStmt PresetD2oB PresetD2oBPf PresetD2pB.
(* discharges: the B start-up (YB1n), a Theorem Labs lane's non-primary room (CfRoomLivePreset, image-generic: its lemmas are in
   `Section P. Context {ci : CfImg}`), the driver walk composed from its leaves (CwD1pB's PresetD1pBPfC) and CwPreB's
   five interceptor-site results (PresetD1preBxPf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YB1n YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset PRH_Base.
(* the B bridge (lane BridgeB): the four ledger accessors' #102 record fields from the image-B walks, and the closed
   TfibB entry for peak_reset (PST_unowned at TfibB) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PRW_AfnBridgeB PwPstUnownedB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD2runB PresetD1pBPfC PresetD1preBxPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD1rB.
(* The kit's texts and image B's PrhImg; a Theorem Labs lane's B' walks of check_bounded_alloc and check_reject_clean at the record's
   relation, and the vocabulary of the latter's two premises *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnCheck PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Witness.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require CrcB CheckBoundedAllocBInst CrcBInstLive.
(* the premise-free theorems part A0 cites: read_members, fuzz_alloc_ran_out / _reset, fuzz_alloc_most, the bcmp row
   with the ARcf laws, and the image's shadow visibility *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PRowCmp AImgShadowVisCfB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require read_members_Bp4 FuzzAllocAccInstB102 FuzzAllocMostBp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD1sitesBIPf.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. Discharged obligations, proved here from their owners' theorems. *)

(* START-UP: the B core's tfib_startup_T1 (lib/Reusable/YB1n.v:52, at the hand-off table of record HS_tfib,
   lib/Reusable/YB01.v) is the statement tfib_startup_T1_B HS_tfib (lib/AU/PresetD1qB.v) by conversion. *)
Lemma tfib_startup_T1_B_at_HS : tfib_startup_T1_B HS_tfib.
Proof. exact YB1n.tfib_startup_T1. Qed.

(* THE NON-PRIMARY ROOM: iface_room_np := np_live_B (lib/AU/PresetDrvTopBStmt.v: room_live_cf at preset's parameters,
   a Theorem Labs lane, lib/Reusable/YGcfRoomLive.v); its three laws are a8's unfolded _u lemmas (lib/A/CfRoomLivePreset.v), at
   ci := CfImg_B. *)
Lemma np_live_init_B : iface_room_np_init np_live_B.
Proof. unfold iface_room_np_init, np_live_B. exact CfRoomLivePreset.room_live_np_init_u. Qed.
Lemma np_live_step_B : iface_room_np_step (ci := CfImg_B) (cp := CfParams_preset) np_live_B.
Proof. unfold iface_room_np_step, np_live_B. exact (@CfRoomLivePreset.room_live_np_step_u CfImg_B). Qed.
Lemma np_live_tail_B : iface_room_np_tail (cp := CfParams_preset) np_live_B.
Proof. unfold iface_room_np_tail, np_live_B. exact CfRoomLivePreset.room_live_np_tail_u. Qed.

(* ---------------------------------------------------------------------- *)
(* 0b. The callee record's texts at the B' instance (PresetCfnB.v section 6, preset_callee_contracts, field by field:
      the kit's t<f>_specX at fy, rc, ci := CfImg_B, CPX := CfParams_preset, PI := preset_prh_img, RL := prh_room_live_a8,
      L := B_prog_listing, PA := PI_prog_B, B := TfibB, ARx := iface_ARx, the sink head and the context iface_ctx0), for
      the ten callees whose walk is not in this tree at the record's form (four of them, read_members, fuzz_alloc_ran_out,
      fuzz_alloc_ran_out_reset and fuzz_alloc_most, are proved in part A0); and check_reject_clean's two premises
      (CrcBInstLive.v :45-46) in the walk's own words, both proved in part A0. *)
Definition txt_check_no_overread_B (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnCheck.tcheck_no_overread_specX fx rc CfImg_B CfParams_preset PresetCfnB.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) B_prog_listing (@PI_prog_B rc) TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B TfibB) PresetCfnB.preset_sink_head PresetCfnB.iface_ctx0.
Definition txt_parse_noting_B (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnCheck.tparse_noting_specX fx rc CfImg_B CfParams_preset PresetCfnB.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) B_prog_listing (@PI_prog_B rc) TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B TfibB) PresetCfnB.preset_sink_head PresetCfnB.iface_ctx0.
Definition txt_check_as_written_B (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnCheck.tcheck_as_written_specX fx rc CfImg_B CfParams_preset PresetCfnB.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) B_prog_listing (@PI_prog_B rc) TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B TfibB) PresetCfnB.preset_sink_head PresetCfnB.iface_ctx0.
Definition txt_check_reject_clean_starved_B (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnCheck.tcheck_reject_clean_starved_specX fx rc CfImg_B CfParams_preset PresetCfnB.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) B_prog_listing (@PI_prog_B rc) TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B TfibB) PresetCfnB.preset_sink_head PresetCfnB.iface_ctx0.
Definition txt_read_members_B (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnCheck.tread_members_specX fx rc CfParams_preset PresetCfnB.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) B_prog_listing (@PI_prog_B rc) TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B TfibB) PresetCfnB.preset_sink_head.
Definition txt_check_round_trip_B (fx : YK11.FPState) (rc : YM05.RunCeil) (a_mod_at a_stamp : Z) : Prop :=
  @PRH_FnCheck.tcheck_round_trip_specX fx rc CfImg_B CfParams_preset PresetCfnB.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) B_prog_listing (@PI_prog_B rc) TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B TfibB) PresetCfnB.preset_sink_head PresetCfnB.iface_ctx0 a_mod_at a_stamp.
Definition txt_pj_free_B (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnPj.tpj_free_specX fx rc CfImg_B CfParams_preset PresetCfnB.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) B_prog_listing (@PI_prog_B rc) TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B TfibB) PresetCfnB.preset_sink_head PresetCfnB.iface_ctx0 PRH_Base.DOC_D.
Definition txt_fuzz_alloc_ran_out_reset_B (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnAlloc.tfuzz_alloc_ran_out_reset_specX fx rc CfParams_preset PresetCfnB.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) B_prog_listing (@PI_prog_B rc) TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B TfibB) PresetCfnB.preset_sink_head.
Definition txt_fuzz_alloc_most_B (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnCheck.tfuzz_alloc_most_specX fx rc CfParams_preset PresetCfnB.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) B_prog_listing (@PI_prog_B rc) TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B TfibB) PresetCfnB.preset_sink_head.
Definition txt_fuzz_alloc_ran_out_B (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnAlloc.tfuzz_alloc_ran_out_specX fx rc CfParams_preset PresetCfnB.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) B_prog_listing (@PI_prog_B rc) TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B TfibB) PresetCfnB.preset_sink_head.
(* check_reject_clean's walk at the record's relation (CrcBInstLive.v :44-48): the bcmp wrapper's memnorm-keeping
   contract (BCMP B') and the image's shadow visibility *)
Definition crc_bcmp_B (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  YGcallMxmn.abcmp_realizes_xm (fx := fx) (@YC4aP.pa_segs rc B_prog_listing (@PI_prog_B rc)) TfibB
    (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B TfibB)
    (@YC4aP.pa_sigma rc B_prog_listing (@PI_prog_B rc) YPsym.AS___wrap_bcmp).
Definition crc_img_shadow_vis_B (rc : YM05.RunCeil) : Prop :=
  CrcB.cr_img_shadow_vis_B
    (fun ly S Hp W mem md => ARcf (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) (@YC4aP.pa_segs rc B_prog_listing (@PI_prog_B rc)) TfibB
       ly S Hp W mem md).

(* THE INSTANCE UNIVERSE'S CLOSURE at the slot's context set (the no-DW slot pre's conjunct before the last, state-free),
   at the
   instance: the batch kit's witness (lib/A/PRH_Witness.v prh_univ_closure_witness_B, the batch kit 8ba304fe2f93: a decision
   procedure proved sound once and run by vm_compute) at TfibB, whose code record and universe are the witness's by
   definition (YD2l.TfibB); preset_prh_img and iface_ctx0 = [[RA_LLVMF]] are the witness's image table and context
   by conversion. No room count is stated here (the wild traces' depot room is a Theorem Labs lane's count thread). *)
Lemma univ_closure_TfibB_B : @PRH_Base.prh_univ_closure PresetCfnB.preset_prh_img TfibB CfImg_B PresetCfnB.iface_ctx0.
Proof. exact (PRH_Witness.prh_univ_closure_witness_B TfibB eq_refl eq_refl). Qed.

Section closed.
(* ---------------------------------------------------------------------- *)
(* A. The parts of the driver layer (the same names as lib/AU/PresetD2oBPf.v). *)
#[local] Existing Instance YK11.fx0.
(* the image's CfImg record: CfImg_B (lib/AU/CfImgB.v, blob 4b8e1b9596a7; its one home a working branch 5023be8f2869; owner
   order 06:00Z), so the result is TFIB_T_closed_B at the image *)
#[local] Existing Instance CfImg_B.
(* START-UP: discharged, tfib_startup_T1_B_at_HS above (YB1n.tfib_startup_T1). *)

(* ---------------------------------------------------------------------- *)
(* A0. Four callee texts of section 0b and check_reject_clean's two premises crc_bcmp_B / crc_img_shadow_vis_B, each by
      a premise-free theorem of this tree at the B' instance (under the two local instances above). *)
(* read_members: read_members_Bp4.read_members_holds_Bp4 (lib/B/Prog/read_members_Bp4.v) at RL := prh_room_live_a8,
   SK := preset_sink_head *)
Lemma txt_read_members_B_holds : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_read_members_B fx rc.
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.read_members_Bp4.read_members_holds_Bp4
  (fx := fx) (rc := rc) (RL := @PRH_Base.prh_room_live_a8 CfParams_preset) PresetCfnB.preset_sink_head).
Qed.
(* fuzz_alloc_ran_out / fuzz_alloc_ran_out_reset: FuzzAllocAccInstB102.fuzz_alloc_ran_out_holds_B_inst /
   fuzz_alloc_ran_out_reset_holds_B_inst (lib/B/Prog/FuzzAllocAccInstB102.v) at SK := preset_sink_head *)
Lemma txt_fuzz_alloc_ran_out_B_holds : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_fuzz_alloc_ran_out_B fx rc.
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.FuzzAllocAccInstB102.fuzz_alloc_ran_out_holds_B_inst
  (fx := fx) (rc := rc) (SK := PresetCfnB.preset_sink_head)).
Qed.
Lemma txt_fuzz_alloc_ran_out_reset_B_holds : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  txt_fuzz_alloc_ran_out_reset_B fx rc.
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.FuzzAllocAccInstB102.fuzz_alloc_ran_out_reset_holds_B_inst
  (fx := fx) (rc := rc) (SK := PresetCfnB.preset_sink_head)).
Qed.
(* fuzz_alloc_most: FuzzAllocMostBp.fuzz_alloc_most_holds_B (lib/B/Prog/FuzzAllocMostBp.v) at B := TfibB,
   SK := preset_sink_head; its premise PST_unowned by PwPstUnownedB.pst_unowned_TfibB *)
Lemma txt_fuzz_alloc_most_B_holds : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_fuzz_alloc_most_B fx rc.
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.FuzzAllocMostBp.fuzz_alloc_most_holds_B
  (fx := fx) (rc := rc) (SK := PresetCfnB.preset_sink_head) YD2l.TfibB PwPstUnownedB.pst_unowned_TfibB).
Qed.
(* BCMP B': PRowCmp.pr_bcmp_xm_B (lib/AU/PRowCmp.v) at B := TfibB, ARx := iface_ARx, the ARcf laws
   YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf; the pc is pa_sigma PI_prog_B AS___wrap_bcmp *)
Lemma crc_bcmp_B_holds : forall (rc : YM05.RunCeil) (fx : YK11.FPState), crc_bcmp_B fx rc.
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PRowCmp.pr_bcmp_xm_B YD2l.TfibB
  (@PresetCfnB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B YD2l.TfibB) _
  (YGcallcf.AR_laws_x_xs (cp := CfParams_preset) (@YC4aP.pa_segs rc B_prog_listing (@PI_prog_B rc)) YD2l.TfibB
     (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) (@YC4aP.pa_segs rc B_prog_listing (@PI_prog_B rc)) YD2l.TfibB))
  YD2l.TfibB_syms).
Qed.
(* the image's shadow visibility: AImgShadowVisCfB.tfib_img_shadow_vis_cf_B (lib/AU/AImgShadowVisCfB.v) at
   segs := pa_segs PI_prog_B, its TfibSyms by YD2l.TfibB_syms *)
Lemma crc_img_shadow_vis_B_holds : forall rc : YM05.RunCeil, crc_img_shadow_vis_B rc.
Proof.
intros rc.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.AImgShadowVisCfB.tfib_img_shadow_vis_cf_B
  (rc := rc) (cp := CfParams_preset) (@YC4aP.pa_segs rc B_prog_listing (@PI_prog_B rc)) YD2l.TfibB YD2l.TfibB_syms).
Qed.

(* THE DRIVER WALK: CwD1pB's tfib_drv_main_B_holds (lib/AU/PresetD1pBPfC.v), composed from the leaves' pushed theorems
   on the memnorm interface (MnPrefix's rd0 twins lib/AU/PresetD2runBRd0mnPf.v, the loop's memnorm premise PROVED by
   PresetD1rBmn.H_memnorm_drv_B_holds) and the start-up rows PROVED by lib/AU/PresetStartRowsB.v; applied below. *)

(* THE SECOND ALLOCATOR INSTANCE at TfibB. OWNER a Theorem Labs lane. Donor Lets YD2o.v:37-39 (AMALLOC, AFREE, AICPY). *)
(* malloc and free in their keep forms (YGcfMallocComposeKeep: the leaf's memnorm keep, which the layer's leaves no
   longer carry since field round 3 part 3c), both at every float state, free in its primed form under the re-hide
   (YG0dcfR.afree_realizes_cf_rh); the driver parts below (lib/AU/PresetD2oBPf.v) take malloc at fx0, its instance *)
Hypothesis H_amalloc_realizes_cf_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fx) (cp := CfParams_preset) tfibsegs TfibB.
Hypothesis H_afree_realizes_cf_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (cp := CfParams_preset) tfibsegs TfibB.
(* realloc in its keep _k form (YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep: the leaf's memnorm keep and the room
   at k) at the program listing's segments and realloc entry, the form of FuzzReallocB_p102's AREAL_cf (the realloc
   row the pj_set / pj_write walks reach). OPEN, and no proof of this Section uses it yet: Rocq generalizes a closed
   top only over the Section hypotheses its proof uses, so this row is a binder of no top below until one does. *)
Hypothesis H_arealloc_realizes_cf_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (Hp : list Z) (k : nat),
  YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset)
    (@YC4aP.pa_segs rc B_prog_listing (@PI_prog_B rc)) TfibB Hp
    (@YC4aP.pa_sigma rc B_prog_listing (@PI_prog_B rc) YPsym.AS___wrap_realloc) k.
(* the memcpy / memset texts in a Theorem Labs lane's KEEP form (lib/Reusable/YGcallMxmn.v aintrin_realizes_xm: a8's
   aintrin_realizes_cf with the memnorm keep `memnorm segs mem -> memnorm segs mem'` as its last post conjunct): the
   driver's AICPY (lib/AU/PresetD1pB.v) and CwSites' printf results (lib/AU/PresetD1sitesB.v) take this form.
   OWNER a Theorem Labs lane (the B instance) with a Theorem Labs lane (the keep). *)
Hypothesis H_aintrin_realizes_xm_cpy_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OCpy (pc_wrap_memcpy (as_code TfibB)).
Hypothesis H_aintrin_realizes_xm_set_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OSet (pc_wrap_memset (as_code TfibB)).
(* the frame-area allocation in the record's memnorm-keeping form (PresetCfnB.v astack_malloc_realizes_cfm, the
   record's pcc_stack_malloc). OWNER a Theorem Labs lane (FCapiCfB) with a Theorem Labs lane (the keep): the B bridge proves only the cf
   form (PRW_AfnBridgeB.pcc_stack_malloc_of_fcapi), and astack_malloc_realizes_cfm_cf goes only from cfm to cf. *)
Hypothesis H_astack_malloc_realizes_cfm_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (cid : Z),
  In cid (@cf_fs_classes CfParams_preset) -> astack_malloc_realizes_cfm (rc := rc) (fx := fx) tfibsegs TfibB cid.

(* THE READ INTERCEPTOR'S CHECK over ARcf. Donor Let YD2o.v:43 ARDCHK (YD2m tfib_ARDCHK). Statement
   aread_check_stmt_cf (lane CwPreB, lib/AU/PresetD1preB.v); no result statement yet. *)
Hypothesis H_aread_check_stmt_cf_B : forall rc : YM05.RunCeil, aread_check_stmt_cf (cp := CfParams_preset) TfibB.

(* THE INTERCEPTOR SITES over ARcf (CwPreB, lib/AU/PresetD1preBxPf.v): cited theorems, applied below. *)
(* THE PRINTF AND EXIT SITES over ARcf (CwSites, lib/AU/PresetD1sitesBIPf.v): cited theorems, applied below. *)

(* ---------------------------------------------------------------------- *)
(* B. The interface's Section v parameters (lib/AU/PresetCfnB.v) and the program walks' own parameters. *)
(* the harness model's parameter of lib/Spec/PresetRun.v hruns / hcons (owner two Theorem Labs lanes) *)
Variable sm : list Z -> Z * Z.
Variables XM_LIB XN_LIB : Z -> Z.
Variable PAYLOAD_ROOM : list byte -> Prop.
(* check_round_trip's two literal addresses (the record's A_MOD_AT / A_STAMP; the harness walk passes the image's) *)
Variables (a_mod_at a_stamp : Z).

(* ---------------------------------------------------------------------- *)
(* C. The program walks: the six callee texts of section 0b not proved in part A0 (OWNER of each: its walk's row owner,
      the program walks over the kit's batch), the harness walk, and the
      payload-room bridge of its PAYLOAD_ROOM. *)
Hypothesis H_txt_check_no_overread_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_check_no_overread_B fx rc.
Hypothesis H_txt_parse_noting_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_parse_noting_B fx rc.
Hypothesis H_txt_check_as_written_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_check_as_written_B fx rc.
Hypothesis H_txt_check_reject_clean_starved_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  txt_check_reject_clean_starved_B fx rc.
Hypothesis H_txt_check_round_trip_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  txt_check_round_trip_B fx rc a_mod_at a_stamp.
Hypothesis H_txt_pj_free_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_pj_free_B fx rc.
Hypothesis H_preset_lib_x_stmt_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  preset_lib_x_stmt (rc := rc) (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
    (L := B_prog_listing) (PA := PI_prog_B (rc := rc)) (ci := CfImg_B) (fx := fx)
    sm np_live_B TfibB ameter_triv XM_LIB XN_LIB PAYLOAD_ROOM a_mod_at a_stamp.
Hypothesis H_payload_room_B : forall (en_p : ExecEntry) (inp : ProcInput) (a0 p data : list byte),
  ~ run_scfg_budget_refused Shapes.Env.alloc_forced_only Images.plain Shapes.Budgets.Asan.lim_source en_p inp ->
  in_argv inp = [a0; p] -> Fs.fs_lookup (in_fs inp) p = Some data -> PAYLOAD_ROOM (payload data).

(* ---------------------------------------------------------------------- *)
(* D. The callee record (PresetCfnB.v section 6) at the B' instance, by field name. *)
Lemma preset_callees_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  preset_callee_contracts (rc := rc) (L := B_prog_listing) (PA := PI_prog_B (rc := rc)) (ci := CfImg_B) (fx := fx)
    TfibB a_mod_at a_stamp.
Proof.
intros rc fx. exact {|
  pcc_check_no_overread := fun fy => H_txt_check_no_overread_B rc fy;
  pcc_parse_noting := fun fy => H_txt_parse_noting_B rc fy;
  pcc_check_bounded_alloc := fun fy =>
    CheckBoundedAllocBInst.check_bounded_alloc_holds_B_inst_xs (fx := fy) (rc := rc) PresetCfnB.preset_sink_head;
  pcc_check_as_written := fun fy => H_txt_check_as_written_B rc fy;
  pcc_check_reject_clean := fun fy =>
    CrcBInstLive.check_reject_clean_holds_B_inst_live (fx := fy) (rc := rc) PresetCfnB.preset_sink_head
      (crc_bcmp_B_holds rc fy) (crc_img_shadow_vis_B_holds rc);
  pcc_check_reject_clean_starved := fun fy => H_txt_check_reject_clean_starved_B rc fy;
  pcc_read_members := fun fy => txt_read_members_B_holds rc fy;
  pcc_check_round_trip := fun fy => H_txt_check_round_trip_B rc fy;
  pcc_pj_free := fun fy => H_txt_pj_free_B rc fy;
  pcc_fuzz_alloc_ran_out_reset := fun fy => txt_fuzz_alloc_ran_out_reset_B_holds rc fy;
  pcc_fuzz_alloc_most := fun fy => txt_fuzz_alloc_most_B_holds rc fy;
  pcc_fuzz_alloc_live := fun fy => PRW_AfnBridgeB.pcc102_fuzz_alloc_live_of_walk (rc := rc) TfibB fy;
  pcc_fuzz_alloc_count := fun fy => PRW_AfnBridgeB.pcc102_fuzz_alloc_count_of_walk (rc := rc) TfibB fy;
  pcc_fuzz_alloc_peak_reset := fun fy =>
    PRW_AfnBridgeB.pcc102_fuzz_alloc_peak_reset_of_walk (rc := rc) TfibB PwPstUnownedB.pst_unowned_TfibB fy;
  pcc_fuzz_alloc_peak := fun fy => PRW_AfnBridgeB.pcc102_fuzz_alloc_peak_of_walk (rc := rc) TfibB fy;
  pcc_fuzz_alloc_ran_out := fun fy => txt_fuzz_alloc_ran_out_B_holds rc fy;
  pcc_stack_malloc := H_astack_malloc_realizes_cfm_B rc fx;
  pcc_stack_free := astack_free_law_ok_cf (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) tfibsegs TfibB |}.
Qed.

Theorem TFIB_T_closed_B_holds : TFIB_T_closed_B.
Proof.
exact (TFIB_T_of_partsXF_B_holds tfib_startup_T1_B_at_HS
  PresetD1pBPfC.tfib_drv_main_B_holds
  (fun rc => H_amalloc_realizes_cf_B rc YK11.fx0) H_afree_realizes_cf_B H_aintrin_realizes_xm_cpy_B
  H_aintrin_realizes_xm_set_B
  H_aread_check_stmt_cf_B
  PresetD1preBxPf.tfib_fwrite_site_cf_B_holds PresetD1preBxPf.tfib_refused_site_cf_B_holds
  PresetD1preBxPf.tfib_fprintf_open_site_cf_B_holds PresetD1preBxPf.tfib_fprintf_rderr_site_cf_B_holds
  PresetD1preBxPf.tfib_fprintf_usage_site_cf_B_holds
  PresetD1sitesBIPf.tfib_printf_first_cf_B_holds PresetD1sitesBIPf.tfib_printf_next_cf_B_holds
  PresetD1sitesBIPf.tfib_exit_site_cf_B_holds univ_closure_TfibB_B
  sm np_live_B XM_LIB XN_LIB PAYLOAD_ROOM a_mod_at a_stamp
  np_live_init_B np_live_step_B np_live_tail_B
  preset_callees_B H_preset_lib_x_stmt_B H_payload_room_B).
Qed.

(* The ROOM forms with the same discharges, for the halts tops (lib/AU/PresetD2oB.v section 2): the hypotheses are
   those of TFIB_T_closed_B_holds minus H_payload_room_B (the payload's room is the statement's own premise);
   the statement is the room form's residual conclusion at the Section's PAYLOAD_ROOM. *)
Theorem TFIB_T_room_all_B_closed : TFIB_T_room_all_concl_B PAYLOAD_ROOM.
Proof.
exact (TFIB_T_room_all_B_holds tfib_startup_T1_B_at_HS
  PresetD1pBPfC.tfib_drv_main_B_holds
  (fun rc => H_amalloc_realizes_cf_B rc YK11.fx0) H_afree_realizes_cf_B H_aintrin_realizes_xm_cpy_B
  H_aintrin_realizes_xm_set_B
  H_aread_check_stmt_cf_B
  PresetD1preBxPf.tfib_fwrite_site_cf_B_holds PresetD1preBxPf.tfib_refused_site_cf_B_holds
  PresetD1preBxPf.tfib_fprintf_open_site_cf_B_holds PresetD1preBxPf.tfib_fprintf_rderr_site_cf_B_holds
  PresetD1preBxPf.tfib_fprintf_usage_site_cf_B_holds
  PresetD1sitesBIPf.tfib_printf_first_cf_B_holds PresetD1sitesBIPf.tfib_printf_next_cf_B_holds
  PresetD1sitesBIPf.tfib_exit_site_cf_B_holds univ_closure_TfibB_B
  sm np_live_B XM_LIB XN_LIB PAYLOAD_ROOM a_mod_at a_stamp
  np_live_init_B np_live_step_B np_live_tail_B
  preset_callees_B H_preset_lib_x_stmt_B).
Qed.

Theorem TFIB_T_room_B_closed : TFIB_T_room_concl_B PAYLOAD_ROOM.
Proof.
exact (TFIB_T_room_B_holds tfib_startup_T1_B_at_HS
  PresetD1pBPfC.tfib_drv_main_B_holds
  (fun rc => H_amalloc_realizes_cf_B rc YK11.fx0) H_afree_realizes_cf_B H_aintrin_realizes_xm_cpy_B
  H_aintrin_realizes_xm_set_B
  H_aread_check_stmt_cf_B
  PresetD1preBxPf.tfib_fwrite_site_cf_B_holds PresetD1preBxPf.tfib_refused_site_cf_B_holds
  PresetD1preBxPf.tfib_fprintf_open_site_cf_B_holds PresetD1preBxPf.tfib_fprintf_rderr_site_cf_B_holds
  PresetD1preBxPf.tfib_fprintf_usage_site_cf_B_holds
  PresetD1sitesBIPf.tfib_printf_first_cf_B_holds PresetD1sitesBIPf.tfib_printf_next_cf_B_holds
  PresetD1sitesBIPf.tfib_exit_site_cf_B_holds univ_closure_TfibB_B
  sm np_live_B XM_LIB XN_LIB PAYLOAD_ROOM a_mod_at a_stamp
  np_live_init_B np_live_step_B np_live_tail_B
  preset_callees_B H_preset_lib_x_stmt_B).
Qed.

(* S1, the B' halts top's export (lib/AU/PresetDrvTopBStmt.v, a Theorem Labs lane's HaltsClosedB): the all-arms room form at the
   program SLOT, from the driver parts alone (no callee text, no harness walk: the halts top proves the slot). *)
Theorem TFIB_T_room_all_B_closed_stmt_holds : TFIB_T_room_all_B_closed_stmt.
Proof.
intros sm' XM' XN' PR' SLOT.
exact (TFIB_T_room_all_B_of_slot tfib_startup_T1_B_at_HS
  PresetD1pBPfC.tfib_drv_main_B_holds
  (fun rc => H_amalloc_realizes_cf_B rc YK11.fx0) H_afree_realizes_cf_B H_aintrin_realizes_xm_cpy_B
  H_aintrin_realizes_xm_set_B
  H_aread_check_stmt_cf_B
  PresetD1preBxPf.tfib_fwrite_site_cf_B_holds PresetD1preBxPf.tfib_refused_site_cf_B_holds
  PresetD1preBxPf.tfib_fprintf_open_site_cf_B_holds PresetD1preBxPf.tfib_fprintf_rderr_site_cf_B_holds
  PresetD1preBxPf.tfib_fprintf_usage_site_cf_B_holds
  PresetD1sitesBIPf.tfib_printf_first_cf_B_holds PresetD1sitesBIPf.tfib_printf_next_cf_B_holds
  PresetD1sitesBIPf.tfib_exit_site_cf_B_holds univ_closure_TfibB_B
  np_live_B np_live_init_B np_live_step_B np_live_tail_B sm' XM' XN' PR' SLOT).
Qed.
Print Assumptions TFIB_T_closed_B_holds.
Print Assumptions TFIB_T_room_all_B_closed_stmt_holds.
End closed.

(* the elaborated statement of the closed top: its Section names are now its binders (rule 17:10Z: printed with
   implicit arguments and without notations), and the statement it proves *)
Set Printing Implicit. Unset Printing Notations.
Check TFIB_T_closed_B_holds.
Check TFIB_T_room_all_B_closed_stmt_holds.
Print PresetD2pB.TFIB_T_closed_B.
Print PresetTFIBAU.TFIB_T_AU.
Unset Printing Implicit. Set Printing Notations.
