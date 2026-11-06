(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2p.v:11-17 (asan; its asan-ubsan twin is
   lib/YD2p.v:11-17) for fuzz_preset's asan image.
   The PROOF of TFIB_T_closed_A (lib/A/PresetD2pA.v), i.e. of preset's TFIB_T (lib/A/PresetTFIB.v): the donor applies
   TFIB_T_of_partsXF to cgif's three closed library walks; here every input that is not a theorem of this tree is a
   NAMED Section variable or hypothesis, one per obligation (the list, with owners and status, is
   preset-F note, the internal file OBLIGATIONS.md). Print Assumptions of TFIB_T_closed_A_holds, inside this
   Section, is exactly these names, the kernel's primitives and the allowed axioms the discharges cite
   (functional_extensionality_dep, from the callee bridge). Nothing in this file is a proof of a function (rule 24:
   no function proved; this is the composition / driver layer of a port).
   ON THE MEMNORM INTERFACE (lane MnTop, a Theorem Labs lane, 2026-10-29; interface a working branch 3a622dfaff87,
   prefix and closed driver a working branch 8a59abdc84b7, A bridge a working branch
   0c8e1ed21bd3):
   - the driver walk is CwD1pA's tfib_drv_main_A_holds (lib/A/PresetD1pAPfC.v), now over MnPrefix's
     memnorm twins (lib/A/PresetD2runARd0mnPf.v) and the PROVED loop premise PresetD1rAmn.H_memnorm_drv_A_holds; its
     three named premises (YGcfNilInit.ARcf_nil_init's start-up premises, PresetD1pA.v section 4) are Section
     hypotheses here (the image rows are discharged inside it);
   - the memcpy / memset premises are in a Theorem Labs lane's KEEP form YGcallMxmn.aintrin_realizes_xm (the driver's AICPY and
     CwSites' printf results take it), H_aintrin_realizes_xm_cpy_A / _set_A in place of the plain aintrin_realizes_cf.
   #102 (no-DW interface, PresetCfnA.v, first at commit 8259b94c42ee; on the kit's batch; driver relocation 2026-10-29):
   the program part is the interface's ONE callee record preset_callee_contracts
   (PresetCfnA.v section 6), assembled here by field name at the A' instance (B := TfibB, L := A_prog_listing,
   PA := PI_prog_A, ci := CfImg_A, RL := prh_room_live_a8, ARx := iface_ARx = ARcf /\ xs_placed_cf): the kit's texts
   themselves, no afn_spec_cf records, no bridge, no data words. Discharged by walks of this tree: check_bounded_alloc
   (a Theorem Labs lane N10-CBAA CheckBoundedAllocAInst.check_bounded_alloc_holds_A_inst, no premise), check_reject_clean
   (a Theorem Labs lane N10-CRCA Crc102InstLive.check_reject_clean_holds_A102_inst_live, premise BCMP A'), the four ledger
   accessors live / count / peak_reset / peak (a Theorem Labs lane's PwAllocSurf tops at prh_room_live_a8; peak_reset at
   PwAllocSurfSat.PST_unowned_at_TfibB) and the frame release (a8's astack_free_law_ok_cf); and, by the premise-free
   theorems of this tree cited in part A0, read_members, fuzz_alloc_ran_out, fuzz_alloc_ran_out_reset, fuzz_alloc_most
   and check_reject_clean's premise BCMP A'. Named premises: the other six callees' kit texts (section 0b), the
   frame-area allocation in its memnorm-keeping form (pcc_stack_malloc). The driver walk's start-up rows
   H_start_lazy_A / H_start_cells_A / H_start_pf_A are theorems of lib/A/PresetD1pAPfC.v (the kit's start-up facts), so the
   driver walk tfib_drv_main_A_holds is cited with no premise.
   #102, THE LIVE REAL STACK (the interface's header item (13); a Theorem Labs lane's ruling 09:23Z): the slot pre's last
   conjunct, YGcallStackUp.astack_up_x at each harness call's state, is PROVED by the driver walk from main's entry
   (lane StackDrv: the loop's invariant, carried by every prefix leaf, seeded at main by the start-up lane's
   stack_up_main_W1_A over the kit's argH0; lib/A/PresetD1pAPfC.v H_stackup_main_A_holds). No premise remains for it. *)

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15 YK18 YA02 YM05 YO06 YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0n YG0d YC5d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf YG0d2cf YGcfRoomKeep YG0tcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP0b YPsym YC4aP YGcallMxmn YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB01 AF0m AD2l ACeg AD1w AD1x AD1k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetCfnA PresetTFIB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1sitesA PresetD1preA PresetD1preAx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1qA PresetD1pA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD2oA PresetD2oAPf PresetD2pA.
(* discharges: the core's start-up (AB1n), a Theorem Labs lane's non-primary room (CfRoomLivePreset), the driver walk composed
   from its leaves (CwD1pA's PresetD1pAPfC) and CwPreA's five interceptor-site results (PresetD1preAxPf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB1n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset PRH_Base.
(* the four ledger accessors' walks (a Theorem Labs lane's PwAllocSurf tops at prh_room_live_a8) and PST_unowned at TfibB
   (PwAllocSurfSat) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PwAllocSurf PwAllocSurfSat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetD2runA PresetD1pAPfC PresetD1preAxPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetD1rA.
(* The kit's texts and image A's PrhImg; the A' walks of check_bounded_alloc and check_reject_clean at the record's relation,
   and the vocabulary of the latter's premise *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnCheck PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Witness.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crc102InstA CheckBoundedAllocAInst Crc102InstLive.
(* the premise-free theorems part A0 cites: read_members, fuzz_alloc_ran_out / _reset, fuzz_alloc_most, and the bcmp
   row with the ARcf laws *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRowCmp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require read_members_Ap4 FuzzAllocAccInst102 FuzzAllocMostAp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetD1sitesAIPf.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. Discharged obligations, proved here from their owners' theorems. *)

(* START-UP: the core's tfib_startup_T1 (lib/A/AB1n.v:53, a Theorem Labs lane's start-up at the hand-off table of record
   HS_tfib, lib/A/AB01.v) is the statement tfib_startup_T1_A HS_tfib (lib/A/PresetD1qA.v) by conversion. *)
Lemma tfib_startup_T1_A_at_HS : tfib_startup_T1_A HS_tfib.
Proof. exact AB1n.tfib_startup_T1. Qed.

(* THE NON-PRIMARY ROOM: iface_room_np := room_live_cf at preset's parameters (a Theorem Labs lane, lib/Reusable/YGcfRoomLive.v,
   lib/A/CfRoomLivePreset.v); its three laws are a8's unfolded _u lemmas, each by one exact. *)
Definition np_live_A : astate -> Prop := YGcfRoomLive.room_live_cf (cp := CfParams_preset).
Lemma np_live_init_A : iface_room_np_init np_live_A.
Proof. unfold iface_room_np_init, np_live_A. exact CfRoomLivePreset.room_live_np_init_u. Qed.
Lemma np_live_step_A : iface_room_np_step (ci := CfImg_A) (cp := CfParams_preset) np_live_A.
Proof. unfold iface_room_np_step, np_live_A. exact (@CfRoomLivePreset.room_live_np_step_u CfImg_A). Qed.
Lemma np_live_tail_A : iface_room_np_tail (cp := CfParams_preset) np_live_A.
Proof. unfold iface_room_np_tail, np_live_A. exact CfRoomLivePreset.room_live_np_tail_u. Qed.

(* ---------------------------------------------------------------------- *)
(* 0b. The callee record's texts at the A' instance (PresetCfnA.v section 6, preset_callee_contracts, field by field:
      the kit's t<f>_specX at fy, rc, ci := CfImg_A, CPX := CfParams_preset, PI := preset_prh_img, RL := prh_room_live_a8,
      L := A_prog_listing, PA := PI_prog_A, B := TfibB, ARx := iface_ARx, the sink head and the context iface_ctx0), for
      the ten callees whose walk is not in this tree at the record's form (four of them, read_members, fuzz_alloc_ran_out,
      fuzz_alloc_ran_out_reset and fuzz_alloc_most, are proved in part A0); and check_reject_clean's premise
      (Crc102InstLive.v :36) in the walk's own words, proved in part A0. *)
Definition txt_check_no_overread_A (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnCheck.tcheck_no_overread_specX fx rc CfImg_A CfParams_preset PresetCfnA.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PI_prog_A rc) TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImg_A TfibB) PresetCfnA.preset_sink_head PresetCfnA.iface_ctx0.
Definition txt_parse_noting_A (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnCheck.tparse_noting_specX fx rc CfImg_A CfParams_preset PresetCfnA.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PI_prog_A rc) TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImg_A TfibB) PresetCfnA.preset_sink_head PresetCfnA.iface_ctx0.
Definition txt_check_as_written_A (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnCheck.tcheck_as_written_specX fx rc CfImg_A CfParams_preset PresetCfnA.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PI_prog_A rc) TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImg_A TfibB) PresetCfnA.preset_sink_head PresetCfnA.iface_ctx0.
Definition txt_check_reject_clean_starved_A (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnCheck.tcheck_reject_clean_starved_specX fx rc CfImg_A CfParams_preset PresetCfnA.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PI_prog_A rc) TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImg_A TfibB) PresetCfnA.preset_sink_head PresetCfnA.iface_ctx0.
Definition txt_read_members_A (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnCheck.tread_members_specX fx rc CfParams_preset PresetCfnA.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PI_prog_A rc) TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImg_A TfibB) PresetCfnA.preset_sink_head.
Definition txt_check_round_trip_A (fx : YK11.FPState) (rc : YM05.RunCeil) (a_mod_at a_stamp : Z) : Prop :=
  @PRH_FnCheck.tcheck_round_trip_specX fx rc CfImg_A CfParams_preset PresetCfnA.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PI_prog_A rc) TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImg_A TfibB) PresetCfnA.preset_sink_head PresetCfnA.iface_ctx0 a_mod_at a_stamp.
Definition txt_pj_free_A (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnPj.tpj_free_specX fx rc CfImg_A CfParams_preset PresetCfnA.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PI_prog_A rc) TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImg_A TfibB) PresetCfnA.preset_sink_head PresetCfnA.iface_ctx0 PRH_Base.DOC_D.
Definition txt_fuzz_alloc_ran_out_reset_A (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnAlloc.tfuzz_alloc_ran_out_reset_specX fx rc CfParams_preset PresetCfnA.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PI_prog_A rc) TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImg_A TfibB) PresetCfnA.preset_sink_head.
Definition txt_fuzz_alloc_most_A (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnCheck.tfuzz_alloc_most_specX fx rc CfParams_preset PresetCfnA.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PI_prog_A rc) TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImg_A TfibB) PresetCfnA.preset_sink_head.
Definition txt_fuzz_alloc_ran_out_A (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  @PRH_FnAlloc.tfuzz_alloc_ran_out_specX fx rc CfParams_preset PresetCfnA.preset_prh_img (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PI_prog_A rc) TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImg_A TfibB) PresetCfnA.preset_sink_head.
(* check_reject_clean's walk at the record's relation (Crc102InstLive.v :35-38): the bcmp wrapper's memnorm-keeping
   contract (BCMP A'), in the walk's own words *)
Definition crc_bcmp_A (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  YGcallMxmn.abcmp_realizes_xm (fx := fx) OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs AD2l.TfibB
    (@Crc102InstA.c102_ARx rc CfImg_A)
    (PAImg_prog.A_prog_sigma YPsym.AS___wrap_bcmp).

(* THE INSTANCE UNIVERSE'S CLOSURE at the slot's context set (the no-DW slot pre's conjunct before the last,
   state-free), at the instance: the batch kit's witness (lib/A/PRH_Witness.v prh_univ_closure_witness_A, the batch kit 8ba304fe2f93: a
   decision
   procedure proved sound once and run by vm_compute) at TfibB, whose code record and universe are the witness's by
   definition (AD2l.TfibB); preset_prh_img and iface_ctx0 = [[RA_LLVMF]] are the witness's image table and context
   by conversion. No room count is stated here (the wild traces' depot room is a Theorem Labs lane's count thread). *)
Lemma univ_closure_TfibB_A : @PRH_Base.prh_univ_closure PresetCfnA.preset_prh_img TfibB CfImg_A PresetCfnA.iface_ctx0.
Proof. exact (PRH_Witness.prh_univ_closure_witness_A TfibB eq_refl eq_refl). Qed.

Section closed.
(* ---------------------------------------------------------------------- *)
(* A. The parts of the driver layer (the same names as lib/A/PresetD2oAPf.v). *)
#[local] Existing Instance YK11.fx0.
(* the image's CfImg record: CfImg_A (lib/A/CfImgA.v), so the result is TFIB_T_closed_A at the image *)
#[local] Existing Instance CfImg_A.
(* START-UP: discharged, tfib_startup_T1_A_at_HS above (AB1n.tfib_startup_T1). *)

(* ---------------------------------------------------------------------- *)
(* A0. Four callee texts of section 0b and check_reject_clean's premise crc_bcmp_A, each by a premise-free theorem of
      this tree at the A' instance (under the two local instances above). *)
(* read_members: read_members_Ap4.read_members_holds_Ap4 (lib/A/Prog/read_members_Ap4.v) at RL := prh_room_live_a8,
   SK := preset_sink_head *)
Lemma txt_read_members_A_holds : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_read_members_A fx rc.
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.read_members_Ap4.read_members_holds_Ap4
  (fx := fx) (rc := rc) (RL := @PRH_Base.prh_room_live_a8 CfParams_preset) PresetCfnA.preset_sink_head).
Qed.
(* fuzz_alloc_ran_out / fuzz_alloc_ran_out_reset: FuzzAllocAccInst102.fuzz_alloc_ran_out_holds_inst /
   fuzz_alloc_ran_out_reset_holds_inst (lib/A/Prog/FuzzAllocAccInst102.v) at SK := preset_sink_head *)
Lemma txt_fuzz_alloc_ran_out_A_holds : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_fuzz_alloc_ran_out_A fx rc.
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.FuzzAllocAccInst102.fuzz_alloc_ran_out_holds_inst
  (fx := fx) (rc := rc) (SK := PresetCfnA.preset_sink_head)).
Qed.
Lemma txt_fuzz_alloc_ran_out_reset_A_holds : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  txt_fuzz_alloc_ran_out_reset_A fx rc.
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.FuzzAllocAccInst102.fuzz_alloc_ran_out_reset_holds_inst
  (fx := fx) (rc := rc) (SK := PresetCfnA.preset_sink_head)).
Qed.
(* fuzz_alloc_most: FuzzAllocMostAp.fuzz_alloc_most_holds (lib/A/Prog/FuzzAllocMostAp.v) at B := TfibB,
   SK := preset_sink_head; its premise PST_unowned by PwAllocSurfSat.PST_unowned_at_TfibB *)
Lemma txt_fuzz_alloc_most_A_holds : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_fuzz_alloc_most_A fx rc.
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.FuzzAllocMostAp.fuzz_alloc_most_holds
  (fx := fx) (rc := rc) (SK := PresetCfnA.preset_sink_head) AD2l.TfibB PwAllocSurfSat.PST_unowned_at_TfibB).
Qed.
(* BCMP A': PRowCmp.pr_bcmp_xm_A (lib/A/PRowCmp.v) at B := TfibB, ARx := Crc102InstA.c102_ARx, the ARcf laws
   YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf; the pc is A_prog_sigma AS___wrap_bcmp *)
Lemma crc_bcmp_A_holds : forall (rc : YM05.RunCeil) (fx : YK11.FPState), crc_bcmp_A fx rc.
Proof.
intros rc fx.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PRowCmp.pr_bcmp_xm_A AD2l.TfibB
  (@Crc102InstA.c102_ARx rc CfImg_A) _
  (YGcallcf.AR_laws_x_xs (cp := CfParams_preset) OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs
     AD2l.TfibB
     (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs
        AD2l.TfibB))
  AD2l.TfibB_syms).
Qed.

(* THE DRIVER WALK: CwD1pA's tfib_drv_main_A_holds (lib/A/PresetD1pAPfC.v), composed from the leaves' pushed theorems
   on the memnorm interface (MnPrefix's rd0 twins lib/A/PresetD2runARd0mnPf.v, the loop's memnorm premise PROVED by
   PresetD1rAmn.H_memnorm_drv_A_holds), at its three named premises below; applied below. *)

(* THE SECOND ALLOCATOR INSTANCE at TfibB. OWNER a Theorem Labs lane. Donor Lets YD2o.v:37-39 (AMALLOC, AFREE, AICPY). *)
(* malloc and free in their keep forms (YGcfMallocComposeKeep: the leaf's memnorm keep, which the layer's leaves no
   longer carry since field round 3 part 3c), both at every float state, free in its primed form under the re-hide
   (YG0dcfR.afree_realizes_cf_rh); the driver parts below (lib/A/PresetD2oAPf.v) take malloc at fx0, its instance *)
Hypothesis H_amalloc_realizes_cf_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fx) (cp := CfParams_preset) tfibsegs TfibB.
Hypothesis H_afree_realizes_cf_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (cp := CfParams_preset) tfibsegs TfibB.
(* realloc in its keep _k form (YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep: the leaf's memnorm keep and the room
   at k) at the program listing's segments and realloc entry, the form of FuzzReallocAp's AREAL_cf (the realloc row
   the pj_set / pj_write walks reach). OPEN, and no proof of this Section uses it yet: Rocq generalizes a closed top
   only over the Section hypotheses its proof uses, so this row is a binder of no top below until one does. *)
Hypothesis H_arealloc_realizes_cf_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (Hp : list Z) (k : nat),
  YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset)
    (@YC4aP.pa_segs rc A_prog_listing (@PI_prog_A rc)) TfibB Hp
    (@YC4aP.pa_sigma rc A_prog_listing (@PI_prog_A rc) YPsym.AS___wrap_realloc) k.
(* the memcpy / memset texts in a Theorem Labs lane's KEEP form (lib/Reusable/YGcallMxmn.v aintrin_realizes_xm: a8's
   aintrin_realizes_cf with the memnorm keep `memnorm segs mem -> memnorm segs mem'` as its last post conjunct): the
   driver's AICPY (lib/A/PresetD1pA.v) and CwSites' printf results (lib/A/PresetD1sitesA.v) take this form.
   OWNER a Theorem Labs lane (the B instance) with a Theorem Labs lane (the keep). *)
Hypothesis H_aintrin_realizes_xm_cpy_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OCpy (pc_wrap_memcpy (as_code TfibB)).
Hypothesis H_aintrin_realizes_xm_set_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OSet (pc_wrap_memset (as_code TfibB)).
(* the frame-area allocation in the record's memnorm-keeping form (PresetCfnA.v astack_malloc_realizes_cfm, the
   record's pcc_stack_malloc). OWNER a Theorem Labs lane (FCapiCfB) with a Theorem Labs lane (the keep): the A bridge proves only the cf
   form (PRW_AfnBridge.pcc_stack_malloc_of_fcapi), and astack_malloc_realizes_cfm_cf goes only from cfm to cf. *)
Hypothesis H_astack_malloc_realizes_cfm_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (cid : Z),
  In cid (@cf_fs_classes CfParams_preset) -> astack_malloc_realizes_cfm (rc := rc) (fx := fx) tfibsegs TfibB cid.

(* THE READ INTERCEPTOR'S CHECK over ARcf. Donor Let YD2o.v:43 ARDCHK (YD2m tfib_ARDCHK). Statement
   aread_check_stmt_cf (lane CwPreB, lib/A/PresetD1preA.v); no result statement yet. *)
Hypothesis H_aread_check_stmt_cf_A : forall rc : YM05.RunCeil, aread_check_stmt_cf (cp := CfParams_preset) TfibB.

(* THE INTERCEPTOR SITES over ARcf (CwPreB, lib/A/PresetD1preAxPf.v): cited theorems, applied below. *)
(* THE PRINTF AND EXIT SITES over ARcf (CwSites, lib/A/PresetD1sitesAIPf.v): cited theorems, applied below. *)

(* ---------------------------------------------------------------------- *)
(* B. The interface's Section v parameters (lib/A/PresetCfnA.v) and the program walks' own parameters. *)
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
Hypothesis H_txt_check_no_overread_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_check_no_overread_A fx rc.
Hypothesis H_txt_parse_noting_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_parse_noting_A fx rc.
Hypothesis H_txt_check_as_written_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_check_as_written_A fx rc.
Hypothesis H_txt_check_reject_clean_starved_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  txt_check_reject_clean_starved_A fx rc.
Hypothesis H_txt_check_round_trip_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  txt_check_round_trip_A fx rc a_mod_at a_stamp.
Hypothesis H_txt_pj_free_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState), txt_pj_free_A fx rc.
Hypothesis H_preset_lib_x_stmt_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  preset_lib_x_stmt (rc := rc) (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
    (L := A_prog_listing) (PA := PI_prog_A (rc := rc)) (ci := CfImg_A) (fx := fx)
    sm np_live_A TfibB ameter_triv XM_LIB XN_LIB PAYLOAD_ROOM a_mod_at a_stamp.
Hypothesis H_payload_room_A : forall (en_p : ExecEntry) (inp : ProcInput) (a0 p data : list byte),
  ~ run_scfg_budget_refused Shapes.Env.alloc_forced_only Images.plain Shapes.Budgets.Asan.lim_source en_p inp ->
  in_argv inp = [a0; p] -> Fs.fs_lookup (in_fs inp) p = Some data -> PAYLOAD_ROOM (payload data).

(* ---------------------------------------------------------------------- *)
(* D. The callee record (PresetCfnA.v section 6) at the A' instance, by field name. *)
Lemma preset_callees_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  preset_callee_contracts (rc := rc) (L := A_prog_listing) (PA := PI_prog_A (rc := rc)) (ci := CfImg_A) (fx := fx)
    TfibB a_mod_at a_stamp.
Proof.
intros rc fx. exact {|
  pcc_check_no_overread := fun fy => H_txt_check_no_overread_A rc fy;
  pcc_parse_noting := fun fy => H_txt_parse_noting_A rc fy;
  pcc_check_bounded_alloc := fun fy =>
    CheckBoundedAllocAInst.check_bounded_alloc_holds_A_inst (fx := fy) (rc := rc) PresetCfnA.preset_sink_head;
  pcc_check_as_written := fun fy => H_txt_check_as_written_A rc fy;
  pcc_check_reject_clean := fun fy =>
    Crc102InstLive.check_reject_clean_holds_A102_inst_live (fx := fy) (rc := rc)
      (RL := @PRH_Base.prh_room_live_a8 CfParams_preset) (crc_bcmp_A_holds rc fy);
  pcc_check_reject_clean_starved := fun fy => H_txt_check_reject_clean_starved_A rc fy;
  pcc_read_members := fun fy => txt_read_members_A_holds rc fy;
  pcc_check_round_trip := fun fy => H_txt_check_round_trip_A rc fy;
  pcc_pj_free := fun fy => H_txt_pj_free_A rc fy;
  pcc_fuzz_alloc_ran_out_reset := fun fy => txt_fuzz_alloc_ran_out_reset_A_holds rc fy;
  pcc_fuzz_alloc_most := fun fy => txt_fuzz_alloc_most_A_holds rc fy;
  pcc_fuzz_alloc_live := fun fy =>
    PwAllocSurf.fuzz_alloc_live_holds (fx := fy) (rc := rc) (SK := PresetCfnA.preset_sink_head) TfibB;
  pcc_fuzz_alloc_count := fun fy =>
    PwAllocSurf.fuzz_alloc_count_holds (fx := fy) (rc := rc) (SK := PresetCfnA.preset_sink_head) TfibB;
  pcc_fuzz_alloc_peak_reset := fun fy =>
    PwAllocSurf.fuzz_alloc_peak_reset_holds (fx := fy) (rc := rc) (SK := PresetCfnA.preset_sink_head) TfibB
      PwAllocSurfSat.PST_unowned_at_TfibB;
  pcc_fuzz_alloc_peak := fun fy =>
    PwAllocSurf.fuzz_alloc_peak_holds (fx := fy) (rc := rc) (SK := PresetCfnA.preset_sink_head) TfibB;
  pcc_fuzz_alloc_ran_out := fun fy => txt_fuzz_alloc_ran_out_A_holds rc fy;
  pcc_stack_malloc := H_astack_malloc_realizes_cfm_A rc fx;
  pcc_stack_free := astack_free_law_ok_cf (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) tfibsegs TfibB |}.
Qed.

Theorem TFIB_T_closed_A_holds : TFIB_T_closed_A.
Proof.
exact (TFIB_T_of_partsXF_A_holds tfib_startup_T1_A_at_HS
  PresetD1pAPfC.tfib_drv_main_A_holds
  (fun rc => H_amalloc_realizes_cf_A rc YK11.fx0) H_afree_realizes_cf_A H_aintrin_realizes_xm_cpy_A
  H_aintrin_realizes_xm_set_A
  H_aread_check_stmt_cf_A
  PresetD1preAxPf.tfib_fwrite_site_cf_A_holds PresetD1preAxPf.tfib_refused_site_cf_A_holds
  PresetD1preAxPf.tfib_fprintf_open_site_cf_A_holds PresetD1preAxPf.tfib_fprintf_rderr_site_cf_A_holds
  PresetD1preAxPf.tfib_fprintf_usage_site_cf_A_holds
  PresetD1sitesAIPf.tfib_printf_first_cf_A_holds PresetD1sitesAIPf.tfib_printf_next_cf_A_holds
  PresetD1sitesAIPf.tfib_exit_site_cf_A_holds univ_closure_TfibB_A
  sm np_live_A XM_LIB XN_LIB PAYLOAD_ROOM a_mod_at a_stamp
  np_live_init_A np_live_step_A np_live_tail_A
  preset_callees_A H_preset_lib_x_stmt_A H_payload_room_A).
Qed.

(* The ROOM forms with the same discharges, for the halts tops (lib/A/PresetD2oA.v section 2): the hypotheses are
   those of TFIB_T_closed_A_holds minus H_payload_room_A (the payload's room is the statement's own premise);
   the statement is the room form's residual conclusion at the Section's PAYLOAD_ROOM. *)
Theorem TFIB_T_room_all_A_closed : TFIB_T_room_all_concl_A PAYLOAD_ROOM.
Proof.
exact (TFIB_T_room_all_A_holds tfib_startup_T1_A_at_HS
  PresetD1pAPfC.tfib_drv_main_A_holds
  (fun rc => H_amalloc_realizes_cf_A rc YK11.fx0) H_afree_realizes_cf_A H_aintrin_realizes_xm_cpy_A
  H_aintrin_realizes_xm_set_A
  H_aread_check_stmt_cf_A
  PresetD1preAxPf.tfib_fwrite_site_cf_A_holds PresetD1preAxPf.tfib_refused_site_cf_A_holds
  PresetD1preAxPf.tfib_fprintf_open_site_cf_A_holds PresetD1preAxPf.tfib_fprintf_rderr_site_cf_A_holds
  PresetD1preAxPf.tfib_fprintf_usage_site_cf_A_holds
  PresetD1sitesAIPf.tfib_printf_first_cf_A_holds PresetD1sitesAIPf.tfib_printf_next_cf_A_holds
  PresetD1sitesAIPf.tfib_exit_site_cf_A_holds univ_closure_TfibB_A
  sm np_live_A XM_LIB XN_LIB PAYLOAD_ROOM a_mod_at a_stamp
  np_live_init_A np_live_step_A np_live_tail_A
  preset_callees_A H_preset_lib_x_stmt_A).
Qed.

Theorem TFIB_T_room_A_closed : TFIB_T_room_concl_A PAYLOAD_ROOM.
Proof.
exact (TFIB_T_room_A_holds tfib_startup_T1_A_at_HS
  PresetD1pAPfC.tfib_drv_main_A_holds
  (fun rc => H_amalloc_realizes_cf_A rc YK11.fx0) H_afree_realizes_cf_A H_aintrin_realizes_xm_cpy_A
  H_aintrin_realizes_xm_set_A
  H_aread_check_stmt_cf_A
  PresetD1preAxPf.tfib_fwrite_site_cf_A_holds PresetD1preAxPf.tfib_refused_site_cf_A_holds
  PresetD1preAxPf.tfib_fprintf_open_site_cf_A_holds PresetD1preAxPf.tfib_fprintf_rderr_site_cf_A_holds
  PresetD1preAxPf.tfib_fprintf_usage_site_cf_A_holds
  PresetD1sitesAIPf.tfib_printf_first_cf_A_holds PresetD1sitesAIPf.tfib_printf_next_cf_A_holds
  PresetD1sitesAIPf.tfib_exit_site_cf_A_holds univ_closure_TfibB_A
  sm np_live_A XM_LIB XN_LIB PAYLOAD_ROOM a_mod_at a_stamp
  np_live_init_A np_live_step_A np_live_tail_A
  preset_callees_A H_preset_lib_x_stmt_A).
Qed.

(* the all-arms room form at the program SLOT (the A' halts top's form; the image-A twin of PresetD2pBPf's S1,
   TFIB_T_room_all_B_closed_stmt_holds), from the driver parts alone (no callee text, no harness walk) *)
Theorem TFIB_T_room_all_A_closed_slot : forall (sm' : list Z -> Z * Z) (XM' XN' : Z -> Z) (PR' : list byte -> Prop),
  (forall rc : YM05.RunCeil,
     preset_lib_contract_x_all (rc := rc) (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
       (L := A_prog_listing) (PA := PI_prog_A (rc := rc)) (ci := CfImg_A)
       sm' np_live_A TfibB ameter_triv XM' XN' PR') ->
  TFIB_T_room_all_concl_A PR'.
Proof.
intros sm' XM' XN' PR' SLOT.
exact (TFIB_T_room_all_A_of_slot tfib_startup_T1_A_at_HS
  PresetD1pAPfC.tfib_drv_main_A_holds
  (fun rc => H_amalloc_realizes_cf_A rc YK11.fx0) H_afree_realizes_cf_A H_aintrin_realizes_xm_cpy_A
  H_aintrin_realizes_xm_set_A
  H_aread_check_stmt_cf_A
  PresetD1preAxPf.tfib_fwrite_site_cf_A_holds PresetD1preAxPf.tfib_refused_site_cf_A_holds
  PresetD1preAxPf.tfib_fprintf_open_site_cf_A_holds PresetD1preAxPf.tfib_fprintf_rderr_site_cf_A_holds
  PresetD1preAxPf.tfib_fprintf_usage_site_cf_A_holds
  PresetD1sitesAIPf.tfib_printf_first_cf_A_holds PresetD1sitesAIPf.tfib_printf_next_cf_A_holds
  PresetD1sitesAIPf.tfib_exit_site_cf_A_holds univ_closure_TfibB_A
  np_live_A np_live_init_A np_live_step_A np_live_tail_A sm' XM' XN' PR' SLOT).
Qed.
Print Assumptions TFIB_T_closed_A_holds.
Print Assumptions TFIB_T_room_all_A_closed_slot.
End closed.

(* the elaborated statement of the closed top: its Section names are now its binders (rule 17:10Z: printed with
   implicit arguments and without notations), and the statement it proves *)
Set Printing Implicit. Unset Printing Notations.
Check TFIB_T_closed_A_holds.
Check TFIB_T_room_all_A_closed_slot.
Print PresetD2pA.TFIB_T_closed_A.
Print PresetTFIB.TFIB_T.
Unset Printing Implicit. Set Printing Notations.
