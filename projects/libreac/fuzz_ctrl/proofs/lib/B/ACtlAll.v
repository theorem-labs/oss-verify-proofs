(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v; 727 of its 778 lines of code are new or changed and 508 lines of the source are left out. *)
(* lib/B/ACtlAll.v -- the TOP of fuzz_ctrl image B's (asan-ubsan) cgif-form walk of LLVMFuzzerTestOneInput in ROUTE (C)
   (the cut carries B.ACtlRtC.ctl_rt_C; no AR_states_vis0_shadow / AR_states_owned_ro anywhere), closed as far as the
   route-C stage lemmas reach.  proves no function (kind: merge; rule 24: a composition of proved stage lemmas, no
   whole function is proved here).  Writer a Theorem Labs lane for a Theorem Labs lane (brief briefs/top.md (a working note, not in this delivery); route-C port 2026-10-29).

   lib/B/ACtl.v section 9 defines ctl_lib_x_CtrlB (the walk's top at the B core's CtrlB, ameter_triv, XL0 and the relro
   span 0x9f1a0 / 0xa15e8), whose remaining arguments are ACtl.v Section Ctl's hypotheses LS_LEAF, CTLRT_ENTRY,
   CHAIN_OF_CUT and the 89 stage hypotheses seg_*, in that order.  ctl_lib_x_CtrlB_all applies it to one term per
   argument, each of the same name as ACtl.v's hypothesis:
   - a stage whose lemma is Qed in a ROUTE-C stage file of this tree is a Let: B.ACtlW<P>.seg_X at
     SK := Reusable.YE2k.tfib_sink_head, B := CtrlB, MT := ameter_triv, XM_LIB = XN_LIB := XL0, RLO / RHI := 0x9f1a0 /
     0xa15e8, FP := [], applied to its own Section hypotheses, and typed by ACtl.v's text (so Coq checks the stage lemma
     against ACtl.v's hypothesis).  A stage file of this tree that is not re-fitted to route C is not used: its stages
     stay ACtl.v hypotheses;
   - section 9's CtrlB_libS is a Theorem Labs lane's Reusable.CtrlBCode.ctrlb_libS, passed directly (also to chain_of_cut);
     CTLRT_ENTRY / CHAIN_OF_CUT are Lets bound to lib/B/ACtlTopFacts.v's proofs; so is every stage-file Section
     hypothesis a proved lemma discharges (section DISCHARGES; the comment above each Let names the lemma and its
     source); the closed numeric facts (RO_OFL, kn_relro, ctl_cat_relro_lo / _hi, RELRO_CAT, GLOBS_FR, FR_RELRO) are
     proved here by computation;
   - provenance of the frame-allocator contracts (a Theorem Labs lane's condition): stack_malloc6_contract / stack_free6_contract are
     a Theorem Labs lane's B.Rt.StackMalloc6.disco_stack_malloc6 / B.Rt.StackFree6S.disco_stack_free6_shared, files of record at
     a working branch 055c2ebca7f, cbrec v9 VERDICT ok
     its build record (a build record, not in this delivery);
   - LS stays a Context parameter, so ACtl.v's LS_LEAF stays a named premise: it is discharged where the top is
     applied, by a Theorem Labs lane's closing lemma B.CtrlClose_B.ctrl_LS_LEAF (reflexivity at fuzz_ctrl's shape);
   - everything else is a NAMED Section hypothesis (sections OPEN-ACTL and OPEN-STAGE) with its text from ACtl.v or
     from the stage file, at the instantiation above.
   Every Section hypothesis left becomes an argument of ctl_lib_x_CtrlB_all when the Section closes (About lists them).
   No Axiom, no Parameter, no Admitted. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YK18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YI16 YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YCfn Reusable.YE2k.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCeg Reusable.YD2l Reusable.YF0m Reusable.YCbp.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlK B.ACtlCut B.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlW0 B.ACtlW1 B.ACtlW2a B.ACtlW2b B.ACtlW3a B.ACtlW3b B.ACtlW4a B.ACtlW4b B.ACtlW4c B.ACtlW4d B.ACtlW4e1 B.ACtlW4e2 B.ACtlW4f B.ACtlW4g B.ACtlW5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtl B.ACtlTopFacts B.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.CtrlBCode.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgBridge B.ProgWorld B.ProgBridgeData B.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0q Reusable.YD1u Reusable.YG05 Reusable.YCej Reusable.YB1w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK04R Reusable.YA0n Reusable.YG01 Reusable.YImgTop.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.APostBase Reusable.MemchrDef Reusable.StackFreeDef Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.Img0 B.Prog.reac_ctrl_identity_fragment_c B.Prog.reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Rt.SetShadow Reusable.SetShadowDef Reusable.SetShadowDefP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.C_reac_ctrl_identity_reply B.Prog.C_reac_ctrl_parse B.Prog.reac_identity_init_c B.Prog.bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_identity_fragment_F_closed B.Prog.reac_identity_init_F_closed B.Rt.Memchr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.declaration_of_F_closed B.Prog.declaration_of_c B.Prog.C_reac_ctrl_classify_box_frame B.Prog.C_reac_box_catalogue_match B.Prog.rng_asan B.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YE2s B.ProgWorld_Fs B.ProgWorldRt B.ProgWorldCtlRt B.Prog.bcmp_wrap_F B.Rt.StackMalloc6 B.Rt.StackFree6S.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldBlkApart.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_headamp_record_verify_F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_box_catalogueF B.Prog.reac_identity_initF B.Prog.asan_memsetF_on B.Prog.memset B.ACtlOwn6 B.Prog.declaration_of_c B.Prog.joined_byte_c B.Prog.C_reac_ctrl_build_as Reusable.AStrcmpDef B.Prog.strcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YD2m Reusable.YD1o Reusable.YF0w Reusable.YF0q Reusable.YG0t B.Prog.CtrlRo B.Prog.declaration_of_F_closed.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.CtrlTopLink Reusable.YF0l B.Rt.IntrinCpySet B.Rt.Strcmp B.Rt.StackMalloc0 B.Rt.StackMalloc1 B.Rt.StackMalloc2 B.BFrameFlagLaw B.ACtlCutC B.Prog.asan_stack_malloc_c B.Prog.asan_stack_malloc_cF_on B.Prog.asan_stack_malloc_0F B.Prog.asan_memset_cF_on B.Prog.asan_memcpy_cF_on B.Prog.asan_memcpyF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.build_dt1_single_c B.Prog.build_dt1_single_F_closed B.Prog.dt1_head_c B.Prog.dt1_head_F B.Prog.name_field_c_on B.Prog.name_fieldF_on B.Prog.bcmp_wrap_c_on B.Prog.bcmp_wrap_on B.Prog.reac_box_model_block_c B.Prog.reac_box_catalogue_match_c B.Prog.C_reac_box_catalogue_match.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.C_reac_ctrl_parsePf B.Prog.C_reac_box_model_blockPb B.Prog.C_reac_ctrl_identity_replyTop B.Prog.C_reac_box_catalogue_matchPfZ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.C_ctrl_emit_as B.Prog.C_ctrl_lay_blockPb.
Module RFG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_fragment_c.
Module KNC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_kind_name_c.
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanRT.
Module RII := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_identity_init_c.

Local Notation segs := Reusable.YB1v.tfibsegs.
Local Notation CtrlB := Reusable.YD2l.CtrlB.
Local Notation MT0 := Reusable.YCbp.ameter_triv.

(* ---------------------------------------------------------------------------------------------------------
   CLOSED FACTS the stage files ask of the top, proved here as top-level lemmas (so Check / Print Assumptions
   can name them); section DISCHARGES binds each to the stage files' hypothesis name. *)
Section CtlAllFacts.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
(* model_block's JOIN_0013 table lies in a zero-shadow range of CtrlB (computation over as_zero_shadow) *)
Lemma ctlall_HZS_J13 : B.Prog.CtrlRo.in_zs CtrlB B.Prog.reac_box_model_block_c.JOIN_0013 32.
Proof.
  unfold B.Prog.CtrlRo.in_zs.
  assert (H : existsb (fun r : Z * Z => ((fst r <=? B.Prog.reac_box_model_block_c.JOIN_0013) && (B.Prog.reac_box_model_block_c.JOIN_0013 + 32 <=? fst r + snd r))%bool) (Reusable.YG0f.as_zero_shadow CtrlB) = true) by (vm_compute; reflexivity).
  apply existsb_exists in H as ([q m] & Hin & Hb). exists q, m. apply andb_true_iff in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in *. split; [exact Hin | lia].
Qed.
(* model_block's JOIN_0014 table lies in a zero-shadow range of CtrlB (computation) *)
Lemma ctlall_HZS_J14 : B.Prog.CtrlRo.in_zs CtrlB B.Prog.reac_box_model_block_c.JOIN_0014 32.
Proof.
  unfold B.Prog.CtrlRo.in_zs.
  assert (H : existsb (fun r : Z * Z => ((fst r <=? B.Prog.reac_box_model_block_c.JOIN_0014) && (B.Prog.reac_box_model_block_c.JOIN_0014 + 32 <=? fst r + snd r))%bool) (Reusable.YG0f.as_zero_shadow CtrlB) = true) by (vm_compute; reflexivity).
  apply existsb_exists in H as ([q m] & Hin & Hb). exists q, m. apply andb_true_iff in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in *. split; [exact Hin | lia].
Qed.
(* the build_as frame table lies in the relro span (arithmetic) *)
Lemma ctlall_FR_RELRO : 0x9f1a0 <= 0xa0600 /\ 0xa0708 <= 0xa15e8.
Proof.
  lia.
Qed.
(* the build_as frame table is a registered global (computation) *)
Lemma ctlall_GLOBS_FR : In (0xa0600, 264) B.ProgBridgeData.ctrl_ro_globs.
Proof.
  cbv [B.ProgBridgeData.ctrl_ro_globs].
  repeat (first [left; reflexivity | right]).
Qed.
(* the catalogue table [CM_T, CM_T + 3256) is the registered global (0x9f620, 0xcb8) of ctrl_ro_globs (computation) *)
Lemma ctlall_CM_HG17 : exists q sz, In (q, sz) B.ProgBridgeData.ctrl_ro_globs /\ q <= B.Prog.reac_box_catalogue_match_c.CM_T /\ B.Prog.reac_box_catalogue_match_c.CM_T + 3256 <= q + sz.
Proof.
  exists 0x9f620, 0xcb8. split; [cbv [B.ProgBridgeData.ctrl_ro_globs]; repeat (first [left; reflexivity | right]) |].
  unfold B.Prog.reac_box_catalogue_match_c.CM_T. lia.
Qed.
(* the catalogue table ends in the relro span (arithmetic) *)
Lemma ctlall_CM_HRHI : B.Prog.C_reac_box_catalogue_match.A_CM_TBL + B.Prog.C_reac_box_catalogue_match.CM_ROWS <= 0xa15e8.
Proof.
  unfold B.Prog.C_reac_box_catalogue_match.A_CM_TBL, B.Prog.C_reac_box_catalogue_match.CM_ROWS. lia.
Qed.
(* the catalogue table starts in the relro span (arithmetic) *)
Lemma ctlall_CM_HRLO : 0x9f1a0 <= B.Prog.C_reac_box_catalogue_match.A_CM_TBL.
Proof.
  unfold B.Prog.C_reac_box_catalogue_match.A_CM_TBL. lia.
Qed.
(* the catalogue and the build_as row table lie in the relro span (computation; ACtlW1.v) *)
Lemma ctlall_RELRO_CAT : 0x9f1a0 <= B.ACtlCutP.SM.CAT /\ B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) <= 0xa15e8.
Proof.
  vm_compute. split; intro H; discriminate H.
Qed.
(* the box catalogue ends in the relro span (computation; ACtlW4f.v: owner the top) *)
Lemma ctlall_ctl_cat_relro_hi : B.ACtlCutP.SM.CAT + B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N <= 0xa15e8.
Proof.
  vm_compute. intro H; discriminate H.
Qed.
(* the box catalogue starts in the relro span (computation; ACtlW4f.v: owner the top) *)
Lemma ctlall_ctl_cat_relro_lo : 0x9f1a0 <= B.ACtlCutP.SM.CAT.
Proof.
  vm_compute. intro H; discriminate H.
Qed.
(* W2b's two-window form of the set_shadow post, proved here with lib/B/ProgWorld.v's own proof of ctl_post_set_shadow (its lemmas rt_post_frame_vis, rw_cells_CB_of_present, mrd_of_aview_some; the window list is generic there) *)
Lemma ctlall_ctl_post_set_shadow : forall (W : Reusable.YA0n.world segs) (mem mem' : word -> option byte) (sp q n v : Z),
    0 <= q -> q + n <= 2 ^ 64 -> 0 < n ->
    (forall a, q <= a < q + n -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem a) ->
    (forall i, 0 <= i < n -> Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem' (q + i) = Some v) ->
    B.ProgWorld.rt_post_frame W mem mem' ((q, q + n) :: (sp - Reusable.YG0d.ESTACK, sp) :: nil) ->
    B.ProgWorld.munch_vis (Reusable.YA0n.w_H W) ((q, q + n) :: (sp - Reusable.YG0d.ESTACK, sp) :: nil) mem mem' /\
    B.ProgWorld.wmono_vis (Reusable.YA0n.w_H W) mem mem' /\
    lib.Lib.Step.rw_cells B.Img0.rsegs mem' q (lib.Lib.Cells.CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n)) :: nil).
Proof.
  intros W mem mem' sp q n v Hq Hqn Hn Hpres Hv Hf.
  destruct (B.ProgWorld.rt_post_frame_vis W mem mem' _ Hf) as [Hm Hw].
  split; [exact Hm | split; [exact Hw |]].
  destruct Hf as [_ Hp].
  apply B.ProgWorld.rw_cells_CB_of_present.
  - apply repeat_length.
  - exact Hq.
  - lia.
  - intros i Hi. rewrite nth_error_repeat by exact Hi.
    destruct (Hp _ (Hpres (q + Z.of_nat i) ltac:(lia))) as [Hh _].
    exact (B.ProgWorld.mrd_of_aview_some W mem' _ _ Hh (Hv (Z.of_nat i) ltac:(lia))).
  - intros i Hi. destruct (Hp _ (Hpres (q + i) ltac:(lia))) as [_ [b Eb]].
    rewrite Eb. discriminate.
Qed.
(* the KIND_NAME table lies in [0x9f1a0, 0xa15e8) (computation; ACtlW3b.v: owner the top) *)
Lemma ctlall_kn_relro : 0x9f1a0 <= KNC.KIND_NAME /\ KNC.KIND_NAME + 112 <= 0xa15e8.
Proof.
  vm_compute. split; intro H; discriminate H.
Qed.
End CtlAllFacts.

Section CtlAll.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.

(* ACtl.v section 1's notations at the top's instantiation. *)
Local Notation ctlcx := ACtlCut.ctlcx.
Local Notation ctlcut := ACtlCut.ctlcut.
Local Notation cut_pc := ACtlCut.cut_pc.
Local Notation cut_own := ACtlCut.cut_own.
Local Notation cut_kmax := ACtlCut.cut_kmax.
Local Notation cut_body := ACtlCut.cut_body.
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation c_md := ACtlCut.c_md.
Local Notation c_mem := ACtlCut.c_mem.
Local Notation CB cx := (ACtlCut.ctl_base CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 cx).
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := Reusable.YE2k.tfib_sink_head) CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] POST X).
Local Notation ctl_post := (ACtlCut.ctl_post CtrlB MT0 B.ACtl.XL0).

(* The cut records of ACtlCutP.v this file names: all 90 (every one is the entry or an exit of a stage). *)
Local Notation C_ENTRY := (ACtlCutP.C_ENTRY CtrlB).
Local Notation C_B81090 := (ACtlCutP.C_B81090 CtrlB).
Local Notation C_B810c4 := (ACtlCutP.C_B810c4 CtrlB).
Local Notation C_B81220 := (ACtlCutP.C_B81220 CtrlB).
Local Notation C_B81548_at := (ACtlCutP.C_B81548_at CtrlB).
Local Notation C_B81550 := (ACtlCutP.C_B81550 CtrlB).
Local Notation C_B815fc := (ACtlCutP.C_B815fc CtrlB).
Local Notation C_B81640 := (ACtlCutP.C_B81640 CtrlB).
Local Notation C_B8168c := (ACtlCutP.C_B8168c CtrlB).
Local Notation C_B8169c := (ACtlCutP.C_B8169c CtrlB).
Local Notation C_B816ec_at := (ACtlCutP.C_B816ec_at CtrlB).
Local Notation C_B81710_at := (ACtlCutP.C_B81710_at CtrlB).
Local Notation C_B81764_at := (ACtlCutP.C_B81764_at CtrlB).
Local Notation C_B8177c_at := (ACtlCutP.C_B8177c_at CtrlB).
Local Notation C_B817a4_at := (ACtlCutP.C_B817a4_at CtrlB).
Local Notation C_B817ec_at := (ACtlCutP.C_B817ec_at CtrlB).
Local Notation C_B81834_at := (ACtlCutP.C_B81834_at CtrlB).
Local Notation C_B81860_at := (ACtlCutP.C_B81860_at CtrlB).
Local Notation C_B818a8_at := (ACtlCutP.C_B818a8_at CtrlB).
Local Notation C_B81914_at := (ACtlCutP.C_B81914_at CtrlB).
Local Notation C_B8194c_at := (ACtlCutP.C_B8194c_at CtrlB).
Local Notation C_B819a8_at := (ACtlCutP.C_B819a8_at CtrlB).
Local Notation C_B819d0_at := (ACtlCutP.C_B819d0_at CtrlB).
Local Notation C_B81a50_at := (ACtlCutP.C_B81a50_at CtrlB).
Local Notation C_B81a68_at := (ACtlCutP.C_B81a68_at CtrlB).
Local Notation C_B81aa0_at := (ACtlCutP.C_B81aa0_at CtrlB).
Local Notation C_B81ac0_at := (ACtlCutP.C_B81ac0_at CtrlB).
Local Notation C_B81c58 := (ACtlCutP.C_B81c58 CtrlB).
Local Notation C_B81c60 := (ACtlCutP.C_B81c60 CtrlB).
Local Notation C_B81ca8 := (ACtlCutP.C_B81ca8 CtrlB).
Local Notation C_B81cb0 := (ACtlCutP.C_B81cb0 CtrlB).
Local Notation C_B81d18 := (ACtlCutP.C_B81d18 CtrlB).
Local Notation C_B81d28 := (ACtlCutP.C_B81d28 CtrlB).
Local Notation C_B81d68 := (ACtlCutP.C_B81d68 CtrlB).
Local Notation C_B81d80 := (ACtlCutP.C_B81d80 CtrlB).
Local Notation C_B81da8 := (ACtlCutP.C_B81da8 CtrlB).
Local Notation C_B81dbc := (ACtlCutP.C_B81dbc CtrlB).
Local Notation C_B81dd4 := (ACtlCutP.C_B81dd4 CtrlB).
Local Notation C_B81de8 := (ACtlCutP.C_B81de8 CtrlB).
Local Notation C_B81e08 := (ACtlCutP.C_B81e08 CtrlB).
Local Notation C_B81ec4_at := (ACtlCutP.C_B81ec4_at CtrlB).
Local Notation C_B81f50_at := (ACtlCutP.C_B81f50_at CtrlB).
Local Notation C_B81f78_at := (ACtlCutP.C_B81f78_at CtrlB).
Local Notation C_B81fbc_at := (ACtlCutP.C_B81fbc_at CtrlB).
Local Notation C_B82048_at := (ACtlCutP.C_B82048_at CtrlB).
Local Notation C_B82098_at := (ACtlCutP.C_B82098_at CtrlB).
Local Notation C_B8215c_at := (ACtlCutP.C_B8215c_at CtrlB).
Local Notation C_B82174_at := (ACtlCutP.C_B82174_at CtrlB).
Local Notation C_B82180_at := (ACtlCutP.C_B82180_at CtrlB).
Local Notation C_B821ec_at := (ACtlCutP.C_B821ec_at CtrlB).
Local Notation C_B8226c_at := (ACtlCutP.C_B8226c_at CtrlB).
Local Notation C_B82304_at := (ACtlCutP.C_B82304_at CtrlB).
Local Notation C_B82308_at := (ACtlCutP.C_B82308_at CtrlB).
Local Notation C_B82340_at := (ACtlCutP.C_B82340_at CtrlB).
Local Notation C_B8235c_at := (ACtlCutP.C_B8235c_at CtrlB).
Local Notation C_B82378_at := (ACtlCutP.C_B82378_at CtrlB).
Local Notation C_B8237c_at := (ACtlCutP.C_B8237c_at CtrlB).
Local Notation C_B823d8_at := (ACtlCutP.C_B823d8_at CtrlB).
Local Notation C_B82464_at := (ACtlCutP.C_B82464_at CtrlB).
Local Notation C_B82468_at := (ACtlCutP.C_B82468_at CtrlB).
Local Notation C_B82634_at := (ACtlCutP.C_B82634_at CtrlB).
Local Notation C_B8264c_at := (ACtlCutP.C_B8264c_at CtrlB).
Local Notation C_B82668_at := (ACtlCutP.C_B82668_at CtrlB).
Local Notation C_B82728_at := (ACtlCutP.C_B82728_at CtrlB).
Local Notation C_B827f8_at := (ACtlCutP.C_B827f8_at CtrlB).
Local Notation C_B8283c_at := (ACtlCutP.C_B8283c_at CtrlB).
Local Notation C_B82844_at := (ACtlCutP.C_B82844_at CtrlB).
Local Notation C_B82878_at := (ACtlCutP.C_B82878_at CtrlB).
Local Notation C_B82888_at := (ACtlCutP.C_B82888_at CtrlB).
Local Notation C_B828a4_at := (ACtlCutP.C_B828a4_at CtrlB).
Local Notation C_B828b4_at := (ACtlCutP.C_B828b4_at CtrlB).
Local Notation C_B8292c_at := (ACtlCutP.C_B8292c_at CtrlB).
Local Notation C_B82aa4_at := (ACtlCutP.C_B82aa4_at CtrlB).
Local Notation C_B82abc_at := (ACtlCutP.C_B82abc_at CtrlB).
Local Notation C_B82af8_at := (ACtlCutP.C_B82af8_at CtrlB).
Local Notation C_B82b38_at := (ACtlCutP.C_B82b38_at CtrlB).
Local Notation C_B82b5c_at := (ACtlCutP.C_B82b5c_at CtrlB).
Local Notation C_B82bcc_at := (ACtlCutP.C_B82bcc_at CtrlB).
Local Notation C_B82bf4_at := (ACtlCutP.C_B82bf4_at CtrlB).
Local Notation C_B82c24_at := (ACtlCutP.C_B82c24_at CtrlB).
Local Notation C_B82c38_at := (ACtlCutP.C_B82c38_at CtrlB).
Local Notation C_B82c84_at := (ACtlCutP.C_B82c84_at CtrlB).
Local Notation C_B82c90_at := (ACtlCutP.C_B82c90_at CtrlB).
Local Notation C_B82ca0_at := (ACtlCutP.C_B82ca0_at CtrlB).
Local Notation C_B82d1c_at := (ACtlCutP.C_B82d1c_at CtrlB).
Local Notation C_B82eac := (ACtlCutP.C_B82eac CtrlB).
Local Notation C_B82ecc := (ACtlCutP.C_B82ecc CtrlB).
Local Notation C_Jrel := (ACtlCutP.C_Jrel CtrlB).
Local Notation C_B82f48 := (ACtlCutP.C_B82f48 CtrlB).
Local Notation C_B82f5c := (ACtlCutP.C_B82f5c CtrlB).
Local Notation ctl_post_leaf := (@B.ACtl.ctl_post_leaf fx rc CtrlB MT0 B.ACtl.XL0).

(* ---------------------------------------------------------------------------------------------------------
   OPEN-ACTL: ACtl.v Section Ctl's hypotheses that no proved route-C lemma discharges yet, with ACtl.v's text. *)
Hypothesis LS_LEAF : forall pl fs K, @lib.Reusable.YO09.LIBK LS pl fs K = K (lib.Reusable.YO09.LL 0 fs []).

(* ---------------------------------------------------------------------------------------------------------
   OPEN-STAGE: Section hypotheses of the route-C stage lemmas used below that no proved lemma discharges yet,
   with the stage file's text at the instantiation. *)

(* ---------------------------------------------------------------------------------------------------------
   DISCHARGES: ACtl.v and stage-file Section hypotheses discharged by proved lemmas or by computation. *)
(* lib/B/Prog/bcmp_wrap_on.v bcmp_wrap_holds_F_on *)
Let ABCMP : B.Prog.bcmp_wrap_c_on.bcmp_wrap_contract_F_on := B.Prog.bcmp_wrap_on.bcmp_wrap_holds_F_on.
(* the core: Reusable.YD2l.CtrlB_syms *)
Let TFIB_SYMS : Reusable.YF0m.CtrlTSyms CtrlB := Reusable.YD2l.CtrlB_syms.
(* the core: Reusable.YF0q.afree_realizes_closed *)
Let AFREE : Reusable.YG0d.afree_realizes segs CtrlB :=
    Reusable.YF0q.afree_realizes_closed CtrlB TFIB_SYMS (fun _ => eq_refl).
(* the core: Reusable.YG0q.AR_laws_ok *)
Let LAWS : Reusable.YG0d.AR_laws segs CtrlB := Reusable.YG0q.AR_laws_ok segs CtrlB.
(* the core: Reusable.YG05.model_laws_ok at Reusable.YCej.Tfib_universe_ok *)
Let ML : Reusable.YG0d.model_laws (Reusable.YG0f.as_universe CtrlB) :=
    Reusable.YG05.model_laws_ok _ Reusable.YCej.Tfib_universe_ok.
(* the core: Reusable.YCeg.tl_env at Reusable.CtrlBCode.ctrlb_libS *)
Let errno_low : Reusable.YCbq.api_env segs CtrlB := Reusable.YCeg.tl_env CtrlB Reusable.CtrlBCode.ctrlb_libS.
(* the core: Reusable.YCeg.tfib_segs_low *)
Let segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd :=
    Reusable.YCeg.tfib_segs_low.
(* the core: Reusable.YCbp.afree04_rule_triv (the rule at ameter_triv from the free contract) *)
Let AFREE4 :=
    @Reusable.YCbp.afree04_rule_triv fx rc Reusable.YE2k.tfib_sink_head segs CtrlB segs_low errno_low LAWS ML
    AFREE.
(* the core: Reusable.YD1u.tfib_AIL *)
Let AIL := Reusable.YD1u.tfib_AIL CtrlB TFIB_SYMS.
(* the core: Reusable.YF0w.tfib_amalloc_realizes (as_dhash CtrlB = tfib_dhash by definition) *)
Let AMALLOC : Reusable.YG0d.amalloc_realizes segs CtrlB :=
    Reusable.YF0w.tfib_amalloc_realizes CtrlB TFIB_SYMS (fun _ => eq_refl).
(* the core: Reusable.YCbp.amalloc04_rule_triv (the rule at ameter_triv from the malloc contract) *)
Let AMALLOC4 :=
    @Reusable.YCbp.amalloc04_rule_triv fx rc Reusable.YE2k.tfib_sink_head segs CtrlB segs_low errno_low LAWS ML
    AMALLOC.
(* a Theorem Labs lane's lib/B/Rt/Memchr.v (by path, 80272cf7f78) *)
Let AMEMCHR : Reusable.MemchrDef.amemchr_realizes segs CtrlB 0x42ab0 :=
    B.Rt.Memchr.memchr_icpt_realizes CtrlB LAWS TFIB_SYMS.
(* a Theorem Labs lane's lib/B/Rt/IntrinCpySet.v asan_memcpy_aintrin (a working branch, v9 VERDICT ok) *)
Let AMEMCPY : Reusable.YG0d.aintrin_realizes segs CtrlB Reusable.YG0d.OCpy Reusable.YB1w.tfib_A_asan_memcpy :=
    B.Rt.IntrinCpySet.asan_memcpy_aintrin CtrlB TFIB_SYMS.
(* a Theorem Labs lane's lib/B/Rt/IntrinCpySet.v asan_memset_aintrin *)
Let AMEMSET : Reusable.YG0d.aintrin_realizes segs CtrlB Reusable.YG0d.OSet Reusable.YB1w.tfib_A_asan_memset :=
    B.Rt.IntrinCpySet.asan_memset_aintrin CtrlB TFIB_SYMS.
(* the core: Reusable/YG0t.v:473 astack_free_law_ok *)
Let ASF : Reusable.YG0d.astack_free_law segs CtrlB := Reusable.YG0t.astack_free_law_ok segs CtrlB.
(* a Theorem Labs lane's lib/B/Rt/SetShadow.v (presence form) *)
Let ASF00 : Reusable.SetShadowDefP.aset_shadow_realizesP segs CtrlB 0x55024 0 :=
    B.Rt.SetShadow.ctrl_set_shadow_00P CtrlB LAWS TFIB_SYMS.
(* a Theorem Labs lane's lib/B/Rt/SetShadow.v (presence form) *)
Let ASF8 : Reusable.SetShadowDefP.aset_shadow_realizesP segs CtrlB 0x55144 0xf8 :=
    B.Rt.SetShadow.ctrl_set_shadow_f8P CtrlB LAWS TFIB_SYMS.
(* a Theorem Labs lane's lib/B/Rt/StackMalloc0.v ctrl_stack_malloc0 *)
Let ASM0 : Reusable.YG0d.astack_malloc_realizes segs CtrlB 0 :=
    B.Rt.StackMalloc0.ctrl_stack_malloc0 fx CtrlB LAWS TFIB_SYMS.
(* a Theorem Labs lane's lib/B/Rt/StackMalloc1.v ctrl_stack_malloc1 *)
Let ASM1 : Reusable.YG0d.astack_malloc_realizes segs CtrlB 1 :=
    B.Rt.StackMalloc1.ctrl_stack_malloc1 fx CtrlB LAWS TFIB_SYMS.
(* a Theorem Labs lane's lib/B/Rt/StackMalloc2.v ctrl_stack_malloc2 *)
Let ASM2 : Reusable.YG0d.astack_malloc_realizes segs CtrlB 2 :=
    B.Rt.StackMalloc2.ctrl_stack_malloc2 fx CtrlB LAWS TFIB_SYMS.
(* a Theorem Labs lane's lib/B/ProgBridgeData.v ctrl_ro_globs_marked at CtrlB, its HB := Reusable.YD2l.CtrlB_syms (= TFIB_SYMS) *)
Let GM : B.Prog.CtrlRo.globs_marked segs CtrlB B.ProgBridgeData.ctrl_ro_globs :=
    B.ProgBridgeData.ctrl_ro_globs_marked CtrlB TFIB_SYMS.
(* lib/B/ACtl.v section 9 *)
Let RELRO_IMG : forall a, 0x9f1a0 <= a < 0xa15e8 -> Reusable.YG0d.in_img segs a := B.ACtl.relro_img_CtrlB.
(* CtrlB's code table, by conversion *)
Let PC1 : Reusable.YG0f.pc_stack_malloc (Reusable.YG0f.as_code CtrlB) 1 = B.Prog.asan_stack_malloc_c.ASAN_STACK_MALLOC_1 :=
    eq_refl.
(* the core: Reusable.YG05.stack_malloc_progress (ACtlW0.v's form) *)
Let SMP : Reusable.YCbq.stack_malloc_progressP CtrlB :=
    fun s cid => Reusable.YG05.stack_malloc_progress (Reusable.YG0f.as_universe CtrlB) s cid.
(* a Theorem Labs lane's lib/B/BFrameFlagLaw.v frame_flag_law_ok (dddf4fa8e61, v11 VERDICT ok) *)
Let FFL : Reusable.YCbq.frame_flag_lawP segs CtrlB := B.BFrameFlagLaw.frame_flag_law_ok CtrlB.
(* a Theorem Labs lane's lib/B/Prog/build_dt1_single_F_closed.v (at head lib/B/Prog/build_dt1_single_F_closed.v:27; from a working branch 467b2c94dcc) build_dt1_single_F_holds_on_closed *)
Let HBD : B.Prog.build_dt1_single_c.build_dt1_single_contract_F_on :=
    B.Prog.build_dt1_single_F_closed.build_dt1_single_F_holds_on_closed.
(* a Theorem Labs lane's lib/B/Prog/dt1_head_F.v:117 dt1_head_F_holds_on *)
Let HDH : B.Prog.dt1_head_c.dt1_head_contract_F_on := B.Prog.dt1_head_F.dt1_head_F_holds_on.
(* a Theorem Labs lane's lib/B/ACtlCutC.v ctrl_img_shadow_vis *)
Let HIMGSH : B.Prog.CtrlRo.img_shadow_vis segs CtrlB := B.ACtlCutC.ctrl_img_shadow_vis CtrlB TFIB_SYMS LAWS.
(* lib/B/Prog/asan_memcpyF_on.v asan_memcpy_holds_F_on *)
Let HMC : B.Prog.asan_memcpy_cF_on.asan_memcpy_contract_F_on := B.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on.
(* lib/B/Prog/asan_memsetF_on.v at memset_holds *)
Let HMS : B.Prog.asan_memset_cF_on.asan_memset_contract_F_on :=
    B.Prog.asan_memsetF_on.asan_memset_holds_F_on B.Prog.memset.memset_holds.
(* a Theorem Labs lane's lib/B/Prog/name_fieldF_on.v name_field_holds_F_on at the memset _on run (fc9d52761d0) *)
Let HNF : B.Prog.name_field_c_on.name_field_contract_F_on := B.Prog.name_fieldF_on.name_field_holds_F_on HMS.
(* a Theorem Labs lane's lib/B/Prog/asan_stack_malloc_0F.v asan_stack_malloc_0_holds_F_on (a working branch 4fcf3722ed4, v12 ok) *)
Let HSM : B.Prog.asan_stack_malloc_cF_on.asan_stack_malloc_0_contract_F_on :=
    B.Prog.asan_stack_malloc_0F.asan_stack_malloc_0_holds_F_on.
(* model_block's JOIN_0013 table lies in a zero-shadow range of CtrlB (computation over as_zero_shadow): ctlall_HZS_J13 above *)
Let HZS_J13 : B.Prog.CtrlRo.in_zs CtrlB B.Prog.reac_box_model_block_c.JOIN_0013 32 := ctlall_HZS_J13.
(* model_block's JOIN_0014 table lies in a zero-shadow range of CtrlB (computation): ctlall_HZS_J14 above *)
Let HZS_J14 : B.Prog.CtrlRo.in_zs CtrlB B.Prog.reac_box_model_block_c.JOIN_0014 32 := ctlall_HZS_J14.
(* CtrlB's code table, by conversion *)
Let PC0 : Reusable.YG0f.pc_stack_malloc (Reusable.YG0f.as_code CtrlB) 0 = 251636 := eq_refl.
(* a Theorem Labs lane's lib/B/Prog/C_reac_box_model_blockPb.v pb_reac_box_model_block (VIS0-free) *)
Let TMB :=
    @B.Prog.C_reac_box_model_blockPb.pb_reac_box_model_block fx rc Reusable.YE2k.tfib_sink_head CtrlB LAWS
    segs_low ML ASF FFL 0x9f1a0 0xa15e8 B.ProgBridgeData.ctrl_ro_globs RELRO_IMG TFIB_SYMS errno_low SMP ASM0
    PC0 GM HZS_J13 HZS_J14 HIMGSH HSM HMS HMC HBD HDH HNF.
(* a Theorem Labs lane's lib/B/Prog/C_ctrl_lay_blockPb.v pb_ctrl_lay_block (VIS0-free; HGM := GM, TMB above) *)
Let TLAY :=
    @B.Prog.C_ctrl_lay_blockPb.pb_ctrl_lay_block fx rc Reusable.YE2k.tfib_sink_head 0x9f1a0 0xa15e8 RELRO_IMG
    CtrlB B.ProgBridgeData.ctrl_ro_globs LAWS errno_low ML SMP ASM1 ASF PC1 TFIB_SYMS GM TMB.
(* a Theorem Labs lane's lib/B/Prog/C_ctrl_emit_as.v pb_ctrl_emit_as (4b7386f8736, re-pointed to the record core; a working branch 8249a22a3e4) *)
Let EMIT :=
    @B.Prog.C_ctrl_emit_as.pb_ctrl_emit_as fx rc Reusable.YE2k.tfib_sink_head 0x9f1a0 0xa15e8 CtrlB RELRO_IMG
    TFIB_SYMS LAWS B.ProgBridgeData.ctrl_ro_globs GM TLAY.
(* the build_as frame table lies in the relro span (arithmetic): ctlall_FR_RELRO above *)
Let FR_RELRO : 0x9f1a0 <= 0xa0600 /\ 0xa0708 <= 0xa15e8 := ctlall_FR_RELRO.
(* the build_as frame table is a registered global (computation): ctlall_GLOBS_FR above *)
Let GLOBS_FR : In (0xa0600, 264) B.ProgBridgeData.ctrl_ro_globs := ctlall_GLOBS_FR.
(* a Theorem Labs lane's lib/B/Prog/C_reac_ctrl_build_as.v pb_reac_ctrl_build_as (by path, d10821c397d; VIS0-free) *)
Let BUILD_AS : B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_spec (SK := Reusable.YE2k.tfib_sink_head) 0x9f1a0 0xa15e8 CtrlB B.ProgBridgeData.ctrl_ro_globs :=
    @B.Prog.C_reac_ctrl_build_as.pb_reac_ctrl_build_as fx rc Reusable.YE2k.tfib_sink_head 0x9f1a0 0xa15e8
    RELRO_IMG CtrlB B.ProgBridgeData.ctrl_ro_globs LAWS TFIB_SYMS EMIT GM GLOBS_FR FR_RELRO.
(* lib/B/ACtlTopFacts.v chain_of_cut *)
Let CHAIN_OF_CUT := B.ACtlTopFacts.chain_of_cut CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 Reusable.CtrlBCode.ctrlb_libS.
(* the catalogue table [CM_T, CM_T + 3256) is the registered global (0x9f620, 0xcb8) of ctrl_ro_globs (computation): ctlall_CM_HG17 above *)
Let CM_HG17 : exists q sz, In (q, sz) B.ProgBridgeData.ctrl_ro_globs /\ q <= B.Prog.reac_box_catalogue_match_c.CM_T /\ B.Prog.reac_box_catalogue_match_c.CM_T + 3256 <= q + sz := ctlall_CM_HG17.
(* the catalogue table ends in the relro span (arithmetic): ctlall_CM_HRHI above *)
Let CM_HRHI : B.Prog.C_reac_box_catalogue_match.A_CM_TBL + B.Prog.C_reac_box_catalogue_match.CM_ROWS <= 0xa15e8 := ctlall_CM_HRHI.
(* the catalogue table starts in the relro span (arithmetic): ctlall_CM_HRLO above *)
Let CM_HRLO : 0x9f1a0 <= B.Prog.C_reac_box_catalogue_match.A_CM_TBL := ctlall_CM_HRLO.
(* lib/B/ACtlTopFacts.v ctlrt_entry (route C: B.ProgWorldCtlRtC.ctl_rt_C_of_AR) *)
Let CTLRT_ENTRY := B.ACtlTopFacts.ctlrt_entry CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 TFIB_SYMS.
(* lib/B/ProgBridge.v fevt_of_evtF *)
Let FEVT : forall (RNG : Lib.ExecF.footprint) (P : machine_state -> Prop) (ms : machine_state),
  Lib.ExecF.evtF B.Img0.rsegs RNG P ms -> exists ms', Reusable.YK04R.fsteps segs RNG ms ms' /\ P ms' :=
    B.ProgBridge.fevt_of_evtF.
(* trivial at ameter_triv *)
Let HMOK : forall S m, Reusable.YC5d.mo_ok MT0 S m := fun _ _ => I.
(* trivial at ameter_triv *)
Let HMOLE : forall (S S' : Reusable.YG00.astate) (m : Z), Reusable.YC5d.mo_le MT0 S S' m := fun _ _ _ => I.
(* by computation (CtrlB's code record) *)
Let HPCF : Reusable.YG0f.pc_wrap_free (Reusable.YG0f.as_code CtrlB) = Reusable.YB1w.tfib_A_free := eq_refl.
(* by computation (CtrlB's code record) *)
Let HPCM : Reusable.YG0f.pc_wrap_malloc (Reusable.YG0f.as_code CtrlB) = Reusable.YB1w.tfib_A_malloc := eq_refl.
(* the core: Reusable.YE2s.bcmp_icpt_contract (BCMP_WRAP = 0x42aac) *)
Let H_bcmp : Reusable.YG0d.abcmp_realizes segs CtrlB B.Prog.bcmp_wrap_c.BCMP_WRAP :=
    Reusable.YE2s.bcmp_icpt_contract CtrlB LAWS TFIB_SYMS.
(* a Theorem Labs lane's trampoline constant is 0x42aa0, by reflexivity *)
Let STRCMP_AT : B.Rt.Strcmp.STRCMP_TRAMP = 0x42aa0 := eq_refl.
(* a Theorem Labs lane's lib/B/Rt/Strcmp.v:468 ctrl_strcmp_tramp at B_strcmp_tramp_entry := 0x42aa0, moved along STRCMP_AT (B_strcmp_tramp_at : 0x42aa0 = STRCMP_WRAP is eq_refl too) *)
Let H_strcmp : Reusable.AStrcmpDef.astrcmp_realizes segs CtrlB 0x42aa0 :=
    eq_rect B.Rt.Strcmp.STRCMP_TRAMP (fun e => Reusable.AStrcmpDef.astrcmp_realizes segs CtrlB e)
    (B.Rt.Strcmp.ctrl_strcmp_tramp CtrlB LAWS TFIB_SYMS) 0x42aa0 STRCMP_AT.
(* the core: Reusable/YCeg.v:64 Hwx_tfa (Qed :65), stated over tfibsegs, the same term as segs *)
Let Hwx : Reusable.YK04.wx_segs_nowrap segs := Reusable.YCeg.Hwx_tfa.
(* a Theorem Labs lane's lib/B/Prog/C_reac_ctrl_parsePf.v pb_reac_ctrl_parse (3e03efa9e16; premises errno_low ML SMP ASM1 PC1 ASF TS, no VIS0) *)
Let PARSE : B.Prog.C_reac_ctrl_parse.treac_ctrl_parse_spec (SK := Reusable.YE2k.tfib_sink_head) segs CtrlB 0x9f1a0 0xa15e8 :=
    @B.Prog.C_reac_ctrl_parsePf.pb_reac_ctrl_parse fx rc Reusable.YE2k.tfib_sink_head CtrlB 0x9f1a0 0xa15e8
    errno_low ML SMP ASM1 PC1 ASF TFIB_SYMS.
(* the catalogue and the build_as row table lie in the relro span (computation; ACtlW1.v): ctlall_RELRO_CAT above *)
Let RELRO_CAT : 0x9f1a0 <= B.ACtlCutP.SM.CAT /\ B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) <= 0xa15e8 := ctlall_RELRO_CAT.
(* a Theorem Labs lane's lib/Reusable/CtrlTopLink.v ctrlb_RO (a working branch 204fa48d73b, v11 VERDICT ok) *)
Let RO_OFL : @Reusable.APostBase.ro_below_ofl segs 0x9f1a0 0xa15e8 Reusable.YE2k.tfib_sink_head :=
    Reusable.CtrlTopLink.ctrlb_RO.
(* a Theorem Labs lane's lib/B/Prog/C_reac_ctrl_classify_box_frame.v pb_reac_ctrl_classify_box_frame, the VIS0-free form (0371159a0f7: RELRO_IMG, LAWS, TPARSE, CtrlTSyms) *)
Let TCLS : B.Prog.C_reac_ctrl_classify_box_frame.treac_ctrl_classify_box_frame_spec CtrlB 0x9f1a0 0xa15e8 :=
    B.Prog.C_reac_ctrl_classify_box_frame.pb_reac_ctrl_classify_box_frame CtrlB 0x9f1a0 0xa15e8 RELRO_IMG LAWS
    PARSE TFIB_SYMS.
(* CtrlB's code table is Tfib_code by definition *)
Let TL_CODE : Reusable.YG0f.as_code CtrlB = Reusable.YF0l.Tfib_code := eq_refl.
(* a Theorem Labs lane's lib/B/Prog/C_reac_box_catalogue_matchPfZ.v cmPf_top (VIS0-free; its premises 2-4 proved here) *)
Let TMATCH : B.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := Reusable.YE2k.tfib_sink_head) 0x9f1a0 0xa15e8 CtrlB :=
    @B.Prog.C_reac_box_catalogue_matchPfZ.cmPf_top fx rc Reusable.YE2k.tfib_sink_head CtrlB LAWS ASF segs_low
    errno_low ML SMP ASM2 TL_CODE 0x9f1a0 0xa15e8 RELRO_IMG B.ProgBridgeData.ctrl_ro_globs PARSE TMB ABCMP
    TFIB_SYMS CM_HG17 CM_HRLO CM_HRHI.
(* a Theorem Labs lane's lib/B/Prog/C_reac_ctrl_identity_replyTop.v pb_reac_ctrl_identity_reply (VIS0-free) *)
Let TREPLY : B.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec (SK := Reusable.YE2k.tfib_sink_head) 0x9f1a0 0xa15e8 CtrlB :=
    @B.Prog.C_reac_ctrl_identity_replyTop.pb_reac_ctrl_identity_reply fx rc Reusable.YE2k.tfib_sink_head 0x9f1a0
    0xa15e8 CtrlB RELRO_IMG LAWS ML TFIB_SYMS errno_low SMP ASM1 ASF FFL PC1 PARSE.
(* lib/B/ProgWorld.v *)
Let aview_vis_mrd := B.ProgWorld.aview_vis_mrd.
(* lib/B/ProgBridgeData.v *)
Let ctl_bcmp_cells_of_AR := @B.ProgBridgeData.ctl_bcmp_cells_of_AR rc CtrlB TFIB_SYMS.
(* lib/B/ProgBridgeData.v (74a700f78a6) *)
Let ctl_box_view := B.ProgBridgeData.ctl_box_view CtrlB TFIB_SYMS.
(* lib/B/ProgBridgeData.v *)
Let ctl_cat_addressable := @B.ProgBridgeData.ctl_cat_addressable rc CtrlB TFIB_SYMS.
(* the box catalogue ends in the relro span (computation; ACtlW4f.v: owner the top): ctlall_ctl_cat_relro_hi above *)
Let ctl_cat_relro_hi : B.ACtlCutP.SM.CAT + B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N <= 0xa15e8 := ctlall_ctl_cat_relro_hi.
(* the box catalogue starts in the relro span (computation; ACtlW4f.v: owner the top): ctlall_ctl_cat_relro_lo above *)
Let ctl_cat_relro_lo : 0x9f1a0 <= B.ACtlCutP.SM.CAT := ctlall_ctl_cat_relro_lo.
(* lib/B/ProgBridgeData.v (GLOBS := ctrl_ro_globs; 0x9f1a0 <= 0x9f620, 0xa0708 <= 0xa15e8) *)
Let ctl_cat_ro := B.ProgBridgeData.ctl_cat_ro CtrlB TFIB_SYMS 0x9f1a0 0xa15e8 ltac:(lia) ltac:(lia).
(* lib/B/ProgBridgeData.v *)
Let ctl_cat_shadow_vis := @B.ProgBridgeData.ctl_cat_shadow_vis rc CtrlB TFIB_SYMS.
(* lib/B/ProgBridgeData.v *)
Let ctl_kind_name_addressable := @B.ProgBridgeData.ctl_kind_name_addressable rc CtrlB TFIB_SYMS.
(* lib/B/ProgBridgeData.v *)
Let ctl_kind_name_not_owned := B.ProgBridgeData.ctl_kind_name_not_owned CtrlB TFIB_SYMS.
(* lib/B/ProgBridgeData.v *)
Let ctl_kind_name_shadow_vis := @B.ProgBridgeData.ctl_kind_name_shadow_vis rc CtrlB TFIB_SYMS.
(* lib/B/ProgBridgeData.v *)
Let ctl_kind_name_str_shadow := @B.ProgBridgeData.ctl_kind_name_str_shadow rc CtrlB TFIB_SYMS.
(* lib/B/ProgBridgeData.v *)
Let ctl_names_addressable := @B.ProgBridgeData.ctl_names_addressable rc CtrlB TFIB_SYMS.
(* lib/B/ProgBridgeData.v (GLOBS := ctrl_ro_globs) *)
Let ctl_names_ro := B.ProgBridgeData.ctl_names_ro CtrlB TFIB_SYMS 0x9f1a0 0xa15e8 ltac:(lia) ltac:(lia).
(* lib/B/ProgBridgeData.v *)
Let ctl_names_shadow_vis := B.ProgBridgeData.ctl_names_shadow_vis CtrlB TFIB_SYMS.
(* lib/B/ProgBridgeData.v *)
Let ctl_parse_bc_addressable := @B.ProgBridgeData.ctl_parse_bc_addressable rc CtrlB TFIB_SYMS.
(* lib/B/ProgBridgeData.v *)
Let ctl_ports_addressable := B.ProgBridgeData.ctl_ports_addressable CtrlB TFIB_SYMS.
(* lib/B/ProgBridgeData.v *)
Let ctl_ports_shadow_vis := B.ProgBridgeData.ctl_ports_shadow_vis CtrlB TFIB_SYMS.
(* lib/B/ProgWorld.v *)
Let ctl_post_acall_kept := @B.ProgWorld.ctl_post_acall_kept rc.
(* lib/B/ProgWorld.v *)
Let ctl_post_memchr := B.ProgWorld.ctl_post_memchr.
(* W2b's two-window form of the set_shadow post, proved here with lib/B/ProgWorld.v's own proof of ctl_post_set_shadow (its lemmas rt_post_frame_vis, rw_cells_CB_of_present, mrd_of_aview_some; the window list is generic there): ctlall_ctl_post_set_shadow above *)
Let ctl_post_set_shadow : forall (W : Reusable.YA0n.world segs) (mem mem' : word -> option byte) (sp q n v : Z),
    0 <= q -> q + n <= 2 ^ 64 -> 0 < n ->
    (forall a, q <= a < q + n -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem a) ->
    (forall i, 0 <= i < n -> Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem' (q + i) = Some v) ->
    B.ProgWorld.rt_post_frame W mem mem' ((q, q + n) :: (sp - Reusable.YG0d.ESTACK, sp) :: nil) ->
    B.ProgWorld.munch_vis (Reusable.YA0n.w_H W) ((q, q + n) :: (sp - Reusable.YG0d.ESTACK, sp) :: nil) mem mem' /\
    B.ProgWorld.wmono_vis (Reusable.YA0n.w_H W) mem mem' /\
    lib.Lib.Step.rw_cells B.Img0.rsegs mem' q (lib.Lib.Cells.CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n)) :: nil) := ctlall_ctl_post_set_shadow.
(* lib/B/ProgBridgeData.v *)
Let ctl_qmark_addressable := @B.ProgBridgeData.ctl_qmark_addressable rc CtrlB TFIB_SYMS.
(* lib/B/ProgBridgeData.v *)
Let ctl_relro_not_owned := B.ProgBridgeData.ctl_relro_not_owned CtrlB TFIB_SYMS.
(* a Theorem Labs lane's lib/B/Prog/declaration_of_F_closed.v declaration_of_F_holds_closed_on (a working branch) *)
Let declaration_of_F_holds_on : B.Prog.declaration_of_c.declaration_of_contract_F_on :=
    B.Prog.declaration_of_F_closed.declaration_of_F_holds_closed_on.
(* lib/B/ProgBridge.v img_vis_W *)
Let img_vis_W := B.ProgBridge.img_vis_W.
(* the KIND_NAME table lies in [0x9f1a0, 0xa15e8) (computation; ACtlW3b.v: owner the top): ctlall_kn_relro above *)
Let kn_relro : 0x9f1a0 <= KNC.KIND_NAME /\ KNC.KIND_NAME + 112 <= 0xa15e8 := ctlall_kn_relro.
(* a Theorem Labs lane's lib/B/ProgBridgeData.v (3d6fd9e4988) *)
Let mem_grows_fsteps := B.ProgBridgeData.mem_grows_fsteps.
(* a Theorem Labs lane's lib/B/ACtlOwn6.v own6_frame_proved (by path, 92b69bb98ec; cbrec v6 record) *)
Let own6_frame : forall (cx : B.ACtlCut.ctlcx) ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k fr,
  Reusable.YCbq.ajournal (SK := Reusable.YE2k.tfib_sink_head) segs CtrlB Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) []
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = B.ACtlCut.own6 cx ->
  fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx) ->
  fr = Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) /\
  Reusable.YImgTop.IMG_TOP <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling /\
  (forall a, fr <= a < fr + 4096 \/ ART.shadow_addr fr <= a < ART.shadow_addr fr + 512 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a) :=
    @B.ACtlOwn6.own6_frame_proved rc Reusable.YE2k.tfib_sink_head CtrlB [].
(* a Theorem Labs lane's lib/B/Prog/reac_ctrl_identity_fragment_F_closed.v:34 reac_ctrl_identity_fragment_holds_F_closed_on (a working branch, cbrec v9 VERDICT ok) *)
Let reac_ctrl_identity_fragment_holds_F_on : B.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_contract_F_on :=
    B.Prog.reac_ctrl_identity_fragment_F_closed.reac_ctrl_identity_fragment_holds_F_closed_on.
(* W4c's name for the same open premise (reac_ctrl_identity_fragment_contract_F_on) *)
Let reac_ctrl_identity_fragment_holds_F_closed_on := reac_ctrl_identity_fragment_holds_F_on.
(* lib/B/Prog/reac_identity_initF.v at the memset _on run (asan_memsetF_on.asan_memset_holds_F_on memset_holds) *)
Let reac_identity_init_F_holds_on :=
    B.Prog.reac_identity_initF.reac_identity_init_F_holds_on (B.Prog.asan_memsetF_on.asan_memset_holds_F_on
    B.Prog.memset.memset_holds).
(* the same closed proof under W3a's name *)
Let reac_identity_init_holds_F_on := reac_identity_init_F_holds_on.
(* a Theorem Labs lane's lib/B/Rt/SetShadow.v *)
Let set_shadow_f8 : Reusable.YG0d.AR_laws segs CtrlB -> Reusable.YF0m.CtrlTSyms CtrlB -> Reusable.SetShadowDef.aset_shadow_realizes segs CtrlB 0x55144 0xf8 :=
    B.Rt.SetShadow.ctrl_set_shadow_f8 CtrlB.
(* a Theorem Labs lane's lib/B/Rt/StackFree6S.v disco_stack_free6_shared (055c2ebca7f; SF6_ENTRY = 0x3dd30) *)
Let stack_free6_contract : Reusable.StackFreeDef.astack_free_realizes segs CtrlB 0x3dd30 6 :=
    B.Rt.StackFree6S.disco_stack_free6_shared fx CtrlB LAWS TFIB_SYMS.
(* a Theorem Labs lane's lib/B/Rt/StackMalloc6.v disco_stack_malloc6 (a working branch 055c2ebca7f, record above) *)
Let stack_malloc6_contract : Reusable.YG0d.AR_laws segs CtrlB -> Reusable.YF0m.CtrlTSyms CtrlB -> Reusable.YG0d.astack_malloc_realizes segs CtrlB 6 :=
    fun L T => B.Rt.StackMalloc6.disco_stack_malloc6 fx CtrlB L T.
(* lib/B/ProgBridge.v *)
Let tfibsegs_rsegs : Reusable.YB1v.tfibsegs = B.Img0.rsegs := B.ProgBridge.tfibsegs_rsegs.

(* ---------------------------------------------------------------------------------------------------------
   STAGES: each proved route-C stage lemma at the instantiation, typed by ACtl.v's hypothesis of the same name. *)
Let seg_A1 : forall POST, (forall cx p, POST (ACtlCut.cx_set_fpos cx p) = POST cx) ->
  CF POST C_B81090 -> CF POST C_B810c4 -> CF POST C_ENTRY :=
    @B.ACtlW0.seg_A1 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx
    Reusable.YF0m.CtrlTSyms LAWS TFIB_SYMS stack_malloc6_contract set_shadow_f8 TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_A2 : forall POST, CF POST C_B810c4 -> CF POST C_B81090 :=
    @B.ACtlW0.seg_A2 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx
    Reusable.YF0m.CtrlTSyms LAWS TFIB_SYMS stack_malloc6_contract set_shadow_f8.
Let seg_A3 : forall POST, CF POST C_B81220 -> CF POST C_B810c4 :=
    @B.ACtlW0.seg_A3 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx
    Reusable.YF0m.CtrlTSyms LAWS TFIB_SYMS stack_malloc6_contract set_shadow_f8 TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_A4 : forall POST, CF POST (ix_cut C_B81548_at [0]) -> CF POST C_Jrel -> CF POST C_B81220 :=
    @B.ACtlW1.seg_A4 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL eq_refl.
Let seg_A5 : forall POST (t : Z),
  CF POST C_B81550 -> CF POST C_B815fc -> CF POST C_B81cb0 -> CF POST (ix_cut C_B81548_at [t]) :=
    @B.ACtlW1.seg_A5 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL RELRO_CAT eq_refl ctl_kind_name_addressable.
Let seg_R1 : forall POST, CF POST C_B815fc -> CF POST C_B81cb0 -> CF POST C_B81550 :=
    @B.ACtlW1.seg_R1 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL RELRO_CAT eq_refl ctl_kind_name_addressable.
Let seg_R2 : forall POST, CF POST C_B81640 -> CF POST C_B815fc :=
    @B.ACtlW1.seg_R2 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL ASF00.
Let seg_R3 : forall POST, CF POST C_B8168c -> CF POST C_B81640 :=
    @B.ACtlW1.seg_R3 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL.
Let seg_R4 : forall POST, CF POST C_B8169c -> CF POST C_B8168c :=
    @B.ACtlW1.seg_R4 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL AMEMSET ctl_names_addressable.
Let seg_R5 : forall POST, CF POST (ix_cut C_B816ec_at [Z.of_nat 0]) -> CF POST C_B8169c :=
    @B.ACtlW1.seg_R5 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL RELRO_CAT ctl_relro_not_owned.
Let seg_R6 : forall POST (b : nat),
  CF POST (ix_cut C_B81710_at [Z.of_nat b]) -> CF POST (ix_cut C_B816ec_at [Z.of_nat b]) :=
    @B.ACtlW2a.seg_R6 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL B.ProgBridgeData.ctrl_ro_globs BUILD_AS ctl_cat_ro ctl_names_ro ctl_box_view
    ctl_relro_not_owned ctl_names_addressable.
Let seg_R7 : forall POST (b : nat),
  CF POST (ix_cut C_B81764_at [Z.of_nat b]) -> CF POST (ix_cut C_B81ac0_at [Z.of_nat b]) ->
  CF POST (ix_cut C_B81710_at [Z.of_nat b]) :=
    @B.ACtlW2a.seg_R7 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] AMALLOC4 HMOK
    LAWS TFIB_SYMS RELRO_IMG RO_OFL HPCM ctl_relro_not_owned ctl_names_addressable (CHAIN_OF_CUT []).
Let seg_R8 : forall POST (b : nat),
  CF POST (ix_cut C_B8177c_at [Z.of_nat b]) -> CF POST (ix_cut C_B81764_at [Z.of_nat b]) :=
    @B.ACtlW2a.seg_R8 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS
    TFIB_SYMS RELRO_IMG RO_OFL AMEMCPY ctl_names_addressable.
Let seg_R9 : forall POST (b : nat),
  CF POST (ix_cut C_B817a4_at [Z.of_nat b]) -> CF POST (ix_cut C_B8177c_at [Z.of_nat b]) :=
    @B.ACtlW2a.seg_R9 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL PARSE ctl_relro_not_owned ctl_names_addressable.
Let seg_R10 : forall POST (b : nat),
  CF POST (ix_cut C_B817ec_at [Z.of_nat b]) -> CF POST (ix_cut C_B81834_at [Z.of_nat b]) ->
  CF POST (ix_cut C_B818a8_at [Z.of_nat b]) -> CF POST (ix_cut C_B81914_at [Z.of_nat b]) ->
  CF POST (ix_cut C_B8194c_at [Z.of_nat b]) -> CF POST (ix_cut C_B817a4_at [Z.of_nat b]) :=
    @B.ACtlW2a.seg_R10 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL TREPLY ctl_bcmp_cells_of_AR ctl_relro_not_owned ctl_names_addressable.
Let seg_R11 : forall POST (b : nat),
  CF POST (ix_cut C_B81860_at [Z.of_nat b]) -> CF POST (ix_cut C_B817ec_at [Z.of_nat b]) :=
    @B.ACtlW2a.seg_R11 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL ctl_names_addressable.
Let seg_R12 : forall POST (b : nat),
  CF POST (ix_cut C_B81860_at [Z.of_nat b]) -> CF POST (ix_cut C_B81834_at [Z.of_nat b]) :=
    @B.ACtlW2a.seg_R12 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL ctl_names_addressable.
Let seg_R13 : forall POST (b : nat),
  CF POST (ix_cut C_B81aa0_at [Z.of_nat b]) -> CF POST (ix_cut C_B81860_at [Z.of_nat b]) :=
    @B.ACtlW2a.seg_R13 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] AFREE4 HMOK
    LAWS TFIB_SYMS RELRO_IMG RO_OFL HPCF ctl_relro_not_owned ctl_names_addressable (CHAIN_OF_CUT []).
Let seg_R14 : forall POST (b : nat),
  CF POST (ix_cut C_B819a8_at [Z.of_nat b]) -> CF POST (ix_cut C_B818a8_at [Z.of_nat b]) :=
    @B.ACtlW2a.seg_R14 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL TMATCH ctl_relro_not_owned ctl_names_addressable.
Let seg_R15 : forall POST (b : nat),
  CF POST (ix_cut C_B81aa0_at [Z.of_nat b]) -> CF POST (ix_cut C_B81914_at [Z.of_nat b]) :=
    @B.ACtlW2b.seg_R15 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    ctl_relro_not_owned ctl_names_addressable LAWS TFIB_SYMS RELRO_IMG RO_OFL AFREE4 HMOK HPCF (CHAIN_OF_CUT []).
Let seg_R16 : forall POST (b : nat),
  CF POST (ix_cut C_B81aa0_at [Z.of_nat b]) -> CF POST (ix_cut C_B8194c_at [Z.of_nat b]) :=
    @B.ACtlW2b.seg_R16 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    ctl_relro_not_owned ctl_names_addressable LAWS TFIB_SYMS RELRO_IMG RO_OFL AFREE4 HMOK HPCF (CHAIN_OF_CUT []).
Let seg_R17 : forall POST (b : nat),
  CF POST (ix_cut C_B819d0_at [Z.of_nat b]) -> CF POST (ix_cut C_B819a8_at [Z.of_nat b]) :=
    @B.ACtlW2b.seg_R17 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS TFIB_SYMS
    RELRO_IMG RO_OFL.
Let seg_R18 : forall POST (b : nat),
  CF POST (ix_cut C_B81a50_at [Z.of_nat b]) -> CF POST (ix_cut C_B819d0_at [Z.of_nat b]) :=
    @B.ACtlW2b.seg_R18 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    ctl_names_addressable ctl_cat_addressable ctl_cat_shadow_vis LAWS TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_R19 : forall POST (b : nat),
  CF POST (ix_cut C_B81a68_at [Z.of_nat b]) -> CF POST (ix_cut C_B81a50_at [Z.of_nat b]) :=
    @B.ACtlW2b.seg_R19 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    B.Prog.bcmp_wrap_c.BCMP_WRAP eq_refl H_bcmp ctl_names_addressable LAWS TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_R20 : forall POST (b : nat),
  CF POST (ix_cut C_B81aa0_at [Z.of_nat b]) -> CF POST (ix_cut C_B81a68_at [Z.of_nat b]) :=
    @B.ACtlW2b.seg_R20 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    ctl_relro_not_owned ctl_names_addressable LAWS TFIB_SYMS RELRO_IMG RO_OFL AFREE4 HMOK HPCF (CHAIN_OF_CUT []).
Let seg_R21 : forall POST (b : nat),
  CF POST (ix_cut C_B816ec_at [Z.of_nat (S b)]) -> CF POST C_B81c58 -> CF POST C_B81ca8 ->
  CF POST (ix_cut C_B81aa0_at [Z.of_nat b]) :=
    @B.ACtlW2b.seg_R21 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] ASF8 0x42aa0
    eq_refl H_strcmp ctl_post_set_shadow ctl_names_addressable ctl_names_shadow_vis ctl_kind_name_addressable
    ctl_cat_addressable ctl_cat_shadow_vis LAWS TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_R21_a5c : forall POST (b : nat),
  CF POST (ix_cut C_B816ec_at [Z.of_nat (S b)]) -> CF POST C_B81c58 -> CF POST C_B81c60 ->
  CF POST (ix_cut C_B81ac0_at [Z.of_nat b]) :=
    @B.ACtlW2b.seg_R21_a5c fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] 0x42aa0
    eq_refl H_strcmp ctl_names_addressable ctl_names_shadow_vis ctl_kind_name_addressable ctl_cat_addressable
    ctl_cat_shadow_vis LAWS TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_P1 : forall POST, CF POST C_B81ca8 -> CF POST C_B81c58 :=
    @B.ACtlW3a.seg_P1 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low ASF8 TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable.
Let seg_P1_bfc : forall POST, CF POST C_B81ca8 -> CF POST C_B81c60 :=
    @B.ACtlW3a.seg_P1_bfc fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low ASF8 TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable.
Let seg_P2 : forall POST, CF POST C_B81cb0 -> CF POST C_B81ca8 :=
    @B.ACtlW3a.seg_P2 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low.
Let seg_P3 : forall POST, CF POST C_B81d18 -> CF POST C_B81cb0 :=
    @B.ACtlW3a.seg_P3 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low AMEMSET TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable reac_identity_init_holds_F_on.
Let seg_P4 : forall POST, CF POST C_B81d28 -> CF POST C_B81d18 :=
    @B.ACtlW3a.seg_P4 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low AMEMSET TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable.
Let seg_P5 : forall POST, CF POST C_B81d68 -> CF POST C_B81d28 :=
    @B.ACtlW3a.seg_P5 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low AMEMSET TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable ctl_parse_bc_addressable.
Let seg_P6 : forall POST, CF POST C_B81d80 -> CF POST C_B81d68 :=
    @B.ACtlW3a.seg_P6 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable TREPLY.
Let seg_P7 : forall POST, CF POST C_B81da8 -> CF POST C_B81d80 :=
    @B.ACtlW3b.seg_P7 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] tfibsegs_rsegs
    Hwx img_vis_W FEVT reac_ctrl_identity_fragment_holds_F_on LAWS segs_low mem_grows_fsteps own6_frame
    ctl_bcmp_cells_of_AR.
Let seg_P8 : forall POST, CF POST C_B81dbc -> CF POST C_B81da8 :=
    @B.ACtlW3b.seg_P8 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] tfibsegs_rsegs
    Hwx FEVT LAWS segs_low mem_grows_fsteps own6_frame.
Let seg_P9 : forall POST, CF POST C_B81dd4 -> CF POST C_B81dbc :=
    @B.ACtlW3b.seg_P9 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] tfibsegs_rsegs
    Hwx FEVT LAWS segs_low mem_grows_fsteps own6_frame.
Let seg_P10 : forall POST, CF POST C_B81de8 -> CF POST C_B81dd4 :=
    @B.ACtlW3b.seg_P10 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] tfibsegs_rsegs
    Hwx img_vis_W FEVT LAWS segs_low mem_grows_fsteps own6_frame.
Let seg_P11 : forall POST, CF POST C_B81e08 -> CF POST C_B81de8 :=
    @B.ACtlW3b.seg_P11 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] tfibsegs_rsegs
    Hwx img_vis_W FEVT LAWS segs_low mem_grows_fsteps own6_frame aview_vis_mrd ctl_kind_name_not_owned kn_relro
    eq_refl ctl_kind_name_shadow_vis.
Let seg_P12 : forall POST, CF POST (ix_cut C_B81ec4_at [Z.of_nat 0]) -> CF POST C_B82eac -> CF POST C_B81e08 :=
    @B.ACtlW3b.seg_P12 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    tfibsegs_rsegs Hwx img_vis_W FEVT LAWS segs_low mem_grows_fsteps own6_frame eq_refl ctl_kind_name_str_shadow
    ctl_qmark_addressable.
Let seg_F1 : forall POST (j : nat),
  CF POST (ix_cut C_B81f50_at [Z.of_nat j]) -> CF POST C_B82eac -> CF POST (ix_cut C_B81ec4_at [Z.of_nat j]) :=
    @B.ACtlW4a.seg_F1 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] tfibsegs_rsegs
    Hwx AMALLOC4 HMOK HPCM ctl_kind_name_addressable ctl_kind_name_not_owned TFIB_SYMS RELRO_IMG RO_OFL
    (CHAIN_OF_CUT []) LAWS segs_low.
Let seg_F2 : forall POST (j : nat),
  CF POST (ix_cut C_B81f78_at [Z.of_nat j]) -> CF POST (ix_cut C_B82048_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B81f50_at [Z.of_nat j]) :=
    @B.ACtlW4a.seg_F2 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] tfibsegs_rsegs
    Hwx AMEMCPY ctl_kind_name_addressable ctl_kind_name_not_owned TFIB_SYMS RELRO_IMG RO_OFL LAWS segs_low PARSE.
Let seg_F3 : forall POST (j : nat),
  CF POST (ix_cut C_B81fbc_at [Z.of_nat j]) -> CF POST (ix_cut C_B82048_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B81f78_at [Z.of_nat j]) :=
    @B.ACtlW4a.seg_F3 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] tfibsegs_rsegs
    Hwx ctl_kind_name_addressable ctl_kind_name_not_owned TFIB_SYMS RELRO_IMG RO_OFL LAWS segs_low PARSE.
Let seg_F4 : forall POST (j : nat),
  CF POST (ix_cut C_B82098_at [Z.of_nat j]) -> CF POST (ix_cut C_B81fbc_at [Z.of_nat j]) :=
    @B.ACtlW4a.seg_F4 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] tfibsegs_rsegs
    Hwx TFIB_SYMS RELRO_IMG RO_OFL LAWS segs_low.
Let seg_F5 : forall POST (j : nat),
  CF POST (ix_cut C_B8215c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82048_at [Z.of_nat j]) :=
    @B.ACtlW4a.seg_F5 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] tfibsegs_rsegs
    Hwx ctl_kind_name_addressable ctl_kind_name_not_owned TFIB_SYMS RELRO_IMG RO_OFL LAWS segs_low PARSE.
Let seg_F6 : forall POST (j : nat),
  CF POST (ix_cut C_B8215c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82098_at [Z.of_nat j]) :=
    @B.ACtlW4a.seg_F6 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] tfibsegs_rsegs
    Hwx ctl_kind_name_addressable ctl_kind_name_not_owned TFIB_SYMS RELRO_IMG RO_OFL LAWS segs_low PARSE.
Let seg_F7 : forall POST (j : nat),
  CF POST (ix_cut C_B82174_at [Z.of_nat j]) -> CF POST (ix_cut C_B8215c_at [Z.of_nat j]) :=
    @B.ACtlW4b.seg_F7 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    ctl_kind_name_shadow_vis LAWS.
Let seg_F8 : forall POST (j : nat),
  CF POST (ix_cut C_B82180_at [Z.of_nat j]) -> CF POST (ix_cut C_B82174_at [Z.of_nat j]) :=
    @B.ACtlW4b.seg_F8 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    ctl_kind_name_shadow_vis LAWS.
Let seg_F9 : forall POST (j : nat),
  CF POST (ix_cut C_B821ec_at [Z.of_nat j]) -> CF POST (ix_cut C_B82180_at [Z.of_nat j]) :=
    @B.ACtlW4b.seg_F9 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    ctl_kind_name_addressable ctl_kind_name_str_shadow ctl_kind_name_not_owned TFIB_SYMS RELRO_IMG RO_OFL LAWS
    TREPLY.
Let seg_F10 : forall POST (j : nat),
  CF POST (ix_cut C_B8226c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82308_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B821ec_at [Z.of_nat j]) :=
    @B.ACtlW4b.seg_F10 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS.
Let seg_F11 : forall POST (j : nat),
  CF POST (ix_cut C_B82304_at [Z.of_nat j]) -> CF POST (ix_cut C_B8226c_at [Z.of_nat j]) :=
    @B.ACtlW4b.seg_F11 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS.
Let seg_F12 : forall POST (j : nat),
  CF POST (ix_cut C_B82340_at [Z.of_nat j]) -> CF POST (ix_cut C_B82304_at [Z.of_nat j]) :=
    @B.ACtlW4b.seg_F12 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    ctl_kind_name_shadow_vis TFIB_SYMS RELRO_IMG RO_OFL AMEMCPY LAWS.
Let seg_F12_298 : forall POST (j : nat),
  CF POST (ix_cut C_B82340_at [Z.of_nat j]) -> CF POST (ix_cut C_B82308_at [Z.of_nat j]) :=
    @B.ACtlW4b.seg_F12_298 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    ctl_kind_name_shadow_vis TFIB_SYMS RELRO_IMG RO_OFL AMEMCPY LAWS.
Let seg_F13 : forall POST (j : nat),
  CF POST (ix_cut C_B8235c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82340_at [Z.of_nat j]) :=
    @B.ACtlW4c.seg_F13 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx
    B.Prog.bcmp_wrap_c.BCMP_WRAP H_bcmp LAWS segs_low ctl_bcmp_cells_of_AR eq_refl TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_F14 : forall POST (j : nat),
  CF POST (ix_cut C_B8237c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82378_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B8235c_at [Z.of_nat j]) :=
    @B.ACtlW4c.seg_F14 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] tfibsegs_rsegs
    Hwx B.Prog.bcmp_wrap_c.BCMP_WRAP H_bcmp LAWS segs_low eq_refl ctl_kind_name_addressable TFIB_SYMS RELRO_IMG
    RO_OFL.
Let seg_F15 : forall POST (j : nat),
  CF POST (ix_cut C_B8237c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82378_at [Z.of_nat j]) :=
    @B.ACtlW4c.seg_F15 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low.
Let seg_F15b : forall POST (j : nat),
  CF POST (ix_cut C_B823d8_at [Z.of_nat j]) -> CF POST (ix_cut C_B82468_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B8237c_at [Z.of_nat j]) :=
    @B.ACtlW4c.seg_F15b fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low.
Let seg_F16 : forall POST (j : nat),
  CF POST (ix_cut C_B82464_at [Z.of_nat j]) -> CF POST (ix_cut C_B823d8_at [Z.of_nat j]) :=
    @B.ACtlW4c.seg_F16 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low.
Let seg_F17 : forall POST (j : nat),
  CF POST (ix_cut C_B82468_at [Z.of_nat j]) -> CF POST (ix_cut C_B82464_at [Z.of_nat j]) :=
    @B.ACtlW4c.seg_F17 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low.
Let seg_F17b : forall POST (j : nat),
  CF POST (ix_cut C_B82634_at [Z.of_nat j]) -> CF POST (ix_cut C_B82468_at [Z.of_nat j]) :=
    @B.ACtlW4d.seg_F17b fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx AMEMCPY
    LAWS TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable.
Let seg_F18 : forall POST (j : nat),
  CF POST (ix_cut C_B8264c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82abc_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82634_at [Z.of_nat j]) :=
    @B.ACtlW4e1.seg_F18 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    tfibsegs_rsegs Hwx LAWS segs_low TFIB_SYMS RELRO_IMG RO_OFL B.Prog.bcmp_wrap_c.BCMP_WRAP eq_refl H_bcmp
    ctl_kind_name_addressable.
Let seg_F19 : forall POST (j : nat),
  CF POST (ix_cut C_B82668_at [Z.of_nat j]) -> CF POST (ix_cut C_B8264c_at [Z.of_nat j]) :=
    @B.ACtlW4e1.seg_F19 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    tfibsegs_rsegs Hwx LAWS segs_low TFIB_SYMS RELRO_IMG RO_OFL B.Prog.bcmp_wrap_c.BCMP_WRAP eq_refl H_bcmp
    ctl_kind_name_addressable.
Let seg_F20 : forall POST (j : nat),
  CF POST (ix_cut C_B82728_at [Z.of_nat j]) -> CF POST (ix_cut C_B82668_at [Z.of_nat j]) :=
    @B.ACtlW4e1.seg_F20 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low ctl_kind_name_addressable.
Let seg_F21 : forall POST (j : nat),
  CF POST (ix_cut C_B827f8_at [Z.of_nat j]) -> CF POST (ix_cut C_B82844_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82728_at [Z.of_nat j]) :=
    @B.ACtlW4e1.seg_F21 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    tfibsegs_rsegs Hwx LAWS segs_low ctl_kind_name_addressable.
Let seg_F22 : forall POST (j : nat),
  CF POST (ix_cut C_B8283c_at [Z.of_nat j]) -> CF POST (ix_cut C_B827f8_at [Z.of_nat j]) :=
    @B.ACtlW4e1.seg_F22 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    tfibsegs_rsegs Hwx LAWS segs_low.
Let seg_F22t : forall POST (j : nat),
  CF POST (ix_cut C_B82844_at [Z.of_nat j]) -> CF POST (ix_cut C_B8283c_at [Z.of_nat j]) :=
    @B.ACtlW4e1.seg_F22t fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low ctl_kind_name_addressable.
Let seg_F23 : forall POST (j : nat),
  CF POST (ix_cut C_B82878_at [Z.of_nat j]) -> CF POST (ix_cut C_B82844_at [Z.of_nat j]) :=
    @B.ACtlW4e1.seg_F23 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 []
    tfibsegs_rsegs Hwx LAWS segs_low TFIB_SYMS RELRO_IMG RO_OFL AMEMCPY ctl_kind_name_addressable
    ctl_ports_addressable ctl_ports_shadow_vis.
Let seg_F24 : forall POST (j : nat),
  CF POST (ix_cut C_B82888_at [Z.of_nat j]) -> CF POST (ix_cut C_B82878_at [Z.of_nat j]) :=
    @B.ACtlW4e2.seg_F24 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low.
Let seg_F25 : forall POST (j : nat),
  CF POST (ix_cut C_B828a4_at [Z.of_nat j]) -> CF POST (ix_cut C_B82888_at [Z.of_nat j]) :=
    @B.ACtlW4e2.seg_F25 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low.
Let seg_F26 : forall POST (j : nat),
  CF POST (ix_cut C_B828b4_at [Z.of_nat j]) -> CF POST (ix_cut C_B828a4_at [Z.of_nat j]) :=
    @B.ACtlW4e2.seg_F26 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low.
Let seg_F27 : forall POST (j : nat),
  CF POST (ix_cut C_B8292c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82aa4_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B828b4_at [Z.of_nat j]) :=
    @B.ACtlW4e2.seg_F27 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low.
Let seg_F28 : forall POST (j : nat),
  CF POST (ix_cut C_B82aa4_at [Z.of_nat j]) -> CF POST (ix_cut C_B8292c_at [Z.of_nat j]) :=
    @B.ACtlW4e2.seg_F28 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low.
Let seg_F29 : forall POST (j : nat),
  CF POST (ix_cut C_B82abc_at [Z.of_nat j]) -> CF POST (ix_cut C_B82aa4_at [Z.of_nat j]) :=
    @B.ACtlW4e2.seg_F29 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low.
Let seg_F30 : forall POST (j : nat),
  CF POST (ix_cut C_B82af8_at [Z.of_nat j]) -> CF POST (ix_cut C_B82abc_at [Z.of_nat j]) :=
    @B.ACtlW4f.seg_F30 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx
    LAWS segs_low ctl_kind_name_addressable ctl_kind_name_not_owned TFIB_SYMS RELRO_IMG RO_OFL TCLS eq_refl.
Let seg_F31 : forall POST (j : nat),
  CF POST (ix_cut C_B82b38_at [Z.of_nat j]) -> CF POST (ix_cut C_B82b5c_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82af8_at [Z.of_nat j]) :=
    @B.ACtlW4f.seg_F31 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low B.Prog.bcmp_wrap_c.BCMP_WRAP H_bcmp eq_refl ctl_kind_name_addressable TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_F32 : forall POST (j : nat),
  CF POST (ix_cut C_B82bcc_at [Z.of_nat j]) -> CF POST (ix_cut C_B82c90_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82b38_at [Z.of_nat j]) /\ CF POST (ix_cut C_B82b5c_at [Z.of_nat j]) :=
    @B.ACtlW4f.seg_F32 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_F33 : forall POST (j : nat),
  CF POST (ix_cut C_B82bf4_at [Z.of_nat j; Z.of_nat 0]) -> CF POST (ix_cut C_B82c84_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82bcc_at [Z.of_nat j]) :=
    @B.ACtlW4f.seg_F33 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low.
Let seg_F34 : forall POST (j i : nat),
  CF POST (ix_cut C_B82c24_at [Z.of_nat j; Z.of_nat i]) -> CF POST (ix_cut C_B82bf4_at [Z.of_nat j; Z.of_nat i]) :=
    @B.ACtlW4f.seg_F34 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx
    LAWS segs_low ctl_relro_not_owned ctl_cat_relro_lo ctl_cat_relro_hi ctl_cat_addressable ctl_cat_shadow_vis
    declaration_of_F_holds_on TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_F35 : forall POST (j i : nat),
  CF POST (ix_cut C_B82bf4_at [Z.of_nat j; Z.of_nat (S i)]) ->
  CF POST (ix_cut C_B82c38_at [Z.of_nat j; Z.of_nat i]) -> CF POST (ix_cut C_B82ca0_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82c24_at [Z.of_nat j; Z.of_nat i]) :=
    @B.ACtlW4f.seg_F35 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low B.Prog.bcmp_wrap_c.BCMP_WRAP H_bcmp eq_refl ctl_kind_name_addressable TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_F36 : forall POST (j i : nat),
  CF POST (ix_cut C_B82bf4_at [Z.of_nat j; Z.of_nat (S i)]) -> CF POST (ix_cut C_B82ca0_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82c38_at [Z.of_nat j; Z.of_nat i]) :=
    @B.ACtlW4f.seg_F36 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low ctl_kind_name_addressable ctl_kind_name_not_owned ctl_relro_not_owned TFIB_SYMS RELRO_IMG RO_OFL
    TMATCH.
Let seg_F36_c20 : forall POST (j : nat),
  CF POST (ix_cut C_B82ca0_at [Z.of_nat j]) -> CF POST (ix_cut C_B82c84_at [Z.of_nat j]) :=
    @B.ACtlW4f.seg_F36_c20 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low ctl_kind_name_addressable ctl_kind_name_not_owned ctl_relro_not_owned TFIB_SYMS RELRO_IMG RO_OFL
    TMATCH.
Let seg_F36_c2c : forall POST (j : nat),
  CF POST (ix_cut C_B82ca0_at [Z.of_nat j]) -> CF POST (ix_cut C_B82c90_at [Z.of_nat j]) :=
    @B.ACtlW4f.seg_F36_c2c fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    segs_low ctl_kind_name_addressable ctl_kind_name_not_owned ctl_relro_not_owned TFIB_SYMS RELRO_IMG RO_OFL
    TMATCH.
Let seg_F37 : forall POST (j : nat),
  CF POST (ix_cut C_B82d1c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82ca0_at [Z.of_nat j]) :=
    @B.ACtlW4g.seg_F37 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx AFREE4
    HMOK HPCF LAWS (CHAIN_OF_CUT []) ctl_post_acall_kept ctl_kind_name_addressable ctl_kind_name_not_owned
    TFIB_SYMS eq_refl.
Let seg_F38 : forall POST (j : nat),
  CF POST (ix_cut C_B81ec4_at [Z.of_nat (S j)]) -> CF POST C_B82eac -> CF POST (ix_cut C_B82d1c_at [Z.of_nat j]) :=
    @B.ACtlW4g.seg_F38 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] Hwx LAWS
    eq_refl.
Let seg_X1 : forall POST, CF POST C_B82ecc -> CF POST C_Jrel -> CF POST C_B82eac :=
    @B.ACtlW5.seg_X1 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS Hwx
    TFIB_SYMS RELRO_IMG RO_OFL 0x42ab0 AMEMCHR eq_refl aview_vis_mrd ctl_post_memchr.
Let seg_X2 : forall POST, CF POST C_Jrel -> CF POST C_B82ecc :=
    @B.ACtlW5.seg_X2 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS Hwx
    TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_Jrel : forall POST, CF POST C_B82f48 -> CF POST C_Jrel :=
    @B.ACtlW5.seg_Jrel fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS Hwx
    TFIB_SYMS RELRO_IMG RO_OFL.
Let seg_Y1 : forall POST, CF POST C_B82f5c -> CF POST C_B82f48 :=
    @B.ACtlW5.seg_Y1 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS Hwx
    TFIB_SYMS RELRO_IMG RO_OFL stack_free6_contract ML aview_vis_mrd.
Let seg_Y3 : CF ctl_post_leaf C_B82f5c :=
    @B.ACtlW5.seg_Y3 fx rc Reusable.YE2k.tfib_sink_head CtrlB MT0 B.ACtl.XL0 B.ACtl.XL0 0x9f1a0 0xa15e8 [] LAWS
    Hwx AIL HMOLE eq_refl.

(* ---------------------------------------------------------------------------------------------------------
   THE TOP. *)
Theorem ctl_lib_x_CtrlB_all :
  @Reusable.YCfn.tfib_lib_contract_x fx rc LS Reusable.YD2l.CtrlB Reusable.YCbp.ameter_triv B.ACtl.XL0 B.ACtl.XL0
    0x9f1a0 0xa15e8.
Proof.
  exact (@B.ACtl.ctl_lib_x_CtrlB fx rc LS Reusable.CtrlBCode.ctrlb_libS
    LS_LEAF CTLRT_ENTRY CHAIN_OF_CUT seg_A1 seg_A2 seg_A3 seg_A4 seg_A5 seg_R1 seg_R2 seg_R3 seg_R4 seg_R5
    seg_R6 seg_R7 seg_R8 seg_R9 seg_R10 seg_R11 seg_R12 seg_R13 seg_R14 seg_R15 seg_R16 seg_R17 seg_R18 seg_R19
    seg_R20 seg_R21 seg_R21_a5c seg_P1 seg_P1_bfc seg_P2 seg_P3 seg_P4 seg_P5 seg_P6 seg_P7 seg_P8 seg_P9
    seg_P10 seg_P11 seg_P12 seg_F1 seg_F2 seg_F3 seg_F4 seg_F5 seg_F6 seg_F7 seg_F8 seg_F9 seg_F10 seg_F11
    seg_F12 seg_F12_298 seg_F13 seg_F14 seg_F15 seg_F15b seg_F16 seg_F17 seg_F17b seg_F18 seg_F19 seg_F20
    seg_F21 seg_F22 seg_F22t seg_F23 seg_F24 seg_F25 seg_F26 seg_F27 seg_F28 seg_F29 seg_F30 seg_F31 seg_F32
    seg_F33 seg_F34 seg_F35 seg_F36 seg_F36_c20 seg_F36_c2c seg_F37 seg_F38 seg_X1 seg_X2 seg_Jrel seg_Y1 seg_Y3).
Qed.

End CtlAll.
