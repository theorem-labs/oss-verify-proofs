(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4): THE TOP of the
   walk of parse_noting (A' 0x81f14, 120 bytes, 30 instructions, frame 48; row N10-PNA; cut table
   lib/A/Prog/PN102Cuts.v): the six segments composed into the batch kit's tparse_noting_specX ITSELF (lib/A/PRH_FnCheck.v
   :596-730 on the kit's cut of record 7cdbb61b5fa0) at the A' instance, then at the
   real A' binding B := AD2l.TfibB, then in the consumer's form (a Theorem Labs lane's H_txt_parse_noting_A, drv102
   lib/A/PresetD2pAPf.v:99-101 / :195). NO _FIX TWIN and NO premise of the walk's own: the signed walk's FIX premises
   are all retired by the batch kit (the cut table's header has the text diff).
   The six segments:
     S1 lib/A/Prog/PN102S1.v pn_seg_S1   entry -> cut_S2 (+0x28), through tfuzz_alloc_live_specX;
     S2 lib/A/Prog/PN102S2.v pn_seg_S2   cut_S2 -> cut_S3 (+0x3c), through tpj_parse_specX at CW := pn_cw X;
     S3 lib/A/Prog/PN102S34.v pn_seg_S3  cut_S3 -> cut_S4 (+0x44), through tfuzz_alloc_ran_out_specX;
     S4 lib/A/Prog/PN102S34.v pn_seg_S4  cut_S4 -> cut_S5 (+0x48) \/ cut_S6 (+0x58), the beqz;
     S5 lib/A/Prog/PN102S5.v pn_seg_S5   cut_S5 -> cut_S6, through tcheck_reject_clean_specX;
     S6 lib/A/Prog/PN102S6.v pn_seg_S6   cut_S6 -> the text's post, the epilogue and the ret.
   All 30 instructions are stepped: 10 in S1 (one engine run of 9, the jal), 5 in S2, 2 in S3, 1 in S4, 4 in S5, 8 in
   S6; S5's four run only when g_ran_out <> 0 (S4's taken edge skips them).
   THE FREE / REALLOC MOVE: the batch kit's text concludes SRr' segs RZ_cf (SRrG at YA0nH.wle' segs RZ_cf: pj_parse frees). S2
   concludes SRr' itself; S1, S3, S4, S5 and S6 are plain SRr segments, lifted by YA0nH.SRr_SRr'; the six compose by
   YA0nH.SRrG_bind at wle' (YA0nH.wle'_trans).
   rule 24: proves function parse_noting (reuse search: `proof-index parse_noting` exit 4 at 2026-10-30 07:2xZ,
   index v5 06:36:24Z: 0 named / 0 by address / 0 related / 0 released; the unreleased hits are this lane's own N10-PNA
   files and the plain / UBSan / B' twins; R24Pna CONFIRM 2026-10-29 18:2xZ; own signed walk 13970867e0c9, its one
   announced re-bind). This file: the top of that walk.
   THE BATCH KIT'S RE-BIND: a Theorem Labs lane's signed A' file of the same role (a working branch 13970867e0c9),
   re-fit to the batch kit's cut (commit 7cdbb61b5fa0) as the B' twin was re-fit
   (a working branch c7276d935095 lib/B/Prog/PN102B<same role>.v, read back at PI_prog_A / prh_img_A).
   ON COMBINE6 (a working branch, base f40eca0736e0 on the
   combine6 tree, the cut merged with int102): the kit texts are the cut's (same blobs);
   ARcf below is combine6's (YG0ncf.v 6748bee76f02, with cls1_band_vis_cf; the cut's 9c48a1a860d6). The files are the
   k1 line's (a working branch 319a231e9da8), unchanged but for comments.
   CWPJ RE-FIT (POST-BATCH, not for the cut landing): the texts are those of the kit's prh_cw_pj repair
   a working branch f29626eb1667 (the cut + 4b8f95c0455, 0ee9bda470d, f29626eb1667). Of them only
   PRH_Base.prh_cw_pj, the cursor-set premise of HPJ's tpj_parse_specX, changes a statement this walk reads (defect
   repair: the old text is unprovable at a satisfiable CW on B' (cwpjcm 8fa0b4530baa); falsity of the old text not
   shown); tparse_noting_specX itself is unchanged. The re-fit is PN102Cuts.v pn_cw_pj only.
   THE INSTANCE: PA := PI_prog_A (lib/A/PAImg_prog.v, the A' listing lib/A/Listing_prog.v), PI := prh_img_A
   (lib/A/PRH_Img.v), cp := CfParams_preset, RL := prh_room_live_a8, ARx := ARcf /\ xs_placed_cf (= PresetCfnA.v
   iface_ARx), LAWS := AR_laws_x_xs (AR_laws_ok_cf) (YGcallcf.v / YG0lawscf.v).
   SECTION HYPOTHESES (the callee texts, at the batch kit's texts on the cut, each with its owner), nothing else:
     HLIVE : tfuzz_alloc_live_specX              (lib/A/PRH_FnAlloc.v; owner a Theorem Labs lane)
     HPJ   : forall CW, tpj_parse_specX CTX0 CW  (lib/A/PRH_FnPj.v; owned by the kit owner, a Theorem Labs lane); the walk uses it only at
             CW := pn_cw X, which meets the repaired PRH_Base.prh_cw_pj, one disjunct per arm (PN102Cuts.v pn_cw_pj)
     HRO   : forall fy, tfuzz_alloc_ran_out_specX (fx := fy)   (lib/A/PRH_FnAlloc.v; owner a Theorem Labs lane)
     HCRC  : forall fy, tcheck_reject_clean_specX (fx := fy)   (lib/A/PRH_FnCheck.v :578-592 here; owned by the kit)
   and the image binding TB : AF0m.TfibSyms B (lib/A/AF0m.v), discharged at B := AD2l.TfibB by AD2l.TfibB_syms
   (pn_top_TB_witness below). Every other image premise is a vm_compute witness at PI_prog_A / prh_img_A in the cut
   table (pn_slot_*, pn_frame_*_A, pn_free_sites_A) or an A' image lemma (S1ImgA.v pst_not_ro_A,
   AImgShadowVis.v tfib_img_shadow_cover at TB, PN102S2Help.v pn2_img_vis). No CFHEAD-16 hypothesis: the text
   guards its two HEAD-sized conjuncts with `cf_head = PresetReqAt.HEAD ->` itself (and at CfParams_preset cf_head =
   16 = HEAD by reflexivity).
   NON-VACUITY AT TfibB: the batch kit's closure premise and the batch kit's room premise are satisfiable at the real binding -
   prh_univ_closure TfibB CTX0 for the driver's context [[0x814dc]] = PresetCfnA.iface_ctx0 (pn_top_univ_witness,
   the kit's lib/A/PRH_Witness.v prh_univ_closure_witness_A) and wild_room U [] (prh_wk F_parse_noting) at the driver's
   start depot (pn_top_wild_witness, PRH_Witness.v prh_wild_room_witness_A). No witness of the whole premise set at one
   state is given here.
   NUMERALS: none of the walk's own (0x814dc is the driver context PresetCfnA.v RA_LLVMF names). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YG0ncf YG0dcf YGcfRoomPre YGcfRoomKeep YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Witness.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m AD2l CfImgA PresetCfnA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PN102Cuts PN102S1 PN102S2 PN102S34
  PN102S5 PN102S6.
Import ListNotations.
Local Open Scope Z_scope.

(* the image binding TB at the real A' binding (lib/A/AD2l.v) *)
Lemma pn_top_TB_witness : AF0m.TfibSyms AD2l.TfibB.
Proof. exact AD2l.TfibB_syms. Qed.

(* NON-VACUITY at TfibB: the batch kit's closure premise at the driver's context PresetCfnA.iface_ctx0 = [[RA_LLVMF]] =
   [[0x814dc]] (the consumer's CTX0), and the batch kit's room premise at the driver's start depot, both the kit's witnesses
   (lib/A/PRH_Witness.v) at the real binding *)
Lemma pn_top_univ_witness : @prh_univ_closure prh_img_A AD2l.TfibB CfImgA.CfImg_A PresetCfnA.iface_ctx0.
Proof. exact (PRH_Witness.prh_univ_closure_witness_A AD2l.TfibB eq_refl eq_refl). Qed.
Lemma pn_top_wild_witness :
  YCbqGwild.wild_room (as_universe AD2l.TfibB) [] (prh_wk F_parse_noting) (st_depot init_state).
Proof.
exact (PRH_Witness.prh_wild_room_witness_A AD2l.TfibB F_parse_noting eq_refl
  ltac:(rewrite pn_wk_A; unfold YCbqGwild.K_LLVMF; lia)).
Qed.

Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := (@PI_prog_A rc).
#[local] Abbreviation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Abbreviation RL := (prh_room_live_a8 (cp := CP)).
Variable B : asyms.
#[local] Abbreviation ARc := (fun ly S Hp (W : world SEGS) mem md =>
  ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Variable CTX0 : list (list Z).
(* the image binding of B (witness pn_top_TB_witness) *)
Hypothesis TB : AF0m.TfibSyms B.
(* the callee texts (owners in the header) *)
Hypothesis HLIVE : tfuzz_alloc_live_specX (fx := fx) (cp := CP) (PI := prh_img_A) (RL := RL) (PA := PA) B ARc SK.
Hypothesis HPJ : forall CW : list (list Z),
  tpj_parse_specX (fx := fx) (cp := CP) (PI := prh_img_A) (RL := RL) (PA := PA) B ARc SK CTX0 CW.
Hypothesis HRO : forall fy : YK11.FPState,
  tfuzz_alloc_ran_out_specX (fx := fy) (cp := CP) (PI := prh_img_A) (RL := RL) (PA := PA) B ARc SK.
Hypothesis HCRC : forall fy : YK11.FPState,
  tcheck_reject_clean_specX (fx := fy) (cp := CP) (PI := prh_img_A) (RL := RL) (PA := PA) B ARc SK.
#[local] Abbreviation RZW := (wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Abbreviation RZT := (wle'_trans SEGS YGcfRehidePost.RZ_cf).
#[local] Abbreviation LIFT := (SRr_SRr' SEGS YGcfRehidePost.RZ_cf).

Theorem tparse_noting_specX_A :
  tparse_noting_specX (fx := fx) (cp := CP) (PI := prh_img_A) (RL := RL) (PA := PA) B ARc SK CTX0.
Proof.
apply pn_intro. intros X HPRE. unfold SRr'.
eapply (SRrG_bind SEGS RZW RZT); [apply LIFT; exact (pn_seg_S1 (fx := fx) (SK := SK) B CTX0 HLIVE X HPRE)|].
intros W1 c1 _ H1.
eapply (SRrG_bind SEGS RZW RZT); [exact (pn_seg_S2 (fx := fx) (SK := SK) B TB CTX0 HPJ X W1 c1 HPRE H1)|].
intros W2 c2 _ H2.
eapply (SRrG_bind SEGS RZW RZT); [apply LIFT; exact (pn_seg_S3 (fx := fx) (SK := SK) B CTX0 HRO X W2 c2 HPRE H2)|].
intros W3 c3 _ H3.
eapply (SRrG_bind SEGS RZW RZT); [apply LIFT; exact (pn_seg_S4 (fx := fx) (SK := SK) B CTX0 X W3 c3 HPRE H3)|].
intros W4 c4 _ [H4 | H4].
- eapply (SRrG_bind SEGS RZW RZT); [apply LIFT; exact (pn_seg_S5 (fx := fx) (SK := SK) B CTX0 HCRC X W4 c4 HPRE H4)|].
  intros W5 c5 _ H5. apply LIFT. exact (pn_seg_S6 (fx := fx) (SK := SK) B CTX0 X W5 c5 HPRE H5).
- apply LIFT. exact (pn_seg_S6 (fx := fx) (SK := SK) B CTX0 X W4 c4 HPRE H4).
Qed.
End T.

(* ---------------------------------------------------------------------- *)
(* THE THEOREM AT THE REAL A' BINDING: B := AD2l.TfibB, TB discharged by pn_top_TB_witness; what remains are the four
   callee texts at that binding (owners in the header). *)
Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := (@PI_prog_A rc).
#[local] Abbreviation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Abbreviation ARcA := (fun ly S Hp (W : world SEGS) mem md =>
  ARcf (cp := CP) SEGS AD2l.TfibB ly S Hp W mem md /\ xs_placed_cf ly S).
Theorem tparse_noting_specX_A_TfibB : forall CTX0,
  tfuzz_alloc_live_specX (fx := fx) (cp := CP) (PI := prh_img_A) (RL := prh_room_live_a8 (cp := CP)) (PA := PA)
    AD2l.TfibB ARcA SK ->
  (forall CW : list (list Z), tpj_parse_specX (fx := fx) (cp := CP) (PI := prh_img_A)
    (RL := prh_room_live_a8 (cp := CP)) (PA := PA) AD2l.TfibB ARcA SK CTX0 CW) ->
  (forall fy : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fy) (cp := CP) (PI := prh_img_A)
    (RL := prh_room_live_a8 (cp := CP)) (PA := PA) AD2l.TfibB ARcA SK) ->
  (forall fy : YK11.FPState, tcheck_reject_clean_specX (fx := fy) (cp := CP) (PI := prh_img_A)
    (RL := prh_room_live_a8 (cp := CP)) (PA := PA) AD2l.TfibB ARcA SK) ->
  tparse_noting_specX (fx := fx) (cp := CP) (PI := prh_img_A) (RL := prh_room_live_a8 (cp := CP)) (PA := PA)
    AD2l.TfibB ARcA SK CTX0.
Proof.
intros CTX0 HL HP HR HC.
exact (tparse_noting_specX_A (fx := fx) (SK := SK) AD2l.TfibB CTX0 pn_top_TB_witness HL HP HR HC).
Qed.
End R.

(* ---------------------------------------------------------------------- *)
(* THE CONSUMER'S FORM: a Theorem Labs lane's txt_parse_noting_A (a working branch 4c5ae3c40e82
   lib/A/PresetD2pAPf.v:99-101), every argument spelled as there - ci := CfImg_A, PI := PresetCfnA.preset_prh_img,
   ARx := PresetCfnA.iface_ARx at TfibB, SK := PresetCfnA.preset_sink_head, CTX0 := PresetCfnA.iface_ctx0 - from the
   four callee texts at the same instance. It is the theorem above by conversion. Since the round-6f CfImg repairs
   PresetCfnA.iface_ARx takes the CfImg its ARcf reads (Section v's ci), so it is spelled at ci := CfImg_A here. *)
Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PIc := PresetCfnA.preset_prh_img.
#[local] Abbreviation RLc := (@prh_room_live_a8 CfParams_preset).
#[local] Abbreviation PA := (@PI_prog_A rc).
#[local] Abbreviation ARi := (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB).
Theorem tparse_noting_specX_A_iface :
  tfuzz_alloc_live_specX (fx := fx) (cp := CP) (PI := PIc) (RL := RLc) (PA := PA) AD2l.TfibB ARi
    PresetCfnA.preset_sink_head ->
  (forall CW : list (list Z), tpj_parse_specX (fx := fx) (cp := CP) (PI := PIc) (RL := RLc) (PA := PA) AD2l.TfibB ARi
    PresetCfnA.preset_sink_head PresetCfnA.iface_ctx0 CW) ->
  (forall fy : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fy) (cp := CP) (PI := PIc) (RL := RLc) (PA := PA)
    AD2l.TfibB ARi PresetCfnA.preset_sink_head) ->
  (forall fy : YK11.FPState, tcheck_reject_clean_specX (fx := fy) (cp := CP) (PI := PIc) (RL := RLc) (PA := PA)
    AD2l.TfibB ARi PresetCfnA.preset_sink_head) ->
  @PRH_FnCheck.tparse_noting_specX fx rc CfImgA.CfImg_A CfParams_preset PresetCfnA.preset_prh_img
    (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PI_prog_A rc) AD2l.TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB) PresetCfnA.preset_sink_head
    PresetCfnA.iface_ctx0.
Proof.
intros HL HP HR HC.
exact (tparse_noting_specX_A_TfibB (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A) (SK := PresetCfnA.preset_sink_head)
  PresetCfnA.iface_ctx0 HL HP HR HC).
Qed.
End I.

(* ---------------------------------------------------------------------- *)
(* THE CHECKS: the elaborated statements with every implicit argument shown, the entry float state in its class
   position; the closure. *)
Set Printing Implicit. Unset Printing Notations.
Check @tparse_noting_specX_A_iface.
Check @tparse_noting_specX_A_TfibB.
Check @tparse_noting_specX_A.
Print tparse_noting_specX.
Print pn_pre.
Print pn_R.
Print pn_post.
Print pn_frame.
Print pn_frameR.
Print pn_hull.
Print pn_cw.
Print pn_cut_S2.
Print pn_cut_S3.
Print pn_cut_S4.
Print pn_cut_S5.
Print pn_cut_S6.
Print pn_seg_S1_stmt.
Print pn_seg_S2_stmt.
Print pn_seg_S3_stmt.
Print pn_seg_S4_stmt.
Print pn_seg_S5_stmt.
Print pn_seg_S6_stmt.
Check @pn_seg_S1.
Check @pn_seg_S2.
Check @pn_seg_S3.
Check @pn_seg_S4.
Check @pn_seg_S5.
Check @pn_seg_S6.
Check @pn_top_univ_witness.
Check @pn_top_wild_witness.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions tparse_noting_specX_A_iface.
Print Assumptions tparse_noting_specX_A_TfibB.
Print Assumptions tparse_noting_specX_A.
Print Assumptions pn_top_univ_witness.
Print Assumptions pn_top_wild_witness.
