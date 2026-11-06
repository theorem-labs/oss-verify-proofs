(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102, pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b): THE TOP of the
   walk of parse_noting (B' 0x81ed0, 30 instructions; the B' twin of row N10-PNA; cut table lib/B/Prog/PN102BCuts.v):
   the six segments composed into the batch kit's tparse_noting_specX ITSELF (lib/A/PRH_FnCheck.v blob c40cf3fdcd2a :596-730,
   the batch kit, unchanged in the kit's cut) at the
   B' instance, then at the real B' binding
   B := YD2l.TfibB. NO _FIX TWIN: the f97c walk's four FIX premises are all retired by the batch kit (the cut table's header has
   the measured text diff: FIX (4) and FIX (slot word) go with DW, FIX (5) F6 with the batch kit's src_rd, FIX P4.2 is the batch kit's own
   premise).
   The six segments (a Theorem Labs lane's A' layout, a working branch lib/A/Prog/PN102Top.v):
     S1 lib/B/Prog/PN102BS1.v pn_seg_S1   entry -> cut_S2 (+0x28), through tfuzz_alloc_live_specX;
     S2 lib/B/Prog/PN102BS2.v pn_seg_S2   cut_S2 -> cut_S3 (+0x3c), through tpj_parse_specX at CW := pn_cw X;
     S3 lib/B/Prog/PN102BS34.v pn_seg_S3  cut_S3 -> cut_S4 (+0x44), through tfuzz_alloc_ran_out_specX;
     S4 lib/B/Prog/PN102BS34.v pn_seg_S4  cut_S4 -> cut_S5 (+0x48) \/ cut_S6 (+0x58), the beqz;
     S5 lib/B/Prog/PN102BS5.v pn_seg_S5   cut_S5 -> cut_S6, through tcheck_reject_clean_specX;
     S6 lib/B/Prog/PN102BS6.v pn_seg_S6   cut_S6 -> the text's post, the epilogue and the ret.
   All 30 instructions are stepped: 10 in S1, 5 in S2, 2 in S3, 1 in S4, 4 in S5, 8 in S6; S5's four run only when
   g_ran_out <> 0 (S4's taken edge skips them). No UBSan check exists in the B' body (the cut table's instruction
   compare), so no UBSan branch is owed.
   THE FREE / REALLOC MOVE: the batch kit's text concludes SRr' segs RZ_cf (SRrG at YA0nH.wle' segs RZ_cf: pj_parse frees). S2
   concludes SRr' itself; S1, S3, S4, S5 and S6 are plain SRr segments, lifted by YA0nH.SRr_SRr'; the six compose by
   YA0nH.SRrG_bind at wle' (YA0nH.wle'_trans).
   rule 24: proves function parse_noting (fuzz_preset, image B') (preparation; proof-index 03:20Z, its output summarized: 0 named, 0 by
   address, 0 related, 0 released, 0 by file name, delivery 0; rule-24 parse_noting second-agent check 03:25Z CONFIRM). This
   file: its top. NOT A RESULT until re-run on the kit's announced cut sha.
   THE INSTANCE: PA := PI_prog_B (lib/B/PAImg_prog.v, the B' listing lib/B/Listing_prog.v), PI := prh_img_B
   (lib/B/PRH_ImgB.v), cp := CfParams_preset, RL := prh_room_live_a8, ARx := ARcfx = ARcf /\ xs_placed_cf,
   LAWS := AR_laws_x_xs (AR_laws_ok_cf) (YGcallcf.v / YG0lawscf.v).
   SECTION HYPOTHESES (the callee texts, at the batch kit's texts, each with its owner), nothing else:
     HLIVE : tfuzz_alloc_live_specX              (lib/A/PRH_FnAlloc.v 4d8aeba047e5 :119-127; owner a Theorem Labs lane)
     HPJ   : forall CW, tpj_parse_specX CTX0 CW  (lib/A/PRH_FnPj.v 5aca5cbe2cfb in the kit's cut, text
             unchanged from 3aa72eee2204 :592-736; owned by the kit owner, a Theorem Labs lane); the walk uses it only at CW := pn_cw X.
             In that cut PRH_Base.prh_cw_pj (blob ef7c8ca98529) is PINNED per cursor function (parse_items:
             the cursor end or the A' code word; parse_string: the slot word or the A' code word), so every CW it
             admits is one the B' frees store; pn_cw X meets it by the cursor end for parse_items and the slot word
             for parse_string (PN102BCuts.v pn_cw_pj)
     HRO   : forall fy, tfuzz_alloc_ran_out_specX (fx := fy)   (PRH_FnAlloc.v; owner a Theorem Labs lane)
     HCRC  : forall fy, tcheck_reject_clean_specX (fx := fy)   (lib/A/PRH_FnCheck.v c40cf3fdcd2a :566-580; owned by the kit)
   and the image binding TB : YF0m.TfibSyms B (lib/Reusable/YF0m.v), discharged at B := YD2l.TfibB by
   YD2l.TfibB_syms (pn_top_TB_witness below). Every other image premise is a vm_compute witness at PI_prog_B /
   prh_img_B in the cut table (pn_slot_*, pn_frame_*_B, pn_free_sites_B) or in the support files (PN102BKeep.v
   pnk_pst_ro, PN102BS2Help.v pn2_img_cover_B). No ARX_DEPOT hypothesis: the walk never needs NoDup (st_depot S)
   (the room is paid by wild_room_set and the budget by ajournal_xw_norm, neither of which asks it).
   NON-VACUITY AT TfibB (the f97c top was vacuous there through the DW slot-word clause): the batch kit's closure premise, which
   carried that clause, and the batch kit's new room premise are satisfiable at the real binding - prh_univ_closure TfibB CTX0
   for the driver's context (pn_top_univ_witness, the kit's lib/A/PRH_Witness.v prh_univ_closure_witness_B) and
   wild_room U [] (prh_wk F_parse_noting) at the driver's start depot (pn_top_wild_witness, PRH_Witness.v
   prh_wild_room_witness_B). No witness of the whole premise set at one state is given here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YG0ncf YG0dcf YGcfRoomPre YGcfRoomKeep YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YF0m YD2l YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Witness.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PN102BCuts PN102BS1 PN102BS2 PN102BS34
  PN102BS5 PN102BS6.
Import ListNotations.
Local Open Scope Z_scope.

(* the image binding TB at the real B' binding (YD2l.v, TfibB') *)
Lemma pn_top_TB_witness : YF0m.TfibSyms YD2l.TfibB.
Proof. exact YD2l.TfibB_syms. Qed.

(* NON-VACUITY at TfibB: the batch kit's closure premise (which carried the f97c DW slot-word clause) for some driver context, and
   the batch kit's room premise at the driver's start depot, both the kit's witnesses (lib/A/PRH_Witness.v) at the real binding *)
Lemma pn_top_univ_witness : exists CTX0, @prh_univ_closure prh_img_B YD2l.TfibB CfImgB.CfImg_B CTX0.
Proof. eexists. exact (PRH_Witness.prh_univ_closure_witness_B YD2l.TfibB eq_refl eq_refl). Qed.
Lemma pn_top_wild_witness :
  YCbqGwild.wild_room (as_universe YD2l.TfibB) [] (prh_wk F_parse_noting) (st_depot init_state).
Proof.
exact (PRH_Witness.prh_wild_room_witness_B YD2l.TfibB F_parse_noting eq_refl
  ltac:(rewrite pn_wk_B; unfold YCbqGwild.K_LLVMF; lia)).
Qed.

Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := (@PI_prog_B rc).
#[local] Abbreviation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Abbreviation RL := (prh_room_live_a8 (cp := CP)).
Variable B : asyms.
#[local] Abbreviation ARc := (fun ly S Hp (W : world SEGS) mem md =>
  ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Variable CTX0 : list (list Z).
(* the image binding of B (witness pn_top_TB_witness) *)
Hypothesis TB : YF0m.TfibSyms B.
(* the callee texts (owners in the header) *)
Hypothesis HLIVE : tfuzz_alloc_live_specX (fx := fx) (cp := CP) (PI := prh_img_B) (RL := RL) (PA := PA) B ARc SK.
Hypothesis HPJ : forall CW : list (list Z),
  tpj_parse_specX (fx := fx) (cp := CP) (PI := prh_img_B) (RL := RL) (PA := PA) B ARc SK CTX0 CW.
Hypothesis HRO : forall fy : YK11.FPState,
  tfuzz_alloc_ran_out_specX (fx := fy) (cp := CP) (PI := prh_img_B) (RL := RL) (PA := PA) B ARc SK.
Hypothesis HCRC : forall fy : YK11.FPState,
  tcheck_reject_clean_specX (fx := fy) (cp := CP) (PI := prh_img_B) (RL := RL) (PA := PA) B ARc SK.
#[local] Abbreviation RZW := (wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Abbreviation RZT := (wle'_trans SEGS YGcfRehidePost.RZ_cf).
#[local] Abbreviation LIFT := (SRr_SRr' SEGS YGcfRehidePost.RZ_cf).

Theorem tparse_noting_specX_B :
  tparse_noting_specX (fx := fx) (cp := CP) (PI := prh_img_B) (RL := RL) (PA := PA) B ARc SK CTX0.
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
(* THE THEOREM AT THE REAL B' BINDING: B := YD2l.TfibB (TfibB'), TB discharged by pn_top_TB_witness; what remains are
   the four callee texts at that binding (owners in the header). *)
Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := (@PI_prog_B rc).
#[local] Abbreviation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Abbreviation ARcB := (fun ly S Hp (W : world SEGS) mem md =>
  ARcf (cp := CP) SEGS YD2l.TfibB ly S Hp W mem md /\ xs_placed_cf ly S).
Theorem tparse_noting_specX_TfibB : forall CTX0,
  tfuzz_alloc_live_specX (fx := fx) (cp := CP) (PI := prh_img_B) (RL := prh_room_live_a8 (cp := CP)) (PA := PA)
    YD2l.TfibB ARcB SK ->
  (forall CW : list (list Z), tpj_parse_specX (fx := fx) (cp := CP) (PI := prh_img_B)
    (RL := prh_room_live_a8 (cp := CP)) (PA := PA) YD2l.TfibB ARcB SK CTX0 CW) ->
  (forall fy : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fy) (cp := CP) (PI := prh_img_B)
    (RL := prh_room_live_a8 (cp := CP)) (PA := PA) YD2l.TfibB ARcB SK) ->
  (forall fy : YK11.FPState, tcheck_reject_clean_specX (fx := fy) (cp := CP) (PI := prh_img_B)
    (RL := prh_room_live_a8 (cp := CP)) (PA := PA) YD2l.TfibB ARcB SK) ->
  tparse_noting_specX (fx := fx) (cp := CP) (PI := prh_img_B) (RL := prh_room_live_a8 (cp := CP)) (PA := PA)
    YD2l.TfibB ARcB SK CTX0.
Proof.
intros CTX0 HL HP HR HC.
exact (tparse_noting_specX_B (fx := fx) (SK := SK) YD2l.TfibB CTX0 pn_top_TB_witness HL HP HR HC).
Qed.
End R.

(* ---------------------------------------------------------------------- *)
(* THE CHECKS: the elaborated statements with every implicit argument shown, the entry float state in its class
   position; the closure. *)
Set Printing Implicit. Unset Printing Notations.
Check @tparse_noting_specX_TfibB.
Check @tparse_noting_specX_B.
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
Print Assumptions tparse_noting_specX_TfibB.
Print Assumptions tparse_noting_specX_B.
Print Assumptions pn_top_univ_witness.
Print Assumptions pn_top_wild_witness.
