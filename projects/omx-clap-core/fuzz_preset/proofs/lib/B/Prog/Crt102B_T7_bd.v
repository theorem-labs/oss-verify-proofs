(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 996 of its 1069 lines of code are new or changed and 441 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Crt102B_T7.v; 94 of its 144 lines of code are new or changed and 1019 lines of the source are left out. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan
   d663f82d7f488d30, unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T7 = CRT-B-CEXIT: THE ROW'S
   INTERNAL BOUNDARIES.

   proves no function (kind: boundary definitions of a segment walk).

   The segment C (+0x6f8) .. the exit `j` X (+0x80c) is cut at three more points, each the state just before an
   instruction of B/Listing_prog.v 8bcc2c9e7809 (lines 1636 / 1638 / 1640; offsets DERIVED from Crt102Img.v's call
   offsets, 4 bytes per instruction):
     FF (+0x7f8 = CRT_FF2_CALL_B - 4, `ld a0, 0(s1)`): both __wrap_strcmp checks and the type check passed; the state
        is crt_at_C_B's (the strcmp calls write only below s1 and the run stores nothing);
     PF (+0x800 = CRT_FF2_CALL_B + 4, `ld a0, 0x38(s1)`): fuzz_free (saved) returned; t7_at_PF;
     E  (+0x808 = CRT_PJF2_CALL_B + 4, `mv s5, zero`): pj_free (&back) returned; t7_at_E.
   T7_AT_C / T7_AT_FF / T7_AT_PF / T7_AT_E are `the run from that cut reaches QF` (the glue's CRT_B_AT_* shape);
   T7_AT_C is the glue's CRT_B_AT_C at the B instance.

   crt_at_C_B carries the facts this row found missing (the row's seam fix, frozen bd1a4a7ce28e, block facts restated
   to the PERMUTATION form eda8876a8e89): kw = last (wcaps (copy_set ms) true) 0, back's and copy's block sizes against
   tblk up to permutation, copy's depth; and the two FREE ORDERS - back's (frozen 7281359fe8bc), which t7_at_PF
   carries as t7_back_tie for pj_free (&back), and copy's (Crt102Glue.v at 275deb46b92d), which t7_at_PF and t7_at_E
   carry as t7_copy_tie up to X, where crt_at_J_B asks for it.

   KB ROUND (the glue's wild budget, Crt102Glue.v G3 / G4): t7_at_PF and t7_at_E carry crt_live at kb = prh_wk
   F_check_round_trip (66), the budget of crt_at_C_B and crt_at_J_B; their text is unchanged, the notation liveB carries
   the budget. The T7_AT_* statements are unchanged.

   INPUTS OF RECORD: this tree's Crt102Glue.v, Crt102Img.v, Crt102Model.v (the row's base was commit cbe6d10993c2, an
   ancestor of this tree; the contract texts at the kit tip 3ac20a5c9e30); lib/Spec PresetReqAt.v / PresetReqAtNoMiss.v.

   NUMERALS. LENGTH: 4 (one instruction). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
(* the re-hiding move's step relation (YA0nH.SRr') at preset's zone RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt PresetReqAtNoMiss PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- the row's three internal cuts (DERIVED from Crt102Img.v's call offsets; checked against the listing) ---- *)
Definition CRT7_FF_OFF_B : Z := CRT_FF2_CALL_B - 4.   (* +0x7f8 `ld a0, 0(s1)`, line 1636 *)
Definition CRT7_PF_OFF_B : Z := CRT_FF2_CALL_B + 4.   (* +0x800 `ld a0, 0x38(s1)`, line 1638 *)
Definition CRT7_E_OFF_B : Z := CRT_PJF2_CALL_B + 4.   (* +0x808 `mv s5, zero`, line 1640 *)
Lemma crt7_cut_FF_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT7_FF_OFF_B) = Some (PW 0x4b503).
Proof. vm_compute. reflexivity. Qed.
Lemma crt7_cut_PF_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT7_PF_OFF_B) = Some (PW 0x384b503).
Proof. vm_compute. reflexivity. Qed.
Lemma crt7_cut_E_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT7_E_OFF_B) = Some (PW 0xa93).
Proof. vm_compute. reflexivity. Qed.
Lemma crt7_cuts_B : CRT7_FF_OFF_B = 2040 /\ CRT7_PF_OFF_B = 2048 /\ CRT7_E_OFF_B = 2056 /\ CRT_C_OFF_B = 1784 /\
  CRT_X_OFF_B = 780.
Proof. vm_compute. repeat split. Qed.

Section t7. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model)
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z))
  (Lam : list (Z * Z)) (peak cnt ran most : Z).
(* kb round: every state of this row (C, FF, PF, E, X) is at kb = prh_wk F_check_round_trip (66): parse_noting is
   behind, and strcmp, fuzz_free and pj_free store no fresh wild trace (Crt102Glue.v G4). As the A' twin's livea
   (Crt102Loops.v), the notation carries the budget, so liveB below is crt_live at 66. *)
#[local] Notation liveB := (@crt_live rc prh_img_B RL SK B_prog_listing PA B ARx
  ly S Hp W regs mem md doc t D Lam peak most (prh_wk F_check_round_trip)).
#[local] Notation atCB := (@crt_at_C_B fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt most).
#[local] Notation QFb := (@QF fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).
#[local] Notation cfgB := (@crt_cfg rc B_prog_listing PA CRT_PC_B).
#[local] Notation bregsB := (@crt_bregs_B regs).
#[local] Notation spillB := (@crt_spill rc B_prog_listing PA regs).
#[local] Notation posB := (crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (t := t)).
#[local] Notation tcB := (@crt_tc t).
#[local] Notation treeJ := (crt_tree_J (t := t)).

(* back's FREE ORDER, crt_at_C_B's conjunct (Crt102Glue.v at 7281359fe8bc) in the words t7_at_PF carries it in:
   pj_free's order list Fb of back's tree has the model's requests fo crt_tc IN ORDER. pj_free (&back)'s text
   (PRH_FnPj.tpj_free_specX) moves the room position only for a run whose next events are prhPj_free_evs Fb. *)
Definition t7_back_tie (Wc : world SEGS) (memc : word -> option byte) (Lamc : list (Z * Z)) (lyc : alayout)
  (pos : Z) (Dback : list (Z * Z)) : Prop :=
  exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
      (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback Fb /\
    map (fun b => snd b + cf_head) Fb = PresetReqAt.fo tcB.

(* copy's FREE ORDER, crt_at_C_B's other conjunct (Crt102Glue.v at 275deb46b92d, the same freeze on the copy side):
   copy's order list Fc holds the model's requests fo crt_tree_J IN ORDER. T7 writes none of copy's blocks, so the
   cuts carry it from C to X (PRH_PjOrder.pj_foR_frame across each memory change), where crt_at_J_B asks for it. *)
Definition t7_copy_tie (Wc : world SEGS) (memc : word -> option byte) (Lamc : list (Z * Z)) (lyc : alayout)
  (pos : Z) (Dc : list (Z * Z)) : Prop :=
  exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
      (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
    map (fun b => snd b + cf_head) Fc = PresetReqAt.fo treeJ.

(* ---- PF (+0x800): fuzz_free (saved) has returned. Its block has left the walk's list and the ledger; the room
   position stands at pj_free (&back)'s event; back's free-order tie came through fuzz_free. ---- *)
Definition t7_at_PF (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Dback Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset : Z) : Prop :=
  t = PjTree.JObj ms /\
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  liveB lyc Sc Hpc Wc memc mdc kj pos (Dback ++ Dc) Lamc peakc cntc 0 0 /\
  bregsB rg (frame_addr lyc CRT_CID pos) /\
  spillB Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  0 <= cset <= 3 /\ (In ck_MOD_AT (map fst ms) -> cset = 0) /\
  cntc = cnt + ck_crt_count t cset /\
  pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) treeJ Dc /\
  Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk treeJ) /\
  t7_copy_tie Wc memc Lamc lyc pos Dc /\
  (PjTree.depth treeJ <= DOC_D)%nat /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) tcB Dback /\
  Permutation (map (fun b => snd b + cf_head) Dback) (PresetReqAtNoMiss.tblk tcB) /\
  posB Sc ([PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))] ++
           [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))]) /\
  t7_back_tie Wc memc Lamc lyc pos Dback.

(* ---- E (+0x808): pj_free (&back) has returned. Only copy's blocks are left beyond the entry's, and only
   pj_free (&copy)'s event of round_trip: crt_at_X_B's r = 0 state but for s5, which +0x808 clears. Its copy conjuncts
   are crt_at_J_B's r = 0 arm's (pj_nodeR at crt_tree_J, the blocks against tblk up to permutation, the depth). ---- *)
Definition t7_at_E (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset : Z) : Prop :=
  t = PjTree.JObj ms /\
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  liveB lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc 0 0 /\
  bregsB rg (frame_addr lyc CRT_CID pos) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  0 <= cset <= 3 /\ (In ck_MOD_AT (map fst ms) -> cset = 0) /\
  cntc = cnt + ck_crt_count t cset /\
  pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc /\
  posB Sc [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))] /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) treeJ Dc /\
  Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk treeJ) /\
  t7_copy_tie Wc memc Lamc lyc pos Dc /\
  (PjTree.depth treeJ <= DOC_D)%nat.

(* ---- the stretch statements of the row's cuts: from any state a cut describes, at any float state, QF ---- *)
Definition T7_AT_C : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw,
  atCB fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_C_OFF_B rg memc mdc) QFb.
Definition T7_AT_FF : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw,
  atCB fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT7_FF_OFF_B rg memc mdc) QFb.
Definition T7_AT_PF : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset,
  t7_at_PF fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT7_PF_OFF_B rg memc mdc) QFb.
Definition T7_AT_E : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg ms cset,
  t7_at_E fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg ms cset ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT7_E_OFF_B rg memc mdc) QFb.
(* the glue's X statement at the B instance (Crt102Glue.v CRT_B_AT_X; T4's CRTB_X by conversion) *)
Definition T7_AT_X : Prop :=
  @CRT_B_AT_X fx rc prh_img_B RL SK B_prog_listing PA CRT_PC_B CRT_X_OFF_B B ARx rp_sm rp_x rp_os rp_i rp_H0
    ly S Hp W regs mem md doc t D Lam peak cnt ran most.

End g.
End f.
End t7.
