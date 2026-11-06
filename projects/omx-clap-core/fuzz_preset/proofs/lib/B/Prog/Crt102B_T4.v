(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 3520 of its 3599 lines of code are new or changed and 435 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): every journal of this row is the engine's R form at R := YA0nH.wle'
   SEGS YGcfRehidePost.RZ_cf (the notations AJ / AJW, as Crt102KitB.v) and every segment statement (CRTB_* / CRT4_*,
   T4_GOAL_PJW, t4_goal_pn) concludes YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (the glue's crt_live_journal and QF are
   there). Calls: pj_write over YCbqGwild.aj_call_xbFR, parse_noting over aj_call_xbF_spR, fuzz_alloc_ran_out (a plain
   text) over aj_call_xb_spR after apost_base_x_R_lift, the strlen row (a plain text) over the local cb4_strlen_xromR
   (the engine has no R form of aj_strlen_at_xrom) under YA0nH.SRr_SRr'. THE LENGTH BOUND: the run's
   `(length rp_os <= 4)%nat` is the Section hypothesis HOS4 (pj_write's text and parse_noting's hull ask it). THE HULL:
   parse_noting's hull budget is paid from the run position (PresetHullPay.hull_budget_of_room_pos, the reading's events
   an infix of round_trip, c4_hull_pn). Contract note: the re-hiding contract (the internal file WLE-CONTRACT.md, not in this tree). *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan
   d663f82d7f488d30, unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T4: the segment
   W, N, O2, FF, X = B' entry + 0x2a4 -> + 0x348 (round_trip_rewrite inlined, fuzz_preset.c new:735-743).

   proves no function (kind: segment lemma).

   INPUTS OF RECORD (taken by path):
   - base commit 5e7e7aa75c4e (merged; glue Records, the landing cut 7cdbb61b5fa0, Crt102Img / Crt102ImgB split):
     the glue lib/A/Prog/Crt102Glue.v (crt_side 6 wide;
     crt_pos with the strtod tie and prh_cons_from; CRT_W0_OFF_B; the frozen B' boundaries crt_at_W_B with copy's
     guarded blocks against tblk and depth, crt_at_J_B / crt_at_X_B with r = 0, crt_at_L0_B with copy's and back's
     blocks over Permutation and back's free order (pj_foR .. = fo crt_tc) on the granted arm, crt_bregs_B,
     crt_dregs_B, CRT_SP_*_B, CRT_OWN_LO_B), Crt102Img.v and Crt102ImgB.v, Crt102Model.v, the image-B kit Crt102KitB.v (twelve
     helpers cited), and the contract texts
     the base carries (commit 3ac20a5c9e30: the ledger with g_most / g_own_ran_out as fields; tpj_write_specX;
     tparse_noting_specX in the post-implication form with its outcome clause; tfuzz_alloc_ran_out_specX; fpre with
     frm_zero at entry), consumed unchanged;
     lib/Reusable/YImgTop.v is the base's record blob (IMG_TOP_B = 0x601000), so the segment is stated at PI_prog_B.
   - the A' twins: Crt102Arms.v 97a937b1e61 (the call / live / chain templates), Crt102Rewrite.v 370f759b180.
   - pins: A' asan 1be0f53d96cb9d6c (twin bff8519bbe3ea0e4), B' asan-ubsan d663f82d7f488d30 (twin c90d4fa54d43160b).
   - listing: lib/B/Listing_prog.v 8bcc2c9e7809 (commit d42e123915ae). The body was decoded
     word by word from the pin itself: a lane record (the internal file decode-T4.txt) (+0x288 ..
     +0x34c, every word equal to the listing's, sha256 faffcb209b9bc977), the internal file decode-L0.txt (+0x470 .. +0x4c0).
   - engine: the s1b set (YCbqG, YCbqGcall, YGcallMx, YGcallMxmn, YC1fPx) as the lane base carries it; the segment
     environment lib/A/Prog/S10Env.v.
   - build route pins102: the internal file zfb-targets.dc6f8f60073340be.sh, FACTS 8f3e7e1a07f1,
     PAU pau-preset-102.
   - rule 24: no released ASan proof of check_round_trip by name (the 13:37Z lookup: the released proofs are plain/ubsan
     only; re-checked 2026-10-31 12:14Z by name and by a recipes git grep). The row's address lookups are no evidence
     here (fuzz_preset's released builds carry no symbol table), so none is cited; written new. The census-1
     cold/* sweep (15:56Z, a lane record (the internal file census-T4.out) sha256 61997a9902375ef2) found no
     other walk of this segment.
   - kb round (on the A' head a54cc6d36c2c with the kb Glue): the glue's crt_live
     with its budget kb and its journal at a budget WS with wbudget [] kb WS, QF at the text's budget
     prh_wk F_check_round_trip = 66 (Crt102Glue.v G1 - G4: W_B at 64, L0_B / J_B / X_B at 66); Crt102KitB.v at the
     kb glue (cb4_ff / cb4_chain at any budget, cb4_live_call over budgeted journals, cb4_live_mono); the A' twins
     Crt102Rewrite.v (crt102rw_strlen_call, crt102rw_R724, crt102rw_wild_budget_pn_goal, crt102rw_kb_pn) and
     Crt102Kit.v (crt102rw_call / crt102rw_call_b, and its image-free Section kbw, Required here); the engine
     YCbqGwild.v (aj_call_xb / aj_call_xbF / aj_call_xbF_sp, apost_base_xb_of_x / apost_base_xbF_of_x,
     ajournal_xw_rebase / ajournal_xw_unbase0, ajournal_xw_room, wild_room_le, wbudget_app).

   STATUS (kb round). Closed (Qed): crtB_T4_X (X -> J, both at 66), crt4_lane_W (W -> Wr at 64, from crt_at_W_B,
   given T4_GOAL_PJW; pj_write over the budgeted rule at its empty budget), crt4_lane_Wr (Wr -> S at 64 | O2 in the
   L0 state at 66: the failed-write arm skips parse_noting and steps 64 up to 66 by Crt102KitB.cb4_live_mono),
   crt4_lane_S_at (S at 64 -> O2 at 66 given t4_goal_pn: strlen over rebase / unbase0, parse_noting's wild room
   paid from the text's entry room HWR0, the caller landing at 64 + 2 by wbudget_app, crt4_kb_pn), crt4_lane_O2
   (O2 -> L0), cb4_back_tblk (back's blocks against tblk), cb4_back_fo (back's free order is fo crt_tc, by
   PresetFreeFo.pj_frees_acc and pj_frees_wdoc_t), t4_goal_pjw (T4_GOAL_PJW by ONE application of the
   callee text tpj_write_specX, which states DEAD-PJWRITE at this head), t4_goal_pn_holds (t4_goal_pn RESTATED in
   the kb form - the text's wild room premise in the text's place and its budgeted post fpostFbm .. (wbudget []
   (prh_wk F_parse_noting)) - and proved from the text PN), and the composition crtB_T4 : CRTB_L0 -> CRTB_W (its
   t4_goal_pn premise retired). T4 has no open goal.
   The FF block (+0x300 .. +0x30c, r = 1) is unreachable (crt_at_X_B carries r = 0): every entry is refuted at its
   source (crtB_T4's comment). Section hypotheses: the text's own premises (HPRE .. HFR, and HWR0, the text's entry
   wild room, PRH_FnCheck.v:1366) and the callee texts PN / PJW / FRO / ASTRLEN. Named Section hypothesis:
   ALX_CEIL8 (SRC-CEIL -> alx_blocks_ceil8, the allocator engine's F21b), no longer used by any lemma here (see its
   comment). pj_write's entry run events are supplied by PRH_Supply.prhWriter_pjw_evs_w_evs / _granted (cited;
   the base's PRH_Supply.v builds in this closure).

   THE B' CODE (pin d663f82d, offsets from the B' entry 0x82828):
     +0x2a4 addi a0, s3, 0x20     +0x2a8 sd a0, 0x38(s1)      &back spilled
     +0x2ac addi a1, zero, 1      +0x2b0 addi s5, zero, 1     +0x2b4 mv a0, s4      +0x2b8 jal pj_write
     +0x2bc mv s8, a0             +0x2c0 beqz a0, +0x2f0
     +0x2c4 lbu a0, 0x2d0(s10)    +0x2c8 bnez a0, +0x300      +0x2cc jal fuzz_alloc_ran_out  +0x2d0 bnez a0, +0x2f0
     +0x2d4 mv a0, s8             +0x2d8 jal __wrap_strlen
     +0x2dc mv a1, a0  +0x2e0 mv a0, s8  +0x2e4 ld a2, 0x38(s1)  +0x2e8 jal parse_noting  +0x2ec snez s5, a0
     +0x2f0 lbu a0, 0x2d0(s10)    +0x2f4 bnez a0, +0x300      +0x2f8 jal fuzz_alloc_ran_out  +0x2fc beqz a0, +0x478 (L0)
     +0x300 mv a0, s8             +0x304 jal fuzz_free        +0x308 addi s5, zero, 1
     +0x30c addi a0, zero, -8     +0x310 .. +0x344 fourteen `sb a0, k(s2)` (k = 8 9 10 16 .. 22 4 .. 7): X
     +0x348 mv a0, s4: J.

   NUMERALS. DERIVED: the cut offsets 676 / 780 / 840 / 1144 (4 * the slot inside the function, the pin's decode;
   checked against the listing by vm_compute below), 720 (the lbu immediate 0x2d0 of the words at +0x2c4 / +0x2f0),
   4 / 23 (the frame's shadow bytes the re-poison writes: back's 4 .. 10, v's 16 .. 22), 56 .. 96 (the spill words of
   s1 the segment writes, 0x38). LENGTH: 512 / 64 (the class-3 frame and its shadow), 16 (cf_head), 256 (the frame
   bound of sp1). WORD: register indices. No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetFreeFo PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
(* the B' image Section of Crt102Img.v (CRT_PC_B, the CRT_*_OFF_B cuts, ..), moved to its own file *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
(* the image-B kit: twelve helpers this file used to hold, moved there character for
   character (Crt102KitB.v's header); this file cites them through the abbreviations below and inside Section g *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Crt102KitB.
(* the A' kit's image-free kb Section kbw (lib/A/Prog/Crt102Kit.v: crt_run_xw / crt_run_to_xw / crt_run_xw_inv /
   crt_run_to_xw_inv, the runners over a journal at a wild-trace budget, and crt_jw_wild), cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetCfnA.
(* the model supply lemmas (the base's lib/A/PRH_Supply.v, from commit d7c502629be9 at a508dcbd0df) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Supply.
(* the re-hiding move's world and step relations (YA0nH), the step lemmas (YSRrG), the zone
   (YGcfRehidePost.RZ_cf); the hull budget (PresetHullBudget, PresetHullPay) and the counts it is paid from *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetSecTotal PresetSecTotalRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Notation cb4_fb := Crt102KitB.cb4_fb.
#[local] Notation cb4_stkc := Crt102KitB.cb4_stkc.
#[local] Notation cb4_ro_img := Crt102KitB.cb4_ro_img.
#[local] Notation cb4_fregs_trans := Crt102KitB.cb4_fregs_trans.
#[local] Notation cb4_rdword_of_val_mem := Crt102KitB.cb4_rdword_of_val_mem.
#[local] Notation cb4_fpchain_keep := Crt102KitB.cb4_fpchain_keep.

(* ---- the cuts of this row on B' (DERIVED: 4 * the slot inside the function, the pin's decode). W0 (+0x2a4: O1's
   fall-through, `addi a0, s3, 0x20`: the T3 / T4 cut) is the glue's CRT_W0_OFF_B (Crt102Glue.v, defined once) ---- *)
Lemma crt_cut_W0_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_W0_OFF_B) = Some (PW 0x2098513).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cuts_T4_B : CRT_X_OFF_B = 780 /\ CRT_J_OFF_B = 840 /\ CRT_L0_OFF_B = 1144.
Proof. vm_compute. repeat split. Qed.
(* this row's own internal cut S (+0x2d4, `mv a0, s8`: the run after the first ran_out test fell through, before the
   strlen call); the other internal cuts are Crt102Img.v's CRT_W_OFF_B (+0x2bc, pj_write's return) and CRT_O2_OFF_B
   (+0x2f0); CRT_FF_OFF_B (+0x300) starts the unreachable r = 1 block *)
Definition CRT4_S_OFF_B : Z := 724.
Lemma crt_cut_S_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT4_S_OFF_B) = Some (PW 0xc0513).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cuts_T4i_B : CRT_W_OFF_B = 700 /\ CRT_O2_OFF_B = 752 /\ CRT_FF_OFF_B = 768.
Proof. vm_compute. repeat split. Qed.

(* the kb arithmetic of this row (prh_wk F_check_round_trip = 66 = 32 + 32 + 2, PRH_Base.v:151-160; the A' twin is
   Crt102Rewrite.crt102rw_kb_pn): the W state's 64 = prh_wk F_round_trip_text + prh_wk F_round_trip_text leaves the
   parse_noting call its 2, and lands at 66 *)
Lemma crt4_kb_pn :
  (prh_wk F_round_trip_text + prh_wk F_round_trip_text + prh_wk F_parse_noting <= prh_wk F_check_round_trip)%nat.
Proof. cbn. lia. Qed.

(* ======================================================================================================== *)
(* PART 1, image-free: the freeable-tree facts (Crt102Rewrite.v b96772c578f :37-231, prefix crt102rw_ renamed cb4_).
   cb4_nodeR_fdR: a represented tree is freeable at its depth; cb4_fdR_mono: freeable at d is freeable at every
   d' >= d; cb4_fdR_frame: a freeable tree whose footprint keeps its bytes (and writability) is the same tree. *)
Section rd.
Variable segs : list Segment.

Lemma cb4_pf_items_mono : forall m lblk (P Q : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a D1, P a D1 -> Q a D1) -> pf_itemsR segs m lblk P ks a ka n D -> pf_itemsR segs m lblk Q ks a ka n D.
Proof.
intros m lblk P Q ks n. induction n as [|n IH]; intros a ka D H Hp; cbn [pf_itemsR] in *; [exact Hp|].
destruct Hp as (Dk & D1 & D2 & E & Hk & HP & HR). exists Dk, D1, D2.
split; [exact E|]. split; [exact Hk|]. split; [exact (H a D1 HP) | exact (IH (a + 56) (ka + 8) D2 H HR)].
Qed.
Lemma cb4_fshape_mono : forall m lblk (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) p D,
  (forall ks kids keys n Di, Pi ks kids keys n Di -> Pi' ks kids keys n Di) ->
  pj_fshapeR segs m lblk Pi p D -> pj_fshapeR segs m lblk Pi' p D.
Proof.
intros m lblk Pi Pi' p D H (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6).
split; [exact Hn|]. split; [exact Ha|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. exact (H _ _ _ _ _ H6).
Qed.
Lemma cb4_fdR_succ : forall m lblk d p D, pj_fdR segs m lblk d p D -> pj_fdR segs m lblk (S d) p D.
Proof.
intros m lblk d. induction d as [|d IH]; intros p D H; cbn [pj_fdR] in H |- *.
- eapply (cb4_fshape_mono m lblk); [|exact H]. intros ks kids keys n Di (En & EDi). cbv beta. subst n Di. exact eq_refl.
- eapply (cb4_fshape_mono m lblk); [|exact H]. intros ks kids keys n Di Hi. cbv beta in Hi |- *.
  apply (cb4_pf_items_mono m lblk (pj_fdR segs m lblk d)); [|exact Hi]. intros a D1 H1. exact (IH a D1 H1).
Qed.
Lemma cb4_fdR_mono : forall m lblk d d' p D, (d <= d')%nat -> pj_fdR segs m lblk d p D -> pj_fdR segs m lblk d' p D.
Proof.
intros m lblk d d' p D Hle. induction Hle as [|d' Hle IH]; intros H; [exact H|]. apply cb4_fdR_succ. apply IH. exact H.
Qed.
Lemma cb4_items_pf : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, In u l -> P a u D1 -> Q a D1) ->
  pj_itemsR P a l D -> pf_itemsR segs m lblk Q false a ka (length l) D.
Proof.
intros m lblk P Q l. induction l as [|u r IH]; intros a ka D H Hl; cbn [pj_itemsR pf_itemsR length] in *; [exact Hl|].
destruct Hl as (D1 & D2 & E & HP & HR). exists [], D1, D2.
split; [exact E|]. split; [exact eq_refl|]. split; [apply (H a u D1); [left; reflexivity | exact HP]|].
apply IH; [intros a' v D3 Hv HP3; apply (H a' v D3); [right; exact Hv | exact HP3] | exact HR].
Qed.
Lemma cb4_mems_pf : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> Q a D1) ->
  pj_memsR segs m lblk P a ka l D -> pf_itemsR segs m lblk Q true a ka (length l) D.
Proof.
intros m lblk P Q l. induction l as [|[nm u] r IH]; intros a ka D H Hl; cbn [pj_memsR pf_itemsR length] in *; [exact Hl|].
destruct Hl as (x & k & D1 & D2 & E & Hx & (Hb & _) & HP & HR). exists [(x, k)], D1, D2.
split; [exact E|].
split; [unfold pj_keyR; exists x; split; [exact Hx | right; exists k; split; [exact Hb | reflexivity]]|].
split; [apply (H a u D1); [exists nm; left; reflexivity | exact HP]|].
apply IH; [intros a' v D3 (nm' & Hv) HP3; apply (H a' v D3); [exists nm'; right; exact Hv | exact HP3] | exact HR].
Qed.
Lemma cb4_nodeR_fdR : forall t m lblk p D, pj_nodeR segs m lblk p t D -> pj_fdR segs m lblk (PjTree.depth t) p D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; intros m lblk p D H;
  cbn [pj_nodeR] in H.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JNull), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JFalse), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JTrue), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag (PjTree.JNum txt bits)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
  split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag (PjTree.JStr s)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
  split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  remember (PjTree.depth (PjTree.JArr items)) as dd eqn:Edd. destruct dd as [|d']; [cbn [PjTree.depth] in Edd; discriminate|].
  cbn [pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
  assert (HI : pf_itemsR segs m lblk (pj_fdR segs m lblk d') false kids keys (Z.to_nat n) Di).
  { rewrite En, Nat2Z.id. apply (cb4_items_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 Hu HP. rewrite Forall_forall in IH.
    apply (cb4_fdR_mono m lblk (PjTree.depth u)); [|exact (IH u Hu m lblk a D1 HP)].
    pose proof (PjTree.depth_item items u Hu). lia. }
  destruct Hcap as [(Hc0 & Hk0)|(Hc0 & Hl)].
  + subst cap. exists (PjTree.tag (PjTree.JArr items)), num, str, kids, keys, n, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|]. split; [left; split; [exact Ek | split; reflexivity]|].
    split; [subst D; cbn; apply Permutation_refl|]. exact HI.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    exists (PjTree.tag (PjTree.JArr items)), num, str, kids, keys, n, cap, false, [], [(kids, 56 * cap)], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [right; exists (56 * cap); split; [exact Hl | split; [lia | reflexivity]]|].
    split; [left; split; [exact Ek | split; reflexivity]|]. split; [subst D; cbn [app]; apply Permutation_refl|]. exact HI.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
  remember (PjTree.depth (PjTree.JObj members)) as dd eqn:Edd. destruct dd as [|d']; [cbn [PjTree.depth] in Edd; discriminate|].
  cbn [pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
  destruct Hcap as [(Hc0 & Hk0 & Hy0)|(Hc0 & L0 & L1)].
  + subst cap. destruct members as [|mb members]; cbn [length] in En; [|lia]. cbn [pj_memsR] in Hi.
    exists (PjTree.tag (PjTree.JObj [])), num, str, kids, keys, n, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|]. split; [left; split; [exact Hy0 | split; reflexivity]|].
    split; [subst D; cbn; apply Permutation_refl|]. cbv beta. replace (Z.to_nat n) with 0%nat by lia. exact Hi.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    exists (PjTree.tag (PjTree.JObj members)), num, str, kids, keys, n, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
    split; [right; split; [reflexivity | exists (8 * cap); split; [exact L1 | split; [lia | reflexivity]]]|].
    split; [subst D; cbn [app]; apply Permutation_refl|].
    cbv beta. rewrite En, Nat2Z.id. apply (cb4_mems_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 (nm & Hu) HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (cb4_fdR_mono m lblk (PjTree.depth u)); [|exact (IH m lblk a D1 HP)].
    pose proof (PjTree.depth_member members nm u Hu). lia.
Qed.

(* the frame lemma of a freeable tree: its header, its key words and its items lie in its footprint *)
Lemma cb4_pf_frame : forall m m' lblk (P P' : Z -> list (Z * Z) -> Prop) ks n a ka D (X : Z -> Prop),
  pf_itemsR segs m lblk P ks a ka n D ->
  (ks = true -> forall x, ka <= x < ka + 8 * Z.of_nat n -> X x) ->
  (forall x, X x -> mbyte segs m' x = mbyte segs m x) ->
  (forall i a1 D1, (i < n)%nat -> a1 = a + 56 * Z.of_nat i -> incl D1 D -> P a1 D1 -> P' a1 D1) ->
  pf_itemsR segs m' lblk P' ks a ka n D.
Proof.
intros m m' lblk P P' ks n. induction n as [|n IH]; intros a ka D X H HX HM HP; cbn [pf_itemsR] in H |- *; [exact H|].
destruct H as (Dk & D1 & D2 & E & Hk & H1 & H2). exists Dk, D1, D2. split; [exact E|]. split.
- unfold pj_keyR in Hk |- *. destruct ks; [|exact Hk]. destruct Hk as (x & Hx & Hd). exists x. split; [|exact Hd].
  apply (rd_u64_frame segs m m' ka x Hx). intros y Hy. apply HM. apply (HX eq_refl). lia.
- split.
  + apply (HP 0%nat a D1); [lia | lia | |exact H1]. subst D. intros b Hb. apply in_or_app. right. apply in_or_app. left. exact Hb.
  + apply (IH (a + 56) (ka + 8) D2 X H2).
    * intros Hks y Hy. apply (HX Hks). lia.
    * exact HM.
    * intros i a1 D3 Hi Ea Hinc HP3. apply (HP (S i) a1 D3); [lia | lia | |exact HP3].
      subst D. intros b Hb. apply in_or_app. right. apply in_or_app. right. exact (Hinc b Hb).
Qed.
Lemma cb4_fdR_frame : forall d m m' lblk p D, pj_fdR segs m lblk d p D ->
  pj_agreeR segs m m' (pj_footR p D) -> pj_fdR segs m' lblk d p D.
Proof.
intros d. induction d as [|d IH]; intros m m' lblk p D H HM; cbn [pj_fdR] in H |- *;
  destruct H as (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6);
  (split; [exact Hn|]); (split; [exact Ha|]); exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di;
  (split; [apply (pj_hdrR_frame segs m m'); [exact H1 | intros x Hx; apply HM; left; exact Hx]|]);
  (split; [exact H2|]); (split; [exact H3|]); (split; [exact H4|]); (split; [exact H5|]).
- exact H6.
- assert (HDi : forall b, In b Di -> In b D).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym H5)). rewrite !in_app_iff. tauto. }
  destruct (Z.eq_dec n 0) as [En0 | Hn0].
  + rewrite En0 in H6 |- *. cbn [Z.to_nat pf_itemsR] in H6 |- *. exact H6.
  + destruct H3 as [(_ & En & _) | (kb & Hkb & Hkn & EDk)]; [lia|].
    assert (HinK : In (kids, kb) D).
    { apply (Permutation_in _ (Permutation_sym H5)). rewrite !in_app_iff. subst Dk. cbn. tauto. }
    apply (cb4_pf_frame m m' lblk (pj_fdR segs m lblk d) (pj_fdR segs m' lblk d) ks (Z.to_nat n) kids keys Di
      (pj_footR p D) H6).
    * intros Hks x Hx. destruct H4 as [(_ & Ek & _) | (_ & yb & Hyb & Hyn & EDy)]; [rewrite Ek in Hks; discriminate|].
      right. exists (keys, yb). split.
      { apply (Permutation_in _ (Permutation_sym H5)). rewrite !in_app_iff. subst Dy. cbn. tauto. }
      unfold pj_holdsR. cbn [fst snd]. rewrite Z2Nat.id in Hx by lia. lia.
    * intros x Hx. exact (proj1 (HM x Hx)).
    * intros i a1 D1 Hi Ea Hinc HP. apply (IH m m' lblk a1 D1 HP). intros x Hx. apply HM.
      destruct Hx as [Hx | (b & Hb & Hx)].
      { right. exists (kids, kb). split; [exact HinK|]. unfold pj_holdsR. cbn [fst snd].
        apply Nat2Z.inj_lt in Hi. rewrite Z2Nat.id in Hi by lia. subst a1. lia. }
      { right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx]. }
Qed.

(* the block predicate of a tree is read only at the tree's own blocks: a tree whose blocks satisfy lblk' is the same
   tree under lblk' (the walk moves a tree from prh_lin Lam to prh_lin Lam' when a call adds or frees other blocks) *)
Lemma cb4_cstrR_lblk : forall m lblk lblk' a k s, pj_cstrR segs m lblk a k s -> lblk' a k -> pj_cstrR segs m lblk' a k s.
Proof. intros m lblk lblk' a k s (_ & H2 & H3 & H4) H. exact (conj H (conj H2 (conj H3 H4))). Qed.
Lemma cb4_itemsR_mono : forall (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D,
  pj_itemsR P a l D -> (forall a u D1, In u l -> incl D1 D -> P a u D1 -> P' a u D1) -> pj_itemsR P' a l D.
Proof.
intros P P' l. induction l as [|u r IH]; intros a D H HP; cbn [pj_itemsR] in *; [exact H|].
destruct H as (D1 & D2 & E & H1 & H2). exists D1, D2. split; [exact E|]. split.
- apply (HP a u D1); [left; reflexivity | | exact H1]. intros b Hb. rewrite E. apply in_or_app. left. exact Hb.
- apply (IH (a + 56) D2 H2). intros a' u' D3 Hu Hinc HP3. apply (HP a' u' D3); [right; exact Hu | | exact HP3].
  intros b Hb. rewrite E. apply in_or_app. right. exact (Hinc b Hb).
Qed.
Lemma cb4_memsR_lblk : forall m lblk lblk' (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D -> (forall a k, In (a, k) D -> lblk' a k) ->
  (forall a u D1, (exists nm, In (nm, u) l) -> incl D1 D -> P a u D1 -> P' a u D1) ->
  pj_memsR segs m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D H HL HP; cbn [pj_memsR] in *; [exact H|].
destruct H as (x & k & D1 & D2 & E & Hx & Hc & H1 & H2). exists x, k, D1, D2.
split; [exact E|]. split; [exact Hx|].
split; [apply (cb4_cstrR_lblk m lblk); [exact Hc | apply HL; rewrite E; left; reflexivity]|].
split.
- apply (HP a u D1); [exists nm; left; reflexivity | | exact H1]. intros b Hb. rewrite E. right. apply in_or_app. left. exact Hb.
- apply (IH (a + 56) (ka + 8) D2 H2).
  + intros a' k' Hak. apply HL. rewrite E. right. apply in_or_app. right. exact Hak.
  + intros a' u' D3 (nm' & Hu) Hinc HP3. apply (HP a' u' D3); [exists nm'; right; exact Hu | | exact HP3].
    intros b Hb. rewrite E. right. apply in_or_app. right. exact (Hinc b Hb).
Qed.
Lemma cb4_nodeR_lblk : forall t m lblk lblk' p D, pj_nodeR segs m lblk p t D ->
  (forall a k, In (a, k) D -> lblk' a k) -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; intros m lblk lblk' p D H HL;
  cbn [pj_nodeR] in H |- *; destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & HR);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact HR.
- exact HR.
- exact HR.
- destruct HR as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (cb4_cstrR_lblk m lblk); [exact Hc|]. apply HL. rewrite ED. left; reflexivity.
- destruct HR as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (cb4_cstrR_lblk m lblk); [exact Hc|]. apply HL. rewrite ED. left; reflexivity.
- destruct HR as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hcap | (Hc0 & Hl)]; [left; exact Hcap | right; split; [exact Hc0|]].
    apply HL. rewrite ED. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  exists Di. split; [exact ED|].
  apply (cb4_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di Hi).
  intros a u D1 Hu Hinc HP. rewrite Forall_forall in IH. apply (IH u Hu m lblk lblk' a D1 HP).
  intros a' k' Hak. apply HL. rewrite ED. apply in_or_app. right. exact (Hinc _ Hak).
- destruct HR as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hcap | (Hc0 & L0 & L1)]; [left; exact Hcap | right; split; [exact Hc0|]].
    split; apply HL; rewrite ED, (proj2 (Z.eqb_neq cap 0)) by lia; [left; reflexivity | right; left; reflexivity]. }
  exists Di. split; [exact ED|].
  apply (cb4_memsR_lblk m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di Hi).
  + intros a k Hak. apply HL. rewrite ED. apply in_or_app. right. exact Hak.
  + intros a u D1 (nm & Hu) Hinc HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (IH m lblk lblk' a D1 HP). intros a' k' Hak. apply HL. rewrite ED. apply in_or_app. right. exact (Hinc _ Hak).
Qed.
Lemma cb4_pfR_lblk : forall m lblk lblk' (P P' : Z -> list (Z * Z) -> Prop) ks n a ka D,
  pf_itemsR segs m lblk P ks a ka n D -> (forall a k, In (a, k) D -> lblk' a k) ->
  (forall a D1, incl D1 D -> P a D1 -> P' a D1) -> pf_itemsR segs m lblk' P' ks a ka n D.
Proof.
intros m lblk lblk' P P' ks n. induction n as [|n IH]; intros a ka D H HL HP; cbn [pf_itemsR] in *; [exact H|].
destruct H as (Dk & D1 & D2 & E & Hk & H1 & H2). exists Dk, D1, D2. split; [exact E|]. split.
- unfold pj_keyR in Hk |- *. destruct ks; [|exact Hk].
  destruct Hk as (x & Hx & Hk). exists x. split; [exact Hx|].
  destruct Hk as [Hz | (k & Hlk & EDk)]; [left; exact Hz|].
  right. exists k. split; [|exact EDk]. apply HL. rewrite E, EDk. left. reflexivity.
- split.
  + apply (HP a D1); [|exact H1]. intros b Hb. rewrite E. apply in_or_app. right. apply in_or_app. left. exact Hb.
  + apply (IH (a + 56) (ka + 8) D2 H2).
    * intros a' k' Hak. apply HL. rewrite E. apply in_or_app. right. apply in_or_app. right. exact Hak.
    * intros a' D3 Hinc HP3. apply (HP a' D3); [|exact HP3].
      intros b Hb. rewrite E. apply in_or_app. right. apply in_or_app. right. exact (Hinc b Hb).
Qed.
Lemma cb4_fshape_lblk : forall m lblk lblk' (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) p D,
  pj_fshapeR segs m lblk Pi p D -> (forall a k, In (a, k) D -> lblk' a k) ->
  (forall ks kids keys n Di, incl Di D -> Pi ks kids keys n Di -> Pi' ks kids keys n Di) ->
  pj_fshapeR segs m lblk' Pi' p D.
Proof.
intros m lblk lblk' Pi Pi' p D (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6) HL HP.
assert (Hin : forall b, In b (Ds ++ Dk ++ Dy ++ Di) -> In b D) by (intros b Hb; exact (Permutation_in _ (Permutation_sym H5) Hb)).
split; [exact Hn|]. split; [exact Ha|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
split; [exact H1|].
split.
{ destruct H2 as [H2 | (k & Hl & E)]; [left; exact H2 | right; exists k; split; [|exact E]].
  apply HL. apply Hin. rewrite E. left. reflexivity. }
split.
{ destruct H3 as [H3 | (k & Hl & Hk & E)]; [left; exact H3 | right; exists k; split; [|split; [exact Hk | exact E]]].
  apply HL. apply Hin. apply in_or_app. right. rewrite E. left. reflexivity. }
split.
{ destruct H4 as [H4 | (Hks & k & Hl & Hk & E)]; [left; exact H4 | right; split; [exact Hks|]; exists k; split; [|split; [exact Hk | exact E]]].
  apply HL. apply Hin. rewrite !in_app_iff. right; right; left. rewrite E. left. reflexivity. }
split; [exact H5|].
apply HP; [|exact H6]. intros b Hb. apply Hin. rewrite !in_app_iff. right; right; right. exact Hb.
Qed.
Lemma cb4_fdR_lblk : forall d m lblk lblk' p D, pj_fdR segs m lblk d p D ->
  (forall a k, In (a, k) D -> lblk' a k) -> pj_fdR segs m lblk' d p D.
Proof.
intros d. induction d as [|d IH]; intros m lblk lblk' p D H HL; cbn [pj_fdR] in H |- *.
- apply (cb4_fshape_lblk m lblk lblk' _ _ p D H HL). intros ks kids keys n Di _ HP. exact HP.
- apply (cb4_fshape_lblk m lblk lblk' _ _ p D H HL). intros ks kids keys n Di Hinc HP. cbv beta in HP |- *.
  apply (cb4_pfR_lblk m lblk lblk' (pj_fdR segs m lblk d) (pj_fdR segs m lblk' d) ks (Z.to_nat n) kids keys Di HP).
  + intros a k Hak. apply HL. apply Hinc. exact Hak.
  + intros a D1 Hinc1 H1. apply (IH m lblk lblk' a D1 H1). intros a' k' Hak. apply HL. apply Hinc. apply Hinc1. exact Hak.
Qed.
End rd.

(* ======================================================================================================== *)
(* PART 2, image B' at the B instance (lib/B/PAImg_prog.v PI_prog_B, PL_prog_B).                            *)
Section t4. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).

(* the B' values Crt102Img.v's Section b took as hypotheses HB_base / HB_entry / HB_segs, now by computation *)
Lemma cb4_base : BASE = B_prog_base.
Proof. vm_compute. reflexivity. Qed.
Lemma cb4_entry : SIGMA AS_check_round_trip = B_prog_base + CRT_PC_B.
Proof. vm_compute. reflexivity. Qed.
Lemma cb4_segs : SEGS = rsegs.
Proof. reflexivity. Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the re-hiding move: every journal at R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild-trace budget WS (YCbqG.v ajournal_xwR at RZW; AJ is it at WS = []); crt_live's journal is at
   the boundary's budget kb (kb round) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z)
  (CTX0 : list (list Z)) (a_mod_at a_stamp : Z).
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (@CRT_sp1 regs).
(* crt_live / crt_side carry no room position since 11c39f7e88b7 (so they take no rp_* argument); the position
   travels as crt_pos on the r = 0-path boundaries only *)
#[local] Notation liveB := (crt_live (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md)
  (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (most := most)).
#[local] Notation posB := (crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (t := t)).
#[local] Notation atJB := (@crt_at_J_B fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).
#[local] Notation atXB := (@crt_at_X_B fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).
#[local] Notation atL0B := (@crt_at_L0_B fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt most).
#[local] Notation QFb := (@QF fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).
#[local] Notation cfgB := (@crt_cfg rc B_prog_listing PA CRT_PC_B).
#[local] Notation dregsB := (@crt_dregs_B regs doc).
#[local] Notation spillB := (@crt_spill rc B_prog_listing PA regs).
#[local] Notation tcB := (@crt_tc t).
#[local] Notation cwB := (@crt_cw t cnt).
#[local] Notation wPB := (@crt_wP t).
#[local] Notation tbB := (@crt_tb t).
#[local] Notation sideB := (crt_side (rc := rc) (PI := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PA) (B := B)
  (doc := doc) (t := t) (D := D) (peak := peak) (most := most)).
(* what is left of round_trip after pj_write (&copy, 1) was granted: the reading, then L0's suffix *)
#[local] Notation evs_after_pjw := (fun ms => PresetReqAt.parse_evs rp_sm
  (WriterValue.wdoc (PresetReqAt.copy_set ms) true) [] ++ crt_evs_L0 ms).

(* THE PRE: the state at W (B' +0x2a4) is the glue's frozen crt_at_W_B (Crt102Glue.v; it ends in crt_pos Sc
   (crt_evs_W ms), the exact room position on the r = 0 path, then copy's blocks against tblk crt_tree_J up to
   permutation under the cf_head guard, and copy's depth; T4 threads both to L0). *)
#[local] Notation atWB := (@crt_at_W_B fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt most).

(* READING THE GLUE RECORDS BY PROJECTION (the Records re-point, the internal file RECORDS-BRIEF.md): each reader poses every field of
   one Record under the names the old intro patterns used; the journal field (kb round) is destructed into its
   budget WS, the journal HJ at WS and the budget bound HBW (wbudget [] kb WS) *)
Ltac cb4_rd_live HL WS HJ HBW HSD HPL HPB HAP HSV HFRM HSPF HCR HCH HMN :=
  destruct (crt_live_journal HL) as (WS & HJ & HBW); pose proof (crt_live_side HL) as HSD;
  pose proof (crt_live_lam_perm HL) as HPL; pose proof (crt_live_blocks_perm HL) as HPB;
  pose proof (crt_live_dx_apart HL) as HAP; pose proof (crt_live_saved HL) as HSV;
  pose proof (crt_live_frame HL) as HFRM; pose proof (crt_live_fspill HL) as HSPF;
  pose proof (crt_live_copy_open HL) as HCR; pose proof (crt_live_copy_hull HL) as HCH;
  pose proof (crt_live_memnorm HL) as HMN.
Ltac cb4_rd_side HSD HLED HPK HRL HRO HDOC HDL :=
  pose proof (crt_side_ledger HSD) as HLED; pose proof (crt_side_peak HSD) as HPK;
  pose proof (crt_side_room HSD) as HRL; pose proof (crt_side_arodata HSD) as HRO;
  pose proof (crt_side_doc HSD) as HDOC; pose proof (crt_side_doc_blocks HSD) as HDL.
Ltac cb4_rd_bregs HBR R2 R3 R4 R8 R9 R18 R20 R19 R23 R25 R27 :=
  pose proof (crt_bregs_B_sp HBR) as R2; pose proof (crt_bregs_B_gp HBR) as R3;
  pose proof (crt_bregs_B_tp HBR) as R4; pose proof (crt_bregs_B_s0 HBR) as R8;
  pose proof (crt_bregs_B_s1 HBR) as R9; pose proof (crt_bregs_B_s2 HBR) as R18;
  pose proof (crt_bregs_B_s4 HBR) as R20; pose proof (crt_bregs_B_s3 HBR) as R19;
  pose proof (crt_bregs_B_s7 HBR) as R23; pose proof (crt_bregs_B_s9 HBR) as R25;
  pose proof (crt_bregs_B_s11 HBR) as R27.
Ltac cb4_rd_dregs HDR R2 R3 R4 R8 R9 R18 R20 R19 R23 R25 R27 R22 :=
  cb4_rd_bregs (crt_dregs_B_bregs HDR) R2 R3 R4 R8 R9 R18 R20 R19 R23 R25 R27;
  pose proof (crt_dregs_B_s6 HDR) as R22.

(* ======================================================================================================== *)
(* THE SEGMENT STATEMENTS: each boundary is `the run from this configuration reaches QF` (Crt102Glue.v:244-247),
   over the frozen B' boundaries crt_at_J_B / crt_at_X_B / crt_at_L0_B, at the re-hiding move's
   step relation YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (the glue's CRT_B_AT_* are there) *)
Definition CRTB_J : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  atJB fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_J_OFF_B rg memc mdc) QFb.
Definition CRTB_X : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  atXB fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_X_OFF_B rg memc mdc) QFb.
Definition CRTB_L0 : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rc,
  atL0B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rc ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_L0_OFF_B rg memc mdc) QFb.
Definition CRTB_W : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg ms cset,
  atWB fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg ms cset ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_W0_OFF_B rg memc mdc) QFb.

(* ======================================================================================================== *)
(* THIS ROW'S INTERNAL CUTS (states of this row only; no other row consumes them).
   own = 0 throughout T4: crt_at_W_B has it, and every callee keeps the ledger's own cell, so the three `lbu a0,
   0x2d0(s10); bnez a0` tests (+0x2c4 / +0x2f0) never branch. g_ran_out = 0 throughout T4 too (every refusal that
   could set it is refuted at its source: crtB_T4's comment), so fuzz_alloc_ran_out () answers 0 at both its calls and
   the FF block (+0x300 .. +0x30c, fuzz_free then r = 1) is never reached. *)

(* after pj_write (&copy, 1) returned q (the writer's run `ok`, the flag `ranw` it left): the walk holds copy's blocks
   Dc and, when q <> 0, the text block (q, cap) at the head of the ledger *)
Definition crt4_wr_core (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset : Z) (ok : list bool) (ranw q : Z) : Prop :=
  let st' := PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB in
  t = PjTree.JObj ms /\
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  prh_oks ok (cwB cset) SIZE_MAXZ (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB)
    (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB) most 0 ranw /\
  liveB (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos
    (if q =? 0 then Dc else (q, WriterApp.w_cap st') :: Dc) Lamc peakc (WriterApp.w_cnt st') 0 ranw /\
  dregsB rg (frame_addr lyc CRT_CID pos) /\
  getr rg 21 = w64 1 /\
  getr rg 26 = w64 (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B) /\
  spillB Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) /\
  spillB Wc memc CRT_SP_SHN_B (shadow_addr (doc + PJ_OFF_N)) /\
  spillB Wc memc CRT_SP_PN_B (doc + PJ_OFF_N) /\
  spillB Wc memc CRT_SP_N_B (Z.of_nat (length ms)) /\
  doc mod 8 = 0 /\ range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  0 <= cset <= 3 /\ (In ck_MOD_AT (map fst ms) -> cset = 0) /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) tcB Dc /\
  (cf_head = PresetReqAt.HEAD ->
     Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk (@crt_tree_J t))) /\
  (PjTree.depth (@crt_tree_J t) <= DOC_D)%nat /\
  (* copy's free order (crt_at_W_B_copy_fo, carried to crt_at_L0_B_copy_fo) *)
  (exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (@crt_tree_J t)) /\
  YCbq.bsum (ck_hblks Dc) <= LIVE_round_trip_text t false + LIVE_round_trip_text t true +
    PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
    PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT)) /\
  ((WriterApp.w_failed st' = 0 /\ q <> 0 /\ ~ In (q, WriterApp.w_cap st') Dc /\
    Z.of_nat (length tbB) < WriterApp.w_cap st' /\ bytes_at Wc memc q (tbB ++ [0]) /\
    (* the write was granted (with g_fail_at = SIZE_MAX a failed grow is a refusal), so the room position advanced
       exactly by pj_write's events: the reading and L0's suffix are left *)
    posB Sc (evs_after_pjw ms)) \/
   (WriterApp.w_failed st' <> 0 /\ q = 0)).

(* Wr (+0x2bc = CRT_W_OFF_B, `mv s8, a0`): pj_write's return, a0 = q, and g_ran_out still 0 (no refusal, T4_GOAL_PJW) *)
Definition crt4_at_Wr (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset : Z) : Prop :=
  exists ok ranw q, crt4_wr_core fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc rg ms cset ok ranw q /\
    getr rg 10 = w64 q /\ ranw = 0.

(* S (+0x2d4 = CRT4_S_OFF_B, `mv a0, s8`): the text is in a block (q <> 0, s8 = q) and the first ran_out test read 0 *)
Definition crt4_at_S (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset : Z) : Prop :=
  exists ok q, crt4_wr_core fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc rg ms cset ok 0 q /\ q <> 0 /\
    getr rg 24 = w64 q.


(* O2 (+0x2f0 = CRT_O2_OFF_B, `lbu a0, 0x2d0(s10)`): s10 still O1's page; the L0 state (g_ran_out = 0) *)
Definition crt4_at_O2 (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset saved : Z) : Prop :=
  getr rg 26 = w64 (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B) /\
  exists Dx rc, atL0B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rc.

Definition CRT4_Wr : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc rg ms cset,
  crt4_at_Wr fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc rg ms cset ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_W_OFF_B rg memc mdc) QFb.
Definition CRT4_S : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc rg ms cset,
  crt4_at_S fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc rg ms cset ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT4_S_OFF_B rg memc mdc) QFb.
Definition CRT4_O2 : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg ms cset saved,
  crt4_at_O2 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg ms cset saved ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_O2_OFF_B rg memc mdc) QFb.

(* ======================================================================================================== *)
(* THE NAMED SECTION HYPOTHESES of the proofs below. LAWS: the allocator relation's laws (discharged at the
   instance ARcfx by lib/Reusable/YGcallcf.v AR_laws_x_xs). HPRE / HTREE: tcheck_round_trip_specX's premises at the
   entry (Crt102Top.v discharges them from the text's). *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
(* the kit's helpers that read this section's entry (Crt102KitB.v, at this section's variables and hypotheses) *)
#[local] Notation cb4_sp := (Crt102KitB.cb4_sp B ARx ly S Hp W regs mem md ch HPRE).
#[local] Notation cb4_ar0 := (Crt102KitB.cb4_ar0 B ARx ly S Hp W regs mem md ch HPRE).
#[local] Notation cb4_ff := (Crt102KitB.cb4_ff B ARx ly S Hp W regs mem md LAWS).
#[local] Notation cb4_doc_home := (Crt102KitB.cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE).
#[local] Notation cb4_chain := (Crt102KitB.cb4_chain B ARx ly S Hp W regs mem md ch HPRE).
#[local] Notation cb4_live_call := (Crt102KitB.cb4_live_call B ARx ly S Hp W regs mem md ch doc t D Lam peak most
  LAWS HPRE).
(* the kit's kb step up (kb <= kb'), read at the walk's one budget step up (crt4_lane_Wr's failed-write arm) *)
#[local] Notation cb4_live_mono := (Crt102KitB.cb4_live_mono B ARx ly S Hp W regs mem md doc t D Lam peak most).
(* the rest of tcheck_round_trip_specX's premises this row reads (PRH_FnCheck.v:927-954, the text's own) *)
Hypothesis HMN : YAkMemnorm.memnorm SEGS mem.
Hypothesis HCL : prh_univ_closure B CTX0.
Hypothesis HCTX : prh_ctx CTX0 F_check_round_trip (raZ regs :: spine ch).
Hypothesis HREAD : ck_read x = Some t.
Hypothesis HLENX : Z.of_nat (length x) <= 3 * 2 ^ 20.
Hypothesis HWL0 : PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x).
Hypothesis HWL1 : PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54.
Hypothesis HCNT : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis HLED0 : prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0.
Hypothesis HRAN : ran = 0.
Hypothesis HRQA : RQA_crt t <= most.
Hypothesis HLIVE : blocks_bytes S + LIVE_check_round_trip t <= LIVE_MAX.
Hypothesis HRQ : RQ_crt t + cf_head < cf_malloc_max.
Hypothesis HFR : Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_round_trip.
(* the text's wild room at entry (PRH_FnCheck.v:1366, kb round): read only by crt4_lane_S_at, which pays the
   parse_noting call's room out of it *)
Hypothesis HWR0 : YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_round_trip) (st_depot S).
(* THE LENGTH BOUND: the run has at most 4 calls (tcheck_round_trip_specX's own premise,
   PRH_FnCheck.v:2363, at its run binder rp_os). Read by crt4_lane_W (pj_write's text asks it of the same rp_os) and
   by crt4_lane_S_at (c4_hull_pn: parse_noting's hull budget paid from the run position) *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.
(* SRC-CEIL -> alx_blocks_ceil8 (the walk's owner's ruling at 18:15Z; owner: the allocator engine): a live allocator
   block ends at least 8 below alloc_ceiling. The allocator engine's F21b (Qed at both instances, ARcf and cgif's AR;
   the allocator engine's notes, the internal file FIELD-BATCH.md:134-137, not in this tree) lands as AR_laws_x's last field in the P''
   engine landing; this hypothesis is then discharged by citation. It paid tparse_noting_specX's src_rd clause
   `text + |tb| + 8 <= alloc_ceiling` for pj_write's buffer (q - cf_head, cap + cf_head) at +0x2e8. At the landing cut
   (7cdbb61b5fa0) src_rd asks `text + |tb| <= alloc_ceiling`, which the block bound of alx_blocks already gives, so
   NO lemma of this file uses ALX_CEIL8 any more (reported to the row owner; the hypothesis is not deleted here). *)
Hypothesis ALX_CEIL8 : forall ly' S' Hp' W' mem' md' p n, ARx ly' S' Hp' W' mem' md' ->
  In (p, n) (ablocks B ly' S') -> p + req_size n + 8 <= YM05.alloc_ceiling.
(* THE CALLEE TEXTS (owners: the contract texts' owner for the PRH_Fn* texts the base carries, as at the kit tip
   3ac20a5c9e30; the libc stdio row for the strlen wrapper's xrom statement, as for T5's astrcmp_realizes_xrom), each
   at ANY float state (a callee is entered at the float state the previous one returned in). pj_write's call is taken
   through the named goal T4_GOAL_PJW (below), which t4_goal_pjw proves from PJW. *)
Hypothesis PN : forall fxk : YK11.FPState,
  @tparse_noting_specX fxk rc ci CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0.
Hypothesis PJW : forall fxk : YK11.FPState,
  @PRH_FnWriter.tpj_write_specX fxk rc ci CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0 DOC_D.
Hypothesis FRO : forall fxk : YK11.FPState,
  @PRH_FnAlloc.tfuzz_alloc_ran_out_specX fxk rc CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK.
Hypothesis ASTRLEN : forall fxk : YK11.FPState,
  astrlen_realizes_xrom (fx := fxk) SEGS B ARx RLO RHI (SIGMA AS___wrap_strlen).

(* ---- THE WRITES OF THIS ROW'S OWN RUNS: the shadow of back and v (frame shadow bytes 4 .. 22) and the spill word
   at sp1 + 0x38 (the A' set's window sp1 + 0x38 .. sp1 + 0x60 kept) ---- *)
Definition cb4_wr (F a : Z) : Prop :=
  (shadow_addr F + 4 <= a < shadow_addr F + 23) \/ (sp1 + 56 <= a < sp1 + 96).

Lemma cb4_nw_low : forall F a, 0 <= F -> 0 <= a < kLowMemEnd -> ~ cb4_wr F a.
Proof.
intros F a HF Ha [Hw | Hw]; pose proof cb4_sp as (_ & Hc & _ & Hs1 & _); pose proof (YM05.alloc_ceiling_val);
  unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *; lia.
Qed.
Lemma cb4_nw_app : forall F a, 0 <= F -> F + 512 <= YM05.alloc_ceiling -> in_app a 1 -> a < YM05.alloc_ceiling ->
  ~ cb4_wr F a.
Proof.
intros F a HF HF2 Ha Hac [Hw | Hw]; pose proof cb4_sp as (_ & Hc & _ & Hs1 & _); pose proof (YM05.alloc_ceiling_val);
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *; lia.
Qed.
Lemma cb4_nw_stack : forall F a, 0 <= F -> F + 512 <= YM05.alloc_ceiling -> YM05.alloc_ceiling <= a ->
  ~ (sp1 + 56 <= a < sp1 + 96) -> ~ cb4_wr F a.
Proof.
intros F a HF HF2 Ha Hn [Hw | Hw]; [|exact (Hn Hw)]. pose proof (YM05.alloc_ceiling_val).
unfold shadow_addr, SHADOW_OFF in *; lia.
Qed.

Lemma cb4_pst_most : forall k, (k < pi_gz_most)%nat -> Exists (in_zr (pi_g_most + Z.of_nat k)) PST.
Proof. intros k Hk. unfold prh_pst. do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma cb4_pst_own : forall k, (k < pi_gz_own_ran_out)%nat -> Exists (in_zr (pi_g_own_ran_out + Z.of_nat k)) PST.
Proof. intros k Hk. unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.

(* ---- the live state across one of this row's own runs (its writes in cb4_wr) ---- *)
Lemma cb4_live_run : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc {kbg : nat}
    {WS : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc' mdc' kj' WS -> YCbqGwild.wbudget [] kbg WS ->
  (forall xw : word, ~ cb4_wr (frame_addr lyc CRT_CID pos) (bv_unsigned xw) ->
     mrestrict (w_H Wc) memc' xw = mrestrict (w_H Wc) memc xw) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc') ->
  liveB kbg lyc Sc Hpc Wc memc' mdc' kj' pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc kbg WS HL HJ' HB' Hag HMN'.
cb4_rd_live HL WSj HJ HBj HSD HPL HPB HAP HSV HFRM HSPF HCR HCH HMNl.
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ') as (_ & _ & _ & _ & _ & Ffr' & Fsh').
pose proof HJ as (HARc & _).
set (F := frame_addr lyc CRT_CID pos) in *.
pose proof cb4_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cb4_doc_home as (Hd1 & Hd2 & Hd3 & Hd4).
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ cb4_wr F a -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. apply aview_eq_of. apply Hag. rewrite unsigned_lit_small by lia. exact Hn. }
assert (Kmb : forall a, 0 <= a < 2 ^ 64 -> ~ cb4_wr F a ->
  mbyte SEGS (mrestrict (w_H Wc) memc') a = mbyte SEGS (mrestrict (w_H Wc) memc) a).
{ intros a Ha Hn. unfold mbyte. rewrite (Hag (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn. }
assert (Kw : forall a, 0 <= a < 2 ^ 64 -> ~ cb4_wr F a ->
  writable_at SEGS (mrestrict (w_H Wc) memc) a -> writable_at SEGS (mrestrict (w_H Wc) memc') a).
{ intros a Ha Hn Hw. unfold writable_at, wview in *. rewrite (Hag (Z_to_bv 64 a)); [exact Hw|].
  rewrite unsigned_lit_small by lia. exact Hn. }
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity.
assert (Kblk : forall a k, In (a, k) Lamc -> 0 <= k /\ forall i, 0 <= i < k + 16 ->
  0 <= a - 16 + i < 2 ^ 64 /\ ~ cb4_wr F (a - 16 + i)).
{ intros a k Hk. pose proof (crt_side_ledger HSD) as HLED.
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc a k _ _ HLED Hk) as (Hk0 & Hab & _).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & Bapp & _).
  rewrite Hch16 in *.
  assert (Hrs : k + 16 <= req_size (k + 16)) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
  split; [exact Hk0|]. intros i Hi.
  split; [lia|]. apply (cb4_nw_app F _ ltac:(lia) ltac:(lia)); [|lia].
  apply (in_app_sub _ _ _ _ Bapp); lia. }
assert (Hs2 : shadow_addr F mod 4 = 0 /\ SHADOW_OFF <= shadow_addr F /\ shadow_addr F + 64 <= SHADOW_OFF + 2 ^ 44).
{ unfold shadow_addr, SHADOW_OFF. split; lia. }
refine {| crt_live_journal := ex_intro _ WS (conj HJ' HB'); crt_live_side := _; crt_live_lam_perm := HPL;
          crt_live_blocks_perm := HPB;
          crt_live_dx_apart := HAP; crt_live_saved := _; crt_live_frame := _; crt_live_fspill := _;
          crt_live_copy_open := _; crt_live_copy_hull := _; crt_live_memnorm := HMN' |}.
{ cb4_rd_side HSD HLED HPK HRL HRO HDOC HDL.
  refine {| crt_side_ledger := _; crt_side_peak := HPK; crt_side_room := HRL; crt_side_arodata := _;
            crt_side_doc := _; crt_side_doc_blocks := HDL |}.
  { apply (prh_ledger_kept_aview B lyc Sc Hpc Wc memc lyc Sc Hpc Wc memc' Lamc peakc cntc SIZE_MAXZ ranc _ _ HLED).
    - intros a Ha. pose proof (@pa_segs_low _ _ PA a (pst_in_img_B a Ha)) as Hl. apply K; [unfold kLowMemEnd in Hl; lia|].
      apply cb4_nw_low; [lia | exact Hl].
    - intros a k i Hk Hi. destruct (Kblk a k Hk) as (Hk0 & Hb). rewrite Hch16.
      destruct (Hb i ltac:(lia)) as (H1 & H2). apply K; assumption.
    - intros a k _ Hab. exact Hab.
    - apply Permutation_refl. }
  { intros a Hro Ho He. pose proof (@pa_segs_low _ _ PA a (cb4_ro_img a Hro)) as Hl.
    rewrite K; [exact (HRO a Hro Ho He) | unfold kLowMemEnd in Hl; lia | apply cb4_nw_low; [lia | exact Hl]]. }
  apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') (prh_lin Lamc) doc D HDOC).
  intros y Hy.
  assert (Hyr : 0 <= y < 2 ^ 64 /\ ~ cb4_wr F y).
  { destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
    - split; [lia|]. apply (cb4_nw_app F y ltac:(lia) ltac:(lia)); [|lia]. apply (in_app_sub _ _ _ _ Hd3); lia.
    - unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
      destruct (Kblk b kb (HDL _ Hb)) as (Hk0 & Hbb).
      destruct (Hbb (y - (b - 16)) ltac:(lia)) as (H1 & H2).
      replace (b - 16 + (y - (b - 16))) with y in H1, H2 by lia. split; assumption. }
  split; [apply Kmb; apply Hyr | apply Kw; apply Hyr]. }
{ intros j Hj k Hk. rewrite Kmb; [exact (HSV j Hj k Hk) | lia |].
  apply (cb4_nw_stack F _ ltac:(lia) ltac:(lia)); lia. }
{ pose proof (crt_frame_flag_word HFRM) as Hfl.
  refine {| crt_frame_listed := crt_frame_listed HFRM; crt_frame_flag_word := _; crt_frame_present := _ |}.
  - rewrite <- Hfl. apply ts_rdword_keep. intros j Hj. rewrite cb4_fb.
    apply K; [lia|]. apply (cb4_nw_app F _ ltac:(lia) ltac:(lia)); [|lia]. apply (in_app_sub _ _ _ _ Fb3); lia.
  - intros a Ha. rewrite cb4_fb in Ha. exact (proj1 (Ffr' a Ha)). }
{ intros k Hk. unfold CRT_SP_F in *. rewrite Kmb; [exact (HSPF k Hk) | lia |].
  apply (cb4_nw_stack F _ ltac:(lia) ltac:(lia)); lia. }
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HCR].
  intros y Hy. unfold CRT_OFF_COPY in Hy. unfold shadow_of_addr. apply K; [unfold SHADOW_OFF; lia|].
  intros [Hw | Hw]; [|unfold SHADOW_OFF in *; pose proof (YM05.alloc_ceiling_val); lia].
  unfold shadow_addr, SHADOW_OFF in *. pose proof (Z.div_mod F 32 ltac:(lia)).
  assert (F / 8 + 28 <= y / 8) by (apply Z.div_le_lower_bound; lia). lia. }
{ intros s Hs. pose proof (YM05.alloc_ceiling_val).
  rewrite K; [exact (HCH s Hs) | unfold CRT_OFF_COPY, shadow_addr, SHADOW_OFF in *; lia |].
  intros [Hw | Hw]; unfold CRT_OFF_COPY, shadow_addr, SHADOW_OFF in *; lia. }
Qed.

(* the live state with its journal re-stated (the other fields read the same memory; was `conj HJ' (proj2 HL)`
   before the glue predicates became Records), at the same budget kbg *)
Lemma cb4_live_rejournal : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc mdc' kj' {kbg : nat}
    {WS : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc' kj' WS -> YCbqGwild.wbudget [] kbg WS ->
  liveB kbg lyc Sc Hpc Wc memc mdc' kj' pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc mdc' kj' kbg WS HL HJ' HB'.
exact {| crt_live_journal := ex_intro _ WS (conj HJ' HB'); crt_live_side := crt_live_side HL;
         crt_live_lam_perm := crt_live_lam_perm HL;
         crt_live_blocks_perm := crt_live_blocks_perm HL; crt_live_dx_apart := crt_live_dx_apart HL;
         crt_live_saved := crt_live_saved HL; crt_live_frame := crt_live_frame HL;
         crt_live_fspill := crt_live_fspill HL; crt_live_copy_open := crt_live_copy_open HL;
         crt_live_copy_hull := crt_live_copy_hull HL; crt_live_memnorm := crt_live_memnorm HL |}.
Qed.

(* ---- a byte of a live harness block, or of a tree whose blocks are harness blocks, is application memory below
   alloc_ceiling, so no run of this row writes it ---- *)
Lemma cb4_lam_app : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc a k y {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  In (a, k) Lamc -> a <= y < a + k -> 4096 <= y < YM05.alloc_ceiling /\ in_app y 1.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc a k y kbg HL Hk Hy.
destruct (crt_live_journal HL) as (? & (HARc & _) & _). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc a k _ _ HLED Hk) as (Hk0 & Hab & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & Bapp & _).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity. rewrite Hch16 in *.
assert (Hrs : k + 16 <= req_size (k + 16)) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
split; [lia|]. apply (in_app_sub _ _ _ _ Bapp); lia.
Qed.
Lemma cb4_foot_nw : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc D' p y {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (forall bk, In bk D' -> In bk Lamc) ->
  frame_addr lyc CRT_CID pos <= p -> p + 56 <= frame_addr lyc CRT_CID pos + 512 ->
  pj_footR p D' y -> 0 <= y < 2 ^ 64 /\ ~ cb4_wr (frame_addr lyc CRT_CID pos) y.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc D' p y kbg HL HD Hp1 Hp2 Hy.
destruct (crt_live_journal HL) as (WSj & HJ & HBj).
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- split; [lia|]. apply cb4_nw_app; [lia | lia | apply (in_app_sub _ _ _ _ Fb3); lia | lia].
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  destruct (cb4_lam_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ b kb y HL (HD _ Hb) Hy) as (H1 & H2).
  split; [lia|]. apply cb4_nw_app; [lia | lia | exact H2 | lia].
Qed.

(* ======================================================================================================== *)
(* SHARED CALL INFRASTRUCTURE of the W walk (every call of T4 is made at sp = s1 = CRT_sp1 with s0 = the entry sp).
   B' twins of Crt102Arms.v 97a937b1e61 (arms_dregs_pres / _eq). cb4_fregs_trans, cb4_rdword_of_val_mem,
   cb4_fpchain_keep, cb4_chain and cb4_live_call (the twins of arms_fregs_trans .. arms_chain and of Crt102Rewrite.v
   370f759b180 crt102rw_live_call) are Crt102KitB.v's. *)

(* the kept registers carry the B' register snapshot across a call (callee-saved) *)
Lemma cb4_dregs_pres : forall rg rg' F, dregsB rg F -> aregs_preserved rg rg' -> dregsB rg' F.
Proof.
intros rg rg' F HD HP.
pose proof (crt_dregs_B_bregs HD) as HB.
refine {| crt_dregs_B_bregs := {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _;
            crt_bregs_B_s1 := _; crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _;
            crt_bregs_B_s9 := _; crt_bregs_B_s11 := _ |}; crt_dregs_B_s6 := _ |}.
- rewrite (ts_ap rg rg' 2%bv HP) by ts_cs. exact (crt_bregs_B_sp HB).
- rewrite (ts_ap rg rg' 3%bv HP) by ts_cs. exact (crt_bregs_B_gp HB).
- rewrite (ts_ap rg rg' 4%bv HP) by ts_cs. exact (crt_bregs_B_tp HB).
- rewrite (ts_ap rg rg' 8%bv HP) by ts_cs. exact (crt_bregs_B_s0 HB).
- rewrite (ts_ap rg rg' 9%bv HP) by ts_cs. exact (crt_bregs_B_s1 HB).
- rewrite (ts_ap rg rg' 18%bv HP) by ts_cs. exact (crt_bregs_B_s2 HB).
- rewrite (ts_ap rg rg' 20%bv HP) by ts_cs. exact (crt_bregs_B_s4 HB).
- rewrite (ts_ap rg rg' 19%bv HP) by ts_cs. exact (crt_bregs_B_s3 HB).
- rewrite (ts_ap rg rg' 23%bv HP) by ts_cs. exact (crt_bregs_B_s7 HB).
- rewrite (ts_ap rg rg' 25%bv HP) by ts_cs. exact (crt_bregs_B_s9 HB).
- rewrite (ts_ap rg rg' 27%bv HP) by ts_cs. exact (crt_bregs_B_s11 HB).
- rewrite (ts_ap rg rg' 22%bv HP) by ts_cs. exact (crt_dregs_B_s6 HD).
Qed.
(* ... and across a run that did not write them *)
Definition CB4_DREGS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 27]%bv.
Lemma cb4_dregs_eq : forall rg rg' F, dregsB rg F -> (forall r, In r CB4_DREGS -> getr rg' r = getr rg r) ->
  dregsB rg' F.
Proof.
intros rg rg' F HD HE.
pose proof (crt_dregs_B_bregs HD) as HB. unfold CB4_DREGS in HE.
refine {| crt_dregs_B_bregs := {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _;
            crt_bregs_B_s1 := _; crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _;
            crt_bregs_B_s9 := _; crt_bregs_B_s11 := _ |}; crt_dregs_B_s6 := _ |}.
- rewrite HE by (cbn [In]; tauto). exact (crt_bregs_B_sp HB).
- rewrite HE by (cbn [In]; tauto). exact (crt_bregs_B_gp HB).
- rewrite HE by (cbn [In]; tauto). exact (crt_bregs_B_tp HB).
- rewrite HE by (cbn [In]; tauto). exact (crt_bregs_B_s0 HB).
- rewrite HE by (cbn [In]; tauto). exact (crt_bregs_B_s1 HB).
- rewrite HE by (cbn [In]; tauto). exact (crt_bregs_B_s2 HB).
- rewrite HE by (cbn [In]; tauto). exact (crt_bregs_B_s4 HB).
- rewrite HE by (cbn [In]; tauto). exact (crt_bregs_B_s3 HB).
- rewrite HE by (cbn [In]; tauto). exact (crt_bregs_B_s7 HB).
- rewrite HE by (cbn [In]; tauto). exact (crt_bregs_B_s9 HB).
- rewrite HE by (cbn [In]; tauto). exact (crt_bregs_B_s11 HB).
- rewrite HE by (cbn [In]; tauto). exact (crt_dregs_B_s6 HD).
Qed.

(* the segment environment of S10Env.v at the B instance (named, so no other PAImg instance is picked) *)
#[local] Notation TEB := (TE (L := B_prog_listing) (PA := PA)).
#[local] Notation te_curB := (te_cur (L := B_prog_listing) (PA := PA)).
(* ---- the shadow-store segment shape (X's re-poison): one region, the frame's shadow bytes 4 .. 22, no chunks
   (the shadow speed-up, a Theorem Labs lane's internal file SHADOW-SPEEDUP.md: write window only, the address an atom) ---- *)
Definition cb4_ssSH (pc : Z) : sstate := mkSS pc cur_atoms
  [YP09.mkRegion (Some (xr 18)) 4 23 4 23 []] None (mkFacts [(xr 18, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)] [] []).
Lemma cb4_SH_entry : forall (fxk : YK11.FPState) pc (Wc : world SEGS) memc rg F,
  getr rg 18 = w64 (shadow_addr F) -> 0 <= F -> F + 512 <= 2 ^ 47 ->
  (forall i, 0 <= i < 64 -> apresent (w_H Wc) memc (shadow_addr F + i)) ->
  st_ok_pi SEGS VAL (TEB regs rg []) (cb4_ssSH pc)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TEB regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk pc Wc memc rg F R18 HF0 HF HP.
set (E := TEB regs rg []).
assert (X18 : bv_unsigned (ew E (xr 18)) = shadow_addr F).
{ unfold E, xr. rewrite (te_curB regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TEB regs rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 18) (shadow_addr F)); [exact X18 | unfold shadow_addr, SHADOW_OFF; lia
    | unfold shadow_addr, SHADOW_OFF; lia | | constructor].
  intros o Ho. apply (apresent_writable SEGS). apply HP. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X18.
  split; [|exact I]. unfold shadow_addr, SHADOW_OFF. lia.
Qed.

Ltac cb4_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

(* ======================================================================================================== *)
(* X (B' +0x30c .. +0x344): the shared re-poison of back and v (f8 into the frame's shadow bytes 8 .. 10, 16 .. 22,
   4 .. 7), then the join J (+0x348). The B' twin of Crt102Rewrite.v's crt102rw_at_X. *)
Lemma crtB_T4_X : CRTB_J -> CRTB_X.
Proof.
intros HJmp fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r HX.
pose proof (crt_at_X_B_join HX) as HJB.
pose proof (crt_at_J_B_live HJB) as HL. pose proof (crt_at_J_B_frm_zero HJB) as HFZ.
pose proof (crt_at_J_B_fregs HJB) as HFK. pose proof (crt_at_J_B_bregs HJB) as HBR.
pose proof (crt_at_J_B_ret HJB) as R21. pose proof (crt_at_J_B_copy_fd HJB) as HFD.
pose proof (crt_at_J_B_r0 HJB) as Er0. pose proof (crt_at_J_B_count HJB) as HCNTJ.
cb4_rd_live HL WSJ HJ HBJ HSD HPL HPB HAP HSV HFRM HSPF HCR HCH HMNl.
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
cb4_rd_bregs HBR R2 R3 R4 R8 R9 R18 R20 R19 R23 R25 R27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cb4_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (cb4_SH_entry fxk (CRT_PC_B + CRT_X_OFF_B) Wc memc rg F R18 ltac:(lia) ltac:(lia)
  (fun i Hi => proj1 (Fsh i Hi))) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TEB regs rg [])) by apply te_env.
assert (X18 : bv_unsigned (ew (TEB regs rg []) (xr 18)) = shadow_addr F).
{ unfold xr. rewrite (te_curB regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
pose proof HMNl as HPM.
pose (RUNTO := @Crt102Kit.crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
unfold crt_cfg.
paj_run_to_tok_x_inv (RUNTO WSJ) HS HJ SHOK HPM (2 ^ 63, 2 ^ 63) (CRT_PC_B + CRT_J_OFF_B).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 18) (shadow_addr F)); [reflexivity | exact X18 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists CRT_CID, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite cb4_fb. change (512 / 8) with 64.
    fold F. lia. }
  apply awr_ok_nil. }
pmkst HS.
set (WSH := ss_mem (cb4_ssSH (CRT_PC_B + CRT_X_OFF_B))) in *.
assert (Hwr : forall a, in_wrange (TEB regs rg []) WSH a -> shadow_addr F + 4 <= a < shadow_addr F + 23).
{ intros a (rr & Hr & Ha). cbv [WSH cb4_ssSH ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ts_bv_some, X18 in Ha. lia. }
assert (Hag : forall xw : word, ~ cb4_wr F (bv_unsigned xw) ->
  mrestrict (w_H Wc) (ms_mem ms) xw = mrestrict (w_H Wc) memc xw).
{ intros xw Hn. apply HFr. intros Hw. apply Hn. left. exact (Hwr _ Hw). }
pose proof (cb4_live_run lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ pos Dc Lamc peakc cntc ownc ranc HL HJ HBJ Hag
  HPM) as HL1.
assert (KR : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) rr = getr rg rr).
{ intros rr Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [cb4_keep HS |]). destruct Hr. }
clear HF HG.
lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
  change n with (CRT_PC_B + CRT_J_OFF_B) end.
apply (HJmp fxk lyc Sc Hpc Wc (ms_mem ms) _ kj pos Lamc peakc cntc ownc ranc Dc (ms_regs ms) r).
(* copy's footprint (its node and Dc's blocks) is off the re-poison's writes, so its bytes and their writability are
   kept: this carries pj_fdR and, on J's r = 0 arm, the named tree pj_nodeR (glue f1c3354d1d8); the tblk equality,
   the depth bound and crt_pos read no memory *)
assert (HAGc : forall y, pj_footR (F + CRT_OFF_COPY) Dc y ->
  mbyte SEGS (mrestrict (w_H Wc) (ms_mem ms)) y = mbyte SEGS (mrestrict (w_H Wc) memc) y /\
  (writable_at SEGS (mrestrict (w_H Wc) memc) y -> writable_at SEGS (mrestrict (w_H Wc) (ms_mem ms)) y)).
{ intros y Hy.
  assert (HDc : forall bk, In bk Dc -> In bk Lamc).
  { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hbk. }
  destruct (cb4_foot_nw _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dc (F + CRT_OFF_COPY) y HL HDc
    ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) Hy) as (Hy1 & Hy2).
  assert (E : mrestrict (w_H Wc) (ms_mem ms) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y)).
  { apply Hag. rewrite unsigned_lit_small by lia. exact Hy2. }
  split; [unfold mbyte; rewrite E; reflexivity|].
  intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
refine {| crt_at_J_B_live := HL1; crt_at_J_B_frm_zero := HFZ; crt_at_J_B_fregs := HFK;
          crt_at_J_B_bregs := _; crt_at_J_B_ret := _; crt_at_J_B_copy_fd := _; crt_at_J_B_r0 := Er0;
          crt_at_J_B_count := _ |}.
{ refine {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _;
            crt_bregs_B_s1 := _; crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _;
            crt_bregs_B_s9 := _; crt_bregs_B_s11 := _ |}; rewrite KR by (cbv; tauto); assumption. }
{ rewrite KR by (cbv; tauto). exact R21. }
{ apply (cb4_fdR_frame SEGS DOC_D (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc)
    (F + CRT_OFF_COPY) Dc HFD).
  intros y Hy. destruct (HAGc y Hy) as (E1 & E2). split; [rewrite E1; reflexivity | exact E2]. }
destruct HCNTJ as (cset & Hc1 & Hc2 & [R1 | (R0a & R0b & R0c & R0d & Hpos & Hnode & Htblk & HFo & Hdep)]).
- exists cset. split; [exact Hc1|]. split; [exact Hc2|]. left. exact R1.
- exists cset. split; [exact Hc1|]. split; [exact Hc2|]. right.
  split; [exact R0a|]. split; [exact R0b|]. split; [exact R0c|]. split; [exact R0d|]. split; [exact Hpos|].
  split.
  { apply (pj_nodeR_frame SEGS _ (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc)
      (F + CRT_OFF_COPY) Dc Hnode).
    intros y Hy. destruct (HAGc y Hy) as (E1 & E2). split; [rewrite E1; reflexivity | exact E2]. }
  split; [exact Htblk|]. split; [|exact Hdep].
  destruct HFo as (Fc & HFc & EFc). exists Fc. split; [|exact EFc].
  eapply PRH_PjOrder.pj_foR_frame; [exact HFc | |].
  + intros a k Hak. eapply PRH_PjOrder.pj_foR_lblk; [exact HFc | exact Hak].
  + intros y Hy. destruct (HAGc y Hy) as (E1 & E2). split; [rewrite E1; reflexivity | exact E2].
Qed.

(* ======== PART A of this row (Crt102B_T4A.v, merged into this file) ======== *)

(* ======================================================================================================== *)
(* PART A (row T4): W (+0x2a4) -> pj_write (&copy, 1) -> Wr (+0x2bc).                                      *)

(* ---- the writer run of pj_write (&copy, 1), this part's own facts over the pure model: a run that ENDS UNFAILED
   had every outcome of its fuzz_realloc calls accepting (so it was granted: PRH_Base.prh_granted holds vacuously),
   and a run from g_fail_at = SIZE_MAX keeps g_fail_at = SIZE_MAX (put1's chosen failure resets it to SIZE_MAX) ---- *)
Lemma cb4w_wput_ok : forall P ok st, WriterApp.w_failed st = 0 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok st P) = 0 ->
  forall i, (i < PRH_FnWriter.prhWriter_k ok st P)%nat -> nth i ok true = true.
Proof.
induction P as [|b P IH]; intros ok st Hf Hend i Hi.
- unfold PRH_FnWriter.prhWriter_k in Hi. cbn [PRH_FnWriter.prhWriter_putN] in Hi. lia.
- rewrite PRH_Supply.prhWriter_k_cons in Hi. cbn [PRH_FnWriter.prhWriter_putN] in Hend.
  revert Hi Hend. destruct (PRH_FnWriter.prhWriter_grows st b) eqn:G; cbv beta iota.
  + destruct (WriterApp.w_cnt st =? WriterApp.w_fail st) eqn:E.
    * intros _ Hend. exfalso.
      assert (Hf1 : WriterApp.w_failed (PRH_FnWriter.prhWriter_put1 (hd true ok) st b) <> 0).
      { unfold PRH_FnWriter.prhWriter_put1. rewrite G, E. cbn [WriterApp.w_failed]. lia. }
      rewrite (PRH_Supply.sup_putN_failed _ _ _ Hf1) in Hend. exact (Hf1 Hend).
    * destruct (hd true ok) eqn:Hh; intros Hi Hend.
      -- destruct i as [|i].
         ++ rewrite cm_nth_hd. exact Hh.
         ++ rewrite cm_nth_tl. apply (IH (tl ok) (PRH_FnWriter.prhWriter_put1 true st b)); [| exact Hend | lia].
            unfold PRH_FnWriter.prhWriter_put1. rewrite G, E. reflexivity.
      -- exfalso.
         assert (Hf1 : WriterApp.w_failed (PRH_FnWriter.prhWriter_put1 false st b) <> 0).
         { unfold PRH_FnWriter.prhWriter_put1. rewrite G, E. cbn [WriterApp.w_failed]. lia. }
         rewrite (PRH_Supply.sup_putN_failed _ _ _ Hf1) in Hend. exact (Hf1 Hend).
  + intros Hi Hend. apply (IH ok (WriterApp.put1 st b)); [| exact Hend | exact Hi].
    unfold PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need in G. rewrite Hf in G.
    cbn [Z.eqb andb] in G. apply Z.ltb_ge in G.
    unfold WriterApp.put1. rewrite Hf. cbn [Z.eqb negb]. rewrite (proj2 (Z.leb_le _ _) G). reflexivity.
Qed.

(* ---- no refused call among the k (prh_granted): prh_oks leaves g_ran_out as it was ---- *)
Lemma cb4w_granted_ran : forall ok c0 f0 k ns mo r0 r1,
  prh_oks ok c0 f0 k ns mo r0 r1 -> PRH_Base.prh_granted ok c0 f0 k -> r1 = r0.
Proof.
intros ok c0 f0 k ns mo r0 r1 (_ & [E | (_ & i & Hi & Hr & _)] & _) HG; [exact E|].
exfalso. unfold prh_refused in Hr. apply andb_prop in Hr as [H1 H2].
apply negb_true_iff in H1. apply negb_true_iff, Z.eqb_neq in H2.
exact (H2 (HG i Hi H1)).
Qed.

Lemma cb4w_wput_failmax : forall P ok st, WriterApp.w_fail st = 2 ^ 64 - 1 ->
  WriterApp.w_fail (PRH_FnWriter.prhWriter_putN ok st P) = 2 ^ 64 - 1.
Proof.
induction P as [|b P IH]; intros ok st H; cbn [PRH_FnWriter.prhWriter_putN]; [exact H|].
destruct (PRH_FnWriter.prhWriter_grows st b) eqn:G; apply IH.
- unfold PRH_FnWriter.prhWriter_put1. rewrite G. cbv beta iota zeta.
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [reflexivity|]. destruct (hd true ok); exact H.
- destruct (PRH_Supply.sup_put1_keep st b G) as (_ & _ & K). rewrite K. exact H.
Qed.

(* ---- the writer's tree visibility survives a run that keeps every byte below alloc_ceiling (a block's bytes, its
   granule and its shadow all lie there) ---- *)
Lemma cb4w_tv_keep : forall (Wx : world SEGS) m m' Dt,
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a) ->
  PRH_FnWriter.prhWriter_tree_vis Wx m Dt -> PRH_FnWriter.prhWriter_tree_vis Wx m' Dt.
Proof.
intros Wx m m' Dt K HT a k Hin.
destruct (HT a k Hin) as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
pose proof asan_consts as (C1 & _).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split.
{ apply (range_addressable_agree (aview SEGS (w_H Wx) m)); [|exact H5].
  intros y Hy. unfold shadow_of_addr. apply K. unfold SHADOW_OFF. lia. }
split.
{ intros Hk s Hs. rewrite K; [exact (H6 Hk s Hs)|]. unfold shadow_addr, SHADOW_OFF in Hs. lia. }
intros y Hy. rewrite K; [exact (H7 y Hy) | lia].
Qed.

(* ---- the document's home keeps its 56 addressable bytes at every state the journal from the entry reaches
   (Crt102Arms.v 97a937b1e61 arms_home_keep, :476-504, at B') ---- *)
Lemma cb4w_home_keep : forall own lyc Sc Hpc Wc memc mdc kj {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kj WS -> ck_obj_home lyc Sc Wc memc doc.
Proof.
intros own lyc Sc Hpc Wc memc mdc kj WS HJ.
pose proof HPRE as ((HAR & _) & _).
pose proof HTREE as (_ & _ & _ & Hd8 & (cid & pos & Hfin & Hfa1 & Hfa2) & HRA).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR Hly) as (_ & Efa & _).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfin) as (F32 & _).
split; [exact Hd8|]. split.
- exists cid, pos. rewrite Efa. split; [rewrite Hfrs; apply in_or_app; right; exact Hfin|]. split; lia.
- intros a Ha. destruct (HRA a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr. apply (F4 cid pos); [exact Hfin | right | apply inFP_nil].
  unfold in_zr, shadow_addr. cbn [fst snd].
  assert (E8 : (frame_addr ly cid pos + fs_frame_bytes cid) / 8 = frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8).
  { apply Z.mod_divide in F32; [|lia]. destruct F32 as [q Hq]. rewrite Hq.
    replace (q * 32 + fs_frame_bytes cid) with (fs_frame_bytes cid + (4 * q) * 8) by lia. rewrite Z.div_add by lia.
    replace (q * 32) with ((4 * q) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (Hd : (doc + 56) / 8 = doc / 8 + 7).
  { apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 56) with ((q + 7) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
  pose proof (Z.div_le_mono (frame_addr ly cid pos) a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono a (doc + 55) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (doc + 56) (frame_addr ly cid pos + fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)).
  assert ((doc + 55) / 8 = doc / 8 + 6).
  { apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 55) with (7 + (q + 6) * 8) by lia. rewrite Z.div_add by lia. rewrite Z.div_mul by lia. cbn. lia. }
  lia.
Qed.

(* ---- the read-only view across a call with an empty footprint (the journal's image clause; alloc.c's statics
   are not read-only, S1ImgB.v pst_not_ro_B) ---- *)
Lemma cb4w_ro_call : forall STK1 sp' lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 {WS1 : list (list Z)},
  AJW STK1 sp' [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memc) -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H W2) mem2).
Proof.
intros STK1 sp' lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS1 HJ1 HRO a Hro Hno Her.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _).
rewrite (G3 a); [exact (HRO a Hro Hno Her) | exact (cb4_ro_img a Hro) | exact Hno | exact Her
  | exact (fun Hx => pst_not_ro_B a Hx Hro) | apply fp_spares_closed; exact sink_closed_nil].
Qed.

(* ---- the document's tree across a call with an empty footprint: its root in a fake frame of the entry (the frame
   clause), its blocks harness blocks live at both ends (the block clause) ---- *)
Lemma cb4w_doc_call : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 sp' ly2 S2 Hp2 W2 mem2
    md2 k1 Lam2 {kbg : nat} {WS1 : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STK1 sp' [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall bk, In bk Lamc -> In bk Lam2) ->
  (forall a k, In (a, k) Lamc -> In (a - cf_head, k + cf_head) (ablocks B ly2 S2)) ->
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) doc t D /\ (forall bk, In bk D -> In bk Lam2).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 sp' ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 kbg WS1
  HL HJ1 HLam HAB.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_doc HSD) as HND.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
pose proof HJ1 as (HAR2 & HLY1 & _ & _ & _ & HFR1 & _ & _ & _ & G2 & _ & G4 & _).
pose proof HPRE as ((HAR & _) & _).
pose proof HTREE as (_ & _ & _ & _ & (cid & pos' & Hfin & Hfa1 & Hfa2) & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR HLYc) as (_ & Efa0 & _).
destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc ly2 HARc HLY1) as (_ & Efa1 & _).
assert (Hfin1 : In (cid, pos') (frames Sc)) by (rewrite HFRc; apply in_or_app; right; exact Hfin).
assert (Hfin2 : In (cid, pos') (frames S2)) by (rewrite HFR1; exact Hfin1).
destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos' HAR2 Hfin2) as (_ & _ & Ffr2 & _).
pose proof (Efa0 cid pos') as E0. pose proof (Efa1 cid pos') as E1.
assert (Hh16 : @cf_head CfParams_preset = 16) by reflexivity.
split; [| intros bk Hbk; apply HLam; apply HDL; exact Hbk].
apply (cb4_nodeR_lblk SEGS t _ (prh_lin Lamc)); [| intros a k Hk; apply HLam; apply HDL; exact Hk].
apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) memc) _ (prh_lin Lamc) doc D HND).
intros y Hy. destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- split.
  + apply (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2). apply (G4 cid pos' y Hfin1); [|apply inFP_nil].
    left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
  + intros _. apply apresent_writable. exact (proj1 (Ffr2 y ltac:(lia))).
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDL _ Hb))
    as (Hk0 & Hab1 & _).
  pose proof (HAB b kb (HDL _ Hb)) as Hab2.
  rewrite Hh16 in Hab1, Hab2.
  assert (Hrq : req_size (kb + 16) = kb + 16) by (unfold req_size; destruct (Z.eqb_spec (kb + 16) 0); lia).
  split.
  + apply (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2).
    replace y with ((b - 16) + (y - b + 16)) by lia. apply (G2 _ _ _ Hab1 Hab2); [rewrite Hrq; lia | apply inFP_nil].
  + intros _. apply apresent_writable.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hpres & _).
    rewrite Hrq in Hpres. exact (proj1 (Hpres y ltac:(lia))).
Qed.

(* ---- a tree's FREE ORDER across a call with an empty footprint: its header in the class-3 frame, its blocks
   harness blocks live at both ends (copy's, carried from crt_at_W_B_copy_fo to crt_at_L0_B_copy_fo) ---- *)
Lemma cb4w_foR_call : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 sp' ly2 S2 Hp2 W2 mem2
    md2 k1 Lam2 (D' : list (Z * Z)) p d F' {kbg : nat} {WS1 : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STK1 sp' [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  frame_addr lyc CRT_CID pos <= p -> p + 56 <= frame_addr lyc CRT_CID pos + fs_frame_bytes CRT_CID ->
  (forall bk, In bk D' -> In bk Lamc) -> (forall bk, In bk D' -> In bk Lam2) ->
  (forall a k, In (a, k) D' -> In (a - cf_head, k + cf_head) (ablocks B ly2 S2)) ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) d p D' F' ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) d p D' F'.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 sp' ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 D' p d F'
  kbg WS1 HL HJ1 Hp1 Hp2' HDL HLam HAB HFo.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
pose proof HJ1 as (HAR2 & HLY1 & _ & _ & _ & HFR1 & _ & _ & _ & G2 & _ & G4 & _).
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ) as (Hin & _).
assert (Hfin2 : In (CRT_CID, pos) (frames S2)) by (rewrite HFR1; exact Hin).
destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 CRT_CID pos HAR2 Hfin2) as (_ & _ & Ffr2 & _).
destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc ly2 HARc HLY1) as (_ & Efa1 & _).
pose proof (Efa1 CRT_CID pos) as E1.
assert (Hh16 : @cf_head CfParams_preset = 16) by reflexivity.
eapply PRH_PjOrder.pj_foR_frame; [exact HFo | intros a k Hak; exact (HLam _ Hak) |].
intros y Hy. destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- split.
  + apply (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2). apply (G4 CRT_CID pos y Hin); [|apply inFP_nil].
    left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
  + intros _. apply apresent_writable. exact (proj1 (Ffr2 y ltac:(lia))).
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDL _ Hb))
    as (Hk0 & Hab1 & _).
  pose proof (HAB b kb Hb) as Hab2.
  rewrite Hh16 in Hab1, Hab2.
  assert (Hrq : req_size (kb + 16) = kb + 16) by (unfold req_size; destruct (Z.eqb_spec (kb + 16) 0); lia).
  split.
  + apply (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2).
    replace y with ((b - 16) + (y - b + 16)) by lia. apply (G2 _ _ _ Hab1 Hab2); [rewrite Hrq; lia | apply inFP_nil].
  + intros _. apply apresent_writable.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hpres & _).
    rewrite Hrq in Hpres. exact (proj1 (Hpres y ltac:(lia))).
Qed.

(* ---- the run W (+0x2a4 .. +0x2b8): one region, the spill word 0x38(s1) of &back ---- *)
Definition cb4w_ssW : sstate := mkSS (CRT_PC_B + CRT_W0_OFF_B) cur_atoms
  [YP09.mkRegion (Some (xr 9)) 56 64 56 64 []] None (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Lemma cb4w_stkw : @STK_pj_write prh_img_B DOC_D = 23360.
Proof. vm_compute. reflexivity. Qed.
Lemma cb4w_ret : 4096 <= BASE + (CRT_PC_B + CRT_W_OFF_B) < 2 ^ 31 /\ (CRT_PC_B + CRT_W_OFF_B) mod 2 = 0 /\
  0 <= CRT_PC_B + CRT_W_OFF_B < 2 ^ 40.
Proof.
(split; [split; vm_compute; first [discriminate | reflexivity]|]); (split; [vm_compute; reflexivity|]);
  split; vm_compute; first [discriminate | reflexivity].
Qed.

(* ======================================================================================================== *)
(* THE pj_write CALL OF THIS SEGMENT WITH ITS REFUSAL ARM DEAD, AS ONE NAMED GOAL (`T4_GOAL_PJW`).
   It is tpj_write_specX (PRH_FnWriter.v:773 at this head) at depth DOC_D, premise for premise and conjunct for
   conjunct, read at a run whose strtod model is a binder rsm with the premise rsm = ReaderRes.jr_strtod (the text
   writes ReaderRes.jr_strtod itself): the entry premise prh_cons_from over pj_write's own window and the post
   conjunct prh_granted - the dead refusal arm DEAD-PJWRITE (no grow refused; the chosen failure is still
   allowed). It closes (t4_goal_pjw) by ONE application of that text after `subst rsm`. T4 uses only prh_granted,
   through cb4w_granted_ran: pj_write leaves g_ran_out at 0, so the FF block is not entered from Wr; the failed arm
   q = 0, if a caller keeps it, goes to L0's saved = 0 arm. On the Step-1 text: the text's run
   length bound `(length ros <= 4)%nat` in its place (after the position; crt4_lane_W gives HOS4) and its post at
   YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (fpostFm is at wle'). *)
Definition T4_GOAL_PJW : Prop :=
  forall (fxk : YK11.FPState) (rsm : list Z -> Z * Z) (rx : list Z) (ros : list (option nat * option nat * option nat))
    (ri : nat) (rH0 : list Z) (rhist : list YG00.chunk) (mo ow : Z),
  forall lyw Sw Hpw (Ww : world SEGS) rgw mmw mdw chw v pretty (tw : PjTree.jv) Dw Lw pkw cw fw rw,
  fpre B ARx (@STK_pj_write prh_img_B DOC_D) lyw Sw Hpw Ww rgw mmw mdw chw ->
  prh_univ_closure B CTX0 ->
  room_live_cf Sw -> PresetRoomPos.iface_room_pos rsm rx ros ri rH0 rhist Sw ->
  (length ros <= 4)%nat ->
  rsm = ReaderRes.jr_strtod ->
  PRH_Base.prh_cons_from rsm rx ros ri
    (length (PRH_FnWriter.prhWriter_pjw_evs [] cw fw (WriterValue.wdpieces tw (negb (pretty =? 0))))) ->
  getr rgw 10 = w64 v -> getr rgw 11 = w64 pretty -> 0 <= pretty < 2 ^ 31 ->
  prh_ledger B lyw Sw Hpw Ww mmw Lw pkw cw fw rw mo ow ->
  prh_run_at rsm rx ros ri (PRH_FnWriter.prhWriter_pjw_evs [] cw fw (WriterValue.wdpieces tw (negb (pretty =? 0)))) ->
  pj_nodeR SEGS (mrestrict (w_H Ww) mmw) (prh_lin Lw) v tw Dw ->
  ((spZ rgw <= v /\ v + 56 <= ly_stk_hi lyw) \/ (exists x0 y0, In (x0, y0) Lw /\ x0 <= v /\ v + 56 <= x0 + y0) \/
   PRH_FnWriter.prhWriter_in_frame lyw Sw v) ->
  range_addressable (aview SEGS (w_H Ww) mmw) SHADOW_OFF v 56 ->
  PRH_FnWriter.prhWriter_tree_vis Ww mmw Dw ->
  (forall a k, In (a, k) Dw -> In (a, k) Lw) ->
  (PjTree.depth tw <= DOC_D)%nat -> Z.of_nat (PjTree.depth tw) <= 2 ^ 31 - 1 ->
  Z.of_nat (length (frames Sw)) < fs_frames 0 ->
  Z.of_nat (length (WriterValue.wdoc tw (negb (pretty =? 0)))) + 1 <= PRH_FnWriter.prhWriter_WMAX ->
  PRH_FnWriter.prhWriter_WMAX + cf_head < cf_malloc_max ->
  blocks_bytes Sw + PRH_FnWriter.LIVE_pj_write tw (negb (pretty =? 0)) <= LIVE_MAX ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Ww
    (mkCfg (@YK11.mkst fxk rgw (Z_to_bv 64 (SIGMA AS_pj_write)) mmw (YK11.seg_rom SEGS)) mdw)
    (@fpostFm fxk rc prh_img_B B_prog_listing PA B ARx SK (@STK_pj_write prh_img_B DOC_D) [] rgw lyw Sw Hpw Ww mmw mdw
      (fun ly' S' Hp' W' regs' mem' md' =>
       exists ok ran' q Lam' peak',
       let P := WriterValue.wdpieces tw (negb (pretty =? 0)) in
       let st' := PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cw fw) P in
       prh_oks ok cw fw (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cw fw) P)
         (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 cw fw) P) mo rw ran' /\
       getr regs' 10 = w64 q /\
       room_live_cf S' /\
       (* DEAD-PJWRITE *)
       PRH_Base.prh_granted ok cw fw (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cw fw) P) /\
       (PRH_Base.prh_granted ok cw fw (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cw fw) P) ->
          exists hist', PresetRoomPos.iface_room_pos rsm rx ros
            (ri + length (PRH_FnWriter.prhWriter_pjw_evs ok cw fw P))%nat rH0 hist' S') /\
       pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lw) v tw Dw /\
       PRH_FnWriter.prhWriter_tree_vis W' mem' Dw /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt st') (WriterApp.w_fail st') ran' mo ow /\
       ((WriterApp.w_failed st' = 0 /\ q <> 0 /\ ~ In (q - cf_head, WriterApp.w_cap st' + cf_head) (ablocks B lyw Sw) /\
         Lam' = (q, WriterApp.w_cap st') :: Lw /\ peak' = Z.max pkw (Ledger.lsum Lw + WriterApp.w_cap st') /\
         Permutation (ablocks B ly' S') ((q - cf_head, WriterApp.w_cap st' + cf_head) :: ablocks B lyw Sw) /\
         Z.of_nat (length (WriterValue.wdoc tw (negb (pretty =? 0)))) < WriterApp.w_cap st' /\
         bytes_at W' mem' q (WriterValue.wdoc tw (negb (pretty =? 0)) ++ [0]))
        \/
        (WriterApp.w_failed st' <> 0 /\ q = 0 /\ Lam' = Lw /\ Permutation (ablocks B ly' S') (ablocks B lyw Sw) /\
         ((WriterApp.w_cap st' = 0 /\ peak' = Z.max pkw (PRH_FnWriter.prhWriter_rpeak ok Lw (WriterApp.w0 cw fw) P)) \/
          (WriterApp.w_cap st' <> 0 /\
           peak' = Z.max (Z.max pkw (Ledger.lsum Lw + WriterApp.w_cap st'))
             (PRH_FnWriter.prhWriter_rpeak ok Lw (WriterApp.w0 cw fw) P))))))).

Lemma t4_goal_pjw : T4_GOAL_PJW.
Proof.
intros fxk rsm rx ros ri rH0 rhist mo ow lyw Sw Hpw Ww rgw mmw mdw chw v pretty tw Dw Lw pkw cw fw rw
  Hpre Hcl Hrl Hpos Hos Esm.
subst rsm.
exact (PJW fxk rx ros ri rH0 rhist mo ow lyw Sw Hpw Ww rgw mmw mdw chw v pretty tw Dw Lw pkw cw fw rw
  Hpre Hcl Hrl Hpos Hos).
Qed.

(* ---- PART A: from W (crt_at_W_B) to Wr (crt4_at_Wr), the pj_write call through T4_GOAL_PJW. ---- *)
Lemma crt4_lane_W : T4_GOAL_PJW -> CRT4_Wr -> CRTB_W.
Proof.
intros GPJW HWr fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg mso cset HW.
pose proof (crt_at_W_B_obj HW) as Ems. pose proof (crt_at_W_B_frm_zero HW) as HFZ.
pose proof (crt_at_W_B_fregs HW) as HFK. pose proof (crt_at_W_B_live HW) as HL.
pose proof (crt_at_W_B_dregs HW) as HDR. pose proof (crt_at_W_B_s5 HW) as R21.
pose proof (crt_at_W_B_s10_own HW) as R26. pose proof (crt_at_W_B_sp_shn HW) as SSHN.
pose proof (crt_at_W_B_sp_pn HW) as SPN. pose proof (crt_at_W_B_sp_n HW) as SN.
pose proof (crt_at_W_B_doc_align HW) as Hd8. pose proof (crt_at_W_B_doc_open HW) as HRAd.
pose proof (crt_at_W_B_back_open HW) as HRAb. pose proof (crt_at_W_B_v_open HW) as HRAv.
pose proof (crt_at_W_B_cset_range HW) as Hcs. pose proof (crt_at_W_B_cset_mod HW) as Hmod.
pose proof (crt_at_W_B_cnt HW) as Ecnt. pose proof (crt_at_W_B_copy HW) as HCT.
pose proof (crt_at_W_B_tree_vis HW) as HTV. pose proof (crt_at_W_B_live_bound HW) as HBS.
pose proof (crt_at_W_B_pos HW) as HPOS. pose proof (crt_at_W_B_copy_tblk HW) as HCPw.
pose proof (crt_at_W_B_copy_fo HW) as HFOw. pose proof (crt_at_W_B_copy_depth HW) as HDPw.
clear HW. subst cntc.
cb4_rd_live HL WS0 HJ0 HB0 HSD HPm HPab HDap HSV HFRM HSPF HCR HCH HMNl.
cb4_rd_side HSD HLED Hpk HROOM HRO HND HDL.
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ0) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
cb4_rd_dregs HDR R2 R3 R4 R8 R9 R18 R20 R19 R23 R25 R27 R22.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cb4_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof cb4_stkc as HSTKC. pose proof cb4w_stkw as HSTKW.
pose proof cb4w_ret as (Hr1 & Hr2 & Hr3).
pose proof HJ0 as (HARc & HLYc & _ & _ & _ & HFRc & _ & _ & _ & _ & _ & _ & _ & HPRc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac & Hfz0).
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran _ _ HLED0) as (_ & _ & Hcnt0 & _).
(* THE POSITION at W: pj_write's events are the head of crt_evs_W *)
pose proof (crt_pos_strtod HPOS) as Esm. destruct (crt_pos_ex HPOS) as (pre & hist & HA).
pose proof (crt_pos_split HA) as Ert. pose proof (crt_pos_room HA) as HRP. pose proof (crt_pos_run HA) as HRUN.
pose proof (crt_pos_cons HA) as HCF.
unfold crt_evs_W in Ert, HRUN, HCF. apply prh_run_at_app_iff in HRUN as [HRUNw HRUNr].
rewrite length_app in HCF. apply PRH_Base.prh_cons_from_app_iff in HCF as [HCFw HCFr].
assert (Etc : tcB = PresetReqAt.copy_set mso) by (unfold crt_tc; rewrite Ems; reflexivity).
destruct (cm_cnt_write x t mso cset cnt HIN Ems Hcs ltac:(lia)) as (Hc0 & Hc1). rewrite cm_cnt2_eq in Hc0, Hc1.
assert (Hcw : cwB cset = cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
  PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t) + 1 + cset) by reflexivity.
assert (Hwc : Z.of_nat (PresetReqAt.wcalls (PresetReqAt.copy_set mso) true) =
  PjWriteHyp.wcalls (ck_crt_tree t) true) by (rewrite Ems; reflexivity).
assert (Hpjw0 : PRH_FnWriter.prhWriter_pjw_evs [] (cwB cset) SIZE_MAXZ (WriterValue.wdpieces tcB true) =
  PresetReqAt.w_evs (PresetReqAt.copy_set mso) true).
{ rewrite Etc. apply PRH_Supply.prhWriter_pjw_evs_w_evs; [reflexivity | lia |].
  intros j Hj. unfold SIZE_MAXZ. rewrite Z.mod_small by lia. lia. }
(* T4_GOAL_PJW's run hypothesis over pj_write's own window (crt_pos's prh_cons_from, split at the writer's events) *)
assert (HCFW : PRH_Base.prh_cons_from rp_sm rp_x rp_os (rp_i + length pre)%nat
  (length (PRH_FnWriter.prhWriter_pjw_evs [] (cwB cset) SIZE_MAXZ (WriterValue.wdpieces tcB true)))).
{ rewrite Hpjw0. exact HCFw. }
assert (HRUNW : prh_run_at rp_sm rp_x rp_os (rp_i + length pre)
  (PRH_FnWriter.prhWriter_pjw_evs [] (cwB cset) SIZE_MAXZ (WriterValue.wdpieces tcB true))).
{ rewrite Hpjw0. exact HRUNw. }
(* THE SEAT at +0x2a4 *)
assert (X9 : bv_unsigned (ew (TEB regs rg []) (xr 9)) = sp1).
{ unfold xr. rewrite (te_curB regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X19 : bv_unsigned (ew (TEB regs rg []) 51) = frame_addr lyc CRT_CID pos).
{ change 51%nat with (32 + 19)%nat. rewrite (te_curB regs rg _ 19%bv 19) by reflexivity. rewrite R19.
  apply unsigned_lit_small. lia. }
assert (HS : st_ok_pi SEGS VAL (TEB regs rg []) cb4w_ssW
  (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_W0_OFF_B))) memc (YK11.seg_rom SEGS)))).
{ apply ts_st_ok.
  - apply te_regs_ok.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (ts_rok _ _ (xr 9) sp1); [exact X9 | lia | lia | | constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HPRc. rewrite HSTKC. lia.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9.
    change (2 ^ 5) with 32. repeat split; lia. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TEB regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TEB regs rg [])) by apply te_env.
pose proof HMNl as HPM. pose proof HJ0 as HJ.
pose (RUN := @Crt102Kit.crt_run_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
unfold crt_cfg.
paj_run_tok_x_inv (RUN WS0) HS HJ SHOK HPM (0, 0).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - sp0)); [reflexivity | | | |].
  - rewrite X9. lia.
  - cbn [YP09.r_wlo]. rewrite HSTKC. lia.
  - cbn [YP09.r_whi]. lia.
  - apply awr_ok_nil. }
(* the run's memory: the spill it wrote, and everything else kept *)
pose proof (ts_region_nth_c _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
assert (VSP : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (sp1 + 56) 8
  (frame_addr lyc CRT_CID pos + CRT_OFF_BACK)).
{ pose proof (ts_field _ _ (xr 9) sp1 _ _ _ _ _ 56 8 (SOff 51 32) HR0 X9
    ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as V.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V. change (N.to_nat 8) with 8%nat in V.
  rewrite U_SOff, X19, YP0m.zcanon_small in V by lia. rewrite Z.mod_small in V by lia.
  unfold CRT_OFF_BACK. exact V. }
assert (Hwr : forall a, in_wrange (TEB regs rg []) (ss_mem cb4w_ssW) a -> sp1 + 56 <= a < sp1 + 64).
{ intros a (rr & Hr & Ha). cbv [cb4w_ssW ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ts_bv_some, X9 in Ha. lia. }
assert (Hag : forall xw : word, ~ cb4_wr (frame_addr lyc CRT_CID pos) (bv_unsigned xw) ->
  mrestrict (w_H Wc) (ms_mem ms) xw = mrestrict (w_H Wc) memc xw).
{ intros xw Hn. apply HFr. intros Hw. apply Hn. right. pose proof (Hwr _ Hw). lia. }
pose proof (cb4_live_run lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ pos Dc Lamc peakc (cwB cset) 0 0 HL HJ HB0 Hag
  HPM) as HL1.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 56 <= a < sp1 + 64) ->
  aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. exact (ts_keep Wc _ (ss_mem cb4w_ssW) memc (ms_mem ms) _ HFr Hwr a Ha Hn). }
(* the run's registers: a0 = &copy, a1 = 1, s5 = 1, ra = +0x2bc, the snapshot kept *)
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (21%bv : bv 5) Q21. prreg HS (1%bv : bv 5) Q1.
assert (X10 : getr (ms_regs ms) 10 = w64 (frame_addr lyc CRT_CID pos + CRT_OFF_COPY)) by (rewrite Q10, <- R20; te_close).
assert (X11 : getr (ms_regs ms) 11 = w64 1) by (rewrite Q11; reflexivity).
assert (X21 : getr (ms_regs ms) 21 = w64 1) by (rewrite Q21; reflexivity).
assert (X1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + CRT_W_OFF_B))) by (rewrite Q1; vm_compute; reflexivity).
assert (HDR1 : dregsB (ms_regs ms) (frame_addr lyc CRT_CID pos)).
{ apply (cb4_dregs_eq rg); [exact HDR|]. intros r Hr. unfold CB4_DREGS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [cb4_keep HS|]); destruct Hr. }
assert (X26 : getr (ms_regs ms) 26 = getr rg 26) by cb4_keep HS.
rewrite R26 in X26.
cb4_rd_dregs HDR1 R2' R3' R4' R8' R9' R18' R20' R19' R23' R25' R27' R22'.
cb4_rd_live HL1 WSx HJx HBx HSD1 HPm1 HPab1 HDap1 HSV1 HFRM1 HSPF1 HCR1 HCH1 HMN1.
pose proof (crt_side_ledger HSD1) as HLED1. pose proof (crt_side_room HSD1) as HROOM1.
pose proof (crt_side_arodata HSD1) as HRO1. pose proof (crt_side_doc HSD1) as HND1.
pose proof (crt_side_doc_blocks HSD1) as HDL1.
destruct (cb4_chain _ _ _ _ _ _ _ _ HJ HSV1) as (ch1 & Hch1 & Ech1).
assert (Hspz : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite R2'; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0z : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8'. unfold w64. apply unsigned_lit_small.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (HE2 : bv_unsigned (ew (TEB regs rg []) 2) = sp0)
  by (rewrite (te_entry regs rg [] 2%bv 2) by reflexivity; reflexivity).
assert (Hspc : getr (ms_regs ms) 2 = sv_denot (TEB regs rg []) (SOff 2 (sp1 - sp0))).
{ apply bv_eq. rewrite denot_SOff, HE2, R2'. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite YP0m.zcanon_small by lia. lia. }
(* pj_write's model premises, from the text's own (Crt102Model.v) *)
assert (Hdep : (PjTree.depth tcB <= DOC_D)%nat) by exact (cm_crt_depth_doc t (cm_in_depth x t HIN)).
assert (Hdep31 : Z.of_nat (PjTree.depth tcB) <= 2 ^ 31 - 1).
{ pose proof Hdep as Hd. apply Nat2Z.inj_le in Hd. assert (Z.of_nat DOC_D = 33) by reflexivity. lia. }
destruct (cm_in_wlen_crt x t HIN) as (_ & Hwl & _).
pose proof (cm_rq_wmax t HRQ) as Hwmax.
assert (Hbb : blocks_bytes Sc <= blocks_bytes S + LIVE_round_trip_text t false + LIVE_round_trip_text t true +
  PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
  PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT))).
{ rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (YCbq.bsum_perm _ _ HPab), YCbq.bsum_app. lia. }
pose proof (cm_live_write t (blocks_bytes S) (blocks_bytes Sc) HLIVE Hbb) as Hlive.
assert (Hfr0 : Z.of_nat (length (frames Sc)) < fs_frames 0).
{ rewrite HFRc. cbn [app length]. refine (proj1 (cm_frames_fs0 _ _)).
  pose proof (cm_frames_before (length (frames S)) HFR) as Hb.
  unfold FR_round_trip_text, FR_pj_parse in Hb. assert (Z.of_nat DOC_D = 33) by reflexivity. lia. }
assert (HTV1 : PRH_FnWriter.prhWriter_tree_vis Wc (ms_mem ms) Dc).
{ apply (cb4w_tv_keep Wc memc (ms_mem ms) Dc); [|exact HTV]. intros a Ha. apply K; lia. }
assert (HDc : forall a k, In (a, k) Dc -> In (a, k) Lamc).
{ intros a k Hk. apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. left. exact Hk. }
assert (HDcb : forall bk, In bk Dc -> In bk Lamc) by (intros [a k] Hk; exact (HDc a k Hk)).
assert (HCT1 : pj_nodeR SEGS (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc)
  (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) tcB Dc).
{ apply (pj_nodeR_frame SEGS tcB (mrestrict (w_H Wc) memc) _ (prh_lin Lamc) _ Dc HCT).
  intros y Hy.
  destruct (cb4_foot_nw _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dc (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) y HL HDcb
    ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) Hy) as (Hy1 & Hy2).
  assert (E : mrestrict (w_H Wc) (ms_mem ms) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y)).
  { apply Hag. rewrite unsigned_lit_small by lia. exact Hy2. }
  split; [unfold mbyte; rewrite E; reflexivity|].
  intros Hw. unfold writable_at, wview in Hw |- *. rewrite E. exact Hw. }
(* copy's free order, kept by the run the same way *)
assert (HFO1 : exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc) DOC_D
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
  map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (@crt_tree_J t)).
{ destruct HFOw as (Fc & HFc & EFc). exists Fc. split; [|exact EFc].
  eapply PRH_PjOrder.pj_foR_frame; [exact HFc | intros a k Hak; eapply PRH_PjOrder.pj_foR_lblk; [exact HFc | exact Hak] |].
  intros y Hy.
  destruct (cb4_foot_nw _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dc (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) y HL HDcb
    ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) Hy) as (Hy1 & Hy2).
  assert (E : mrestrict (w_H Wc) (ms_mem ms) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y)).
  { apply Hag. rewrite unsigned_lit_small by lia. exact Hy2. }
  split; [unfold mbyte; rewrite E; reflexivity|].
  intros Hw. unfold writable_at, wview in Hw |- *. rewrite E. exact Hw. }
assert (Hhi1 : spZ (ms_regs ms) + 64 <= ly_stk_hi lyc) by (rewrite Hspz, Eshi; lia).
assert (Hrac1 : raZ (ms_regs ms) < YM05.alloc_ceiling) by (unfold raZ; rewrite X1, unsigned_lit_small by lia; lia).
(* THE CALL: pj_write (&copy, 1), tpj_write_specX at DOC_D. The caller's journal is at its budget WS0 (crt_live's kb
   journal) and pj_write has no wild site: the budgeted call rule YCbqGwild.aj_call_xbFR at RZW at the callee's empty
   budget, P := (fun WS1 => WS1 = []), the callee's text by YCbqGwild.apost_base_xbF_of_xR (Crt102Kit.crt102rw_call's
   kb shape); the run's length bound is HOS4 *)
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ refine (@YCbqGwild.aj_call_xbFR fxk rc SK SEGS B PST ARx cf_head LAWS (@pa_segs_low rc B_prog_listing PA)
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc
    (TEB regs rg []) _ ms STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc _ kj WS0
    (@STK_pj_write prh_img_B DOC_D) [] (sp1 - sp0) (ew (TEB regs rg []) 2) (getr (ms_regs ms) 1) ch1
    (fun WS1 => WS1 = []) _ HS eq_refl HJ Hspc eq_refl HE2 _ _ _ _ _ _ eq_refl _ _ _ _ _).
  - apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. apply Z.mod_divide in Hs1a; [|lia].
    destruct Hs1a as [q' Hq']. apply Z.mod_divide; [lia|]. exists (2 * q' - q). lia.
  - lia.
  - rewrite HSTKW. lia.
  - rewrite HSTKW, HSTKC. lia.
  - rewrite R3'. exact Hgp.
  - rewrite R4'. exact Htp.
  - rewrite X1. apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2].
  - rewrite X1, unsigned_lit_small by lia. lia.
  - replace (sp0 + (sp1 - sp0)) with sp1 by lia. rewrite Hs0z. exact Hch1.
  - intros HPRE1. eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
    + exact (GPJW fxk rp_sm rp_x rp_os (rp_i + length pre)%nat rp_H0 hist most 0 lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms)
        _ ch1 (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) 1 tcB Dc Lamc peakc (cwB cset) SIZE_MAXZ 0
        (conj HPRE1 (conj HRO1 (conj Hhi1 (conj Hrac1 HFZ)))) HCL HROOM HRP HOS4 Esm HCFW X10 X11 ltac:(lia) HLED1 HRUNW
        HCT1 ltac:(right; right; exists CRT_CID, pos; split; [exact Hin|]; rewrite cb4_fb; unfold CRT_OFF_COPY; lia)
        HCR1 HTV1 HDc Hdep Hdep31 Hfr0 Hwl Hwmax Hlive).
    + intros W' c' _ Hpo. apply YCbqGwild.apost_base_xbF_of_xR; [reflexivity | exact Hpo].
  - intros a Hfa. exfalso. exact (inFP_nil a Hfa). }
(* THE RETURN at +0x2bc: the caller's journal at WS0 ++ [] = WS0 *)
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ2 & HFK2 & HPW & HJ2 & HJ1 &
  HP & HQ & HMN2).
subst WS1. rewrite app_nil_r in HJ2.
replace (sp0 + (sp1 - sp0)) with sp1 in HJ1 by lia.
rewrite X1.
destruct HQ as (ok & ranw & q & Lam' & peak' & HQr).
cbv zeta in HQr. change (negb (1 =? 0)) with true in HQr.
destruct HQr as (HOKS & HR10 & HROOM2 & HGR0 & HPOS2 & HND2c & HTV2 & HLED2 & HARMS).
(* no grow refused (T4_GOAL_PJW's dead arm), so pj_write left g_ran_out at 0 *)
pose proof (cb4w_granted_ran _ _ _ _ _ _ _ _ HOKS HGR0) as Er0.
assert (HWF : WriterApp.w_fail (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ)
  (WriterValue.wdpieces tcB true)) = SIZE_MAXZ)
  by exact (cb4w_wput_failmax (WriterValue.wdpieces tcB true) ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) eq_refl).
rewrite HWF in HLED2.
apply (HWr fx' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Dc Lam' peak' regs2 mso cset).
exists ok, ranw, q. split; [|split; [exact HR10 | exact Er0]].
unfold crt4_wr_core. cbv zeta. unfold crt_wP, crt_tb.
set (st' := PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) (WriterValue.wdpieces tcB true)) in *.
(* the callee's journal keeps the frame, the stack above sp1, and the class-3 frame's shadow *)
pose proof HJ1 as (HAR2 & HLY1 & _ & _ & _ & HFR1 & _ & _ & KS1 & _ & _ & KF1 & _).
pose proof HLY1 as (_ & _ & _ & _ & _ & EFF & _).
assert (EF : frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos) by (unfold frame_addr; rewrite EFF; reflexivity).
assert (KS : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros a Ha. apply KS1; lia. }
assert (KSM : forall a, sp1 <= a < 2 ^ 64 -> ~ (sp1 + 56 <= a < sp1 + 64) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. rewrite (KS a Ha). exact (K a ltac:(lia) Hn). }
assert (KFR : forall a, shadow_addr (frame_addr lyc CRT_CID pos) <= a < shadow_addr (frame_addr lyc CRT_CID pos) + 64 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. rewrite (KF1 CRT_CID pos a Hin); [| right | apply inFP_nil].
  - apply K; unfold shadow_addr, SHADOW_OFF in Ha |- *; lia.
  - unfold in_zr. cbn [fst snd]. rewrite cb4_fb. change (512 / 8) with 64. exact Ha. }
(* the blocks the walk held before the call are still live *)
assert (HLam : forall bk, In bk Lamc -> In bk Lam').
{ intros bk Hbk. destruct HARMS as [(_ & _ & _ & ELam & _) | (_ & _ & ELam & _)];
    [rewrite ELam; right; exact Hbk | rewrite ELam; exact Hbk]. }
assert (HAB2 : forall a k, In (a, k) Lamc -> In (a - cf_head, k + cf_head) (ablocks B ly2 S2)).
{ intros a k Hk.
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc (ms_mem ms) Lamc peakc (cwB cset) SIZE_MAXZ 0 a k _ _ HLED1 Hk)
    as (_ & Hab & _).
  destruct HARMS as [(_ & _ & _ & _ & _ & HPab2 & _) | (_ & _ & _ & HPab2 & _)];
    [apply (Permutation_in _ (Permutation_sym HPab2)); right; exact Hab
    | apply (Permutation_in _ (Permutation_sym HPab2)); exact Hab]. }
destruct (cb4w_doc_call lyc Sc Hpc Wc (ms_mem ms) _ kj pos Dc Lamc peakc (cwB cset) 0 0 _ _ ly2 S2 Hp2 W2 mem2 md2 k1
  Lam' HL1 HJ1 HLam HAB2) as (HND2 & HDL2).
destruct HFO1 as (Fc & HFc1 & EFc).
pose proof (cb4w_foR_call lyc Sc Hpc Wc (ms_mem ms) _ kj pos Dc Lamc peakc (cwB cset) 0 0 _ _ ly2 S2 Hp2 W2 mem2 md2 k1
  Lam' Dc (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) DOC_D Fc HL1 HJ1
  ltac:(unfold CRT_OFF_COPY; lia) ltac:(rewrite cb4_fb; unfold CRT_OFF_COPY; lia) HDcb
  (fun bk Hbk => HLam bk (HDcb bk Hbk)) (fun a k Hak => HAB2 a k (HDc a k Hak)) HFc1) as HFc2.
assert (Hpk2 : peak <= peak').
{ destruct HARMS as [(_ & _ & _ & _ & Epk & _) | (_ & _ & _ & _ & [(_ & Epk) | (_ & Epk)])]; rewrite Epk; lia. }
assert (HSD2 : sideB ly2 S2 Hp2 W2 mem2 Lam' peak' (WriterApp.w_cnt st') 0 ranw).
{ exact {| crt_side_ledger := HLED2; crt_side_peak := Hpk2; crt_side_room := HROOM2;
           crt_side_arodata := cb4w_ro_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1 HRO1;
           crt_side_doc := HND2; crt_side_doc_blocks := HDL2 |}. }
(* the boundary's conjuncts both arms share *)
assert (HCOM :
  dregsB regs2 (frame_addr ly2 CRT_CID pos) /\
  getr regs2 21 = w64 1 /\
  getr regs2 26 = w64 (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B) /\
  spillB W2 mem2 CRT_SP_BACK (frame_addr ly2 CRT_CID pos + CRT_OFF_BACK) /\
  spillB W2 mem2 CRT_SP_SHN_B (shadow_addr (doc + PJ_OFF_N)) /\
  spillB W2 mem2 CRT_SP_PN_B (doc + PJ_OFF_N) /\
  spillB W2 mem2 CRT_SP_N_B (Z.of_nat (length mso)) /\
  doc mod 8 = 0 /\ range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF doc 56 /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (frame_addr ly2 CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (frame_addr ly2 CRT_CID pos + CRT_OFF_V) 56 /\
  0 <= cset <= 3 /\ (In ck_MOD_AT (map fst mso) -> cset = 0) /\
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam') (frame_addr ly2 CRT_CID pos + CRT_OFF_COPY) tcB Dc /\
  (exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam') DOC_D
     (frame_addr ly2 CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (@crt_tree_J t)) /\
  YCbq.bsum (ck_hblks Dc) <= LIVE_round_trip_text t false + LIVE_round_trip_text t true +
    PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
    PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT))).
{ rewrite EF.
  split; [exact (cb4_dregs_pres _ _ _ HDR1 HP)|].
  split; [rewrite (ts_ap (ms_regs ms) regs2 21%bv HP) by ts_cs; exact X21|].
  split; [rewrite (ts_ap (ms_regs ms) regs2 26%bv HP) by ts_cs; exact X26|].
  split.
  { unfold crt_spill. apply (ts_vm_av (w_H Wc) (w_H W2) (ms_mem ms) mem2 _ 8 _); [|exact VSP].
    intros i Hi. apply KS. unfold CRT_SP_BACK. lia. }
  split.
  { unfold crt_spill in SSHN |- *. apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact SSHN].
    intros i Hi. apply KSM; unfold CRT_SP_SHN_B; lia. }
  split.
  { unfold crt_spill in SPN |- *. apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact SPN].
    intros i Hi. apply KSM; unfold CRT_SP_PN_B; lia. }
  split.
  { unfold crt_spill in SN |- *. apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact SN].
    intros i Hi. apply KSM; unfold CRT_SP_N_B; lia. }
  split; [exact Hd8|].
  split; [exact (proj2 (proj2 (cb4w_home_keep _ _ _ _ _ _ _ _ HJ2)))|].
  split.
  { apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAb].
    intros y Hy. apply KFR. unfold shadow_of_addr, shadow_addr, CRT_OFF_BACK in Hy |- *. lia. }
  split.
  { apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAv].
    intros y Hy. apply KFR. unfold shadow_of_addr, shadow_addr, CRT_OFF_V in Hy |- *. lia. }
  split; [exact Hcs|]. split; [exact Hmod|].
  split.
  { apply (cb4_nodeR_lblk SEGS tcB _ (prh_lin Lamc)); [exact HND2c|].
    intros a k Hk. apply HLam. apply HDc. exact Hk. }
  split; [exists Fc; split; [exact HFc2 | exact EFc] | exact HBS]. }
destruct HARMS as [(Hs & Hq0 & HnAb & ELam & Epk & HPab2 & Hlen & Hbytes) | (Hf & Hq0 & ELam & HPab2 & Hcap)].
- (* q <> 0: the text in the new block (q, cap), the write granted *)
  assert (HL2 : liveB (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos
    ((q, WriterApp.w_cap st') :: Dc) Lam' peak' (WriterApp.w_cnt st') 0 ranw).
  { refine (cb4_live_call lyc Sc Hpc Wc (ms_mem ms) _ kj pos Dc Lamc peakc (cwB cset) 0 0
      (@STK_pj_write prh_img_B DOC_D) [] ly2 S2 Hp2 W2 mem2 md2 k1 ((q, WriterApp.w_cap st') :: Dc) Lam' peak'
      (WriterApp.w_cnt st') 0 ranw HL1 (ex_intro _ WS0 (conj HJ2 HB0)) HJ1 ltac:(rewrite HSTKW; lia) _ HSD2 _ _ _
      HMN2).
    - intros a Hfa. exfalso. exact (inFP_nil a Hfa).
    - rewrite ELam. cbn [app]. apply perm_skip. exact HPm1.
    - eapply perm_trans; [exact HPab2|].
      change (ck_hblks ((q, WriterApp.w_cap st') :: Dc)) with
        ((q - cf_head, WriterApp.w_cap st' + cf_head) :: ck_hblks Dc).
      eapply perm_trans; [apply perm_skip; exact HPab1 | apply Permutation_middle].
    - intros bk [<- | Hbk] HinD; [|exact (HDap1 bk Hbk HinD)]. apply HnAb.
      destruct (prh_ledger_hblock B lyc Sc Hpc Wc (ms_mem ms) Lamc peakc (cwB cset) SIZE_MAXZ 0 _ _ _ _ HLED1
        (HDL1 _ HinD)) as (_ & Hab & _).
      exact Hab. }
  rewrite (proj2 (Z.eqb_neq q 0) Hq0).
  split; [exact Ems|]. split; [exact HFZ2|]. split; [exact (cb4_fregs_trans fx fxk fx' HFK HFK2)|].
  split; [exact HOKS|]. split; [exact HL2|].
  destruct HCOM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13 & M14 & M16 & M15).
  do 18 (split; [assumption|]).
  left. split; [exact Hs|]. split; [exact Hq0|].
  split.
  { intros HinDc. apply HnAb.
    destruct (prh_ledger_hblock B lyc Sc Hpc Wc (ms_mem ms) Lamc peakc (cwB cset) SIZE_MAXZ 0 _ _ _ _ HLED1
      (HDc _ _ HinDc)) as (_ & Hab & _).
    exact Hab. }
  split; [exact Hlen|]. split; [exact Hbytes|].
  (* THE POSITION after the granted write: pre ++ w_evs done, the reading and L0's suffix left *)
  assert (HGR : PRH_Base.prh_granted ok (cwB cset) SIZE_MAXZ
    (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) (WriterValue.wdpieces tcB true))).
  { intros i Hi Hn.
    rewrite (cb4w_wput_ok (WriterValue.wdpieces tcB true) ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) eq_refl Hs i Hi)
      in Hn.
    discriminate. }
  destruct (HPOS2 HGR) as (hist' & HP2).
  rewrite (PRH_Supply.prhWriter_pjw_evs_granted _ ok (cwB cset) SIZE_MAXZ ltac:(lia) ltac:(unfold SIZE_MAXZ; lia) HGR),
    Hpjw0 in HP2.
  refine {| crt_pos_strtod := Esm; crt_pos_ex := _ |}.
  exists (pre ++ PresetReqAt.w_evs (PresetReqAt.copy_set mso) true), hist'. cbv beta.
  refine {| crt_pos_split := _; crt_pos_room := _; crt_pos_run := _; crt_pos_cons := _ |}.
  + rewrite Ert, <- app_assoc. reflexivity.
  + rewrite length_app, Nat.add_assoc. exact HP2.
  + rewrite length_app, Nat.add_assoc. exact HRUNr.
  + rewrite length_app, Nat.add_assoc. exact HCFr.
- (* q = 0: the write refused, nothing held beyond Dc *)
  subst q.
  assert (HL2 : liveB (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos
    Dc Lam' peak' (WriterApp.w_cnt st') 0 ranw).
  { refine (cb4_live_call lyc Sc Hpc Wc (ms_mem ms) _ kj pos Dc Lamc peakc (cwB cset) 0 0
      (@STK_pj_write prh_img_B DOC_D) [] ly2 S2 Hp2 W2 mem2 md2 k1 Dc Lam' peak'
      (WriterApp.w_cnt st') 0 ranw HL1 (ex_intro _ WS0 (conj HJ2 HB0)) HJ1 ltac:(rewrite HSTKW; lia) _ HSD2 _ _ HDap1
      HMN2).
    - intros a Hfa. exfalso. exact (inFP_nil a Hfa).
    - rewrite ELam. exact HPm1.
    - eapply perm_trans; [exact HPab2 | exact HPab1]. }
  split; [exact Ems|]. split; [exact HFZ2|]. split; [exact (cb4_fregs_trans fx fxk fx' HFK HFK2)|].
  split; [exact HOKS|]. split; [exact HL2|].
  destruct HCOM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13 & M14 & M16 & M15).
  do 18 (split; [assumption|]).
  right. split; [exact Hf | reflexivity].
Qed.


(* ======== PART B of this row (Crt102B_T4B.v, merged into this file) ======== *)

(* ======================================================================================================== *)
(* PART B (rows Wr and O2 of T4): the two `lbu a0, 0x2d0(s10); bnez a0; jal fuzz_alloc_ran_out` tests, at
   +0x2c4 (offset 708, the call at +0x2cc, its return at +0x2d0 = 720) and at +0x2f0 (offset 752, the call at
   +0x2f8, its return at +0x2fc = 764). own = 0 at both, so neither `bnez` branches, and the shared call lemma
   cb4_ro below is used at both sites. *)

(* ---- a frame of the current state: aligned, bounded, its bytes present ---- *)
Lemma cb4_frame_any : forall lyc Sc Hpc Wc memc mdc cid pos',
  ARx lyc Sc Hpc Wc memc mdc -> In (cid, pos') (frames Sc) ->
  frame_addr lyc cid pos' mod 32 = 0 /\ 4096 <= frame_addr lyc cid pos' /\
  frame_addr lyc cid pos' + fs_frame_bytes cid <= YM05.alloc_ceiling /\
  (forall a, frame_addr lyc cid pos' <= a < frame_addr lyc cid pos' + fs_frame_bytes cid ->
     apresent (w_H Wc) memc a).
Proof.
intros lyc Sc Hpc Wc memc mdc cid pos' HAR Hin.
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc cid pos' HAR Hin) as (Fb1 & Fb2 & _).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc cid pos' HAR Hin) as (F32 & _ & Ffr & _).
split; [exact F32|]. split; [exact Fb1|]. split; [exact Fb2|].
intros a Ha. exact (proj1 (Ffr a Ha)).
Qed.

(* ---- a slot of the class-3 frame is a 56-byte window inside a live frame ---- *)
Lemma cb4_in_frame_slot : forall lyc Sc pos off, In (CRT_CID, pos) (frames Sc) -> 0 <= off -> off + 56 <= 512 ->
  ck_in_frame lyc Sc (frame_addr lyc CRT_CID pos + off) 56.
Proof.
intros lyc Sc pos off Hin H1 H2. exists CRT_CID, pos. split; [exact Hin|]. rewrite cb4_fb. lia.
Qed.

(* ---- the document's home stays a live fake frame of the entry (Crt102Kit's crt102rw_home_keep) ---- *)
Lemma cb4_home_keep : forall own lyc Sc Hpc Wc memc mdc kj {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kj WS -> ck_obj_home lyc Sc Wc memc doc.
Proof.
intros own lyc Sc Hpc Wc memc mdc kj WS HJ.
pose proof HPRE as ((HAR & _) & _).
pose proof HTREE as (_ & _ & _ & Hd8 & (cid & pos' & Hfin & Hfa1 & Hfa2) & HRA).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
destruct (alx_layout _ _ _ LAWS ly S Hp W mem md lyc HAR Hly) as (_ & Efa & _).
destruct (alx_frames _ _ _ LAWS ly S Hp W mem md cid pos' HAR Hfin) as (F32 & _).
split; [exact Hd8|]. split.
- exists cid, pos'. rewrite Efa. split; [rewrite Hfrs; apply in_or_app; right; exact Hfin|]. split; lia.
- intros a Ha. destruct (HRA a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr. apply (F4 cid pos'); [exact Hfin | right | apply inFP_nil].
  unfold in_zr, shadow_addr. cbn [fst snd].
  assert (E8 : (frame_addr ly cid pos' + fs_frame_bytes cid) / 8 = frame_addr ly cid pos' / 8 + fs_frame_bytes cid / 8).
  { apply Z.mod_divide in F32; [|lia]. destruct F32 as [q Hq]. rewrite Hq.
    replace (q * 32 + fs_frame_bytes cid) with (fs_frame_bytes cid + (4 * q) * 8) by lia. rewrite Z.div_add by lia.
    replace (q * 32) with ((4 * q) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (H55 : (doc + 55) / 8 = doc / 8 + 6).
  { apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 55) with (7 + (q + 6) * 8) by lia. rewrite Z.div_add by lia. rewrite Z.div_mul by lia. cbn. lia. }
  assert (Hd : (doc + 56) / 8 = doc / 8 + 7).
  { apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 56) with ((q + 7) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
  pose proof (Z.div_le_mono (frame_addr ly cid pos') a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono a (doc + 55) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (doc + 56) (frame_addr ly cid pos' + fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)).
  lia.
Qed.

(* ======================================================================================================== *)
(* WHAT THE fuzz_alloc_ran_out CALL KEEPS. Its stack budget is 0 and its footprint is empty, so the callee's
   journal keeps: every byte of a 56-byte window of a live frame (and that byte is present again), the shadow of
   such a window (as a range_addressable keep), every byte of a live allocator block, and every byte at or above
   alloc_ceiling (the whole stack: its window sp1 - 0 .. sp1 is empty). *)
Definition cb4_kept (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
  (forall p y, ck_in_frame lyc Sc p 56 -> p <= y < p + 56 ->
     aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y /\ apresent (w_H W2) mem2 y) /\
  (forall p, ck_in_frame lyc Sc p 56 -> p mod 8 = 0 ->
     range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF p 56 ->
     range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF p 56) /\
  (forall a n i, In (a, n) (ablocks B lyc Sc) -> 0 <= i < req_size n ->
     aview SEGS (w_H W2) mem2 (a + i) = aview SEGS (w_H Wc) memc (a + i) /\ apresent (w_H W2) mem2 (a + i)) /\
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).

(* bytes a keep names agree, and a kept byte that is present is writable *)
Lemma cb4_agree_of : forall (Wc : world SEGS) memc (W2 : world SEGS) mem2 (X : Z -> Prop),
  (forall y, X y -> aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y /\ apresent (w_H W2) mem2 y) ->
  pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) X.
Proof.
intros Wc memc W2 mem2 X HX y Hy. destruct (HX y Hy) as (Ha & Hap).
split; [exact (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2 y Ha)|].
intros _. apply (apresent_writable SEGS). exact Hap.
Qed.

(* a byte of a live harness block *)
Lemma cb4_km_blk : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc W2 mem2 a k y {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  cb4_kept lyc Sc Wc memc W2 mem2 ->
  In (a, k) Lamc -> a <= y < a + k ->
  aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y /\ apresent (w_H W2) mem2 y.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc W2 mem2 a k y kbg HL HK Hin Hy.
pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
destruct HK as (_ & _ & KB & _).
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc a k _ _ HLED Hin) as (Hk0 & Hab & _).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity. rewrite Hch16 in Hab.
assert (Hrq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
destruct (KB (a - 16) (k + 16) (y - (a - 16)) Hab ltac:(rewrite Hrq; lia)) as (H1 & H2).
replace (a - 16 + (y - (a - 16))) with y in H1, H2 by lia.
split; [exact H1 | exact H2].
Qed.

(* every byte of a tree that sits in a 56-byte window of a live frame and whose blocks are live *)
Lemma cb4_km_foot : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc W2 mem2 D' p y {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  cb4_kept lyc Sc Wc memc W2 mem2 ->
  (forall bk, In bk D' -> In bk Lamc) -> ck_in_frame lyc Sc p 56 ->
  pj_footR p D' y ->
  aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y /\ apresent (w_H W2) mem2 y.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc W2 mem2 D' p y kbg HL HK HD Hfr Hy.
destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- destruct HK as (KF & _). exact (KF p y Hfr Hy).
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  exact (cb4_km_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b kb y HL HK (HD _ Hb) Hy).
Qed.

Lemma cb4_km_nodeR : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc W2 mem2 D' p tv {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  cb4_kept lyc Sc Wc memc W2 mem2 ->
  (forall bk, In bk D' -> In bk Lamc) -> ck_in_frame lyc Sc p 56 ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) p tv D' ->
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lamc) p tv D'.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc W2 mem2 D' p tv kbg HL HK HD Hfr HN.
apply (pj_nodeR_frame SEGS tv (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) p D' HN).
apply cb4_agree_of. intros y Hy.
exact (cb4_km_foot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D' p y HL HK HD Hfr Hy).
Qed.

Lemma cb4_km_fdR : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc W2 mem2 D' p d {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  cb4_kept lyc Sc Wc memc W2 mem2 ->
  (forall bk, In bk D' -> In bk Lamc) -> ck_in_frame lyc Sc p 56 ->
  pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) d p D' ->
  pj_fdR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lamc) d p D'.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc W2 mem2 D' p d kbg HL HK HD Hfr HN.
apply (cb4_fdR_frame SEGS d (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) p D' HN).
apply cb4_agree_of. intros y Hy.
exact (cb4_km_foot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D' p y HL HK HD Hfr Hy).
Qed.

Lemma cb4_km_foR : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc W2 mem2 D' p d F' {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  cb4_kept lyc Sc Wc memc W2 mem2 ->
  (forall bk, In bk D' -> In bk Lamc) -> ck_in_frame lyc Sc p 56 ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) d p D' F' ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lamc) d p D' F'.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc W2 mem2 D' p d F' kbg HL HK HD Hfr HN.
eapply PRH_PjOrder.pj_foR_frame; [exact HN | |].
- intros a k Hak. eapply PRH_PjOrder.pj_foR_lblk; [exact HN | exact Hak].
- apply cb4_agree_of. intros y Hy.
  exact (cb4_km_foot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D' p y HL HK HD Hfr Hy).
Qed.

Lemma cb4_km_spill : forall lyc Sc Wc memc W2 mem2 off v,
  cb4_kept lyc Sc Wc memc W2 mem2 -> 0 <= off <= 200 ->
  spillB Wc memc off v -> spillB W2 mem2 off v.
Proof.
intros lyc Sc Wc memc W2 mem2 off v HK Hoff HV. destruct HK as (_ & _ & _ & KH).
pose proof cb4_sp as (_ & Hceil & H47 & Hs1 & _ & Hs0). pose proof (YM05.alloc_ceiling_val).
unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact HV].
intros i Hi. apply KH. lia.
Qed.

Lemma cb4_km_bytes : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc W2 mem2 q cap l {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  cb4_kept lyc Sc Wc memc W2 mem2 ->
  In (q, cap) Lamc -> Z.of_nat (length l) <= cap ->
  bytes_at Wc memc q l -> bytes_at W2 mem2 q l.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc W2 mem2 q cap l kbg HL HK Hin Hlen HB.
unfold bytes_at in *.
apply (ts_garr_av (w_H Wc) (w_H W2) memc mem2 q l); [|exact HB].
intros j Hj.
destruct (cb4_km_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q cap (q + Z.of_nat j) HL HK Hin ltac:(lia)) as (H1 & _).
exact H1.
Qed.

(* ======================================================================================================== *)
(* the registers a call keeps (callee-saved, plus gp and tp) *)
Definition CB4_KEEP : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma cb4_keep_pres : forall rg rg', aregs_preserved rg rg' -> forall r, In r CB4_KEEP -> getr rg' r = getr rg r.
Proof.
intros rg rg' HP r Hr. unfold CB4_KEEP in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [rewrite (ts_ap rg rg' _ HP) by ts_cs; reflexivity|]). destruct Hr.
Qed.

(* ---- the return site of the two ran_out calls ---- *)
Lemma cb4_ret_ro : forall off, off = 720 \/ off = 764 ->
  4096 <= BASE + (CRT_PC_B + off) < 2 ^ 31 /\ (CRT_PC_B + off) mod 2 = 0 /\ 0 <= CRT_PC_B + off < 2 ^ 40.
Proof.
intros off [-> | ->];
  (split; [split; vm_compute; first [discriminate | reflexivity]|]);
  (split; [vm_compute; reflexivity|]); split; vm_compute; first [discriminate | reflexivity].
Qed.

(* ======================================================================================================== *)
(* THE fuzz_alloc_ran_out CALL (B' +0x2cc and +0x2f8): from the state the run leaves at the `jal`, the text FRO at
   the call's binders; the continuation gets the composed journal, the live state again, the kept registers, the
   returned flag and the keep cb4_kept. The model is Crt102Kit's crt102rw_call, specialised to this callee. kb round:
   the live state at any budget kbg, and the callee has no wild site, so the call runs over the budgeted rule at the
   callee's empty budget and the caller's journal stays at its budget (the continuation gets it at a WS with
   wbudget [] kbg WS, Crt102Kit.crt102rw_call's shape). At the re-hiding move the rule is
   YCbqGwild.aj_call_xb_spR at RZW (aj_call_xb is gone from the engine), the plain text FRO lifted by YA0nH.SRr_SRr'
   and apost_base_x_R_lift at YA0nH.wle_wle', the walk in SRr' *)
Lemma cb4_ro_call : forall (fxk : YK11.FPState) (off : Z) (Wc : world SEGS) E ss ms mdc lyc Sc Hpc kj pos
    Dx Lamc peakc cntc ranc {kbg : nat},
  frm_zero (@YK11.fp_csr fxk) ->
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None ->
  ss_pc ss = SIGMA AS_fuzz_alloc_ran_out ->
  bv_unsigned (ew E 2) = sp0 ->
  liveB kbg lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc 0 ranc ->
  dregsB (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  (off = 720 \/ off = 764) -> getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + off)) ->
  (forall rg2 ly2 W2 mem2 md2 k1,
     (exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 Sc Hpc W2 mem2 md2 (kj + k1) WS /\
        YCbqGwild.wbudget [] kbg WS) ->
     liveB kbg ly2 Sc Hpc W2 mem2 md2 (kj + k1) pos Dx Lamc peakc cntc 0 ranc ->
     frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos ->
     cb4_kept lyc Sc Wc (ms_mem ms) W2 mem2 ->
     (forall r, In r CB4_KEEP -> getr rg2 r = getr (ms_regs ms) r) ->
     getr rg2 10 = w64 ranc ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
       (mkCfg (@YK11.mkst fxk rg2 (Z_to_bv 64 (BASE + (CRT_PC_B + off))) mem2 (YK11.seg_rom SEGS)) md2) QFb) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFb.
Proof.
intros fxk off Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc ranc kbg HFZc HS Hrv Hpcs HE2 HL HDR Hoff Hra HK.
cb4_rd_live HL WS0 HJ HB0 HSD HPL HPB HAP HSV HFRM HSPF HCR HCH HMNc.
cb4_rd_side HSD HLED Hpk HROOM HRO HND HDL.
cb4_rd_dregs HDR R2 R3 R4 R8 R9 R18 R20 R19 R23 R25 R27 R22.
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac & Hfz0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
pose proof cb4_sp as (Hs16 & Hsc & Hs47 & Hs1 & Hs32 & Hs0).
pose proof HJ as (HARc & HLYc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ) as (Hin3 & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (cb4_chain [(CRT_CID, pos)] lyc Sc Hpc Wc (ms_mem ms) mdc kj HJ HSV) as (ch1 & Hch1 & _).
destruct (cb4_ret_ro off Hoff) as (Hr1 & Hr2 & Hr3).
assert (ESTK : @STK_fuzz_alloc_ran_out prh_img_B = 0) by (vm_compute; reflexivity).
set (o := sp1 - sp0).
assert (Hspz : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0z : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (Hraz : raZ (ms_regs ms) = BASE + (CRT_PC_B + off)) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; lia).
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ refine (@YCbqGwild.aj_call_xb_spR fxk rc SK SEGS B PST ARx cf_head LAWS (@pa_segs_low rc B_prog_listing PA)
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E ss ms
    STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc mdc kj WS0 (@STK_fuzz_alloc_ran_out prh_img_B) [] o
    (getr (ms_regs ms) 1) ch1 (fun WS1 => WS1 = []) _
    HS Hrv HJ ltac:(rewrite Hspz; unfold o; lia) _ _ _ _ _ _ eq_refl _ _ _ _ _).
  - unfold o. apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q Hq]. apply Z.mod_divide in Hs32; [|lia].
    destruct Hs32 as [q' Hq']. apply Z.mod_divide; [lia|]. exists (2 * q' - q). lia.
  - unfold o. lia.
  - rewrite ESTK. lia.
  - rewrite ESTK. unfold o. rewrite cb4_stkc. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - rewrite Hra. apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2].
  - rewrite Hra, unsigned_lit_small by lia. lia.
  - replace (sp0 + o) with sp1 by (unfold o; lia). rewrite Hs0z. exact Hch1.
  - intros HPRE1. rewrite Hpcs.
    assert (HFP1 : fpre B ARx (@STK_fuzz_alloc_ran_out prh_img_B) lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1).
    { split; [exact HPRE1|]. split; [exact HRO|].
      split; [rewrite Hspz, Eshi; lia | split; [rewrite Hraz; lia | exact HFZc]]. }
    eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
    + exact (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf _ _ _
        (FRO fxk lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 Lamc peakc cntc SIZE_MAXZ ranc most 0 HFP1 HLED)).
    + intros W' c' _ Hpo. apply YCbqGwild.apost_base_xb_of_xR; [reflexivity|].
      eapply apost_base_x_R_lift; [exact (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact Hpo].
  - intros a Hfa. exfalso. exact (inFP_nil a Hfa). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW & HJ2 & HJ1 & HP & HQ).
subst WS1. rewrite app_nil_r in HJ2.
replace (sp0 + o) with sp1 in HJ1 by (unfold o; lia).
destruct HQ as ((HROOM2 & HR10 & EHp & ES & Eab & HLED2) & HMN2).
subst Hp2 S2.
pose proof HJ1 as (HAR2 & HLY1 & _ & _ & _ & HFR1 & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof HLY1 as (_ & _ & _ & _ & _ & EFF & _).
assert (EF : frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos)
  by (unfold frame_addr; rewrite EFF; reflexivity).
assert (Efa : forall cid pos', frame_addr ly2 cid pos' = frame_addr lyc cid pos')
  by (intros cid pos'; unfold frame_addr; rewrite EFF; reflexivity).
assert (Hfr2 : forall cid pos', In (cid, pos') (frames Sc) -> In (cid, pos') (frames Sc))
  by (intros; assumption).
(* the keep *)
assert (HKEEP : cb4_kept lyc Sc Wc (ms_mem ms) W2 mem2).
{ split.
  { intros p y (cid & pos' & Hfin & Hfa1 & Hfa2) Hy.
    destruct (cb4_frame_any ly2 Sc Hpc W2 mem2 md2 cid pos' HAR2 ltac:(rewrite HFR1; exact Hfin))
      as (_ & _ & _ & Fpres2).
    rewrite (Efa cid pos') in Fpres2.
    split.
    - apply (G4 cid pos' y Hfin); [left | apply inFP_nil]. unfold in_zr, frame_rng. cbn [fst snd]. lia.
    - apply Fpres2. lia. }
  split.
  { intros p (cid & pos' & Hfin & Hfa1 & Hfa2) Hp8 HRAp.
    destruct (cb4_frame_any lyc Sc Hpc Wc (ms_mem ms) mdc cid pos' HARc Hfin) as (Fa32 & Fa1 & Fa2 & _).
    apply (range_addressable_agree (aview SEGS (w_H Wc) (ms_mem ms))); [|exact HRAp].
    intros y Hy. unfold shadow_of_addr.
    apply (G4 cid pos'); [exact Hfin | right | apply inFP_nil].
    unfold in_zr, shadow_addr. cbn [fst snd].
    assert (E8 : (frame_addr lyc cid pos' + fs_frame_bytes cid) / 8
                 = frame_addr lyc cid pos' / 8 + fs_frame_bytes cid / 8).
    { apply Z.mod_divide in Fa32; [|lia]. destruct Fa32 as [q Hq]. rewrite Hq.
      replace (q * 32 + fs_frame_bytes cid) with (fs_frame_bytes cid + (4 * q) * 8) by lia. rewrite Z.div_add by lia.
      replace (q * 32) with ((4 * q) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    assert (H55 : (p + 55) / 8 = p / 8 + 6).
    { apply Z.mod_divide in Hp8; [|lia]. destruct Hp8 as [q Hq]. rewrite Hq.
      replace (q * 8 + 55) with (7 + (q + 6) * 8) by lia. rewrite Z.div_add by lia. rewrite Z.div_mul by lia. cbn. lia. }
    assert (Hd : (p + 56) / 8 = p / 8 + 7).
    { apply Z.mod_divide in Hp8; [|lia]. destruct Hp8 as [q Hq]. rewrite Hq.
      replace (q * 8 + 56) with ((q + 7) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
    pose proof (Z.div_le_mono (frame_addr lyc cid pos') y 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono y (p + 55) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p + 56) (frame_addr lyc cid pos' + fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)).
    lia. }
  split.
  { intros a n i Hab Hi. split.
    - apply (G2 a n i Hab); [rewrite Eab; exact Hab | exact Hi | apply inFP_nil].
    - destruct (alx_blocks _ _ _ LAWS ly2 Sc Hpc W2 mem2 md2 a n HAR2 ltac:(rewrite Eab; exact Hab))
        as (_ & _ & _ & _ & Hpres2 & _).
      exact (proj1 (Hpres2 (a + i) ltac:(lia))). }
  { intros a Ha. apply G1; [lia|]. rewrite ESTK. lia. } }
(* the live state after the call *)
assert (HL2 : liveB kbg ly2 Sc Hpc W2 mem2 md2 (kj + k1) pos Dx Lamc peakc cntc 0 ranc).
{ refine (cb4_live_call lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc 0 ranc
    (@STK_fuzz_alloc_ran_out prh_img_B) [] ly2 Sc Hpc W2 mem2 md2 k1 Dx Lamc peakc cntc 0 ranc
    HL (ex_intro _ WS0 (conj HJ2 HB0)) HJ1 ltac:(rewrite ESTK; lia)
    ltac:(intros a Hfa; exfalso; exact (inFP_nil a Hfa)) _ HPL _ HAP
    ltac:(intros Hm; exact (HMN2 Hm))).
  - refine {| crt_side_ledger := HLED2; crt_side_peak := Hpk; crt_side_room := HROOM2 HROOM;
              crt_side_arodata := _; crt_side_doc := _; crt_side_doc_blocks := HDL |}.
    { intros a Hro Hno Her. rewrite (G3 a); [exact (HRO a Hro Hno Her) | exact (cb4_ro_img a Hro) | exact Hno
        | exact Her | | ].
      - intros Hps. exact (pst_not_ro_B a Hps Hro).
      - apply fp_spares_closed. apply sink_closed_pos. apply Forall_nil. }
    destruct (cb4_home_keep [(CRT_CID, pos)] lyc Sc Hpc Wc (ms_mem ms) mdc kj HJ) as (Hd8 & Hdfr & _).
    exact (cb4_km_nodeR lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc 0 ranc W2 mem2 D doc t
      HL HKEEP HDL Hdfr HND).
  - rewrite Eab. exact HPB. }
rewrite Hra.
exact (HK regs2 ly2 W2 mem2 md2 k1 (ex_intro _ WS0 (conj HJ2 HB0)) HL2 EF HKEEP (cb4_keep_pres _ _ HP) HR10).
Qed.

(* ---- the segment shape of the two `lbu a0, 0x2d0(s10)` tests: one read-only byte at s10 + 0x2d0, which is
   g_own_ran_out and reads 0 (own = 0 at both tests) ---- *)
Definition cb4_ssRO (pc : Z) : sstate := mkSS pc cur_atoms
  [YP09.mkRegion (Some (xr 26)) 720 721 0 0 [YP09.mkChunk 720 (CVal 1 (SLit 0))]] None (mkFacts [] [] []).

Lemma cb4_RO_entry : forall (fxk : YK11.FPState) pc (Wc : world SEGS) memc rg,
  getr rg 26 = w64 (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B) -> prh_own Wc memc 0 ->
  st_ok_pi SEGS VAL (TEB regs rg []) (cb4_ssRO pc)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TEB regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk pc Wc memc rg R26 HOW.
destruct HOW as (HV & _).
assert (Hg : @pi_g_own_ran_out prh_img_B = 6151552) by (vm_compute; reflexivity).
assert (Hgz : @pi_gz_own_ran_out prh_img_B = 1%nat) by (vm_compute; reflexivity).
rewrite Hgz in HV.
set (E := TEB regs rg []).
assert (X26 : bv_unsigned (ew E (xr 26)) = @pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B).
{ unfold E, xr. rewrite (te_curB regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  rewrite Hg. unfold CRT_OWN_LO_B. lia. }
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TEB regs rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 26) (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B));
    [exact X26 | rewrite Hg; unfold CRT_OWN_LO_B; lia | rewrite Hg; unfold CRT_OWN_LO_B; lia | | ].
  + intros o Ho. cbn [YP09.r_wlo YP09.r_whi] in Ho. exfalso. lia.
  + constructor; [|constructor].
    apply (ts_chunk E _ _ 720 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 1) with 1%nat.
    replace (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B + 720) with (@pi_g_own_ran_out prh_img_B)
      by (unfold CRT_OWN_LO_B; lia).
    exact HV.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [exact I | split; [exact I | exact I]].
Qed.

(* ======================================================================================================== *)
(* THE SHARED TEST-AND-CALL (B' +0x2c4 .. +0x2d0 and +0x2f0 .. +0x2fc): `lbu a0, 0x2d0(s10)` reads 0 (own = 0),
   so `bnez a0` falls through, `jal fuzz_alloc_ran_out` returns the ledger's ran in a0, and the state is kept, at the
   live state's budget kbg (kb round) *)
Lemma cb4_ro : forall (fxk : YK11.FPState) (offs offr : Z) (Wc : world SEGS) memc mdc lyc Sc Hpc kj pos
    Dx Lamc peakc cntc ranc rg {kbg : nat},
  frm_zero (@YK11.fp_csr fxk) ->
  (offs = 708 /\ offr = 720) \/ (offs = 752 /\ offr = 764) ->
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 ranc ->
  dregsB rg (frame_addr lyc CRT_CID pos) ->
  getr rg 26 = w64 (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B) ->
  (forall rg2 ly2 W2 mem2 md2 k1,
     (exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 Sc Hpc W2 mem2 md2 (kj + k1) WS /\
        YCbqGwild.wbudget [] kbg WS) ->
     liveB kbg ly2 Sc Hpc W2 mem2 md2 (kj + k1) pos Dx Lamc peakc cntc 0 ranc ->
     frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos ->
     cb4_kept lyc Sc Wc memc W2 mem2 ->
     (forall r, In r CB4_KEEP -> getr rg2 r = getr rg r) ->
     getr rg2 10 = w64 ranc ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfgB fxk offr rg2 mem2 md2) QFb) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk offs rg memc mdc) QFb.
Proof.
intros fxk offs offr Wc memc mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc ranc rg kbg HFZc Hoffs HL HDR R26 HK.
cb4_rd_live HL WSJ HJ HBJ HSD HPL HPB HAP HSV HFRM HSPF HCR HCH HMNl.
pose proof (crt_side_ledger HSD) as HLED.
assert (HOWN : prh_own Wc memc 0) by (eapply PRH_Base.prh_ledger_own; exact HLED).
assert (HEI : img_env VAL A_LIM (TEB regs rg [])) by apply te_env.
assert (HE2 : bv_unsigned (ew (TEB regs rg []) 2) = sp0)
  by (rewrite (te_entry regs rg [] 2%bv 2) by reflexivity; reflexivity).
pose (RUN := @Crt102Kit.crt_run_xw fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS).
unfold crt_cfg.
destruct Hoffs as [(-> & ->) | (-> & ->)].
- destruct (cb4_RO_entry fxk (CRT_PC_B + 708) Wc memc rg R26 HOWN) as [HS SHOK].
  paj_run_tok_x (RUN WSJ) HS HJ SHOK (0, 0).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' x1 x2 x3 x4 x5 x6 x7) end.
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
  apply frame_of_read_only in HF; [|vm_compute; reflexivity].
  rewrite HF in HJ.
  pose proof (cb4_live_rejournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ HBJ) as HL1.
  assert (KR : forall rr : bv 5, In rr CB4_KEEP -> getr (ms_regs ms) rr = getr rg rr).
  { intros rr Hr. unfold CB4_KEEP in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [cb4_keep HS |]). destruct Hr. }
  assert (HDR1 : dregsB (ms_regs ms) (frame_addr lyc CRT_CID pos)).
  { apply (cb4_dregs_eq rg); [exact HDR|]. intros r0 Hr0. apply KR. unfold CB4_DREGS in Hr0. unfold CB4_KEEP.
    cbn [In] in Hr0 |- *. tauto. }
  prreg HS (1%bv : bv 5) Q1.
  assert (X1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + 720))) by (rewrite Q1; vm_compute; reflexivity).
  clear HFr HG.
  refine (@cb4_ro_call fxk 720 Wc _ _ ms _ lyc Sc Hpc kj pos Dx Lamc peakc cntc ranc kbg HFZc HS eq_refl eq_refl HE2
    _ HDR1 (or_introl eq_refl) X1 _).
  + rewrite HF. exact HL1.
  + intros rg2 ly2 W2 mem2 md2 k1 HJ2 HL2 EF HKEEP HKR HR10.
    rewrite HF in HKEEP.
    apply (HK rg2 ly2 W2 mem2 md2 k1 HJ2 HL2 EF HKEEP); [|exact HR10].
    intros r0 Hr0. rewrite (HKR r0 Hr0). exact (KR r0 Hr0).
- destruct (cb4_RO_entry fxk (CRT_PC_B + 752) Wc memc rg R26 HOWN) as [HS SHOK].
  paj_run_tok_x (RUN WSJ) HS HJ SHOK (0, 0).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' x1 x2 x3 x4 x5 x6 x7) end.
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
  apply frame_of_read_only in HF; [|vm_compute; reflexivity].
  rewrite HF in HJ.
  pose proof (cb4_live_rejournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ HBJ) as HL1.
  assert (KR : forall rr : bv 5, In rr CB4_KEEP -> getr (ms_regs ms) rr = getr rg rr).
  { intros rr Hr. unfold CB4_KEEP in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [cb4_keep HS |]). destruct Hr. }
  assert (HDR1 : dregsB (ms_regs ms) (frame_addr lyc CRT_CID pos)).
  { apply (cb4_dregs_eq rg); [exact HDR|]. intros r0 Hr0. apply KR. unfold CB4_DREGS in Hr0. unfold CB4_KEEP.
    cbn [In] in Hr0 |- *. tauto. }
  prreg HS (1%bv : bv 5) Q1.
  assert (X1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + 764))) by (rewrite Q1; vm_compute; reflexivity).
  clear HFr HG.
  refine (@cb4_ro_call fxk 764 Wc _ _ ms _ lyc Sc Hpc kj pos Dx Lamc peakc cntc ranc kbg HFZc HS eq_refl eq_refl HE2
    _ HDR1 (or_intror eq_refl) X1 _).
  + rewrite HF. exact HL1.
  + intros rg2 ly2 W2 mem2 md2 k1 HJ2 HL2 EF HKEEP HKR HR10.
    rewrite HF in HKEEP.
    apply (HK rg2 ly2 W2 mem2 md2 k1 HJ2 HL2 EF HKEEP); [|exact HR10].
    intros r0 Hr0. rewrite (HKR r0 Hr0). exact (KR r0 Hr0).
Qed.

(* ---- the count pj_write's run leaves is inside the function's whole budget ---- *)
Lemma cb4_wcnt : forall ok cset msl, t = PjTree.JObj msl -> 0 <= cset <= 3 ->
  cnt <= WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB)
      <= cnt + ck_crt_count t cset.
Proof.
intros ok cset msl Et Hc.
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran _ _ HLED0) as (_ & _ & Hcnt0 & _).
destruct (cm_cnt_write x t msl cset cnt HIN Et Hc ltac:(lia)) as (Hw1 & Hw2).
pose proof (cm_cnt2_eq cnt t) as E2.
assert (Ecw : @crt_cw t cnt cset = ck_cnt2 cnt t + 1 + cset) by (unfold crt_cw; lia).
rewrite Ecw.
pose proof (cm_pjw_cnt ok (ck_cnt2 cnt t + 1 + cset) SIZE_MAXZ (ck_crt_tree t) true ltac:(lia) ltac:(lia)) as (_ & Hb).
pose proof (cm_wcalls_nonneg (ck_crt_tree t) true) as Hnn.
pose proof (cm_pre4 t msl cset 0 Et ltac:(lia) ltac:(lia)) as P0.
pose proof (cm_pre4 t msl cset (PjWriteHyp.wcalls (ck_crt_tree t) true) Et ltac:(lia) ltac:(lia)) as P1.
unfold crt_wP, crt_tc in *. lia.
Qed.

(* ---- the two range_addressable keeps this row needs: a slot of the class-3 frame, and the document ---- *)
Lemma cb4_km_ra_slot : forall lyc Sc Wc memc W2 mem2 pos off,
  cb4_kept lyc Sc Wc memc W2 mem2 -> In (CRT_CID, pos) (frames Sc) ->
  frame_addr lyc CRT_CID pos mod 32 = 0 -> 0 <= off -> off + 56 <= 512 -> off mod 8 = 0 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + off) 56 ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (frame_addr lyc CRT_CID pos + off) 56.
Proof.
intros lyc Sc Wc memc W2 mem2 pos off HK Hin F32 H1 H2 H8 HRA.
destruct HK as (_ & KR & _).
exact (KR _ (cb4_in_frame_slot lyc Sc pos off Hin H1 H2) ltac:(lia) HRA).
Qed.

Lemma cb4_km_ra_doc : forall own lyc Sc Hpc Wc memc mdc kj W2 mem2 {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kj WS ->
  cb4_kept lyc Sc Wc memc W2 mem2 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc 56 ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF doc 56.
Proof.
intros own lyc Sc Hpc Wc memc mdc kj W2 mem2 WS HJ HK HRA.
destruct (cb4_home_keep own lyc Sc Hpc Wc memc mdc kj HJ) as (Hd8 & Hdfr & _).
destruct HK as (_ & KR & _). exact (KR doc Hdfr Hd8 HRA).
Qed.

(* ======================================================================================================== *)
(* PART B, FIRST LEMMA. Wr (+0x2bc): `mv s8, a0`, `beqz a0, +0x2f0`.
   q = 0: the write failed, the walk jumps to O2 with saved = 0, in the L0 state (pj_write left g_ran_out at 0:
   crt4_at_Wr).
   q <> 0: the first `lbu a0, 0x2d0(s10)` reads own = 0, so `bnez` falls through and fuzz_alloc_ran_out () is
   called at +0x2cc; its answer is the ledger's ran, which is 0 here (crt4_at_Wr): so S (+0x2d4); the answer 1 is
   refuted. *)
Lemma crt4_lane_Wr : CRT4_S -> CRT4_O2 -> CRT4_Wr.
Proof.
intros HSn HO2 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc rg msl cset (ok & ranw & q & HC & R10 & Er0).
destruct HC as (Et & HFZ & HFK & HOKS & HL & HDR & R21 & R26 & SPB & SPSHN & SPPN & SPN & Hd8 & RAdoc & RAback & RAv
  & Hcset & HcsetAt & HND & HCP & HDP & HFO & HBS & Harm).
cb4_rd_live HL WSJ HJ HBJ HSD HPL HPB HAP HSV HFRM HSPF HCR HCH HMNl.
cb4_rd_side HSD HLED Hpk HROOM HRO HNDdoc HDL.
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ) as (Hin3 & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cb4_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof (crt_dregs_B_bregs HDR) as HBR. pose proof (crt_dregs_B_s6 HDR) as R22.
cb4_rd_bregs HBR R2 R3 R4 R8 R9 R18 R20 R19 R23 R25 R27.
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
destruct (prh_ledger_bounds B lyc Sc Hpc Wc memc Lamc peakc _ SIZE_MAXZ ranw _ _ HLED) as (_ & _ & _ & _ & Hranw).
assert (Hqr : 0 <= q < 2 ^ 64).
{ destruct Harm as [(Hf0 & Hq0 & Hnin & Hlenb & Hbytes & Hposw) | (Hf & Hq0)]; [|lia].
  assert (Hinq : In (q, WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB))
                    Lamc).
  { apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq q 0) Hq0). left. reflexivity. }
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc _ SIZE_MAXZ ranw _ _ _ _ HLED Hinq) as (Hk0 & Hab & _).
  assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity. rewrite Hch16 in Hab.
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ (proj1 HJ) Hab) as (_ & B4096 & Bce & _).
  assert (Hrq : req_size (WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB)
                          + 16)
                = WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB) + 16)
    by (unfold req_size;
        destruct (Z.eqb_spec
          (WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB) + 16) 0); lia).
  rewrite Hrq in Bce. pose proof (YM05.alloc_ceiling_val). lia. }
assert (HDL' : forall bk, In bk Dc -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left.
  destruct (Z.eqb_spec q 0); [exact Hbk | right; exact Hbk]. }
assert (HFD : pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
  (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc).
{ apply (cb4_fdR_mono SEGS _ _ (PjTree.depth tcB) DOC_D); [exact (cm_crt_depth_doc t (cm_in_depth x t HIN))|].
  exact (cb4_nodeR_fdR SEGS tcB _ _ _ _ HND). }
assert (HcsetAt' : forall ms0, t = PjTree.JObj ms0 -> In ck_MOD_AT (map fst ms0) -> cset = 0).
{ intros ms0 E0 Hin0. apply HcsetAt. rewrite Et in E0. injection E0 as E0. rewrite E0. exact Hin0. }
assert (Hwcnt : cnt <= WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB)
  <= cnt + ck_crt_count t cset) by exact (cb4_wcnt ok cset msl Et Hcset).
assert (HEI : img_env VAL A_LIM (TEB regs rg [])) by apply te_env.
pose (RUN := @Crt102Kit.crt_run_xw fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS).
pose (RUNTO := @Crt102Kit.crt_run_to_xw fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS).
pose (BR := YSRrG.paj_branchR (fx := fxk) (rc := rc) (L := B_prog_listing) (PI := PA) RZW).
unfold crt_cfg.
assert (HS : @st_ok_pi SEGS VAL fxk (TEB regs rg [])
  (mkSS (CRT_PC_B + CRT_W_OFF_B) cur_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_W_OFF_B))) memc (YK11.seg_rom SEGS)))).
{ apply (@ts_st_ok fxk); [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TEB regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (A42 : bv_unsigned (ew (TEB regs rg []) 42) = q).
{ rewrite (te_curB regs rg _ 10%bv 10) by reflexivity. rewrite R10. unfold w64. apply unsigned_lit_small. lia. }
paj_run_tok_x (RUN WSJ) HS HJ SHOK (0, 0).
{ apply awr_ok_nil. }
apply frame_of_read_only in HF; [|vm_compute; reflexivity].
rename HF into EMA.
assert (KR1 : forall rr : bv 5, In rr CB4_DREGS -> getr (ms_regs ms) rr = getr rg rr).
{ intros rr Hr. unfold CB4_DREGS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [cb4_keep HS |]). destruct Hr. }
assert (K21 : getr (ms_regs ms) 21 = getr rg 21) by cb4_keep HS.
assert (K26 : getr (ms_regs ms) 26 = getr rg 26) by cb4_keep HS.
assert (HDR1 : dregsB (ms_regs ms) (frame_addr lyc CRT_CID pos))
  by (apply (cb4_dregs_eq rg); [exact HDR | exact KR1]).
prreg HS (24%bv : bv 5) Q24.
assert (X24 : getr (ms_regs ms) 24 = w64 q).
{ rewrite Q24. rewrite (te_curB regs rg _ 10%bv 10) by reflexivity. exact R10. }
clear HFr HG. rename ms into msA.
psrr_branch_tok RUN BR HS SHOK (0, 0).
- (* a0 = 0: the write was refused; jump to O2 with saved = 0 *)
  rewrite branch_eq_U, !ts_U0, U_SLit, A42 in Hc. rewrite YP0m.zcanon_small in Hc by lia.
  apply Z.eqb_eq in Hc. clear A42. subst q.
  destruct Harm as [(_ & Hq0 & _) | (Hfail & _)]; [exfalso; exact (Hq0 eq_refl)|].
  paj_run_to_tok_x (RUNTO WSJ) HS HJ SHOK (0, 0) (CRT_PC_B + CRT_O2_OFF_B).
  { apply awr_ok_nil. }
  apply frame_of_read_only in HF; [|vm_compute; reflexivity].
  rewrite EMA in HF.
  rewrite HF in HJ.
  pose proof (cb4_live_rejournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ HBJ) as HL2.
  assert (KR2 : forall rr : bv 5, In rr CB4_DREGS -> getr (ms_regs ms) rr = getr rg rr).
  { intros rr Hr. unfold CB4_DREGS in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [cb4_keep HS |]). destruct Hr. }
  assert (HDR2 : dregsB (ms_regs ms) (frame_addr lyc CRT_CID pos))
    by (apply (cb4_dregs_eq rg); [exact HDR | exact KR2]).
  assert (K21b : getr (ms_regs ms) 21 = getr rg 21) by cb4_keep HS.
  assert (K26b : getr (ms_regs ms) 26 = getr rg 26) by cb4_keep HS.
  assert (K10b : getr (ms_regs ms) 24 = getr rg 10) by cb4_keep HS.
  assert (K24b : getr (ms_regs ms) 24 = w64 0) by (rewrite K10b; exact R10).
  clear HFr HG.
  pmkst HS.
  lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
    change n with (CRT_PC_B + CRT_O2_OFF_B) end.
  apply (HO2 fxk lyc Sc Hpc Wc (ms_mem ms) _ kj pos Dc Lamc peakc
    (WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB))
    (ms_regs ms) msl cset 0).
  rewrite HF.
  split; [rewrite K26b; exact R26|].
  subst ranw. exists Dc, 0.
  (* the failed write skips parse_noting: the live state at the W budget 64 steps up to L0's 66
     (Crt102KitB.cb4_live_mono; wbudget is an upper bound, so only room is given up, and from L0 on nothing asks
     for room) *)
  assert (Hup : (prh_wk F_round_trip_text + prh_wk F_round_trip_text <= prh_wk F_check_round_trip)%nat)
    by (pose proof crt4_kb_pn as Hk; clear - Hk; lia).
  refine {| crt_at_L0_B_obj := Et; crt_at_L0_B_frm_zero := HFZ; crt_at_L0_B_fregs := HFK;
            crt_at_L0_B_live := cb4_live_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 Hup;
            crt_at_L0_B_dregs := HDR2; crt_at_L0_B_saved := K24b;
            crt_at_L0_B_flag := _; crt_at_L0_B_sp_back := SPB; crt_at_L0_B_sp_shn := SPSHN;
            crt_at_L0_B_sp_pn := SPPN; crt_at_L0_B_sp_n := SPN; crt_at_L0_B_doc_align := Hd8;
            crt_at_L0_B_doc_open := RAdoc; crt_at_L0_B_back_open := RAback; crt_at_L0_B_v_open := RAv;
            crt_at_L0_B_cset_range := Hcset; crt_at_L0_B_cset_mod := HcsetAt; crt_at_L0_B_copy := HND;
            crt_at_L0_B_copy_fd := HFD; crt_at_L0_B_copy_tblk := HCP eq_refl; crt_at_L0_B_copy_fo := HFO;
            crt_at_L0_B_copy_depth := HDP; crt_at_L0_B_outcome := _ |}.
  { rewrite K21b. exact R21. }
  exists ok. split; [exact HOKS|].
  left. split; [reflexivity|]. split; [exact Hfail | reflexivity].
- (* a0 <> 0: the text is in a block; the own test, then fuzz_alloc_ran_out () *)
  rewrite branch_eq_U, !ts_U0, U_SLit, A42 in Hc. rewrite YP0m.zcanon_small in Hc by lia.
  apply Z.eqb_neq in Hc.
  destruct Harm as [(Hfail0 & Hqne & Hnin & Hlenb & Hbytes & Hposw) | (_ & Hq0)]; [|exfalso; exact (Hc Hq0)].
  assert (Hinq : In (q, WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB))
                    Lamc).
  { apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq q 0) Hqne). left. reflexivity. }
  paj_run_to_tok_x (RUNTO WSJ) HS HJ SHOK (0, 0) (CRT_PC_B + 708).
  { apply awr_ok_nil. }
  apply frame_of_read_only in HF; [|vm_compute; reflexivity].
  rewrite EMA in HF.
  rewrite HF in HJ.
  pose proof (cb4_live_rejournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ HBJ) as HL2.
  assert (KR2 : forall rr : bv 5, In rr CB4_DREGS -> getr (ms_regs ms) rr = getr rg rr).
  { intros rr Hr. unfold CB4_DREGS in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [cb4_keep HS |]). destruct Hr. }
  assert (HDR2 : dregsB (ms_regs ms) (frame_addr lyc CRT_CID pos))
    by (apply (cb4_dregs_eq rg); [exact HDR | exact KR2]).
  assert (K21b : getr (ms_regs ms) 21 = getr rg 21) by cb4_keep HS.
  assert (K26b : getr (ms_regs ms) 26 = getr rg 26) by cb4_keep HS.
  assert (K10b : getr (ms_regs ms) 24 = getr rg 10) by cb4_keep HS.
  assert (K24b : getr (ms_regs ms) 24 = w64 q) by (rewrite K10b; exact R10).
  clear HFr HG.
  pmkst HS.
  lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
    change n with (CRT_PC_B + 708) end.
  rewrite HF. clear HF.
  refine (cb4_ro fxk 708 720 Wc memc _ lyc Sc Hpc kj pos _ Lamc peakc _ ranw (ms_regs ms) HFZ
    (or_introl (conj eq_refl eq_refl)) HL2 HDR2 ltac:(rewrite K26b; exact R26) _).
  intros rg2 ly2 W2 mem2 md2 k1 (WS2 & HJ2 & HB2) HL3 EF HKEEP HKR HR10.
  assert (HEI2 : img_env VAL A_LIM (TEB regs rg2 [])) by apply te_env.
  unfold crt_cfg.
  assert (HS2 : @st_ok_pi SEGS VAL fxk (TEB regs rg2 [])
    (mkSS (CRT_PC_B + 720) cur_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W2) (@YK11.mkst fxk rg2 (Z_to_bv 64 (BASE + (CRT_PC_B + 720))) mem2 (YK11.seg_rom SEGS)))).
  { apply (@ts_st_ok fxk); [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
  assert (SHOK2 : sh_ok SEGS (SLit 0) [] (TEB regs rg2 []) (mrestrict (w_H W2) mem2)) by apply Forall_nil.
  assert (A42b : bv_unsigned (ew (TEB regs rg2 []) 42) = ranw).
  { rewrite (te_curB regs rg2 _ 10%bv 10) by reflexivity. rewrite HR10. unfold w64. apply unsigned_lit_small.
    destruct Hranw; lia. }
  assert (K24c : getr rg2 24 = w64 q) by (rewrite (HKR 24%bv ltac:(cbv; tauto)); exact K24b).
  assert (K21c : getr rg2 21 = w64 1) by (rewrite (HKR 21%bv ltac:(cbv; tauto)); rewrite K21b; exact R21).
  assert (K26c : getr rg2 26 = w64 (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B))
    by (rewrite (HKR 26%bv ltac:(cbv; tauto)); rewrite K26b; exact R26).
  assert (HDR3 : dregsB rg2 (frame_addr lyc CRT_CID pos)).
  { apply (cb4_dregs_eq (ms_regs ms)); [exact HDR2|]. intros r0 Hr0. apply HKR.
    unfold CB4_DREGS in Hr0. unfold CB4_KEEP. cbn [In] in Hr0 |- *. tauto. }
  rename ms into msB.
  psrr_branch_tok RUN BR HS2 SHOK2 (0, 0).
  + (* ran = 1 is refuted: pj_write left g_ran_out = 0 (crt4_at_Wr) *)
    rewrite branch_ne_U, !ts_U0, U_SLit, A42b in Hc0. rewrite YP0m.zcanon_small in Hc0 by (destruct Hranw; lia).
    apply negb_true_iff, Z.eqb_neq in Hc0. exfalso. exact (Hc0 Er0).
  + (* ran = 0: S (+0x2d4) *)
    rewrite branch_ne_U, !ts_U0, U_SLit, A42b in Hc0. rewrite YP0m.zcanon_small in Hc0 by (destruct Hranw; lia).
    apply negb_false_iff, Z.eqb_eq in Hc0. clear A42b. subst ranw.
    paj_run_to_tok_x (RUNTO WS2) HS2 HJ2 SHOK2 (0, 0) (CRT_PC_B + CRT4_S_OFF_B).
    { apply awr_ok_nil. }
    apply frame_of_read_only in HF; [|vm_compute; reflexivity].
    rewrite HF in HJ2.
    pose proof (cb4_live_rejournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL3 HJ2 HB2) as HL4.
    assert (KR3 : forall rr : bv 5, In rr CB4_DREGS -> getr (ms_regs ms) rr = getr rg2 rr).
    { intros rr Hr. unfold CB4_DREGS in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [cb4_keep HS2 |]). destruct Hr. }
    assert (HDR4 : dregsB (ms_regs ms) (frame_addr lyc CRT_CID pos))
      by (apply (cb4_dregs_eq rg2); [exact HDR3 | exact KR3]).
    assert (K24d : getr (ms_regs ms) 24 = w64 q) by (rewrite <- K24c; cb4_keep HS2).
    assert (K21d : getr (ms_regs ms) 21 = w64 1) by (rewrite <- K21c; cb4_keep HS2).
    assert (K26d : getr (ms_regs ms) 26 = w64 (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B))
      by (rewrite <- K26c; cb4_keep HS2).
    clear HFr HG.
    pmkst HS2.
    lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
      change n with (CRT_PC_B + CRT4_S_OFF_B) end.
    apply (HSn fxk ly2 Sc Hpc W2 (ms_mem ms) _ (kj + k1) pos Dc Lamc peakc (ms_regs ms) msl cset).
    rewrite HF.
    exists ok, q.
    split; [|split; [exact Hqne | exact K24d]].
    split; [exact Et|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact HOKS|].
    split; [exact HL4|]. split; [rewrite EF; exact HDR4|]. split; [exact K21d|]. split; [exact K26d|].
    split; [rewrite EF; exact (cb4_km_spill lyc Sc Wc memc W2 mem2 CRT_SP_BACK _ HKEEP
      ltac:(unfold CRT_SP_BACK; lia) SPB)|].
    split; [exact (cb4_km_spill lyc Sc Wc memc W2 mem2 CRT_SP_SHN_B _ HKEEP
      ltac:(unfold CRT_SP_SHN_B; lia) SPSHN)|].
    split; [exact (cb4_km_spill lyc Sc Wc memc W2 mem2 CRT_SP_PN_B _ HKEEP
      ltac:(unfold CRT_SP_PN_B; lia) SPPN)|].
    split; [exact (cb4_km_spill lyc Sc Wc memc W2 mem2 CRT_SP_N_B _ HKEEP
      ltac:(unfold CRT_SP_N_B; lia) SPN)|].
    split; [exact Hd8|].
    split; [exact (cb4_km_ra_doc [(CRT_CID, pos)] lyc Sc Hpc Wc memc _ _ W2 mem2 HJ HKEEP RAdoc)|].
    split; [rewrite EF; exact (cb4_km_ra_slot lyc Sc Wc memc W2 mem2 pos CRT_OFF_BACK HKEEP Hin3 F32
      ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) RAback)|].
    split; [rewrite EF; exact (cb4_km_ra_slot lyc Sc Wc memc W2 mem2 pos CRT_OFF_V HKEEP Hin3 F32
      ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) RAv)|].
    split; [exact Hcset|]. split; [exact HcsetAt|].
    split; [rewrite EF; exact (cb4_km_nodeR lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc _ 0 0 W2 mem2 Dc
      (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) tcB HL HKEEP HDL'
      (cb4_in_frame_slot lyc Sc pos CRT_OFF_COPY Hin3 ltac:(unfold CRT_OFF_COPY; lia)
         ltac:(unfold CRT_OFF_COPY; lia)) HND)|].
    split; [exact HCP|]. split; [exact HDP|].
    split.
    { destruct HFO as (Fc & HFc & EFc). exists Fc. split; [|exact EFc].
      rewrite EF; exact (cb4_km_foR lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc _ 0 0 W2 mem2 Dc
        (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) DOC_D Fc HL HKEEP HDL'
        (cb4_in_frame_slot lyc Sc pos CRT_OFF_COPY Hin3 ltac:(unfold CRT_OFF_COPY; lia)
           ltac:(unfold CRT_OFF_COPY; lia)) HFc). }
    split; [exact HBS|].
    left. split; [exact Hfail0|]. split; [exact Hqne|]. split; [exact Hnin|]. split; [exact Hlenb|].
    split; [|exact Hposw].
    exact (cb4_km_bytes lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc _ 0 0 W2 mem2 q _ (tbB ++ [0])
      HL HKEEP Hinq ltac:(rewrite length_app; cbn [length]; lia) Hbytes).
Qed.

(* ======================================================================================================== *)
(* PART B, SECOND LEMMA. O2 (+0x2f0): `lbu a0, 0x2d0(s10)` reads own = 0, `bnez` falls through,
   fuzz_alloc_ran_out () at +0x2f8 answers the ledger's ran, 0 in the L0 state, and `beqz a0, +0x478` takes L0. *)
Lemma crt4_lane_O2 : CRTB_L0 -> CRT4_O2.
Proof.
intros HL0 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg msl cset saved (R26 & Dx & rcv & HatL0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cb4_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
assert (HEI : img_env VAL A_LIM (TEB regs rg [])) by apply te_env.
pose (RUN := @Crt102Kit.crt_run_xw fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS).
pose (RUNTO := @Crt102Kit.crt_run_to_xw fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS).
pose (BR := YSRrG.paj_branchR (fx := fxk) (rc := rc) (L := B_prog_listing) (PI := PA) RZW).
- pose proof (crt_at_L0_B_obj HatL0) as Et. pose proof (crt_at_L0_B_frm_zero HatL0) as HFZ.
  pose proof (crt_at_L0_B_fregs HatL0) as HFK. pose proof (crt_at_L0_B_live HatL0) as HLv.
  pose proof (crt_at_L0_B_dregs HatL0) as HDR. pose proof (crt_at_L0_B_saved HatL0) as R24.
  pose proof (crt_at_L0_B_flag HatL0) as R21. pose proof (crt_at_L0_B_sp_back HatL0) as SPB.
  pose proof (crt_at_L0_B_sp_shn HatL0) as SPSHN. pose proof (crt_at_L0_B_sp_pn HatL0) as SPPN.
  pose proof (crt_at_L0_B_sp_n HatL0) as SPN. pose proof (crt_at_L0_B_doc_align HatL0) as Hd8.
  pose proof (crt_at_L0_B_doc_open HatL0) as RAdoc. pose proof (crt_at_L0_B_back_open HatL0) as RAback.
  pose proof (crt_at_L0_B_v_open HatL0) as RAv. pose proof (crt_at_L0_B_cset_range HatL0) as Hcset.
  pose proof (crt_at_L0_B_cset_mod HatL0) as HcsetAt. pose proof (crt_at_L0_B_copy HatL0) as HNDc.
  pose proof (crt_at_L0_B_copy_fd HatL0) as HFDc. pose proof (crt_at_L0_B_copy_tblk HatL0) as HCPc.
  pose proof (crt_at_L0_B_copy_fo HatL0) as HFOc. pose proof (crt_at_L0_B_copy_depth HatL0) as HDPc.
  destruct (crt_at_L0_B_outcome HatL0) as (okw & HOKS & Harm). clear HatL0.
  cb4_rd_live HLv WSJ HJ HBJ HSD HPL HPB HAP HSV HFRM HSPF HCR HCH HMNl.
  cb4_rd_side HSD HLED Hpk HROOM HRO HNDdoc HDL.
  destruct (cb4_ff _ _ _ _ _ _ _ _ HJ) as (Hin3 & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
  assert (HDxL : forall bk, In bk Dx -> In bk Lamc).
  { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hbk. }
  assert (HDcx : forall bk, In bk Dc -> In bk Dx).
  { intros bk Hbk.
    destruct Harm as [(Hs0 & Hf & EDx) | (Hs0 & Hf & okr & res & tr & Hrun & Hoks2 & Hcnt2 & Hgr & Hm)].
    - rewrite EDx. exact Hbk.
    - destruct res as [tv|].
      + destruct Hm as (Hrc & Hpos & Dback & EDx & HNb). rewrite EDx. apply in_or_app. right. right. exact Hbk.
      + destruct Hm as (Hrc & EDx). rewrite EDx. right. exact Hbk. }
  assert (HDcL : forall bk, In bk Dc -> In bk Lamc) by (intros bk Hbk; apply HDxL; apply HDcx; exact Hbk).
  refine (cb4_ro fxk 752 764 Wc memc mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc 0 rg HFZ
    (or_intror (conj eq_refl eq_refl)) HLv HDR R26 _).
  intros rg2 ly2 W2 mem2 md2 k1 (WS2 & HJ2 & HB2) HL2 EF HKEEP HKR HR10.
  assert (HEI2 : img_env VAL A_LIM (TEB regs rg2 [])) by apply te_env.
  unfold crt_cfg.
  assert (HS2 : @st_ok_pi SEGS VAL fxk (TEB regs rg2 [])
    (mkSS (CRT_PC_B + 764) cur_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W2) (@YK11.mkst fxk rg2 (Z_to_bv 64 (BASE + (CRT_PC_B + 764))) mem2 (YK11.seg_rom SEGS)))).
  { apply (@ts_st_ok fxk); [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
  assert (SHOK2 : sh_ok SEGS (SLit 0) [] (TEB regs rg2 []) (mrestrict (w_H W2) mem2)) by apply Forall_nil.
  assert (A42 : bv_unsigned (ew (TEB regs rg2 []) 42) = 0).
  { rewrite (te_curB regs rg2 _ 10%bv 10) by reflexivity. rewrite HR10. unfold w64.
    apply unsigned_lit_small. lia. }
  assert (HDR3 : dregsB rg2 (frame_addr lyc CRT_CID pos)).
  { apply (cb4_dregs_eq rg); [exact HDR|]. intros r0 Hr0. apply HKR.
    unfold CB4_DREGS in Hr0. unfold CB4_KEEP. cbn [In] in Hr0 |- *. tauto. }
  assert (K24c : getr rg2 24 = w64 saved) by (rewrite (HKR 24%bv ltac:(cbv; tauto)); exact R24).
  assert (K21c : getr rg2 21 = w64 (if saved =? 0 then 1 else if rcv =? 0 then 0 else 1))
    by (rewrite (HKR 21%bv ltac:(cbv; tauto)); exact R21).
  psrr_branch_tok RUN BR HS2 SHOK2 (0, 0).
  + (* a0 = 0: the L0 state *)
    paj_run_to_tok_x (RUNTO WS2) HS2 HJ2 SHOK2 (0, 0) (CRT_PC_B + CRT_L0_OFF_B).
    { apply awr_ok_nil. }
    apply frame_of_read_only in HF; [|vm_compute; reflexivity].
    rewrite HF in HJ2.
    pose proof (cb4_live_rejournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 HJ2 HB2) as HL3.
    assert (KR3 : forall rr : bv 5, In rr CB4_DREGS -> getr (ms_regs ms) rr = getr rg2 rr).
    { intros rr Hr. unfold CB4_DREGS in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [cb4_keep HS2 |]). destruct Hr. }
    assert (HDR4 : dregsB (ms_regs ms) (frame_addr lyc CRT_CID pos))
      by (apply (cb4_dregs_eq rg2); [exact HDR3 | exact KR3]).
    assert (K24d : getr (ms_regs ms) 24 = w64 saved) by (rewrite <- K24c; cb4_keep HS2).
    assert (K21d : getr (ms_regs ms) 21 = w64 (if saved =? 0 then 1 else if rcv =? 0 then 0 else 1))
      by (rewrite <- K21c; cb4_keep HS2).
    clear HFr HG.
    pmkst HS2.
    lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
      change n with (CRT_PC_B + CRT_L0_OFF_B) end.
    apply (HL0 fxk ly2 Sc Hpc W2 (ms_mem ms) _ (kj + k1) pos Dc Dx Lamc peakc cntc (ms_regs ms) msl cset saved rcv).
    rewrite HF.
    refine {| crt_at_L0_B_obj := Et; crt_at_L0_B_frm_zero := HFZ; crt_at_L0_B_fregs := HFK;
              crt_at_L0_B_live := HL3; crt_at_L0_B_dregs := _; crt_at_L0_B_saved := K24d; crt_at_L0_B_flag := K21d;
              crt_at_L0_B_sp_back := _; crt_at_L0_B_sp_shn := _; crt_at_L0_B_sp_pn := _; crt_at_L0_B_sp_n := _;
              crt_at_L0_B_doc_align := Hd8; crt_at_L0_B_doc_open := _; crt_at_L0_B_back_open := _;
              crt_at_L0_B_v_open := _; crt_at_L0_B_cset_range := Hcset; crt_at_L0_B_cset_mod := HcsetAt;
              crt_at_L0_B_copy := _; crt_at_L0_B_copy_fd := _; crt_at_L0_B_copy_tblk := HCPc;
              crt_at_L0_B_copy_fo := _; crt_at_L0_B_copy_depth := HDPc; crt_at_L0_B_outcome := _ |}.
    { rewrite EF; exact HDR4. }
    { rewrite EF; exact (cb4_km_spill lyc Sc Wc memc W2 mem2 CRT_SP_BACK _ HKEEP
        ltac:(unfold CRT_SP_BACK; lia) SPB). }
    { exact (cb4_km_spill lyc Sc Wc memc W2 mem2 CRT_SP_SHN_B _ HKEEP ltac:(unfold CRT_SP_SHN_B; lia) SPSHN). }
    { exact (cb4_km_spill lyc Sc Wc memc W2 mem2 CRT_SP_PN_B _ HKEEP ltac:(unfold CRT_SP_PN_B; lia) SPPN). }
    { exact (cb4_km_spill lyc Sc Wc memc W2 mem2 CRT_SP_N_B _ HKEEP ltac:(unfold CRT_SP_N_B; lia) SPN). }
    { exact (cb4_km_ra_doc [(CRT_CID, pos)] lyc Sc Hpc Wc memc _ _ W2 mem2 HJ HKEEP RAdoc). }
    { rewrite EF; exact (cb4_km_ra_slot lyc Sc Wc memc W2 mem2 pos CRT_OFF_BACK HKEEP Hin3 F32
        ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) RAback). }
    { rewrite EF; exact (cb4_km_ra_slot lyc Sc Wc memc W2 mem2 pos CRT_OFF_V HKEEP Hin3 F32
        ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) RAv). }
    { rewrite EF; exact (cb4_km_nodeR lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 0 W2 mem2 Dc
        (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) tcB HLv HKEEP HDcL
        (cb4_in_frame_slot lyc Sc pos CRT_OFF_COPY Hin3 ltac:(unfold CRT_OFF_COPY; lia)
           ltac:(unfold CRT_OFF_COPY; lia)) HNDc). }
    { rewrite EF; exact (cb4_km_fdR lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 0 W2 mem2 Dc
        (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) DOC_D HLv HKEEP HDcL
        (cb4_in_frame_slot lyc Sc pos CRT_OFF_COPY Hin3 ltac:(unfold CRT_OFF_COPY; lia)
           ltac:(unfold CRT_OFF_COPY; lia)) HFDc). }
    { destruct HFOc as (Fc & HFc & EFc). exists Fc. split; [|exact EFc].
      rewrite EF; exact (cb4_km_foR lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 0 W2 mem2 Dc
        (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) DOC_D Fc HLv HKEEP HDcL
        (cb4_in_frame_slot lyc Sc pos CRT_OFF_COPY Hin3 ltac:(unfold CRT_OFF_COPY; lia)
           ltac:(unfold CRT_OFF_COPY; lia)) HFc). }
    exists okw. split; [exact HOKS|].
    destruct Harm as [(Hs0 & Hf & EDx) | (Hs0 & Hf & okr & res & tr & Hrun & Hoks2 & Hcnt2 & Hgr & Hm)].
    * left. split; [exact Hs0|]. split; [exact Hf | exact EDx].
    * right. split; [exact Hs0|]. split; [exact Hf|]. exists okr, res, tr.
      split; [exact Hrun|]. split; [exact Hoks2|]. split; [exact Hcnt2|]. split; [exact Hgr|].
      destruct res as [tv|].
      -- destruct Hm as (Hrc & Hpos & Dback & EDx & HNb & HTb & (Fb & HFb & EFb)).
         assert (HDbL : forall bk, In bk Dback -> In bk Lamc)
           by (intros bk Hbk; apply HDxL; rewrite EDx; apply in_or_app; left; exact Hbk).
         assert (HinB : ck_in_frame lyc Sc (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56)
           by exact (cb4_in_frame_slot lyc Sc pos CRT_OFF_BACK Hin3 ltac:(unfold CRT_OFF_BACK; lia)
              ltac:(unfold CRT_OFF_BACK; lia)).
         split; [exact Hrc|]. split; [exact Hpos|]. exists Dback. split; [exact EDx|].
         rewrite EF. split; [|split; [exact HTb|]].
         ++ exact (cb4_km_nodeR lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 0 W2 mem2 Dback
              (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) tv HLv HKEEP HDbL HinB HNb).
         ++ exists Fb. split; [|exact EFb].
            exact (cb4_km_foR lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 0 W2 mem2 Dback
              (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) DOC_D Fb HLv HKEEP HDbL HinB HFb).
      -- exact Hm.
  + (* a0 = 0 makes `beqz` taken: this arm is impossible *)
    exfalso. rewrite branch_eq_U, !ts_U0, U_SLit, A42 in Hc. rewrite YP0m.zcanon_small in Hc by lia.
    apply Z.eqb_neq in Hc. exact (Hc eq_refl).
Qed.


(* ======== PART C of this row (Crt102B_T4C.v, merged into this file) ======== *)

(* ======================================================================================================== *)
(* PART C (crt4_lane_S): the segment S (+0x2d4) -> O2 (+0x2f0): the strlen call, the argument set-up, the
   parse_noting call, `snez s5, a0`. Helpers first. *)

(* bytes outside the image that a keep leaves alone are the same bytes, writability included (Crt102Kit.v
   crt102rw_mr_of_aview / crt102rw_agree_of_aview, which this file does not Require) *)
Lemma c4_mr_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> aview SEGS H' m' a = aview SEGS H m a ->
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn E. unfold aview, mbyte in E.
rewrite (seg_rom_none SEGS a Ha Hn) in E.
destruct (mrestrict H' m' (Z_to_bv 64 a)) as [b'|]; destruct (mrestrict H m (Z_to_bv 64 a)) as [b|];
  cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma c4_agree_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) (X : Z -> Prop),
  (forall y, X y -> 0 <= y < 2 ^ 64 /\ ~ in_img SEGS y /\ aview SEGS H' m' y = aview SEGS H m y) ->
  pj_agreeR SEGS (mrestrict H m) (mrestrict H' m') X.
Proof.
intros H H' m m' X HX y Hy. destruct (HX y Hy) as (Hr & Hn & E).
pose proof (c4_mr_of_aview H H' m m' y Hr Hn E) as Em.
split; [unfold mbyte; rewrite Em; reflexivity|].
intros Hw. unfold writable_at, wview in *. rewrite Em. exact Hw.
Qed.
Lemma c4_apresent_vis : forall (H : word -> bool) m a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
(* a covering hull is a hull of each sub-range (FuzzStrdupB.v sd_hull_sub) *)
Lemma c4_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (YCbq.shadow_mono p d Hpd) as M1.
pose proof (YCbq.shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia | apply Z.div_le_mono; lia]).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* ---- THE STACK WINDOW of a call made at sp1: no byte this row cares about is in it (every such byte is below
   alloc_ceiling - application memory, the shadow, the image - or at or above sp1 - the spills and the saved
   words) ---- *)
Lemma c4_nw_stk : forall a, a < YM05.alloc_ceiling \/ sp1 <= a -> ~ (sp1 - 2 * ESTACK <= a < sp1).
Proof.
intros a Ha. pose proof cb4_sp as (_ & Hceil & _ & Hs1 & _). pose proof (YM05.alloc_ceiling_val).
unfold ESTACK. lia.
Qed.
(* every shadow byte of an address below 2 ^ 47 is far below alloc_ceiling (the shadow lives in [SHADOW_OFF,
   SHADOW_OFF + 2 ^ 44), which the ceiling's own range clears) *)
Lemma c4_shadow_lo : forall a, 0 <= a <= 2 ^ 47 -> 0 <= SHADOW_OFF + a / 8 /\ SHADOW_OFF + a / 8 + 8 < YM05.alloc_ceiling.
Proof.
intros a Ha. pose proof (YM05.alloc_ceiling_val).
assert (a / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
assert (0 <= a / 8) by (apply Z.div_pos; lia).
unfold SHADOW_OFF. lia.
Qed.

(* ---- THE LIVE STATE ACROSS A CALL THAT ONLY WROTE ITS OWN STACK WINDOW (the strlen wrapper, whose rule keeps
   every byte outside [sp1 - 2 * ESTACK, sp1) and gives the journal back at the same k) ---- *)
Lemma c4_live_stk : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc {kbg : nat}
    {WS : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc' mdc' kj' WS -> YCbqGwild.wbudget [] kbg WS ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc') ->
  liveB kbg lyc Sc Hpc Wc memc' mdc' kj' pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc kbg WS HL HJ' HB' Hag HMN'.
cb4_rd_live HL WSj HJ HBj HSD HPL HPB HAP HSV HFRM HSPF HCR HCH HMNl.
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ') as (_ & _ & _ & _ & _ & Ffr' & Fsh').
pose proof HJ as (HARc & _).
set (F := frame_addr lyc CRT_CID pos) in *.
pose proof cb4_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cb4_doc_home as (Hd1 & Hd2 & Hd3 & Hd4).
(* K: a byte below alloc_ceiling; Ku: a byte at or above sp1 *)
assert (K : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hag; [lia | apply c4_nw_stk; left; lia]. }
assert (Ku : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hag; [lia | apply c4_nw_stk; right; lia]. }
assert (Kmb : forall a, 0 <= a < YM05.alloc_ceiling ->
  mbyte SEGS (mrestrict (w_H Wc) memc') a = mbyte SEGS (mrestrict (w_H Wc) memc) a).
{ intros a Ha. apply prh_mbyte_of_aview. exact (K a Ha). }
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity.
assert (Kblk : forall a k, In (a, k) Lamc -> 0 <= k /\ forall i, 0 <= i < k + 16 ->
  0 <= a - 16 + i < YM05.alloc_ceiling).
{ intros a k Hk. pose proof (crt_side_ledger HSD) as HLED.
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc a k _ _ HLED Hk) as (Hk0 & Hab & _).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & Bapp & _).
  rewrite Hch16 in *.
  assert (Hrs : k + 16 <= req_size (k + 16)) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
  split; [exact Hk0|]. intros i Hi. lia. }
refine {| crt_live_journal := ex_intro _ WS (conj HJ' HB'); crt_live_side := _; crt_live_lam_perm := HPL;
          crt_live_blocks_perm := HPB;
          crt_live_dx_apart := HAP; crt_live_saved := _; crt_live_frame := _; crt_live_fspill := _;
          crt_live_copy_open := _; crt_live_copy_hull := _; crt_live_memnorm := HMN' |}.
{ cb4_rd_side HSD HLED HPK HRL HRO HDOC HDL.
  refine {| crt_side_ledger := _; crt_side_peak := HPK; crt_side_room := HRL; crt_side_arodata := _;
            crt_side_doc := _; crt_side_doc_blocks := HDL |}.
  { apply (prh_ledger_kept_aview B lyc Sc Hpc Wc memc lyc Sc Hpc Wc memc' Lamc peakc cntc SIZE_MAXZ ranc _ _ HLED).
    - intros a Ha. pose proof (@pa_segs_low _ _ PA a (pst_in_img_B a Ha)) as Hl. apply K. unfold kLowMemEnd in Hl. lia.
    - intros a k i Hk Hi. destruct (Kblk a k Hk) as (Hk0 & Hb). rewrite Hch16.
      apply K. exact (Hb i ltac:(lia)).
    - intros a k _ Hab. exact Hab.
    - apply Permutation_refl. }
  { intros a Hro Ho He. pose proof (@pa_segs_low _ _ PA a (cb4_ro_img a Hro)) as Hl.
    rewrite K; [exact (HRO a Hro Ho He) | unfold kLowMemEnd in Hl; lia]. }
  apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') (prh_lin Lamc) doc D HDOC).
  apply (c4_agree_of_aview (w_H Wc) (w_H Wc) memc memc').
  intros y Hy.
  assert (Hyr : 0 <= y < YM05.alloc_ceiling).
  { destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
    - lia.
    - unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
      destruct (Kblk b kb (HDL _ Hb)) as (Hk0 & Hbb).
      destruct (Hbb (y - (b - 16)) ltac:(lia)) as (H1 & H2). lia. }
  split; [lia|]. split.
  - intros Hi. pose proof (@pa_segs_low _ _ PA y Hi) as Hl.
    destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
    + pose proof HTREE as (_ & _ & _ & (_ & (cid & pos' & Hfin & Hfa1 & Hfa2) & _)).
      exact (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos' y cb4_ar0 Hfin ltac:(lia) Hi).
    + unfold pj_holdsR in Hy. cbn [fst snd] in Hy.

      destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDL _ Hb))
        as (Hk0 & Hab & _).
      rewrite Hch16 in Hab.
      assert (Hrs : kb + 16 <= req_size (kb + 16)) by (unfold req_size; destruct (Z.eqb_spec (kb + 16) 0); lia).
      exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc (b - 16) (kb + 16) y HARc Hab ltac:(lia) Hi).
  - apply K. exact Hyr. }
{ intros j Hj. apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc' _ 8 _); [|exact (HSV j Hj)].
  intros i Hi. apply Ku. lia. }
{ pose proof (crt_frame_flag_word HFRM) as Hfl.
  refine {| crt_frame_listed := crt_frame_listed HFRM; crt_frame_flag_word := _; crt_frame_present := _ |}.
  - rewrite <- Hfl. apply ts_rdword_keep. intros j Hj. rewrite cb4_fb. apply K. lia.
  - intros a Ha. rewrite cb4_fb in Ha. exact (proj1 (Ffr' a Ha)). }
{ apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc' _ 8 _); [|exact HSPF].
  intros i Hi. apply Ku. unfold CRT_SP_F. lia. }
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HCR].
  intros y Hy. unfold CRT_OFF_COPY in Hy. unfold shadow_of_addr.
  destruct (c4_shadow_lo y ltac:(lia)) as (Hs0 & Hs2). apply K. lia. }
{ intros s Hs. rewrite K; [exact (HCH s Hs)|].
  destruct (c4_shadow_lo (F + CRT_OFF_COPY) ltac:(unfold CRT_OFF_COPY; lia)) as (G1 & G2).
  destruct (c4_shadow_lo (F + CRT_OFF_COPY + 56 - 1) ltac:(unfold CRT_OFF_COPY; lia)) as (G3 & G4).
  unfold shadow_addr in Hs.
  set (u := SHADOW_OFF + (F + CRT_OFF_COPY) / 8) in *.
  set (v := SHADOW_OFF + (F + CRT_OFF_COPY + 56 - 1) / 8) in *.
  pose proof (Z.div_mod u 8 ltac:(lia)). pose proof (Z.mod_pos_bound u 8 ltac:(lia)).
  pose proof (Z.div_mod v 8 ltac:(lia)). pose proof (Z.mod_pos_bound v 8 ltac:(lia)). lia. }
Qed.

(* ---- the text block (q, cap) the walk holds: its bounds, the strlen rule's range and shadow premises over its
   first n + 1 bytes, and its bytes' presence ---- *)
Lemma c4_blk_facts : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc qq cap n {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  In (qq, cap) Lamc -> 0 <= n -> n + 1 <= cap ->
  4096 <= qq /\ qq + cap <= YM05.alloc_ceiling /\ in_app qq cap /\ YGcallMx.amem_range8 qq (n + 1) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF qq (n + 1) /\
  shadow_hull_vis (aview SEGS (w_H Wc) memc) qq (n + 1) /\
  (forall a, qq + n < a < qq + n - (qq + n) mod 8 + 8 -> aview SEGS (w_H Wc) memc a <> None) /\
  (forall a, qq <= a < qq + cap -> apresent (w_H Wc) memc a).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc qq cap n kbg HL Hin Hn0 Hnc.
destruct (crt_live_journal HL) as (? & (HARc & _) & _). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc qq cap _ _ HLED Hin)
  as (Hk0 & Hab & Hhp & Hal16 & Hhdr).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity. rewrite Hch16 in *.
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (Hm16 & B4096 & Bce & Bapp & Bpr & _).
assert (Hrs : req_size (cap + 16) = cap + 16) by (unfold req_size; destruct (Z.eqb_spec (cap + 16) 0); lia).
rewrite Hrs in Bce, Bapp, Bpr.
destruct (alx_hshadow _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab Hhp) as (Hbs & Hhu).
rewrite Hrs in Hbs, Hhu.
replace (qq - 16 + 16) with qq in Hbs, Hhu by lia.
replace (cap + 16 - 16) with cap in Hbs, Hhu by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [lia|]. split; [apply (in_app_sub _ _ _ _ Bapp); lia|].
split.
{ unfold YGcallMx.amem_range8. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bapp.
  rewrite C3, C4, C5. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia. }
split; [eapply block_shadow_range; [exact Hbs | lia | lia]|].
split; [apply (c4_hull_sub _ qq cap qq (n + 1) (Hhu ltac:(lia))); lia|].
split.
{ intros a Ha.
  pose proof (Z.div_mod (qq + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (qq + n) 8 ltac:(lia)).
  destruct (Z_lt_le_dec a (qq + cap)) as [Hlt|Hge].
  - apply c4_apresent_vis. exact (proj1 (Bpr a ltac:(lia))).
  - apply (alx_blocks_tail _ _ _ LAWS lyc Sc Hpc Wc memc mdc (qq - 16) (cap + 16) a HARc Hab).
    rewrite Hrs.
    assert (D1 : (qq + n) / 8 * 8 <= (qq + cap - 1) / 8 * 8)
      by (apply Z.mul_le_mono_nonneg_r; [lia | apply Z.div_le_mono; lia]).
    assert (E7 : (qq - 16 + (cap + 16) + 7) / 8 = (qq + cap - 1) / 8 + 1).
    { replace (qq - 16 + (cap + 16) + 7) with ((qq + cap - 1) + 1 * 8) by lia. apply Z.div_add. lia. }
    rewrite E7. lia. }
intros a Ha. exact (proj1 (Bpr a ltac:(lia))).
Qed.

(* ---- the string premises of the strlen rule, from the bytes the walk holds (FuzzStrdupB.v sd_garr8_aview /
   sd_first_byte / sd_src_ok, whose file this one does not Require) ---- *)
Lemma c4_garr8_aview : forall (Wc : world SEGS) m p l j, garr8 SEGS (mrestrict (w_H Wc) m) p l -> (j < length l)%nat ->
  aview SEGS (w_H Wc) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros Wc m p l j H Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.
Lemma c4_first_byte : forall (Wc : world SEGS) m p l, garr8 SEGS (mrestrict (w_H Wc) m) p (l ++ [0]) ->
  Forall (fun c => c <> 0) l ->
  first_byte SEGS Wc m p (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)).
Proof.
intros Wc m p l Hg Hnz. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) l 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (c4_garr8_aview Wc m p (l ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn [length]; lia).
    rewrite app_nth1 by lia. reflexivity.
  + apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
- intros _.
  rewrite (c4_garr8_aview Wc m p (l ++ [0]) (length l) Hg) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma c4_src_ok : forall (Wc : world SEGS) rgx m p l, garr8 SEGS (mrestrict (w_H Wc) m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ (spZ rgx - ESTACK <= a < spZ rgx)) ->
  src_ok SEGS Wc rgx m p (Z.of_nat (length l)).
Proof.
intros Wc rgx m p l H Hw a Ha. split; [|exact (Hw a Ha)].
replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (c4_garr8_aview Wc m p l (Z.to_nat (a - p)) H) by lia. discriminate.
Qed.

(* ---- a live harness block and a live fake frame are apart (the separation law's cross pairs) ---- *)
Lemma c4_blk_frame_disj : forall lyc Sc Hpc Wc memc mdc a k cid pos',
  ARx lyc Sc Hpc Wc memc mdc -> In (a, k) (ablocks B lyc Sc) -> In (cid, pos') (frames Sc) ->
  zdisjoint (a, req_size k) (frame_addr lyc cid pos', fs_frame_bytes cid).
Proof.
intros lyc Sc Hpc Wc memc mdc a k cid pos' HAR Hab Hfr.
destruct (alx_sep _ _ _ LAWS lyc Sc Hpc Wc memc mdc HAR) as (Hsep & _).
destruct (pairwise_app_inv _ _ _ Hsep) as (_ & _ & HX).
apply (HX (a, req_size k) (frame_addr lyc cid pos', fs_frame_bytes cid)).
- apply in_map_iff. exists (a, k). split; [reflexivity | exact Hab].
- apply in_map_iff. exists (cid, pos'). split; [reflexivity | exact Hfr].
Qed.
(* a byte of a block the walk holds is not a byte of the class-3 frame *)
Lemma c4_blk_off_frame : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc a k y {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  In (a, k) Lamc -> a <= y < a + k ->
  ~ (frame_addr lyc CRT_CID pos <= y < frame_addr lyc CRT_CID pos + 512).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc a k y kbg HL Hin Hy.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof HJ as (HARc & _).
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ) as (Hinf & _).
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc a k _ _ HLED Hin) as (Hk0 & Hab & _).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity. rewrite Hch16 in Hab.
assert (Hrs : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
pose proof (c4_blk_frame_disj lyc Sc Hpc Wc memc mdc (a - 16) (k + 16) CRT_CID pos HARc Hab Hinf) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrs, cb4_fb in Hd. lia.
Qed.
(* the document's 56 bytes are not bytes of the class-3 frame (its home is a frame of the entry) *)
Lemma c4_doc_off_frame : forall lyc Sc Hpc Wc memc mdc kj pos y {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS ->
  doc <= y < doc + 56 -> ~ (frame_addr lyc CRT_CID pos <= y < frame_addr lyc CRT_CID pos + 512).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos y WS HJ Hy.
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
pose proof HTREE as (_ & _ & _ & (_ & (cid & pos' & Hfin & Hfa1 & Hfa2) & _)).
destruct (alx_layout _ _ _ LAWS ly S Hp W mem md lyc cb4_ar0 HLYc) as (_ & Efa & _).
destruct (alx_sep _ _ _ LAWS lyc Sc Hpc Wc memc mdc HARc) as (Hsep & _).
apply pairwise_app_l in Hsep as [_ Hsep]. rewrite HFRc in Hsep. cbn [app map pairwise] in Hsep.
destruct Hsep as (Hsep & _). rewrite Forall_map in Hsep.
pose proof (proj1 (Forall_forall _ _) Hsep (cid, pos') Hfin) as Hd. cbn [fst snd] in Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (Efa cid pos') in Hd. rewrite cb4_fb in Hd. lia.
Qed.

(* ---- A TREE ACROSS A CALL: its header is in a live fake frame and its blocks are live harness blocks the callee
   kept, and the callee's footprint touches neither ---- *)
Lemma c4_tree_keep : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc
    STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 (D' : list (Z * Z)) (p : Z) (tv : PjTree.jv) Lam2 cid pos' {kbg : nat}
    {WS1 : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  In (cid, pos') (frames Sc) ->
  frame_addr lyc cid pos' <= p -> p + 56 <= frame_addr lyc cid pos' + fs_frame_bytes cid ->
  (forall a, p <= a < p + 56 -> ~ inFP FP1 a) ->
  (forall a k y, In (a, k) D' -> a <= y < a + k -> ~ inFP FP1 y) ->
  (forall bk, In bk D' -> In bk Lamc) ->
  (forall a k, In (a, k) D' -> In (a - cf_head, k + cf_head) (ablocks B ly2 S2)) ->
  (forall bk, In bk D' -> In bk Lam2) ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) p tv D' ->
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) p tv D'.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 D' p tv Lam2
  cid pos' kbg WS1 HL HJ1 Hfin Hp1 Hp2' HnFPp HnFPb HDL HBK2 HLam2 HND.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof HJ as (HARc & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _ & G4 & _).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity.
apply (cb4_nodeR_lblk SEGS tv (mrestrict (w_H W2) mem2) (prh_lin Lamc) (prh_lin Lam2) p D');
  [|intros a k Hak; exact (HLam2 _ Hak)].
apply (pj_nodeR_frame SEGS tv (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) p D' HND).
apply (c4_agree_of_aview (w_H Wc) (w_H W2) memc mem2).
intros y Hy.
destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- unfold pj_holdsR in *.
  destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc cid pos' HARc Hfin) as (Fb1 & Fb2 & Fb3).
  pose proof (YM05.alloc_ceiling_val).
  split; [lia|]. split.
  + exact (frm_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' y HARc Hfin ltac:(lia)).
  + apply (G4 cid pos' y Hfin); [|exact (HnFPp y Hy)].
    left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDL _ Hb))
    as (Hk0 & Hab & _).
  rewrite Hch16 in Hab.
  assert (Hrs : req_size (kb + 16) = kb + 16) by (unfold req_size; destruct (Z.eqb_spec (kb + 16) 0); lia).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & _).
  rewrite Hrs in Bce. pose proof (YM05.alloc_ceiling_val).
  split; [lia|]. split.
  + exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc (b - 16) (kb + 16) y HARc Hab ltac:(lia)).
  + pose proof (HBK2 b kb Hb) as Hab2. rewrite Hch16 in Hab2.
    replace y with (b - 16 + (y - (b - 16))) by lia.
    apply (G2 (b - 16) (kb + 16) (y - (b - 16)) Hab Hab2); [rewrite Hrs; lia|].
    replace (b - 16 + (y - (b - 16))) with y by lia. exact (HnFPb b kb y Hb ltac:(lia)).
Qed.

(* ---- A TREE'S FREE ORDER ACROSS A CALL: the same keep as c4_tree_keep, read by pj_foR (copy's free order,
   carried from crt_at_W_B_copy_fo to crt_at_L0_B_copy_fo) ---- *)
Lemma c4_tree_keep_fo : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc
    STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 (D' : list (Z * Z)) (p : Z) d F' Lam2 cid pos' {kbg : nat}
    {WS1 : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  In (cid, pos') (frames Sc) ->
  frame_addr lyc cid pos' <= p -> p + 56 <= frame_addr lyc cid pos' + fs_frame_bytes cid ->
  (forall a, p <= a < p + 56 -> ~ inFP FP1 a) ->
  (forall a k y, In (a, k) D' -> a <= y < a + k -> ~ inFP FP1 y) ->
  (forall bk, In bk D' -> In bk Lamc) ->
  (forall a k, In (a, k) D' -> In (a - cf_head, k + cf_head) (ablocks B ly2 S2)) ->
  (forall bk, In bk D' -> In bk Lam2) ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) d p D' F' ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) d p D' F'.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 D' p d F' Lam2
  cid pos' kbg WS1 HL HJ1 Hfin Hp1 Hp2' HnFPp HnFPb HDL HBK2 HLam2 HFo.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof HJ as (HARc & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _ & G4 & _).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity.
eapply PRH_PjOrder.pj_foR_frame; [exact HFo | intros a k Hak; exact (HLam2 _ Hak) |].
apply (c4_agree_of_aview (w_H Wc) (w_H W2) memc mem2).
intros y Hy.
destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- unfold pj_holdsR in *.
  destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc cid pos' HARc Hfin) as (Fb1 & Fb2 & Fb3).
  pose proof (YM05.alloc_ceiling_val).
  split; [lia|]. split.
  + exact (frm_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' y HARc Hfin ltac:(lia)).
  + apply (G4 cid pos' y Hfin); [|exact (HnFPp y Hy)].
    left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDL _ Hb))
    as (Hk0 & Hab & _).
  rewrite Hch16 in Hab.
  assert (Hrs : req_size (kb + 16) = kb + 16) by (unfold req_size; destruct (Z.eqb_spec (kb + 16) 0); lia).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & _).
  rewrite Hrs in Bce. pose proof (YM05.alloc_ceiling_val).
  split; [lia|]. split.
  + exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc (b - 16) (kb + 16) y HARc Hab ltac:(lia)).
  + pose proof (HBK2 b kb Hb) as Hab2. rewrite Hch16 in Hab2.
    replace y with (b - 16 + (y - (b - 16))) by lia.
    apply (G2 (b - 16) (kb + 16) (y - (b - 16)) Hab Hab2); [rewrite Hrs; lia|].
    replace (b - 16 + (y - (b - 16))) with y by lia. exact (HnFPb b kb y Hb ltac:(lia)).
Qed.

(* ---- the shadow hull of `back` (the frame's slot at +0x20, 56 bytes) lies inside the frame's own 64 shadow
   bytes: the frame is 32-aligned, so shadow_addr F is 0 or 4 mod 8 and the hull of [F + 32, F + 88) rounds to
   [shadow_addr F, shadow_addr F + 16) ---- *)
Lemma c4_back_hull : forall (Wc : world SEGS) memc' F0,
  0 <= F0 -> F0 mod 32 = 0 ->
  (forall i, 0 <= i < 64 -> apresent (w_H Wc) memc' (shadow_addr F0 + i)) ->
  shadow_hull_vis (aview SEGS (w_H Wc) memc') (F0 + CRT_OFF_BACK) 56.
Proof.
intros Wc memc' F0 HF0 H32 Hsh s Hs. apply c4_apresent_vis.
assert (Hu : exists u, F0 = 32 * u /\ 0 <= u).
{ apply Z.mod_divide in H32; [|lia]. destruct H32 as (u & Hu). exists u. split; lia. }
destruct Hu as (u & Hu & Hu0).
assert (E0 : F0 / 8 = 4 * u)
  by (rewrite Hu; replace (32 * u) with (4 * u * 8) by lia; apply Z.div_mul; lia).
assert (E1 : (F0 + CRT_OFF_BACK) / 8 = 4 * u + 4).
{ unfold CRT_OFF_BACK. rewrite Hu. replace (32 * u + 32) with ((4 * u + 4) * 8) by lia. apply Z.div_mul. lia. }
assert (E2 : (F0 + CRT_OFF_BACK + 56 - 1) / 8 = 4 * u + 10).
{ unfold CRT_OFF_BACK. rewrite Hu. replace (32 * u + 32 + 56 - 1) with (7 + (4 * u + 10) * 8) by lia.
  rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
unfold shadow_addr in Hs, Hsh |- *. rewrite E1, E2 in Hs. rewrite E0 in Hsh.
pose proof (Z.div_mod (SHADOW_OFF + (4 * u + 4)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * u + 4)) 8 ltac:(lia)).
pose proof (Z.div_mod (SHADOW_OFF + (4 * u + 10)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * u + 10)) 8 ltac:(lia)).
pose proof (Z.div_mod u 2 ltac:(lia)). pose proof (Z.mod_pos_bound u 2 ltac:(lia)).
replace s with (SHADOW_OFF + 4 * u + (s - (SHADOW_OFF + 4 * u))) by lia.
apply Hsh. unfold SHADOW_OFF in *. lia.
Qed.
(* ======================================================================================================== *)
(* THE parse_noting CALL OF THIS SEGMENT, AS ONE NAMED GOAL (`t4_goal_pn`).
   It is tparse_noting_specX (PRH_FnCheck.v:586-713 at commit 3ac20a5c9e30, PRH_FnCheck 0844ed8c0608) at this
   call site's binders - fail = SIZE_MAXZ, ran = 0, own = 0, its post verbatim (the refusal peak prh_refused_peak and
   prh_oks over prh_ev_reqs as the text states them) - read at the site's own position: the goal takes the reading's
   run events at the entry position (`prh_run_at .. ii (parse_evs ..)`), the run hypothesis over that window
   (prh_cons_from), the strtod tie rp_sm = jr_strtod and no injected failure in the reading's window (all three from
   crt_pos, which crt4_at_S's posB carries, and the count bounds), and states the text's OUTCOME CLAUSE (:658-667) at
   that position: the reading GRANTED (ran' = 0) and the position at the GRANTED advance ii + length (parse_evs ..
   tb []). The goal's premises are the site's; t4_goal_pn_holds below applies the text and derives the post.
   kb round: the goal is the text's kb form - the text's wild room premise `wild_room (as_universe B) []
   (prh_wk F_parse_noting) (st_depot Sc)` in the text's place (after room_live_cf, PRH_FnCheck.v:638) and the text's
   BUDGETED post fpostFbm .. (wbudget [] (prh_wk F_parse_noting)) (:649); the call site pays the room out of the
   text's entry room HWR0 (crt4_lane_S_at). *)
Definition c4_pn_post (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (text dc : Z) (tb : list Z) (Lamc : list (Z * Z)) (peakc cntc : Z) (ii : nat)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    room_live_cf S' /\
    (exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
       (ii + length (PresetReqAt.parse_evs rp_sm tb []))%nat rp_H0 hist' S') /\
    exists Lam' peak' cnt' fail' ran' okr res tr,
    PjGrammar.jr_run ReaderRes.jr_strtod tb okr = (res, tr) /\
    ran' = 0 /\
    prh_oks okr cntc SIZE_MAXZ (PjGrammar.calls tr) (prh_ev_reqs tr) most 0 ran' /\
    cnt' = cntc + Z.of_nat (PjGrammar.calls tr) /\
    ReaderRes.fail_after cntc SIZE_MAXZ (PjGrammar.calls tr) fail' /\
    peak' = Z.max (Z.max peakc (Ledger.lsum Lamc + ReaderRes.hpeak tr))
      (prh_refused_peak okr cntc SIZE_MAXZ (PjGrammar.calls tr)
         (map (Z.add (Ledger.lsum Lamc)) (prh_ev_helds (PRH_FnPj.prhPj_ptrace tb)))) /\
    ReaderRes.hpeak tr <= 224 * Z.of_nat (length tb) + 16384 /\
    (cntc <= SIZE_MAXZ < cntc + ck_ncalls tb -> res = None) /\
    (ran' <> 0 -> res = None) /\
    (ran' = 0 -> SIZE_MAXZ < cntc \/ cntc + ck_ncalls tb <= SIZE_MAXZ ->
       res = ck_read tb /\ Z.of_nat (PjGrammar.calls tr) = ck_ncalls tb) /\
    bytes_at W' mem' text tb /\
    prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most 0 /\
    match res with
    | Some tv =>
        getr regs' 10 = w64 0 /\
        exists Dr, Permutation Lam' (Dr ++ Lamc) /\
          Permutation (map snd Dr) (map Z.of_nat (ReaderRes.lsz tr)) /\
          Z.of_nat (length Dr) = ReaderRes.nlive tr /\
          (* the built tree's free order (the text's :704-706, verbatim) *)
          (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth tv <= n)%nat ->
             exists Fr, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') n dc Dr Fr /\
               map (fun b => snd b + cf_head) Fr = PresetReqAt.pj_frees ReaderRes.jr_strtod okr tb) /\
          (forall a k, In (a, k) Dr -> ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) /\
          Permutation (ablocks B ly' S') (ablocks B lyc Sc ++ ck_hblks Dr) /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') dc tv Dr
    | None =>
        getr regs' 10 = w64 (-1) /\ Permutation Lam' Lamc /\
        Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\ pj_zeroR SEGS (mrestrict (w_H W') mem') dc
    end.

Definition t4_goal_pn : Prop :=
  forall (fxk : YK11.FPState) lyc Sc Hpc Wc regsT memc mdc ch1 text (tb : list Z) dc Lamc peakc cntc ii hist,
  let len := Z.of_nat (length tb) in
  fpre B ARx (@STK_parse_noting prh_img_B) lyc Sc Hpc Wc regsT memc mdc ch1 ->
  YAkMemnorm.memnorm SEGS memc ->
  prh_univ_closure B CTX0 ->
  getr regsT 10 = w64 text -> getr regsT 11 = w64 len -> getr regsT 12 = w64 dc ->
  len < 2 ^ 40 -> 0 < text -> text + len < 2 ^ 62 ->
  src_rd Wc memc text tb -> @PRH_FnReader.prhReader_home rc B_prog_listing PA B lyc Sc Hpc Lamc text len ->
  Z.of_nat (PjRoundTrip.maxrun tb) < 2 ^ 30 ->
  dc mod 8 = 0 -> ck_out_ok B (@STK_parse_noting prh_img_B) lyc Sc Wc regsT memc dc 56 ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ 0 most 0 -> cntc + 2 * len + 2 < 2 ^ 64 - 1 ->
  blocks_bytes Sc + PRH_FnPj.LIVE_pj_parse tb <= LIVE_MAX -> PRH_FnPj.RQ_pj_parse tb + cf_head < cf_malloc_max ->
  Z.of_nat (length (frames Sc)) <= ck_FRAMES_CAP - FR_parse_noting -> @ck_frm0 fxk ->
  room_live_cf Sc -> YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot Sc) ->
  (* the text's hull budget (PRH_FnCheck.v:661) in the text's place (the two pkR room counts
     between, which t4_goal_pn_holds derives from the position, are not premises here); the call site pays it from
     the run position (c4_hull_pn) *)
  PresetHullBudget.hull_budget Sc (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os ii rp_H0 hist Sc ->
  prh_run_at rp_sm rp_x rp_os ii (PresetReqAt.parse_evs rp_sm tb []) ->
  (* the site's run facts (crt_pos) and count bounds, for the text's outcome clause; the text's premise
     RQ_pj_parse tb <= most, paid at the site from HRQA (Crt102Model.cm_rqa_read) *)
  rp_sm = ReaderRes.jr_strtod ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os ii (length (PresetReqAt.parse_evs rp_sm tb [])) ->
  cntc + ck_ncalls tb <= SIZE_MAXZ ->
  PRH_FnPj.RQ_pj_parse tb <= most ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
    (mkCfg (@YK11.mkst fxk regsT (Z_to_bv 64 (SIGMA AS_parse_noting)) memc (YK11.seg_rom SEGS)) mdc)
    (@fpostFbm fxk rc prh_img_B B_prog_listing PA B ARx SK (YCbqGwild.wbudget [] (prh_wk F_parse_noting))
       (@STK_parse_noting prh_img_B) [(dc, dc + 56)] regsT
       lyc Sc Hpc Wc memc mdc (c4_pn_post lyc Sc Wc memc text dc tb Lamc peakc cntc ii)).

(* THE HULL AT THE parse_noting CALL (t4_goal_pn's hull premise, the text's PRH_FnCheck.v:661):
   the reading's all-granted events are an infix of the run's round_trip, whose secondary counts are within one
   call's (PresetSecTotalRun.NT_round_trip, x a read input of at most MAXB bytes: HREAD, HLENX), so the run position
   pays their hull budget (PresetHullPay.hull_budget_of_room_pos at the length bound HOS4) *)
Lemma c4_hull_pn : forall pre rest ii hist Sc tb, rp_sm = ReaderRes.jr_strtod ->
  PresetReqAt.round_trip rp_sm t = pre ++ PresetReqAt.parse_evs rp_sm tb [] ++ rest ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os ii rp_H0 hist Sc ->
  PresetHullBudget.hull_budget Sc (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []).
Proof.
intros pre rest ii hist Sc tb Esm Ert Hpos. rewrite Esm in Ert, Hpos.
destruct (PresetSecTotalRun.NT_round_trip ReaderRes.jr_strtod x t ltac:(unfold PresetReqAt.MAXB; lia) HREAD)
  as [N T].
rewrite Ert, !PresetSecTotal.nsec_app, !Nat2Z.inj_add in N.
rewrite Ert, !PresetSecTotalRun.treq_app in T.
pose proof (PresetSecTotalRun.treq_nn pre) as T1. pose proof (PresetSecTotalRun.treq_nn rest) as T2.
pose proof (PresetSecTotalRun.tsec_treq (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) as Ts.
assert (KN : 3 * PresetSecTotal.RB_N + 8 + 3 * PresetSecTotal.CH_P + 2 * PresetSecTotal.CH_C <= PresetSecTotal.NCALL)
  by (apply Z.leb_le; vm_compute; reflexivity).
assert (KT : 3 * PresetSecTotal.RB_T + 2 * PresetSecTotal.TOP_GROW_T + 3 * PresetSecTotal.CHP_T +
  2 * PresetSecTotal.CHC_T + PresetSecTotal.SEC_MAP_OVH * PresetSecTotal.NCALL <= PresetSecTotal.TCALL)
  by (apply Z.leb_le; vm_compute; reflexivity).
unfold PresetSecTotal.SEC_MAP_OVH in Ts, KT.
apply (PresetHullPay.hull_budget_of_room_pos ReaderRes.jr_strtod rp_x rp_os ii rp_H0 hist Sc _ HOS4 Hpos); lia.
Qed.

(* ======================================================================================================== *)
(* BACK'S BLOCKS AGAINST tblk crt_tc UP TO PERMUTATION (crt_at_L0_B's Some arm, base eda8876a8e89), from the
   parse_noting post's multiset `Permutation (map snd D) (map Z.of_nat (ReaderRes.lsz tr))`: a Some reading of the
   writer's text wdoc crt_tc true is the all-granted run (PjGrammar.G7_1 / G7_2), whose trace is ttrace crt_tc
   (PjRoundTrip.G9_trace); lsz of a reader trace shifted by HEAD is the live list of its heap events (cb4_lsz_hlive);
   and that list is tblk crt_tc up to permutation (PresetReqAtNoMiss.ttrace_blocks). *)
Lemma cb4_rm1n_map : forall k s, map (fun n => Z.of_nat n + PresetReqAt.HEAD) (ReaderRes.rm1n k s) =
  PresetReqAt.rm1 (Z.of_nat k + PresetReqAt.HEAD) (map (fun n => Z.of_nat n + PresetReqAt.HEAD) s).
Proof.
intros k s. induction s as [|a r IH]; [reflexivity|]. cbn [ReaderRes.rm1n PresetReqAt.rm1 map].
destruct (Nat.eqb_spec a k) as [E | E].
- subst a. rewrite Z.eqb_refl. reflexivity.
- rewrite (proj2 (Z.eqb_neq (Z.of_nat a + PresetReqAt.HEAD) (Z.of_nat k + PresetReqAt.HEAD))) by lia.
  cbn [map]. rewrite IH. reflexivity.
Qed.

Lemma cb4_lsz_hlive : forall tr s, map (fun n => Z.of_nat n + PresetReqAt.HEAD) (fold_left ReaderRes.lsz_ev tr s) =
  PresetReqAt.hlive_from (map (fun n => Z.of_nat n + PresetReqAt.HEAD) s) (PresetReqAt.rd_hevs tr).
Proof.
induction tr as [|e tr IH]; intros s; [reflexivity|].
cbn [fold_left]. rewrite IH. unfold PresetReqAt.rd_hevs. cbn [flat_map]. rewrite PresetReqAt.hlive_from_app.
f_equal.
destruct e as [n | [|m] n | n | n];
  cbn [ReaderRes.lsz_ev PresetReqAt.rd_hev PresetReqAt.hlive_from fold_left PresetReqAt.hstep map];
  try reflexivity.
- f_equal. apply cb4_rm1n_map.
- apply cb4_rm1n_map.
Qed.

Lemma cb4_back_tblk : forall okr tv tr (Dr : list (Z * Z)),
  PjGrammar.jr_run ReaderRes.jr_strtod tbB okr = (Some tv, tr) ->
  Permutation (map snd Dr) (map Z.of_nat (ReaderRes.lsz tr)) ->
  Permutation (map (fun b => snd b + cf_head) Dr) (PresetReqAtNoMiss.tblk tcB).
Proof.
intros okr tv tr Dr Hjr HP.
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
pose proof (cm_in_crt_wf x t HIN) as Hwf.
assert (Etr : tr = PjRoundTrip.ttrace tcB).
{ destruct (PjGrammar.ok_upto_dec okr (PjGrammar.ncalls ReaderRes.jr_strtod tbB)) as [Hu | (j & Hj & Hf & Hu)].
  - pose proof (PjGrammar.G7_1 ReaderRes.jr_strtod tbB okr Hu) as E. rewrite Hjr in E. injection E as _ E.
    rewrite E. exact (PjRoundTrip.G9_trace _ _ Hwf true).
  - destruct (PjGrammar.G7_2 ReaderRes.jr_strtod tbB okr j Hj Hf Hu) as (E & _). rewrite Hjr in E. discriminate E. }
subst tr.
replace (map (fun b => snd b + cf_head) Dr) with (map (fun z => z + PresetReqAt.HEAD) (map snd Dr))
  by (rewrite map_map; reflexivity).
apply (Permutation_trans (Permutation_map (fun z => z + PresetReqAt.HEAD) HP)).
rewrite map_map. unfold ReaderRes.lsz. rewrite (cb4_lsz_hlive (PjRoundTrip.ttrace tcB) []). cbn [map].
exact (PresetReqAtNoMiss.ttrace_blocks tcB).
Qed.

(* ---- back's FREE ORDER at L0 (crt_at_L0_B's granted arm, base 7281359fe8bc): a Some reading of the writer's text
   is the all-granted run (G7_1 / G7_2), its tree is crt_tc (G9), so its depth is copy's (cm_crt_depth_doc), and
   pj_free's reader-side list at the post's grant list is the list at [] (PresetFreeFo.pj_frees_acc,
   taken by path from commit f8c50a8d2d5: the PRH_FnPj.v:414-416 OWED (d) fact), which is fo crt_tc
   (PresetFreeFo.pj_frees_wdoc_t) ---- *)
Lemma cb4_back_fo : forall okr tv tr,
  PjGrammar.jr_run ReaderRes.jr_strtod tbB okr = (Some tv, tr) ->
  (PjTree.depth tv <= DOC_D)%nat /\
  PresetReqAt.pj_frees ReaderRes.jr_strtod okr tbB = PresetReqAt.fo tcB.
Proof.
intros okr tv tr Hjr.
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
pose proof (cm_in_crt_wf x t HIN) as Hwf.
assert (Hu : PjGrammar.ok_upto okr (PjGrammar.ncalls ReaderRes.jr_strtod tbB)).
{ destruct (PjGrammar.ok_upto_dec okr (PjGrammar.ncalls ReaderRes.jr_strtod tbB)) as [Hu | (j & Hj & Hf & Hu)];
    [exact Hu|].
  destruct (PjGrammar.G7_2 ReaderRes.jr_strtod tbB okr j Hj Hf Hu) as (E & _). rewrite Hjr in E. discriminate E. }
split.
- pose proof (PjGrammar.G7_1 ReaderRes.jr_strtod tbB okr Hu) as E. rewrite Hjr in E. injection E as E _.
  assert (G : PjGrammar.json_read ReaderRes.jr_strtod tbB = Some tcB) by exact (PjRoundTrip.G9 _ _ Hwf true).
  rewrite G in E. injection E as Etv. subst tv.
  exact (cm_crt_depth_doc t (cm_in_depth x t HIN)).
- rewrite (PresetFreeFo.pj_frees_acc ReaderRes.jr_strtod tbB okr tv tr Hjr).
  exact (PresetFreeFo.pj_frees_wdoc_t ReaderRes.jr_strtod _ true Hwf).
Qed.

(* ---- a tree whose header is in a live fake frame and whose blocks the walk holds is kept across a call that
   wrote only its own stack window (the strlen wrapper) ---- *)
Lemma c4_tree_stk : forall lyc Sc Hpc Wc memc memc' mdc kj pos Dx Lamc peakc cntc ownc ranc
    (D' : list (Z * Z)) (p : Z) (tv : PjTree.jv) cid pos' {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  In (cid, pos') (frames Sc) ->
  frame_addr lyc cid pos' <= p -> p + 56 <= frame_addr lyc cid pos' + fs_frame_bytes cid ->
  (forall bk, In bk D' -> In bk Lamc) ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) p tv D' ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc') (prh_lin Lamc) p tv D'.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc kj pos Dx Lamc peakc cntc ownc ranc D' p tv cid pos' kbg HL Hag Hfin Hp1 Hp2' HDL
  HND.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof HJ as (HARc & _).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity.
apply (pj_nodeR_frame SEGS tv (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') (prh_lin Lamc) p D' HND).
apply (c4_agree_of_aview (w_H Wc) (w_H Wc) memc memc').
intros y Hy. pose proof (YM05.alloc_ceiling_val).
destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc cid pos' HARc Hfin) as (Fb1 & Fb2 & Fb3).
  split; [lia|]. split.
  + exact (frm_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' y HARc Hfin ltac:(lia)).
  + apply Hag; [lia | apply c4_nw_stk; left; lia].
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDL _ Hb))
    as (Hk0 & Hab & _).
  rewrite Hch16 in Hab.
  assert (Hrs : req_size (kb + 16) = kb + 16) by (unfold req_size; destruct (Z.eqb_spec (kb + 16) 0); lia).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & _).
  rewrite Hrs in Bce.
  split; [lia|]. split.
  + exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc (b - 16) (kb + 16) y HARc Hab ltac:(lia)).
  + apply Hag; [lia | apply c4_nw_stk; left; lia].
Qed.

(* ---- the same keep across the strlen wrapper, read by pj_foR ---- *)
Lemma c4_tree_stk_fo : forall lyc Sc Hpc Wc memc memc' mdc kj pos Dx Lamc peakc cntc ownc ranc
    (D' : list (Z * Z)) (p : Z) d F' cid pos' {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  In (cid, pos') (frames Sc) ->
  frame_addr lyc cid pos' <= p -> p + 56 <= frame_addr lyc cid pos' + fs_frame_bytes cid ->
  (forall bk, In bk D' -> In bk Lamc) ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) d p D' F' ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc') (prh_lin Lamc) d p D' F'.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc kj pos Dx Lamc peakc cntc ownc ranc D' p d F' cid pos' kbg HL Hag Hfin Hp1 Hp2' HDL
  HFo.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof HJ as (HARc & _).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity.
eapply PRH_PjOrder.pj_foR_frame; [exact HFo | intros a k Hak; eapply PRH_PjOrder.pj_foR_lblk; [exact HFo | exact Hak] |].
apply (c4_agree_of_aview (w_H Wc) (w_H Wc) memc memc').
intros y Hy. pose proof (YM05.alloc_ceiling_val).
destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc cid pos' HARc Hfin) as (Fb1 & Fb2 & Fb3).
  split; [lia|]. split.
  + exact (frm_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' y HARc Hfin ltac:(lia)).
  + apply Hag; [lia | apply c4_nw_stk; left; lia].
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDL _ Hb))
    as (Hk0 & Hab & _).
  rewrite Hch16 in Hab.
  assert (Hrs : req_size (kb + 16) = kb + 16) by (unfold req_size; destruct (Z.eqb_spec (kb + 16) 0); lia).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & _).
  rewrite Hrs in Bce.
  split; [lia|]. split.
  + exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc (b - 16) (kb + 16) y HARc Hab ltac:(lia)).
  + apply Hag; [lia | apply c4_nw_stk; left; lia].
Qed.

(* ---- a slot of a 32-aligned frame: the shadow byte of each of its bytes is one of the frame's shadow bytes ---- *)
Lemma c4_slot_sh : forall F0 n y, 0 <= F0 -> F0 mod 32 = 0 -> F0 <= y < F0 + n ->
  shadow_addr F0 <= SHADOW_OFF + y / 8 < shadow_addr F0 + (n + 7) / 8.
Proof.
intros F0 n y HF0 H32 Hy.
apply Z.mod_divide in H32; [|lia]. destruct H32 as (u & Hu).
assert (E0 : F0 / 8 = 4 * u) by (rewrite Hu; replace (u * 32) with (4 * u * 8) by lia; apply Z.div_mul; lia).
unfold shadow_addr. rewrite E0.
pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia.
Qed.

(* ---- O2 FROM THE parse_noting POST: the live state, the frame's locals, the registers and the forwarded writer
   and reader outcomes after the call, for a register map rg' that keeps the snapshot and holds `snez a0` in s5.
   Its states: the call's (lyc Sc Hpc Wc memc mdc, the strlen call already made) and the post's. kb round: the call
   state's live state at any budget kbg, the caller's journal after the call at the landing WS3 with
   `wbudget [] (prh_wk F_check_round_trip) WS3` (crt4_lane_S_at: WS0 ++ WS1 by wbudget_app), the callee's at its
   own WS1; the O2 state's live state at prh_wk F_check_round_trip ---- *)
Lemma c4_O2_state : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc msv cset ok q pre
    fx3 ly3 S3 Hp3 W3 regs3 mem3 md3 k1 md' rg' {kbg : nat} {WS3 WS1 : list (list Z)},
  let st' := PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB in
  (cf_head = PresetReqAt.HEAD ->
     Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk (@crt_tree_J t))) ->
  (PjTree.depth (@crt_tree_J t) <= DOC_D)%nat ->
  (exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (@crt_tree_J t)) ->
  t = PjTree.JObj msv ->
  fregs_kept_x fx fxk ->
  prh_oks ok (cwB cset) SIZE_MAXZ (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB)
    (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB) most 0 0 ->
  WriterApp.w_failed st' = 0 -> q <> 0 -> ~ In (q, WriterApp.w_cap st') Dc ->
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos ((q, WriterApp.w_cap st') :: Dc) Lamc peakc (WriterApp.w_cnt st') 0 0 ->
  spillB Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) ->
  spillB Wc memc CRT_SP_SHN_B (shadow_addr (doc + PJ_OFF_N)) ->
  spillB Wc memc CRT_SP_PN_B (doc + PJ_OFF_N) ->
  spillB Wc memc CRT_SP_N_B (Z.of_nat (length msv)) ->
  doc mod 8 = 0 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc 56 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 ->
  0 <= cset <= 3 -> (In ck_MOD_AT (map fst msv) -> cset = 0) ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) tcB Dc ->
  PresetReqAt.round_trip rp_sm t = pre ++ PresetReqAt.parse_evs rp_sm tbB [] ++ crt_evs_L0 msv ->
  prh_run_at rp_sm rp_x rp_os (rp_i + length pre + length (PresetReqAt.parse_evs rp_sm tbB []))%nat
    (crt_evs_L0 msv) ->
  rp_sm = ReaderRes.jr_strtod ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os (rp_i + length pre + length (PresetReqAt.parse_evs rp_sm tbB []))%nat
    (length (crt_evs_L0 msv)) ->
  frm_zero (@YK11.fp_csr fx3) -> fregs_kept_x fxk fx3 ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly3 S3 Hp3 W3 mem3 md3 (kj + k1) WS3 ->
  YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS3 ->
  AJW (@STK_parse_noting prh_img_B) sp1
    [(frame_addr lyc CRT_CID pos + CRT_OFF_BACK, frame_addr lyc CRT_CID pos + CRT_OFF_BACK + 56)]
    lyc Sc Hpc Wc memc mdc [] ly3 S3 Hp3 W3 mem3 md3 k1 WS1 ->
  c4_pn_post lyc Sc Wc memc q (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) tbB Lamc peakc (WriterApp.w_cnt st')
    (rp_i + length pre) ly3 S3 Hp3 W3 regs3 mem3 md3 ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem3) ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly3 S3 Hp3 W3 mem3 md' (kj + k1) WS3 ->
  dregsB rg' (frame_addr lyc CRT_CID pos) -> getr rg' 24 = w64 q ->
  getr rg' 26 = w64 (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B) ->
  getr rg' 21 = alu64 ALU_SLTU (Z_to_bv 64 0) (getr regs3 10) ->
  exists Lam3 peak3 cnt3,
    crt4_at_O2 fx3 ly3 S3 Hp3 W3 mem3 md' (kj + k1) pos Dc Lam3 peak3 cnt3 rg' msv cset q.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc msv cset ok q pre fx3 ly3 S3 Hp3 W3 regs3 mem3 md3 k1 md' rg'
  kbg WS3 WS1
  st' HCPc HDPc HFOc Et HFK HOK Hfail0 Hq0 HnIn HL HSPB HSPS HSPP HSPN Hd8 HRAd HRAb HRAv Hcs Hcs0 HCT Hpre Hpos2b Esm
  HCF2
  HFZ3 HFK3 HJ3 HB3 HJ1 HQ3 HMN3 HJ3' HDR' R24' R26' R21'.
set (cap := WriterApp.w_cap st') in *. set (cntW := WriterApp.w_cnt st') in *.
cb4_rd_live HL WSj HJ HBj HSD HPL HPB HAP HSV HFRM HSPF HCR HCH HMNl.
cb4_rd_side HSD HLED HPK HRL HRO HDOC HDL.
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ) as (Hinf & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof HJ1 as (HAR3 & HLY1 & _ & _ & _ & HFR1 & _ & _ & G1 & G2 & G3 & G4 & _).
destruct (alx_layout _ _ _ LAWS lyc Sc Hpc Wc memc mdc ly3 HARc HLY1) as (_ & Efa & _).
assert (EF : frame_addr ly3 CRT_CID pos = frame_addr lyc CRT_CID pos) by apply Efa.
set (F := frame_addr lyc CRT_CID pos) in *.
pose proof cb4_sp as (Hal16 & Hceil & H47 & Hs1 & Hs32 & Hs1b).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (YM05.alloc_ceiling_val) as Hcv.
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity.
assert (Eq0 : (q =? 0) = false) by (apply Z.eqb_neq; exact Hq0).
destruct HQ3 as (HRL3 & (histp & HPOSp) & Lam3 & peak3 & cnt3 & fail3 & ran3 & okr & res & tr &
  Hjr & Er3 & Hoks & Ecnt3 & Hfa3 & Epk3 & Hhp3 & Hfr3 & Hrr3 & Hok3 & Hby3 & HLED3 & Hres).
assert (Ef3 : fail3 = SIZE_MAXZ).
{ destruct Hfa3 as (Hf1 & Hf2). unfold SIZE_MAXZ in *.
  destruct (Z_le_dec cntW (2 ^ 64 - 1)); destruct (Z_lt_dec (2 ^ 64 - 1) (cntW + Z.of_nat (PjGrammar.calls tr)));
    first [apply Hf1; lia | apply Hf2; lia]. }
rewrite Ef3 in HLED3.
pose proof (prh_ledger_bounds B ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 SIZE_MAXZ ran3 _ _ HLED3) as (_ & _ & _ & _ & Hran01).
(* the blocks the walk holds at the call stay live after it *)
assert (HKB : (forall bk, In bk Lamc -> In bk Lam3) /\
  (forall a k, In (a, k) Lamc -> In (a - cf_head, k + cf_head) (ablocks B ly3 S3))).
{ destruct res as [tv|].
  - destruct Hres as (_ & Dr & HPLr & _ & _ & _ & _ & HPBr & _). split.
    + intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPLr)). apply in_or_app. right. exact Hbk.
    + intros a k Hk. apply (Permutation_in _ (Permutation_sym HPBr)). apply in_or_app. left.
      exact (proj1 (proj2 (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntW SIZE_MAXZ 0 a k _ _ HLED Hk))).
  - destruct Hres as (_ & HPLr & HPBr & _). split.
    + intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPLr)). exact Hbk.
    + intros a k Hk. apply (Permutation_in _ (Permutation_sym HPBr)).
      exact (proj1 (proj2 (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntW SIZE_MAXZ 0 a k _ _ HLED Hk))). }
destruct HKB as (HLam3 & HBK3).
assert (HDcL : forall bk, In bk Dc -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. right. exact Hbk. }
set (FP1 := [(F + CRT_OFF_BACK, F + CRT_OFF_BACK + 56)]) in *.
assert (HFPin : forall a, inFP FP1 a -> F + 32 <= a < F + 88).
{ intros a Ha. unfold FP1 in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold CRT_OFF_BACK in Ha; lia|].
  exfalso. exact (inFP_nil a Ha). }
assert (HnFPsh : forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 -> ~ inFP FP1 a).
{ intros a Ha Hf. apply HFPin in Hf.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
(* the document's tree and the copy's tree after the call *)
pose proof HTREE as (_ & _ & _ & (_ & (cid & pos' & Hfin & Hfa1 & Hfa2) & _)).
destruct (alx_layout _ _ _ LAWS ly S Hp W mem md lyc cb4_ar0 HLYc) as (_ & Efa0 & _).
assert (Hfin' : In (cid, pos') (frames Sc)) by (rewrite HFRc; apply in_or_app; right; exact Hfin).
assert (HDOC3 : pj_nodeR SEGS (mrestrict (w_H W3) mem3) (prh_lin Lam3) doc t D).
{ apply (c4_tree_keep lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc cntW 0 0 _ FP1 ly3 S3 Hp3 W3 mem3 md3 k1 D doc t Lam3
    cid pos' HL HJ1 Hfin').
  - rewrite (Efa0 cid pos'). exact Hfa1.
  - rewrite (Efa0 cid pos'). exact Hfa2.
  - intros a Ha Hf. apply HFPin in Hf.
    apply (c4_doc_off_frame lyc Sc Hpc Wc memc mdc kj pos a HJ Ha). unfold CRT_OFF_BACK in Hf. lia.
  - intros a k y Hak Hy Hf. apply HFPin in Hf.
    apply (c4_blk_off_frame lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc cntW 0 0 a k y HL (HDL _ Hak) Hy). lia.
  - exact HDL.
  - intros a k Hak. exact (HBK3 a k (HDL _ Hak)).
  - intros bk Hbk. exact (HLam3 bk (HDL _ Hbk)).
  - exact HDOC. }
assert (HCT3 : pj_nodeR SEGS (mrestrict (w_H W3) mem3) (prh_lin Lam3) (F + CRT_OFF_COPY) tcB Dc).
{ apply (c4_tree_keep lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc cntW 0 0 _ FP1 ly3 S3 Hp3 W3 mem3 md3 k1 Dc
    (F + CRT_OFF_COPY) tcB Lam3 CRT_CID pos HL HJ1 Hinf).
  - unfold CRT_OFF_COPY. lia.
  - rewrite cb4_fb. unfold CRT_OFF_COPY. lia.
  - intros a Ha Hf. apply HFPin in Hf. unfold CRT_OFF_COPY, CRT_OFF_BACK in *. lia.
  - intros a k y Hak Hy Hf. apply HFPin in Hf.
    apply (c4_blk_off_frame lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc cntW 0 0 a k y HL (HDcL _ Hak) Hy). lia.
  - exact HDcL.
  - intros a k Hak. exact (HBK3 a k (HDcL _ Hak)).
  - intros bk Hbk. exact (HLam3 bk (HDcL _ Hbk)).
  - exact HCT. }
assert (HFD3 : pj_fdR SEGS (mrestrict (w_H W3) mem3) (prh_lin Lam3) DOC_D (F + CRT_OFF_COPY) Dc).
{ apply (cb4_fdR_mono SEGS _ _ (PjTree.depth tcB)); [exact (cm_crt_depth_doc t (cm_in_depth x t HIN))|].
  exact (cb4_nodeR_fdR SEGS tcB _ _ _ _ HCT3). }
(* copy's free order, kept the same way *)
assert (HFO3 : exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W3) mem3) (prh_lin Lam3) DOC_D (F + CRT_OFF_COPY) Dc Fc /\
  map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (@crt_tree_J t)).
{ destruct HFOc as (Fc & HFc & EFc). exists Fc. split; [|exact EFc].
  apply (c4_tree_keep_fo lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc cntW 0 0 _ FP1 ly3 S3 Hp3 W3 mem3 md3 k1 Dc
    (F + CRT_OFF_COPY) DOC_D Fc Lam3 CRT_CID pos HL HJ1 Hinf).
  - unfold CRT_OFF_COPY. lia.
  - rewrite cb4_fb. unfold CRT_OFF_COPY. lia.
  - intros a Ha Hf. apply HFPin in Hf. unfold CRT_OFF_COPY, CRT_OFF_BACK in *. lia.
  - intros a k y Hak Hy Hf. apply HFPin in Hf.
    apply (c4_blk_off_frame lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc cntW 0 0 a k y HL (HDcL _ Hak) Hy). lia.
  - exact HDcL.
  - intros a k Hak. exact (HBK3 a k (HDcL _ Hak)).
  - intros bk Hbk. exact (HLam3 bk (HDcL _ Hbk)).
  - exact HFc. }
(* the read-only view, the spills, the shadow of the three locals and of the document *)
assert (HRO3 : arodata_okP SEGS RLO RHI B (aview SEGS (w_H W3) mem3)).
{ intros a Hro Hno Her. rewrite (G3 a); [exact (HRO a Hro Hno Her) | exact (cb4_ro_img a Hro) | exact Hno | exact Her
    | intros Hps; exact (pst_not_ro_B a Hps Hro) |].
  apply fp_spares_closed. apply sink_closed_pos. unfold FP1.
  constructor; [cbn [fst]; unfold CRT_OFF_BACK; lia | constructor]. }
assert (KS : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply G1; lia. }
assert (KFsh : forall cid0 pos0 a, In (cid0, pos0) (frames Sc) ->
  shadow_addr (frame_addr lyc cid0 pos0) <= a < shadow_addr (frame_addr lyc cid0 pos0) + fs_frame_bytes cid0 / 8 ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H Wc) memc a).
{ intros cid0 pos0 a Hin0 Ha. apply (G4 cid0 pos0 a Hin0); [right; unfold in_zr; cbn [fst snd]; lia|].
  apply HnFPsh.
  destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc cid0 pos0 HARc Hin0) as (Q1 & Q2 & Q3).
  pose proof (fs_frame_bytes_nonneg cid0).
  assert (frame_addr lyc cid0 pos0 / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  assert (fs_frame_bytes cid0 / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  assert (0 <= frame_addr lyc cid0 pos0 / 8) by (apply Z.div_pos; lia).
  unfold shadow_addr in Ha. lia. }
assert (HRAslot : forall off, 0 <= off -> off + 56 <= 512 -> off mod 8 = 0 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F + off) 56 ->
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (F + off) 56).
{ intros off Ho1 Ho2 Ho3 HR. apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HR].
  intros y Hy. unfold shadow_of_addr. apply (KFsh CRT_CID pos (SHADOW_OFF + y / 8) Hinf). rewrite cb4_fb.
  change (512 / 8) with 64.
  pose proof (c4_slot_sh F 512 y ltac:(lia) F32 ltac:(lia)) as Hss.
  change ((512 + 7) / 8) with 64 in Hss. exact Hss. }
assert (HRAd3 : range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF doc 56).
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAd].
  intros y Hy. unfold shadow_of_addr. apply (KFsh cid pos' (SHADOW_OFF + y / 8) Hfin').
  rewrite (Efa0 cid pos').
  destruct (alx_frames _ _ _ LAWS ly S Hp W mem md cid pos' cb4_ar0 Hfin) as (Fa32 & _).
  set (fa := frame_addr ly cid pos') in *. set (fsb := fs_frame_bytes cid) in *.
  destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md cid pos' cb4_ar0 Hfin) as (Q1 & Q2 & Q3).
  apply Z.mod_divide in Fa32; [|lia]. destruct Fa32 as (g & Hg).
  apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as (dd & Hdd).
  assert (Efs : (fa + fsb) / 8 = 4 * g + fsb / 8).
  { rewrite Hg. replace (g * 32 + fsb) with (fsb + (4 * g) * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (Hm : (doc + 56) / 8 <= (fa + fsb) / 8) by (apply Z.div_le_mono; lia).
  assert (Ed : (doc + 56) / 8 = dd + 7) by (rewrite Hdd; replace (dd * 8 + 56) with ((dd + 7) * 8) by lia; apply Z.div_mul; lia).
  assert (Efa8 : fa / 8 = 4 * g) by (rewrite Hg; replace (g * 32) with (4 * g * 8) by lia; apply Z.div_mul; lia).
  unfold shadow_addr. rewrite Efa8.
  pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia. }
(* the live state after the call, for each arm's blocks *)
assert (HFP : forall a, inFP FP1 a -> a < YM05.alloc_ceiling /\ in_app a 1 /\
  ~ (frame_addr lyc CRT_CID pos + 504 <= a < frame_addr lyc CRT_CID pos + 512)).
{ intros a Ha. apply HFPin in Ha. split; [lia|]. split; [apply (in_app_sub _ _ _ _ Fb3); lia | lia]. }
assert (HSD3 : sideB ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 0 ran3).
{ refine {| crt_side_ledger := HLED3; crt_side_peak := _; crt_side_room := HRL3; crt_side_arodata := HRO3;
            crt_side_doc := HDOC3; crt_side_doc_blocks := _ |}.
  - rewrite Epk3; lia.
  - intros bk Hbk. exact (HLam3 bk (HDL _ Hbk)). }
assert (HLV : forall Dx', Permutation Lam3 (Dx' ++ Lam) ->
  Permutation (ablocks B ly3 S3) (ablocks B ly S ++ ck_hblks Dx') -> (forall bk, In bk Dx' -> ~ In bk D) ->
  liveB (prh_wk F_check_round_trip) ly3 S3 Hp3 W3 mem3 md' (kj + k1) pos Dx' Lam3 peak3 cnt3 0 ran3).
{ intros Dx' P1 P2 P3.
  pose proof (cb4_live_call lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc cntW 0 0 (@STK_parse_noting prh_img_B) FP1
    ly3 S3 Hp3 W3 mem3 md3 k1 Dx' Lam3 peak3 cnt3 0 ran3 HL (ex_intro _ WS3 (conj HJ3 HB3)) HJ1
    ltac:(vm_compute; discriminate) HFP HSD3 P1 P2 P3 HMN3) as HLr.
  exact (cb4_live_rejournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLr HJ3' HB3). }
(* the spills after the call, at the post's layout *)
assert (HSPV : forall off v, sp1 + off + 8 <= 2 ^ 64 -> 0 <= off -> spillB Wc memc off v -> spillB W3 mem3 off v).
{ intros off v Ho1 Ho2 Hv. apply (ts_vm_av (w_H Wc) (w_H W3) memc mem3 _ 8 _); [|exact Hv].
  intros i Hi. apply KS. lia. }
assert (Hsp64 : sp1 + 200 <= 2 ^ 64) by lia.
(* the writer's count: cntW = cwB cset + wcalls of the rewrite (the write succeeded) *)
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran _ _ HLED0) as (_ & _ & Hcnt64 & _).
assert (Hcnt0 : 0 <= cnt < 2 ^ 62 - 2 ^ 30) by lia.
assert (Ecw : cwB cset = ck_cnt2 cnt t + 1 + cset) by (unfold crt_cw; rewrite cm_cnt2_eq; lia).
destruct (cm_cnt_write x t msv cset cnt HIN Et Hcs Hcnt0) as (Hcw0 & Hcw1).
assert (EwP : WriterValue.wdpieces (ck_crt_tree t) true = wPB) by reflexivity.
destruct (cm_pjw_succ ok (cwB cset) SIZE_MAXZ (ck_crt_tree t) true ltac:(lia) ltac:(lia) Hfail0) as (Ek & EcntW).
rewrite EwP in Ek, EcntW. fold cntW in EcntW.
exists Lam3, peak3, cnt3.
split; [exact R26'|].
(* g_ran_out = 0 (the reading granted: the text's outcome clause, t4_goal_pn's ran' = 0): the L0 state *)
subst ran3.
  assert (Hreg21 : forall rcv : Z, getr regs3 10 = w64 rcv -> (rcv = 0 \/ rcv = -1) ->
    getr rg' 21 = w64 (if q =? 0 then 1 else if rcv =? 0 then 0 else 1)).
  { intros rcv Hr Hrc. rewrite R21', Hr, Eq0. destruct Hrc as [-> | ->]; vm_compute; reflexivity. }
  assert (Hcommon : forall Dx' rcv,
    liveB (prh_wk F_check_round_trip) ly3 S3 Hp3 W3 mem3 md' (kj + k1) pos Dx' Lam3 peak3 cnt3 0 0 ->
    getr regs3 10 = w64 rcv -> (rcv = 0 \/ rcv = -1) ->
    (match res with
     | Some tv => rcv = 0 /\ posB S3 (crt_evs_L0 msv) /\ exists Dback,
         Dx' = Dback ++ (q, cap) :: Dc /\
         pj_nodeR SEGS (mrestrict (w_H W3) mem3) (prh_lin Lam3) (F + CRT_OFF_BACK) tv Dback /\
         Permutation (map (fun b => snd b + cf_head) Dback) (PresetReqAtNoMiss.tblk tcB) /\
         (exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W3) mem3) (prh_lin Lam3) DOC_D (F + CRT_OFF_BACK) Dback Fb /\
          map (fun b => snd b + cf_head) Fb = PresetReqAt.fo tcB)
     | None => rcv = -1 /\ Dx' = (q, cap) :: Dc
     end) ->
    atL0B fx3 ly3 S3 Hp3 W3 mem3 md' (kj + k1) pos Dc Dx' Lam3 peak3 cnt3 rg' msv cset q rcv).
  { intros Dx' rcv HLV' Hr Hrc Hmatch.
    refine {| crt_at_L0_B_obj := Et; crt_at_L0_B_frm_zero := HFZ3;
              crt_at_L0_B_fregs := cb4_fregs_trans fx fxk fx3 HFK HFK3; crt_at_L0_B_live := HLV';
              crt_at_L0_B_dregs := _; crt_at_L0_B_saved := R24'; crt_at_L0_B_flag := Hreg21 rcv Hr Hrc;
              crt_at_L0_B_sp_back := _; crt_at_L0_B_sp_shn := _; crt_at_L0_B_sp_pn := _; crt_at_L0_B_sp_n := _;
              crt_at_L0_B_doc_align := Hd8; crt_at_L0_B_doc_open := HRAd3; crt_at_L0_B_back_open := _;
              crt_at_L0_B_v_open := _; crt_at_L0_B_cset_range := Hcs; crt_at_L0_B_cset_mod := Hcs0;
              crt_at_L0_B_copy := _; crt_at_L0_B_copy_fd := _; crt_at_L0_B_copy_tblk := HCPc eq_refl;
              crt_at_L0_B_copy_fo := _; crt_at_L0_B_copy_depth := HDPc; crt_at_L0_B_outcome := _ |};
      try rewrite EF.
    { exact HDR'. }
    { apply HSPV; [unfold CRT_SP_BACK; lia | unfold CRT_SP_BACK; lia | exact HSPB]. }
    { apply HSPV; [unfold CRT_SP_SHN_B; lia | unfold CRT_SP_SHN_B; lia | exact HSPS]. }
    { apply HSPV; [unfold CRT_SP_PN_B; lia | unfold CRT_SP_PN_B; lia | exact HSPP]. }
    { apply HSPV; [unfold CRT_SP_N_B; lia | unfold CRT_SP_N_B; lia | exact HSPN]. }
    { apply HRAslot; [unfold CRT_OFF_BACK; lia | unfold CRT_OFF_BACK; lia | reflexivity | exact HRAb]. }
    { apply HRAslot; [unfold CRT_OFF_V; lia | unfold CRT_OFF_V; lia | reflexivity | exact HRAv]. }
    { exact HCT3. }
    { exact HFD3. }
    { exact HFO3. }
    exists ok. split; [exact HOK|]. right. split; [exact Hq0|]. split; [exact Hfail0|].
    exists okr, res, tr. split; [exact Hjr|]. split; [exact Hoks|]. split; [exact Ecnt3|].
    split; [exact (Hok3 eq_refl)|]. exact Hmatch. }
  destruct res as [tv|].
  + destruct Hres as (R10 & Dr & HPLr & HLszr & HNLr & HFOr & HFrr & HPBr & HNDr).
    exists (Dr ++ (q, cap) :: Dc), 0.
    apply (Hcommon _ 0); [| exact R10 | left; reflexivity |].
    * apply HLV.
      -- rewrite <- app_assoc. eapply perm_trans; [exact HPLr|]. apply Permutation_app_head. exact HPL.
      -- eapply perm_trans; [exact HPBr|]. eapply perm_trans; [apply Permutation_app_tail; exact HPB|].
         rewrite <- app_assoc. apply Permutation_app_head. unfold ck_hblks. rewrite map_app.
         apply Permutation_app_comm.
      -- intros [a k] Hbk HbD. apply in_app_or in Hbk as [Hbk | Hbk].
         ++ apply (HFrr a k Hbk).
            exact (proj1 (proj2 (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntW SIZE_MAXZ 0 a k _ _ HLED
              (HDL _ HbD)))).
         ++ exact (HAP _ Hbk HbD).
    * split; [reflexivity|]. split.
      -- refine {| crt_pos_strtod := Esm; crt_pos_ex := _ |}.
         exists (pre ++ PresetReqAt.parse_evs rp_sm tbB []), histp.
         refine {| crt_pos_split := _; crt_pos_room := _; crt_pos_run := _; crt_pos_cons := _ |}.
         ++ rewrite Hpre, app_assoc. reflexivity.
         ++ rewrite length_app, Nat.add_assoc. exact HPOSp.
         ++ rewrite length_app, Nat.add_assoc. exact Hpos2b.
         ++ rewrite length_app, Nat.add_assoc. exact HCF2.
      -- exists Dr. split; [reflexivity|]. split; [exact HNDr|].
         split; [exact (cb4_back_tblk okr tv tr Dr Hjr HLszr)|].
         destruct (cb4_back_fo okr tv tr Hjr) as (Hdtv & Efo).
         destruct (HFOr eq_refl DOC_D Hdtv) as (Fb & HFb & EFb).
         exists Fb. split; [exact HFb|]. rewrite EFb. exact Efo.
  + destruct Hres as (R10 & HPLr & HPBr & HZr).
    exists ((q, cap) :: Dc), (-1).
    apply (Hcommon _ (-1)); [| exact R10 | right; reflexivity | split; reflexivity].
    apply HLV; [eapply perm_trans; [exact HPLr | exact HPL] | eapply perm_trans; [exact HPBr | exact HPB] | exact HAP].
Qed.

(* ======================================================================================================== *)
(* PART C: from S (+0x2d4) the run reaches QF, given that it does from O2 (+0x2f0), with the parse_noting call
   taken through the named goal t4_goal_pn. kb round: S is at 64 = prh_wk F_round_trip_text + prh_wk
   F_round_trip_text; the strlen wrapper's rule is over ajournal_x, so the journal is rebased to the current depot
   and stepped back to its budget after it (YCbqGwild.ajournal_xw_rebase / ajournal_xw_unbase0, Crt102Rewrite's
   crt102rw_strlen_call); the parse_noting call's room comes from the text's entry room HWR0 and the journal at 64
   (YCbqGwild.ajournal_xw_room, wild_room_le: 66 - 64 >= 2, crt4_kb_pn), the call runs over the budgeted rule
   YCbqGwild.aj_call_xbF_sp at the callee's budget prh_wk F_parse_noting, and the caller lands at WS0 ++ WS1 at the
   budget 64 + 2 <= 66 (YCbqGwild.wbudget_app; the A' twin is Crt102Rewrite.crt102rw_wild_budget_pn_goal). *)
Lemma crt4_lane_S_at : t4_goal_pn -> CRT4_O2 -> CRT4_S.
Proof.
intros HG HO2 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc rg msv cset (ok & q & HC & Hq0 & R24).
pose proof HC as (Et & HFZ & HFK & HOK & HL & HDR & R21 & R26 & HSPB & HSPS & HSPP & HSPN & Hd8 & HRAd & HRAb & HRAv
  & Hcs & Hcs0 & HCT & HCP & HDP & HFO & HBS & HOR).
destruct HOR as [(Hfail0 & _ & HnIn & Hcapgt & Hby & Hpos) | (_ & Hq00)]; [|lia].
assert (Eq0 : (q =? 0) = false) by (apply Z.eqb_neq; exact Hq0).
rewrite Eq0 in HL.
cb4_rd_live HL WS0 HJ HB0 HSD HPL HPB HAP HSV HFRM HSPF HCR HCH HMNl.
cb4_rd_side HSD HLED HPK HRL HRO HDOC HDL.
pose proof (crt_dregs_B_bregs HDR) as HBR. pose proof (crt_dregs_B_s6 HDR) as R22.
cb4_rd_bregs HBR R2 R3 R4 R8 R9 R18 R20 R19 R23 R25 R27.
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ) as (Hinf & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof cb4_sp as (Hal16 & Hceil & H47 & Hs1 & Hs32 & Hs1b).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as ((HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac & Hfz0).
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
set (F := frame_addr lyc CRT_CID pos) in *.
set (cap := WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB)) in *.
set (cntW := WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (cwB cset) SIZE_MAXZ) wPB)) in *.
set (lenb := Z.of_nat (length tbB)) in *.
(* the text block is on the ledger *)
assert (HqL : In (q, cap) Lamc).
{ apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. left. reflexivity. }
destruct (c4_blk_facts lyc Sc Hpc Wc memc mdc kj pos ((q, cap) :: Dc) Lamc peakc cntW 0 0 q cap lenb HL HqL
  ltac:(unfold lenb; lia) ltac:(lia)) as (Hq4096 & Hqce & Hqapp & Hamr & HRAq & HHUq & HTailq & Hprq).
(* the text's bytes, all nonzero *)
destruct (proj1 (garr8_app SEGS (mrestrict (w_H Wc) memc) q tbB [0]) Hby) as (Hbt & _).
assert (Hnz : Forall (fun c => c <> 0) tbB).
{ eapply Forall_impl; [|exact (cm_wdoc_pos ReaderRes.jr_strtod (ck_crt_tree t) true (cm_in_crt_wf x t HIN))].
  cbv beta. intros a Ha. lia. }
assert (Etb : WriterValue.wdoc (ck_crt_tree t) true = tbB) by reflexivity.
destruct (cm_in_wlen_crt x t HIN) as (Hlw1 & Hlw2 & Hlw3).
rewrite Etb in Hlw1, Hlw2, Hlw3. fold lenb in Hlw1, Hlw2, Hlw3.
unfold PRH_FnWriter.prhWriter_WMAX in Hlw2.
pose proof (cm_in_maxrun_crt x t HIN) as Hmaxrun. rewrite Etb in Hmaxrun.
unfold crt_cfg.
assert (HS : st_ok_pi SEGS VAL (TEB regs rg []) (mkSS (CRT_PC_B + CRT4_S_OFF_B) cur_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT4_S_OFF_B))) memc (YK11.seg_rom SEGS)))).
{ apply (@ts_st_ok fxk); [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TEB regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TEB regs rg [])) by apply te_env.
pose (RUN := @Crt102Kit.crt_run_xw fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS).
paj_run_tok_x (RUN WS0) HS HJ SHOK (0, 0).
{ apply awr_ok_nil. }
apply frame_of_read_only in HF; [|vm_compute; reflexivity].
rewrite HF in HJ.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
assert (X10 : getr (ms_regs ms) 10 = w64 q) by (rewrite Q10, <- R24; te_close).
assert (X2 : getr (ms_regs ms) 2 = w64 CRT_sp1) by (rewrite Q2, <- R2; te_close).
assert (X3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, <- Hgp, <- R3; te_close).
assert (X4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, <- Htp, <- R4; te_close).
assert (X9 : getr (ms_regs ms) 9 = w64 CRT_sp1) by (prreg HS (9%bv : bv 5) Q9; rewrite Q9, <- R9; te_close).
assert (X1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + (CRT4_S_OFF_B + 8))))
  by (rewrite Q1; vm_compute; reflexivity).
assert (Hspms : spZ (ms_regs ms) = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite X2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (KR : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) rr = getr rg rr).
{ intros rr Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [cb4_keep HS |]). destruct Hr. }
assert (HDR1 : dregsB (ms_regs ms) F).
{ apply (cb4_dregs_eq rg); [exact HDR|]. intros r0 Hr0. apply KR. unfold CB4_DREGS in Hr0.
  cbn [In] in Hr0 |- *. tauto. }
assert (X24 : getr (ms_regs ms) 24 = w64 q) by (rewrite KR by (cbv; tauto); exact R24).

pmkst HS. rewrite HF.
(* ---- the strlen call (ASTRLEN through the engine's YGcallMxmn.aj_strlen_at_xromR at RZW, under YA0nH.SRr_SRr'): a0 = q, the
   text q .. q + |tbB| with its NUL. The rule is over ajournal_xR: the journal rebased to the current depot
   (YCbqGwild.ajournal_xw_rebaseR) and stepped back to its budget WS0 after it (YCbqGwild.ajournal_xw_unbase0R, from
   the journal's wild clause) ---- *)
pose proof (Crt102Kit.crt_jw_wild B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  eapply (YGcallMxmn.aj_strlen_at_xromR (fx := fxk) (SK := SK) SEGS B PST ARx RLO RHI LAWS (@pa_segs_low _ _ PA)
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
    (SIGMA AS___wrap_strlen) (ASTRLEN fxk) Wc (ms_regs ms) memc STKC sp0 [] ly (set_depot (st_depot Sc) S) Hp W
    mem md [(CRT_CID, pos)] lyc Sc Hpc _ kj q lenb (sp1 - sp0) _ HJr).
  - exact X10.
  - lia.
  - unfold lenb; lia.
  - lia.
  - pose proof (YM05.alloc_ceiling_val). lia.
  - exact Hspms.
  - apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [u Hu].
    apply Z.mod_divide in Hs32; [|lia]. destruct Hs32 as [u' Hu'].
    apply Z.mod_divide; [lia|]. exists (2 * u' - u). lia.
  - lia.
  - rewrite cb4_stkc. unfold ESTACK. lia.
  - exact X3.
  - exact X4.
  - exact X1.
  - apply (ret_ok_codeptr_v (PI := PA));
      [split; vm_compute; first [discriminate | reflexivity] | vm_compute; reflexivity].
  - exact (c4_first_byte Wc memc q tbB Hby Hnz).
  - replace (lenb + 1) with (Z.of_nat (length (tbB ++ [0]))) by (rewrite length_app; cbn [length]; unfold lenb; lia).
    apply (c4_src_ok Wc (ms_regs ms) memc q (tbB ++ [0]) Hby).
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite Hspms.
    pose proof (YM05.alloc_ceiling_val). unfold ESTACK, lenb in *. lia.
  - intros a Ha. pose proof (YM05.alloc_ceiling_val). unfold ESTACK, lenb in *. lia.
  - exact Hamr.
  - exact HRAq.
  - exact HHUq.
  - exact HTailq.
  - exact HRO. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hlen2 & Hfr2 & Hpres2 & Hmn2).
eapply YCbqGwild.ajournal_xw_unbase0R in HJ2; [|exact Hinc].
(* ---- the live state at mem2: the call wrote only its own stack window ---- *)
assert (Hag2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. apply Hfr2; [exact Ha|]. lia. }
pose proof (c4_live_stk lyc Sc Hpc Wc memc mem2 _ _ kj kj pos _ Lamc peakc cntW 0 0 HL HJ2 HB0 Hag2
  (fun H0 => Hmn2 (HMNl H0))) as HL2.
(* the spill of &back and the registers at the parse_noting call *)
assert (HSPB2 : spillB Wc mem2 CRT_SP_BACK (F + CRT_OFF_BACK)).
{ apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem2 _ 8 _); [|exact HSPB].
  intros i Hi. apply Hag2; [unfold CRT_SP_BACK; lia|]. unfold CRT_SP_BACK, ESTACK. lia. }
assert (E64 : ew (TEB regs regs2 [w64 (F + CRT_OFF_BACK)]) 64 = w64 (F + CRT_OFF_BACK)).
{ change 64%nat with (64 + 0)%nat. rewrite te_more_lt by lia. reflexivity. }
assert (X9b : getr regs2 9 = w64 sp1)
  by (rewrite (ts_ap (ms_regs ms) regs2 9%bv HP2) by ts_cs; exact X9).
assert (E9 : bv_unsigned (ew (TEB regs regs2 [w64 (F + CRT_OFF_BACK)]) (xr 9)) = sp1).
{ unfold xr. rewrite (te_curB regs regs2 _ 9%bv 9) by reflexivity. rewrite X9b.
  apply unsigned_lit_small. lia. }
assert (HS2 : st_ok_pi SEGS VAL (TEB regs regs2 [w64 (F + CRT_OFF_BACK)])
  (mkSS (CRT_PC_B + (CRT4_S_OFF_B + 8)) cur_atoms
     [YP09.mkRegion (Some (xr 9)) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 64 0))]] None (mkFacts [] [] []))
  (restrict (w_H Wc) (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRT_PC_B + (CRT4_S_OFF_B + 8)))) mem2
     (YK11.seg_rom SEGS)))).
{ apply ts_st_ok.
  - apply te_regs_ok.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (ts_rok (TEB regs regs2 [w64 (F + CRT_OFF_BACK)]) _ (xr 9) sp1); [exact E9 | lia | lia | intros o Ho; lia | constructor; [|constructor]].
    apply (ts_chunk (TEB regs regs2 [w64 (F + CRT_OFF_BACK)]) _ _ 56 8 (SOff 64 0) (F + CRT_OFF_BACK)).
    + cbn [sv_denot]. rewrite E64, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + unfold CRT_OFF_BACK. change (8 * Z.of_N 8) with 64. lia.
    + cbn. lia.
    + exact HSPB2.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [exact I | split; exact I]. }
assert (SHOK2 : sh_ok SEGS (SLit 0) [] (TEB regs regs2 [w64 (F + CRT_OFF_BACK)]) (mrestrict (w_H Wc) mem2)) by apply Forall_nil.
assert (HEI2 : img_env VAL A_LIM (TEB regs regs2 [w64 (F + CRT_OFF_BACK)])) by (apply te_env).
clear HS SHOK HEI.
paj_run_tok_x (RUN WS0) HS2 HJ2 SHOK2 (0, 0).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 9) sp1); [reflexivity | exact E9 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
  apply awr_ok_nil. }
apply frame_of_read_only in HF0; [|vm_compute; reflexivity].
cb4_rd_live HL2 WS2x HJ2x HB2x HSD2 HPL2 HPB2 HAP2 HSV2 HFRM2 HSPF2 HCR2 HCH2 HMN2x.
cb4_rd_side HSD2 HLED2 HPK2 HRL2 HRO2 HDOC2 HDL2.
assert (KR2 : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms0) rr = getr regs2 rr).
{ intros rr Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [cb4_keep HS2 |]). destruct Hr. }
assert (HDR2 : dregsB regs2 F) by (apply (cb4_dregs_pres (ms_regs ms)); [exact HDR1 | exact HP2]).
pose proof (crt_dregs_B_bregs HDR2) as HBR2. pose proof (crt_dregs_B_s6 HDR2) as R22b.
cb4_rd_bregs HBR2 R2b R3b R4b R8b R9bb R18b R20b R19b R23b R25b R27b.
assert (Y2 : getr (ms_regs ms0) 2 = w64 sp1) by (rewrite KR2 by (cbv; tauto); exact R2b).
assert (Y8 : getr (ms_regs ms0) 8 = w64 sp0) by (rewrite KR2 by (cbv; tauto); exact R8b).
assert (Y3 : getr (ms_regs ms0) 3 = w64 (as_gp B)) by (rewrite KR2 by (cbv; tauto); rewrite R3b; exact Hgp).
assert (Y4 : getr (ms_regs ms0) 4 = w64 (as_tp B)) by (rewrite KR2 by (cbv; tauto); rewrite R4b; exact Htp).
assert (Hsp0' : spZ (ms_regs ms0) = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite Y2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hs0z : s0Z (ms_regs ms0) = sp0).
{ unfold s0Z. rewrite Y8. unfold w64. apply unsigned_lit_small.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
prreg HS2 (10%bv : bv 5) P10. prreg HS2 (11%bv : bv 5) P11. prreg HS2 (12%bv : bv 5) P12.
prreg HS2 (1%bv : bv 5) P1.
assert (Y10 : getr (ms_regs ms0) 10 = w64 q).
{ rewrite P10. rewrite (te_curB regs regs2 _ 24%bv 24) by reflexivity.
  rewrite (ts_ap (ms_regs ms) regs2 24%bv HP2) by ts_cs. exact X24. }
assert (Y11 : getr (ms_regs ms0) 11 = w64 lenb).
{ rewrite P11. rewrite (te_curB regs regs2 _ 10%bv 10) by reflexivity. exact Hlen2. }
assert (Y12 : getr (ms_regs ms0) 12 = w64 (F + CRT_OFF_BACK)).
{ rewrite P12. change 64%nat with (64 + 0)%nat. rewrite te_more_lt by lia. reflexivity. }
assert (Y1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + CRT_N_OFF_B)))
  by (rewrite P1; vm_compute; reflexivity).
(* the text at mem2 *)
assert (Hbt2 : bytes_at Wc mem2 q tbB).
{ intros j Hj. split; [|exact (proj2 (Hbt j Hj))].
  apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem2 _ 1 _); [|exact (proj1 (Hbt j Hj))].
  intros i Hi. pose proof (YM05.alloc_ceiling_val). apply Hag2; unfold ESTACK, lenb in *; lia. }
assert (HRAq2 : range_addressable (aview SEGS (w_H Wc) mem2) SHADOW_OFF q lenb).
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|apply (range_addressable_sub _ _ q (lenb + 1)); [exact HRAq | lia | lia]].
  intros y Hy. unfold shadow_of_addr. destruct (c4_shadow_lo y ltac:(unfold lenb in *; lia)) as (Hz0 & Hz2).
  pose proof (YM05.alloc_ceiling_val). apply Hag2; unfold ESTACK; lia. }
assert (HHUq2 : 0 < lenb -> shadow_hull_vis (aview SEGS (w_H Wc) mem2) q lenb).
{ intros Hl0 s Hs.
  assert (Hsub : shadow_hull_vis (aview SEGS (w_H Wc) memc) q lenb)
    by (apply (c4_hull_sub _ q (lenb + 1) q lenb HHUq); lia).
  destruct (c4_shadow_lo q ltac:(lia)) as (Hz0 & Hz2).
  destruct (c4_shadow_lo (q + lenb - 1) ltac:(unfold lenb in *; lia)) as (Hz3 & Hz4).
  unfold shadow_addr in Hs.
  set (u := SHADOW_OFF + q / 8) in *. set (v := SHADOW_OFF + (q + lenb - 1) / 8) in *.
  pose proof (Z.div_mod u 8 ltac:(lia)). pose proof (Z.mod_pos_bound u 8 ltac:(lia)).
  pose proof (Z.div_mod v 8 ltac:(lia)). pose proof (Z.mod_pos_bound v 8 ltac:(lia)).
  pose proof (YM05.alloc_ceiling_val).
  rewrite Hag2; [exact (Hsub s Hs) | unfold ESTACK in *; lia | unfold ESTACK in *; lia]. }
(* the back slot: its shadow hull and its range at mem2 *)
assert (HHUb : shadow_hull_vis (aview SEGS (w_H Wc) mem2) (F + CRT_OFF_BACK) 56).
{ apply (c4_back_hull Wc mem2 F ltac:(lia) F32). intros i Hi. apply Hpres2. exact (proj1 (Fsh i Hi)). }
assert (HRAb2 : range_addressable (aview SEGS (w_H Wc) mem2) SHADOW_OFF (F + CRT_OFF_BACK) 56).
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAb].
  intros y Hy. unfold shadow_of_addr.
  destruct (c4_shadow_lo y ltac:(unfold CRT_OFF_BACK in *; lia)) as (Hz0 & Hz2).
  pose proof (YM05.alloc_ceiling_val). apply Hag2; unfold ESTACK; lia. }
assert (HSTKPN : @STK_parse_noting prh_img_B = 27216) by (vm_compute; reflexivity).
assert (HOUT : ck_out_ok B (@STK_parse_noting prh_img_B) lyc Sc Wc (ms_regs ms0) mem2 (F + CRT_OFF_BACK) 56).
{ pose proof (YM05.alloc_ceiling_val).
  split; [exists CRT_CID, pos; split; [exact Hinf|]; rewrite cb4_fb; unfold CRT_OFF_BACK; lia|].
  split; [unfold CRT_OFF_BACK; lia|]. split; [unfold CRT_OFF_BACK; lia|].
  split.
  { unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fb3.
    rewrite C3, C4, C5. unfold CRT_OFF_BACK, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
  split; [|split; [exact HRAb2 | intros _; exact HHUb]].
  intros a Ha. split; [|split].
  - apply apresent_writable. apply Hpres2. exact (proj1 (Ffr a ltac:(unfold CRT_OFF_BACK in *; lia))).
  - exact (proj2 (Ffr a ltac:(unfold CRT_OFF_BACK in *; lia))).
  - rewrite Hsp0', HSTKPN. unfold CRT_OFF_BACK in *. lia. }
(* src_rd's ceiling clause (the landing cut: `q + |tb| <= alloc_ceiling`): the buffer's block ends below
   alloc_ceiling (c4_blk_facts) and |tbB| < cap *)
assert (Hq8 : q + lenb <= YM05.alloc_ceiling) by (unfold lenb in *; lia).
(* the counters at the call *)
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran _ _ HLED0) as (_ & _ & Hcnt64 & _).
assert (Hcnt0 : 0 <= cnt < 2 ^ 62 - 2 ^ 30) by lia.
assert (Ecw : cwB cset = ck_cnt2 cnt t + 1 + cset) by (unfold crt_cw; rewrite cm_cnt2_eq; lia).
destruct (cm_cnt_write x t msv cset cnt HIN Et Hcs Hcnt0) as (Hcw0 & Hcw1).
assert (EwP : WriterValue.wdpieces (ck_crt_tree t) true = wPB) by reflexivity.
destruct (cm_pjw_succ ok (cwB cset) SIZE_MAXZ (ck_crt_tree t) true ltac:(lia) ltac:(lia) Hfail0) as (Ek & EcntW).
rewrite EwP in Ek, EcntW. fold cntW in EcntW.
destruct (cm_pjw_cap ok (cwB cset) SIZE_MAXZ (ck_crt_tree t) true
  ltac:(rewrite Etb; fold lenb; lia) Hfail0) as (Hc0 & Hc1).
rewrite EwP in Hc0, Hc1. fold cap in Hc0, Hc1.
assert (Hpn21 : cntW + 2 * lenb + 2 < 2 ^ 64 - 1).
{ rewrite EcntW, Ecw.
  exact (cm_cnt_noting x t msv cset cnt (PjWriteHyp.wcalls (ck_crt_tree t) true) HIN Et Hcs Hcnt0 ltac:(lia)). }
(* the live room at the call *)
assert (Hbb : blocks_bytes Sc <= blocks_bytes S + LIVE_round_trip_text t false + LIVE_round_trip_text t true +
    PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
    PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT)) +
    PRH_FnWriter.LIVE_pj_write (ck_crt_tree t) true).
{ rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S).
  rewrite (YCbq.bsum_perm _ _ HPB), YCbq.bsum_app.
  rewrite (cm_bsum_hblks ((q, cap) :: Dc)). rewrite (cm_bsum_hblks Dc) in HBS.
  cbn [Ledger.lsum length]. rewrite Nat2Z.inj_succ. pose proof cf_head_nonneg. lia. }
(* the room position: the reading's events are the prefix the walk holds *)
assert (Ecs : WriterValue.wdoc (PresetReqAt.copy_set msv) true = tbB) by (rewrite Et; reflexivity).
rewrite Ecs in Hpos.
pose proof (crt_pos_strtod Hpos) as Esm. destruct (crt_pos_ex Hpos) as (pre & histw & HApos).
pose proof (crt_pos_split HApos) as Hpre. pose proof (crt_pos_room HApos) as Hpos1.
pose proof (crt_pos_run HApos) as Hpos2. pose proof (crt_pos_cons HApos) as HCF.
apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in Hpos2. destruct Hpos2 as (Hpos2a & Hpos2b).
rewrite length_app in HCF. apply PRH_Base.prh_cons_from_app_iff in HCF as [HCFa HCFb].
(* the chain at the call *)
destruct (cb4_chain [(CRT_CID, pos)] lyc Sc Hpc Wc (ms_mem ms0) _ kj HJ2 ltac:(rewrite HF0; exact HSV2))
  as (ch1 & Hch1 & Ech1).
pose proof HJ2 as (_ & HLYc & _ & _ & _ & HFRc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HRA31 : 0 <= BASE + (CRT_PC_B + CRT_N_OFF_B) < 2 ^ 31)
  by (split; vm_compute; first [discriminate | reflexivity]).
(* THE WILD ROOM the text asks at the call (PRH_FnCheck.v:638): the journal from the entry is at WS0 with
   wfresh [] WS0 <= 64, so the entry room 66 (HWR0) leaves 66 - wfresh [] WS0 >= 2 at Sc (YCbqGwild.ajournal_xw_room,
   wild_room_le, crt4_kb_pn) *)
pose proof crt4_kb_pn as Hkbpn.
assert (HWRpn : YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot Sc)).
{ unfold YCbqGwild.wbudget in HB0.
  apply (YCbqGwild.wild_room_le _ _ (prh_wk F_check_round_trip - YCbqGwild.wfresh [] WS0)); [clear - HB0 Hkbpn; lia|].
  eapply YCbqGwild.ajournal_xw_roomR; [exact HJ2 | exact HWR0 | clear - HB0 Hkbpn; lia]. }
(* ---- the parse_noting call, over the budgeted call rule at the text's budget wbudget [] (prh_wk F_parse_noting) ---- *)
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg ?mq ?mdq) _ =>
  eapply (@YCbqGwild.aj_call_xbF_spR fxk rc SK SEGS B PST ARx cf_head LAWS (@pa_segs_low _ _ PA)
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc
    (TEB regs regs2 [w64 (F + CRT_OFF_BACK)]) _ mq STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc mdq kj WS0
    (@STK_parse_noting prh_img_B) [(F + CRT_OFF_BACK, F + CRT_OFF_BACK + 56)] (sp1 - sp0) _ ch1
    (YCbqGwild.wbudget [] (prh_wk F_parse_noting)) _ HS2 eq_refl HJ2)
  end.
  - exact Hsp0'.
  - apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [u Hu].
    apply Z.mod_divide in Hs32; [|lia]. destruct Hs32 as [u' Hu'].
    apply Z.mod_divide; [lia|]. exists (2 * u' - u). lia.
  - lia.
  - rewrite HSTKPN. lia.
  - rewrite HSTKPN, cb4_stkc. lia.
  - exact Y3.
  - exact Y4.
  - exact Y1.
  - apply (ret_ok_codeptr_v (PI := PA));
      [split; vm_compute; first [discriminate | reflexivity] | vm_compute; reflexivity].
  - rewrite unsigned_lit_small by lia. vm_compute. discriminate.
  - rewrite Hs0z. replace (sp0 + (sp1 - sp0)) with sp1 by lia. exact Hch1.
  - intros HPRE1. rewrite HF0 in HPRE1 |- *.
    apply (HG fxk lyc Sc Hpc Wc (ms_regs ms0) mem2 _ ch1 q tbB (F + CRT_OFF_BACK) Lamc peakc cntW
      (rp_i + length pre)%nat histw).
    + split; [exact HPRE1|]. split; [exact HRO2|]. split.
      * rewrite Hsp0', Eshi. lia.
      * split; [unfold raZ; rewrite Y1, unsigned_lit_small by lia; pose proof (YM05.alloc_ceiling_val); lia
               | exact HFZ].
    + exact (HMN2x HMN).
    + exact HCL.
    + exact Y10.
    + exact Y11.
    + exact Y12.
    + exact Hlw3.
    + lia.
    + pose proof (YM05.alloc_ceiling_val). unfold lenb in *. lia.
    + split; [exact Hbt2|]. split; [lia|]. split; [exact Hq8|].
      split; [unfold amem_range; unfold YGcallMx.amem_range8 in Hamr; unfold lenb in *; lia|].
      split; [exact HRAq2 | exact HHUq2].
    + left. left. exists q, cap. split; [exact HqL | split; unfold lenb in *; lia].
    + exact Hmaxrun.
    + apply Z.mod_divide in F32; [|lia]. destruct F32 as [u Hu].
      apply Z.mod_divide; [lia|]. exists (4 * u + 4). unfold CRT_OFF_BACK. lia.
    + exact HOUT.
    + exact HLED2.
    + exact Hpn21.
    + exact (cm_live_read t (blocks_bytes S) (blocks_bytes Sc) HLIVE Hbb).
    + pose proof (cm_rq_read t HRQ) as Hrr. rewrite Etb in Hrr. exact Hrr.
    + rewrite HFRc. cbn [app length]. apply cm_frames_noting.
      pose proof (cm_frames_before (length (frames S)) HFR). lia.
    + exact HFZ.
    + exact HRL2.
    + (* the text's wild room (PRH_FnCheck.v:638), paid out of HWR0 above *)
      exact HWRpn.
    + (* the text's hull budget (PRH_FnCheck.v:661), paid from the run position *)
      exact (c4_hull_pn pre (crt_evs_L0 msv) (rp_i + length pre)%nat histw Sc tbB Esm Hpre Hpos1).
    + exact Hpos1.
    + exact Hpos2a.
    + exact Esm.
    + exact HCFa.
    + (* no injected failure in the reading's window: its calls are tcalls crt_tc, at most 2 |tb| + 2 *)
      pose proof (cm_ncalls_crt x t true HIN) as Enc. rewrite Etb in Enc.
      pose proof (cm_tcalls_wlen ReaderRes.jr_strtod (ck_crt_tree t) true (cm_in_crt_wf x t HIN)) as Htw.
      unfold PjWriteHyp.wlen in Htw. rewrite Etb in Htw. fold lenb in Htw.
      unfold SIZE_MAXZ. lia.
    + pose proof (cm_rqa_read t most HRQA) as Hrqa. rewrite Etb in Hrqa. exact Hrqa.
  - intros a Hfa. apply inFP_cons in Hfa as [Hfa | Hfa]; [|exfalso; exact (inFP_nil a Hfa)].
    right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite cb4_fb. unfold CRT_OFF_BACK in *. lia. }
cbv beta.
intros W3 c3 _ (fx3 & ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k1 & WS1 & -> & HFZ3 & HFK3 & HPW & HJ3 & HJ1 & HP3 & HQ3 &
  HMN3).
(* the caller's landing: WS0 ++ WS1 at the budget 64 + 2 <= 66 = prh_wk F_check_round_trip (YCbqGwild.wbudget_app) *)
assert (HB3 : YCbqGwild.wbudget [] (prh_wk F_check_round_trip) (WS0 ++ WS1)).
{ pose proof (YCbqGwild.wbudget_app [] _ _ WS0 WS1 HB0 HPW) as Hb. unfold YCbqGwild.wbudget in *.
  clear - Hb Hkbpn. lia. }
rewrite HF0 in HJ1. replace (sp0 + (sp1 - sp0)) with sp1 in HJ1 by lia.
(* the registers after the call *)
assert (HDR3a : dregsB (ms_regs ms0) F).
{ apply (cb4_dregs_eq regs2); [exact HDR2|]. intros r0 Hr0. apply KR2. unfold CB4_DREGS in Hr0.
  cbn [In] in Hr0 |- *. tauto. }
assert (HDR3 : dregsB regs3 F) by (apply (cb4_dregs_pres (ms_regs ms0)); [exact HDR3a | exact HP3]).
assert (R24c : getr regs3 24 = w64 q).
{ rewrite (ts_ap (ms_regs ms0) regs3 24%bv HP3) by ts_cs. rewrite KR2 by (cbv; tauto).
  rewrite (ts_ap (ms_regs ms) regs2 24%bv HP2) by ts_cs. exact X24. }
assert (R26c : getr regs3 26 = w64 (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B)).
{ rewrite (ts_ap (ms_regs ms0) regs3 26%bv HP3) by ts_cs. rewrite KR2 by (cbv; tauto).
  rewrite (ts_ap (ms_regs ms) regs2 26%bv HP2) by ts_cs. rewrite KR by (cbv; tauto). exact R26. }
(* ---- N (+0x2ec): `snez s5, a0`, then O2 (+0x2f0) ---- *)
assert (HS3 : st_ok_pi SEGS VAL (TEB regs regs3 []) (mkSS (CRT_PC_B + CRT_N_OFF_B) cur_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (@YK11.mkst fx3 regs3 (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_N_OFF_B))) mem3 (YK11.seg_rom SEGS)))).
{ apply (@ts_st_ok fx3); [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK3 : sh_ok SEGS (SLit 0) [] (TEB regs regs3 []) (mrestrict (w_H W3) mem3)) by apply Forall_nil.
assert (HEI3 : img_env VAL A_LIM (TEB regs regs3 [])) by apply te_env.
clear HS2 SHOK2 HEI2 HEI HEI0.
pose proof HJ3 as HJ3pre.
pose (RUN3 := @Crt102Kit.crt_run_xw fx3 rc SK B_prog_listing PL PA B PST ARx _ LAWS).
paj_run_tok_x (RUN3 (WS0 ++ WS1)) HS3 HJ3 SHOK3 (0, 0).
{ apply awr_ok_nil. }
lazymatch goal with H : frame_of (TEB regs regs3 []) _ mem3 _ |- _ =>
  apply frame_of_read_only in H; [|vm_compute; reflexivity]; rename H into HF3 end.
rewrite HF3 in HJ3.
prreg HS3 (21%bv : bv 5) Z21.
assert (KR3 : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms1) rr = getr regs3 rr).
{ intros rr Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [cb4_keep HS3 |]). destruct Hr. }
assert (HDR4 : dregsB (ms_regs ms1) F).
{ apply (cb4_dregs_eq regs3); [exact HDR3|]. intros r0 Hr0. apply KR3. unfold CB4_DREGS in Hr0.
  cbn [In] in Hr0 |- *. tauto. }
assert (R24d : getr (ms_regs ms1) 24 = w64 q) by (rewrite KR3 by (cbv; tauto); exact R24c).
assert (R26d : getr (ms_regs ms1) 26 = w64 (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B))
  by (rewrite KR3 by (cbv; tauto); exact R26c).
assert (R21d : getr (ms_regs ms1) 21 = alu64 ALU_SLTU (Z_to_bv 64 0) (getr regs3 10)).
{ rewrite Z21. rewrite (te_curB regs regs3 [] 10%bv 10) by reflexivity. reflexivity. }
(* the call state's facts at mem2 (the strlen call wrote only its stack window) *)
pose proof HJ2 as HJ2m. rewrite HF0 in HJ2m.
pose proof (cb4_live_rejournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 HJ2m HB0) as HL2q.
assert (HSPx2 : forall off v, spillB Wc memc off v -> 0 <= off -> off + 8 <= 200 -> spillB Wc mem2 off v).
{ intros off v Hv Ho1 Ho2. apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem2 _ 8 _); [|exact Hv].
  intros i Hi. apply Hag2; [lia|]. unfold ESTACK. lia. }
assert (HRAd2 : range_addressable (aview SEGS (w_H Wc) mem2) SHADOW_OFF doc 56).
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAd].
  intros y Hy. unfold shadow_of_addr. pose proof cb4_doc_home as (Hd1 & Hd2' & _).
  pose proof (YM05.alloc_ceiling_val).
  destruct (c4_shadow_lo y ltac:(lia)) as (Hz0 & Hz2). apply Hag2; unfold ESTACK; lia. }
assert (HRAv2 : range_addressable (aview SEGS (w_H Wc) mem2) SHADOW_OFF (F + CRT_OFF_V) 56).
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAv].
  intros y Hy. unfold shadow_of_addr. pose proof (YM05.alloc_ceiling_val).
  destruct (c4_shadow_lo y ltac:(unfold CRT_OFF_V in *; lia)) as (Hz0 & Hz2). apply Hag2; unfold ESTACK; lia. }
assert (HCT2 : pj_nodeR SEGS (mrestrict (w_H Wc) mem2) (prh_lin Lamc) (F + CRT_OFF_COPY) tcB Dc).
{ apply (c4_tree_stk lyc Sc Hpc Wc memc mem2 mdc kj pos _ Lamc peakc cntW 0 0 Dc (F + CRT_OFF_COPY) tcB CRT_CID pos
    HL Hag2 Hinf).
  - unfold CRT_OFF_COPY. lia.
  - rewrite cb4_fb. unfold CRT_OFF_COPY. lia.
  - intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. right. exact Hbk.
  - exact HCT. }
assert (HFO2 : exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) mem2) (prh_lin Lamc) DOC_D (F + CRT_OFF_COPY) Dc Fc /\
  map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (@crt_tree_J t)).
{ destruct HFO as (Fc & HFc & EFc). exists Fc. split; [|exact EFc].
  apply (c4_tree_stk_fo lyc Sc Hpc Wc memc mem2 mdc kj pos _ Lamc peakc cntW 0 0 Dc (F + CRT_OFF_COPY) DOC_D Fc
    CRT_CID pos HL Hag2 Hinf).
  - unfold CRT_OFF_COPY. lia.
  - rewrite cb4_fb. unfold CRT_OFF_COPY. lia.
  - intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. right. exact Hbk.
  - exact HFc. }
destruct (c4_O2_state fxk lyc Sc Hpc Wc mem2 _ kj pos Dc Lamc peakc msv cset ok q pre fx3 ly3 S3 Hp3 W3 regs3 mem3
  md3 k1 _ (ms_regs ms1) HCP HDP HFO2 Et HFK HOK Hfail0 Hq0 HnIn HL2q HSPB2
  (HSPx2 _ _ HSPS ltac:(unfold CRT_SP_SHN_B; lia) ltac:(unfold CRT_SP_SHN_B; lia))
  (HSPx2 _ _ HSPP ltac:(unfold CRT_SP_PN_B; lia) ltac:(unfold CRT_SP_PN_B; lia))
  (HSPx2 _ _ HSPN ltac:(unfold CRT_SP_N_B; lia) ltac:(unfold CRT_SP_N_B; lia))
  Hd8 HRAd2 HRAb2 HRAv2 Hcs Hcs0 HCT2 Hpre Hpos2b Esm HCFb HFZ3 HFK3 HJ3pre HB3 HJ1 HQ3 HMN3 HJ3 HDR4 R24d R26d
  R21d)
  as (Lam3 & peak3 & cnt3 & HO2s).
pmkst HS3. rewrite HF3.
lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
  change n with (CRT_PC_B + CRT_O2_OFF_B) end.
exact (HO2 fx3 ly3 S3 Hp3 W3 mem3 _ (kj + k1) pos Dc Lam3 peak3 cnt3 (ms_regs ms1) msv cset q HO2s).
Qed.

(* THE parse_noting STEP: t4_goal_pn from tparse_noting_specX (PRH_FnCheck.v:597-731 at this base). The proof applies
   the text at the site's binders and derives the whole post: the granted outcome and the exact advance come from the
   text's OUTCOME CLAUSE (:673-682) at the site's position, whose run hypothesis prh_cons_from (:677) and strtod tie
   the goal takes from crt_pos, and RQ_pj_parse tb <= most (:632) is the goal's premise, paid at the site from HRQA
   (Crt102Model.cm_rqa_read). The two pkR room counts (:642-645) come from the room position and the run window by
   PresetRoomCounts.peak_sec_of_room_pos / peak_c24_of_room_pos (taken by path, 5b877a834be4). AT THE LANDING
   CUT (7cdbb61b5fa0) THE DW PREMISE IS GONE (UNIV-END retired; the closure's clause
   4b holds the cursor free traces at every word). AT THE kb ROUND the two items the cut left open are the goal's
   own kb form: the text's wild room premise (:638) is t4_goal_pn's premise in the text's place (the call site pays
   it out of the text's entry room HWR0, crt4_lane_S_at), and the text's budgeted post fpostFbm .. (wbudget []
   (prh_wk F_parse_noting)) (:649) is t4_goal_pn's post at the same budget: the text's journal and its budget are
   carried unchanged, and only the inner post is read at the site's position (c4_pn_post). Qed. *)
Lemma t4_goal_pn_holds : t4_goal_pn.
Proof.
intros fxk lyc Sc Hpc Wc regsT memc mdc ch1 text tb dc Lamc peakc cntc ii hist. cbv zeta.
intros HPRE1 HMN1 HCL1 H10 H11 H12 Hl40
  Ht0 Ht62 Hsrc Hhome Hmax Hdc8 Hout HLED1 Hcnt1 Hlive1 Hrq1 Hfr1 Hfrm0 Hroom1 GWR GHULL Hpos1 Hrun1 Esm HCF Hnp
  Hrqm.
pose proof (PresetRoomCounts.peak_sec_of_room_pos rp_sm rp_x rp_os ii rp_H0 hist Sc _ Hpos1 Hrun1) as GSEC.
pose proof (PresetRoomCounts.peak_c24_of_room_pos rp_sm rp_x rp_os ii rp_H0 hist Sc _ Hpos1 Hrun1) as G24.
rewrite Esm in GSEC, G24.
eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
{ exact (PN fxk most 0 lyc Sc Hpc Wc regsT memc mdc ch1 text tb dc Lamc peakc cntc SIZE_MAXZ 0
    HPRE1 HMN1 HCL1 H10 H11 H12 Hl40 Ht0 Ht62 Hsrc Hhome Hmax Hdc8 Hout eq_refl HLED1 Hcnt1 Hlive1 Hrq1 Hrqm
    Hfr1 Hfrm0 Hroom1 GWR GSEC G24 GHULL). }
(* the text's budgeted post at the goal's budget: the same float state, journal, budget WS (and its wbudget) and kept
   registers, the inner post read at the site's position *)
cbv beta. intros W' c' _ Hpost.
unfold fpostFbm, fpostFb, fQmn, YCbqGwild.apost_base_xbFR in Hpost |- *.
destruct Hpost as (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HFZ' & HFK' & HPW & HJ' & HPr & HQ &
  Hmn).
exists fx', ly', S', Hp', regs', mem', md', k, WS.
split; [exact Hc|]. split; [exact HFZ'|]. split; [exact HFK'|]. split; [exact HPW|]. split; [exact HJ'|].
split; [exact HPr|]. split; [|exact Hmn].
destruct HQ as (_ & Hroom' & Lam' & peak' & cnt' & fail' & ran' & okr & res & tr & Hjr & _ & _ &
  HOC & Hoks & Ecnt & Hfa & Epk & Hhp & Hcfn & Hrr & Hok & Hby & HLED' & Hres).
rewrite Esm in Hpos1, Hrun1, HCF.
destruct (HOC ReaderRes.jr_strtod rp_x rp_os ii rp_H0 hist Hpos1 Hrun1 HCF (or_intror Hnp))
  as (Er0 & _ & _ & hist' & Hadv).
unfold c4_pn_post. rewrite Esm.
split; [exact Hroom'|]. split; [exists hist'; exact Hadv|].
exists Lam', peak', cnt', fail', ran', okr, res, tr.
split; [exact Hjr|]. split; [exact Er0|]. split; [exact Hoks|]. split; [exact Ecnt|]. split; [exact Hfa|].
split; [exact Epk|]. split; [exact Hhp|]. split; [exact Hcfn|]. split; [exact Hrr|]. split; [exact Hok|].
split; [exact Hby|]. split; [exact HLED'|].
destruct res as [tv|]; [|exact Hres].
(* the Some arm: back's tree, its blocks and its free order (the text's rd_blocks and CAP (pj_ncapR) conjuncts are
   not read here) *)
destruct Hres as (R10 & Dr & HPLr & HLszr & HNLr & _ & HFOr & HFrr & HPBr & HNDr & _).
split; [exact R10|]. exists Dr. split; [exact HPLr|]. split; [exact HLszr|]. split; [exact HNLr|].
split; [exact HFOr|]. split; [exact HFrr|]. split; [exact HPBr | exact HNDr].
Qed.

(* ======================================================================================================== *)
(* THE SEGMENT LEMMA OF ROW T4: from crt_at_W_B (+0x2a4) the run reaches QF, given that it does from every
   crt_at_L0_B state (row T5). Both calls of the segment are taken through their proved goals: the parse_noting call
   at +0x2e8 through t4_goal_pn (t4_goal_pn_holds, from the text PN; its wild room paid from the text's entry room
   HWR0 in crt4_lane_S_at), the pj_write call at +0x2b8 through T4_GOAL_PJW (t4_goal_pjw, from the callee text
   tpj_write_specX).
   The r = 1 exit FF -> X (+0x300 .. +0x30c) is UNREACHABLE (crt_at_J_B / crt_at_X_B now carry r = 0, glue
   80a20e4edde): every way into FF is a refusal (g_ran_out = 1), and each is refuted at its source - a refused
   pj_write by T4_GOAL_PJW (its ranw = 0), a granted pj_write leaving ran = 1 by its own prh_oks (cb4w_granted_ran),
   a refused reading by tparse_noting_specX's outcome clause (t4_goal_pn's ran' = 0). So the walk from W exits at L0
   only, and no J premise is needed. copy's blocks against tblk (under crt_at_W_B's cf_head guard, discharged by
   reflexivity at L0 since CfParams_preset's cf_head is HEAD) and copy's depth are threaded W -> Wr -> S -> L0. The
   closed pieces: crt4_lane_W (W -> Wr), crt4_lane_Wr (Wr -> S | O2), crt4_lane_S_at (S -> O2, given t4_goal_pn),
   crt4_lane_O2 (O2 -> L0), t4_goal_pjw, t4_goal_pn_holds; crtB_T4_X (X -> J) stays, Qed, for the X boundary. *)
Lemma crtB_T4 : CRTB_L0 -> CRTB_W.
Proof.
intros HL0.
pose proof (crt4_lane_O2 HL0) as HO2.
pose proof (crt4_lane_S_at t4_goal_pn_holds HO2) as HS.
exact (crt4_lane_W t4_goal_pjw (crt4_lane_Wr HS HO2)).
Qed.

End g.
End f.
End t4.

(* the evidence the row reports: what the closed lemmas rest on (the Section hypotheses are their arguments) *)
Print Assumptions crtB_T4.
Print Assumptions crtB_T4_X.
Print Assumptions crt4_lane_W.
Print Assumptions crt4_lane_Wr.
Print Assumptions crt4_lane_S_at.
Print Assumptions crt4_lane_O2.
Print Assumptions cb4_back_tblk.
Print Assumptions cb4_back_fo.
Print Assumptions t4_goal_pjw.
Print Assumptions t4_goal_pn_holds.
