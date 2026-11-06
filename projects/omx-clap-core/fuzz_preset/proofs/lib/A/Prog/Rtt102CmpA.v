(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module names changed; 78 of its 113 lines of code are new or changed and 893 lines of the source are left out. *)
(* fuzz_preset, image A' (asan, sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): STRETCH CMP of
   round_trip_text's walk ON THE #102 PINS (lane RttCmp of WalkRtt102, the text owner), RTT_SEG_CMP of Rtt102Cut.v:
   rtt_seg RT_O2 rtt_at_o2 -> rtt_seg RT_CMP rtt_at_cmp.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma); the function-level lookup
   (proof-index EXIT=0, no released ASan proof) is the brief's.
   THE CODE (A' +0x2e4 .. +0x328, A' capstone listing :187-203), in three segments:
     S12  +740 beqz s6 (REFUTED: q <> 0) .. +752 jal __wrap_strcmp .. +756 bnez a0 (REFUTED: the strings are equal,
          both hold ri_tb D) .. +760 addi s7, s10, 0x20 .. +768 jal __wrap_strlen            -> +772 cmp_at_len
     PN   +772 .. +784 jal parse_noting (text, len, &back)                                   -> +788 cmp_at_pn
     FF   +788 mv s8, a0 .. +796 jal __wrap_free (want) .. +804 jal fuzz_free (text)         -> +808 RT_O2
   WHAT IS PROVED, rtt_seg_cmp_A : RTT_SEG_CMP, ON THE BATCH KIT'S CUT 7cdbb61b5fa0 (WalkRtt102b's shared layer 80a1d52c32c7),
   under the Section hypotheses below only (engine / instance laws, the callee texts, the head), with NO premise of
   its own. The pre-cut theorem rtt_seg_cmp_A_univend was CMP from a cut strengthened by two tagged premises; both
   retire at the batch kit's cut:
     K0-UNIV-END   GONE. The cut's tparse_noting_specX (PRH_FnCheck.v:596-730) takes no membership of the cursor end
                   (PRH_FnCheck.v:615-616: prh_univ_closure's clause 4b holds the cursor traces at every word); DW is
                   gone from every text. rtt_at_cmp_ue, RTT_UNIVEND_CLAUSE and rtt_seg_cmp_A_of_univend are deleted.
     K0-SRC-CEIL   DISCHARGED. The cut's src_rd (PRH_Base.v:1660) asks q + len <= alloc_ceiling, no `+ 8`;
                   Rtt102CmpPNA.v cmp_pn's assert HSRC_CEIL derives it from the text block being live: alx_blocks
                   (YCbqG.v:113-116, ARx_blocks_law: p + req_size n <= alloc_ceiling) at (q - cf_head, capw + cf_head),
                   req_size n >= n, and len < capw (Rtt102Cut.v:575, rtt_at_cmp).
   Everything else is the texts': parse_noting's outcome clause gives the granted reading at the cut's position and
   prh_cons_from share (its ran-out outcome is refuted at the call), the read-back blocks over rd_blocks, the free
   order over pj_frees at every depth bound (at DOC_D PresetFreeFo.pj_frees_wdoc_t turns it into fo t) and K0-CAP's
   pj_ncapR; the wild budget's 2 for parse_noting is the text's 32 less the rendering's 30 (rtt_wild_room).
   HISTORY: at f9eda666dd9 (record 9cf516b1971, WITHDRAWN as a stretch result) the theorem rested on K0-TBLK, an
   ordered block equality since MEASURED FALSE, so that theorem was vacuous; the later K0-FREEORD (universal over
   every pj_nodeR tree at the reader's size multiset) was of the same refutable class. Neither is carried here.
   Numerals: the program points above (DERIVED). No ADDRESS literal: every pc is pa_sigma / pa_val of the listing. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YG00cf YGcallMx YGcallMxmn YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep PresetRun PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnTx PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA S1Ledger Rtt102Cut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102FR1Kit Rtt102FR1KitA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102CmpLib Rtt102CmpDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102CmpS12A Rtt102CmpPNA Rtt102CmpFFA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Context {RF : PrhRoomFree (cp := CfParamsPreset.CfParams_preset) (RL := RL)}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
(* the listing offset of round_trip_text's entry (DERIVED: 4 * its slot; convertible to the lanes' own RTT_K) *)
#[local] Notation RTT_K := (4 * Z.of_nat (A_prog_slot AS_round_trip_text)).
(* the world relation of every journal of the walk (Rtt102Cut.v RZW) *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variables (CTX0 : list (list Z)).

(* ---- the Section hypotheses of the three segments, in one place (each lane's file states the same ones) ---- *)
(* (a) the allocator laws at the cf instance's head (engine fold, YCbqG.v AR_laws_x) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* (a) MARKED STAND-IN (owned by the kit / the core's PALib): the unit's image binding of B *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.
(* (a) the free wrapper's call form, model and re-hiding call post with its three laws (Rtt102CmpFFA.v's block,
   verbatim; YGcallx.v Sections r / rR; at the cf instance: QM_cf / QMm_cf / malloc_cf / cf_malloc_max / Wf_cf,
   APOST := YGcallMxmnKeep.APOST_cf_keep with POST_AR_cf_keep / POST_J_cf_keep / proj2, AFREE by
   afree_realizes_x_cf_rh_keep, QMR by QMm_cf_of_room, ACF by acall_pre_x_xs_cf). OWNLOW is no longer read. *)
Variable QM : astate -> Prop.
Variable QMm : astate -> (word -> option byte) -> Prop.
Variable mt : Z -> list Z -> YG00.M sptr.
Variable nmax : Z.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis AMX : alloc_model_laws_x B QM mt nmax YG00cf.free_cf WFx.
Hypothesis QMQ : forall S mem, QMm S mem -> QM S.
Variable APOST : Z -> alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.
Hypothesis POST_AR : apost_ar_law SEGS ARx APOST.
Hypothesis POST_J : apost_j_law (rc := rc) (SK := SK) SEGS B ARx RZW APOST.
Hypothesis POST_MN : forall stk ly S Hp W regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md',
  APOST stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
  YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem'.
Hypothesis AFREE : forall fx' : YK11.FPState,
  afree_realizes_xR (fx := fx') SEGS B ARx QMm YG00cf.free_cf RZW APOST.
Hypothesis QMR : forall ly S Hp W mem md, ARx ly S Hp W mem md -> qtight S -> room_live_cf S ->
  PresetHullBudget.hull_budget S [] ->
  arodata_okP SEGS (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) B (aview SEGS (w_H W) mem) ->
  QMm S mem.
Hypothesis ACF : forall ly S Hp W regs mem md ch, acall_pre_x SEGS B ARx QMm ly S Hp W regs mem md ch ->
  YG0dcf.acall_pre_cf SEGS B ly S Hp W regs mem md ch.
(* (c) MARKED STAND-IN (owned by the kit, the image binding of B): alloc.c's statics are not the runtime's own statics *)
Hypothesis pal_pst_static : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* (a) PRH_Base.v prh_head_wide (the preset instance has cf_head = 16) *)
Hypothesis HW : prh_head_wide.
(* (a) the strcmp / strlen wrappers' texts in the read-only-premise form with the memnorm keep (YGcallMxmn.v
   section 8, owner a Theorem Labs lane), at every float state: the calls are made at the cut's *)
Hypothesis STRCMP : forall fx' : YK11.FPState,
  @YGcallMxmn.astrcmp_realizes_xrom fx' SEGS B ARx (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA)
    (SIGMA AS___wrap_strcmp).
Hypothesis STRLEN : forall fx' : YK11.FPState,
  @YGcallMxmn.astrlen_realizes_xrom fx' SEGS B ARx (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA)
    (SIGMA AS___wrap_strlen).
(* (b) the callee's kit text, fuzz_free (PRH_FnAlloc.v at the batch kit's cut: admits premise, post budgeted at its own trace),
   at any float state: the call happens at the cut's fxc *)
Hypothesis TFF : forall fx' : YK11.FPState,
  @tfuzz_free_specX fx' rc CfParamsPreset.CfParams_preset prh_img_A RL A_prog_listing PA B ARx SK.
(* (b) the callee's kit text, parse_noting (PRH_FnCheck.v at the batch kit's cut 7cdbb61b5fa0, blob c40cf3fdcd2a: the
   post-implication form with its own exact advance, the wild room at entry and the budgeted post), at any float state:
   the call happens at the cut's fxc, which rtt_fx only relates to fx *)
Hypothesis TPN : forall fx0 : YK11.FPState,
  tparse_noting_specX (fx := fx0) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0.
(* (a) the preset instance's head (CfParams_preset's cf_head = 16 = alloc.c's HEAD; WalkRtt102's ruling: a Section
   hypothesis HHEAD, owner the preset instantiation) *)
Hypothesis HHEAD : cf_head = PresetReqAt.HEAD.
(* (a) the meter caps of the instance's CfParams cover the run's section bounds (Rtt102CmpPNA.v's HI_hull, verbatim;
   at CfParams_preset: CrsSeg_W1.crs_W1_HI_hull, by computation) *)
Hypothesis HI_hull : PresetSecTotal.SEC_N_CAP <= @YGcfNames.cf_kmax CfParamsPreset.CfParams_preset /\
  PresetSecTotal.SEC_T_CAP <= @YGcfNames.cf_T_max CfParamsPreset.CfParams_preset.

(* ---- THE STRETCH: RTT_SEG_CMP of Rtt102Cut.v, with no premise beyond the Section hypotheses above ---- *)
Theorem rtt_seg_cmp_A :
  @RTT_SEG_CMP fx rc ci CfParamsPreset.CfParams_preset prh_img_A RL A_prog_listing PA B ARx SK CTX0.
Proof.
intros SO2 D HP fxc ly S Hp W regs mem md k pos HC.
assert (ESIG : SIGMA AS_round_trip_text = BASE + RTT_K) by (vm_compute; reflexivity).
rewrite ESIG. replace (BASE + RTT_K + RT_CMP) with (BASE + (RTT_K + RT_CMP)) by lia.
(* PROOF-CONTEXT FPState CHECK (the text owner's rule): fxc (and later fx') are LOCAL FPStates here, so each segment's
   class-implicit fx is passed BY NAME; no assert / have below mentions an FPState-implicit term *)
apply (cmp_s12 (fx := fx) B ARx SK CTX0 LAWS HW STRCMP STRLEN D HP fxc ly S Hp W regs mem md k pos HC).
intros regs2 mem2 md2 _ HLEN.
apply (cmp_pn (fx := fx) B ARx SK CTX0 LAWS HW TPN HHEAD HI_hull D HP fxc ly S Hp W regs2 mem2 md2 k pos HLEN).
intros fx' ly2 S2 Hp2 W2 regs3 mem3 md3 k2 HPN.
exact (cmp_ff (fx := fx) B ARx SK CTX0 LAWS PAL QM QMm mt nmax WFx WFL AMX QMQ APOST POST_AR POST_J POST_MN AFREE QMR
  ACF pal_pst_static HW TFF SO2 HHEAD D HP fx' ly2 S2 Hp2 W2 regs3 mem3 md3 k2 pos HPN).
Qed.

End c.

(* THE STATEMENT CHECK (the text owner's amended rule): the theorem's type IS its statement, so `Check` reads it; with
   implicits on and notations off, every class-implicit FPState must be the contract's fx, and fx0 / fxc only where
   the statement binds them *)
Set Printing Implicit.
Unset Printing Notations.
Check @rtt_seg_cmp_A.
Set Printing Notations.
Unset Printing Implicit.

Print Assumptions rtt_seg_cmp_A.
