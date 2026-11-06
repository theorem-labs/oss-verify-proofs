(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1535 of its 1608 lines of code are new or changed and 441 lines of the source are left out. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcfTreeVis YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAtNoMiss PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Glue Crt102Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PLB102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102B_T3Base.
(* kb round: crt_live carries its budget kb (64 at U and S) and its journal at a budget WS; the runs go through
   Crt102Kit's AJW runners (crt_run_xw_inv / crt_run_to_xw), used qualified, and pj_string (no wild site) through
   YCbqGwild.aj_call_xWb_sp at its empty budget, so the caller's journal stays at the budget it had at U *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Kit.
(* The re-hiding move: the journal at YA0nH.wle' SEGS YGcfRehidePost.RZ_cf, the
   steps at YA0nH.SRr' (YSRrG's bind / mono / branch), pj_string's plain text lifted (the re-hiding contract's R5; its
   fpostWm post by the engine's YCbqGcallW.fpostW_x_R_lift) into YCbqGwild.aj_call_xWb_spR *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YSRrG.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section t3s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head} {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).
#[local] Notation PL := PL_B102.
(* THE IMAGE: Crt102Img.v's Section b hypotheses, verbatim (B' values in Crt102Img.v:1002-1013). Owner: the image-B
   instance; each is a vm_compute at PI_prog_B once lib/B/PAImg_prog.v builds (its :160 waits for the instance
   owner's IMG_TOP_B = 0x601000). *)
Hypothesis HB_base : BASE = B_prog_base.
Hypothesis HB_entry : SIGMA AS_check_round_trip = B_prog_base + CRT_PC_B.
Hypothesis HB_segs : SEGS = B.Img0.rsegs.
Hypothesis HB_relro : forall a, Exists (in_zr a) PST -> ~ (RLO <= a < RHI).
Hypothesis HB_hi : @pa_hi _ B_prog_listing PA <= 2 ^ 31.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)).
(* the journal at a wild-trace budget WS at the contract's R (YCbqG.v ajournal_xwR at YA0nH.wle' SEGS
   YGcfRehidePost.RZ_cf; AJ is it at WS = []); crt_live's journal is at the boundary's budget kb (kb round) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)).
(* the allocator's engine laws at hl = cf_head (at the instance: AR_laws_x_cf of the instance owner's ARcf) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the two image facts walk S4's lanes carry (S4_PsSrc.v:116-119): the image's zero-shadow ranges are granule-aligned
   (asyms_ok's aso_zshadow, YG0f.v:191), and IMAGE B's shadow bytes are present: Crt102B_T3Base.crt3_img_shadow_vis_B,
   the instance owner's YGcfAmx2.img_shadow_vis_cf (YGcfAmx2.v:47-49) at image B's CfImgB.CfImg_B, over
   [IMG_LO_B, IMG_TOP_B), with ARcf -> ARx (crt3_img_shadow_vis_B_a8: at ARx := ARcf (ci := CfImg_B) it is the
   instance owner's definition). Never image A's IMG_LO / IMG_TOP. Owner: the instance owner (the instance's
   supply of img_shadow_vis_cf at CfImg_B). *)
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Hypothesis IMGV : crt3_img_shadow_vis_B SEGS ARx.
Variable CTX0 : list (list Z).
(* THE CALLEE TEXTS, at every float state. Their walks are other lanes'; Crt102Top discharges these.
   tpj_string_specX / tpj_set_specX: the base's lib/A/PRH_FnPj.v 908f34f0beaa (the contract kit's: the ledger is
   PRH_Base.v section c's prh_ledger .. ran most own; the entry-keyed pj family is PRH_FnPj.v section c), with
   PRH_PjOrder.v and PRH_FnReader.v of the base. tfuzz_alloc_ran_out_specX: the base's PRH_FnAlloc.v 740f4d11d144. *)
(* pj family: entry-keyed event form *)
(* LEDGER, the ledger half: pj_string's outcome is prh_alloc_post at `most own` (arm 2, the refusal: PEAK' = Z.max
   peak (Z.min SIZE_MAXZ (lsum Lam + n)), RAN' = if n <=? most then 1 else ran); this row reads RAN' = 1 only under
   n = 21 <= most (Crt102Model.cm_rqa_stamp from RQA_crt t <= most). The run event: prhPj_string_evs 20 cnt
   SIZE_MAXZ, supplied by prhPj_string_evs_supply from the position U carries. *)
Hypothesis HPJS : forall fxq : YK11.FPState,
  @PRH_FnPj.tpj_string_specX fxq rc ci CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0.
(* pj family: entry-keyed event form *)
(* LEDGER, the ledger half: pj_set's refusals are read through prh_oks' third conjunct (a refusal sets g_ran_out), the
   clause over the per-call request list that the ledger half restates; this row reads it only for requests <= most
   (cm_rqa_key 11, cm_rqa_grow 56 * cap2R, cm_rqa_grow_keys 8 * cap2R at cap = ck_members t). The run events:
   prhPj_set_evs ms MOD_KEY n cap, supplied by prhPj_set_evs_supply (n = |ms|, cap = ncap |ms|: Crt102Model's
   cm_cap_of_tblk from crt_at_U_B's last conjunct, the tblk equality, which S carries as crt3_tblk Db). *)
Hypothesis HPJSET : forall fxq : YK11.FPState,
  @PRH_FnPj.tpj_set_specX fxq rc ci CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0 DOC_D.
Hypothesis HRO : forall fxq : YK11.FPState,
  @PRH_FnAlloc.tfuzz_alloc_ran_out_specX fxq rc CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK.

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z).
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (CRT_sp1 (regs := regs)).
(* crt_side / crt_live take no rp_* since 11c39f7e88b7 (the position is crt_pos, on the r = 0 path only) *)
#[local] Notation liveB := (crt_live (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (most := most)).
#[local] Notation sideB := (crt_side (rc := rc) (PI := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PA) (B := B)
  (doc := doc) (t := t) (D := D) (peak := peak) (most := most)).
#[local] Notation posB := (crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (t := t)).
#[local] Notation evsU := (crt_evs_U (rp_sm := rp_sm)).
#[local] Notation evsW := (crt_evs_W (rp_sm := rp_sm)).
#[local] Notation tblkB := (crt3_tblk (t := t)).
#[local] Notation spillB := (crt_spill (L := B_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation savedB := (crt_saved (L := B_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation dregsB := (crt_dregs_B (regs := regs) (doc := doc)).
#[local] Notation bregsB := (crt_bregs_B (regs := regs)).
#[local] Notation QFb := (QF (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation cfgB := (crt_cfg (rc := rc) (L := B_prog_listing) (PA := PA) (CRT_PC := CRT_PC_B)).
#[local] Notation atU := (crt_at_U_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK)
  (L := B_prog_listing) (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os)
  (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md)
  (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation atX := (crt_at_X_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK)
  (L := B_prog_listing) (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os)
  (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md)
  (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation atW := (crt_at_W_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK)
  (L := B_prog_listing) (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os)
  (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md)
  (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation atS := (crt_at_S3 (fx := fx) (rc := rc) (RL := RL) (SK := SK) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp)
  (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak)
  (cnt := cnt) (most := most)).
#[local] Notation atO1 := (crt_at_O1_3 (fx := fx) (rc := rc) (RL := RL) (SK := SK) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp)
  (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak)
  (cnt := cnt) (most := most)).
#[local] Notation STMT_X := (CRT3_X (fx := fx) (rc := rc) (RL := RL) (SK := SK) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp)
  (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak)
  (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation STMT_W := (CRT3_W (fx := fx) (rc := rc) (RL := RL) (SK := SK) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp)
  (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak)
  (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation STMT_O1 := (CRT3_O1 (fx := fx) (rc := rc) (RL := RL) (SK := SK) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp)
  (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak)
  (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation STMT_S := (CRT3_S (fx := fx) (rc := rc) (RL := RL) (SK := SK) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp)
  (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak)
  (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation STMT_U := (CRT3_U (fx := fx) (rc := rc) (RL := RL) (SK := SK) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp)
  (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak)
  (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation tcB := (crt_tc (t := t)).
#[local] Notation cwB := (crt_cw (t := t) (cnt := cnt)).
#[local] Notation F_ lyc pos := (frame_addr lyc CRT_CID pos).
(* THE TEXT'S PREMISES this row reads (tcheck_round_trip_specX, PRH_FnCheck.v 9ecd8eb167c6, at the
   instance's two string addresses for a_mod_at / a_stamp); Crt102Top discharges them from the text's own premises.
   The text's room position premise reaches this row through crt_at_U_B's crt_pos. *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HUNIV : prh_univ_closure B CTX0.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
Hypothesis HREAD : ck_read x = Some t.
Hypothesis HLENX : Z.of_nat (length x) <= 3 * 2 ^ 20.
Hypothesis HWL0 : PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x).
Hypothesis HWL1 : PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54.
Hypothesis HKMOD : kept_img B (CRT_MOD_AT_B (PA := PA)) (Z.of_nat (length ck_MOD_AT) + 1).
Hypothesis HKST : kept_img B (CRT_STAMP_B (PA := PA)) (Z.of_nat (length ck_STAMP) + 1).
Hypothesis HCNT : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis HRAN : ran = 0.
Hypothesis HRQA : RQA_crt t <= most.
Hypothesis HLIVE : blocks_bytes S + LIVE_check_round_trip t <= LIVE_MAX.
Hypothesis HRQ : RQ_crt t + cf_head < cf_malloc_max.
(* THE RUN HAS AT MOST 4 CALLS (DRAFT, the text's own premise PRH_FnCheck.v:2363): tpj_string_specX asks it of the
   caller's rp_os (fuzz_strdup's hull budget paid from the position, lib/A/PresetHullPay.v hull_budget_of_room_pos) *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.

(* ======================================================================================================== *)
(* ---- THE SYMBOLIC STATE AT U (+0x1ec), the probe's (measured): the stack spill window of the
   realigned sp (base s1 = atom 9, sp1 + 0x48 .. + 0x60), the frame's own shadow (base s2 = atom 18, the 23 bytes the
   fourteen stores touch) and the document's n field read-only (base s6 = atom 22, its value the extra atom 32). The
   atom facts: sp and s1 in the stack band (32-aligned), the frame shadow in the shadow band, the document below
   0x7fffff800000 (DERIVED: CEIL_MAX of YM05.v, the only bound on alloc_ceiling a vm_compute may read), 8-aligned,
   and the shadow base s11 = SHADOW_OFF. 2 ^ 46 - 256 / 2 ^ 47 / 2 ^ 44 are DERIVED (stack band, shadow span). ---- *)
Definition t3U_Bx : sv := SOff 27 0.
Definition t3U_rstack : YP09.region := YP09.mkRegion (Some 9%nat) 72 96 72 96 [].
Definition t3U_rshadow : YP09.region := YP09.mkRegion (Some 18%nat) 0 23 0 23 [].
Definition t3U_rdoc : YP09.region := YP09.mkRegion (Some 22%nat) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 32 0))].
Definition t3U_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46 - 256) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46 - 256) (2 ^ 47) 5);
           (18%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (22%nat, mkAF 4096 0x7fffff800000 3);
           (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition t3U_ssA : sstate :=
  mkSS (CRT_PC_B + CRT_U_OFF_B) sr_atoms [t3U_rstack; t3U_rshadow; t3U_rdoc] None t3U_facts.
Definition t3U_E (rg : bvmap 5 word) (n : Z) : env := @Eimg _ B_prog_listing PA (Ereg rg [w64 n]).

Lemma crt3U_fb : fs_frame_bytes CRT_CID = 512.
Proof. vm_compute. reflexivity. Qed.

(* the entry's registers as the environment reads them *)
Lemma crt3U_E_vals : forall rg F n, dregsB rg F ->
  0 <= F -> F + 512 <= YM05.alloc_ceiling -> 0 <= doc < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  bv_unsigned (ew (t3U_E rg n) 2) = sp1 /\ bv_unsigned (ew (t3U_E rg n) 9) = sp1 /\
  bv_unsigned (ew (t3U_E rg n) 18) = shadow_addr F /\ bv_unsigned (ew (t3U_E rg n) 19) = F /\
  bv_unsigned (ew (t3U_E rg n) 22) = doc /\ bv_unsigned (ew (t3U_E rg n) 27) = SHADOW_OFF /\
  ew (t3U_E rg n) 32 = w64 n /\
  (forall q, (q < A_TEXT)%nat -> ew (t3U_E rg n) q = ew (Ereg rg [w64 n]) q).
Proof.
intros rg F n H HF0 HFc Hd Hn.
pose proof (crt_dregs_B_bregs H) as HBR. pose proof (crt_dregs_B_s6 H) as R22.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3.
pose proof (crt_bregs_B_tp HBR) as R4. pose proof (crt_bregs_B_s0 HBR) as R8.
pose proof (crt_bregs_B_s1 HBR) as R9. pose proof (crt_bregs_B_s2 HBR) as R18.
pose proof (crt_bregs_B_s4 HBR) as R20. pose proof (crt_bregs_B_s3 HBR) as R19.
pose proof (crt_bregs_B_s7 HBR) as R23. pose proof (crt_bregs_B_s9 HBR) as R25.
pose proof (crt_bregs_B_s11 HBR) as R27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (crt3_sp1 HPRE) as (Hs32 & Hs1 & Hs0). destruct (crt3_sp0 HPRE) as (Hal16 & Hsc & H47 & _).
assert (EL : forall q, (q < A_TEXT)%nat -> ew (t3U_E rg n) q = ew (Ereg rg [w64 n]) q)
  by (intros q Hq; unfold t3U_E; apply Eimg_low; exact Hq).
assert (Hsh : 0 <= shadow_addr F < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  assert (F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat rg _ 2 2%bv eq_refl), R2; unfold w64;
  apply unsigned_lit_small; lia|].
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat rg _ 9 9%bv eq_refl), R9; unfold w64;
  apply unsigned_lit_small; lia|].
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat rg _ 18 18%bv eq_refl), R18; unfold w64;
  apply unsigned_lit_small; lia|].
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat rg _ 19 19%bv eq_refl), R19; unfold w64;
  apply unsigned_lit_small; lia|].
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat rg _ 22 22%bv eq_refl), R22; unfold w64;
  apply unsigned_lit_small; lia|].
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat rg _ 27 27%bv eq_refl), R27; unfold w64;
  apply unsigned_lit_small; unfold SHADOW_OFF; lia|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra rg [w64 n] 0)|].
exact EL.
Qed.

(* ---- the entry state at U: the symbolic state above holds (H5CrtS3.v crt3_entry's argument at the B' registers) ---- *)
Lemma crt3U_entry : forall (fxk : YK11.FPState) lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc rg ms
    {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  dregsB rg (F_ lyc pos) -> t = PjTree.JObj ms ->
  st_ok_pi (fx := fxk) SEGS VAL (t3U_E rg (Z.of_nat (length ms))) t3U_ssA
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_U_OFF_B))) memc (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS t3U_Bx [] (t3U_E rg (Z.of_nat (length ms))) (mrestrict (w_H Wc) memc).
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc rg ms kbg HL HDR Ht.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_doc HSD) as HND.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct (crt3_ff LAWS lyc Sc Hpc Wc memc mdc kj pos HJ) as (Hin & Hnin & HF0 & HFc & HFapp & HF32 & HFpr & HFsh).
destruct (crt3_home_keep LAWS HPRE HTREE _ _ _ _ _ _ _ _ HJ) as (Hd8 & (cidd & posd & Hind & Hdlo & Hdhi) & Hdra).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc cidd posd HARc Hind) as (HD0 & HDc & HDapp).
destruct (crt3_sp1 HPRE) as (Hs32 & Hs1 & Hs0). destruct (crt3_sp0 HPRE) as (Hal16 & Hsc & H47 & _).
pose proof crt3_stk as Hstk.
set (F := F_ lyc pos) in *.
rewrite Ht in HND. cbn [pj_nodeR] in HND.
destruct HND as (_ & _ & num & str & kids & keys & nn & cap & HHDR & Hrest).
destruct Hrest as (_ & Hnn & _).
destruct HHDR as (_ & _ & _ & _ & _ & _ & Hn40 & _). destruct Hn40 as (Hnr & Hnv).
subst nn.
set (n := Z.of_nat (length ms)) in *.
assert (Hdoc0 : 4096 <= doc) by lia.
assert (Hdocc : doc + 56 <= YM05.alloc_ceiling) by lia.
destruct (crt3U_E_vals rg F n HDR ltac:(lia) ltac:(lia) ltac:(lia) Hnr) as (U2 & U9 & U18 & U19 & U22 & U27 & E32 & EL).
assert (Hsa : SHADOW_OFF <= shadow_addr F /\ shadow_addr F + 64 <= SHADOW_OFF + 2 ^ 44).
{ unfold shadow_addr. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  assert (F / 8 <= 2 ^ 44 - 64) by (apply Z.div_le_upper_bound; lia).
  lia. }
rewrite restrict_mkst_fx.
split; [|unfold sh_ok; apply Forall_nil].
unfold t3U_ssA. apply pa_entry_st_ok_full.
- unfold t3U_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + unfold t3U_rstack, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + unfold t3U_rshadow, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U18. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
    split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFsh o ltac:(lia))).
  + unfold t3U_rdoc, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ doc 40 8 (SOff 32 0) n).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * change (N.to_nat 8) with 8%nat. exact Hnv.
- assert (Hds : doc + 48 <= shadow_addr F \/ shadow_addr F + 23 <= doc + 40).
  { destruct HDapp as (_ & [Hlow | [Hhi _]]);
    [left; unfold kLowShadowBeg, SHADOW_OFF in *; lia | right; unfold kHighMemBeg, SHADOW_OFF in *; lia]. }
  cbn [pairwise_disjoint all_disjoint].
  unfold extent_disjoint, t3U_rstack, t3U_rshadow, t3U_rdoc.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U18, U22.
  repeat split.
  + right. unfold SHADOW_OFF in *. lia.
  + right. lia.
  + destruct Hds as [Hx | Hx]; [right; lia | left; lia].
- unfold facts_ok, t3U_facts.
  cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  repeat match goal with |- _ /\ _ => split | |- True => exact I end.
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2.
    change (2 ^ 5) with 32. split; [lia|]. split; [exact Hs32 | lia].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9.
    change (2 ^ 5) with 32. split; [lia|]. split; [exact Hs32 | lia].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18.
    change (2 ^ 0) with 1. split; [lia|]. split; [apply Z.mod_1_r | lia].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22.
    change (2 ^ 3) with 8. split; [lia|]. split; [exact Hd8 | lia].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U27.
    change (2 ^ 0) with 1. split; [lia|]. split; [apply Z.mod_1_r | lia].
Qed.

(* ---- reading a symbolic state's chunks back as bytes ---- *)
Lemma crt3U_chunk1 : forall E m base off,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 1 (SLit 0))) -> mbyte SEGS m (base + off) = Some (Z_to_bv 8 0).
Proof.
intros E m base off H. destruct (H 0 ltac:(unfold YP09.c_len; cbn; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm. rewrite Z.add_0_r in Hm.
assert (Eb : YP09.byte_of_word (sv_denot E (SLit 0)) 0 = Z_to_bv 8 0) by (vm_compute; reflexivity).
rewrite Eb in Hb. injection Hb as <-. exact Hm.
Qed.
Lemma crt3U_chunk8 : forall E m base off e,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 e)) -> val_mem SEGS m (base + off) 8 (U E e).
Proof.
intros E m base off e H k Hk.
destruct (H (Z.of_nat k) ltac:(unfold YP09.c_len; cbn; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm. injection Hb as <-.
rewrite Hm. f_equal. unfold YP09.byte_of_word, le_byte, U.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
unfold YO0f.le_byte.
rewrite (Z.mod_small (bv_unsigned (sv_denot E e))) by (cbn; lia).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* a symbolic state keeps its soundness when regions are dropped (H5CrtS3.v crt3_st_ok_pi_submem) *)
Lemma crt3U_st_ok_pi_submem : forall (fxq : YK11.FPState) E ss ms rs,
  st_ok_pi (fx := fxq) SEGS VAL E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi (fx := fxq) SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros fxq E ss ms rs HS Hsub Hwf. unfold st_ok_pi, abs_ss in *. destruct ss.
exact (st_ok_submem SEGS E _ ms rs HS Hsub Hwf).
Qed.

(* ---- THE WRITES OF THIS STAGE'S OWN RUNS (B'): the frame shadow window of run A (bytes 0 .. 22, of which the
   stores write 4 .. 10 and 16 .. 22) and the spill window sp1 + 0x48 .. + 0x60 of runs A and B ---- *)
Definition crt3U_wr (F a : Z) : Prop :=
  (shadow_addr F <= a < shadow_addr F + 23) \/ (sp1 + 72 <= a < sp1 + 96).

Lemma crt3U_nw_low : forall F a, 0 <= F -> 0 <= a < kLowMemEnd -> ~ crt3U_wr F a.
Proof.
intros F a HF Ha [Hw | Hw]; destruct (crt3_sp1 HPRE) as (_ & Hs1 & _); destruct (crt3_sp0 HPRE) as (_ & Hsc & _);
  pose proof asan_consts as (C1 & _); pose proof crt3_stk;
  unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *; [pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia))|]; lia.
Qed.
Lemma crt3U_nw_app : forall F a, 0 <= F -> F + 512 <= YM05.alloc_ceiling -> in_app a 1 -> a < YM05.alloc_ceiling ->
  ~ crt3U_wr F a.
Proof.
intros F a HF HF2 Ha Hac [Hw | Hw]; destruct (crt3_sp1 HPRE) as (_ & Hs1 & _); destruct (crt3_sp0 HPRE) as (_ & Hsc & _);
  pose proof asan_consts as (C1 & _); pose proof crt3_stk.
- assert (F / 8 <= 2 ^ 44 - 64) by (apply Z.div_le_upper_bound; lia).
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *; lia.
- lia.
Qed.
Lemma crt3U_nw_stack : forall F a, 0 <= F -> F + 512 <= YM05.alloc_ceiling -> YM05.alloc_ceiling <= a ->
  ~ (sp1 + 72 <= a < sp1 + 96) -> ~ crt3U_wr F a.
Proof.
intros F a HF HF2 Ha Hn [Hw | Hw]; [|exact (Hn Hw)]. pose proof asan_consts as (C1 & _).
assert (F / 8 <= 2 ^ 44 - 64) by (apply Z.div_le_upper_bound; lia).
unfold shadow_addr, SHADOW_OFF in *; lia.
Qed.
Lemma crt3U_shadow_add : forall F k, F mod 8 = 0 -> shadow_addr (F + 8 * k) = shadow_addr F + k.
Proof.
intros F k H. unfold shadow_addr. apply Z.mod_divide in H; [|lia]. destruct H as [q ->].
replace (q * 8 + 8 * k) with ((q + k) * 8) by lia. rewrite !Z.div_mul by lia. lia.
Qed.

(* ---- the statics are in PST ---- *)
Lemma crt3U_pst_static : forall c (gz : nat) k, In (c, Z.of_nat gz) PST -> (k < gz)%nat -> Exists (in_zr (c + Z.of_nat k)) PST.
Proof.
intros c gz k Hin Hk. apply Exists_exists. exists (c, Z.of_nat gz). split; [exact Hin|]. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma crt3U_val_pst : forall (W1 W2 : world SEGS) m1 m2 c (gz : nat) v,
  (forall a, Exists (in_zr a) PST -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
  In (c, Z.of_nat gz) PST -> val_mem SEGS (mrestrict (w_H W1) m1) c gz v -> val_mem SEGS (mrestrict (w_H W2) m2) c gz v.
Proof.
intros W1 W2 m1 m2 c gz v Hs Hin Hv k Hk.
rewrite (mbyte_of_aview SEGS (w_H W1) (w_H W2) m1 m2 _ (Hs _ (crt3U_pst_static c gz k Hin Hk))). exact (Hv k Hk).
Qed.

(* ---- the ledger at a memory that agrees on the statics and on the heads (S1Ledger.v prh_ledger_kept_aview, same
   layout and blocks) ---- *)
#[local] Ltac t3U_in := unfold prh_pst; cbn [In]; repeat (first [left; reflexivity | right]).
Lemma crt3U_ledger_keep : forall ly1 S1 Hp1 (W1 W2 : world SEGS) m1 m2 Lam1 peak1 cnt1 fail1 ran1 most1 own1,
  prh_ledger B ly1 S1 Hp1 W1 m1 Lam1 peak1 cnt1 fail1 ran1 most1 own1 ->
  (forall a, Exists (in_zr a) PST -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
  (forall a k i, In (a, k) Lam1 -> 0 <= i < 8 ->
     aview SEGS (w_H W2) m2 (a - cf_head + i) = aview SEGS (w_H W1) m1 (a - cf_head + i)) ->
  prh_ledger B ly1 S1 Hp1 W2 m2 Lam1 peak1 cnt1 fail1 ran1 most1 own1.
Proof.
intros ly1 S1 Hp1 W1 W2 m1 m2 Lam1 peak1 cnt1 fail1 ran1 most1 own1
  ((G1 & G2 & G3 & G4 & G5 & (Gm & Gm0) & (Go & Go0) & Gb) & ND & HB & HP) Hs Hh.
split; [|split; [exact ND|split; [|exact HP]]].
- split; [apply (crt3U_val_pst W1 W2 m1 m2 _ _ _ Hs); [t3U_in | exact G1]|].
  split; [apply (crt3U_val_pst W1 W2 m1 m2 _ _ _ Hs); [t3U_in | exact G2]|].
  split; [apply (crt3U_val_pst W1 W2 m1 m2 _ _ _ Hs); [t3U_in | exact G3]|].
  split; [apply (crt3U_val_pst W1 W2 m1 m2 _ _ _ Hs); [t3U_in | exact G4]|].
  split; [apply (crt3U_val_pst W1 W2 m1 m2 _ _ _ Hs); [t3U_in | exact G5]|].
  split; [split; [apply (crt3U_val_pst W1 W2 m1 m2 _ _ _ Hs); [t3U_in | exact Gm] | exact Gm0]|].
  split; [split; [apply (crt3U_val_pst W1 W2 m1 m2 _ _ _ Hs); [t3U_in | exact Go] | exact Go0]|].
  exact Gb.
- rewrite Forall_forall in HB |- *. intros [a k] Hin. destruct (HB (a, k) Hin) as (H1 & H2 & H3 & H4 & H5).
  cbn [fst snd] in *. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  intros j Hj. rewrite (mbyte_of_aview SEGS (w_H W1) (w_H W2) m1 m2 _ (Hh a k (Z.of_nat j) Hin ltac:(lia))).
  exact (H5 j Hj).
Qed.

(* ---- the tree over a block predicate that holds wherever the old one did (transcribed from lib/A/Prog/Crt102Tail.v's
   ct_cstr_lblk / ct_mems_lblk / ct_nodeR_lblk, prefixed crt3U_) ---- *)
Lemma crt3U_cstr_lblk : forall m (lblk lblk' : Z -> Z -> Prop) a k s, pj_cstrR SEGS m lblk a k s ->
  (lblk a k -> lblk' a k) -> pj_cstrR SEGS m lblk' a k s.
Proof. intros m lblk lblk' a k s (Hl & Hr) H. exact (conj (H Hl) Hr). Qed.
Lemma crt3U_mems_lblk : forall m (lblk lblk' : Z -> Z -> Prop) (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR SEGS m lblk P a ka l D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  (forall i nm u D1, nth_error l i = Some (nm, u) -> incl D1 D -> P (a + 56 * Z.of_nat i) u D1 ->
     P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR SEGS m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka Dm H HL HP; cbn [pj_memsR] in H |- *; [exact H|].
destruct H as (xk & k & D1 & D2 & -> & Hx & Hc & H1 & H2). exists xk, k, D1, D2. split; [reflexivity|].
split; [exact Hx|].
split; [apply (crt3U_cstr_lblk m lblk lblk' xk k nm Hc); apply HL; left; reflexivity|].
split.
- pose proof (HP 0%nat nm u D1 eq_refl (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_introl Hy)))) as HP0.
  replace (a + 56 * Z.of_nat 0) with a in HP0 by lia. exact (HP0 H1).
- apply (IH (a + 56) (ka + 8) D2 H2).
  + intros y kk Hy. apply HL. right. apply in_or_app. right. exact Hy.
  + intros i nm' u' D1' Hi Hinc HPi.
    specialize (HP (Datatypes.S i) nm' u' D1' Hi (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_intror (Hinc y Hy))))).
    replace (a + 56 * Z.of_nat (Datatypes.S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia. exact (HP HPi).
Qed.
Lemma crt3U_nodeR_lblk : forall tv m (lblk lblk' : Z -> Z -> Prop) p Dt, pj_nodeR SEGS m lblk p tv Dt ->
  (forall x k, In (x, k) Dt -> lblk x k -> lblk' x k) -> pj_nodeR SEGS m lblk' p tv Dt.
Proof.
intros tv. induction tv as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk lblk' p Dt H HL; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & nn & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, nn, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (crt3U_cstr_lblk m lblk lblk' str k txt Hc). apply HL. subst Dt. left. reflexivity.
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (crt3U_cstr_lblk m lblk lblk' str k s Hc). apply HL. subst Dt. left. reflexivity.
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  assert (HDi : forall b, In b Di -> In b Dt) by (intros b Hb; subst Dt; apply in_or_app; right; exact Hb).
  split.
  { destruct Hcap as [Hz | (Hcp & Hk)]; [left; exact Hz | right; split; [exact Hcp|]].
    apply HL; [|exact Hk]. subst Dt. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR SEGS m lblk) (pj_nodeR SEGS m lblk') items kids Di Hi).
  intros i u D1 Hil Hinc HP. rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 HP).
  intros y k Hy. apply HL. apply HDi. apply Hinc. exact Hy.
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  assert (HDi : forall b, In b Di -> In b Dt) by (intros b Hb; subst Dt; apply in_or_app; right; exact Hb).
  split.
  { destruct Hcap as [Hz | (Hcp & Hk & Hy)]; [left; exact Hz | right; split; [exact Hcp|]].
    subst Dt. rewrite (proj2 (Z.eqb_neq cap 0)) in HL by lia.
    split; [apply HL; [left; reflexivity | exact Hk] | apply HL; [right; left; reflexivity | exact Hy]]. }
  exists Di. split; [exact ED|].
  apply (crt3U_mems_lblk m lblk lblk' (pj_nodeR SEGS m lblk) (pj_nodeR SEGS m lblk') members kids keys Di Hi).
  + intros y k Hy. apply HL. apply HDi. exact Hy.
  + intros i nm u D1 Hil Hinc HP. rewrite Forall_forall in IH.
    specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
    apply (IH m lblk lblk' _ D1 HP). intros y k Hy. apply HL. apply HDi. apply Hinc. exact Hy.
Qed.

(* ---- a tree at a later memory whose footprint bytes are the same and present ---- *)
Lemma crt3U_tree_keep : forall (W1 W2 : world SEGS) m1 m2 (lblk lblk' : Z -> Z -> Prop) p tv Dt,
  pj_nodeR SEGS (mrestrict (w_H W1) m1) lblk p tv Dt ->
  (forall x, pj_footR p Dt x -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x /\ apresent (w_H W2) m2 x) ->
  (forall x k, In (x, k) Dt -> lblk x k -> lblk' x k) ->
  pj_nodeR SEGS (mrestrict (w_H W2) m2) lblk' p tv Dt.
Proof.
intros W1 W2 m1 m2 lblk lblk' p tv Dt H HK HL.
apply (crt3U_nodeR_lblk tv _ lblk lblk' p Dt); [|exact HL].
apply (pj_nodeR_frame SEGS tv (mrestrict (w_H W1) m1) (mrestrict (w_H W2) m2) lblk p Dt H).
intros y Hy. destruct (HK y Hy) as (Ha & Hpr). split.
- exact (mbyte_of_aview SEGS (w_H W1) (w_H W2) m1 m2 y Ha).
- intros _. exact (apresent_writable SEGS (w_H W2) m2 y Hpr).
Qed.

(* ---- the ledger's blocks, the allocator's blocks, frames (transcribed from Crt102B_T3S.v crt3s_hblk /
   crt3s_blk_bounds / crt3s_blk_frm, prefixed crt3U_) ---- *)
Lemma crt3U_hblk : forall lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc b k,
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> In (b, k) Lamc ->
  0 <= k /\ In (b - 16, k + 16) (ablocks B lyc Sc) /\ In (b - 16) Hpc /\ b mod 16 = 0 /\ req_size (k + 16) = k + 16.
Proof.
intros lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc b k HLG Hin.
pose proof (proj1 (Forall_forall _ _)
  (prh_ledger_blocks B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc HLG) (b, k) Hin)
  as (Hk0 & Hab & Hhp & H16 & _).
change (@cf_head CfParams_preset) with 16 in Hab, Hhp. cbn [fst snd] in Hk0, Hab, Hhp, H16.
split; [exact Hk0|]. split; [exact Hab|]. split; [exact Hhp|]. split; [exact H16|].
unfold req_size. destruct (Z.eqb_spec (k + 16) 0); lia.
Qed.
Lemma crt3U_blk_bounds : forall lyc Sc Hpc Wc memc mdc p nb,
  ARx lyc Sc Hpc Wc memc mdc -> In (p, nb) (ablocks B lyc Sc) ->
  4096 <= p /\ p + req_size nb <= YM05.alloc_ceiling /\ in_app p (req_size nb) /\
  (forall a, p <= a < p + req_size nb -> apresent (w_H Wc) memc a).
Proof.
intros lyc Sc Hpc Wc memc mdc p nb HAR Hb.
destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc p nb HAR Hb) as (H16 & H4096 & Hc & Happ & Hpr & _).
split; [exact H4096|]. split; [exact Hc|]. split; [exact Happ|]. intros a Ha. exact (proj1 (Hpr a Ha)).
Qed.
Lemma crt3U_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
Lemma crt3U_aview_present : forall (H : word -> bool) m a, apresent H m a -> aview SEGS H m a <> None.
Proof.
intros H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

(* ---- an image string under route (a) (kept_img) at any ARx state with the read-only view: its shadow and its
   C-string facts (transcribed from Crt102B_T3S.v crt3s_garr8_of_view / crt3s_hull_img / crt3s_zs_byte /
   crt3s_kimg_shadow / crt3s_tail_b / crt3s_tail_ok / crt3s_cstr_mod, at the stamp) ---- *)
Lemma crt3U_garr8_of_view : forall (H : word -> bool) (m : word -> option byte) p (l : list Z),
  (forall j, (j < length l)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0)) ->
  Forall (fun c => 0 <= c < 256) l -> garr8 SEGS (mrestrict H m) p l.
Proof.
intros H m p l HV HB j Hj. pose proof (proj1 (Forall_forall _ _) HB (nth j l 0) (nth_In l 0 Hj)) as Hr.
split; [|exact Hr]. intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (HV j Hj). unfold aview in HV.
destruct (mbyte SEGS (mrestrict H m) (p + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HV; [|discriminate HV].
injection HV as HV. f_equal. rewrite <- HV. apply bv_eq. rewrite Z_to_bv_unsigned.
pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
cbv [YO0f.le_byte]. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite !Z.mod_small; lia.
Qed.
(* the hull is IMAGE B's, [IMG_LO_B, IMG_TOP_B), in the allocator lane's FuzzStrdupB form
   (commit e8c226ad89c3, lib/B/Prog/FuzzStrdupB.v:131-135 sd_hull_img): never image A's
   IMG_LO / IMG_TOP *)
Lemma crt3U_hull_img : forall p nn s, 0 < nn -> IMG_LO_B + 64 <= p -> p + nn + 64 <= IMG_TOP_B ->
  shadow_addr p / 8 * 8 <= s < shadow_addr (p + nn - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ IMG_LO_B <= 8 * (s - SHADOW_OFF) < IMG_TOP_B.
Proof.
intros p nn s Hn Hlo Hhi Hs. pose proof IMG_LO_B_val as EL. pose proof IMG_TOP_B_val as ET. rewrite EL, ET in *.
unfold shadow_addr in *. unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.
Lemma crt3U_zs_byte : forall (rd : reader) q m z, q mod 8 = 0 -> m mod 8 = 0 -> zero_shadow rd SHADOW_OFF q m ->
  q <= z < q + m -> rd (shadow_addr z) = Some 0.
Proof.
intros rd q m z Hq Hm Hz Hx. unfold shadow_addr.
replace (SHADOW_OFF + z / 8) with (shadow_of_addr SHADOW_OFF q + (z / 8 - q / 8)) by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.
(* the bounds are image B's and come from the B' fact (Crt102B_T3Base.crt3_str_hull_B at the caller), not from
   kept_img's hull; kept_img gives the per-byte facts only *)
Lemma crt3U_kimg_shadow : forall lyc Sc Hpc Wc memc mdc p nn,
  ARx lyc Sc Hpc Wc memc mdc -> kept_img B p nn -> 0 < nn ->
  IMG_LO_B + 64 <= p -> p + nn + 64 <= IMG_TOP_B ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF p nn /\ shadow_hull_vis (aview SEGS (w_H Wc) memc) p nn.
Proof.
intros lyc Sc Hpc Wc memc mdc p nn HAR (_ & _ & Hk) Hn Hlo Hhi. split.
- intros z Hz. destruct (Hk z Hz) as (_ & _ & _ & [Hzs | (v & Hc & Hv)]).
  + destruct Hzs as (q & m & Hin & Hq & Hqm). destruct (ZSA q m Hin) as [Zq Zm].
    pose proof (alx_zshadow SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc (q, m) HAR
      ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz0.
    cbn [fst snd] in Hz0. exists 0. split; [|left; reflexivity].
    unfold shadow_of_addr. change (SHADOW_OFF + z / 8) with (shadow_addr z).
    apply (crt3U_zs_byte _ q m z Zq Zm Hz0). lia.
  + pose proof (alx_const_cells SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc HAR) as HC.
    pose proof (proj1 (Forall_forall _ _) HC _ (Hc lyc)) as Hch.
    cbn [cell_holds z1 c1 c_at c_w c_val aeval] in Hch. specialize (Hch 0%nat ltac:(lia)).
    rewrite Z.add_0_r in Hch. exists v. split.
    * unfold shadow_of_addr. change (SHADOW_OFF + z / 8) with (shadow_addr z). rewrite Hch. f_equal.
      unfold le_byte. cbn [Z.of_nat]. rewrite Z.shiftr_0_r. change (2 ^ (8 * 1)) with 256.
      rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
    * destruct Hv as [Hv|Hv]; [left; exact Hv | right; exact Hv].
- intros s0 Hs. destruct (crt3U_hull_img p nn s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
  apply (IMGV lyc Sc Hpc Wc memc mdc _ HAR). rewrite crt3_cfimgB_lo, crt3_cfimgB_top. exact Hr.
Qed.
Definition crt3U_tail_b (segs : list Segment) (p nn : Z) : bool :=
  forallb (fun i => match YK11.seg_rom segs (Z_to_bv 64 (p + nn + 1 + Z.of_nat i)) with Some _ => true | None => false end)
    (seq 0 (Z.to_nat (7 - (p + nn) mod 8))).
Lemma crt3U_tail_ok : forall (H : word -> bool) (m : word -> option byte) p nn,
  crt3U_tail_b SEGS p nn = true -> forall z, p + nn < z < p + nn - (p + nn) mod 8 + 8 -> aview SEGS H m z <> None.
Proof.
intros H m p nn Hb z Hz. unfold crt3U_tail_b in Hb. rewrite forallb_forall in Hb.
pose proof (Z.mod_pos_bound (p + nn) 8 ltac:(lia)) as Hr.
specialize (Hb (Z.to_nat (z - (p + nn + 1)))). rewrite in_seq in Hb.
specialize (Hb ltac:(lia)). rewrite Z2Nat.id in Hb by lia. replace (p + nn + 1 + (z - (p + nn + 1))) with z in Hb by lia.
unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 z)); [cbn; discriminate|].
destruct (YK11.seg_rom SEGS (Z_to_bv 64 z)); [cbn; discriminate | discriminate Hb].
Qed.
Lemma crt3U_stamp_tail : crt3U_tail_b SEGS (CRT_STAMP_B (PA := PA)) (Z.of_nat (length ck_STAMP)) = true.
Proof.
destruct (crt_str_res_B (PA := PA)) as (H1 & _). rewrite HB_segs, HB_base in H1.
assert (C : match res_pair (segf B.Img0.rsegs) (B_prog_base + (CRT_PC_B + CRT_STAMP1_HI_B))
                  (B_prog_base + (CRT_PC_B + CRT_STAMP1_LO_B)) with
            | Some p => crt3U_tail_b B.Img0.rsegs p (Z.of_nat (length ck_STAMP)) | None => false end = true)
  by (vm_compute; reflexivity).
rewrite H1 in C. rewrite HB_segs. exact C.
Qed.
Lemma crt3U_cstr_stamp : forall lyc Sc Hpc Wc memc mdc,
  ARx lyc Sc Hpc Wc memc mdc -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memc) ->
  cstr_ok Wc memc (CRT_STAMP_B (PA := PA)) ck_STAMP.
Proof.
intros lyc Sc Hpc Wc memc mdc HAR HROD.
(* the string's bounds: image B's, from the B' fact (crt3_str_hull_B), not kept_img's hull *)
pose proof HKST as (_ & _ & Hk). destruct (crt3_str_hull_B HB_base HB_segs) as (_ & _ & Hlo & Hhi).
pose proof IMG_LO_B_val as EL. pose proof IMG_TOP_B_val as ET.
pose proof YM05.alloc_ceiling_val as Hac.
assert (Hn : Z.of_nat (length ck_STAMP) = 20) by reflexivity.
destruct (crt3U_kimg_shadow lyc Sc Hpc Wc memc mdc _ _ HAR HKST ltac:(lia) Hlo Hhi) as [HRA HHU].
split; [split|].
{ apply crt3U_garr8_of_view.
  - intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    destruct (Hk (CRT_STAMP_B (PA := PA) + Z.of_nat j) ltac:(lia)) as (Hro & Hno & Her & _).
    rewrite (HROD _ Hro Hno Her).
    exact (proj2 (crt_str_rom_B HB_base HB_segs) j ltac:(unfold CRT_STAMP_S; rewrite length_app; cbn [length]; lia)).
  - unfold ck_STAMP. cbn [app]. repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
{ unfold ck_STAMP. repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold YGcfStr.amem_range8, kLowMemEnd; lia|].
split; [exact HRA|]. split; [exact HHU|].
apply crt3U_tail_ok. exact crt3U_stamp_tail.
Qed.

(* ---- the frame's shadow covers the hull of a 56-byte local (Crt102B_T3S.v crt3s_hull_frame) ---- *)
Lemma crt3U_hull_frame : forall (rd : reader) Fa off nn,
  Fa mod 32 = 0 -> 32 <= off -> 0 < nn -> off + nn <= 448 -> 0 <= Fa ->
  (forall i, 0 <= i < 64 -> rd (shadow_addr Fa + i) <> None) -> shadow_hull_vis rd (Fa + off) nn.
Proof.
intros rd Fa off nn H32 Hoff Hn Hon HF0 Hpr s Hs.
replace s with (shadow_addr Fa + (s - shadow_addr Fa)) by lia. apply Hpr.
unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.

(* the shadow hull of copy (F + 224, 56 bytes) lies in the frame's shadow bytes 24 .. 39 *)
Lemma crt3U_copy_hull : forall Fa s, Fa mod 32 = 0 -> 0 <= Fa ->
  shadow_addr (Fa + CRT_OFF_COPY) / 8 * 8 <= s < shadow_addr (Fa + CRT_OFF_COPY + 56 - 1) / 8 * 8 + 8 ->
  shadow_addr Fa + 24 <= s < shadow_addr Fa + 40.
Proof.
intros Fa s H32 HF0 Hs. unfold CRT_OFF_COPY, shadow_addr, SHADOW_OFF in *. lia.
Qed.

(* ---- the live state across one of this stage's own runs (writes in crt3U_wr; lib/A/Prog/Crt102Kit.v's
   crt102rw_live_run at the B' write set) ---- *)
Lemma crt3U_live_run : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc {kbg : nat}
    {WS : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc' mdc' kj' WS -> YCbqGwild.wbudget [] kbg WS ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ crt3U_wr (F_ lyc pos) a ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc') ->
  liveB kbg lyc Sc Hpc Wc memc' mdc' kj' pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc kbg WS HL HJ' HB' K HMN'.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMN.
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & _ & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ') as (_ & _ & _ & _ & _ & _ & Ffr' & Fsh').
pose proof HJ' as (HARc' & _ & _ & _ & _ & HFRS' & _).
pose proof crt3U_fb as HFB.
set (F := F_ lyc pos) in *.
destruct (crt3_sp1 HPRE) as (Hs32 & Hs1 & Hs0). destruct (crt3_sp0 HPRE) as (Hal16 & Hsc & H47 & _).
pose proof crt3_stk as Hstk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (crt3_home_keep LAWS HPRE HTREE _ _ _ _ _ _ _ _ HJ') as (Hd8 & (cidd & posd & Hind & Hdlo & Hdhi) & _).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc' mdc' cidd posd HARc' Hind) as (HD0 & HDc & HDapp).
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc' mdc' cidd posd HARc' Hind) as (_ & _ & HDpr & _).
assert (Hhd : @cf_head CfParams_preset = 16) by reflexivity.
assert (Kst : forall a, Exists (in_zr a) PST -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. pose proof (@pa_segs_low _ _ PA a (crt_pst_img_B HB_segs a Ha)) as Hl.
  apply K; [unfold kLowMemEnd in Hl; lia|]. apply crt3U_nw_low; [lia | exact Hl]. }
assert (Kblk : forall b k, In (b, k) Lamc -> forall i, 0 <= i < k + 16 ->
  aview SEGS (w_H Wc) memc' (b - 16 + i) = aview SEGS (w_H Wc) memc (b - 16 + i) /\
  apresent (w_H Wc) memc' (b - 16 + i)).
{ intros b k Hk i Hi. pose proof (crt_side_ledger HSD) as HLED.
  destruct (crt3U_hblk _ _ _ _ _ _ _ _ _ _ _ _ b k HLED Hk) as (Hk0 & Hab & _ & _ & Hrq).
  destruct (crt3U_blk_bounds lyc Sc Hpc Wc memc' mdc' _ _ HARc' Hab) as (B4096 & Bce & Bapp & Bpr).
  rewrite Hrq in *. split; [|apply Bpr; lia].
  apply K; [lia|]. apply (crt3U_nw_app F _ ltac:(lia) ltac:(lia)); [|lia]. apply (in_app_sub _ _ _ _ Bapp); lia. }
assert (Hsh : SHADOW_OFF <= shadow_addr F /\ shadow_addr F + 64 <= SHADOW_OFF + 2 ^ 44).
{ unfold shadow_addr. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  assert (F / 8 <= 2 ^ 44 - 64) by (apply Z.div_le_upper_bound; lia). lia. }
assert (Kfs : forall i, 24 <= i < 40 -> aview SEGS (w_H Wc) memc' (shadow_addr F + i) = aview SEGS (w_H Wc) memc (shadow_addr F + i)).
{ intros i Hi. apply K; [unfold SHADOW_OFF in *; lia|]. intros [Hw | Hw]; [lia|]. unfold SHADOW_OFF in *; lia. }
refine {| crt_live_journal := ex_intro _ WS (conj HJ' HB'); crt_live_side := _; crt_live_lam_perm := HPL;
          crt_live_blocks_perm := HPB; crt_live_dx_apart := HAP; crt_live_saved := _;
          crt_live_frame := _; crt_live_fspill := _; crt_live_copy_open := _;
          crt_live_copy_hull := _; crt_live_memnorm := HMN' |}.
- (* crt_side *)
  pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK.
  pose proof (crt_side_room HSD) as HRL. pose proof (crt_side_arodata HSD) as HRD.
  pose proof (crt_side_doc HSD) as HDOC. pose proof (crt_side_doc_blocks HSD) as HDL.
  refine {| crt_side_ledger := _; crt_side_peak := HPK; crt_side_room := HRL;
            crt_side_arodata := _; crt_side_doc := _; crt_side_doc_blocks := HDL |}.
  + apply (crt3U_ledger_keep _ _ _ Wc Wc memc memc' _ _ _ _ _ _ _ HLED Kst).
    intros a k i Hk Hi. rewrite Hhd. destruct (crt3U_hblk _ _ _ _ _ _ _ _ _ _ _ _ a k HLED Hk) as (Hk0 & _).
    exact (proj1 (Kblk a k Hk i ltac:(lia))).
  + intros a Hro Ho He. pose proof (@pa_segs_low _ _ PA a (crt3U_ro_img a Hro)) as Hl.
    rewrite K; [exact (HRD a Hro Ho He) | unfold kLowMemEnd in Hl; lia | apply crt3U_nw_low; [lia | exact Hl]].
  + apply (crt3U_tree_keep Wc Wc memc memc' (prh_lin Lamc) (prh_lin Lamc) doc t D HDOC); [|intros; assumption].
    intros y Hy. destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
    * split.
      -- apply K; [lia|]. apply (crt3U_nw_app F y ltac:(lia) ltac:(lia)); [|lia]. apply (in_app_sub _ _ _ _ HDapp); lia.
      -- apply HDpr. lia.
    * unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
      destruct (Kblk b kb (HDL _ Hb) (y - (b - 16))
        ltac:(destruct (crt3U_hblk _ _ _ _ _ _ _ _ _ _ _ _ b kb HLED (HDL _ Hb)); lia)) as (H1 & H2).
      replace (b - 16 + (y - (b - 16))) with y in H1, H2 by lia. split; assumption.
- (* crt_live_saved *)
  intros j Hj k Hk. rewrite (mbyte_of_aview SEGS (w_H Wc) (w_H Wc) memc memc'); [exact (HSV j Hj k Hk)|].
  apply K; [lia|]. apply (crt3U_nw_stack F _ ltac:(lia) ltac:(lia)); lia.
- (* crt_frame *)
  pose proof (crt_frame_listed HFRM) as Hinf. pose proof (crt_frame_flag_word HFRM) as Hfl.
  pose proof (crt_frame_present HFRM) as Hpr.
  refine {| crt_frame_listed := Hinf; crt_frame_flag_word := _; crt_frame_present := _ |}.
  + rewrite <- Hfl. apply crt3_rdword_keep. intros j Hj. rewrite HFB.
    apply K; [lia|]. apply (crt3U_nw_app F _ ltac:(lia) ltac:(lia)); [|lia]. apply (in_app_sub _ _ _ _ Fb3); lia.
  + intros a Ha. rewrite HFB in Ha. exact (proj1 (Ffr' a Ha)).
- (* crt_live_fspill *)
  intros k Hk. unfold CRT_SP_F in *. rewrite (mbyte_of_aview SEGS (w_H Wc) (w_H Wc) memc memc'); [exact (HSPF k Hk)|].
  apply K; [lia|]. apply (crt3U_nw_stack F _ ltac:(lia) ltac:(lia)); lia.
- (* crt_live_copy_open *)
  apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HCR].
  intros y Hy. unfold CRT_OFF_COPY in Hy. unfold shadow_of_addr.
  change (SHADOW_OFF + y / 8) with (shadow_addr y).
  replace (shadow_addr y) with (shadow_addr F + (shadow_addr y - shadow_addr F)) by lia. apply Kfs.
  unfold shadow_addr. assert (F / 8 + 28 <= y / 8 < F / 8 + 35) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  lia.
- (* crt_live_copy_hull *)
  intros s Hs. pose proof (crt3U_copy_hull F s F32 ltac:(lia) Hs) as Hr.
  replace s with (shadow_addr F + (s - shadow_addr F)) by lia. rewrite Kfs by lia.
  replace (shadow_addr F + (s - shadow_addr F)) with s by lia. exact (HCH s Hs).
Qed.

(* ---- the live state across a callee whose footprint is inside v (pj_string (&v, ..)): every byte the boundary
   reads is kept by the callee's journal (the saved slots and the spill above its sp, the own frame's bytes and
   shadow outside v, the document's header in a frame of the entry, the document's blocks); the side facts at the
   new state are the callee's post's ---- *)
Lemma crt3U_live_call : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc
  ly2 S2 Hp2 W2 mem2 md2 kj2 STKw spw FP1 k1 Dx' Lam' peak' cnt' own' ran' {kbg kbg' : nat} {WS1 : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (exists WS2, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 kj2 WS2 /\
     YCbqGwild.wbudget [] kbg' WS2) ->
  AJW STKw spw FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  spw = sp1 -> 0 <= STKw ->
  (forall a, inFP FP1 a -> F_ lyc pos + CRT_OFF_V <= a < F_ lyc pos + CRT_OFF_V + 56) ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam' peak' cnt' SIZE_MAXZ ran' most own' -> peak <= peak' -> room_live_cf S2 ->
  (forall bk, In bk Lamc -> In bk Lam') ->
  Permutation Lam' (Dx' ++ Lam) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks Dx') ->
  (forall bk, In bk Dx' -> ~ In bk D) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  liveB kbg' ly2 S2 Hp2 W2 mem2 md2 kj2 pos Dx' Lam' peak' cnt' own' ran'.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ly2 S2 Hp2 W2 mem2 md2 kj2 STKw spw FP1 k1
  Dx' Lam' peak' cnt' own' ran' kbg kbg' WS1 HL (WS2 & HJ2 & HB2) HJ1 Espw HSTKw HFP1 HLED2 HPK2 HRL2 HLL HPL2 HPB2
  HAP2 HMN2.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMN.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK.
pose proof (crt_side_room HSD) as HRL. pose proof (crt_side_arodata HSD) as HRD.
pose proof (crt_side_doc HSD) as HDOC. pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & Hly & _ & _ & _ & HFRS & _).
pose proof HJ1 as (HAR2 & Hly1 & _ & _ & _ & _ & _ & _ & K1 & K2 & K3 & K4 & _).
pose proof HJ2 as (_ & Hly2 & _ & _ & _ & HFRS2 & _).
pose proof (proj1 (proj1 HPRE)) as HAR0.
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Hnin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ2) as (Hin2 & _ & _ & _ & _ & _ & Ffr2 & Fsh2).
destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc ly2 HARc Hly1) as (_ & Efa & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR0 Hly) as (_ & Ef0 & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md ly2 HAR0 Hly2) as (_ & Ef02 & _).
pose proof crt3U_fb as HFB.
assert (EF2 : frame_addr ly2 CRT_CID pos = F_ lyc pos) by apply Efa.
assert (EFl : flag_addr ly2 CRT_CID pos = flag_addr lyc CRT_CID pos).
{ pose proof (Efa CRT_CID pos) as Ex. unfold frame_addr in Ex. unfold flag_addr. lia. }
rewrite EF2 in Ffr2, Fsh2.
set (F := F_ lyc pos) in *.
destruct (crt3_sp1 HPRE) as (Hs32 & Hs1 & Hs0). destruct (crt3_sp0 HPRE) as (Hal16 & Hsc & H47 & _).
pose proof crt3_stk as Hstk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
subst spw.
(* the callee's footprint lies in the own frame, whose bytes and shadow are apart from every other byte read *)
assert (Hnfp : forall a, inFP FP1 a -> F <= a < F + 512) by (intros a Ha; pose proof (HFP1 a Ha); unfold CRT_OFF_V in *; lia).
assert (Hshb : forall i, 0 <= i < 64 -> ~ inFP FP1 (shadow_addr F + i)).
{ intros i Hi Hf. pose proof (Hnfp _ Hf) as Hr.
  assert (F / 8 <= 2 ^ 44 - 64) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *; lia. }
(* the document's home frame, a frame of the entry *)
pose proof HTREE as (_ & _ & _ & (Hd8 & (cid0 & pos0 & Hin0 & Hlo0 & Hhi0) & _)).
assert (Hin0c : In (cid0, pos0) (frames Sc)) by (rewrite HFRS; apply in_or_app; right; exact Hin0).
assert (Hin02 : In (cid0, pos0) (frames S2)) by (rewrite HFRS2; apply in_or_app; right; exact Hin0).
assert (Hsep0 : frame_addr lyc cid0 pos0 + fs_frame_bytes cid0 <= F \/ F + 512 <= frame_addr lyc cid0 pos0).
{ apply in_split in Hin0 as (m1 & m2 & Em).
  pose proof (sep_frames_pos_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc (CRT_CID, pos) (cid0, pos0) [] m1 m2 HARc
    ltac:(rewrite HFRS, Em; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite HFB in Hd. subst F. lia. }
destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid0 pos0 HAR2 Hin02) as (_ & _ & HDpr2 & _).
rewrite (Ef02 cid0 pos0), <- (Ef0 cid0 pos0) in HDpr2. rewrite <- (Ef0 cid0 pos0) in Hlo0, Hhi0.
pose proof (fs_frame_bytes_nonneg cid0) as Hfb0.
(* a block of the document stays a block across the call *)
assert (HDblk : forall b k, In (b, k) D -> forall i, 0 <= i < k + 16 ->
  aview SEGS (w_H W2) mem2 (b - 16 + i) = aview SEGS (w_H Wc) memc (b - 16 + i) /\
  apresent (w_H W2) mem2 (b - 16 + i)).
{ intros b k Hb i Hi.
  destruct (crt3U_hblk _ _ _ _ _ _ _ _ _ _ _ _ b k HLED (HDL _ Hb)) as (Hk0 & Hab & _ & _ & Hrq).
  assert (Hab0 : In (b - 16, k + 16) (ablocks B ly S)).
  { apply (Permutation_in _ HPB) in Hab. apply in_app_or in Hab as [Hab | Hab]; [exact Hab|].
    exfalso. unfold ck_hblks in Hab. apply in_map_iff in Hab as ((b' & k') & E & Hb').
    cbn [fst snd] in E. change (@cf_head CfParams_preset) with 16 in E. injection E as E1 E2.
    assert (b' = b) by lia. assert (k' = k) by lia. subst b' k'. exact (HAP _ Hb' Hb). }
  assert (Hab2 : In (b - 16, k + 16) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym HPB2)); apply in_or_app; left; exact Hab0).
  destruct (crt3U_blk_bounds _ _ _ _ _ _ _ _ HAR2 Hab2) as (_ & _ & _ & Bpr2).
  pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hab Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFB in Hd.
  split; [|apply Bpr2; rewrite Hrq; lia].
  apply (K2 _ _ i Hab Hab2); [rewrite Hrq; lia|]. intros Hf. pose proof (Hnfp _ Hf). rewrite Hrq in Hd. subst F. lia. }
(* the stack bytes above the callee's sp *)
assert (Kst : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply K1; lia. }
(* the own frame's bytes and shadow outside v *)
assert (Kfr : forall a, F <= a < F + 512 -> ~ (F + CRT_OFF_V <= a < F + CRT_OFF_V + 56) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hv. apply (K4 CRT_CID pos a Hin).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFB. subst F. lia.
  - intros Hf. exact (Hv (HFP1 a Hf)). }
assert (Kfs : forall i, 0 <= i < 64 -> aview SEGS (w_H W2) mem2 (shadow_addr F + i) = aview SEGS (w_H Wc) memc (shadow_addr F + i)).
{ intros i Hi. apply (K4 CRT_CID pos _ Hin).
  - right. unfold in_zr. cbn [fst snd]. rewrite HFB. change (512 / 8) with 64. subst F. lia.
  - exact (Hshb i Hi). }
refine {| crt_live_journal := ex_intro _ WS2 (conj HJ2 HB2); crt_live_side := _; crt_live_lam_perm := HPL2;
          crt_live_blocks_perm := HPB2; crt_live_dx_apart := HAP2; crt_live_saved := _;
          crt_live_frame := _; crt_live_fspill := _; crt_live_copy_open := _;
          crt_live_copy_hull := _; crt_live_memnorm := HMN2 |}.
- (* crt_side *)
  refine {| crt_side_ledger := HLED2; crt_side_peak := HPK2; crt_side_room := HRL2;
            crt_side_arodata := _; crt_side_doc := _;
            crt_side_doc_blocks := ltac:(intros bk Hbk; exact (HLL _ (HDL _ Hbk))) |}.
  + intros a Hro Ho He. rewrite K3; [exact (HRD a Hro Ho He) | exact (crt3U_ro_img a Hro) | exact Ho | exact He | |].
    * intros Hpst. exact (crt_pst_ro_B HB_segs HB_relro a Hpst Hro).
    * intros (r & Hr & Hrr). exfalso. pose proof (Hnfp 0 (ex_intro _ r (conj Hr Hrr))). lia.
  + apply (crt3U_tree_keep Wc W2 memc mem2 (prh_lin Lamc) (prh_lin Lam') doc t D HDOC).
    * intros y Hy. destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
      -- split; [|exact (proj1 (HDpr2 y ltac:(lia)))].
         apply (K4 cid0 pos0 y Hin0c).
         ++ left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
         ++ intros Hf. pose proof (Hnfp _ Hf). lia.
      -- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
         destruct (crt3U_hblk _ _ _ _ _ _ _ _ _ _ _ _ b kb HLED (HDL _ Hb)) as (Hk0 & _).
         destruct (HDblk b kb Hb (y - (b - 16)) ltac:(lia)) as (H1 & H2).
         replace (b - 16 + (y - (b - 16))) with y in H1, H2 by lia. split; assumption.
    * intros y k Hy Hl. exact (HLL _ Hl).
- (* crt_live_saved *)
  intros j Hj k Hk. rewrite (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2); [exact (HSV j Hj k Hk)|].
  apply Kst. lia.
- (* crt_frame *)
  pose proof (crt_frame_flag_word HFRM) as Hfl.
  refine {| crt_frame_listed := Hin2; crt_frame_flag_word := _; crt_frame_present := _ |}.
  + rewrite EF2, EFl, <- Hfl. apply crt3_rdword_keep. intros j Hj. rewrite HFB.
    apply Kfr; unfold CRT_OFF_V; lia.
  + intros a Ha. rewrite EF2, HFB in Ha. exact (proj1 (Ffr2 a Ha)).
- (* crt_live_fspill *)
  intros k Hk. unfold CRT_SP_F in *. rewrite EF2.
  rewrite (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2); [exact (HSPF k Hk)|]. apply Kst. lia.
- (* crt_live_copy_open *)
  rewrite EF2.
  apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HCR].
  intros y Hy. unfold CRT_OFF_COPY in Hy. unfold shadow_of_addr.
  change (SHADOW_OFF + y / 8) with (shadow_addr y).
  replace (shadow_addr y) with (shadow_addr F + (shadow_addr y - shadow_addr F)) by lia. apply Kfs.
  unfold shadow_addr. assert (F / 8 + 28 <= y / 8 < F / 8 + 35) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  lia.
- (* crt_live_copy_hull *)
  rewrite EF2.
  intros s Hs. pose proof (crt3U_copy_hull F s F32 ltac:(lia) Hs) as Hr.
  replace s with (shadow_addr F + (s - shadow_addr F)) by lia. rewrite Kfs by lia.
  replace (shadow_addr F + (s - shadow_addr F)) with s by lia. exact (HCH s Hs).
Qed.

(* ---- copy's footprint (its 56 bytes in the own frame, its blocks Dx) across one of the stage's own runs: the
   AGREEMENT, shared by copy's tree and copy's ordered free list ---- *)
Lemma crt3U_copy_agree_run : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc
    {kbg : nat} {WS : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc' mdc' kj' WS ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ crt3U_wr (F_ lyc pos) a ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  forall y, pj_footR (F_ lyc pos + CRT_OFF_COPY) Dx y ->
    aview SEGS (w_H Wc) memc' y = aview SEGS (w_H Wc) memc y /\ apresent (w_H Wc) memc' y.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc kbg WS HL HJ' K.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_side_ledger HSD) as HLED.
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & _ & Fb1 & Fb2 & Fb3 & F32 & _ & _).
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ') as (_ & _ & _ & _ & _ & _ & Ffr' & _).
pose proof HJ' as (HARc' & _).
set (F := F_ lyc pos) in *.
intros y Hy. destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- unfold CRT_OFF_COPY in Hy. split; [|exact (proj1 (Ffr' y ltac:(lia)))].
  apply K; [pose proof asan_consts as (C1 & _); lia|]. apply (crt3U_nw_app F y ltac:(lia) ltac:(lia)); [|lia].
  apply (in_app_sub _ _ _ _ Fb3); lia.
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  assert (Hbl : In (b, kb) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
  destruct (crt3U_hblk _ _ _ _ _ _ _ _ _ _ _ _ b kb HLED Hbl) as (Hk0 & Hab & _ & _ & Hrq).
  destruct (crt3U_blk_bounds lyc Sc Hpc Wc memc' mdc' _ _ HARc' Hab) as (B4096 & Bce & Bapp & Bpr).
  rewrite Hrq in *. split; [|apply Bpr; lia].
  apply K; [pose proof asan_consts as (C1 & _); lia|]. apply (crt3U_nw_app F _ ltac:(lia) ltac:(lia)); [|lia].
  apply (in_app_sub _ _ _ _ Bapp); lia.
Qed.

(* ---- copy's tree across one of the stage's own runs ---- *)
Lemma crt3U_copy_run : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc tv
    {kbg : nat} {WS : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc' mdc' kj' WS ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ crt3U_wr (F_ lyc pos) a ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  crt_copy_tree Wc memc Lamc (F_ lyc pos) tv Dx -> crt_copy_tree Wc memc' Lamc (F_ lyc pos) tv Dx.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc tv kbg WS HL HJ' K HC.
unfold crt_copy_tree in *.
apply (crt3U_tree_keep Wc Wc memc memc' (prh_lin Lamc) (prh_lin Lamc) _ tv Dx HC); [|intros; assumption].
exact (crt3U_copy_agree_run lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc HL HJ' K).
Qed.

(* ---- copy's ORDERED FREE LIST (crt3_copy_fo0, crt_at_U_B_copy_fo's text) at a later memory whose copy footprint
   agrees and is present, over a ledger that still holds copy's blocks: PRH_PjOrder.pj_foR_frame ---- *)
Lemma crt3U_fo0_keep : forall (W1 W2 : world SEGS) m1 m2 (Lam1 Lam2 : list (Z * Z)) p Dt ms,
  crt3_copy_fo0 W1 m1 Lam1 p Dt ms ->
  (forall y, pj_footR p Dt y -> aview SEGS (w_H W2) m2 y = aview SEGS (w_H W1) m1 y /\ apresent (w_H W2) m2 y) ->
  (forall a k, In (a, k) Dt -> In (a, k) Lam2) ->
  crt3_copy_fo0 W2 m2 Lam2 p Dt ms.
Proof.
intros W1 W2 m1 m2 Lam1 Lam2 p Dt ms H HK HL. unfold crt3_copy_fo0 in *.
intros Hhd nn Hnn. destruct (H Hhd nn Hnn) as (Fo & HFo & HFm). exists Fo. split; [|exact HFm].
apply (PRH_PjOrder.pj_foR_frame SEGS nn (mrestrict (w_H W1) m1) (mrestrict (w_H W2) m2) (prh_lin Lam1)
  (prh_lin Lam2) p Dt Fo HFo).
- intros a k Hk. exact (HL a k Hk).
- intros y Hy. destruct (HK y Hy) as (Ha & Hpr). split.
  + exact (mbyte_of_aview SEGS (w_H W1) (w_H W2) m1 m2 y Ha).
  + intros _. exact (apresent_writable SEGS (w_H W2) m2 y Hpr).
Qed.

(* ---- copy's footprint across the callee: its header is the own frame's, outside v; its blocks are blocks of both
   states (they are among Dx, which the new state's blocks still hold). The AGREEMENT, shared by the tree and by
   the header cap below. ---- *)
Lemma crt3U_copy_agree : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc
  ly2 S2 Hp2 W2 mem2 md2 kj2 STKw spw FP1 k1 Dx' {kbg : nat} {WS2 WS1 : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 kj2 WS2 ->
  AJW STKw spw FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall a, inFP FP1 a -> F_ lyc pos + CRT_OFF_V <= a < F_ lyc pos + CRT_OFF_V + 56) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks Dx') -> (forall bk, In bk Dx -> In bk Dx') ->
  forall y, pj_footR (F_ lyc pos + CRT_OFF_COPY) Dx y ->
    aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y /\ apresent (w_H W2) mem2 y.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ly2 S2 Hp2 W2 mem2 md2 kj2 STKw spw FP1 k1 Dx'
  kbg WS2 WS1 HL HJ2 HJ1 HFP1 HPB2 HDD.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_side_ledger HSD) as HLED.
pose proof HJ1 as (HAR2 & Hly1 & _ & _ & _ & _ & _ & _ & K1 & K2 & K3 & K4 & _).
pose proof HJ as (HARc & _).
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & _ & Fb1 & Fb2 & Fb3 & F32 & _ & _).
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ2) as (_ & _ & _ & _ & _ & _ & Ffr2 & _).
destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc ly2 HARc Hly1) as (_ & Efa & _).
rewrite (Efa CRT_CID pos) in Ffr2.
pose proof crt3U_fb as HFB.
set (F := F_ lyc pos) in *.
intros y Hy. destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- unfold CRT_OFF_COPY in Hy. split; [|exact (proj1 (Ffr2 y ltac:(lia)))].
  apply (K4 CRT_CID pos y Hin).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFB. subst F. lia.
  + intros Hf. pose proof (HFP1 y Hf). unfold CRT_OFF_V in *. lia.
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  assert (Hbl : In (b, kb) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
  destruct (crt3U_hblk _ _ _ _ _ _ _ _ _ _ _ _ b kb HLED Hbl) as (Hk0 & Hab & _ & _ & Hrq).
  assert (Hab2 : In (b - 16, kb + 16) (ablocks B ly2 S2)).
  { apply (Permutation_in _ (Permutation_sym HPB2)). apply in_or_app. right. unfold ck_hblks.
    apply in_map_iff. exists (b, kb). split; [reflexivity | exact (HDD _ Hb)]. }
  destruct (crt3U_blk_bounds _ _ _ _ _ _ _ _ HAR2 Hab2) as (_ & _ & _ & Bpr2).
  pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hab Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFB, Hrq in Hd.
  replace y with (b - 16 + (y - (b - 16))) by lia.
  split; [|apply Bpr2; rewrite Hrq; lia].
  apply (K2 _ _ _ Hab Hab2); [rewrite Hrq; lia|]. intros Hf. pose proof (HFP1 _ Hf). unfold CRT_OFF_V in *. subst F. lia.
Qed.

Lemma crt3U_copy_call : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc
  ly2 S2 Hp2 W2 mem2 md2 kj2 STKw spw FP1 k1 Dx' Lam' tv {kbg : nat} {WS2 WS1 : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 kj2 WS2 ->
  AJW STKw spw FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall a, inFP FP1 a -> F_ lyc pos + CRT_OFF_V <= a < F_ lyc pos + CRT_OFF_V + 56) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks Dx') -> (forall bk, In bk Dx -> In bk Dx') ->
  (forall bk, In bk Lamc -> In bk Lam') ->
  crt_copy_tree Wc memc Lamc (F_ lyc pos) tv Dx -> crt_copy_tree W2 mem2 Lam' (F_ lyc pos) tv Dx.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ly2 S2 Hp2 W2 mem2 md2 kj2 STKw spw FP1 k1 Dx' Lam'
  tv kbg WS2 WS1 HL HJ2 HJ1 HFP1 HPB2 HDD HLL HC.
unfold crt_copy_tree in *.
apply (crt3U_tree_keep Wc W2 memc mem2 (prh_lin Lamc) (prh_lin Lam') _ tv Dx HC);
  [|intros y k _ Hl; exact (HLL _ Hl)].
exact (crt3U_copy_agree lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ly2 S2 Hp2 W2 mem2 md2 kj2
  STKw spw FP1 k1 Dx' HL HJ2 HJ1 HFP1 HPB2 HDD).
Qed.

(* ---- copy's HEADER CAP across a call (crt_at_U_B's cap conjunct, carried to S): the header's 56 bytes agree, so a
   header read at the later memory is a header read at the earlier one, where the cited conjunct applies. The
   writable half comes from the earlier state's own node (pj_rwR), not from the agreement. ---- *)
Lemma crt3U_cap_keep : forall (W1 W2 : world SEGS) m1 m2 p ms,
  pj_rwR SEGS (mrestrict (w_H W1) m1) p ->
  (forall y, p <= y < p + 56 -> aview SEGS (w_H W2) m2 y = aview SEGS (w_H W1) m1 y) ->
  crt3_cap W1 m1 p ms -> crt3_cap W2 m2 p ms.
Proof.
intros W1 W2 m1 m2 p ms Hrw HA HC ty num str kids keys n cap H2.
destruct H2 as (_ & T & N & Sx & K & Y & Nn & C).
assert (F : forall a w, p <= a -> a + w <= p + 56 -> forall z, a <= z < a + w ->
  mbyte SEGS (mrestrict (w_H W1) m1) z = mbyte SEGS (mrestrict (w_H W2) m2) z).
{ intros a w H1 H2' z Hz. exact (mbyte_of_aview SEGS (w_H W2) (w_H W1) m2 m1 z (eq_sym (HA z ltac:(lia)))). }
apply (HC ty num str kids keys n cap).
split; [exact Hrw|].
split; [apply (rd_u32_frame SEGS _ _ p ty T); apply (F p 4); lia|].
split; [apply (rd_u64_frame SEGS _ _ (p + 8) num N); apply (F (p + 8) 8); lia|].
split; [apply (rd_u64_frame SEGS _ _ (p + 16) str Sx); apply (F (p + 16) 8); lia|].
split; [apply (rd_u64_frame SEGS _ _ (p + 24) kids K); apply (F (p + 24) 8); lia|].
split; [apply (rd_u64_frame SEGS _ _ (p + 32) keys Y); apply (F (p + 32) 8); lia|].
split; [apply (rd_u64_frame SEGS _ _ (p + 40) n Nn); apply (F (p + 40) 8); lia|].
apply (rd_u64_frame SEGS _ _ (p + 48) cap C); apply (F (p + 48) 8); lia.
Qed.

(* ---- the same cap across one of the stage's own runs (the 14 shadow stores write no byte of copy) ---- *)
Lemma crt3U_cap_run : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc ms
    {kbg : nat} {WS : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc' mdc' kj' WS ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ crt3U_wr (F_ lyc pos) a ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  crt_copy_tree Wc memc Lamc (F_ lyc pos) (PjTree.JObj ms) Dx ->
  crt3_cap Wc memc (F_ lyc pos + CRT_OFF_COPY) ms -> crt3_cap Wc memc' (F_ lyc pos + CRT_OFF_COPY) ms.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc ms kbg WS HL HJ' K HC HCAP.
destruct (crt_live_journal HL) as (WSj & HJ & HBj).
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & _ & Fb1 & Fb2 & Fb3 & F32 & _ & _).
set (F := F_ lyc pos) in *.
unfold crt_copy_tree in HC. cbn [pj_nodeR] in HC.
destruct HC as (_ & _ & num0 & str0 & kids0 & keys0 & n0 & cap0 & Hh & _).
apply (crt3U_cap_keep Wc Wc memc memc' _ ms (proj1 Hh)); [|exact HCAP].
intros y Hy. unfold CRT_OFF_COPY in Hy.
apply K; [pose proof asan_consts as (C1 & _); lia|].
apply (crt3U_nw_app F y ltac:(lia) ltac:(lia)); [|lia].
apply (in_app_sub _ _ _ _ Fb3); lia.
Qed.

(* ---- the success arm's block is new: it was not in the call state's block list (FuzzStrdup.v sd_newblk, at ARx) ---- *)
Lemma crt3U_newblk : forall ly1 S1 ly' S' Hp' W' m' md' (b : Z * Z), ARx ly' S' Hp' W' m' md' -> 0 <= snd b ->
  ablocks B ly' S' = ablocks B ly1 S1 ++ [b] -> ~ In b (ablocks B ly1 S1).
Proof.
intros ly1 S1 ly' S' Hp' W' m' md' [p nb] HAR Hn E Hin. cbn [snd] in Hn.
assert (Hin' : In (p, nb) (ablocks B ly' S')) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks SEGS B ARx LAWS ly' S' Hp' W' m' md' p nb HAR Hin') as (_ & _ & _ & _ & _ & Hpw).
rewrite E in Hpw. apply in_split in Hin as (l1 & l2 & El). rewrite El in Hpw.
pose proof (pairwise_In2 zdisjoint _ (p, req_size nb) (p, req_size nb)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) l1) (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) [] Hpw
  ltac:(rewrite <- app_assoc, !map_app; reflexivity)) as Dz.
unfold zdisjoint in Dz. cbn [fst snd] in Dz.
assert (0 < req_size nb) by (unfold req_size; destruct (Z.eqb_spec nb 0); lia). lia.
Qed.

(* ---- what pj_string's journal keeps for the boundary: the stack above its sp (the spills) and the own frame's shadow
   (its footprint v is frame bytes, never a shadow byte) ---- *)
Lemma crt3U_call_keeps : forall lyc Sc Hpc Wc memc mdc kj pos ly2 S2 Hp2 W2 mem2 md2 STKw spw FP1 k1
    {WS WS1 : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS ->
  AJW STKw spw FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  spw = sp1 -> 0 <= STKw ->
  (forall a, inFP FP1 a -> F_ lyc pos + CRT_OFF_V <= a < F_ lyc pos + CRT_OFF_V + 56) ->
  (forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) /\
  (forall i, 0 <= i < 64 -> aview SEGS (w_H W2) mem2 (shadow_addr (F_ lyc pos) + i) =
                            aview SEGS (w_H Wc) memc (shadow_addr (F_ lyc pos) + i)).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos ly2 S2 Hp2 W2 mem2 md2 STKw spw FP1 k1 WS WS1 HJ HJ1 Espw HSTKw HFP1.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _ & _ & K4 & _).
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & _ & Fb1 & Fb2 & Fb3 & F32 & _ & _).
pose proof crt3U_fb as HFB.
set (F := F_ lyc pos) in *.
destruct (crt3_sp1 HPRE) as (Hs32 & Hs1 & Hs0). destruct (crt3_sp0 HPRE) as (Hal16 & Hsc & H47 & _).
pose proof crt3_stk as Hstk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
subst spw.
split.
- intros a Ha. apply K1; lia.
- intros i Hi. apply (K4 CRT_CID pos _ Hin).
  + right. unfold in_zr. cbn [fst snd]. rewrite HFB. change (512 / 8) with 64. subst F. lia.
  + intros Hf. pose proof (HFP1 _ Hf) as Hr.
    assert (F / 8 <= 2 ^ 44 - 64) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
    unfold CRT_OFF_V, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *; lia.
Qed.

Lemma crt3U_bsum_app : forall l1 l2, YCbq.bsum (l1 ++ l2) = YCbq.bsum l1 + YCbq.bsum l2.
Proof. induction l1 as [|b l1 IH]; intros l2; cbn [app]; [cbn; lia|]. rewrite !bsum_cons, IH. lia. Qed.

(* the registers a call and the stage's own runs keep: sp, gp, tp, s0, s1, s2 .. s4, s6, s7, s9, s11 *)
Definition crt3U_K0 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 27]%bv.
Lemma crt3U_K0_cs : forall r, In r crt3U_K0 -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. unfold crt3U_K0 in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr];
  [lazymatch goal with |- acallee_saved ?z => let v := eval vm_compute in z in change z with v end;
   unfold acallee_saved; lia|]).
destruct Hr.
Qed.
Lemma crt3U_dregs_of : forall rg rg' Fa, dregsB rg Fa -> (forall r, In r crt3U_K0 -> getr rg' r = getr rg r) ->
  dregsB rg' Fa.
Proof.
intros rg rg' Fa H HK.
pose proof (crt_dregs_B_bregs H) as HBR. pose proof (crt_dregs_B_s6 H) as R22.
pose proof (fun r (Hr : In r crt3U_K0) => HK r Hr) as HKr.
refine {| crt_dregs_B_bregs := {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _;
            crt_bregs_B_s0 := _; crt_bregs_B_s1 := _; crt_bregs_B_s2 := _; crt_bregs_B_s4 := _;
            crt_bregs_B_s3 := _; crt_bregs_B_s7 := _; crt_bregs_B_s9 := _; crt_bregs_B_s11 := _ |};
          crt_dregs_B_s6 := _ |}.
all: lazymatch goal with |- getr ?g ?r = _ =>
  rewrite (HKr r ltac:(unfold crt3U_K0; cbn [In]; repeat (first [left; reflexivity | right]))) end.
- exact (crt_bregs_B_sp HBR).
- exact (crt_bregs_B_gp HBR).
- exact (crt_bregs_B_tp HBR).
- exact (crt_bregs_B_s0 HBR).
- exact (crt_bregs_B_s1 HBR).
- exact (crt_bregs_B_s2 HBR).
- exact (crt_bregs_B_s4 HBR).
- exact (crt_bregs_B_s3 HBR).
- exact (crt_bregs_B_s7 HBR).
- exact (crt_bregs_B_s9 HBR).
- exact (crt_bregs_B_s11 HBR).
- exact R22.
Qed.

(* ---- AFTER pj_string (+0x25c, `beqz a0, +0x270`): the boundary at S. pj_string GRANTED: its post's
   DEAD-PJSTRING conjunct `(cnt <> fail -> a <> 0)` holds at fail = SIZE_MAXZ (U's ledger) with g_count far below
   it, so the refusal arm (a = 0, `mv s8, zero; j` to O1) is dead at its source and O1 is never entered from here;
   the chosen-fail arm needs cnt = SIZE_MAXZ, also excluded ---- *)
Definition crt3U_ssG : sstate := mkSS (CRT_PC_B + CRT_G_OFF_B) sr_atoms [] None (mkFacts [] [] []).
Lemma crt3U_ret : forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms ly2 S2 Hp2 W2 regs2 mem2 md2 k1 a
    {kbg : nat},
  STMT_S ->
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc 0 ran ->
  dregsB rg (F_ lyc pos) -> t = PjTree.JObj ms ->
  crt_copy_tree Wc memc Lamc (F_ lyc pos) t Db ->
  (forall a' k, In (a', k) Db -> ~ In (a' - cf_head, k + cf_head) (ablocks B ly S)) ->
  Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) ->
  Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) ->
  cntc = ck_cnt2 cnt t ->
  crt3_tblk (t := t) Db ->
  crt3_cap Wc memc (F_ lyc pos + CRT_OFF_COPY) ms ->
  crt3_copy_fo0 Wc memc Lamc (F_ lyc pos + CRT_OFF_COPY) Db ms ->
  spillB Wc memc CRT_SP_SHN_B (shadow_addr (doc + PJ_OFF_N)) ->
  spillB Wc memc CRT_SP_PN_B (doc + PJ_OFF_N) ->
  spillB Wc memc CRT_SP_N_B (Z.of_nat (length ms)) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F_ lyc pos + CRT_OFF_BACK) 56 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F_ lyc pos + CRT_OFF_V) 56 ->
  (exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS /\
     YCbqGwild.wbudget [] (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat WS) ->
  AJ (@STK_pj_string prh_img_B + 0) (sp1 + 0) [(F_ lyc pos + CRT_OFF_V, F_ lyc pos + CRT_OFF_V + 56)]
    lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall r : bv 5, In r crt3U_K0 -> getr regs2 r = getr rg r) ->
  getr regs2 21 = w64 (F_ lyc pos + CRT_OFF_V) ->
  room_live_cf S2 ->
  PRH_FnAlloc.prh_alloc_post B (Z.of_nat (length ck_STAMP) + 1) lyc Sc Hpc Wc Lamc peakc cntc SIZE_MAXZ ran most 0
    a ly2 S2 Hp2 W2 mem2 ->
  (cntc <> SIZE_MAXZ -> a <> 0) ->
  (a <> 0 -> posB S2 (tl (PresetReqAt.set_evs ms) ++ evsW ms)) ->
  (a <> 0 -> getr regs2 10 = w64 0 /\
     pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin ((a, Z.of_nat (length ck_STAMP) + 1) :: Lamc))
       (F_ lyc pos + CRT_OFF_V) (PjTree.JStr ck_STAMP) [(a, Z.of_nat (length ck_STAMP) + 1)]) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
    (mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_G_OFF_B))) mem2 (YK11.seg_rom SEGS)) md2) QFb.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms ly2 S2 Hp2 W2 regs2 mem2 md2 k1 a kbg
  HS3 Hfrm Hfrk HL HDR Ht HCOPY HDBn HDBp HDBl Hcnt HTB HCAP HFO0 HSP1 HSP2 HSP3 HRAb HRAv (WS2 & HJ2 & HB2) HJ1 HK2
  H21 HRL2 HAP HDEAD HPOS2 HSUC HMN2.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAPd. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMN.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK.
pose proof (crt_side_room HSD) as HRL. pose proof (crt_side_arodata HSD) as HRD.
pose proof (crt_side_doc HSD) as HDOC. pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (Hls & Hpk64 & Hcnt64 & _ & Hran).
pose proof HJ as (HARc & _).
pose proof HJ2 as (HAR2 & _).
pose proof HJ1 as (_ & Hly1 & _).
destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc ly2 HARc Hly1) as (_ & Efa & _).
assert (EF2 : F_ ly2 pos = F_ lyc pos) by apply Efa.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (crt3_sp1 HPRE) as (Hs32 & Hs1 & Hs0). destruct (crt3_sp0 HPRE) as (Hal16 & Hsc & H47 & Hshi).
pose proof crt3_stk as Hstk.
pose proof crt3U_fb as HFB.
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & _ & Fb1 & Fb2 & Fb3 & F32 & _ & _).
assert (Hcm : Crt102Model.cm_in x t) by exact (Crt102Model.cm_in_intro x t HREAD HLENX HWL0 HWL1).
(* g_count: the strdup's +1 stays inside the whole count, far below the top *)
assert (HCNT1 : cnt <= cntc + 1 <= cnt + ck_crt_count t 0).
{ apply (Crt102Model.cm_arm_C4a t ms 0 cnt (cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t)) cntc 1 Ht).
  - lia.
  - reflexivity.
  - rewrite Hcnt, Crt102Model.cm_cnt2_eq. lia.
  - lia. }
pose proof (Crt102Model.cm_in_count x t 0 Hcm ltac:(lia)) as Hcc.
assert (Hc1 : (cntc + 1) mod 2 ^ 64 = cntc + 1) by (apply Z.mod_small; lia).
set (F := F_ lyc pos) in *.
assert (HFP1 : forall z, inFP [(F + CRT_OFF_V, F + CRT_OFF_V + 56)] z -> F + CRT_OFF_V <= z < F + CRT_OFF_V + 56)
  by (intros z (rr & [<- | []] & Hz); cbn [fst snd] in Hz; lia).
destruct (crt3U_call_keeps lyc Sc Hpc Wc memc mdc kj pos ly2 S2 Hp2 W2 mem2 md2 _ _ _ k1 HJ HJ1 ltac:(lia)
  ltac:(pose proof crt_stk_nonneg_B as (_ & _ & HS3n & _); lia) HFP1) as (Kst & Kfs).
(* the three spill words and the two locals' shadow, at the post *)
assert (Hsp : forall off v, 0 <= off -> off + 8 <= 96 -> spillB Wc memc off v -> spillB W2 mem2 off v).
{ intros off v Ho1 Ho2 Hv k Hk. unfold crt_spill in Hv.
  rewrite (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2); [exact (Hv k Hk)|]. apply Kst. lia. }
assert (Hrak : forall off, 0 <= off -> off + 56 <= 512 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F + off) 56 ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (F + off) 56).
{ intros off Ho1 Ho2 HR. apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HR].
  intros y Hy. unfold shadow_of_addr. change (SHADOW_OFF + y / 8) with (shadow_addr y).
  replace (shadow_addr y) with (shadow_addr F + (shadow_addr y - shadow_addr F)) by lia. apply Kfs.
  unfold shadow_addr. lia. }
(* the symbolic state at the return: every register an atom of the post's register file, no region *)
set (E2 := @Eimg _ B_prog_listing PA (Ereg regs2 [])).
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (HAE2 : env_agree 32 (Ereg regs2 []) E2)
  by (subst E2; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew E2 10 = getr regs2 10)
  by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 [] 10 10%bv eq_refl)).
assert (HS : st_ok_pi (fx := fxk) SEGS VAL E2 crt3U_ssG
  (restrict (w_H W2) (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_G_OFF_B))) mem2 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold crt3U_ssG. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS (SOff 27 0) [] E2 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
pose (RUNTO := Crt102Kit.crt_run_to_xw (fx := fxk) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS WS2).
pose (BR := YSRrG.paj_branchR (fx := fxk) (PI := PA) (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)).
pose proof HJ2 as HJr.
destruct HAP as [(Ecf & _) | [(Hne2 & Ea0 & _) |
  (_ & Ha4096 & _ & Hanot & _ & EAB & _ & _ & _ & HLED2)]].
- (* chosen-fail: g_count would be g_fail_at = SIZE_MAX, far above the count *)
  exfalso. unfold SIZE_MAXZ in Ecf. lia.
- (* REFUSED (a = 0 at cnt <> fail): DEAD by the post's DEAD-PJSTRING conjunct *)
  exfalso. exact (HDEAD Hne2 Ea0).
- (* ===== SUCCESS (a <> 0, a0 = 0): the branch to S, v the string node over the new block (a, 21) ===== *)
  assert (Hane : a <> 0) by (change (@cf_head CfParams_preset) with 16 in Ha4096; lia).
  destruct (HSUC Hane) as (Hr10 & HNV).
  rewrite Hc1, HRAN in HLED2.
  assert (HPB2 : Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks ((a, Z.of_nat (length ck_STAMP) + 1) :: Db))).
  { rewrite EAB. eapply perm_trans; [apply Permutation_app_tail; exact HPB|]. rewrite <- app_assoc.
    apply Permutation_app_head. unfold ck_hblks. cbn [map fst snd]. apply Permutation_sym, Permutation_cons_append. }
  assert (HAP2 : forall bk, In bk ((a, Z.of_nat (length ck_STAMP) + 1) :: Db) -> ~ In bk D).
  { intros bk [<- | Hbk] HbD; [apply Hanot; exact (in_map fst _ _ (HDL _ HbD)) | exact (HAPd bk Hbk HbD)]. }
  pose proof (crt3U_live_call lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc 0 ran ly2 S2 Hp2 W2 mem2 md2 (kj + k1)
    _ _ _ k1 ((a, Z.of_nat (length ck_STAMP) + 1) :: Db) ((a, Z.of_nat (length ck_STAMP) + 1) :: Lamc) _ (cntc + 1) 0 0
    HL (ex_intro _ WS2 (conj HJ2 HB2)) HJ1 ltac:(lia) ltac:(pose proof crt_stk_nonneg_B as (_ & _ & HS3n & _); lia)
    HFP1 HLED2 ltac:(lia) HRL2 (fun bk H => in_cons _ _ _ H) ltac:(cbn [app]; apply perm_skip; exact HPL)
    HPB2 HAP2 HMN2) as HL2.
  pose proof (crt3U_copy_call lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc 0 ran ly2 S2 Hp2 W2 mem2 md2 (kj + k1)
    _ _ _ k1 ((a, Z.of_nat (length ck_STAMP) + 1) :: Db) ((a, Z.of_nat (length ck_STAMP) + 1) :: Lamc) t
    HL HJ2 HJ1 HFP1 HPB2 (fun bk H => in_cons _ _ _ H) (fun bk H => in_cons _ _ _ H) HCOPY) as HCOPY2.
  assert (E10v : ew E2 10 = Z_to_bv 64 0) by (rewrite E10, Hr10; reflexivity).
  psrr_branch_tok RUNTO BR HS SHOK (0, 0).
  + clear Hc.
    paj_run_to_tok_x RUNTO HS HJr SHOK (0, 0) (CRT_PC_B + CRT_S_OFF_B); [apply awr_ok_nil |].
    lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg ?m3 _) _ => rename m3 into ms3 end.
    assert (Emem3 : ms_mem ms3 = mem2).
    { apply Stdlib.Logic.FunctionalExtensionality.functional_extensionality. intros xw. apply HF.
      intros (r & Hr & _). cbn in Hr. exact Hr. }
    clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi (PI := PA) E2 _ _ regs2 [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]%bv
      HS HAE2 ltac:(vm_compute; reflexivity)) as KR3.
    cbn [ms_regs restrict] in KR3.
    pmkst HS.
    rewrite Emem3 in HJr |- *.
    eapply (HS3 fxk ly2 S2 Hp2 W2 mem2 _ (kj + k1) pos Db ((a, Z.of_nat (length ck_STAMP) + 1) :: Lamc) _ (cntc + 1)
      (ms_regs ms3) ms a).
    unfold crt_at_S3. rewrite EF2.
    split; [exact Ht|]. split; [exact Hfrm|]. split; [exact Hfrk|].
    split; [refine {| crt_live_journal := ex_intro _ WS2 (conj HJr HB2); crt_live_side := crt_live_side HL2;
      crt_live_lam_perm := crt_live_lam_perm HL2; crt_live_blocks_perm := crt_live_blocks_perm HL2;
      crt_live_dx_apart := crt_live_dx_apart HL2; crt_live_saved := crt_live_saved HL2;
      crt_live_frame := crt_live_frame HL2; crt_live_fspill := crt_live_fspill HL2;
      crt_live_copy_open := crt_live_copy_open HL2; crt_live_copy_hull := crt_live_copy_hull HL2;
      crt_live_memnorm := crt_live_memnorm HL2 |}|].
    split.
    { apply (crt3U_dregs_of rg); [exact HDR|]. intros r Hr. rewrite (KR3 r).
      - exact (HK2 r Hr).
      - unfold crt3U_K0 in Hr. cbn [In] in Hr |- *. tauto. }
    split; [rewrite (KR3 21%bv) by (cbn [In]; tauto); exact H21|].
    split; [apply Hsp; [unfold CRT_SP_SHN_B; lia | unfold CRT_SP_SHN_B; lia | exact HSP1]|].
    split; [apply Hsp; [unfold CRT_SP_PN_B; lia | unfold CRT_SP_PN_B; lia | exact HSP2]|].
    split; [apply Hsp; [unfold CRT_SP_N_B; lia | unfold CRT_SP_N_B; lia | exact HSP3]|].
    split; [exact (crt3_tree_ok LAWS HPRE HTREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2)|].
    split; [apply Hrak; [unfold CRT_OFF_BACK; lia | unfold CRT_OFF_BACK; lia | exact HRAb]|].
    split; [apply Hrak; [unfold CRT_OFF_V; lia | unfold CRT_OFF_V; lia | exact HRAv]|].
    split; [exact HCOPY2|].
    split; [exact HNV|].
    split.
    { intros a' k [Eak | Hin'].
      - injection Eak as <- <-. intros Hin0.
        assert (H37 : 0 <= Z.of_nat (length ck_STAMP) + 1 + cf_head) by (vm_compute; discriminate).
        apply (crt3U_newblk lyc Sc ly2 S2 Hp2 W2 mem2 md2
          (a - cf_head, Z.of_nat (length ck_STAMP) + 1 + cf_head) HAR2 H37 EAB).
        apply (Permutation_in _ (Permutation_sym HPB)). apply in_or_app. left. exact Hin0.
      - exact (HDBn a' k Hin'). }
    split; [exact HDBp|]. split; [exact HDBl|].
    split; [rewrite Hcnt; reflexivity|].
    split; [exact HTB|].
    (* copy's header cap: the cited U_B conjunct at the header's 56 bytes, which pj_string's call keeps *)
    split.
    { pose proof HCOPY as HC0. unfold crt_copy_tree in HC0. rewrite Ht in HC0. cbn [pj_nodeR] in HC0.
      destruct HC0 as (_ & _ & num0 & str0 & kids0 & keys0 & n0 & cap0 & Hh & _).
      apply (crt3U_cap_keep Wc W2 memc mem2 _ ms (proj1 Hh)); [|exact HCAP].
      intros y Hy. exact (proj1 (crt3U_copy_agree lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc 0 ran
        ly2 S2 Hp2 W2 mem2 md2 (kj + k1) _ _ _ k1 ((a, Z.of_nat (length ck_STAMP) + 1) :: Db)
        HL HJ2 HJ1 HFP1 HPB2 (fun bk H => in_cons _ _ _ H) y (or_introl Hy))). }
    split; [exact (HPOS2 Hane)|].
    (* copy's ordered free list: crt_at_U_B_copy_fo (carried to the call by the main proof), across pj_string's call
       by pj_foR_frame over the same footprint agreement as copy's tree; copy's blocks stay in the ledger *)
    apply (crt3U_fo0_keep Wc W2 memc mem2 Lamc ((a, Z.of_nat (length ck_STAMP) + 1) :: Lamc) _ Db ms HFO0).
    * exact (crt3U_copy_agree lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc 0 ran
        ly2 S2 Hp2 W2 mem2 md2 (kj + k1) _ _ _ k1 ((a, Z.of_nat (length ck_STAMP) + 1) :: Db)
        HL HJ2 HJ1 HFP1 HPB2 (fun bk H => in_cons _ _ _ H)).
    * intros a' k Hk. right. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hk.
  + (* beqz not taken would need a0 <> 0 *)
    exfalso. rewrite branch_eq_U, (U_atom E2 10 0 E10v ltac:(lia)), U_SLit in Hc.
    vm_compute in Hc. discriminate Hc.
Qed.

Lemma crt3_U : STMT_O1 -> STMT_S -> STMT_U.
Proof.
(* STMT_O1 stays a premise of the fixed statement, unused: pj_string's refusal is dead at its source
   (DEAD-PJSTRING), so U reaches only S *)
intros _ HS3. unfold CRT3_U.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms HU.
(* BY NAME: crt_at_U_B's fields are read by their projections, never by position (the record grew: the room
   position, copy's blocks UP TO PERMUTATION, copy's header cap and copy's ordered free list are its last four). *)
pose proof (crt_at_U_B_live HU) as HL. pose proof (crt_at_U_B_frm_zero HU) as Hfrm.
pose proof (crt_at_U_B_fregs HU) as Hfrk. pose proof (crt_at_U_B_dregs HU) as HDR.
pose proof (crt_at_U_B_obj HU) as Ht. pose proof (crt_at_U_B_tree_ok HU) as HTOK.
pose proof (crt_at_U_B_copy HU) as HCOPY. pose proof (crt_at_U_B_db_fresh HU) as HDBn.
pose proof (crt_at_U_B_db_lsz HU) as HDBp. pose proof (crt_at_U_B_db_nlive HU) as HDBl.
pose proof (crt_at_U_B_cnt HU) as Hcnt. pose proof (crt_at_U_B_pos HU) as HPOS.
pose proof (crt_at_U_B_copy_tblk HU) as HTB0. pose proof (crt_at_U_B_copy_cap HU) as HCAP0.
assert (HTB : crt3_tblk (t := t) Db) by (unfold crt3_tblk; exact HTB0). clear HTB0.
assert (HCAP : crt3_cap Wc memc (F_ lyc pos + CRT_OFF_COPY) ms)
  by (unfold crt3_cap; exact HCAP0). clear HCAP0.
assert (HFO0 : crt3_copy_fo0 Wc memc Lamc (F_ lyc pos + CRT_OFF_COPY) Db ms)
  by (unfold crt3_copy_fo0; exact (crt_at_U_B_copy_fo HU)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (crt3U_entry fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc 0 ran rg ms HL HDR Ht) as [HS SHOK].
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HPM.
pose proof HJ as (HARc & _).
destruct (crt3_ff LAWS lyc Sc Hpc Wc memc mdc kj pos HJ) as (Hin & Hnin & HF0 & HFc & HFapp & HF32 & HFpr & HFsh).
destruct (crt3_home_keep LAWS HPRE HTREE _ _ _ _ _ _ _ _ HJ) as (Hd8 & (cidd & posd & Hind & Hdlo & Hdhi) & Hdra).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc cidd posd HARc Hind) as (HD0 & HDc & HDapp).
destruct (crt3_sp1 HPRE) as (Hs32 & Hs1 & Hs0). destruct (crt3_sp0 HPRE) as (Hal16 & Hsc & H47 & _).
pose proof crt3_stk as Hstk.
pose proof crt3U_fb as HFB.
assert (Hnr : 0 <= Z.of_nat (length ms) < 2 ^ 64).
{ pose proof (crt_side_doc HSD) as HND. rewrite Ht in HND. cbn [pj_nodeR] in HND.
  destruct HND as (_ & _ & num & str & kids & keys & nn & cap & HHDR & Hrest).
  destruct Hrest as (_ & Hnn & _). destruct HHDR as (_ & _ & _ & _ & _ & _ & Hn40 & _). destruct Hn40 as (Hnr & _).
  rewrite <- Hnn. exact Hnr. }
set (F := F_ lyc pos) in *.
set (n := Z.of_nat (length ms)) in *.
destruct (crt3U_E_vals rg F n HDR ltac:(lia) ltac:(lia) ltac:(lia) Hnr) as (U2 & U9 & U18 & U19 & U22 & U27 & E32 & EL).
set (E := t3U_E rg n) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold t3U_E; apply Eimg_env).
pose (P := fun m : word -> option byte => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
pose (PLAW := srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)).
pose (RUN := @Crt102Kit.crt_run_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx cf_head LAWS P PLAW WSj).
unfold crt_cfg.
(* ---- run A: the fourteen unpoisoning stores, &doc->n and its shadow spilled, at the empty span ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM (0, 0).
- unfold t3U_ssA; cbn [ss_mem].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0)).
  + reflexivity.
  + rewrite U9. lia.
  + cbn [YP09.r_wlo t3U_rstack]. lia.
  + cbn [YP09.r_whi t3U_rstack]. lia.
  + eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat (shadow_addr F)).
    * reflexivity.
    * exact U18.
    * cbn [YP09.r_wlo YP09.r_whi t3U_rshadow]. intros a Ha.
      right; right; right. exists CRT_CID, pos. split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite HFB. change (512 / 8) with 64. subst F. lia.
    * apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi t3U_rdoc]; lia | apply awr_ok_nil].
- (* ---- after run A (+0x234): back's and v's shadow is open ---- *)
  rename ms0 into msA. clear HG HF.
  assert (HF8 : F mod 8 = 0) by (apply Z.mod_divide in HF32; [|lia]; destruct HF32 as [q Hq]; rewrite Hq;
    replace (q * 32) with ((4 * q) * 8) by lia; apply Z.mod_mul; lia).
  assert (HZ : forall i, (4 <= i <= 10 \/ 16 <= i <= 22) ->
    aview SEGS (w_H Wc) (ms_mem msA) (shadow_addr F + i) = Some 0).
  { intros i Hi. pose proof HS as (_ & _ & _ & _ & _ & _ & _ & (_ & HRG & _) & _).
    cbn [abs_ss setpc ss_mem restrict ms_mem] in HRG. apply Forall_inv_tail, Forall_inv in HRG.
    destruct HRG as (_ & _ & _ & HCK). cbn [YP09.r_base YP09.r_chunks base_val] in HCK. rewrite U18 in HCK.
    rewrite Forall_forall in HCK.
    assert (Hc : In (YP09.mkChunk i (CVal 1 (SLit 0)))
      [YP09.mkChunk 22 (CVal 1 (SLit 0)); YP09.mkChunk 21 (CVal 1 (SLit 0)); YP09.mkChunk 20 (CVal 1 (SLit 0));
       YP09.mkChunk 19 (CVal 1 (SLit 0)); YP09.mkChunk 18 (CVal 1 (SLit 0)); YP09.mkChunk 17 (CVal 1 (SLit 0));
       YP09.mkChunk 16 (CVal 1 (SLit 0)); YP09.mkChunk 10 (CVal 1 (SLit 0)); YP09.mkChunk 9 (CVal 1 (SLit 0));
       YP09.mkChunk 8 (CVal 1 (SLit 0)); YP09.mkChunk 7 (CVal 1 (SLit 0)); YP09.mkChunk 6 (CVal 1 (SLit 0));
       YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0))]).
    { assert (Hcase : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 16 \/ i = 17 \/ i = 18 \/
        i = 19 \/ i = 20 \/ i = 21 \/ i = 22) by lia.
      cbn [In]. repeat (destruct Hcase as [-> | Hcase]; [repeat (first [left; reflexivity | right])|]).
      subst i. repeat (first [left; reflexivity | right]). }
    unfold aview. rewrite (crt3U_chunk1 _ _ _ _ (HCK _ Hc)). cbn [option_map]. rewrite Z_to_bv_unsigned. reflexivity. }
  assert (HRAb : range_addressable (aview SEGS (w_H Wc) (ms_mem msA)) SHADOW_OFF (F + CRT_OFF_BACK) 56).
  { apply zero_shadow_range; [unfold CRT_OFF_BACK; rewrite Z.add_mod, HF8 by lia; reflexivity | reflexivity |].
    intros i Hi. change (56 / 8) with 7 in Hi. change (shadow_of_addr SHADOW_OFF (F + CRT_OFF_BACK)) with
      (shadow_addr (F + 8 * 4)). rewrite (crt3U_shadow_add F 4 HF8), <- Z.add_assoc. apply HZ. lia. }
  assert (HRAv : range_addressable (aview SEGS (w_H Wc) (ms_mem msA)) SHADOW_OFF (F + CRT_OFF_V) 56).
  { apply zero_shadow_range; [unfold CRT_OFF_V; rewrite Z.add_mod, HF8 by lia; reflexivity | reflexivity |].
    intros i Hi. change (56 / 8) with 7 in Hi. change (shadow_of_addr SHADOW_OFF (F + CRT_OFF_V)) with
      (shadow_addr (F + 8 * 16)). rewrite (crt3U_shadow_add F 16 HF8), <- Z.add_assoc. apply HZ. lia. }
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ crt3U_wr F a ->
    aview SEGS (w_H Wc) (ms_mem msA) a = aview SEGS (w_H Wc) memc a).
  { intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
    intros (r & Hr & Hrr). unfold t3U_ssA in Hr. cbn [ss_mem In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val t3U_rstack t3U_rshadow t3U_rdoc] in Hrr.
    - rewrite U9 in Hrr. apply Hn. right. lia.
    - rewrite U18 in Hrr. apply Hn. left. lia.
    - lia. }
  clear HFr.
  (* drop the frame-shadow region: its window lies in the shadow span the next run checks *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssA (restrict _ _) =>
    let rs := eval vm_compute in (pick (ss_mem ssA) [0; 2]%nat) in
    assert (HSB : st_ok_pi (fx := fxk) SEGS VAL E (mkSS (ss_pc ssA) (ss_regs ssA) rs (ss_resv ssA) (ss_facts ssA))
                    (restrict (w_H Wc) msA))
      by (apply (crt3U_st_ok_pi_submem fxk E ssA _ rs HS); [vm_compute; submem_tac | vm_compute; reflexivity])
  end.
  cbn [ss_pc ss_regs ss_resv ss_facts] in HSB. clear HS. rename HSB into HS.
  (* ---- run B: the instrumented load of doc->n, the spills, &v and STAMP, to pj_string's entry ---- *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  + (* doc->n is addressable: the document's 56 bytes are (its home, a frame of the entry, kept by the journal) *)
    unfold ob_holds. cbn [ob_x ob_n].
    destruct (crt3_home_keep LAWS HPRE HTREE _ _ _ _ _ _ _ _ HJ) as (_ & _ & HdraA).
    assert (HU27 : U E t3U_Bx = SHADOW_OFF)
      by (unfold t3U_Bx; rewrite U_SOff, U27, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
    assert (HU22 : U E (SOff 22 40) = doc + 40) by (rewrite U_SOff, U22; apply zcanon_id; unfold M64; lia).
    rewrite HU27, HU22. rewrite <- (aview_rd_of SEGS).
    eapply range_addressable_sub; [exact HdraA | lia | lia].
  + (* the only writable window left is the spill window *)
    cbn [ss_mem].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0)).
    * reflexivity.
    * rewrite U9. lia.
    * cbn [YP09.r_wlo]. lia.
    * cbn [YP09.r_whi]. lia.
    * apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil].
  + (* ---- at pj_string's entry (+0x258 `jal pj_string`): the state, then the call ---- *)
    rename ms0 into msB. clear HG HF.
    (* the two runs' model in the runner's normal form (the goal's, srr_norm_model) *)
    rewrite !wvb_collapse in HJ.
    assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 72 <= a < sp1 + 96) ->
      aview SEGS (w_H Wc) (ms_mem msB) a = aview SEGS (w_H Wc) (ms_mem msA) a).
    { intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
      intros (r & Hr & Hrr). cbn [ss_mem In] in Hr.
      destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr.
      - rewrite U9 in Hrr. exact (Hn Hrr).
      - lia. }
    clear HFr.
    assert (KAB : forall a, 0 <= a < 2 ^ 64 -> ~ crt3U_wr F a ->
      aview SEGS (w_H Wc) (ms_mem msB) a = aview SEGS (w_H Wc) memc a).
    { intros a Ha Hn. rewrite (KB a Ha); [exact (KA a Ha Hn)|]. intros Hw. apply Hn. right. exact Hw. }
    pose proof (crt3U_live_run lyc Sc Hpc Wc memc (ms_mem msB) mdc _ kj _ pos Db Lamc peakc cntc 0 ran HL HJ HBj KAB
      HPM) as HLB.
    pose proof (crt3U_copy_run lyc Sc Hpc Wc memc (ms_mem msB) mdc _ kj _ pos Db Lamc peakc cntc 0 ran t HL HJ KAB HCOPY)
      as HCOPYB.
    assert (HCAPB : crt3_cap Wc (ms_mem msB) (F + CRT_OFF_COPY) ms).
    { apply (crt3U_cap_run lyc Sc Hpc Wc memc (ms_mem msB) mdc _ kj _ pos Db Lamc peakc cntc 0 ran ms HL HJ KAB);
        [rewrite <- Ht; exact HCOPY | exact HCAP]. }
    (* copy's ordered free list across runs A and B: the same footprint agreement as copy's tree *)
    assert (HFO0B : crt3_copy_fo0 Wc (ms_mem msB) Lamc (F + CRT_OFF_COPY) Db ms).
    { apply (crt3U_fo0_keep Wc Wc memc (ms_mem msB) Lamc Lamc _ Db ms HFO0).
      - exact (crt3U_copy_agree_run lyc Sc Hpc Wc memc (ms_mem msB) mdc _ kj _ pos Db Lamc peakc cntc 0 ran HL HJ KAB).
      - intros a' k Hk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hk. }
    assert (Hshl : forall y, 0 <= y < 2 ^ 47 -> SHADOW_OFF <= shadow_of_addr SHADOW_OFF y < SHADOW_OFF + 2 ^ 44).
    { intros y Hy. unfold shadow_of_addr. pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)).
      assert (y / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
    assert (HRAbB : range_addressable (aview SEGS (w_H Wc) (ms_mem msB)) SHADOW_OFF (F + CRT_OFF_BACK) 56).
    { apply (range_addressable_agree (aview SEGS (w_H Wc) (ms_mem msA))); [|exact HRAb].
      intros y Hy. unfold CRT_OFF_BACK in Hy. pose proof (Hshl y ltac:(lia)).
      apply KB; unfold SHADOW_OFF in *; lia. }
    assert (HRAvB : range_addressable (aview SEGS (w_H Wc) (ms_mem msB)) SHADOW_OFF (F + CRT_OFF_V) 56).
    { apply (range_addressable_agree (aview SEGS (w_H Wc) (ms_mem msA))); [|exact HRAv].
      intros y Hy. unfold CRT_OFF_V in Hy. pose proof (Hshl y ltac:(lia)).
      apply KB; unfold SHADOW_OFF in *; lia. }
    (* the three spill words of runs A and B *)
    assert (V32 : U (ewset E 512 w) (SOff 32 0) = n).
    { rewrite U_SOff, (ew_ewset_other E 512 w 32) by lia. rewrite E32. unfold w64.
      rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
    assert (V22 : U (ewset E 512 w) (SOff 22 40) = doc + 40).
    { rewrite U_SOff, (ew_ewset_other E 512 w 22) by lia. rewrite U22. apply zcanon_id. unfold M64. lia. }
    assert (Vsh : U (ewset E 512 w) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 40) (SLit 3)) (SOff 27 0)) =
      shadow_addr (doc + 40)).
    { rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, V22.
      rewrite U_SOff, (ew_ewset_other E 512 w 27) by lia. rewrite U27, Z.add_0_r.
      rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
      pose proof (Z.div_pos (doc + 40) 8 ltac:(lia) ltac:(lia)).
      assert ((doc + 40) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
      unfold shadow_addr. rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia. }
    assert (HSPB : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msB)) (sp1 + CRT_SP_N_B) 8 n /\
      val_mem SEGS (mrestrict (w_H Wc) (ms_mem msB)) (sp1 + CRT_SP_PN_B) 8 (doc + PJ_OFF_N) /\
      val_mem SEGS (mrestrict (w_H Wc) (ms_mem msB)) (sp1 + CRT_SP_SHN_B) 8 (shadow_addr (doc + PJ_OFF_N))).
    { pose proof HS as (_ & _ & _ & _ & _ & _ & _ & (_ & HRG & _) & _).
      cbn [setpc ss_mem restrict ms_mem] in HRG. apply Forall_inv in HRG.
      destruct HRG as (_ & _ & _ & HCK). cbn [YP09.r_base YP09.r_chunks base_val] in HCK.
      rewrite (ew_ewset_other E 512 w 9), U9 in HCK by lia.
      pose proof (crt3U_chunk8 _ _ _ _ _ (Forall_inv HCK)) as HC1.
      pose proof (crt3U_chunk8 _ _ _ _ _ (Forall_inv (Forall_inv_tail HCK))) as HC2.
      pose proof (crt3U_chunk8 _ _ _ _ _ (Forall_inv (Forall_inv_tail (Forall_inv_tail HCK)))) as HC3.
      rewrite V32 in HC1. rewrite V22 in HC2. rewrite Vsh in HC3.
      unfold CRT_SP_N_B, CRT_SP_PN_B, CRT_SP_SHN_B, PJ_OFF_N. split; [exact HC1|]. split; [exact HC2 | exact HC3]. }
    (* the registers at the call *)
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    prreg HS (21%bv : bv 5) Q21.
    pose proof (crt_dregs_B_bregs HDR) as HBR. pose proof (crt_dregs_B_s6 HDR) as R22.
    pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3.
    pose proof (crt_bregs_B_tp HBR) as R4. pose proof (crt_bregs_B_s0 HBR) as R8.
    pose proof (crt_bregs_B_s1 HBR) as R9. pose proof (crt_bregs_B_s2 HBR) as R18.
    pose proof (crt_bregs_B_s4 HBR) as R20. pose proof (crt_bregs_B_s3 HBR) as R19.
    pose proof (crt_bregs_B_s7 HBR) as R23. pose proof (crt_bregs_B_s9 HBR) as R25.
    pose proof (crt_bregs_B_s11 HBR) as R27.
    pose proof HPRE as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & HROD0 & Hhi0 & Hrac0 & _).
    pose proof HJ as (HARB & HLYB & _).
    pose proof HLYB as (_ & _ & _ & _ & _ & _ & _ & _ & EtopB & EsloB & EshiB & _).
    pose proof (crt_live_side HLB) as HSDB. pose proof (crt_live_lam_perm HLB) as HPLB.
    pose proof (crt_live_blocks_perm HLB) as HPBB. pose proof (crt_live_dx_apart HLB) as HAPB.
    pose proof (crt_live_saved HLB) as HSVB. pose proof (crt_live_frame HLB) as HFRMB.
    pose proof (crt_live_fspill HLB) as HSPFB. pose proof (crt_live_copy_open HLB) as HCRB.
    pose proof (crt_live_copy_hull HLB) as HCHB. pose proof (crt_live_memnorm HLB) as HMNB.
    pose proof (crt_side_ledger HSDB) as HLEDB. pose proof (crt_side_peak HSDB) as HPKB.
    pose proof (crt_side_room HSDB) as HRLB. pose proof (crt_side_arodata HSDB) as HRDB.
    pose proof (crt_side_doc HSDB) as HDOCB. pose proof (crt_side_doc_blocks HSDB) as HDLB.
    destruct (crt3_ff LAWS lyc Sc Hpc Wc _ _ kj pos HJ) as (_ & _ & _ & _ & _ & _ & FfrB & FshB).
    destruct (crt3_chain HPRE _ _ _ _ _ _ _ _ HJ HSVB) as (ch1 & Hch1 & _).
    pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLEDB) as (_ & _ & Hcnt64 & _ & _).
    assert (Hcm : Crt102Model.cm_in x t) by exact (Crt102Model.cm_in_intro x t HREAD HLENX HWL0 HWL1).
    pose proof (Crt102Model.cm_in_count x t 0 Hcm ltac:(lia)) as Hcc.
    assert (HCNT1 : cnt <= cntc + 1 <= cnt + ck_crt_count t 0).
    { apply (Crt102Model.cm_arm_C4a t ms 0 cnt (cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t))
        cntc 1 Ht); [lia | reflexivity | rewrite Hcnt; lia | lia]. }
    assert (Hne : cntc <> SIZE_MAXZ) by (unfold SIZE_MAXZ; lia).
    assert (HBv : 4096 <= BASE <= 2 ^ 30) by (rewrite HB_base; split; vm_compute; first [discriminate | reflexivity]).
    assert (Esp : spZ (ms_regs msB) = sp1) by (unfold spZ; rewrite Q2, U2; reflexivity).
    assert (Es0 : s0Z (ms_regs msB) = sp0).
    { unfold s0Z. rewrite Q8, (EL 8%nat) by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat rg _ 8 8%bv eq_refl), R8.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    assert (Q3' : getr (ms_regs msB) 3 = w64 (as_gp B)).
    { rewrite Q3, (EL 3%nat) by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat rg _ 3 3%bv eq_refl), R3. exact Hgp0. }
    assert (Q4' : getr (ms_regs msB) 4 = w64 (as_tp B)).
    { rewrite Q4, (EL 4%nat) by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat rg _ 4 4%bv eq_refl), R4. exact Htp0. }
    assert (Q10' : getr (ms_regs msB) 10 = w64 (F + CRT_OFF_V)) by (rewrite Q10, U19; reflexivity).
    assert (H21B : getr (ms_regs msB) 21 = w64 (F + CRT_OFF_V)) by (rewrite Q21, U19; reflexivity).
    assert (Q11' : getr (ms_regs msB) 11 = w64 (CRT_STAMP_B (PA := PA))).
    { rewrite Q11, (HEI 243%nat) by (unfold A_TEXT, A_LIM; lia). reflexivity. }
    (* the room position: pj_string is called at the model index the position names; its event is set_evs's head *)
    assert (HPOS' : posB Sc ([PresetReqAt.HMal (Z.of_nat (Datatypes.S (length PresetReqAt.MOD_VAL)) + PresetReqAt.HEAD)] ++
      (tl (PresetReqAt.set_evs ms) ++ evsW ms))).
    { rewrite crt3_evsU_split, crt3_set_evs_cons in HPOS. exact HPOS. }
    destruct (crt3_pos_adv (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (t := t)
      Sc _ _ HPOS') as (pi & phist & Hsm & Hpos & Hrun & Hcons & Hclose).
    assert (EH : PresetReqAt.HMal (Z.of_nat (length ck_STAMP) + 1 + cf_head) =
      PresetReqAt.HMal (Z.of_nat (Datatypes.S (length PresetReqAt.MOD_VAL)) + PresetReqAt.HEAD)) by (vm_compute; reflexivity).
    (* the text's run model is the constant ReaderRes.jr_strtod: crt_pos's crt_pos_strtod (Hsm) moves the position,
       the run premise and the consumer window onto it *)
    assert (Hrun' : prh_run_at ReaderRes.jr_strtod rp_x rp_os pi
      (PRH_FnPj.prhPj_string_evs (Z.of_nat (length ck_STAMP)) cntc SIZE_MAXZ)).
    { unfold PRH_FnPj.prhPj_string_evs. rewrite (proj2 (Z.eqb_neq _ _) Hne), EH, <- Hsm.
      exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) Hrun)). }
    assert (Hpos' : PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os pi rp_H0 phist Sc)
      by (rewrite <- Hsm; exact Hpos).
    (* the consumer window of the call: the strdup's one event, the head of the window crt_pos carries *)
    assert (Hcons' : prh_cons_from ReaderRes.jr_strtod rp_x rp_os pi
      (length (PRH_FnPj.prhPj_string_evs (Z.of_nat (length ck_STAMP)) cntc SIZE_MAXZ))).
    { unfold PRH_FnPj.prhPj_string_evs. rewrite (proj2 (Z.eqb_neq _ _) Hne), EH, <- Hsm.
      rewrite length_app in Hcons. exact (proj1 (proj1 (prh_cons_from_app_iff _ _ _ _ _ _) Hcons)). }
    (* the live room: the blocks held are copy's, below rtt1's room (cm_copy_room_rtt) *)
    assert (HLV : blocks_bytes Sc + PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) <= LIVE_MAX).
    { apply (Crt102Model.cm_live_string t (blocks_bytes S) (blocks_bytes Sc) HLIVE).
      rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPB), crt3U_bsum_app.
      pose proof (Crt102Model.cm_copy_room_rtt t Db (Crt102Model.cm_in_wf x t Hcm) HDBp HDBl).
      pose proof (Crt102Model.cm_LIVE_rtt_nonneg t true). lia. }
    pose proof crt_stk_B as (_ & _ & _ & _ & HSTKs & _). rewrite crt3_pi_frame in HSTKs.
    eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
    { (* pj_string has no wild site: the budgeted call rule at its empty budget, P := (fun WS1 => WS1 = []), over
         R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf; the callee's plain text lifted (YA0nH.SRr_SRr',
         YCbqGcallW.fpostW_x_R_lift at YA0nH.wle_wle') and its post by YCbqGwild.fpostW_xb_of_xR; the caller's journal
         stays at its budget WSj *)
      eapply (YCbqGwild.aj_call_xWb_spR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)
        (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf)
        (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc _ _ msB
        STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc _ kj WSj (@STK_pj_string prh_img_B) 0
        [(F + CRT_OFF_V, F + CRT_OFF_V + 56)] (sp1 - sp0) (Z_to_bv 64 (BASE + 5048)) ch1 (fun WS1 => WS1 = []) _ HS
        eq_refl HJ).
      - rewrite Esp. lia.
      - exact (proj1 (crt_sp1_off sp0 Hal16)).
      - lia.
      - exact (proj1 (proj2 (proj2 crt_stk_nonneg_B))).
      - lia.
      - lia.
      - reflexivity.
      - lia.
      - exact Q3'.
      - exact Q4'.
      - exact Q1.
      - apply (ret_ok_codeptr_v (PI := PA)); [lia | vm_compute; reflexivity].
      - rewrite unsigned_lit_small by lia. lia.
      - rewrite Es0. replace (sp0 + (sp1 - sp0)) with sp1 by lia. exact Hch1.
      - (* pj family: entry-keyed event form; the run's length bound HOS4 (the text's DRAFT premise) *)
        intros HP1 HW1.
        eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
        { apply YA0nH.SRr_SRr'.
          refine (HPJS fxk rp_x rp_os pi rp_H0 phist lyc Sc Hpc Wc (ms_regs msB) (ms_mem msB) _ ch1 0
            (F + CRT_OFF_V) (CRT_STAMP_B (PA := PA)) ck_STAMP Lamc peakc cntc SIZE_MAXZ ran most 0
            _ HUNIV HRLB Hpos' HOS4 Hcons' Q10' Q11' HW1 _ _ _ _ (Crt102Model.cm_rq_stamp t HRQ) HLEDB (fun _ => HLV)
            Hrun').
          - (* fpre at pj_string's entry; the rounding mode is 0 (U's frm_zero at fxk) *)
            split; [exact HP1|]. split; [exact HRDB|]. split; [rewrite Esp, EshiB; lia|].
            split; [unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia | exact Hfrm].
          - (* v's slot: the own frame's bytes 0x80 .. 0xb8 *)
            split; [unfold CRT_OFF_V; lia|].
            split; [right; right; left; exists CRT_CID, pos; split; [exact Hin | rewrite HFB; unfold CRT_OFF_V; lia]|].
            split; [split; [unfold CRT_OFF_V; lia|]|].
            { intros z Hz. apply (apresent_writable SEGS). exact (proj1 (FfrB z ltac:(unfold CRT_OFF_V in Hz; lia))). }
            split; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
                    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, CRT_OFF_V; lia|].
            split; [intros z Hz; split; [exact (proj2 (FfrB z ltac:(unfold CRT_OFF_V in Hz; lia)))
                                         | rewrite Esp; unfold CRT_OFF_V in Hz; lia]|].
            split; [exact HRAvB|].
            apply crt3U_hull_frame; [exact HF32 | unfold CRT_OFF_V; lia | lia | unfold CRT_OFF_V; lia | lia|].
            intros i Hi. apply crt3U_aview_present. exact (proj1 (FshB i Hi)).
          - unfold CRT_OFF_V. lia.
          - unfold prh_head_wide. vm_compute. discriminate.
          - (* the stamp: a kept image string, apart from v (image bytes against a frame's) *)
            right. pose proof HKST as (_ & _ & Hk).
            destruct (crt3_str_hull_B HB_base HB_segs) as (_ & _ & Hklo & Hkhi).
            pose proof IMG_LO_B_val as EIL. pose proof IMG_TOP_B_val as EIT.
            split; [lia|].
            split; [exact (crt3U_cstr_stamp lyc Sc Hpc Wc (ms_mem msB) _ HARB HRDB)|].
            split; [right; right; exact HKST|].
            destruct (Z_le_gt_dec (CRT_STAMP_B (PA := PA) + Z.of_nat (length ck_STAMP) + 1) (F + CRT_OFF_V)) as [Hx | Hx];
              [left; exact Hx|].
            destruct (Z_le_gt_dec (F + CRT_OFF_V + 56) (CRT_STAMP_B (PA := PA))) as [Hy | Hy]; [right; exact Hy|].
            exfalso.
            destruct (Hk (Z.max (CRT_STAMP_B (PA := PA)) (F + CRT_OFF_V)) ltac:(lia)) as (Hro & _).
            apply (frm_img_x SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem msB) _ CRT_CID pos
              (Z.max (CRT_STAMP_B (PA := PA)) (F + CRT_OFF_V)) HARB Hin);
              [rewrite HFB; unfold CRT_OFF_V in *; lia | exact (crt3U_ro_img _ Hro)]. }
        intros W' c' _ HPOST. apply YCbqGwild.fpostW_xb_of_xR; [reflexivity|].
        apply YCbqGcallW.fpostW_x_R_lift; [exact (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact HPOST].
      - (* the callee's footprint: v, in the own frame *)
        intros z (rr & [<- | []] & Hz). cbn [fst snd] in Hz.
        right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|].
        unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFB. unfold CRT_OFF_V in Hz. lia. }
    (* ---- pj_string's post: on to the return (+0x25c) ---- *)
    cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW & HJ2 & HJ1 & _ & HP2 &
      (HQ & HKM)).
    subst WS1. rewrite app_nil_r in HJ2.
    destruct HQ as (HRL2 & ares & HAPo & HDEADo & HPOSo & HSUCo & _).
    replace (sp0 + (sp1 - sp0) + 0) with (sp1 + 0) in HJ1 by lia.
    assert (HAEB : env_agree 32 (Ereg rg [w64 n]) (ewset E 512 w)).
    { split; [intros q Hq; rewrite ew_ewset_other by lia; subst E; unfold t3U_E; apply Eimg_low; unfold A_TEXT; lia
             | reflexivity]. }
    pose proof (regs_kept_of_st_ok SEGS (ewset E 512 w) _ _ rg [w64 n] crt3U_K0 HS HAEB
      ltac:(vm_compute; reflexivity)) as KRB.
    cbn [ms_regs restrict] in KRB.
    assert (HPR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs msB) r).
    { intros r Hr. pose proof (HP2 (bv_unsigned r) Hr) as Hx. rewrite Z_to_bv_bv_unsigned in Hx. exact Hx. }
    assert (HK2 : forall r : bv 5, In r crt3U_K0 -> getr regs2 r = getr rg r).
    { intros r Hr. rewrite (HPR r (crt3U_K0_cs r Hr)). exact (KRB r Hr). }
    assert (H21' : getr regs2 21 = w64 (F + CRT_OFF_V)).
    { rewrite HPR; [exact H21B|].
      lazymatch goal with |- acallee_saved ?z => let v := eval vm_compute in z in change z with v end.
      unfold acallee_saved. lia. }
    unfold PRH_FnPj.prhPj_string_evs in HPOSo. rewrite (proj2 (Z.eqb_neq _ _) Hne) in HPOSo.
    change (Z_to_bv 64 (BASE + 5048)) with (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_G_OFF_B))).
    apply (crt3U_ret fxk lyc Sc Hpc Wc (ms_mem msB) _ kj pos Db Lamc peakc cntc rg ms ly2 S2 Hp2 W2 regs2 mem2 md2 k1
      ares HS3 Hfrm Hfrk HLB HDR Ht HCOPYB HDBn HDBp HDBl ltac:(rewrite Hcnt, Crt102Model.cm_cnt2_eq; reflexivity)
      HTB HCAPB HFO0B (proj2 (proj2 HSPB)) (proj1 (proj2 HSPB)) (proj1 HSPB) HRAbB HRAvB (ex_intro _ WSj (conj HJ2 HBj))
      HJ1 HK2 H21'
      HRL2 HAPo HDEADo).
    * intros Hane. apply Hclose. rewrite Hsm. exact (HPOSo (or_introl Hane)).
    * exact HSUCo.
    * intros H. exact (HKM (HMNB H)).
Qed.

End g.
End f.
End t3s.

Print Assumptions crt3_U.
