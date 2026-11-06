(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1260 of its 1335 lines of code are new or changed and 439 lines of the source are left out. *)
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
(* kb round: crt_live carries its budget kb (64 at S and O1) and its journal at a budget WS; the run to pj_set goes
   through Crt102Kit's AJW runner (crt_run_xw), its wild clause is Crt102Kit.crt_jw_wild (both used qualified), and
   pj_set (no wild site) through YCbqGwild.aj_call_xWb at its empty budget, so the caller's journal stays at the
   budget it had at S *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Kit.
(* The re-hiding move: the journal at YA0nH.wle' SEGS YGcfRehidePost.RZ_cf, the
   steps at YA0nH.SRr' (YSRrG's bind / mono / step), pj_set's text at its own SRr' / fpostWmR (the re-hiding contract's
   R4) through YCbqGwild.aj_call_xWbR *)
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
(* the journal at a wild-trace budget WS at the contract's R (YCbqG.v ajournal_xwR at YA0nH.wle' SEGS
   YGcfRehidePost.RZ_cf; ajournal_xR is it at WS = []); crt_live's journal is at the boundary's budget kb (kb round) *)
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
(* THE RUN HAS AT MOST 4 CALLS (DRAFT, the text's own premise PRH_FnCheck.v:2363): tpj_set_specX asks it of the
   caller's rp_os (its hull budget paid from the position, lib/A/PresetHullPay.v hull_budget_of_room_pos) *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.

(* ======================================================================================================== *)
(* ---- IMAGE-FREE HELPERS: lists, permutations, the read-back's block sizes, the view ---- *)
Lemma crt3s_nodup_app : forall (l1 l2 : list Z) y, NoDup (l1 ++ l2) -> In y l1 -> In y l2 -> False.
Proof.
intros l1. induction l1 as [|z l1 IH]; intros l2 y H H1 H2; [destruct H1|].
cbn [app] in H. inversion H as [|? ? Hn Hd]; subst. destruct H1 as [<- | H1].
- apply Hn. first [apply list_elem_of_In | apply elem_of_list_In | idtac]. apply in_or_app. right. exact H2.
- exact (IH l2 y Hd H1 H2).
Qed.
Lemma crt3s_nodup_perm : forall (l l' : list Z), Permutation l l' -> NoDup l -> NoDup l'.
Proof. intros l l' HP HN. rewrite <- HP. exact HN. Qed.
(* two blocks of a ledger list split in two halves have different bases *)
Lemma crt3s_nodup_apart : forall (L A Bl : list (Z * Z)) u v,
  NoDup (map fst L) -> Permutation L (A ++ Bl) -> In u A -> In v Bl -> fst u = fst v -> False.
Proof.
intros L A Bl u v HN HP HA HB E.
assert (HN' : NoDup (map fst (A ++ Bl))) by (exact (crt3s_nodup_perm _ _ (Permutation_map fst HP) HN)).
rewrite map_app in HN'. apply (crt3s_nodup_app (map fst A) (map fst Bl) (fst u) HN').
- apply in_map. exact HA.
- rewrite E. apply in_map. exact HB.
Qed.
Lemma crt3s_hbl_app : forall l1 l2, PRH_FnPj.prhPj_hbl (l1 ++ l2) = PRH_FnPj.prhPj_hbl l1 ++ PRH_FnPj.prhPj_hbl l2.
Proof. intros l1 l2. unfold PRH_FnPj.prhPj_hbl. apply map_app. Qed.
(* the allocator blocks after a call that moves the harness blocks Dx to Do (prhPj_blocks), relative to the entry *)
Lemma crt3s_ablocks_perm : forall (AS AC A2 Dx L0 Lamc Lam' Do other : list (Z * Z)),
  Permutation AC (AS ++ ck_hblks Dx) -> Permutation Lamc (Dx ++ L0) ->
  Permutation AC (PRH_FnPj.prhPj_hbl Lamc ++ other) -> Permutation A2 (PRH_FnPj.prhPj_hbl Lam' ++ other) ->
  Permutation Lam' (Do ++ L0) -> Permutation A2 (AS ++ ck_hblks Do).
Proof.
intros AS AC A2 Dx L0 Lamc Lam' Do other H1 H2 H3 H4 H5.
change (ck_hblks Dx) with (PRH_FnPj.prhPj_hbl Dx) in H1. change (ck_hblks Do) with (PRH_FnPj.prhPj_hbl Do).
assert (E1 : Permutation (PRH_FnPj.prhPj_hbl Lamc) (PRH_FnPj.prhPj_hbl Dx ++ PRH_FnPj.prhPj_hbl L0)).
{ rewrite <- crt3s_hbl_app. apply Permutation_map. exact H2. }
assert (E2 : Permutation (PRH_FnPj.prhPj_hbl Lam') (PRH_FnPj.prhPj_hbl Do ++ PRH_FnPj.prhPj_hbl L0)).
{ rewrite <- crt3s_hbl_app. apply Permutation_map. exact H5. }
assert (E3 : Permutation AS (PRH_FnPj.prhPj_hbl L0 ++ other)).
{ apply (Permutation_app_inv_l (PRH_FnPj.prhPj_hbl Dx)).
  apply (Permutation_trans (Permutation_app_comm _ _)). apply (Permutation_trans (Permutation_sym H1)).
  apply (Permutation_trans H3). rewrite app_assoc. apply Permutation_app_tail. exact E1. }
apply (Permutation_trans H4). apply (Permutation_trans (Permutation_app_tail other E2)).
rewrite <- app_assoc. apply (Permutation_trans (Permutation_app_head _ (Permutation_sym E3))).
apply Permutation_app_comm.
Qed.
(* the read-back's live sizes are among its requests *)
Lemma crt3s_rm1n_in : forall k s y0, In y0 (ReaderRes.rm1n k s) -> In y0 s.
Proof.
intros k s. induction s as [|y s IH]; intros y0 H; cbn [ReaderRes.rm1n] in H; [exact H|].
destruct (Nat.eqb y k); [right; exact H|]. destruct H as [<- | H]; [left; reflexivity | right; exact (IH y0 H)].
Qed.
Lemma crt3s_lsz_le : forall (tr : list PjGrammar.ev) s M,
  (forall y0, In y0 s -> Z.of_nat y0 <= M) -> (forall e, In e tr -> Z.of_nat (PjGrammar.esize e) <= M) ->
  forall y0, In y0 (fold_left ReaderRes.lsz_ev tr s) -> Z.of_nat y0 <= M.
Proof.
intros tr. induction tr as [|e tr IH]; intros s M Hs He y0 Hx; cbn [fold_left] in Hx; [exact (Hs y0 Hx)|].
apply (IH (ReaderRes.lsz_ev s e) M); [|intros e' He'; apply He; right; exact He' | exact Hx].
intros y Hy. pose proof (He e (or_introl eq_refl)) as Hee.
destruct e as [n|[|m] n|n|n]; cbn [ReaderRes.lsz_ev PjGrammar.esize] in Hy, Hee.
- destruct Hy as [<- | Hy]; [exact Hee | exact (Hs y Hy)].
- destruct Hy as [<- | Hy]; [exact Hee | exact (Hs y Hy)].
- destruct Hy as [<- | Hy]; [exact Hee | exact (Hs y (crt3s_rm1n_in _ _ _ Hy))].
- exact (Hs y Hy).
- exact (Hs y (crt3s_rm1n_in _ _ _ Hy)).
Qed.
Lemma crt3s_maxreq_ge : forall (tr : list PjGrammar.ev) e, In e tr ->
  Z.of_nat (PjGrammar.esize e) <= fold_right Z.max 0 (map (fun e => Z.of_nat (PjGrammar.esize e)) tr).
Proof.
intros tr. induction tr as [|e' tr IH]; intros e H; [destruct H|].
cbn [map fold_right]. destruct H as [<- | H]; [lia|]. specialize (IH e H). lia.
Qed.
(* a block a tree of the read-back owns has a size below the read-back's largest request *)
Lemma crt3s_lsz_maxreq : forall (tr : list PjGrammar.ev) y0, In y0 (ReaderRes.lsz tr) ->
  Z.of_nat y0 <= fold_right Z.max 0 (map (fun e => Z.of_nat (PjGrammar.esize e)) tr).
Proof.
intros tr y0 H. apply (crt3s_lsz_le tr [] _ (fun y Hy => False_ind _ Hy) (crt3s_maxreq_ge tr) y0 H).
Qed.

(* ---- the view: a byte string read through it, a word kept by it, presence ---- *)
Lemma crt3s_vm_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall y, a <= y < a + Z.of_nat n -> aview SEGS H' m' y = aview SEGS H m y) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v HA Hv k Hk. rewrite (mbyte_of_aview SEGS H H' m m'); [exact (Hv k Hk)|]. apply HA. lia.
Qed.
Lemma crt3s_garr8_of_view : forall (H : word -> bool) (m : word -> option byte) p (l : list Z),
  (forall j, (j < length l)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0)) ->
  Forall (fun c => 0 <= c < 256) l -> garr8 SEGS (mrestrict H m) p l.
Proof.
intros H m p l HV HB j Hj. pose proof (proj1 (Forall_forall _ _) HB (nth j l 0) (nth_In l 0 Hj)) as Hr.
split; [|exact Hr]. intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (HV j Hj). unfold aview in HV.
destruct (mbyte SEGS (mrestrict H m) (p + Z.of_nat j)) as [b|] eqn:E; cbn [option_map] in HV; [|discriminate HV].
injection HV as HV. f_equal. rewrite <- HV. apply bv_eq. rewrite Z_to_bv_unsigned.
pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
cbv [YO0f.le_byte]. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite !Z.mod_small; lia.
Qed.
Lemma crt3s_bsum_app : forall l1 l2, YCbq.bsum (l1 ++ l2) = YCbq.bsum l1 + YCbq.bsum l2.
Proof. induction l1 as [|b l1 IH]; intros l2; cbn [app]; [cbn; lia|]. rewrite !bsum_cons, IH. lia. Qed.

(* ---- pairwise lists, blocks against frames, harness blocks, the callee's footprint ---- *)
Lemma crt3s_pw_cross : forall (A : Type) (R : A -> A -> Prop) l1 l2 u v,
  pairwise R (l1 ++ l2) -> In u l1 -> In v l2 -> R u v.
Proof.
intros A R l1. induction l1 as [|z l1 IH]; intros l2 u v H H1 H2; [destruct H1|].
cbn [app pairwise] in H. destruct H as [Hz Hl]. destruct H1 as [<- | H1].
- exact (proj1 (Forall_forall _ _) Hz v (in_or_app _ _ _ (or_intror H2))).
- exact (IH l2 u v Hl H1 H2).
Qed.
Lemma crt3s_blk_frm : forall lyc Sc Hpc Wc memc mdc p n f,
  ARx lyc Sc Hpc Wc memc mdc -> In (p, n) (ablocks B lyc Sc) -> In f (frames Sc) ->
  p + req_size n <= frame_addr lyc (fst f) (snd f) \/ frame_addr lyc (fst f) (snd f) + fs_frame_bytes (fst f) <= p.
Proof.
intros lyc Sc Hpc Wc memc mdc p n f HAR Hb Hf.
destruct (alx_sep SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc HAR) as [Hpw _].
pose proof (crt3s_pw_cross _ zdisjoint _ _ _ _ Hpw
  (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (p, n) Hb)
  (in_map (fun f0 : Z * Z => (frame_addr lyc (fst f0) (snd f0), fs_frame_bytes (fst f0))) _ f Hf)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.
Lemma crt3s_hblk : forall lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc b k,
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
Lemma crt3s_blk_bounds : forall lyc Sc Hpc Wc memc mdc p n,
  ARx lyc Sc Hpc Wc memc mdc -> In (p, n) (ablocks B lyc Sc) ->
  4096 <= p /\ p + req_size n <= YM05.alloc_ceiling /\ in_app p (req_size n) /\ p mod 16 = 0.
Proof.
intros lyc Sc Hpc Wc memc mdc p n HAR Hb.
destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc p n HAR Hb) as (H16 & H4096 & Hc & Happ & _).
auto.
Qed.
Lemma crt3s_fp1_inv : forall Fa (Dx : list (Z * Z)) z,
  inFP ((Fa + CRT_OFF_COPY, Fa + CRT_OFF_COPY + 56) :: (Fa + CRT_OFF_V, Fa + CRT_OFF_V + 56) ::
        ablocks_fp (PRH_FnPj.prhPj_hbl Dx)) z ->
  (Fa + CRT_OFF_COPY <= z < Fa + CRT_OFF_COPY + 56) \/ (Fa + CRT_OFF_V <= z < Fa + CRT_OFF_V + 56) \/
  exists b k, In (b, k) Dx /\ b - 16 <= z < b - 16 + req_size (k + 16).
Proof.
intros Fa Dx z H. apply inFP_cons in H as [H | H]; [left; exact H|].
apply inFP_cons in H as [H | H]; [right; left; exact H|].
right; right. apply inFP_ablocks_fp_inv in H as (p & n & Hin & Hr).
unfold PRH_FnPj.prhPj_hbl in Hin. apply in_map_iff in Hin as ((b & k) & E & Hbk). cbn [fst snd] in E.
injection E as <- <-. change (@cf_head CfParams_preset) with 16 in Hr. exists b, k. split; [exact Hbk | exact Hr].
Qed.

(* ---- the frame's shadow covers the hull of a 56-byte local (F 32-aligned, the local 32 bytes in or more) ---- *)
Lemma crt3s_hull_frame : forall (rd : reader) Fa off n,
  Fa mod 32 = 0 -> 32 <= off -> 0 < n -> off + n <= 448 -> 0 <= Fa ->
  (forall i, 0 <= i < 64 -> rd (shadow_addr Fa + i) <> None) -> shadow_hull_vis rd (Fa + off) n.
Proof.
intros rd Fa off n H32 Hoff Hn Hon HF0 Hpr s Hs.
replace s with (shadow_addr Fa + (s - shadow_addr Fa)) by lia. apply Hpr.
unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.

(* ---- an image string under route (a) (kept_img): its shadow at any ARx state (S4_PsSrc.v psrc_shadow, case 3,
   with its two arithmetic lemmas psrc_hull_img / psrc_zs_byte). The hull is IMAGE B's, [IMG_LO_B, IMG_TOP_B), in
   the allocator lane's FuzzStrdupB form (commit e8c226ad89c3,
   lib/B/Prog/FuzzStrdupB.v:131-135 sd_hull_img): never image A's
   IMG_LO / IMG_TOP ---- *)
Lemma crt3s_hull_img : forall p n s, 0 < n -> IMG_LO_B + 64 <= p -> p + n + 64 <= IMG_TOP_B ->
  shadow_addr p / 8 * 8 <= s < shadow_addr (p + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ IMG_LO_B <= 8 * (s - SHADOW_OFF) < IMG_TOP_B.
Proof.
intros p n s Hn Hlo Hhi Hs. pose proof IMG_LO_B_val as EL. pose proof IMG_TOP_B_val as ET. rewrite EL, ET in *.
unfold shadow_addr in *. unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.
Lemma crt3s_zs_byte : forall (rd : reader) q m z, q mod 8 = 0 -> m mod 8 = 0 -> zero_shadow rd SHADOW_OFF q m ->
  q <= z < q + m -> rd (shadow_addr z) = Some 0.
Proof.
intros rd q m z Hq Hm Hz Hx. unfold shadow_addr.
replace (SHADOW_OFF + z / 8) with (shadow_of_addr SHADOW_OFF q + (z / 8 - q / 8)) by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.
(* the bounds are image B's and come from the B' fact (Crt102B_T3Base.crt3_str_hull_B at the caller), not from
   kept_img's hull; kept_img gives the per-byte facts only *)
Lemma crt3s_kimg_shadow : forall lyc Sc Hpc Wc memc mdc p n,
  ARx lyc Sc Hpc Wc memc mdc -> kept_img B p n -> 0 < n ->
  IMG_LO_B + 64 <= p -> p + n + 64 <= IMG_TOP_B ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF p n /\ shadow_hull_vis (aview SEGS (w_H Wc) memc) p n.
Proof.
intros lyc Sc Hpc Wc memc mdc p n HAR (_ & _ & Hk) Hn Hlo Hhi. split.
- intros z Hz. destruct (Hk z Hz) as (_ & _ & _ & [Hzs | (v & Hc & Hv)]).
  + destruct Hzs as (q & m & Hin & Hq & Hqm). destruct (ZSA q m Hin) as [Zq Zm].
    pose proof (alx_zshadow SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc (q, m) HAR
      ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz0.
    cbn [fst snd] in Hz0. exists 0. split; [|left; reflexivity].
    unfold shadow_of_addr. change (SHADOW_OFF + z / 8) with (shadow_addr z).
    apply (crt3s_zs_byte _ q m z Zq Zm Hz0). lia.
  + pose proof (alx_const_cells SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc HAR) as HC.
    pose proof (proj1 (Forall_forall _ _) HC _ (Hc lyc)) as Hch.
    cbn [cell_holds z1 c1 c_at c_w c_val aeval] in Hch. specialize (Hch 0%nat ltac:(lia)).
    rewrite Z.add_0_r in Hch. exists v. split.
    * unfold shadow_of_addr. change (SHADOW_OFF + z / 8) with (shadow_addr z). rewrite Hch. f_equal.
      unfold le_byte. cbn [Z.of_nat]. rewrite Z.shiftr_0_r. change (2 ^ (8 * 1)) with 256.
      rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
    * destruct Hv as [Hv|Hv]; [left; exact Hv | right; exact Hv].
- intros s0 Hs. destruct (crt3s_hull_img p n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
  apply (IMGV lyc Sc Hpc Wc memc mdc _ HAR). rewrite crt3_cfimgB_lo, crt3_cfimgB_top. exact Hr.
Qed.

(* ---- the key "modifiedAt" at any state the read-only view holds: its C-string facts (cstr_ok) ---- *)
Definition crt3s_tail_b (segs : list Segment) (p n : Z) : bool :=
  forallb (fun i => match YK11.seg_rom segs (Z_to_bv 64 (p + n + 1 + Z.of_nat i)) with Some _ => true | None => false end)
    (seq 0 (Z.to_nat (7 - (p + n) mod 8))).
Lemma crt3s_tail_ok : forall (H : word -> bool) (m : word -> option byte) p n,
  crt3s_tail_b SEGS p n = true -> forall z, p + n < z < p + n - (p + n) mod 8 + 8 -> aview SEGS H m z <> None.
Proof.
intros H m p n Hb z Hz. unfold crt3s_tail_b in Hb. rewrite forallb_forall in Hb.
pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)) as Hr.
specialize (Hb (Z.to_nat (z - (p + n + 1)))). rewrite in_seq in Hb.
specialize (Hb ltac:(lia)). rewrite Z2Nat.id in Hb by lia. replace (p + n + 1 + (z - (p + n + 1))) with z in Hb by lia.
unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 z)); [cbn; discriminate|].
destruct (YK11.seg_rom SEGS (Z_to_bv 64 z)); [cbn; discriminate | discriminate Hb].
Qed.
Lemma crt3s_mod_tail : crt3s_tail_b SEGS (CRT_MOD_AT_B (PA := PA)) (Z.of_nat (length ck_MOD_AT)) = true.
Proof.
destruct (crt_str_res_B (PA := PA)) as (_ & H2 & _). rewrite HB_segs, HB_base in H2.
assert (C : match res_pair (segf B.Img0.rsegs) (B_prog_base + (CRT_PC_B + CRT_MODAT1_HI_B))
                  (B_prog_base + (CRT_PC_B + CRT_MODAT1_LO_B)) with
            | Some p => crt3s_tail_b B.Img0.rsegs p (Z.of_nat (length ck_MOD_AT)) | None => false end = true)
  by (vm_compute; reflexivity).
rewrite H2 in C. rewrite HB_segs. exact C.
Qed.
Lemma crt3s_cstr_mod : forall lyc Sc Hpc Wc memc mdc,
  ARx lyc Sc Hpc Wc memc mdc -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memc) ->
  cstr_ok Wc memc (CRT_MOD_AT_B (PA := PA)) ck_MOD_AT.
Proof.
intros lyc Sc Hpc Wc memc mdc HAR HROD.
(* the string's bounds: image B's, from the B' fact (crt3_str_hull_B), not kept_img's hull *)
pose proof HKMOD as (_ & _ & Hk). destruct (crt3_str_hull_B HB_base HB_segs) as (Hlo & Hhi & _ & _).
pose proof IMG_LO_B_val as EL. pose proof IMG_TOP_B_val as ET.
pose proof YM05.alloc_ceiling_val as Hac.
assert (Hn : Z.of_nat (length ck_MOD_AT) = 10) by reflexivity.
destruct (crt3s_kimg_shadow lyc Sc Hpc Wc memc mdc _ _ HAR HKMOD ltac:(lia) Hlo Hhi) as [HRA HHU].
split; [split|].
{ apply crt3s_garr8_of_view.
  - intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    destruct (Hk (CRT_MOD_AT_B (PA := PA) + Z.of_nat j) ltac:(lia)) as (Hro & Hno & Her & _).
    rewrite (HROD _ Hro Hno Her).
    exact (proj1 (crt_str_rom_B HB_base HB_segs) j ltac:(unfold CRT_MOD_AT_S; rewrite length_app; cbn [length]; lia)).
  - unfold ck_MOD_AT. cbn [app]. repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
{ unfold ck_MOD_AT. repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold YGcfStr.amem_range8, kLowMemEnd; lia|].
split; [exact HRA|]. split; [exact HHU|].
apply crt3s_tail_ok. exact crt3s_mod_tail.
Qed.

(* ---- THE LIVE STATE ACROSS A CALL (Crt102Kit.v crt102rw_live_call at image A', transcribed with the B' names): the
   callee's journal from this function's state at its sp sp1 keeps the saved words, the spills, the frame's flag word
   and copy's shadow; the caller supplies the new side facts, the block lists and the memnorm keep ---- *)
Lemma crt3s_live_call : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc
  STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Dx' Lamc' peakc' cntc' ownc' ranc' {kbg kbg' : nat} {WS1 : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (exists WS2, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS2 /\
     YCbqGwild.wbudget [] kbg' WS2) ->
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall z, inFP FP1 z -> z < YM05.alloc_ceiling /\ in_app z 1 /\
     ~ (F_ lyc pos + 504 <= z < F_ lyc pos + 512)) ->
  sideB ly2 S2 Hp2 W2 mem2 Lamc' peakc' cntc' ownc' ranc' ->
  Permutation Lamc' (Dx' ++ Lam) -> Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks Dx') ->
  (forall bk, In bk Dx' -> ~ In bk D) ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  liveB kbg' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Dx' Lamc' peakc' cntc' ownc' ranc'.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Dx' Lamc'
  peakc' cntc' ownc' ranc' kbg kbg' WS1 HL (WS2 & HJ2 & HB2) HJ1 HFP HSD HPL HPB HAP HMN'.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMN.
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & _ & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ2) as (_ & _ & _ & _ & _ & _ & Ffr2 & Fsh2).
pose proof HJ1 as (_ & HLY1 & _ & _ & _ & _ & _ & _ & KS1 & _ & _ & KF1 & _).
pose proof HLY1 as (_ & _ & _ & _ & _ & EFF & _).
assert (EF : frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos) by (unfold frame_addr; rewrite EFF; reflexivity).
assert (EFl : flag_addr ly2 CRT_CID pos = flag_addr lyc CRT_CID pos) by (unfold flag_addr; rewrite EFF; reflexivity).
rewrite EF in Ffr2, Fsh2.
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (crt3_sp0 HPRE) as (Hal16 & Hsp0c & Hsp047 & Hsp0hi). destruct (crt3_sp1 HPRE) as (Hs32 & Hs1 & Hs10).
pose proof crt3_stk as Hstk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : fs_frame_bytes CRT_CID = 512) by (vm_compute; reflexivity).
assert (KS : forall z, sp1 <= z < 2 ^ 64 -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H Wc) memc z).
{ intros z Hz. apply KS1; lia. }
assert (KF : forall z, (F <= z < F + 512 \/ shadow_addr F <= z < shadow_addr F + 64) -> ~ inFP FP1 z ->
  aview SEGS (w_H W2) mem2 z = aview SEGS (w_H Wc) memc z).
{ intros z Hz Hn. apply (KF1 CRT_CID pos z Hin); [|exact Hn].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfb. change (512 / 8) with 64. fold F. lia. }
assert (KSH : forall z, shadow_addr F <= z < shadow_addr F + 64 ->
  aview SEGS (w_H W2) mem2 z = aview SEGS (w_H Wc) memc z).
{ intros z Hz. apply KF; [right; exact Hz|]. intros Hf. destruct (HFP z Hf) as (H1 & H2 & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *; lia. }
refine {| crt_live_journal := ex_intro _ WS2 (conj HJ2 HB2); crt_live_side := HSD; crt_live_lam_perm := HPL;
          crt_live_blocks_perm := HPB; crt_live_dx_apart := HAP; crt_live_saved := _;
          crt_live_frame := _; crt_live_fspill := _; crt_live_copy_open := _;
          crt_live_copy_hull := _; crt_live_memnorm := _ |}.
- (* crt_live_saved *)
  intros j Hj. apply (crt3s_vm_keep (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact (HSV j Hj)].
  intros y Hy. apply KS. lia.
- (* crt_frame *)
  pose proof (crt_frame_flag_word HFRM) as Hfl.
  refine {| crt_frame_listed := _; crt_frame_flag_word := _; crt_frame_present := _ |}.
  + pose proof HJ2 as (_ & _ & _ & _ & _ & HFR2 & _). rewrite HFR2. left. reflexivity.
  + rewrite EF, EFl, <- Hfl. apply crt3_rdword_keep. intros j Hj. rewrite Hfb. fold F.
    apply KF; [left; lia|]. intros Hf. destruct (HFP _ Hf) as (_ & _ & H3). apply H3. lia.
  + intros z Hz. rewrite EF, Hfb in Hz. fold F in Hz. exact (proj1 (Ffr2 z Hz)).
- (* crt_live_fspill *)
  unfold crt_spill in *. rewrite EF. fold F.
  apply (crt3s_vm_keep (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact HSPF].
  intros y Hy. apply KS. unfold CRT_SP_F in *. lia.
- (* crt_live_copy_open *)
  rewrite EF. fold F. apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HCR].
  intros y Hy. unfold CRT_OFF_COPY in Hy. unfold shadow_of_addr. apply KSH.
  unfold shadow_addr, SHADOW_OFF in *. lia.
- (* crt_live_copy_hull *)
  rewrite EF. fold F. intros s Hs. rewrite KSH; [exact (HCH s Hs)|].
  unfold CRT_OFF_COPY, shadow_addr, SHADOW_OFF in *. lia.
- (* crt_live_memnorm *)
  intros H0. exact (HMN' (HMN H0)).
Qed.

(* ---- a tree read under a new block list that still holds its blocks (Crt102Kit.v crt102rw_mems_lblk /
   crt102rw_nodeR_lblk, image-free, transcribed) ---- *)
Lemma crt3s_mems_lblk : forall m lblk lblk' (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a0 ka D0,
  pj_memsR SEGS m lblk P a0 ka l D0 -> (forall y0 k0, In (y0, k0) D0 -> lblk' y0 k0) ->
  (forall i nm u D1, nth_error l i = Some (nm, u) -> incl D1 D0 -> P (a0 + 56 * Z.of_nat i) u D1 ->
     P' (a0 + 56 * Z.of_nat i) u D1) ->
  pj_memsR SEGS m lblk' P' a0 ka l D0.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a0 ka D0 H HL HP; cbn [pj_memsR] in H |- *;
  [exact H|].
destruct H as (y0 & k & D1 & D2 & -> & Hx & (Hl & Hc) & H1 & H2). exists y0, k, D1, D2. split; [reflexivity|].
split; [exact Hx|]. split; [split; [apply HL; left; reflexivity | exact Hc]|]. split.
- specialize (HP 0%nat nm u D1 eq_refl (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_introl Hy)))).
  replace (a0 + 56 * Z.of_nat 0) with a0 in HP by lia. exact (HP H1).
- apply (IH (a0 + 56) (ka + 8) D2 H2).
  + intros y k' Hy. apply HL. right. apply in_or_app. right. exact Hy.
  + intros i nm' u' D1' Hi Hinc HPi.
    specialize (HP (Datatypes.S i) nm' u' D1' Hi (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_intror (Hinc y Hy))))).
    replace (a0 + 56 * Z.of_nat (Datatypes.S i)) with (a0 + 56 + 56 * Z.of_nat i) in HP by lia. exact (HP HPi).
Qed.
Lemma crt3s_nodeR_lblk : forall tv m lblk lblk' p D0, pj_nodeR SEGS m lblk p tv D0 ->
  (forall y0 k0, In (y0, k0) D0 -> lblk' y0 k0) -> pj_nodeR SEGS m lblk' p tv D0.
Proof.
intros tv. induction tv as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk lblk' p D0 H HL; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & (Hl & Hc) & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. split; [apply HL; subst D0; left; reflexivity | exact Hc].
- destruct Hb as (E2 & E3 & E4 & E5 & k & (Hl & Hc) & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. split; [apply HL; subst D0; left; reflexivity | exact Hc].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hcap | (Hc0 & _)]; [left; exact Hcap | right; split; [exact Hc0|]].
    apply HL. subst D0. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  assert (HDi : forall b, In b Di -> In b D0) by (intros b Hb; subst D0; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR SEGS m lblk) (pj_nodeR SEGS m lblk') items kids Di Hi).
  intros i u D1 Hil Hinc HP. rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 HP).
  intros y0 k0 Hxk. apply HL. apply HDi. apply Hinc. exact Hxk.
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hcap | (Hc0 & _ & _)]; [left; exact Hcap | right; split; [exact Hc0|]].
    split; apply HL; rewrite ED; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; [left; reflexivity | right; left; reflexivity]. }
  assert (HDi : forall b, In b Di -> In b D0) by (intros b Hb; subst D0; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (crt3s_mems_lblk m lblk lblk' (pj_nodeR SEGS m lblk) (pj_nodeR SEGS m lblk') members kids keys Di Hi).
  + intros y0 k0 Hxk. apply HL. apply HDi. exact Hxk.
  + intros i nm u D1 Hil Hinc HP. rewrite Forall_forall in IH.
    specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
    apply (IH m lblk lblk' _ D1 HP). intros y0 k0 Hxk. apply HL. apply HDi. apply Hinc. exact Hxk.
Qed.

(* ---- bytes outside the image that the view keeps are the same bytes, writability included (Crt102Kit.v
   crt102rw_mr_of_aview / crt102rw_agree_of_aview, transcribed) ---- *)
Lemma crt3s_mr_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) z,
  0 <= z < 2 ^ 64 -> ~ in_img SEGS z -> aview SEGS H' m' z = aview SEGS H m z ->
  mrestrict H' m' (Z_to_bv 64 z) = mrestrict H m (Z_to_bv 64 z).
Proof.
intros H H' m m' z Hz Hn E. unfold aview, mbyte in E.
rewrite (seg_rom_none SEGS z Hz Hn) in E.
destruct (mrestrict H' m' (Z_to_bv 64 z)) as [b'|]; destruct (mrestrict H m (Z_to_bv 64 z)) as [b|];
  cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma crt3s_agree_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) (X : Z -> Prop),
  (forall z, X z -> 0 <= z < 2 ^ 64 /\ ~ in_img SEGS z /\ aview SEGS H' m' z = aview SEGS H m z) ->
  pj_agreeR SEGS (mrestrict H m) (mrestrict H' m') X.
Proof.
intros H H' m m' X HX y Hy. destruct (HX y Hy) as (Hr & Hn & E).
pose proof (crt3s_mr_of_aview H H' m m' y Hr Hn E) as Em.
split; [unfold mbyte; rewrite Em; reflexivity|].
intros Hw. unfold writable_at, wview in *. rewrite Em. exact Hw.
Qed.
Lemma crt3s_ro_img : forall z, in_roP SEGS RLO RHI z -> in_img SEGS z.
Proof.
intros z [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA z Hr)].
Qed.

(* ---- two harness blocks with different bases, and a harness block and a fake frame, are apart ---- *)
Lemma crt3s_hblk_disj : forall lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc b k b' k',
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  In (b, k) Lamc -> In (b', k') Lamc -> b <> b' -> b + k <= b' - 16 \/ b' + k' <= b - 16.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc b k b' k' HAR HLG H1 H2 Hne.
destruct (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG H1) as (Hk0 & Hab & _ & _ & Hr).
destruct (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG H2) as (Hk0' & Hab' & _ & _ & Hr').
assert (Hn : (b - 16, k + 16) <> (b' - 16, k' + 16)) by (intros E; injection E as E1 _; lia).
pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HAR Hab Hab' Hn) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hr, Hr' in Hd. lia.
Qed.
Lemma crt3s_hblk_frm : forall lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc b k cid pos',
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  In (b, k) Lamc -> In (cid, pos') (frames Sc) ->
  b + k <= frame_addr lyc cid pos' \/ frame_addr lyc cid pos' + fs_frame_bytes cid <= b - 16.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc b k cid pos' HAR HLG H1 Hf.
destruct (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG H1) as (Hk0 & Hab & _ & _ & Hr).
pose proof (crt3s_blk_frm _ _ _ _ _ _ _ _ _ HAR Hab Hf) as Hd. cbn [fst snd] in Hd. rewrite Hr in Hd. lia.
Qed.

(* ---- THE SIDE FACTS ACROSS A CALL whose footprint lies in the own frame and the blocks Dx the walk holds: the
   read-only view, the document's tree (its header in an entry frame, its blocks among the entry's) ---- *)
Lemma crt3s_side_call : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc
  STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam' peak' cnt' fail' ran' most' own' {kbg : nat} {WS1 : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall z, inFP FP1 z -> (F_ lyc pos <= z < F_ lyc pos + 512) \/ exists b k, In (b, k) Dx /\ b - 16 <= z < b + k) ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam' peak' cnt' fail' ran' most' own' -> (forall bk, In bk Lam -> In bk Lam') ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W2) mem2) /\
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam') doc t D /\ (forall bk, In bk D -> In bk Lam').
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  Lam' peak' cnt' fail' ran' most' own' kbg WS1 HL HJ1 HFP HLED2 HLL.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_arodata HSD) as HROD.
pose proof (crt_side_doc HSD) as HDOC. pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & EFc & _).
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & KB1 & KI1 & KF1 & _).
pose proof HTREE as (_ & HDLam & _ & (Hd8 & (cid & pos' & Hfin & Hfa1 & Hfa2) & _)).
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & HnS & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
assert (Hfb : fs_frame_bytes CRT_CID = 512) by (vm_compute; reflexivity).
assert (EFa : forall c p, frame_addr lyc c p = frame_addr ly c p) by (intros c p; unfold frame_addr; rewrite EFc; reflexivity).
assert (HfinC : In (cid, pos') (frames Sc)) by (rewrite HFRc; right; exact Hfin).
assert (HDx : forall b k, In (b, k) Dx -> In (b, k) Lamc)
  by (intros b k Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
(* the callee's footprint misses the entry's frames and the entry's harness blocks *)
assert (HSNK : ~ YI16.sink_open_fp FP1).
{ intros H0. apply in_fp_inFP in H0. destruct (HFP 0 H0) as [Hz | (b & k & Hb & Hz)]; [lia|].
  destruct (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED (HDx b k Hb)) as (_ & Hab & _).
  destruct (crt3s_blk_bounds _ _ _ _ _ _ _ _ HARc Hab) as (H4096 & _). lia. }
split.
{ intros z Hro Hno Her.
  rewrite (KI1 z (crt3s_ro_img z Hro) Hno Her (fun Hx => crt_pst_ro_B HB_segs HB_relro z Hx Hro)
             (fp_spares_closed (SK := SK) FP1 z HSNK)).
  exact (HROD z Hro Hno Her). }
assert (HDLam' : forall bk, In bk D -> In bk Lam') by (intros bk Hbk; apply HLL; apply HDLam; exact Hbk).
split; [|exact HDLam'].
apply (crt3s_nodeR_lblk t (mrestrict (w_H W2) mem2) (prh_lin Lamc) (prh_lin Lam') doc D);
  [|intros y0 k0 Hy; unfold prh_lin; exact (HDLam' _ Hy)].
apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) doc D HDOC).
apply crt3s_agree_of_aview. intros y [Hy | ((b & k) & Hb & Hy)].
- (* the header, in an entry frame *)
  destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' HARc HfinC) as (G1 & G2 & G3).
  rewrite EFa in G1, G2, G3.
  pose proof asan_consts as (C1 & _).
  split; [lia|]. split.
  { apply (frm_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' y HARc HfinC). rewrite EFa. lia. }
  apply (KF1 cid pos' y HfinC).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa. lia.
  + intros Hf. destruct (HFP y Hf) as [Hz | (b & k & Hb & Hz)].
    * apply in_split in Hfin as (l1 & l2 & El).
      pose proof (sep_frames_pos_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc
        (CRT_CID, pos) (cid, pos') [] l1 l2 HARc ltac:(rewrite HFRc, El; reflexivity)) as Hd.
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite Hfb, !EFa in Hd.
      rewrite EFa in Hz. lia.
    * pose proof (crt3s_hblk_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLED (HDx b k Hb) HfinC) as Hd.
      rewrite EFa in Hd. lia.
- (* a block of the tree, an entry harness block *)
  unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  assert (HbL : In (b, k) Lamc) by exact (HDL _ Hb).
  destruct (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED HbL) as (Hk0 & Hab & _ & _ & Hr).
  destruct (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED2 (HDLam' _ Hb)) as (_ & Hab2 & _).
  destruct (crt3s_blk_bounds _ _ _ _ _ _ _ _ HARc Hab) as (H4096 & Hce & _). rewrite Hr in Hce.
  pose proof asan_consts as (C1 & _).
  split; [lia|]. split.
  { apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc (b - 16) (k + 16) y HARc Hab). rewrite Hr. lia. }
  replace y with (b - 16 + (y - (b - 16))) by lia.
  apply (KB1 (b - 16) (k + 16) (y - (b - 16)) Hab Hab2); [rewrite Hr; lia|].
  replace (b - 16 + (y - (b - 16))) with y by lia.
  intros Hf. destruct (HFP y Hf) as [Hz | (b' & k' & Hb' & Hz)].
  + pose proof (crt3s_hblk_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLED HbL Hin) as Hd.
    rewrite Hfb in Hd. lia.
  + assert (Hne : b' <> b).
    { intros E. apply (crt3s_nodup_apart Lamc Dx Lam (b', k') (b, k) (prh_ledger_nodup B _ _ _ _ _ _ _ _ _ _ _ _ HLED)
        HPL Hb' (HDLam _ Hb) E). }
    pose proof (crt3s_hblk_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLED HbL (HDx b' k' Hb') (fun E => Hne (eq_sym E)))
      as Hd.
    lia.
Qed.

(* ---- +0x284 `seqz s8, a0` (sltiu x24, x10, 1), one concrete step to the cut O1 at +0x288 ---- *)
Lemma crt3s_seqz : forall (fxk : YK11.FPState) (W2 : world SEGS) regs2 mem2 md2 Q,
  (forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg (@YK11.mkst fxk (regupd regs2 24%bv (v_sltiu (getr regs2 10%bv) 1))
      (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_O1_OFF_B))) mem2 (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md2) mat' md2)) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
    (mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_K_OFF_B))) mem2 (YK11.seg_rom SEGS)) md2) Q.
Proof.
intros fxk W2 regs2 mem2 md2 Q HK.
assert (Hpl : plookup (@pl_tpi _ PL_B102) (CRT_PC_B + CRT_K_OFF_B) = Some (PW 0x153c13)) by (vm_compute; reflexivity).
assert (Hdec : exists rd rs imm, decode_any (Z_to_bv 32 0x153c13) = Some (OpImm ALU_SLTU rd rs imm, 4%Z) /\
  rd = 24%bv /\ rs = 10%bv /\ bv_signed imm = 1).
{ let v := eval vm_compute in (decode_any (Z_to_bv 32 0x153c13)) in
  lazymatch v with Some (OpImm ALU_SLTU ?rd ?rs ?imm, _) =>
    exists rd, rs, imm; split; [vm_compute; reflexivity|];
    split; [apply bv_eq; reflexivity|]; split; [apply bv_eq; reflexivity | vm_compute; reflexivity] end. }
destruct Hdec as (rd & rs & imm & Hdec & -> & -> & Himm).
assert (H240 : bv_eqb (24%bv : bv 5) 0 = false) by (vm_compute; reflexivity).
pose proof (pa_lookup_pw (PI := PA) _ _ Hpl) as (Hl & _ & _).
assert (Hraw : 0 <= BASE + (CRT_PC_B + CRT_K_OFF_B) < 2 ^ 31)
  by (rewrite HB_base; split; vm_compute; first [reflexivity | discriminate]).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W2); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fxk)).
  rewrite (step_sltiu (fx := fxk) SEGS regs2 (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_K_OFF_B))) (mrestrict (w_H W2) mem2)
    (YK11.seg_rom SEGS) (Z_to_bv 32 0x153c13) _ _ _ (pa_fetch_ok _ _ Hl)
    (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite H240, Himm. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md2 model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fxk)).
  replace (v_addi (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_K_OFF_B))) 4) with (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_O1_OFF_B))).
  + exact (HK _).
  + unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. unfold CRT_K_OFF_B, CRT_O1_OFF_B. lia.
Qed.

(* ---- the read-back's blocks are below the allocator's request bound: each live size of rtt(doc, 0)'s read-back
   is one of its requests (lsz), at most its largest (RQ_pj_parse of the text = RQ_rtt's third member) ---- *)
Lemma crt3s_db_small : forall (Db : list (Z * Z)),
  Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) ->
  forall b k, In (b, k) Db -> k + 16 < 2 ^ 29 - 2 ^ 20.
Proof.
intros Db HP b k Hin.
assert (Hcm : Crt102Model.cm_in x t) by exact (Crt102Model.cm_in_intro x t HREAD HLENX HWL0 HWL1).
assert (Hk : In k (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t)))).
{ apply (Permutation_in _ HP). exact (in_map snd Db (b, k) Hin). }
apply in_map_iff in Hk as (y & <- & Hy).
pose proof (crt3s_lsz_maxreq _ y Hy) as Hle.
rewrite <- (Crt102Model.cm_ptrace_wf t false (Crt102Model.cm_in_wf x t Hcm)) in Hle.
change (fold_right Z.max 0 (map (fun e => Z.of_nat (PjGrammar.esize e))
  (PRH_FnPj.prhPj_ptrace (WriterValue.wdoc t false)))) with (PRH_FnPj.RQ_pj_parse (WriterValue.wdoc t false)) in Hle.
assert (I1 : PRH_FnPj.RQ_pj_parse (WriterValue.wdoc t false) <= RQ_rtt t false)
  by (unfold RQ_rtt; apply Crt102Model.zmaxl_in; right; right; left; reflexivity).
assert (I2 : RQ_rtt t false <= RQ_crt t) by (unfold RQ_crt; apply Crt102Model.zmaxl_in; left; reflexivity).
(* cf_malloc_max is the of-record blob b60d0f63c926 at this base (2^28 + 2^27); bound it ABOVE by the statement's
   literal rather than equate it, so a future cf_malloc_max change does not reopen this (at the base e2c0399f04d9) *)
assert (Hmm : @cf_malloc_max CfParams_preset <= 2 ^ 29 - 2 ^ 20) by (vm_compute; discriminate).
assert (Hh : @cf_head CfParams_preset = 16) by reflexivity.
rewrite Hh in HRQ. lia.
Qed.

(* ---- the memory-free facts of the writer's tree visibility for a harness block of the ledger, given its size is
   below 2 ^ 32 (crt3_tree_vis_keep's per-block premise; YGcfTreeVis.v tree_vis_of_blocks_cf's arithmetic) ---- *)
Lemma crt3s_tv_facts : forall ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 b k,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  In (b, k) Lam2 -> k < 2 ^ 32 ->
  4096 <= b /\ 0 <= k < 2 ^ 32 /\ (b + k + 7) / 8 * 8 <= YM05.alloc_ceiling /\ amem_range b ((b + k + 7) / 8 * 8 - b).
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 b k HAR HLG Hin Hk.
destruct (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG Hin) as (Hk0 & Hab & _ & _ & Hr).
destruct (crt3s_blk_bounds _ _ _ _ _ _ _ _ HAR Hab) as (H4096 & Hce & Happ & _). rewrite Hr in Hce, Happ.
pose proof YM05.alloc_ceiling_val as CR.
assert (G : (b + k + 7) / 8 * 8 <= YM05.alloc_ceiling) by (apply tv_gran_le; [lia | exact (proj2 CR)]).
split; [lia|]. split; [lia|]. split; [exact G|].
unfold amem_range. unfold in_app in Happ. destruct Happ as [_ [BL | [BH1 BH2]]].
- assert (G' : (b + k + 7) / 8 * 8 <= kLowShadowBeg) by (apply tv_gran_le; [lia | unfold kLowShadowBeg; reflexivity]).
  left. unfold kLowMemEnd, kLowShadowBeg in *. lia.
- right. unfold kHighMemEnd, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* the live state at a materialised model (only the journal reads the model): YCbqG.ajournal_x_materializeR is over
   ajournal_xR, so the journal is rebased to the current depot (YCbqGwild.ajournal_xw_rebaseR) and stepped back to its
   budget after it (YCbqGwild.ajournal_xw_unbase0R, from its wild clause Crt102Kit.crt_jw_wild) *)
Lemma crt3s_live_mat : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc X {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  liveB kbg lyc Sc Hpc Wc memc (with_vm_backing (m_vm_lazy mdc) X mdc) kj pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc X kbg H.
destruct (crt_live_journal H) as (WS & HJ & HB).
refine {| crt_live_journal := ex_intro _ WS (conj _ HB); crt_live_side := crt_live_side H;
          crt_live_lam_perm := crt_live_lam_perm H; crt_live_blocks_perm := crt_live_blocks_perm H;
          crt_live_dx_apart := crt_live_dx_apart H; crt_live_saved := crt_live_saved H;
          crt_live_frame := crt_live_frame H; crt_live_fspill := crt_live_fspill H;
          crt_live_copy_open := crt_live_copy_open H; crt_live_copy_hull := crt_live_copy_hull H;
          crt_live_memnorm := crt_live_memnorm H |}.
pose proof (Crt102Kit.crt_jw_wild B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
eapply YCbqGwild.ajournal_xw_unbase0R; [|exact Hinc].
exact (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)
  (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X HJr).
Qed.

(* the ledger list after pj_set: what it held beside the two trees is the entry's *)
Lemma crt3s_lam_post : forall (Lamc Lam' Db Dw Do Lr L0 : list (Z * Z)) e,
  Dw = [e] -> Permutation Lamc ((e :: Db) ++ L0) -> Permutation Lamc (Db ++ Dw ++ Lr) ->
  Permutation Lam' (Do ++ Lr) -> Permutation Lam' (Do ++ L0).
Proof.
intros Lamc Lam' Db Dw Do Lr L0 e -> H1 H2 H3.
assert (Hr : Permutation Lr L0).
{ apply (Permutation_app_inv_l (Db ++ [e])). rewrite <- !app_assoc.
  apply (Permutation_trans (Permutation_sym H2)). apply (Permutation_trans H1).
  cbn [app]. apply Permutation_middle. }
apply (Permutation_trans H3). apply Permutation_app_head. exact Hr.
Qed.

(* ---- what the callee's journal from sp1 keeps for the O1 boundary: a spill above sp1, and a range of the own
   frame whose shadow lies outside the callee's footprint ---- *)
Lemma crt3s_spill_keep : forall STK1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 off v {WS1 : list (list Z)},
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 -> 0 <= off <= 512 ->
  spillB Wc memc off v -> spillB W2 mem2 off v.
Proof.
intros STK1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 off v WS1 HJ1 Ho Hs.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & KS1 & _).
destruct (crt3_sp0 HPRE) as (Hal16 & Hsp0c & Hsp047 & Hsp0hi). destruct (crt3_sp1 HPRE) as (Hs32 & Hs1 & Hs10).
pose proof crt3_stk as Hstk. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold crt_spill in *. apply (crt3s_vm_keep (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact Hs].
intros y Hy. apply KS1; lia.
Qed.
Lemma crt3s_ra_frame : forall lyc Sc Hpc Wc memc mdc kj pos STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 off
    {WS WS1 : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS ->
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall z, inFP FP1 z -> in_app z 1) -> 0 <= off -> off + 56 <= 512 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F_ lyc pos + off) 56 ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (F_ ly2 pos + off) 56.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 off WS WS1 HJ HJ1 HFP Ho1 Ho2 HRA.
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & _ & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof HJ1 as (_ & HLY1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & KF1 & _).
pose proof HLY1 as (_ & _ & _ & _ & _ & EFF & _).
assert (EF : frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos) by (unfold frame_addr; rewrite EFF; reflexivity).
assert (Hfb : fs_frame_bytes CRT_CID = 512) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite EF. set (F := frame_addr lyc CRT_CID pos) in *.
apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRA].
intros y Hy. unfold shadow_of_addr. apply (KF1 CRT_CID pos _ Hin).
- right. unfold in_zr. cbn [fst snd]. rewrite Hfb. change (512 / 8) with 64. fold F.
  unfold shadow_addr, SHADOW_OFF in *. lia.
- intros Hf. specialize (HFP _ Hf). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *.
  lia.
Qed.

(* ---- `seqz s8, a0` on pj_set's two results ---- *)
Lemma crt3s_seqz_val : forall (r : word) res, r = w64 res -> (res = 0 \/ res = -1) ->
  v_sltiu r 1 = w64 (if res =? 0 then 1 else 0).
Proof. intros r res -> [-> | ->]; vm_compute; reflexivity. Qed.

(* ---- the copy's block sums, and g_count at O1 ---- *)
Lemma crt3s_bsum_nonneg : forall D0, (forall b k, In (b, k) D0 -> 0 <= k) -> 0 <= YCbq.bsum (ck_hblks D0).
Proof.
intros D0 H. rewrite Crt102Model.cm_bsum_hblks.
assert (0 <= Ledger.lsum D0).
{ clear -H. induction D0 as [|[b k] D0 IH]; cbn [Ledger.lsum]; [lia|].
  pose proof (H b k (or_introl eq_refl)).
  assert (0 <= Ledger.lsum D0) by (apply IH; intros b' k' Hi; exact (H b' k' (or_intror Hi))). lia. }
change (@cf_head CfParams_preset) with 16. lia.
Qed.
Lemma crt3s_cnt_range : forall ms cnt0 c0, t = PjTree.JObj ms -> 0 <= c0 ->
  cnt0 <= ck_cnt2 cnt0 t + 1 + c0 <= cnt0 + ck_crt_count t c0.
Proof.
intros ms cnt0 c0 Et Hc. rewrite Crt102Model.cm_cnt2_eq. rewrite Et. unfold ck_crt_count.
pose proof (Crt102Model.cm_wcalls_nonneg (PjTree.JObj ms) false).
pose proof (Crt102Model.cm_wcalls_nonneg (PjTree.JObj ms) true).
pose proof (Crt102Model.cm_tcalls_nonneg (PjTree.JObj ms)).
pose proof (Crt102Model.cm_wcalls_nonneg (ck_crt_tree (PjTree.JObj ms)) true).
pose proof (Crt102Model.cm_tcalls_nonneg (ck_crt_tree (PjTree.JObj ms))). lia.
Qed.
Lemma crt3s_cw : forall c0, crt_cw (t := t) (cnt := cnt) c0 = ck_cnt2 cnt t + 1 + c0.
Proof. intros c0. unfold crt_cw. rewrite Crt102Model.cm_cnt2_eq. lia. Qed.

(* ---- the callee-saved registers across the call (aregs_preserved, read at a bv register) ---- *)
Definition crt3s_csb (r : Z) : bool :=
  (r =? 2) || (r =? 3) || (r =? 4) || (r =? 8) || (r =? 9) || ((18 <=? r) && (r <=? 27)).
Lemma crt3s_pres : forall (rg1 rg2 : bvmap 5 word) (r : bv 5), aregs_preserved rg1 rg2 ->
  crt3s_csb (bv_unsigned r) = true -> getr rg2 r = getr rg1 r.
Proof.
intros rg1 rg2 r H Hc. rewrite <- (Z_to_bv_bv_unsigned _ r). apply H. unfold acallee_saved, crt3s_csb in *.
rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.eqb_eq, !Z.leb_le in Hc. lia.
Qed.

(* ---- copy's blocks after the rewrite UP TO PERMUTATION, and the tree's depth (Base's crt3_copy_tblk), from
   tpj_set_specX's block conclusion on its two granted arms (PRH_FnPj dc0d0aa79c0f:825-845, the permutation form at
   this base). The arms' premises at check_round_trip's arguments: cf_head = HEAD (crt3_head_model); val's block
   (a, 21) is tblk (JStr STAMP) = [37]; the key has no special character (|flat_map ech MOD_AT| = |MOD_AT|) - all
   three by vm_compute. crt_tree_J of JObj ms is copy_set ms = JObj (pj_set_model ms MOD_KEY (JStr MOD_VAL)), the
   text's tree at ck_MOD_AT / ck_STAMP (crt3_modat_model / crt3_stamp_model); its depth is below DOC_D
   (Crt102Model.cm_crt_depth_doc). ---- *)
Lemma crt3s_stamp_tblk : forall a0 : Z,
  Permutation (map (fun b : Z * Z => snd b + cf_head) [(a0, Z.of_nat (length ck_STAMP) + 1)])
    (PresetReqAtNoMiss.tblk (PjTree.JStr ck_STAMP)).
Proof.
intros a0.
replace (map (fun b : Z * Z => snd b + cf_head) [(a0, Z.of_nat (length ck_STAMP) + 1)])
  with (PresetReqAtNoMiss.tblk (PjTree.JStr ck_STAMP)) by (vm_compute; reflexivity).
apply Permutation_refl.
Qed.
Lemma crt3s_modat_ech : length (flat_map PjRoundTrip.ech ck_MOD_AT) = length ck_MOD_AT.
Proof. vm_compute. reflexivity. Qed.

Lemma crt3s_copy_tblk : forall ms (Dc : list (Z * Z)), t = PjTree.JObj ms ->
  Permutation (map (fun b => snd b + cf_head) Dc)
    (PresetReqAtNoMiss.tblk (PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))) ->
  crt3_copy_tblk (t := t) Dc.
Proof.
intros ms Dc Et HT.
assert (EJ : crt_tree_J (t := t) = PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))
  by (unfold crt_tree_J, PresetReqAt.copy_set; rewrite Et, crt3_stamp_model, crt3_modat_model; reflexivity).
unfold crt3_copy_tblk. rewrite EJ. split; [exact HT|].
pose proof (Crt102Model.cm_crt_depth_doc t (Crt102Model.cm_in_depth x t (Crt102Model.cm_in_intro x t HREAD HLENX HWL0 HWL1)))
  as Hd.
rewrite Et in Hd. exact Hd.
Qed.

(* ---- g_ran_out after a call whose allocations were all granted: prh_oks' refusal disjunct needs a failed outcome,
   so ran' = ran (the granted arms of pj_set: c = 0 on the present key, every outcome true on the appended one) ---- *)
Lemma crt3s_oks_granted : forall ok cnt0 fail0 c ns most0 ran0 ran1,
  prh_oks ok cnt0 fail0 c ns most0 ran0 ran1 -> (forall i, (i < c)%nat -> nth i ok true = true) -> ran1 = ran0.
Proof.
intros ok cnt0 fail0 c ns most0 ran0 ran1 (_ & [E | (_ & i & Hi & Hr & _)] & _) Hall; [exact E|].
unfold prh_refused in Hr. rewrite (Hall i Hi) in Hr. discriminate Hr.
Qed.

(* ---- val's ordered free list (FREEORD-COPY's premise on val): v is pj_string's node, ONE block (a, 21), and
   21 + HEAD = 37 = tblk (JStr STAMP), so PRH_PjOrder.pj_free_fo gives its order list with fo's request ---- *)
Lemma crt3s_stamp_fo : forall (Wc : world SEGS) (memc : word -> option byte) (Lamc : list (Z * Z)) (w a0 : Z),
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) w (PjTree.JStr ck_STAMP)
    [(a0, Z.of_nat (length ck_STAMP) + 1)] ->
  forall nv, (PjTree.depth (PjTree.JStr ck_STAMP) <= nv)%nat ->
  exists Fw, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) nv w
      [(a0, Z.of_nat (length ck_STAMP) + 1)] Fw /\
    map (fun b => snd b + cf_head) Fw = PresetReqAt.fo (PjTree.JStr ck_STAMP).
Proof.
intros Wc memc Lamc w a0 HN nv Hnv. rewrite crt3_head_model.
apply (PRH_PjOrder.pj_free_fo SEGS _ _ _ _ _ HN); [|exact Hnv].
replace (map (fun b : Z * Z => snd b + PresetReqAt.HEAD) [(a0, Z.of_nat (length ck_STAMP) + 1)])
  with (PresetReqAtNoMiss.tblk (PjTree.JStr ck_STAMP)) by (vm_compute; reflexivity).
reflexivity.
Qed.

(* ---- copy's ORDERED free list after the rewrite (Base's crt3_copy_fo, = crt_at_W_B_copy_fo's text), from
   tpj_set_specX's FREEORD-COPY conclusion on a granted arm, at nn := DOC_D: crt_tree_J of JObj ms is
   copy_set ms = JObj (pj_set_model ms MOD_KEY (JStr MOD_VAL)) = the text's result tree at ck_MOD_AT / ck_STAMP
   (crt3_modat_model / crt3_stamp_model), of depth <= DOC_D (Crt102Model.cm_crt_depth_doc) ---- *)
Lemma crt3s_copy_fo : forall ms (W2 : world SEGS) (mem2 : word -> option byte) (Lam2 : list (Z * Z)) (p : Z)
  (Dc : list (Z * Z)), t = PjTree.JObj ms ->
  (forall nn, (PjTree.depth (PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP))) <= nn)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) nn p Dc F /\
       map (fun b => snd b + cf_head) F =
         PresetReqAt.fo (PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))) ->
  crt3_copy_fo (t := t) W2 mem2 Lam2 p Dc.
Proof.
intros ms W2 mem2 Lam2 p Dc Et HF.
assert (EJ : crt_tree_J (t := t) = PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))
  by (unfold crt_tree_J, PresetReqAt.copy_set; rewrite Et, crt3_stamp_model, crt3_modat_model; reflexivity).
pose proof (Crt102Model.cm_crt_depth_doc t (Crt102Model.cm_in_depth x t (Crt102Model.cm_in_intro x t HREAD HLENX HWL0 HWL1)))
  as Hd.
rewrite Et in Hd. cbn [ck_crt_tree] in Hd.
destruct (HF DOC_D Hd) as (Fc & HFo & HFm).
unfold crt3_copy_fo. exists Fc. split; [exact HFo|]. rewrite EJ. exact HFm.
Qed.

(* the callee-saved registers the walk keeps *)
Definition crt3s_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Ltac crt3s_inK := unfold crt3s_KEPT; cbn [In]; repeat (first [left; reflexivity | right]).

(* ---- THE CALL (+0x280 jal pj_set): the walk at pj_set's entry, a0 = &copy, a1 = MOD_AT, a2 = &v, ra = +0x284 ---- *)
Lemma crt3s_call : forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms a (rgc : bvmap 5 word),
  STMT_O1 ->
  atS fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms a ->
  getr rgc 10 = w64 (F_ lyc pos + CRT_OFF_COPY) -> getr rgc 11 = w64 (CRT_MOD_AT_B (PA := PA)) ->
  getr rgc 12 = w64 (F_ lyc pos + CRT_OFF_V) ->
  getr rgc 1 = Z_to_bv 64 (BASE + (CRT_PC_B + CRT_K_OFF_B)) ->
  (forall r : bv 5, In r crt3s_KEPT -> getr rgc r = getr rg r) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
    (mkCfg (@YK11.mkst fxk rgc (Z_to_bv 64 (SIGMA AS_pj_set)) memc (YK11.seg_rom SEGS)) mdc) QFb.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms a rgc HO1 HAT Q10 Q11 Q12 Q1 QK.
(* crt_at_S3 ends in FIVE conjuncts - copy's blocks up to permutation, copy's header cap (cited from crt_at_U_B, which
   is what pj_set's `cap` argument needs), the room position, and copy's ORDERED free list (crt3_copy_fo0, which is
   tpj_set_specX's ordered entry premise verbatim). *)
pose proof HAT as (Et & Hfz & Hfk & HLV & HDR & H21 & HSP1 & HSP2 & HSP3 & HTOK & HRAB & HRAV & HCOPY & HVN & HDX
  & HPMS & HLEN & ECNT & HTBLK & HCAPC & HPOS & HFO0).
destruct (crt_live_journal HLV) as (WSj & HJ & HBj). pose proof (crt_live_side HLV) as HSD.
pose proof (crt_live_lam_perm HLV) as HPL. pose proof (crt_live_blocks_perm HLV) as HPB.
pose proof (crt_live_dx_apart HLV) as HAP. pose proof (crt_live_saved HLV) as HSV.
pose proof (crt_live_frame HLV) as HFRM. pose proof (crt_live_fspill HLV) as HSPF.
pose proof (crt_live_copy_open HLV) as HCR. pose proof (crt_live_copy_hull HLV) as HCH.
pose proof (crt_live_memnorm HLV) as HMN.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK.
pose proof (crt_side_room HSD) as HRL. pose proof (crt_side_arodata HSD) as HROD.
pose proof (crt_side_doc HSD) as HDOC. pose proof (crt_side_doc_blocks HSD) as HDL.
(* the room position: the text is called at the model index i that S carries, its events pj_set's own list *)
destruct (crt3_pos_adv (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (t := t)
  Sc (tl (PresetReqAt.set_evs ms)) (crt_evs_W (rp_sm := rp_sm) ms) HPOS)
  as (pi & phist & Hstrtod & Hpos & Hrun & Hcons & Hclose).
pose proof (crt_dregs_B_bregs HDR) as HBR. pose proof (crt_dregs_B_s6 HDR) as R22.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3.
pose proof (crt_bregs_B_tp HBR) as R4. pose proof (crt_bregs_B_s0 HBR) as R8.
pose proof (crt_bregs_B_s1 HBR) as R9. pose proof (crt_bregs_B_s2 HBR) as R18.
pose proof (crt_bregs_B_s4 HBR) as R20. pose proof (crt_bregs_B_s3 HBR) as R19.
pose proof (crt_bregs_B_s7 HBR) as R23. pose proof (crt_bregs_B_s9 HBR) as R25.
pose proof (crt_bregs_B_s11 HBR) as R27.
pose proof HPRE as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & HROD0 & Hhi0 & Hrac0).
pose proof HJ as (HARc & HLYc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & EFc & _ & _ & Etop & Eslo & Eshi & _).
destruct (crt3_sp0 HPRE) as (Hal16 & Hsp0c & Hsp047 & Hsp0hi).
destruct (crt3_sp1 HPRE) as (Hs32 & Hs1 & Hs10).
pose proof crt3_stk as HstkC.
destruct (crt3_chain HPRE _ _ _ _ _ _ _ _ HJ HSV) as (ch1 & Hch1 & _).
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & HnS & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof YM05.alloc_ceiling_lt as Hc47.
assert (Hfb : fs_frame_bytes CRT_CID = 512) by (vm_compute; reflexivity).
assert (Hcm : Crt102Model.cm_in x t) by exact (Crt102Model.cm_in_intro x t HREAD HLENX HWL0 HWL1).
set (F := F_ lyc pos) in *.
set (Dw := [(a, Z.of_nat (length ck_STAMP) + 1)]) in *.
set (FP1 := (F + CRT_OFF_COPY, F + CRT_OFF_COPY + 56) :: (F + CRT_OFF_V, F + CRT_OFF_V + 56) ::
  ablocks_fp (PRH_FnPj.prhPj_hbl (Db ++ Dw))).
assert (HDx : forall b k, In (b, k) ((a, Z.of_nat (length ck_STAMP) + 1) :: Db) -> In (b, k) Lamc)
  by (intros b k Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
assert (HDbDw : forall b k, In (b, k) (Db ++ Dw) -> In (b, k) ((a, Z.of_nat (length ck_STAMP) + 1) :: Db)).
{ intros b k Hb. apply in_app_or in Hb as [Hb | Hb]; [right; exact Hb|]. left. destruct Hb as [Hb | []]. exact Hb. }
assert (HCOPY' : pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (F + CRT_OFF_COPY) (PjTree.JObj ms) Db)
  by (unfold crt_copy_tree in HCOPY; rewrite Et in HCOPY; exact HCOPY).
pose proof HCOPY' as HC'. cbn [pj_nodeR] in HC'.
destruct HC' as (Hnd & Hap & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
assert (Enm : n = ck_members t) by (rewrite Et; exact En).
(* the text's event premises: copy's blocks carry the writer's sizes UP TO PERMUTATION (HTB), and pj_set's own list
   at the header's n and cap. THE CAP IS CITED, not re-derived: it is crt_at_U_B's own conjunct, which S carries as
   crt3_cap (Crt102Model.cm_cap_of_tblk still asks the ORDERED block list, which no instance has at this base, and
   the glue records the row holder's counterexample showing the permutation does not fix cap). *)
assert (HTB : Permutation (map (fun b => snd b + cf_head) Db) (PresetReqAtNoMiss.tblk (PjTree.JObj ms)))
  by (unfold crt3_tblk in HTBLK; rewrite <- Et; exact HTBLK).
assert (Ecap : cap = Z.of_nat (PresetReqAt.ncap (length ms)))
  by exact (HCAPC _ num str kids keys n cap Hh).
assert (Eevs : PRH_FnPj.prhPj_set_evs ms ck_MOD_AT n cap = tl (PresetReqAt.set_evs ms))
  by (rewrite crt3_set_evs_tl, En, Ecap, crt3_modat_model; reflexivity).
(* the text's run, position and consumer window are over the reader's strtod model (no rp_sm binder): crt_pos carries
   rp_sm = ReaderRes.jr_strtod (Hstrtod), and the call's window is the head of S's window (prh_cons_from_app_iff) *)
assert (Hrun' : prh_run_at ReaderRes.jr_strtod rp_x rp_os pi (PRH_FnPj.prhPj_set_evs ms ck_MOD_AT n cap))
  by (rewrite Eevs, <- Hstrtod; exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) Hrun))).
assert (Hcons' : prh_cons_from ReaderRes.jr_strtod rp_x rp_os pi (length (PRH_FnPj.prhPj_set_evs ms ck_MOD_AT n cap))).
{ rewrite Eevs, <- Hstrtod. rewrite length_app in Hcons.
  exact (proj1 (proj1 (prh_cons_from_app_iff _ _ _ _ _ _) Hcons)). }
assert (Hpos0 : PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os pi rp_H0 phist Sc)
  by (rewrite <- Hstrtod; exact Hpos).
assert (Esp : spZ rgc = sp1).
{ unfold spZ. rewrite (QK 2%bv ltac:(crt3s_inK)), R2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Es0 : s0Z rgc = sp0).
{ unfold s0Z. rewrite (QK 8%bv ltac:(crt3s_inK)), R8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hraw : 4096 <= BASE + (CRT_PC_B + CRT_K_OFF_B) < 2 ^ 31)
  by (rewrite HB_base; split; vm_compute; first [reflexivity | discriminate]).
(* the key's bytes and the two locals' footprints: image bytes against the frame and the harness blocks *)
assert (HKimg : forall z, CRT_MOD_AT_B (PA := PA) <= z < CRT_MOD_AT_B (PA := PA) + Z.of_nat (length ck_MOD_AT) + 1 ->
  in_img SEGS z).
{ intros z Hz. destruct HKMOD as (_ & _ & Hk). destruct (Hk z ltac:(lia)) as (Hro & _). exact (crt3s_ro_img z Hro). }
assert (Hfoot_img : forall off D0 z, 0 <= off -> off + 56 <= 512 ->
  (forall bk, In bk D0 -> In bk Lamc) -> in_img SEGS z -> ~ pj_footR (F + off) D0 z).
{ intros off D0 z Ho1 Ho2 HD0 Hz [Hf | ((b & k) & Hb & Hf)].
  - apply (frm_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos z HARc Hin); [rewrite Hfb; lia | exact Hz].
  - unfold pj_holdsR in Hf. cbn [fst snd] in Hf.
    destruct (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED (HD0 _ Hb)) as (_ & Hab & _ & _ & Hr).
    apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc (b - 16) (k + 16) z HARc Hab); [rewrite Hr; lia | exact Hz]. }
(* g_count at the call: cnt + 3 below SIZE_MAX (Crt102Model's count bound) *)
assert (Hcnt3 : cntc + 3 < 2 ^ 64 - 1).
{ rewrite ECNT, Crt102Model.cm_cnt2_eq. pose proof (Crt102Model.cm_in_count x t 0 Hcm ltac:(lia)) as Hk.
  pose proof (Crt102Model.cm_pre2 t 0 ltac:(lia)). lia. }
(* the callee's footprint: copy and v in the own frame, the blocks the walk holds beyond the entry's *)
assert (HFPa : forall z, inFP FP1 z -> z < YM05.alloc_ceiling /\ in_app z 1 /\ ~ (F + 504 <= z < F + 512)).
{ intros z Hz. apply crt3s_fp1_inv in Hz as [Hz | [Hz | (b & k & Hb & Hz)]].
  - unfold CRT_OFF_COPY in Hz. split; [lia|]. split; [apply (in_app_sub F 512 z 1 Fb3); lia | lia].
  - unfold CRT_OFF_V in Hz. split; [lia|]. split; [apply (in_app_sub F 512 z 1 Fb3); lia | lia].
  - pose proof (HDbDw b k Hb) as Hb'.
    destruct (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED (HDx b k Hb')) as (Hk0 & Hab & _ & _ & Hr).
    destruct (crt3s_blk_bounds _ _ _ _ _ _ _ _ HARc Hab) as (H4096 & Hce & Happ & _). rewrite Hr in Hce, Happ.
    pose proof (crt3s_hblk_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLED (HDx b k Hb') Hin) as Hd. rewrite Hfb in Hd.
    rewrite Hr in Hz.
    split; [lia|]. split; [apply (in_app_sub (b - 16) (k + 16) z 1 Happ); lia | lia]. }
assert (HFPb : forall z, inFP FP1 z -> (F <= z < F + 512) \/
  exists b k, In (b, k) ((a, Z.of_nat (length ck_STAMP) + 1) :: Db) /\ b - 16 <= z < b + k).
{ intros z Hz. apply crt3s_fp1_inv in Hz as [Hz | [Hz | (b & k & Hb & Hz)]].
  - left. unfold CRT_OFF_COPY in Hz. lia.
  - left. unfold CRT_OFF_V in Hz. lia.
  - right. pose proof (HDbDw b k Hb) as Hb'.
    destruct (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED (HDx b k Hb')) as (_ & _ & _ & _ & Hr).
    exists b, k. split; [exact Hb'|]. rewrite Hr in Hz. lia. }
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ (* pj_set has no wild site: the budgeted call rule at its empty budget, P := (fun WS1 => WS1 = []), over
     R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (the text's own SRr' and fpostWmR at wle'), the callee's post by
     YCbqGwild.fpostW_xb_of_xR; the caller's journal stays at its budget WSj *)
  eapply (YCbqGwild.aj_call_xWbR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)
    (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf)
    (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc rgc memc
    (SIGMA AS_pj_set) STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc mdc kj WSj (@STK_pj_set prh_img_B DOC_D)
    0 FP1 (sp1 - sp0) (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_K_OFF_B))) ch1 (fun WS1 => WS1 = [])).
  - exact HJ.
  - rewrite Esp. lia.
  - exact (proj1 (crt_sp1_off sp0 Hal16)).
  - lia.
  - exact (proj1 (proj2 (proj2 (proj2 crt_stk_nonneg_B)))).
  - pose proof crt_stk_B as (_ & _ & _ & _ & _ & HS6 & _). rewrite crt3_pi_frame in HS6. lia.
  - lia.
  - reflexivity.
  - lia.
  - rewrite (QK 3%bv ltac:(crt3s_inK)), R3. exact Hgp0.
  - rewrite (QK 4%bv ltac:(crt3s_inK)), R4. exact Htp0.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [split; vm_compute; first [reflexivity | discriminate] | vm_compute; reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - rewrite Es0. replace (sp0 + (sp1 - sp0)) with sp1 by lia. exact Hch1.
  - intros HP1 HW1.
    pose proof HP1 as (_ & _ & _ & _ & _ & (Hal1 & Hst1 & Hcl1 & Hsl1 & _) & _).
    assert (HSLOT : forall off, 32 <= off -> off + 56 <= 448 -> off mod 8 = 0 ->
      range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F + off) 56 ->
      shadow_hull_vis (aview SEGS (w_H Wc) memc) (F + off) 56 ->
      PRH_FnPj.prhPj_slot B (@STK_pj_set prh_img_B DOC_D) 0 lyc Sc Lamc Wc rgc memc (F + off)).
    { intros off Ho1 Ho2 Ho8 HRA HHU.
      split; [lia|].
      split; [right; right; left; exists CRT_CID, pos; split; [exact Hin | rewrite Hfb; lia]|].
      split; [split; [lia | intros z Hz; apply (apresent_writable SEGS); apply (proj1 (Ffr z ltac:(lia)))]|].
      split; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fb3; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
      split; [intros z Hz; split; [exact (proj2 (Ffr z ltac:(lia))) | rewrite Esp in *; lia]|].
      split; [exact HRA | exact HHU]. }
    eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
    (* pj family: entry-keyed event form; no rp_sm binder (HP_sm: the text is over ReaderRes.jr_strtod); the
       run's length bound HOS4 (the text's DRAFT premise) *)
    { refine (HPJSET fxk rp_x rp_os pi rp_H0 phist most 0 lyc Sc Hpc Wc rgc memc mdc ch1 0 (F + CRT_OFF_COPY)
        (CRT_MOD_AT_B (PA := PA)) (F + CRT_OFF_V) ms (PjTree.JStr ck_STAMP) Db Dw num str kids keys n cap ck_MOD_AT
        Lamc peakc cntc SIZE_MAXZ 0 _ HUNIV HRL Hpos0 HOS4 Hcons' Q10 Q11 Q12 HW1 HCOPY' Hh _ _ HVN _ _ _ _ _ _ _ _ _ _ HLED
        _ _ _ _ HTB HFO0 crt3_head_model Hrun').
      - (* fpre (its fifth conjunct, FRM0-ENTRY: the rounding mode at S is 0) *)
        split; [exact HP1|]. split; [exact HROD|]. split; [rewrite Esp, Eshi; lia|].
        split; [unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia | exact Hfz].
      - (* cap *)
        destruct Hcap as [(-> & _) | (Hc0 & Hk1 & _)]; [lia|]. unfold prh_lin in Hk1.
        destruct (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED Hk1) as (_ & Hab & _ & _ & Hr).
        destruct (crt3s_blk_bounds _ _ _ _ _ _ _ _ HARc Hab) as (H4096 & Hce & _). rewrite Hr in Hce. lia.
      - (* copy's slot *)
        apply HSLOT; [unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | exact HCR | exact HCH].
      - (* v's slot *)
        apply HSLOT; [unfold CRT_OFF_V; lia | unfold CRT_OFF_V; lia | unfold CRT_OFF_V; lia | exact HRAV|].
        apply crt3s_hull_frame; [exact F32 | unfold CRT_OFF_V; lia | lia | unfold CRT_OFF_V; lia | lia|].
        intros i0 Hi0. apply (aview_some_of_apresent SEGS). exact (proj1 (Fsh i0 Hi0)).
      - unfold CRT_OFF_V. lia.
      - (* v's block is not copy's *)
        intros bk [<- | []] Hbk.
        exact (crt3s_nodup_apart Lamc [(a, Z.of_nat (length ck_STAMP) + 1)] (Db ++ Lam) _ _
          (prh_ledger_nodup B _ _ _ _ _ _ _ _ _ _ _ _ HLED) HPL (or_introl eq_refl) (in_or_app _ _ _ (or_introl Hbk)) eq_refl).
      - (* v's bytes miss copy's footprint *)
        intros z Hz [Hf | ((b & k) & Hb & Hf)]; [unfold CRT_OFF_V, CRT_OFF_COPY in *; lia|].
        unfold pj_holdsR in Hf. cbn [fst snd] in Hf.
        pose proof (crt3s_hblk_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLED (HDx b k (or_intror Hb)) Hin) as Hd.
        rewrite Hfb in Hd. unfold CRT_OFF_V in Hz. lia.
      - (* v's block misses copy's node *)
        intros bk z [<- | []] Hz Hz'. unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
        pose proof (crt3s_hblk_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLED (HDx _ _ (or_introl eq_refl)) Hin) as Hd.
        rewrite Hfb in Hd. unfold CRT_OFF_COPY in Hz'. lia.
      - rewrite <- Et. pose proof (Crt102Model.cm_in_depth_doc x t Hcm). lia.
      - cbn [PjTree.depth]. lia.
      - exact (crt3s_cstr_mod lyc Sc Hpc Wc memc mdc HARc HROD).
      - right; right. exact HKMOD.
      - intros z Hz. split.
        + apply (Hfoot_img CRT_OFF_COPY Db z); [unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | |exact (HKimg z Hz)].
          intros bk Hbk. destruct bk as (b & k). apply HDx. right. exact Hbk.
        + apply (Hfoot_img CRT_OFF_V Dw z); [unfold CRT_OFF_V; lia | unfold CRT_OFF_V; lia | |exact (HKimg z Hz)].
          intros bk [<- | []]. apply HDx. left. reflexivity.
      - exact Hcnt3.
      - exact (Crt102Model.cm_rq_key t HRQ).
      - intros Encap. exact (Crt102Model.cm_rq_grow t HRQ n cap Enm Encap).
      - apply (Crt102Model.cm_live_set t (blocks_bytes S) (blocks_bytes Sc) HLIVE); [|exact Enm].
        rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPB), crt3s_bsum_app.
        change ((a, Z.of_nat (length ck_STAMP) + 1) :: Db) with ([(a, Z.of_nat (length ck_STAMP) + 1)] ++ Db).
        rewrite Crt102Model.cm_bsum_hblks_app, (Crt102Model.cm_stamp_block a).
        pose proof (Crt102Model.cm_copy_room_rtt t Db (Crt102Model.cm_in_wf x t Hcm) HPMS HLEN).
        pose proof (Crt102Model.cm_LIVE_rtt_nonneg t true). lia. }
    intros W' c' _ HPOST. apply YCbqGwild.fpostW_xb_of_xR; [reflexivity | exact HPOST].
  - (* the callee's footprint: the own frame, or a block made after the entry *)
    intros z Hz. apply crt3s_fp1_inv in Hz as [Hz | [Hz | (b & k & Hb & Hz)]].
    + right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfb. unfold CRT_OFF_COPY in Hz. lia.
    + right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfb. unfold CRT_OFF_V in Hz. lia.
    + right; left. pose proof (HDbDw b k Hb) as Hb'.
      destruct (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED (HDx b k Hb')) as (_ & Hab & _).
      exists (b - 16), (k + 16). split; [exact Hab|]. split; [|exact Hz].
      pose proof (HDX b k Hb') as Hn. change (@cf_head CfParams_preset) with 16 in Hn. exact Hn. }
(* ---- after the call (+0x284): the text's post, then `seqz s8, a0` to O1 (+0x288) ---- *)
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW & HJ2 & HJ1 & _ & HPR2 &
  (HQ2 & HKM)).
subst WS1. rewrite app_nil_r in HJ2.
destruct HQ2 as (HRL2 & Lam' & peak' & fail' & ran' & res & c & ok & Lr & Do & Hres & HLED2 & HOKS
  & HFA & HPLc & HPL2 & HPBc & HZW & HPOS2 & HNR & HDEAD & HARMS).
replace (sp0 + (sp1 - sp0) + 0) with sp1 in HJ1 by lia.
replace (@STK_pj_set prh_img_B DOC_D + 0) with (@STK_pj_set prh_img_B DOC_D) in HJ1 by lia.
pose proof (Crt102Model.cm_set_trace_len n cap ck_MOD_AT) as Ltr.
(* DEAD-PJSET: the call ran at fail = SIZE_MAXZ (S's ledger) with g_count + 3 below it, so its whole trace lies
   before the chosen failure and the text's own clause gives res = 0 - the refused arm (res = -1) is dead here *)
assert (Hres0 : res = 0).
{ apply HDEAD. right. rewrite Ltr. unfold SIZE_MAXZ. destruct (n =? cap); lia. }
assert (Hcl : (c <= 3)%nat).
{ destruct HARMS as [(_ & -> & _) | [(_ & _ & -> & _) | (_ & (_ & Hc2) & _)]]; rewrite ?Ltr in *;
    destruct (n =? cap); lia. }
(* fail stays SIZE_MAX: g_count + c is below it *)
assert (Efail : fail' = SIZE_MAXZ) by (apply (proj2 HFA); unfold SIZE_MAXZ; lia).
subst fail'.
pose proof HTREE as (_ & HDLam & _).
assert (HPL' : Permutation Lam' (Do ++ Lam)) by exact (crt3s_lam_post Lamc Lam' Db Dw Do Lr Lam _ eq_refl HPL HPLc HPL2).
destruct HPBc as (other & Hot1 & Hot2).
assert (HPB' : Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks Do))
  by exact (crt3s_ablocks_perm _ _ _ _ Lam Lamc Lam' Do other HPB HPL Hot1 Hot2 HPL').
assert (HAP' : forall bk, In bk Do -> ~ In bk D).
{ intros bk Hbk HbD.
  exact (crt3s_nodup_apart Lam' Do Lam bk bk (prh_ledger_nodup B _ _ _ _ _ _ _ _ _ _ _ _ HLED2) HPL' Hbk (HDLam _ HbD) eq_refl). }
assert (HLL : forall bk, In bk Lam -> In bk Lam')
  by (intros bk Hbk; apply (Permutation_in _ (Permutation_sym HPL')); apply in_or_app; right; exact Hbk).
assert (HDoL : forall bk, In bk Do -> In bk Lam')
  by (intros bk Hbk; apply (Permutation_in _ (Permutation_sym HPL')); apply in_or_app; left; exact Hbk).
destruct (crt3s_side_call lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc cntc 0 0 _ FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam' peak'
  (cntc + Z.of_nat c) SIZE_MAXZ ran' most 0 HLV HJ1 HFPb HLED2 HLL) as (HROD2 & HDOC2 & HDL2).
assert (Hpk' : peakc <= peak').
{ destruct HARMS as [(_ & _ & _ & -> & _) | [(_ & _ & _ & _ & _ & -> & _) | (_ & _ & _ & _ & _ & -> & _)]]; lia. }
(* g_most and g_own_ran_out ride in the ledger: pj_set's post states the entry's most and own = 0 *)
assert (HSD2 : sideB ly2 S2 Hp2 W2 mem2 Lam' peak' (cntc + Z.of_nat c) 0 ran').
{ refine {| crt_side_ledger := HLED2; crt_side_peak := _; crt_side_room := HRL2;
            crt_side_arodata := HROD2; crt_side_doc := HDOC2; crt_side_doc_blocks := HDL2 |}. lia. }
assert (HLV2 : liveB (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Do
  Lam' peak' (cntc + Z.of_nat c) 0 ran')
  by exact (crt3s_live_call lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc cntc 0 0 _ FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Do Lam'
    peak' (cntc + Z.of_nat c) 0 ran' HLV (ex_intro _ WSj (conj HJ2 HBj)) HJ1 HFPa HSD2 HPL' HPB' HAP' HKM).
pose proof HJ1 as (_ & HLY1 & _).
pose proof HLY1 as (_ & _ & _ & _ & _ & EFF & _).
assert (EF : frame_addr ly2 CRT_CID pos = F) by (unfold F, frame_addr; rewrite EFF; reflexivity).
(* the boundary's memory facts at the post state *)
assert (SP1' := crt3s_spill_keep _ FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 CRT_SP_SHN_B _ HJ1
  ltac:(unfold CRT_SP_SHN_B; lia) HSP1).
assert (SP2' := crt3s_spill_keep _ FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 CRT_SP_PN_B _ HJ1
  ltac:(unfold CRT_SP_PN_B; lia) HSP2).
assert (SP3' := crt3s_spill_keep _ FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 CRT_SP_N_B _ HJ1
  ltac:(unfold CRT_SP_N_B; lia) HSP3).
assert (HFPapp : forall z, inFP FP1 z -> in_app z 1) by (intros z Hz; exact (proj1 (proj2 (HFPa z Hz)))).
assert (HRAB' := crt3s_ra_frame lyc Sc Hpc Wc memc mdc kj pos _ FP1 ly2 S2 Hp2 W2 mem2 md2 k1 CRT_OFF_BACK HJ HJ1 HFPapp
  ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) HRAB).
assert (HRAV' := crt3s_ra_frame lyc Sc Hpc Wc memc mdc kj pos _ FP1 ly2 S2 Hp2 W2 mem2 md2 k1 CRT_OFF_V HJ HJ1 HFPapp
  ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) HRAV).
destruct (crt3_home_keep LAWS HPRE HTREE _ _ _ _ _ _ _ _ HJ2) as (Hd8 & _ & HRAdoc).
(* +0x284 seqz s8, a0 *)
apply crt3s_seqz. intros mat.
set (rgO := regupd regs2 24%bv (v_sltiu (getr regs2 10%bv) 1)).
assert (QR : forall r : bv 5, In r crt3s_KEPT -> r <> 24%bv -> getr rgO r = getr rg r).
{ intros r Hr Hne. unfold rgO. rewrite getr_other by exact Hne. rewrite (crt3s_pres rgc regs2 r HPR2).
  - exact (QK r Hr).
  - unfold crt3s_KEPT in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
assert (DR : crt_dregs_B (regs := regs) (doc := doc) rgO (F_ ly2 pos)).
{ rewrite EF.
  refine {| crt_dregs_B_bregs := {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _;
              crt_bregs_B_s0 := _; crt_bregs_B_s1 := _; crt_bregs_B_s2 := _; crt_bregs_B_s4 := _;
              crt_bregs_B_s3 := _; crt_bregs_B_s7 := _; crt_bregs_B_s9 := _; crt_bregs_B_s11 := _ |};
            crt_dregs_B_s6 := _ |};
  lazymatch goal with |- getr _ ?r = _ =>
    rewrite (QR r ltac:(crt3s_inK) ltac:(reg_neq_tac)); assumption end. }
(* s8 = seqz of pj_set's 0 *)
assert (R24 : getr rgO 24 = w64 1).
{ unfold rgO. rewrite getr_same by reg_neq_tac.
  rewrite (crt3s_seqz_val _ res Hres (or_introl Hres0)), Hres0. reflexivity. }
assert (Hpos' : res = 0 -> posB S2 (evsW ms)).
{ intros E0. apply Hclose. rewrite Hstrtod, <- Eevs. exact (HPOS2 E0). }
unfold CRT3_O1 in HO1.
(* O1 is the GRANTED state (crt_at_O1_3 at sbit = 1, ranc = 0): every granted arm closes through this *)
assert (GO : forall cset, 0 <= cset <= 3 ->
  (In ck_MOD_AT (map fst ms) -> cset = 0) ->
  pj_fdR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam') DOC_D (F_ ly2 pos + CRT_OFF_COPY) Do ->
  cnt <= cntc + Z.of_nat c <= cnt + ck_crt_count t cset -> ran' = 0 ->
  cntc + Z.of_nat c = crt_cw (t := t) (cnt := cnt) cset ->
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam') (F_ ly2 pos + CRT_OFF_COPY) (crt_tc (t := t)) Do ->
  PRH_FnWriter.prhWriter_tree_vis W2 mem2 Do ->
  YCbq.bsum (ck_hblks Do) <= LIVE_round_trip_text t false + LIVE_round_trip_text t true +
    PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
    PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT)) ->
  crt3_copy_tblk (t := t) Do ->
  crt3_copy_fo (t := t) W2 mem2 Lam' (F_ ly2 pos + CRT_OFF_COPY) Do ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
    (mkCfg (@YK11.mkst fxk rgO (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_O1_OFF_B))) mem2 (YK11.seg_rom SEGS))
    (with_vm_backing (m_vm_lazy md2) mat md2)) QFb).
{ intros cset Hcs Hcs0 Hfd Hcn Hran Hcw HND Htv Hbs Htb Hfo.
  apply (HO1 fxk ly2 S2 Hp2 W2 mem2 _ (kj + k1) pos Do Lam' peak' (cntc + Z.of_nat c) ran' rgO ms cset 1).
  split; [exact Et|]. split; [exact Hfz|]. split; [exact Hfk|].
  split; [exact (crt3s_live_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat HLV2)|].
  split; [exact DR|]. split; [exact R24|]. split; [reflexivity|].
  split; [exact SP1'|]. split; [exact SP2'|]. split; [exact SP3'|].
  split; [exact Hd8|]. split; [exact HRAdoc|]. split; [exact HRAB'|]. split; [exact HRAV'|].
  split; [exact Hcs|]. split; [exact Hcs0|]. split; [exact Hfd|]. split; [exact Hcn|].
  split; [exact Hran|].
  intros _. split; [exact Hcw|]. split; [exact HND|]. split; [exact Htv|]. split; [exact Hbs|].
  split; [exact (Hpos' Hres0) | split; [exact Htb | exact Hfo]]. }
(* the facts every arm reads: the copy's old blocks, the stamp's block, the counts, the depths *)
assert (HDbL : forall b k, In (b, k) Db -> 0 <= k)
  by (intros b k Hb; exact (proj1 (crt3s_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED (HDx b k (or_intror Hb))))).
assert (Hroom : YCbq.bsum (ck_hblks Db) <= LIVE_round_trip_text t false)
  by exact (Crt102Model.cm_copy_room_rtt t Db (Crt102Model.cm_in_wf x t Hcm) HPMS HLEN).
pose proof (Crt102Model.cm_stamp_block a) as Hstb.
pose proof (Crt102Model.cm_LIVE_crt_terms t) as (L0 & L1 & L2 & L3 & _).
assert (Hdsm : forall b k, In (b, k) Db -> k < 2 ^ 32)
  by (intros b k Hb; pose proof (crt3s_db_small Db HPMS b k Hb); lia).
assert (Hdepc : (PjTree.depth (PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP))) <= DOC_D)%nat).
{ pose proof (Crt102Model.cm_crt_depth_doc t (Crt102Model.cm_in_depth x t Hcm)) as Hd. rewrite Et in Hd. exact Hd. }
assert (Etc : crt_tc (t := t) = PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))
  by (unfold crt_tc; rewrite Et; reflexivity).
assert (HTV : (forall b k, In (b, k) Do -> k < 2 ^ 32) -> PRH_FnWriter.prhWriter_tree_vis W2 mem2 Do).
{ intros Hsm. apply (crt3_tree_vis_keep B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 Lam' peak' (cntc + Z.of_nat c) SIZE_MAXZ ran'
    most 0 Do (proj1 HJ2) HLED2 HDoL).
  intros b k Hb. exact (crt3s_tv_facts ly2 S2 Hp2 W2 mem2 md2 Lam' peak' (cntc + Z.of_nat c) SIZE_MAXZ ran' most 0 b k
    (proj1 HJ2) HLED2 (HDoL _ Hb) (Hsm b k Hb)). }
(* val's ordered free list, FREEORD-COPY's premise on both granted arms *)
pose proof (crt3s_stamp_fo Wc memc Lamc (F + CRT_OFF_V) a HVN) as HFW.
destruct HARMS as [A1 | [A2 | A3]].
- (* the key is present: copy's value replaced in place, c = 0 *)
  destruct A1 as (Hin1 & -> & Eres & _ & (i & vi & Di' & Dr & _ & _ & _ & HPD & HPDo) & HND2 & HTBo & HFO1).
  apply (GO 0).
  + lia.
  + intros _. reflexivity.
  + rewrite EF. apply (crt3_fd_mono _ _ _ _ _ _ _ Hdepc). exact (crt3_nodeR_fd _ _ _ _ _ _ HND2).
  + rewrite ECNT. exact (crt3s_cnt_range ms cnt 0 Et ltac:(lia)).
  + (* no allocation: g_ran_out unchanged *)
    exact (crt3s_oks_granted _ _ _ _ _ _ _ _ HOKS ltac:(intros i0 Hi0; lia)).
  + rewrite crt3s_cw, ECNT; lia.
  + rewrite Etc, EF; exact HND2.
  + apply HTV. intros b k Hb. apply (Permutation_in _ HPDo) in Hb. apply in_app_or in Hb as [Hb | [Hb | []]].
    * apply (Hdsm b k). apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. exact Hb.
    * injection Hb as _ <-. cbn. lia.
  + rewrite (Crt102Model.cm_bsum_hblks_perm _ _ HPDo), Crt102Model.cm_bsum_hblks_app.
    rewrite (Crt102Model.cm_bsum_hblks_perm _ _ HPD), Crt102Model.cm_bsum_hblks_app in Hroom.
    change (YCbq.bsum (ck_hblks Dw)) with (YCbq.bsum (ck_hblks [(a, Z.of_nat (length ck_STAMP) + 1)])). rewrite Hstb.
    assert (0 <= YCbq.bsum (ck_hblks Di')).
    { apply crt3s_bsum_nonneg. intros b k Hb. apply (HDbL b). apply (Permutation_in _ (Permutation_sym HPD)).
      apply in_or_app. left. exact Hb. }
    lia.
  + exact (crt3s_copy_tblk ms Do Et (HTBo (crt3s_stamp_tblk a))).
  + (* FREEORD-COPY at nn := DOC_D, in the callee's post memory, which the `seqz` step leaves unchanged *)
    rewrite EF. exact (crt3s_copy_fo ms W2 mem2 Lam' (F + CRT_OFF_COPY) Do Et (HFO1 crt3_head_model HFW)).
- (* the key is absent and every allocation was taken: appended, c = the trace's length *)
  destruct A2 as (Hnin & _ & Ec & Hall & Eres & _ & (Dold & Dnew & Dr & a' & HPD & HPDo & _ & Hcase) & HND2 & HTBo
    & HFO2).
  assert (Hc3 : 0 <= Z.of_nat c <= 3) by (rewrite Ec, Ltr; destruct (n =? cap); lia).
  assert (Hk0 : 0 <= cap) by lia.
  pose proof (Crt102Model.cm_cap2R_nonneg cap Hk0) as Hc2n.
  assert (HDr : forall b k, In (b, k) Dr -> In (b, k) Db)
    by (intros b k Hb; apply (Permutation_in _ (Permutation_sym HPD)); apply in_or_app; right; exact Hb).
  apply (GO (Z.of_nat c)).
  + exact Hc3.
  + intros Hin2. exfalso. exact (Hnin Hin2).
  + rewrite EF. apply (crt3_fd_mono _ _ _ _ _ _ _ Hdepc). exact (crt3_nodeR_fd _ _ _ _ _ _ HND2).
  + rewrite ECNT. exact (crt3s_cnt_range ms cnt (Z.of_nat c) Et ltac:(lia)).
  + (* every allocation granted: g_ran_out unchanged *)
    exact (crt3s_oks_granted _ _ _ _ _ _ _ _ HOKS Hall).
  + rewrite crt3s_cw, ECNT; lia.
  + rewrite Etc, EF; exact HND2.
  + apply HTV. intros b k Hb. apply (Permutation_in _ HPDo) in Hb.
    apply in_app_or in Hb as [Hb | [Hb | Hb]].
    * destruct Hcase as [(_ & _ & ->) | (Encap & _ & k' & y' & ->)]; [destruct Hb|].
      pose proof (Crt102Model.cm_rq_grow t HRQ n cap Enm Encap) as Hg.
      change (@cf_head CfParams_preset) with 16 in Hg.
      assert (Hmm : @cf_malloc_max CfParams_preset <= 2 ^ 29 - 2 ^ 20) by (vm_compute; discriminate).
      destruct Hb as [Hb | [Hb | []]]; injection Hb as _ <-; lia.
    * injection Hb as _ <-. cbn. lia.
    * apply in_app_or in Hb as [Hb | [Hb | []]]; [exact (Hdsm b k (HDr b k Hb))|]. injection Hb as _ <-. cbn. lia.
  + rewrite (Crt102Model.cm_bsum_hblks_perm _ _ HPDo).
    replace (Dnew ++ (a', Z.of_nat (length ck_MOD_AT) + 1) :: Dr ++ Dw)
      with ((Dnew ++ [(a', Z.of_nat (length ck_MOD_AT) + 1)]) ++ Dr ++ Dw) by (rewrite <- app_assoc; reflexivity).
    rewrite !Crt102Model.cm_bsum_hblks_app.
    rewrite (Crt102Model.cm_bsum_hblks_perm _ _ HPD), Crt102Model.cm_bsum_hblks_app in Hroom.
    change (YCbq.bsum (ck_hblks Dw)) with (YCbq.bsum (ck_hblks [(a, Z.of_nat (length ck_STAMP) + 1)])). rewrite Hstb.
    assert (0 <= YCbq.bsum (ck_hblks Dold)).
    { apply crt3s_bsum_nonneg. intros b k Hb. apply (HDbL b). apply (Permutation_in _ (Permutation_sym HPD)).
      apply in_or_app. left. exact Hb. }
    assert (YCbq.bsum (ck_hblks Dnew) + YCbq.bsum (ck_hblks [(a', Z.of_nat (length ck_MOD_AT) + 1)]) <=
            PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT))).
    { rewrite <- Crt102Model.cm_bsum_hblks_app.
      destruct Hcase as [(Hlt & _ & ->) | (Encap & _ & k' & y' & ->)].
      - cbn [app]. pose proof (Crt102Model.cm_set_key_block n cap a' Hk0).
        pose proof (Crt102Model.cm_LIVE_set_le n cap (Z.of_nat (length ck_MOD_AT)) ltac:(lia)). rewrite <- Enm. lia.
      - cbn [app]. rewrite (Crt102Model.cm_set_grow_blocks cap k' y' a'). rewrite <- Enm, Encap. lia. }
    lia.
  + exact (crt3s_copy_tblk ms Do Et (HTBo crt3_head_model (crt3s_stamp_tblk a) crt3s_modat_ech)).
  + (* FREEORD-COPY at nn := DOC_D (MOD_KEY has no special character: crt3s_modat_ech) *)
    rewrite EF.
    exact (crt3s_copy_fo ms W2 mem2 Lam' (F + CRT_OFF_COPY) Do Et (HFO2 crt3_head_model HFW crt3s_modat_ech)).
- (* the refused arm returned -1: dead by DEAD-PJSET (Hres0) *)
  exfalso. destruct A3 as (_ & _ & _ & _ & Eres & _). lia.
Qed.

(* the S boundary at a materialised model (only the journal reads the model) *)
Lemma crt3s_atS_mat : forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms a X,
  atS fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms a ->
  atS fxk lyc Sc Hpc Wc memc (with_vm_backing (m_vm_lazy mdc) X mdc) kj pos Db Lamc peakc cntc rg ms a.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms a X (E1 & E2 & E3 & HLv & HR).
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [|exact HR].
exact (crt3s_live_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ X HLv).
Qed.

(* a register after the pre-call run, read off the run's symbolic register file *)
Ltac crt3s_rreg HS r :=
  rewrite (st_ok_restrict_reg SEGS _ _ _ _ r HS);
  lazymatch goal with |- context [sr_get ?s r] => let e := eval vm_compute in (sr_get s r) in change (sr_get s r) with e end;
  cbn [sv_denot].
Ltac crt3s_rlow rg n r :=
  rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat rg [] n r eq_refl);
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
Ltac crt3s_kept HS rg :=
  lazymatch goal with |- getr _ ?rr = getr _ ?rr =>
    crt3s_rreg HS rr; rewrite Eimg_low by (unfold A_TEXT; lia); erewrite (ew_Ereg_nat rg [] _ rr) by reflexivity;
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  end.

Lemma crt3_S : STMT_O1 -> STMT_S.
Proof.
intros HO1 fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms a HAT.
pose proof HAT as (_ & _ & _ & HL & HDR & H21 & _). destruct (crt_live_journal HL) as (WSj & HJ & HBj).
pose proof (crt_dregs_B_bregs HDR) as HBR. pose proof (crt_dregs_B_s6 HDR) as R22.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3.
pose proof (crt_bregs_B_tp HBR) as R4. pose proof (crt_bregs_B_s0 HBR) as R8.
pose proof (crt_bregs_B_s1 HBR) as R9. pose proof (crt_bregs_B_s2 HBR) as R18.
pose proof (crt_bregs_B_s4 HBR) as R20. pose proof (crt_bregs_B_s3 HBR) as R19.
pose proof (crt_bregs_B_s7 HBR) as R23. pose proof (crt_bregs_B_s9 HBR) as R25.
pose proof (crt_bregs_B_s11 HBR) as R27.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rg []))) by apply Eimg_env.
assert (HS : st_ok_pi (fx := fxk) SEGS VAL (Eimg (Ereg rg []))
  (mkSS (CRT_PC_B + CRT_S_OFF_B) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_S_OFF_B))) memc (YK11.seg_rom SEGS)))).
{ rewrite (restrict_mkst_fx (fx := fxk)). apply (pa_entry_st_ok_full (fx := fxk)).
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS (SOff 27 0) [] (Eimg (Ereg rg [])) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose (RUN := @Crt102Kit.crt_run_xw fxk rc SK _ PL PA B PST ARx _ LAWS WSj).
unfold crt_cfg.
(* +0x270 .. +0x280: auipc / addi a1 (MOD_AT), a0 = s4 (&copy), a2 = s5 (&v), jal pj_set; no store *)
paj_run_tok_x RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1); [apply awr_ok_nil|].
pmkst HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msn) =>
  assert (Emem : ms_mem msn = memc)
    by (apply FunctionalExtensionality.functional_extensionality; intros y; apply HF; intros (r & Hin & _);
        cbn [ss_mem In] in Hin; destruct Hin)
end.
rewrite Emem.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msn) =>
  assert (Q10 : getr (ms_regs msn) 10 = w64 (F_ lyc pos + CRT_OFF_COPY))
    by (crt3s_rreg HS (10%bv : bv 5); crt3s_rlow rg 20%nat (20%bv : bv 5); exact R20);
  assert (Q12 : getr (ms_regs msn) 12 = w64 (F_ lyc pos + CRT_OFF_V))
    by (crt3s_rreg HS (12%bv : bv 5); crt3s_rlow rg 21%nat (21%bv : bv 5); exact H21);
  assert (Q11 : getr (ms_regs msn) 11 = w64 (CRT_MOD_AT_B (PA := PA)))
    by (crt3s_rreg HS (11%bv : bv 5); rewrite (HEI 243%nat ltac:(unfold A_TEXT, A_LIM; lia)); reflexivity);
  assert (Q1 : getr (ms_regs msn) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + CRT_K_OFF_B)))
    by (crt3s_rreg HS (1%bv : bv 5); rewrite (HEI 240%nat ltac:(unfold A_TEXT, A_LIM; lia)); reflexivity);
  assert (QK : forall r : bv 5, In r crt3s_KEPT -> getr (ms_regs msn) r = getr rg r)
    by (intros r Hr; unfold crt3s_KEPT in Hr; cbn [In] in Hr;
        repeat (destruct Hr as [<- | Hr]; [crt3s_kept HS rg|]); destruct Hr)
end.
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg _ (with_vm_backing _ ?X _)) _ =>
  exact (crt3s_call fxk lyc Sc Hpc Wc memc _ kj pos Db Lamc peakc cntc rg ms a _ HO1 (crt3s_atS_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X HAT)
    Q10 Q11 Q12 Q1 QK)
end.
Qed.

End g.
End f.
End t3s.

Print Assumptions crt3_S.
