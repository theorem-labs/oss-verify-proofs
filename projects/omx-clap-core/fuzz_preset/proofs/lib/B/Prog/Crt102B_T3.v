(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 141 of its 177 lines of code are new or changed and 478 lines of the source are left out. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan
   d663f82d7f488d30, unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T3 (CRT-B-UGKO1): THE SEGMENT
   LEMMA of U, G, K, O1 = B' entry + 0x1ec -> + 0x2a4 (round_trip_rewrite inlined, fuzz_preset.c new:719-734).
   Owned by the row holder, under the family lead.

   rule 24: proves function check_round_trip (segment T3 of image B' only).
   `proof-index check_round_trip` (index v5, built 2026-10-29T07:26:27Z), first line verbatim:
     proof-index: check_round_trip: 31 named, 92 by address, 86 related, 14 released lemma(s), delivery 0 named and
     0 name(s) holding it, 24 UNRELEASED cold/* file(s) in the lemma index, 0 UNRELEASED hit(s) on live working heads
   Second-agent check: CONFIRM (no hit names the #102 B' image). Address lookup of the segment's pcs
   (index v5 built 16:10:25Z), the rule-24 lookup: 0 released. none: written
   new.

   THE STATEMENT (crt102b_seg_T3): from crt_at_U_B (Crt102Glue.v at the crt head 71a8716672850d3, frozen) at the cut U
   (+0x1ec) the run of check_round_trip reaches QF, given the two boundaries this segment could end in - crt_at_X_B at
   X (+0x30c; CRT3_X = the glue's CRT_B_AT_X at the B' offsets, checked below) and crt_at_W_B at W (+0x2a4; row T4's
   pre, frozen in the glue) - each in the boundary form `the run from this configuration reaches QF`. At this head
   the X exit (C4a: a refusal, then r = 1) is unreachable - the callee texts' DEAD-PJSTRING / -PJSET clauses close
   the refused arms at their source - so STMT_X is a premise the proof does not use; the `!set` abort at +0x2a0 is
   unreachable for the same reason. It is the composition of the three stages (Crt102B_T3U.v crt3_U,
   Crt102B_T3S.v crt3_S, Crt102B_T3O.v crt3_O1) over the inner cuts S and O1 of Crt102B_T3Base.v. No instruction is
   walked here.
   THE ROW'S NAMED HYPOTHESES (each a Section hypothesis below, with its owner):
   - HB_base / HB_entry / HB_segs / HB_relro / HB_hi: Crt102Img.v Section b's image values (owner: the image-B
     instance, lib/B/PAImg_prog.v, which waits for the instance owner's IMG_TOP_B = 0x601000);
   - LAWS: AR_laws_x at hl = cf_head (owner: the instance, AR_laws_x_cf of the instance owner's ARcf);
   - ZSA / IMGV: walk S4's two image facts; IMGV at image B's bounds, the instance owner's img_shadow_vis_cf at
     CfImg_B (owner: the instance owner, img_shadow_vis_cf / aso_zshadow at the instance);
   - HPJS / HPJSET / HRO: the callee texts (their walks are other lanes'); HPJS / HPJSET are the head's entry-keyed
     event-form pj texts (PRH_FnPj.v 5aca5cbe2cfb, the kit cut: DEAD-PJSTRING / -PJSET, FREEORD-COPY) and are
     marked LEDGER (the ledger half, read here only under the request bound);
   - HPRE .. HRQ: tcheck_round_trip_specX's own premises (Crt102Top discharges them).
   kb round (the contract's wild budget in the glue's crt_live): crt102b_seg_T3 and the stage statements keep their text;
   crt_at_U_B and crt_at_W_B carry crt_live at kb 64 (the glue's G4) and so do the inner cuts S and O1
   (Crt102B_T3Base.v); the stage files re-fit their proofs to the journal at a budget WS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102B_T3O Crt102B_T3S Crt102B_T3U.
(* The re-hiding move: the stage statements at YA0nH.SRr' SEGS
   YGcfRehidePost.RZ_cf, the journal at YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (the re-hiding contract) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
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
(* THE RUN HAS AT MOST 4 CALLS (DRAFT, the text's own premise PRH_FnCheck.v:2363): pj_string's and pj_set's texts ask
   it of the caller's rp_os (Crt102B_T3U.v / Crt102B_T3S.v HOS4); Crt102TopB passes the text's premise *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.

(* the X boundary is the glue's own statement (the glue's CRT_B_AT_X) at the B' cut offsets *)
Lemma crt102b_T3_X_is_glue : STMT_X =
  CRT_B_AT_X (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
    (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
    (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
    (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most) (CRT_PC := CRT_PC_B)
    (CRT_X_OFF := CRT_X_OFF_B).
Proof. reflexivity. Qed.

(* THE SEGMENT LEMMA. The two WAITS of the re-fit (2026-10-30) are CLOSED at the crt head
   71a8716672850d3, which carries the kit cut (PRH_FnPj 5aca5cbe2cfb):
   - DEAD-PJSTRING / -PJSET: the C4a exit (a refusal in pj_string / pj_set, then r = 1 at X) is unreachable AT ITS
     SOURCE by the callee texts' own clauses `(cnt <> fail -> a <> 0)` (tpj_string_specX) and `(fail < cnt \/ cnt +
     |trace| <= fail) -> res = 0` (tpj_set_specX) at fail = SIZE_MAXZ; O1 is reached only granted (crt_at_O1_3:
     sbit = 1, ranc = 0), so crt_at_X_B (its crt_at_J_B_r0 : r = 0) is never built and STMT_X is not used;
   - FREEORD-COPY: crt_at_W_B_copy_fo from tpj_set_specX's result free order on both granted arms (Crt102B_T3S.v),
     carried through O1 (Crt102B_T3O.v). *)
Theorem crt102b_seg_T3 : STMT_X -> STMT_W -> STMT_U.
Proof.
intros HX HW.
assert (HO1 : STMT_O1) by (eapply crt3_O1; eassumption).
assert (HS : STMT_S) by (eapply crt3_S; eassumption).
eapply crt3_U; eassumption.
Qed.

End g.
End f.
End t3s.

Print Assumptions crt102b_seg_T3.
