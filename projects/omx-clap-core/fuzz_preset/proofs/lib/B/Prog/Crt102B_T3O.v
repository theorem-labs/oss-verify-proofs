(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 506 of its 557 lines of code are new or changed and 463 lines of the source are left out. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan d663f82d7f488d30),
   FREE-PIECES-102 Part 7a row T3 (CRT-B-UGKO1), STAGE O1: from the cut O1 (B' entry + 0x288, crt_at_O1_3 of
   Crt102B_T3Base.v) to W (+0x2a4, the glue's crt_at_W_B); O1 is the granted state only, so X is not reached.
   Owned by the row holder; written by the O1 stage.

   proves no function (kind: segment lemma crt3_O1 : CRT3_X -> CRT3_W -> CRT3_O1).

   THE CODE (the internal file crt.B.s; offsets from the B' entry):
     +0x288 auipc s10           +0x28c lbu a0, 0x2d0(s10) (g_own_ran_out)   +0x290 addi s5, zero, 1
     +0x294 bnez a0, +0x30c     +0x298 jal fuzz_alloc_ran_out   +0x29c bnez a0, +0x30c
     +0x2a0 beqz s8, +0x824     +0x2a4 W.
   THE PROOF. One engine run +0x288 -> the call of fuzz_alloc_ran_out, from a symbolic state with one read-only region:
   the g_own_ran_out byte (listing atom A_OBJ 13, Base crt3_own13) holding 0 (crt_at_O1_3's crt_live has own = 0), so
   the first bnez falls through. The call by YCbqGwild's aj_call_xb_sp over the contract text tfuzz_alloc_ran_out_specX
   (an m-form fpost: its fQmn conjunct keeps memnorm), at the realigned sp (o = sp1 - sp0, crt_sp1_off), the chain
   crt3_chain, FP1 = []. After the call crt_at_O1_3 holds again at the callee's post state (crt3o_after: the callee
   journal keeps the stack above sp1, the frames and the live blocks, so copy's tree and ordered free list by
   pj_nodeR_frame / pj_foR_frame; the text keeps the ledger with most / own), then: a0 = g_ran_out = ranc = 0, so
   the second bnez falls through (the C4a exit to X is dead); s8 = sbit = 1, so `beqz s8` falls through (the `!set`
   abort is dead); W (CRT3_W) by crt3o_toW. CRT3_X is an unused premise. The engine stretches write no byte, so the
   memory after each run is the memory before it (frame_of with no write window, functional extensionality).
   NUMERALS: register and atom indices (WORD / engine numbering: 32 = the first havoc atom after the call, a0 = 36,
   s8 = 24); 512 / 56 / 64 / 8 / 16 (LENGTH: the class-3 frame, struct pj, its shadow, a word, a granule); 13 (the
   saved slots); 4096 / 2 ^ 30 / 2 ^ 40 (LENGTH: a page, the image and listing bounds a vm_compute checks under
   HB_base). No ADDRESS literal: addresses come from the listing, pa_val, PrhImg fields and the HB hypotheses.
   kb round: crt_live carries its budget kb (64 at O1 and W) and its journal at a budget WS. fuzz_alloc_ran_out has no
   wild site, so its call is the budgeted call rule at its empty budget (P := fun WS1 => WS1 = [], the callee's old
   post by YCbqGwild.apost_base_xb_of_x) and the caller's journal stays at O1's budget WS; the runs keep WS
   (Crt102Kit.crt_run_xw / crt_run_to_xw, used qualified). crt3o_jnl / crt3o_after take the journal at a budget WS
   with wbudget [] 64 WS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Kit.
(* The re-hiding move: the journal at YA0nH.wle' SEGS YGcfRehidePost.RZ_cf, the
   steps at YA0nH.SRr' (YSRrG's bind / mono / branch), fuzz_alloc_ran_out's plain text lifted (the re-hiding contract's R5) *)
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
(* ---- the symbolic state at O1: every register its atom, one read-only region, the g_own_ran_out byte (0) ---- *)
Definition crt3o_Bx : sv := SOff 27 0.
Definition crt3o_rown : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 13)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition crt3o_ss : sstate := mkSS (CRT_PC_B + CRT_O1_OFF_B) sr_atoms [crt3o_rown] None (mkFacts [] [] []).

(* membership in a literal register list *)
Ltac crt3o_in := cbn [In]; repeat first [left; reflexivity | right].

(* a value read through two views that agree on its bytes *)
Lemma crt3o_vm_keep : forall (Wa Wb : world SEGS) ma mb a n v,
  (forall k, (k < n)%nat -> aview SEGS (w_H Wb) mb (a + Z.of_nat k) = aview SEGS (w_H Wa) ma (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict (w_H Wa) ma) a n v -> val_mem SEGS (mrestrict (w_H Wb) mb) a n v.
Proof.
intros Wa Wb ma mb a n v HK Hv k Hk. rewrite (mbyte_of_aview SEGS (w_H Wa) (w_H Wb) ma mb _ (HK k Hk)). exact (Hv k Hk).
Qed.

(* two views agree on a byte set when the later one keeps the bytes and has them present *)
Lemma crt3o_agree : forall (Wa Wb : world SEGS) ma mb (X : Z -> Prop),
  (forall y, X y -> aview SEGS (w_H Wb) mb y = aview SEGS (w_H Wa) ma y /\ apresent (w_H Wb) mb y) ->
  pj_agreeR SEGS (mrestrict (w_H Wa) ma) (mrestrict (w_H Wb) mb) X.
Proof.
intros Wa Wb ma mb X H y Hy. destruct (H y Hy) as [E P]. split.
- exact (mbyte_of_aview SEGS _ _ _ _ y E).
- intros _. exact (apresent_writable SEGS _ _ y P).
Qed.

(* a byte of the class-3 frame has its shadow byte in the frame's 64 shadow bytes *)
Lemma crt3o_shadow_in : forall F y, F mod 8 = 0 -> F <= y < F + 512 ->
  shadow_addr F <= shadow_addr y < shadow_addr F + 512 / 8.
Proof.
intros F y HF Hy. unfold shadow_addr. apply Z.mod_divide in HF; [|lia]. destruct HF as [q ->].
assert (q <= y / 8 < q + 64) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
change (512 / 8) with 64. lia.
Qed.

(* the shadow hull of copy (F + 224, 56 bytes) lies in the frame's 64 shadow bytes *)
Lemma crt3o_hull_in : forall F s, F mod 32 = 0 -> 0 <= F ->
  shadow_addr (F + 224) / 8 * 8 <= s < shadow_addr (F + 224 + 56 - 1) / 8 * 8 + 8 ->
  shadow_addr F <= s < shadow_addr F + 512 / 8.
Proof.
intros F s HF H0 Hs. unfold shadow_addr, SHADOW_OFF in *. change (512 / 8) with 64. lia.
Qed.

(* the journal at a boundary, swapped for another journal at the same state at a budget WS within O1's kb *)
Lemma crt3o_jnl : forall fxk lyc Sc Hpc Wc memc mdc mdc' kj kj' pos Dc Lamc peakc cntc ranc rg mbs cset sbit
    {WS : list (list Z)},
  atO1 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc ranc rg mbs cset sbit ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc' kj' WS ->
  YCbqGwild.wbudget [] (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat WS ->
  atO1 fxk lyc Sc Hpc Wc memc mdc' kj' pos Dc Lamc peakc cntc ranc rg mbs cset sbit.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc mdc' kj kj' pos Dc Lamc peakc cntc ranc rg mbs cset sbit WS
  (H1 & H2 & H3 & HL & H5) HJ' HB'.
refine (conj H1 (conj H2 (conj H3 (conj _ H5)))).
refine {| crt_live_journal := ex_intro _ WS (conj HJ' HB'); crt_live_side := crt_live_side HL;
          crt_live_lam_perm := crt_live_lam_perm HL; crt_live_blocks_perm := crt_live_blocks_perm HL;
          crt_live_dx_apart := crt_live_dx_apart HL; crt_live_saved := crt_live_saved HL;
          crt_live_frame := crt_live_frame HL; crt_live_fspill := crt_live_fspill HL;
          crt_live_copy_open := crt_live_copy_open HL; crt_live_copy_hull := crt_live_copy_hull HL;
          crt_live_memnorm := crt_live_memnorm HL |}.
Qed.

(* ---- O1 AGAIN AFTER fuzz_alloc_ran_out: the callee's journal (at the realigned sp, FP = []) keeps the stack above
   sp1, every frame of the call state with its shadow, and every live block; the text keeps the state, the blocks and
   the ledger (with most and own, own = 0 at O1); the composed journal is the entry's. ---- *)
Lemma crt3o_after : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc ranc rg mbs cset sbit
    STK1 ly2 Hp2 W2 mem2 md2 k1 {WS1 : list (list Z)},
  atO1 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc ranc rg mbs cset sbit ->
  AJW STK1 sp1 [] lyc Sc Hpc Wc memc mdc [] ly2 Sc Hp2 W2 mem2 md2 k1 WS1 ->
  (exists WS2, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 Sc Hp2 W2 mem2 md2 (kj + k1) WS2 /\
     YCbqGwild.wbudget [] (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat WS2) ->
  ablocks B ly2 Sc = ablocks B lyc Sc ->
  prh_ledger B ly2 Sc Hp2 W2 mem2 Lamc peakc cntc SIZE_MAXZ ranc most 0 ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  atO1 fxk ly2 Sc Hp2 W2 mem2 md2 (kj + k1) pos Dc Lamc peakc cntc ranc rg mbs cset sbit.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc ranc rg mbs cset sbit STK1 ly2 Hp2 W2 mem2 md2 k1 WS1
  HO HJ1 (WS2 & HJ2 & HB2) EAB HLED2 HKM.
destruct HO as (Ht & Hfz & Hfk & HL & HDR & H24 & Hsb & HSP1 & HSP2 & HSP3 & Hd8 & HRAd & HRAb & HRAv &
  Hcs & Hcs0 & HFD & Hcnt & Hsb0 & Hsb1).
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPA.
pose proof (crt_live_dx_apart HL) as HDD. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFR. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HRAc. pose proof (crt_live_copy_hull HL) as HHVc.
pose proof (crt_live_memnorm HL) as HMN.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HROOM. pose proof (crt_side_arodata HSD) as HROD.
pose proof (crt_side_doc HSD) as HND. pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ1 as (HAR2 & Hly & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof (crt3_sp0 HPRE) as (Hal16 & Hceil & H47 & Hshi).
pose proof (crt3_sp1 HPRE) as (Hs32 & Hs1 & Hs10).
pose proof crt3_stk as Hstk.
pose proof (YM05.alloc_ceiling_val) as Hcv.
assert (HFB : fs_frame_bytes CRT_CID = 512) by (vm_compute; reflexivity).
destruct (crt3_ff LAWS _ _ _ _ _ _ _ _ HJ) as (HinF & _ & HF0 & HFc & HFapp & HF32 & _ & _).
set (F := frame_addr lyc CRT_CID pos) in *.
assert (HF8 : F mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in HF32; [|lia]. destruct HF32 as [q Hq]. exists (4 * q). lia. }
assert (EF : forall c p, frame_addr ly2 c p = frame_addr lyc c p).
{ intros c p. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & E & _). rewrite E. reflexivity. }
assert (EG : forall c p, flag_addr ly2 c p = flag_addr lyc c p).
{ intros c p. unfold flag_addr. destruct Hly as (_ & _ & _ & _ & _ & E & _). rewrite E. reflexivity. }
(* the callee's keeps *)
assert (KS : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply G1; lia. }
assert (KF : forall c p a, In (c, p) (frames Sc) -> frame_addr lyc c p <= a < frame_addr lyc c p + fs_frame_bytes c ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros c p a Hin Ha. apply (G4 c p a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply inFP_nil]. }
assert (KFS : forall c p a, In (c, p) (frames Sc) ->
  shadow_addr (frame_addr lyc c p) <= a < shadow_addr (frame_addr lyc c p) + fs_frame_bytes c / 8 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros c p a Hin Ha. apply (G4 c p a Hin); [right; unfold in_zr; cbn [fst snd]; lia | apply inFP_nil]. }
assert (KB : forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n ->
  aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H Wc) memc (p + i)).
{ intros p n i Hin Hi. apply (G2 p n i Hin); [rewrite EAB; exact Hin | exact Hi | apply inFP_nil]. }
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a H1 H2 H3 H4. exact (G3 a H1 H2 H3 H4 (fp_spares_closed _ _ sink_closed_nil)). }
(* presence at the post state *)
assert (PF : forall c p a, In (c, p) (frames Sc) -> frame_addr lyc c p <= a < frame_addr lyc c p + fs_frame_bytes c ->
  apresent (w_H W2) mem2 a).
{ intros c p a Hin Ha. destruct (alx_frames SEGS B ARx LAWS ly2 Sc Hp2 W2 mem2 md2 c p HAR2 Hin) as (_ & _ & Hpr & _).
  rewrite EF in Hpr. exact (proj1 (Hpr a Ha)). }
assert (PB : forall p n a, In (p, n) (ablocks B lyc Sc) -> p <= a < p + req_size n -> apresent (w_H W2) mem2 a).
{ intros p n a Hin Ha. rewrite <- EAB in Hin.
  destruct (alx_blocks SEGS B ARx LAWS ly2 Sc Hp2 W2 mem2 md2 p n HAR2 Hin) as (_ & _ & _ & _ & Hpr & _).
  exact (proj1 (Hpr a Ha)). }
(* a byte of a frame of the call state or of a live harness block: kept and present *)
assert (KX : forall y,
  ((exists c p, In (c, p) (frames Sc) /\ frame_addr lyc c p <= y < frame_addr lyc c p + fs_frame_bytes c) \/
   (exists a k, In (a, k) Lamc /\ a <= y < a + k)) ->
  aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y /\ apresent (w_H W2) mem2 y).
{ intros y [(c & p & Hin & Hy) | (a & k & Hin & Hy)].
  - split; [exact (KF c p y Hin Hy) | exact (PF c p y Hin Hy)].
  - pose proof (proj1 (Forall_forall _ _)
      (prh_ledger_blocks B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc most 0 HLED)
      (a, k) Hin) as (Hk0 & Hab & _).
    cbn [fst snd] in Hk0, Hab. change (@cf_head CfParams_preset) with 16 in Hab.
    pose proof (req_size_pos (k + 16) ltac:(lia)) as (_ & Hrq).
    replace y with (a - 16 + (y - (a - 16))) by lia.
    split; [apply (KB _ _ _ Hab); lia | apply (PB _ _ _ Hab); lia]. }
assert (HDc : forall b, In b Dc -> In b Lamc).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hb. }
assert (AGc : pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (pj_footR (F + CRT_OFF_COPY) Dc)).
{ apply crt3o_agree. intros y [Hy | ((a & k) & Hb & Hy)]; apply KX.
  - left. exists CRT_CID, pos. split; [exact HinF|]. fold F. rewrite HFB. unfold CRT_OFF_COPY in Hy. lia.
  - right. exists a, k. split; [exact (HDc _ Hb) | unfold pj_holdsR in Hy; cbn [fst snd] in Hy; exact Hy]. }
(* the frame's locals keep their shadow *)
assert (KRA : forall o, 0 <= o -> o + 56 <= 512 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F + o) 56 ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (F + o) 56).
{ intros o Ho0 Ho1 HR. apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HR].
  intros y Hy. change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y). apply (KFS CRT_CID pos); [exact HinF|].
  fold F. rewrite HFB. apply crt3o_shadow_in; [exact HF8 | lia]. }
(* the stack above sp1 *)
assert (KSV : forall a n v, sp1 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) a n v -> val_mem SEGS (mrestrict (w_H W2) mem2) a n v).
{ intros a n v Ha Hn Hv. apply (crt3o_vm_keep Wc W2 memc mem2); [|exact Hv]. intros k Hk. apply KS. lia. }
unfold crt_at_O1_3. rewrite !EF. fold F.
split; [exact Ht|]. split; [exact Hfz|]. split; [exact Hfk|].
split.
{ (* the live state *)
  refine {| crt_live_journal := ex_intro _ WS2 (conj HJ2 HB2); crt_live_side := _; crt_live_lam_perm := HPL;
            crt_live_blocks_perm := _; crt_live_dx_apart := HDD; crt_live_saved := _;
            crt_live_frame := _; crt_live_fspill := _; crt_live_copy_open := _;
            crt_live_copy_hull := _; crt_live_memnorm := _ |}.
  - (* crt_side *)
    refine {| crt_side_ledger := HLED2; crt_side_peak := Hpk; crt_side_room := HROOM;
              crt_side_arodata := _; crt_side_doc := _; crt_side_doc_blocks := HDL |}.
    + intros a Hro Ho He.
      assert (Hi : in_img SEGS a).
      { destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
      rewrite (KI a Hi Ho He (fun Hp => crt_pst_ro_B HB_segs HB_relro a Hp Hro)). exact (HROD a Hro Ho He).
    + apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) memc) _ (prh_lin Lamc) doc D HND).
      destruct (crt3_home_keep LAWS HPRE HTREE _ _ _ _ _ _ _ _ HJ) as (_ & (c0 & p0 & Hin0 & Hlo0 & Hhi0) & _).
      apply crt3o_agree. intros y [Hy | ((a & k) & Hb & Hy)]; apply KX.
      * left. exists c0, p0. split; [exact Hin0 | lia].
      * right. exists a, k. split; [exact (HDL _ Hb) | unfold pj_holdsR in Hy; cbn [fst snd] in Hy; exact Hy].
  - (* crt_live_blocks_perm *) rewrite EAB; exact HPA.
  - (* crt_live_saved *) intros j Hj. apply KSV; [lia | lia | exact (HSV j Hj)].
  - (* crt_frame *)
    pose proof (crt_frame_listed HFR) as Hin. pose proof (crt_frame_flag_word HFR) as Hrd.
    refine {| crt_frame_listed := Hin; crt_frame_flag_word := _; crt_frame_present := _ |}.
    + rewrite ?EF, ?EG. try fold F.
      rewrite <- Hrd. apply crt3_rdword_keep. intros j Hj. apply (KF CRT_CID pos); [exact Hin|]. fold F. rewrite HFB. lia.
    + rewrite ?EF. try fold F.
      intros a Ha. exact (PF CRT_CID pos a Hin Ha).
  - (* crt_live_fspill *)
    rewrite ?EF. try fold F.
    unfold crt_spill in *. apply KSV; [unfold CRT_SP_F; lia | unfold CRT_SP_F; lia | exact HSPF].
  - (* crt_live_copy_open *)
    rewrite !EF. fold F.
    exact (KRA CRT_OFF_COPY ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) HRAc).
  - (* crt_live_copy_hull *)
    rewrite !EF. fold F.
    intros s Hs. rewrite (KFS CRT_CID pos s HinF); [exact (HHVc s Hs)|]. fold F. rewrite HFB.
    unfold CRT_OFF_COPY in Hs. exact (crt3o_hull_in F s HF32 ltac:(lia) Hs).
  - (* crt_live_memnorm *) intros Hm. exact (HKM (HMN Hm)). }
split; [exact HDR|]. split; [exact H24|]. split; [exact Hsb|].
split; [unfold crt_spill in *; apply KSV; [unfold CRT_SP_SHN_B; lia | unfold CRT_SP_SHN_B; lia | exact HSP1]|].
split; [unfold crt_spill in *; apply KSV; [unfold CRT_SP_PN_B; lia | unfold CRT_SP_PN_B; lia | exact HSP2]|].
split; [unfold crt_spill in *; apply KSV; [unfold CRT_SP_N_B; lia | unfold CRT_SP_N_B; lia | exact HSP3]|].
split; [exact Hd8|].
split; [exact (proj2 (proj2 (crt3_home_keep LAWS HPRE HTREE _ _ _ _ _ _ _ _ HJ2)))|].
split; [exact (KRA CRT_OFF_BACK ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) HRAb)|].
split; [exact (KRA CRT_OFF_V ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) HRAv)|].
split; [exact Hcs|]. split; [exact Hcs0|].
split; [exact (crt3_fdR_frame SEGS DOC_D _ _ (prh_lin Lamc) _ Dc HFD AGc)|].
split; [exact Hcnt|]. split; [exact Hsb0|].
intros E1. destruct (Hsb1 E1) as (Hcw & Hnode & Htv & Hbs & Hpos & HCT & (Fc & HFo & HFom)).
split; [exact Hcw|].
split; [exact (pj_nodeR_frame SEGS tcB _ _ (prh_lin Lamc) _ Dc Hnode AGc)|].
split.
{ apply (crt3_tree_vis_keep B ARx LAWS ly2 Sc Hp2 W2 mem2 md2 Lamc peakc cntc SIZE_MAXZ ranc most 0 Dc HAR2 HLED2 HDc).
  intros a k Hin. destruct (Htv a k Hin) as (H1 & H2 & H3 & H4 & _). auto. }
split; [exact Hbs|]. split; [exact Hpos|]. split; [exact HCT|].
(* copy's ordered free list: same footprint agreement as copy's pj_nodeR *)
exists Fc. split; [|exact HFom].
exact (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) _ Dc Fc HFo
  (fun a k Hin => HDc (a, k) Hin) AGc).
Qed.

(* ---- CLOSED (the former WAITS block, 2026-10-30, crt head 71a8716672850d3): the kit's DEAD-PJSTRING / -PJSET
   make O1 the granted state only (Base: sbit = 1, ranc = 0), so the C4a exit to X (r = 1) is unreachable and
   crt3o_toX is deleted; the kit's FREEORD-COPY gives S copy's ordered free list, which O1 carries as
   crt3_copy_fo and crt3o_after carries across fuzz_alloc_ran_out by pj_foR_frame: crt_at_W_B_copy_fo below. ---- *)

(* ---- W (+0x2a4) from O1 at the post state: s5 = 1, s10 = O1's auipc; the crt_at_W_B record by name ---- *)
Lemma crt3o_toW : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc ranc rg mbs cset sbit rg',
  atO1 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc ranc rg mbs cset sbit ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 27]%bv -> getr rg' r = getr rg r) -> getr rg' 21 = w64 1 ->
  getr rg' 26 = w64 (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B) ->
  atW fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg' mbs cset.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc ranc rg mbs cset sbit rg' HO HK H21 H26.
destruct HO as (Ht & Hfz & Hfk & HL & HDR & H24 & Hsb & HSP1 & HSP2 & HSP3 & Hd8 & HRAd & HRAb & HRAv &
  Hcs & Hcs0 & HFD & Hcnt & Hsb0 & Hsb1).
subst ranc.
destruct (Hsb1 Hsb) as (Hcw & Hnode & Htv & Hbs & Hpos & HCT & HCF).
pose proof (crt_dregs_B_bregs HDR) as HBR.
assert (HDR' : dregsB rg' (F_ lyc pos)).
{ refine {| crt_dregs_B_bregs := {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _;
      crt_bregs_B_s0 := _; crt_bregs_B_s1 := _; crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _;
      crt_bregs_B_s7 := _; crt_bregs_B_s9 := _; crt_bregs_B_s11 := _ |}; crt_dregs_B_s6 := _ |}.
  - rewrite (HK 2%bv) by crt3o_in. exact (crt_bregs_B_sp HBR).
  - rewrite (HK 3%bv) by crt3o_in. exact (crt_bregs_B_gp HBR).
  - rewrite (HK 4%bv) by crt3o_in. exact (crt_bregs_B_tp HBR).
  - rewrite (HK 8%bv) by crt3o_in. exact (crt_bregs_B_s0 HBR).
  - rewrite (HK 9%bv) by crt3o_in. exact (crt_bregs_B_s1 HBR).
  - rewrite (HK 18%bv) by crt3o_in. exact (crt_bregs_B_s2 HBR).
  - rewrite (HK 20%bv) by crt3o_in. exact (crt_bregs_B_s4 HBR).
  - rewrite (HK 19%bv) by crt3o_in. exact (crt_bregs_B_s3 HBR).
  - rewrite (HK 23%bv) by crt3o_in. exact (crt_bregs_B_s7 HBR).
  - rewrite (HK 25%bv) by crt3o_in. exact (crt_bregs_B_s9 HBR).
  - rewrite (HK 27%bv) by crt3o_in. exact (crt_bregs_B_s11 HBR).
  - rewrite (HK 22%bv) by crt3o_in. exact (crt_dregs_B_s6 HDR). }
exact {| crt_at_W_B_obj := Ht; crt_at_W_B_frm_zero := Hfz; crt_at_W_B_fregs := Hfk; crt_at_W_B_live := HL;
         crt_at_W_B_dregs := HDR'; crt_at_W_B_s5 := H21; crt_at_W_B_s10_own := H26;
         crt_at_W_B_sp_shn := HSP1; crt_at_W_B_sp_pn := HSP2; crt_at_W_B_sp_n := HSP3;
         crt_at_W_B_doc_align := Hd8; crt_at_W_B_doc_open := HRAd; crt_at_W_B_back_open := HRAb;
         crt_at_W_B_v_open := HRAv; crt_at_W_B_cset_range := Hcs; crt_at_W_B_cset_mod := Hcs0;
         crt_at_W_B_cnt := Hcw; crt_at_W_B_copy := Hnode; crt_at_W_B_tree_vis := Htv;
         crt_at_W_B_live_bound := Hbs; crt_at_W_B_pos := Hpos;
         crt_at_W_B_copy_tblk := fun _ => proj1 HCT; crt_at_W_B_copy_fo := HCF;
         crt_at_W_B_copy_depth := proj2 HCT |}.
Qed.

Lemma crt3_O1 : STMT_X -> STMT_W -> STMT_O1.
Proof.
intros HXs HWs fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc ranc rg mbs cset sbit HO.
pose proof HO as (Ht & Hfz & Hfk & HL & HDR & H24 & Hsb & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsb0 & _).
destruct (crt_live_journal HL) as (WS0 & HJ0 & HB0). pose proof (crt_live_saved HL) as HSV.
pose proof (crt_side_ledger (crt_live_side HL)) as HLED. pose proof (crt_side_arodata (crt_live_side HL)) as HROD.
pose proof (prh_ledger_own B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc most 0 HLED) as HOWN.
pose proof HPRE as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & HROD0 & HSHI0 & HRAC0 & _).
pose proof (crt3_sp0 HPRE) as (Hal16 & Hceil & H47 & Hshi).
pose proof (crt3_sp1 HPRE) as (Hs32 & Hs1 & Hs10).
pose proof crt3_stk as Hstk.
pose proof (YM05.alloc_ceiling_val) as Hcv.
pose proof HJ0 as (_ & Hly0 & _).
pose proof Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _).
pose proof (crt_dregs_B_bregs HDR) as HBR.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3.
pose proof (crt_bregs_B_tp HBR) as R4. pose proof (crt_bregs_B_s0 HBR) as R8.
assert (HBv : 4096 <= BASE <= 2 ^ 30).
{ rewrite HB_base. split; vm_compute; intro Hx; discriminate Hx. }
assert (Hown : 0 <= @pi_g_own_ran_out prh_img_B < 2 ^ 40).
{ split; vm_compute; [intro Hx; discriminate Hx | reflexivity]. }
assert (Hgz : @pi_gz_own_ran_out prh_img_B = 1%nat) by (vm_compute; reflexivity).
destruct (crt3_chain HPRE _ _ _ _ _ _ _ _ HJ0 HSV) as (ch1 & Hch1 & _).
(* ---- the symbolic state at O1 ---- *)
set (E := @Eimg _ B_prog_listing PA (Ereg rg [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg rg []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (U254 : bv_unsigned (ew E (A_OBJ 13)) = @pi_g_own_ran_out prh_img_B).
{ rewrite (HEI (A_OBJ 13)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). exact (crt3_own13 HB_base HB_segs). }
assert (HS : st_ok_pi (fx := fxk) SEGS VAL E crt3o_ss
  (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_O1_OFF_B))) memc (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold crt3o_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold crt3o_rown, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U254.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (@pi_g_own_ran_out prh_img_B) 0 1 (SLit 0) 0).
    + reflexivity.
    + lia.
    + lia.
    + rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat. rewrite <- Hgz. exact (proj1 HOWN).
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS crt3o_Bx [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose (RUN := Crt102Kit.crt_run_xw (fx := fxk) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS WS0).
pose (RUNTO := Crt102Kit.crt_run_to_xw (fx := fxk) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS WS0).
pose (BR := YSRrG.paj_branchR (fx := fxk) (PI := PA) (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)).
unfold crt_cfg.
(* ---- +0x288 .. +0x298: auipc, lbu g_own_ran_out (= 0), addi s5, bnez (falls through), jal fuzz_alloc_ran_out ---- *)
pose proof HJ0 as HJ.
paj_run_tok_x RUN HS HJ SHOK (0, 0);
  [unfold crt3o_ss; cbn [ss_mem]; apply awr_ok_cons_ro; [unfold crt3o_rown; cbn; lia | apply awr_ok_nil] |].
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg ?m1 _) _ => rename m1 into ms1 end.
assert (Emem1 : ms_mem ms1 = memc).
{ apply Stdlib.Logic.FunctionalExtensionality.functional_extensionality. intros xw. apply HF.
  intros (r & Hin & Hr). unfold crt3o_ss in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  unfold crt3o_rown in Hr. cbn in Hr. lia. }
clear HF HFr HG.
pose proof (regs_kept_of_st_ok SEGS E _ _ rg [] [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 27]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as KR1.
cbn [ms_regs restrict] in KR1.
prreg HS (1%bv : bv 5) R1.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ (* fuzz_alloc_ran_out has no wild site: the budgeted call rule at its empty budget, P := (fun WS1 => WS1 = []),
     over R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf; the callee's plain text lifted (YA0nH.SRr_SRr',
     apost_base_x_R_lift at YA0nH.wle_wle') and its post by YCbqGwild.apost_base_xb_of_xR; the caller's journal stays
     at its budget WS0 *)
  eapply (YCbqGwild.aj_call_xb_spR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)
    (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf)
    (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc _ _ ms1 STKC sp0
    [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc _ kj WS0 (@STK_fuzz_alloc_ran_out prh_img_B) [] (sp1 - sp0) _ ch1
    (fun WS1 => WS1 = []) _ HS eq_refl HJ).
  - unfold spZ at 1. rewrite (KR1 2%bv) by crt3o_in. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact (proj1 (crt_sp1_off _ Hal16)).
  - lia.
  - pose proof crt_stk_nonneg_B as (_ & _ & _ & _ & _ & _ & _ & _ & HSR & _). exact HSR.
  - pose proof crt_stk_B as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSR & _). rewrite crt3_pi_frame in HSR. lia.
  - rewrite (KR1 3%bv) by crt3o_in. rewrite R3. exact Hgp0.
  - rewrite (KR1 4%bv) by crt3o_in. rewrite R4. exact Htp0.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | vm_compute; reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - rewrite Emem1. replace (sp0 + (sp1 - sp0)) with sp1 by lia. unfold s0Z. rewrite (KR1 8%bv) by crt3o_in. rewrite R8.
    unfold w64. rewrite unsigned_lit_small by lia. exact Hch1.
  - intros HP1.
    pose proof HROD as HROD1. rewrite <- Emem1 in HROD1.
    pose proof HLED as HLED1. rewrite <- Emem1 in HLED1.
    assert (HSH : spZ (ms_regs ms1) + 64 <= ly_stk_hi lyc).
    { unfold spZ at 1. rewrite (KR1 2%bv) by crt3o_in. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
    assert (HRA : raZ (ms_regs ms1) < YM05.alloc_ceiling).
    { unfold raZ. rewrite R1. rewrite unsigned_lit_small by lia. lia. }
    eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
    { exact (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf _ _ _
        (HRO fxk lyc Sc Hpc Wc (ms_regs ms1) (ms_mem ms1) _ ch1 Lamc peakc cntc SIZE_MAXZ ranc most 0
          (conj HP1 (conj HROD1 (conj HSH (conj HRA Hfz)))) HLED1)). }
    intros W' c' _ Hpo. apply YCbqGwild.apost_base_xb_of_xR; [reflexivity|].
    eapply (apost_base_x_R_lift SEGS B PST ARx); [exact (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact Hpo].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
(* ---- after the call: O1 again at the callee's post state ---- *)
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW & HJ2 & HJ1 & HP2 &
  (HQ & HKM)).
subst WS1. rewrite app_nil_r in HJ2.
destruct HQ as (HROOMk & HR10 & -> & -> & EAB & HLED2).
rewrite Emem1 in HJ, HJ1, HKM.
replace (sp0 + (sp1 - sp0)) with sp1 in HJ1 by lia.
pose proof (crt3o_after fxk lyc Sc Hpc Wc memc _ kj pos Dc Lamc peakc cntc ranc rg mbs cset sbit _ ly2 Hpc W2 mem2 md2 k1
  (crt3o_jnl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HO HJ HB0) HJ1 (ex_intro _ WS0 (conj HJ2 HB0)) EAB HLED2 HKM)
  as HO2.
jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H W2) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)). rewrite <- restrict_mkst_fx in HS2.
remember (havoc E 32 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS2.
assert (HIM2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 32)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply ew_havoc_old; exact Hn).
assert (E2a0 : ew E2 36 = Z_to_bv 64 ranc) by (rewrite HE2; unfold w64 in HR10; rewrite <- HR10; reflexivity).
assert (HAE2 : env_agree 32 (Ereg rg []) E2) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (E2s8 : ew E2 24 = Z_to_bv 64 sbit).
{ rewrite OLD2 by lia. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat rg [] 24 24%bv eq_refl).
  exact H24. }
assert (U315 : bv_unsigned (ew E2 (A_HI 35)) = @pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B).
{ rewrite (HIM2 (A_HI 35)) by (unfold A_HI, A_TEXT, A_LIM; lia). exact (crt3_hi35 HB_base HB_segs). }
cbn [A_HI Nat.add] in U315.
clear HE2.
clear HS SHOK HJ HJ1. rename HS2 into HS. rename HJ2 into HJ.
assert (SHOK : sh_ok SEGS crt3o_Bx [] E2 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
(* ---- +0x29c: bnez a0 (a0 = g_ran_out = ranc = 0 at O1): the C4a exit to X is dead ---- *)
psrr_branch_tok RUN BR HS SHOK (0, 0).
- exfalso.
  rewrite branch_ne_U, (U_atom E2 36 ranc E2a0 ltac:(lia)), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
  rewrite Hsb0 in Hc. cbn in Hc. discriminate Hc.
- clear Hc.
  paj_run_tok_x RUN HS HJ SHOK (0, 0); [apply awr_ok_nil |].
  lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg ?m4 _) _ => rename m4 into ms4 end.
  assert (Emem4 : ms_mem ms4 = mem2).
  { apply Stdlib.Logic.FunctionalExtensionality.functional_extensionality. intros xw. apply HF.
    intros (r & Hin & _). cbn in Hin. exact Hin. }
  clear HF HFr HG.
  (* ---- +0x2a0: beqz s8 (s8 = sbit = 1 at O1): the `!set` abort is dead ---- *)
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  + exfalso.
    rewrite branch_eq_U, (U_atom E2 24 sbit E2s8 ltac:(lia)), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
    rewrite Hsb in Hc. cbn in Hc. discriminate Hc.
  + clear Hc.
    paj_run_to_tok_x RUNTO HS HJ SHOK (0, 0) (CRT_PC_B + CRT_W0_OFF_B); [apply awr_ok_nil |].
    lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg ?m5 _) _ => rename m5 into ms5 end.
    assert (Emem5 : ms_mem ms5 = mem2).
    { rewrite <- Emem4. apply Stdlib.Logic.FunctionalExtensionality.functional_extensionality. intros xw. apply HF.
      intros (r & Hin & _). cbn in Hin. exact Hin. }
    clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi (PI := PA) E2 _ _ rg [] [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 27]%bv HS HAE2
      ltac:(vm_compute; reflexivity)) as KR5.
    cbn [ms_regs restrict] in KR5.
    prreg HS (21%bv : bv 5) R21.
    pose proof (st_ok_pi_restrict_reg (PI := PA) _ _ _ _ 26%bv HS) as R26.
    lazymatch type of R26 with _ = sv_denot _ (sr_get (ss_regs ?s) _) =>
      let e := eval vm_compute in (sr_get (ss_regs s) 26%bv) in change (sr_get (ss_regs s) 26%bv) with e in R26 end.
    cbn [sv_denot ms_regs restrict] in R26. rewrite U315, Z.add_0_r in R26.
    pmkst HS.
    rewrite Emem5 in HJ |- *.
    apply (HWs fxk ly2 Sc Hpc W2 mem2 _ (kj + k1) pos Dc Lamc peakc cntc (ms_regs ms5) mbs cset).
    apply (crt3o_toW fxk ly2 Sc Hpc W2 mem2 _ (kj + k1) pos Dc Lamc peakc cntc ranc rg mbs cset sbit (ms_regs ms5)
      (crt3o_jnl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HO2 HJ HB0) KR5).
    * rewrite R21. reflexivity.
    * exact R26.
Qed.

End g.
End f.
End t3s.
