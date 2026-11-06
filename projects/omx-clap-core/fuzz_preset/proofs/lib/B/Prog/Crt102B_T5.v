(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 104 of its 139 lines of code are new or changed and 479 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): row T5 at the re-hiding contract.
   crtB_T5's text is unchanged; CRT_B_SEG_T5 (CRT_B_AT_L3 -> CRT_B_AT_C -> CRT_B_AT_L0) now
   means its three cuts at YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf. The journal at R := YA0nH.wle' SEGS RZ_cf. No HOS4
   and no hull: the row's only callee is strcmp. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan d663f82d7f488d30,
   unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T5 (CRT-B-L012): L0 (+0x478) -> L1 (+0x4f8, the
   at-search) -> L2 (+0x56c) -> L3 (+0x5b4) / C (+0x6f8), 79 instructions, fuzz_preset.c new:740-748;
   crtB_T5 : CRT_B_SEG_T5 (lib/A/Prog/Crt102Glue.v, the frozen text)
   at the B' instance.

   proves no function (kind: segment lemma).

   THE WALK. ct5_L0 (Crt102B_T5_L0.v): L0 -> L1 at i = 0 (doc->n > 0) or L2 (doc->n = 0); ct5_L1 (Crt102B_T5_L1.v):
   L1 at i -> `__wrap_strcmp (doc->keys[i], MOD_AT)` -> K -> L1 at i + 1 or L2, by induction on doc->n - i (the
   invariant: no key before i is "modifiedAt", Crt102Model.cm_at_inv); ct5_L2 (Crt102B_T5_L2.v): L2 -> L3 (i = 0) or
   C. The new:740 abort is not taken (ct5_granted, Crt102B_T5_bd.v: the rewrite's pj_write is granted, so saved <> 0
   and rc = 0), nor the new:748 abort (back.n = doc->n + (at == doc->n)), nor the UBSan traps (the symbolic runner).
   Named hypotheses: ASTRCMP (as in row T6), BOK / IMGVIS (as in row T7) and the text's own premises (HRQA, the
   text's RQA_crt t <= most, closes the writer's refusal: every request of the rewrite's pj_write is at most RQW,
   ct5_wreq_le in Crt102B_T5_bd.v).

   KB ROUND (the wild budget, Crt102Glue.v's G3 / G4): crt_at_L0_B, crt_at_L3_B and crt_at_C_B carry crt_live at kb =
   prh_wk F_check_round_trip, and so do the row's inner cuts (the notation liveB); the stretch files keep the journal's
   budget across their runs and strcmp calls. crtB_T5's statement is unchanged.

   INPUTS OF RECORD: base commit cbe6d10993c2 (candidate base) (Crt102Glue.v, Crt102Model.v,
   lib/B/Prog/Crt102KitB.v, lib/A/Prog/Crt102Kit.v, lib/A/PRH_Supply.v, lib/A/PRH_PjOrder.v pj_foR_frame); lib/B/Prog/Crt102B_T7_kit.v /
   Crt102B_T7_tree.v BY PATH as in Crt102B_T6.v; rows T6's Crt102B_T6_st.v / Crt102B_T6.v.
*)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp WriterSpec PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck PRH_FnEx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc PRH_Supply.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102KitB Crt102B_T6_st Crt102B_T7_kit Crt102B_T7_tree Crt102B_T6 Crt102B_T5_bd Crt102B_T5_L2 Crt102B_T5_L1 Crt102B_T5_L0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
(* The re-hiding move's world relation and step relation (YA0nH), the zone (YGcfRehidePost) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

Section t5w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
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
#[local] Notation TEB := (TE (L := B_prog_listing) (PA := PA)).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* The re-hiding move: the journal at R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf *)
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z).
(* tcheck_round_trip_specX's premises at the entry this row reads (PRH_FnCheck.v, the text's own; Crt102Top
   discharges them) *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
Hypothesis HMN : YAkMemnorm.memnorm SEGS mem.
Hypothesis HREAD : ck_read x = Some t.
Hypothesis HLENX : Z.of_nat (length x) <= 3 * 2 ^ 20.
Hypothesis HWL0 : PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x).
Hypothesis HWL1 : PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54.
Hypothesis HCNT : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis HLED0 : prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0.
(* the text's own request bound (PRH_FnCheck.v tcheck_round_trip_specX): every ledger request is within g_most *)
Hypothesis HRQA : RQA_crt t <= most.
(* the read-only string "modifiedAt" the at-search compares with: the text's own `kept_img B a_mod_at 11` at the
   instance's a_mod_at := CRT_MOD_AT_B (Crt102Img.v:1024) *)
Hypothesis HKMA : @kept_img _ B_prog_listing PA B (@CRT_MOD_AT_B _ PA) (Z.of_nat (length ck_MOD_AT) + 1).
(* NAMED HYPOTHESES BOK (asyms_ok B; owner image B's start-up record) and IMGVIS (the image's shadow is
   visible in every ARx state; owner the instance owner, img_shadow_vis_cf), as row T7's Crt102B_T7_tree.v takes them for its
   read-only strcmp operands (cb7t_rom_prem_mod_at) *)
Hypothesis BOK : asyms_ok B.
Hypothesis IMGVIS : forall ly S Hp (W : world SEGS) mem md a,
  ARx ly S Hp W mem md -> @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* THE CALLEE TEXTS, each at ANY float state.
   NAMED HYPOTHESIS ASTRCMP (owner: the libc strcmp row): the __wrap_strcmp row in its read-only-premise form WITH the memnorm
   keep (YGcallMxmn.v:898 astrcmp_realizes_xrom). The _xro form (:849) is not enough here: crt_live's last field
   (Crt102Glue.v crt_live_memnorm, `memnorm mem -> memnorm memc`) must hold again after the call, and astrcmp_realizes_xro's post
   (YGcallMxmn.v:866-873) keeps no memnorm.
   *)
Hypothesis ASTRCMP : forall fxk : YK11.FPState,
  astrcmp_realizes_xrom (fx := fxk) SEGS B ARx RLO RHI (SIGMA AS___wrap_strcmp).
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (@CRT_sp1 regs).
#[local] Notation liveB := (crt_live (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc)
  (t := t) (D := D) (Lam := Lam) (peak := peak) (most := most) (prh_wk F_check_round_trip)).
#[local] Notation L3B := (crt_at_L3_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation CB := (crt_at_C_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation QFb := (QF (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation cfgB := (crt_cfg (rc := rc) (L := B_prog_listing) (PA := PA) (CRT_PC := CRT_PC_B)).

#[local] Notation ENT := (ct6_entry B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam
  peak cnt most HPRE HTREE).
#[local] Notation L0B := (crt_at_L0_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).


#[local] Notation ATL1 Pd j ms := (@CT5_AT_L1 fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D
  Lam peak cnt ran most Pd j ms).

Theorem crtB_T5 : CRT_B_SEG_T5 (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (CRT_PC := CRT_PC_B) (CRT_C_OFF := CRT_C_OFF_B) (CRT_L3_OFF := CRT_L3_OFF_B) (CRT_L0_OFF := CRT_L0_OFF_B)
  (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly)
  (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam)
  (peak := peak) (cnt := cnt) (ran := ran) (most := most).
Proof.
intros HL3 HC.
set (Pd := fun (_ _ : list (Z * Z)) (_ : Z) (_ : list (list Z * PjTree.jv)) => True).
assert (AL3 : @CT5_ATL3 fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran most
  Pd).
{ intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i H _.
  exact (HL3 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i H). }
assert (AC : @CT5_ATC fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran most
  Pd).
{ intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw H _.
  exact (HC fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw H). }
pose proof (ct5_L2 B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HTREE Pd AL3 AC) as AL2.
assert (AL1 : forall d i ms, (length ms - i <= d)%nat -> ATL1 Pd i ms).
{ induction d as [|d IHd]; intros i ms Hd.
  - intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw kd HL1 _. exfalso.
    destruct HL1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). lia.
  - apply (ct5_L1 B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
      HPRE HTREE HMN HKMA BOK IMGVIS ASTRCMP Pd AL2 i ms). intros j Hj. apply IHd. lia. }
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd H.
exact (ct5_L0 B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HTREE HMN HREAD HLENX HWL0 HWL1 HCNT HLED0 HRQA Pd (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => I)
  (fun ms' => AL1 _ 0%nat ms' (le_n _)) AL2 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd H).
Qed.

End g.
End f.
End t5w.
