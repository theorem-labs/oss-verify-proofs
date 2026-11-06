(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PvB_NA.v, with its module paths and module names changed; 22 of its 51 lines of code are new or changed and 930 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrsBoundBp.v, with its module paths and module names changed; 78 of its 115 lines of code are new or changed and 14 lines of the source are left out. *)
(* fuzz_preset, image B' (the #102 pins, asan-ubsan): the two BRIDGES that turn the crcs walk's two shared interims
   into citations of the callee texts of lib/A/PRH_*.v (the whole set
   is on this branch by path):
   - crs_wexact_of_text_B: tpj_write_specX (lib/A/PRH_FnWriter.v blob 2b497bc72172) gives crs_wexact_B
     (lib/B/Prog/CrsWexBp.v) at every C. The text states prh_granted itself (DEAD-PJWRITE) and its advance under
     it; lib/A/PRH_Supply.v's prhWriter_pjw_evs_granted,
     prhWriter_pjw_evs_w_evs and prhWriter_pjw_evs_w_starved name the call's events as the model's w_evs / w_starved,
     whose count and pick are PjWriteHyp's and ck_pick's by CrsKitBp.crs_wcalls_bridge_B / crs_pick_bridge_B. Side
     condition kept as a premise: cf_head = PresetReqAt.HEAD (16 at CfParams_preset; the top discharges it by
     computation).
   - crs_free0_of_text_B: tfuzz_free_specX (lib/A/PRH_FnAlloc.v on the kit's cut, post-implication form) at p = 0
     gives crs_free0_B (lib/B/Prog/CrsFree0Bp.v): its p = 0 arm keeps the state (S' = S), so room_live_cf S' follows
     from room_live_cf S, and the text asks no position and no class-24 bound of a NULL free. The cut's admission
     premise and budgeted post are met by the trace being FIXED (YCbqG.admits_ct_fix, PRH_Base.fpost_of_fpostb_fix).
   DONOR (rule 24, reuse): the A' bridges lib/A/Prog/CrsBridgeAp.v blob 4714c9a8aa0a (a working branch
   3adfdcc651aa), restated at the B' instance. Both texts and both interims are image-free in shape, so the two
   proofs are the A' ones at prh_img_B / PI_prog_B.
   rule 24: proves no function (kind: two kit lemmas of the walk of check_reject_clean_starved; reuse search: `proof-index
   check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an internal record of that lookup; CONFIRM by
   checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B, its released rows were lib/Prog (plain) and
   lib/U/Prog (ubsan) only, and no released asan Proof.v existed for check_reject_clean_starved).
   INPUTS. Pin B' asan-ubsan sha256 d663f82d7f488d30 (release/fuzz-preset-ran-out-pins 8f3e7e1a07f1), unstripped twin
   ELF sha256 c90d4fa54d43160baf62e5aa387211a798dddbad13d2619d85acbf37aee0c175; listing lib/B/Listing_prog.v
   c97cc46b3e13 + lib/B/PAImg_prog.v 15fab93fe702; image record lib/B/PRH_ImgB.v 3216eca68342; the kit texts as above;
   the kit lib/B/Prog/CrsKitBp.v with lib/B/Prog/CrsWexBp.v and CrsFree0Bp.v.
   Numerals: 2 ^ 62 (DERIVED: the kit's count bound), 2 ^ 28 (prhWriter_WMAX, LENGTH), 2 ^ 64 / 2 ^ 64 - 1 (WORD: the
   counter's width, SIZE_MAX). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnWriter PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Supply.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CrsModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import CrsKitBp CrsWexBp CrsFree0Bp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* ONE call: tpj_write_specX at depth DOC_D gives crs_wcall_B, for evs the model's events of that call *)
Lemma crs_wcall_of_text_B : forall (fx' : YK11.FPState) (CTX0 : list (list Z)) (C : crsC_B)
  (pretty : Z) (inj : bool) (evs0 evs : list PresetReqAt.hev),
  cf_head = PresetReqAt.HEAD ->
  evs = (if inj
         then PresetReqAt.w_starved (cb_t C) (negb (pretty =? 0))
                (PresetReqAt.pick (cb_tb C) (PresetReqAt.wcalls (cb_t C) (negb (pretty =? 0))))
         else PresetReqAt.w_evs (cb_t C) (negb (pretty =? 0))) ->
  tpj_write_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0 DOC_D ->
  crs_wcall_B (fx := fx') B ARx CTX0 C pretty inj evs0 evs.
Proof.
intros fx' CTX0 C pretty inj evs0 evs Hhd Hevs HT.
unfold crs_wcall_B.
intros rp_hist ly S Hp W regs mem md ch Lam peak cnt fail ran Hfail Hran Hcnt
  P1 P2 P3 P4 P4b P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21.
pose proof P9 as LB. apply prh_ledger_bounds in LB. destruct LB as (_ & _ & Hc64 & Hf64 & _).
pose proof (HT (cb_rp_x C) (cb_rp_os C) (cb_rp_i C + length evs0)%nat (cb_rp_H0 C) rp_hist
  (cb_most C) 0 ly S Hp W regs mem md ch (cb_doc C) pretty (cb_t C) (cb_D C) Lam peak cnt fail ran
  P1 P2 P3 P4 P4b P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21) as H.
unfold YA0nH.SRr' in H |- *.
eapply YA0nH.SRrG_mono; [exact H|].
intros W' c' _ HP.
unfold fpostFm, fpostF, apost_base_xF, fQmn in HP |- *.
destruct HP as (fx'' & ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hz & Hk & HJ & Hpr & HQ & Hmn).
exists fx'', ly', S', Hp', regs', mem', md', k.
split; [exact Hc|]. split; [exact Hz|]. split; [exact Hk|]. split; [exact HJ|]. split; [exact Hpr|].
split; [|exact Hmn].
destruct HQ as (ok & ran' & q & Lam' & peak' & HQ). cbv zeta in HQ.
destruct HQ as (Hoks & Hq & Hroom & Hg & Hgr & Hnode & Htv & HL & Hdisj).
exists ok, ran', q, Lam', peak'. cbv zeta.
refine (conj Hoks (conj Hq (conj Hroom (conj Hg (conj Hgr (conj Hnode (conj Htv (conj HL (conj Hdisj _))))))))).
intros _.
destruct (Hgr Hg) as (hist' & Hpos). exists hist'.
(* the call's events are the model's *)
assert (Hwc : Z.of_nat (PresetReqAt.wcalls (cb_t C) (negb (pretty =? 0))) <= 2 ^ 28).
{ unfold prhWriter_WMAX in P19.
  assert (W0 := crs_wN_le (cb_t C) (negb (pretty =? 0)) ltac:(unfold PjWriteHyp.wlen; lia)).
  unfold PjWriteHyp.wlen in W0. rewrite <- crs_wcalls_bridge_B. unfold PjWriteHyp.wcalls. lia. }
assert (Elen : prhWriter_pjw_evs ok cnt fail (WriterValue.wdpieces (cb_t C) (negb (pretty =? 0))) = evs).
{ rewrite (PRH_Supply.prhWriter_pjw_evs_granted _ ok cnt fail (proj1 Hc64) (proj2 Hf64) Hg).
  rewrite Hevs. destruct inj; cbv beta iota in Hfail |- *.
  - pose proof (crs_wcalls_pos_B (cb_t C) (negb (pretty =? 0))) as Hp1.
    rewrite crs_wcalls_bridge_B, (crs_pick_bridge_B _ _ Hp1) in Hfail.
    pose proof (crs_pick_lt (cb_tb C) (Z.of_nat (PresetReqAt.wcalls (cb_t C) (negb (pretty =? 0)))) ltac:(lia))
      as Hlt.
    rewrite (crs_pick_bridge_B _ _ Hp1) in Hlt.
    apply (PRH_Supply.prhWriter_pjw_evs_w_starved (cb_t C) _ cnt fail _ Hhd (proj1 Hc64) Hfail (proj2 Hf64)).
    lia.
  - apply (PRH_Supply.prhWriter_pjw_evs_w_evs (cb_t C) _ cnt fail Hhd Hc64).
    intros j Hj. rewrite Hfail. unfold SIZE_MAXZ.
    rewrite Z.mod_small by lia. lia. }
rewrite Elen in Hpos. exact Hpos.
Qed.

(* BRIDGE 1: the whole interim crs_wexact_B, from the text at every float state *)
Lemma crs_wexact_of_text_B : cf_head = PresetReqAt.HEAD -> forall CTX0,
  (forall fx', tpj_write_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0 DOC_D) ->
  forall C, crs_pre_B B ARx CTX0 C ->
  forall fx', crs_wexact_B (fx := fx') B ARx CTX0 C.
Proof.
intros Hhd CTX0 HT C _ fx'. unfold crs_wexact_B.
split; [|split; [|split]]; apply (crs_wcall_of_text_B fx'); try exact Hhd; try exact (HT fx'); reflexivity.
Qed.

(* BRIDGE 2: the NULL free, from the kit's NULL-only text tfuzz_free_null_specX (PRH_FnAlloc.v), plain on purpose: no call
   is made, so the post holds at wle. crs_free0_B's room and trace premises go unused; room_live_cf S' from S' = S *)
Lemma crs_free0_of_text_B :
  (forall fx', tfuzz_free_null_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK) ->
  forall fx', crs_free0_B (fx := fx') B ARx.
Proof.
intros HT fx'. unfold crs_free0_B.
intros most own ly S Hp W regs mem md ch Lam peak cnt fail ran Hpre Hroom _ Hr0 HL.
refine (SRr_mono _ _ _ _ _ (HT fx' most own ly S Hp W regs mem md ch Lam peak cnt fail ran Hpre Hr0 HL) _).
intros W' c' _ HP.
unfold fpostm, fpost, apost_base_x, fQmn in HP |- *.
destruct HP as (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & Hpr & HQ & Hmn).
exists ly', S', Hp', regs', mem', md', k.
split; [exact Hc|]. split; [exact HJ|]. split; [exact Hpr|]. split; [|exact Hmn].
destruct HQ as (ES & EHp & Eab & HL').
split; [rewrite ES; exact Hroom|]. split; [exact ES|]. split; [exact EHp|]. split; [exact Eab | exact HL'].
Qed.

End f.
End d.
