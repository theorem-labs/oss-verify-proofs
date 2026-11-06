(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module paths and module names changed; 671 of its 740 lines of code are new or changed and 859 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/CrsKitAp.v; 14 of its 44 lines of code are new or changed and 710 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/CrsFree0Ap.v; 82 of its 113 lines of code are new or changed and 13 lines of the source are left out. *)
(* fuzz_preset, image A' (the #102 pins): the two BRIDGES that turn the crcs walk's two shared interims into citations
   of the texts:
   - crs_wexact_of_text: tpj_write_specX (lib/A/PRH_FnWriter.v:1142-1223) gives crs_wexact (lib/A/Prog/CrsWexAp.v) at
     every C. The text states prh_granted (DEAD-PJWRITE, :1198) and its advance under it; lib/A/PRH_Supply.v's
     prhWriter_pjw_evs_granted, prhWriter_pjw_evs_w_evs and prhWriter_pjw_evs_w_starved name the call's events as the
     model's w_evs / w_starved, whose count and pick are PjWriteHyp's and ck_pick's by CrsKitAp.crs_wcalls_bridge /
     crs_pick_bridge. Side condition kept as a premise: cf_head = PresetReqAt.HEAD (16 at CfParams_preset; the top
     discharges it by computation).
  - crs_free0_of_text: the NULL-only free text tfuzz_free_null_specX (lib/A/PRH_FnAlloc.v; plain SRr, fpostm, no room
    invariant and no trace premise: a NULL free frees nothing) gives crs_free0 (lib/A/Prog/CrsFree0Ap.v): one SRr_mono,
    the post unpacked; its S' = S keeps the state, so room_live_cf S' follows from room_live_cf S, and crs_free0's own
    trace premise is not used.
   rule 24: proves no function (kind: two kit lemmas of the walk of check_reject_clean_starved; reuse search:
   `proof-index check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an
   internal record of that lookup; CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had
   no lib/A or lib/B, its released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan
   Proof.v existed for check_reject_clean_starved). Written new.
   INPUTS. Pin A' asan sha256 1be0f53d96cb9d6c (release/fuzz-preset-ran-out-pins 8f3e7e1a07f1); listing
   lib/A/Listing_prog.v 7ed1529926bd + lib/A/PAImg_prog.v 505a51ff7d08; the texts as above; the kit
   lib/A/Prog/CrsKitAp.v, CrsWexAp.v (728f24e66ca9 from commit 4828568cb5e3, with kit v4's one added
   premise cnt < 2 ^ 62), CrsFree0Ap.v (79d50622a638 from commit 0165ddc6d5d0).
   Numerals: 2 ^ 62 (DERIVED: the kit's count bound), 2 ^ 28 (prhWriter_WMAX, LENGTH), 2 ^ 64 / 2 ^ 64 - 1 (WORD:
   the counter's width, SIZE_MAX). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnWriter PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Supply.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CrsModel CrsKitAp CrsWexAp CrsFree0Ap.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (PI_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* ONE call: tpj_write_specX at depth DOC_D gives crs_wcall, for evs the model's events of that call. The text's
   premises are discharged by shape (eassumption per premise), so a premise the text adds needs no edit here beyond
   supplying it: the run's call bound (length rp_os <= 4) comes from crs_pre *)
Lemma crs_wcall_of_text : forall (fx' : YK11.FPState) (CTX0 : list (list Z)) (C : crsC) (pretty : Z)
  (inj : bool) (evs0 evs : list PresetReqAt.hev),
  cf_head = PresetReqAt.HEAD ->
  (length (c_rp_os C) <= 4)%nat ->
  evs = (if inj
         then PresetReqAt.w_starved (c_t C) (negb (pretty =? 0))
                (PresetReqAt.pick (c_tb C) (PresetReqAt.wcalls (c_t C) (negb (pretty =? 0))))
         else PresetReqAt.w_evs (c_t C) (negb (pretty =? 0))) ->
  tpj_write_specX (fx := fx') (PI := prh_img_A) (PA := PA) B ARx SK CTX0 DOC_D ->
  crs_wcall (fx := fx') B ARx CTX0 C pretty inj evs0 evs.
Proof.
intros fx' CTX0 C pretty inj evs0 evs Hhd Hlen Hevs HT.
unfold crs_wcall.
intros rp_hist ly S Hp W regs mem md ch Lam peak cnt fail ran Hfail Hran Hcnt.
intros.
assert (LB : prh_ledger B ly S Hp W mem Lam peak cnt fail ran (c_most C) 0) by assumption.
assert (P19 : Z.of_nat (length (WriterValue.wdoc (c_t C) (negb (pretty =? 0)))) + 1 <= prhWriter_WMAX) by assumption.
apply prh_ledger_bounds in LB. destruct LB as (_ & _ & Hc64 & Hf64 & _).
eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
{ eapply (HT (c_rp_x C) (c_rp_os C) (c_rp_i C + length evs0)%nat (c_rp_H0 C) rp_hist (c_most C) 0
    ly S Hp W regs mem md ch (c_doc C) pretty (c_t C) (c_D C) Lam peak cnt fail ran); eassumption. }
intros W' c' _ HP.
unfold fpostFm, fpostF, apost_base_xFR, fQmn in HP |- *.
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
assert (Hwc : Z.of_nat (PresetReqAt.wcalls (c_t C) (negb (pretty =? 0))) <= 2 ^ 28).
{ unfold prhWriter_WMAX in P19.
  assert (W0 := crs_wN_le (c_t C) (negb (pretty =? 0)) ltac:(unfold PjWriteHyp.wlen; lia)).
  unfold PjWriteHyp.wlen in W0. rewrite <- crs_wcalls_bridge. unfold PjWriteHyp.wcalls. lia. }
assert (Elen : prhWriter_pjw_evs ok cnt fail (WriterValue.wdpieces (c_t C) (negb (pretty =? 0))) = evs).
{ rewrite (PRH_Supply.prhWriter_pjw_evs_granted _ ok cnt fail (proj1 Hc64) (proj2 Hf64) Hg).
  rewrite Hevs. destruct inj; cbv beta iota in Hfail |- *.
  - pose proof (crs_wcalls_pos (c_t C) (negb (pretty =? 0))) as Hp1.
    rewrite crs_wcalls_bridge, (crs_pick_bridge _ _ Hp1) in Hfail.
    pose proof (crs_pick_lt (c_tb C) (Z.of_nat (PresetReqAt.wcalls (c_t C) (negb (pretty =? 0)))) ltac:(lia)) as Hlt.
    rewrite (crs_pick_bridge _ _ Hp1) in Hlt.
    apply (PRH_Supply.prhWriter_pjw_evs_w_starved (c_t C) _ cnt fail _ Hhd (proj1 Hc64) Hfail (proj2 Hf64)).
    lia.
  - apply (PRH_Supply.prhWriter_pjw_evs_w_evs (c_t C) _ cnt fail Hhd Hc64).
    intros j Hj. rewrite Hfail. unfold SIZE_MAXZ.
    rewrite Z.mod_small by lia. lia. }
rewrite Elen in Hpos. exact Hpos.
Qed.

(* BRIDGE 1: the whole interim crs_wexact, from the text at every float state *)
Lemma crs_wexact_of_text : cf_head = PresetReqAt.HEAD -> forall CTX0,
  (forall fx', tpj_write_specX (fx := fx') (PI := prh_img_A) (PA := PA) B ARx SK CTX0 DOC_D) ->
  forall C, crs_pre B ARx CTX0 C ->
  forall fx', crs_wexact (fx := fx') B ARx CTX0 C.
Proof.
intros Hhd CTX0 HT C HP fx'. unfold crs_wexact.
assert (Hlen : (length (c_rp_os C) <= 4)%nat) by (unfold crs_pre in HP; tauto).
split; [|split; [|split]]; apply (crs_wcall_of_text fx'); try exact Hhd; try exact Hlen; try exact (HT fx'); reflexivity.
Qed.

(* BRIDGE 2: the NULL free, from the NULL-only text tfuzz_free_null_specX at every float state. On the NULL path
   fuzz_free frees nothing, so the text is plain (SRr, fpostm) and asks neither a room invariant nor a trace; crs_free0
   keeps its own premises, and its room conjunct after the call is the entry's (S' = S) *)
Lemma crs_free0_of_text :
  (forall fx', tfuzz_free_null_specX (fx := fx') (PI := prh_img_A) (PA := PA) B ARx SK) ->
  forall fx', crs_free0 (fx := fx') B ARx.
Proof.
intros HT fx'. unfold crs_free0.
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
