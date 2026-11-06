(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 971 of its 1034 lines of code are new or changed and 451 lines of the source are left out. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan
   d663f82d7f488d30, unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T7 = CRT-B-CEXIT: THE TWO FREES
   of the segment C (+0x6f8) ..
   the exit `j` X (+0x80c).

   rule 24: proves function check_round_trip (image B' of fuzz_preset; reuse search CONFIRMED by name: the R24 confirmation
   note R24-CONFIRM.md (sha256 b58eb5e2e5e3; internal record): released proofs plain/ubsan only, its address runs no evidence; no released walk, no walk held outside this tree, and no walk on an internal branch of these B' segments).

   WHAT IS PROVED HERE (Qed), at Crt102B_T7_bd.v's cut statements applied to this file's Section variables:
   - t7_stretch_FF : T7_AT_PF -> T7_AT_FF. FF (+0x7f8 = CRT7_FF_OFF_B) `ld a0, 0(s1)` (saved), `jal
     fuzz_free` at +0x7fc = CRT_FF2_CALL_B, return at PF (+0x800 = CRT7_PF_OFF_B). The run is one engine run over the
     read-only spill word (t7f_ssFF); the call is the kit's cb7k_call with fuzz_free's text FFREE at p = saved, n = kw
     (in the walk's list Dx = Dback ++ (saved, kw) :: Dc), its trace from HCL + HCTX by prh_univ_closure_site /
     prh_univ_closure_lit at the return site +0x800 (t7f_rets, by computation), its post's position implication at
     the room position's next event HFr (kw + cf_head) (crt_at_C_B's kw equation); t7_at_PF is rebuilt from the post's
     p <> 0 arm (the live state by Crt102KitB.cb4_live_call, the side facts by t7f_side_after, the trees of copy
     (pj_fdR and pj_nodeR at crt_tree_J = crt_tc, t7f_tcJ) and of back by frame and over the new list, the spill of
     &back above the callee window, the shadow of back / v by the frame clause, the position after one event by
     t7f_pos_step, and BOTH free-order ties - back's and copy's, crt_at_C_B's own conjuncts, each carried by
     PRH_PjOrder.pj_foR_frame).
   - t7_stretch_PF : T7_AT_E -> T7_AT_PF. PF (+0x800) `ld a0, 0x38(s1)` (&back), `jal pj_free` at +0x804 =
     CRT_PJF2_CALL_B, return at E (+0x808 = CRT7_E_OFF_B): pj_free's text PJFREE at n = DOC_D, window d = 0 (&back is
     in the class-3 fake frame, prhReader_at's frame arm), its post (fpostWm at d = 0) turned into apost_base_xF for
     cb7k_call, its position implication instantiated at the boundary's t7_back_tie (prhPj_free_evs F = the
     position's next event), t7_at_E rebuilt in full.
   KB ROUND (Crt102Glue.v G3 / G4): FF, PF and E are at kb = prh_wk F_check_round_trip (66), the journal at a budget
   WS with wbudget [] 66 WS. The two runs keep WS (Crt102Kit.v crt_run_xw); the calls go through the re-fit cb7k_call
   at {kbg} = 66, whose continuation hands the caller's journal on packaged (exists WS2, .. /\ wbudget [] 66 WS2) to
   cb4_live_call; t7f_ra_keep takes the caller's journal at any WS. No statement of a stretch changed.
   On the Step-1 contract texts (the re-hiding move): every journal is at R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf
   and the step relation is YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (Crt102Glue.v, the wle' contract); the two free
   texts' posts are at wle' (fuzz_free's fpostbm through PRH_Base.fpost_of_fpostb_fix, pj_free's
   fpostWmR) and go into cb7k_call's apost_base_xFR premise; both frees' hull premise `hull_budget S []` comes from
   the run position by t7f_hull0 at the run's length bound HOS4 (Section g). The stretch statements are T7_bd's, at
   SRr'; t7_stretch_FF / t7_stretch_PF take HOS4 after FFREE / PJFREE.

   INPUTS OF RECORD (the row's base was the T7 row's head merged with commit cbe6d10993c2, an ancestor of this tree):
   this tree's crt_at_C_B with back's AND copy's free-order conjuncts and Crt102Glue.v's crt_pos with its strtod tie
   and consumer window;
   lib/B/Prog/Crt102KitB.v (cb4_ff, cb4_sp, cb4_ro_img, cb4_fregs_trans, cb4_live_call); PRH_PjOrder.v (pj_fdR_foR,
   pj_foR_frame, pj_foR_fdR); lib/B/Prog/Crt102B_T7_kit.v
   (cb7k_call, cb7k_ret); the contract texts at the kit tip 3ac20a5c9e30: PRH_FnAlloc.v tfuzz_free_specX, PRH_FnPj.v
   dc0d0aa79c0f tpj_free_specX (prh_head_wide by CfParamsPreset.preset_head_wide; this tree's PRH_FnPj.v is a later
   blob), PRH_Base.v (prh_run_at_app_iff, prh_cons_from_app_iff, prh_univ_closure_site); row T8's lib/A/Prog/Crt102TailB.v
   at commit 247f3d4e8cf7 (:109-129; this tree's copy is a later rewrite without ct_ccnt24) for the ccnt24 lemma (copied, with its credit), the
   footprint / ledger bookkeeping pattern and ct_bregs_pres.

   NUMERALS. LENGTH: 512 / 504 / 64 (the class-3 frame, its flag word, its shadow bytes), 56 (struct pj), 16
   (cf_head), 32 / 88 (pj_free's frame window = back's node), 240 / 224 (the frame plus the realignment), 27632
   (STK_check_round_trip, by computation), 4096 (the least block address), 8 (a word). DERIVED: the extra atom 64
   (S10Env's TE numbering), every cut offset (the bd file's names), 2 ^ 47 / 2 ^ 64 (address bounds). WORD: register
   numbers 1 2 3 4 8 9 10 18 .. 27. No ADDRESS literal: every code address is pa_val / pa_sigma / CRT_PC_B + an
   offset name. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt PresetReqAtNoMiss PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetLiveBounds PresetLiveSec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc PRH_PjOrder CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102KitB Crt102B_T7_kit Crt102B_T7_bd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
(* the image-free kb runners (Crt102Kit.v Section kbw), by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Kit.
(* the re-hiding move (YA0nH, YSRrG, YGcfRehidePost.RZ_cf) and the hull at the two frees
   (PresetHullBudget's hull_budget, PresetHullPay.hull_budget_of_room_pos), by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* ======================================================================================================== *)
(* image-free pieces *)

(* ---- the tree facts across a call, image-free. A freeable tree under a memory that agrees on its footprint and a
   block predicate that still holds its blocks is the same tree: through the contract kit's order list (PRH_PjOrder.v
   pj_fdR_foR / pj_foR_frame / pj_foR_fdR; Crt102B_T7.v's t7_fdR_frame with the block-predicate change added). A
   represented tree under a new block predicate holding its blocks: lib/A/Prog/Crt102Kit.v blob b570eb6774e0
   crt102rw_mems_lblk :255 / crt102rw_nodeR_lblk :272, copied with the prefix renamed (this file
   Requires Crt102Kit.v only for its image-free kb runners, Section kbw). ---- *)
Section tr. Variable segs : list Segment.
Lemma t7f_fdR_move : forall d m m' lblk lblk' p D, pj_fdR segs m lblk d p D ->
  (forall a k, In (a, k) D -> lblk' a k) -> pj_agreeR segs m m' (pj_footR p D) -> pj_fdR segs m' lblk' d p D.
Proof.
intros d m m' lblk lblk' p D H HL HA.
destruct (PRH_PjOrder.pj_fdR_foR segs m lblk d p D H) as (F & HF).
exact (proj1 (PRH_PjOrder.pj_foR_fdR segs m' lblk' d p D F
  (PRH_PjOrder.pj_foR_frame segs d m m' lblk lblk' p D F HF HL HA))).
Qed.
Lemma t7f_mems_lblk : forall m lblk lblk' (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D -> (forall x k, In (x, k) D -> lblk' x k) ->
  (forall i nm u D1, nth_error l i = Some (nm, u) -> incl D1 D -> P (a + 56 * Z.of_nat i) u D1 ->
     P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D H HL HP; cbn [pj_memsR] in H |- *; [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & (Hl & Hc) & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
split; [exact Hx|]. split; [split; [apply HL; left; reflexivity | exact Hc]|]. split.
- specialize (HP 0%nat nm u D1 eq_refl (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_introl Hy)))).
  replace (a + 56 * Z.of_nat 0) with a in HP by lia. exact (HP H1).
- apply (IH (a + 56) (ka + 8) D2 H2).
  + intros y k' Hy. apply HL. right. apply in_or_app. right. exact Hy.
  + intros i nm' u' D1' Hi Hinc HPi.
    specialize (HP (S i) nm' u' D1' Hi (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_intror (Hinc y Hy))))).
    replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia. exact (HP HPi).
Qed.
Lemma t7f_nodeR_lblk : forall t m lblk lblk' p D, pj_nodeR segs m lblk p t D ->
  (forall x k, In (x, k) D -> lblk' x k) -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk lblk' p D H HL; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & (Hl & Hc) & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. split; [apply HL; subst D; left; reflexivity | exact Hc].
- destruct Hb as (E2 & E3 & E4 & E5 & k & (Hl & Hc) & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. split; [apply HL; subst D; left; reflexivity | exact Hc].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hcap | (Hc0 & _)]; [left; exact Hcap | right; split; [exact Hc0|]].
    apply HL. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di Hi).
  intros i u D1 Hil Hinc HP. rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 HP).
  intros x k Hxk. apply HL. apply HDi. apply Hinc. exact Hxk.
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hcap | (Hc0 & _ & _)]; [left; exact Hcap | right; split; [exact Hc0|]].
    split; apply HL; rewrite ED; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; [left; reflexivity | right; left; reflexivity]. }
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (t7f_mems_lblk m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di Hi).
  + intros x k Hxk. apply HL. apply HDi. exact Hxk.
  + intros i nm u D1 Hil Hinc HP. rewrite Forall_forall in IH.
    specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
    apply (IH m lblk lblk' _ D1 HP). intros x k Hxk. apply HL. apply HDi. apply Hinc. exact Hxk.
Qed.
End tr.

(* the ccnt24 entry premise of the two frees, from the room position (row T8's ct_hruns_big / ct_ccnt24,
   ref/Crt102TailB.v :109-129, commit 247f3d4e8cf7; copied, with its credit to
   lib/AU/PresetCfnB.v:456-484) *)
Lemma t7f_hruns_big : forall sm x os, PresetReqAt.MAXB < Z.of_nat (length x) -> PresetRun.hruns sm x os = [].
Proof.
intros sm x os Hx. induction os as [|[[o1 o2] o0] os IH]; [reflexivity|].
rewrite PresetRun.hruns_cons, IH, app_nil_r. unfold PresetRun.call_evs. cbv zeta.
rewrite (proj2 (Z.ltb_lt _ _) Hx). reflexivity.
Qed.
Lemma t7f_ccnt24 : forall sm x os i H0 hist S, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros sm x os i H0 hist S H.
assert (C2 : Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls 24) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))) <=
  PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ destruct H as ((d & Hd & Hp) & _).
  destruct (Z_le_gt_dec (Z.of_nat (length x)) PresetReqAt.MAXB) as [Hx|Hx].
  - exact (PresetLiveSec.live_c24_state sm x os i _ d Hx Hd Hp).
  - rewrite (t7f_hruns_big sm x os ltac:(lia)), List.firstn_nil in Hp.
    pose proof (PresetLiveSec.cnt_state (PresetRoom.in_cls 24) _ _ d Hd Hp) as C.
    assert (Z0 : forall f, PresetReqAt.cnt f (PresetReqAt.hlive []) = 0%nat) by reflexivity.
    rewrite Z0 in C. rewrite PresetLiveBounds.L24_value. unfold PresetLiveBounds.DRV. lia. }
exact (CfRoomLivePreset.preset_ccnt24 S C2).
Qed.

(* a call's frame-pointer trace is the kit's pc0-filtered prh_trace of its return site and the chain's spine *)
Lemma t7f_unwind_trace : forall pc0 a r b ch, unwind_of_chain pc0 ((a, r, b) :: ch) = prh_trace pc0 r (spine ch).
Proof.
intros pc0 a r b ch. unfold unwind_of_chain, prh_trace.
assert (E : forall l : list (Z * Z * Z),
  flat_map (fun r0 => match r0 with (_, ra, _) => if ra =? pc0 then [] else [ra] end) l =
  flat_map (fun ra => if ra =? pc0 then [] else [ra]) (spine l)).
{ intros l. induction l as [|[[x y] z] l IH]; [reflexivity|]. cbn [flat_map spine map fst snd]. rewrite IH. reflexivity. }
cbn [flat_map]. rewrite E. reflexivity.
Qed.

(* a harness-block list with distinct addresses *)
Lemma t7f_nodup_app : forall (l1 l2 : list (Z * Z)) x, List.NoDup (map fst (l1 ++ l2)) -> In x l1 -> ~ In x l2.
Proof.
intros l1. induction l1 as [|y l1 IH]; intros l2 x H H1 H2; [destruct H1|].
cbn [app map] in H. apply NoDup_cons_iff in H as (Hn & Hnd).
destruct H1 as [<- | H1].
- apply Hn. rewrite map_app. apply in_or_app. right. apply in_map. exact H2.
- exact (IH l2 x Hnd H1 H2).
Qed.
Lemma t7f_nodup_r : forall (l1 l2 : list (Z * Z)), List.NoDup (map fst (l1 ++ l2)) -> List.NoDup (map fst l2).
Proof.
intros l1. induction l1 as [|y l1 IH]; intros l2 H; [exact H|].
cbn [app map] in H. apply NoDup_cons_iff in H as (_ & H). exact (IH l2 H).
Qed.

(* pj_free's order list is not empty: copy_set ms is an object with at least the stamp member *)
Lemma t7f_fo_ne : forall ms, PresetReqAt.fo (PresetReqAt.copy_set ms) <> [].
Proof.
intros ms. unfold PresetReqAt.copy_set.
destruct (PjTree.pj_set_model ms PresetReqAt.MOD_KEY (PjTree.JStr PresetReqAt.MOD_VAL)) as [|[k v] l] eqn:E.
- destruct ms as [|[k0 v0] ms]; cbn [PjTree.pj_set_model] in E; [discriminate E|].
  destruct (list_eq_dec Z.eq_dec k0 PresetReqAt.MOD_KEY); discriminate E.
- cbn [PresetReqAt.fo map concat fst snd]. intros H. destruct (PresetReqAt.fo v); cbn [app] in H; discriminate H.
Qed.

(* a symbolic run over read-only regions writes nothing (Crt102B_T7.v's t7_wr) *)
#[local] Ltac t7f_wr :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0' bc ly' own') end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|] ].
(* a register a run did not write (T4's cb4_keep) *)
#[local] Ltac t7f_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

(* ---- the two symbolic states (S10Env.v's environment TE: atoms 0-31 the entry registers, 32-63 the current ones,
   64- the extras; xr r = 32 + r). FF (+0x7f8 `ld a0, 0(s1)`): the spill word saved at s1 + CRT_SP_SAVED_B, read only,
   its value the extra atom 64. PF (+0x800 `ld a0, 0x38(s1)`): the spill word &back at s1 + CRT_SP_BACK, read only,
   its value F + CRT_OFF_BACK through s3 = F (x19). Both runs stop at the `jal` that follows. ---- *)
Definition t7f_ssFF : sstate := mkSS (CRT_PC_B + CRT7_FF_OFF_B) cur_atoms
  [YP09.mkRegion (Some (xr 9)) CRT_SP_SAVED_B (CRT_SP_SAVED_B + 8) 0 0
     [YP09.mkChunk CRT_SP_SAVED_B (CVal 8 (SOff 64 0))]] None (mkFacts [] [] []).
Definition t7f_ssPF : sstate := mkSS (CRT_PC_B + CRT7_PF_OFF_B) cur_atoms
  [YP09.mkRegion (Some (xr 9)) CRT_SP_BACK (CRT_SP_BACK + 8) 0 0
     [YP09.mkChunk CRT_SP_BACK (CVal 8 (SOff (xr 19) CRT_OFF_BACK))]] None (mkFacts [] [] []).

(* ======================================================================================================== *)
Section t7f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
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
#[local] Notation STKFF := (@STK_fuzz_free prh_img_B).
#[local] Notation STKPF := (@STK_pj_free prh_img_B DOC_D).

Lemma t7f_fb : fs_frame_bytes CRT_CID = 512.
Proof. vm_compute. reflexivity. Qed.
Lemma t7f_stk : STKFF + 240 <= STKC /\ 0 <= STKFF /\ STKPF + 240 <= STKC /\ 0 <= STKPF.
Proof. vm_compute. repeat split; discriminate. Qed.
Lemma t7f_stkc : STKC = 27632.
Proof. vm_compute. reflexivity. Qed.
Lemma t7f_rets : In (BASE + (CRT_PC_B + CRT7_PF_OFF_B)) (pi_ret_sites F_check_round_trip RT_fuzz_free).
Proof. vm_compute. right. left. reflexivity. Qed.
(* pj_free's own events: one bulk event, when its order list's requests are a non-empty model list *)
Lemma t7f_free_evs : forall (F : list (Z * Z)) t', map (fun b => snd b + cf_head) F = PresetReqAt.fo t' ->
  PresetReqAt.fo t' <> [] -> PRH_FnPj.prhPj_free_evs F = [PresetReqAt.HBulk (PresetReqAt.fo t')].
Proof.
intros F t' H Hne. destruct F as [|b F']; [cbn [map] in H; exfalso; exact (Hne (eq_sym H))|].
change (PRH_FnPj.prhPj_free_evs (b :: F')) with [PresetReqAt.HBulk (map (fun b0 => snd b0 + cf_head) (b :: F'))].
rewrite H. reflexivity.
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the journals at the re-hiding move's world relation (YCbqG.v ajournal_xR / ajournal_xwR at RZW; kb round: the
   caller's at a wild-trace budget WS) *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
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
(* kb round: every state of this file (FF, PF, E) is at kb = prh_wk F_check_round_trip (Crt102Glue.v G4); as the A'
   twin's livea (Crt102Loops.v), the notation carries the budget *)
#[local] Notation liveB := (@crt_live rc prh_img_B RL SK B_prog_listing PA B ARx
  ly S Hp W regs mem md doc t D Lam peak most (prh_wk F_check_round_trip)).
#[local] Notation sideB := (@crt_side rc prh_img_B RL B_prog_listing PA B doc t D peak most).
#[local] Notation QFb := (@QF fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).
#[local] Notation cfgB := (@crt_cfg rc B_prog_listing PA CRT_PC_B).
#[local] Notation bregsB := (@crt_bregs_B regs).
#[local] Notation spillB := (@crt_spill rc B_prog_listing PA regs).
#[local] Notation posB := (crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (t := t)).
#[local] Notation tcB := (@crt_tc t).
#[local] Notation TEB := (TE (L := B_prog_listing) (PA := PA)).
#[local] Notation AT_FF := (@T7_AT_FF fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).
#[local] Notation AT_PF := (@T7_AT_PF fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).
#[local] Notation AT_E := (@T7_AT_E fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).

(* ---- THE SECTION HYPOTHESES (the internal file T7-CONTEXT.md's texts, each with its owner) ---- *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.                       (* engine; instance AR_laws_x_xs *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.           (* tcheck_round_trip_specX's premise *)
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.                 (* tcheck_round_trip_specX's premise *)
Hypothesis HCL : prh_univ_closure B CTX0.                          (* tcheck_round_trip_specX's premise *)
Hypothesis HCTX : prh_ctx CTX0 F_check_round_trip (raZ regs :: spine ch).  (* tcheck_round_trip_specX's premise *)
Hypothesis FFREE : forall fxk : YK11.FPState,
  @PRH_FnAlloc.tfuzz_free_specX fxk rc CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK.   (* contract text *)
Hypothesis PJFREE : forall fxk : YK11.FPState,
  @PRH_FnPj.tpj_free_specX fxk rc ci CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0 DOC_D.
    (* contract text, PRH_FnPj.v (kit tip f97c8b2f046b) *)
(* THE LENGTH BOUND of the run (route (i), agreed with the Crt102HullPos row): check_round_trip's own
   text premise (PRH_FnCheck.v:2363), which the tops pass; each free's hull budget comes from it (t7f_hull0) *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.

(* ---- the realigned sp: the A' bound sp0 - 240 <= sp1 (cb7k_call's derivation from cb4_sp) ---- *)
Lemma t7f_sp : YM05.alloc_ceiling + 27632 <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 - 240 <= sp1 <= sp0 - 224 /\
  sp1 mod 32 = 0 /\ 0 <= sp1.
Proof.
pose proof (cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hs16 & Hsc & Hs47 & Hs1 & Hs32 & Hs0).
assert (Hs240 : sp0 - 240 <= sp1).
{ pose proof Hs16 as H16. pose proof Hs32 as H32.
  apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide in H32; [|lia].
  destruct H16 as [q Hq]. destruct H32 as [q' Hq']. lia. }
repeat split; lia.
Qed.

(* ---- the run position: the next event of the walk's suffix, and the suffix after it (the run list split by
   prh_run_at_app_iff, the consumer window by prh_cons_from_app_iff, the strtod tie kept) ---- *)
Lemma t7f_pos_step : forall Sc e evs, posB Sc (e :: evs) ->
  exists i hist, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os i rp_H0 hist Sc /\ prh_run_at rp_sm rp_x rp_os i [e] /\
    forall S' hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (i + 1) rp_H0 hist' S' -> posB S' evs.
Proof.
intros Sc e evs HP.
pose proof (crt_pos_strtod HP) as Hsm. destruct (crt_pos_ex HP) as (pre & hist & HA).
pose proof (crt_pos_split HA) as Ert. pose proof (crt_pos_room HA) as HRP. pose proof (crt_pos_run HA) as HR.
pose proof (crt_pos_cons HA) as HC.
pose proof (proj1 (prh_run_at_app_iff _ _ _ _ [e] evs) HR) as (H1 & H2).
change (length (e :: evs)) with (1 + length evs)%nat in HC.
pose proof (proj1 (prh_cons_from_app_iff _ _ _ _ 1 (length evs)) HC) as (_ & C2).
exists (rp_i + length pre)%nat, hist. split; [exact HRP|]. split; [exact H1|].
intros S' hist' HRP'. refine {| crt_pos_strtod := Hsm; crt_pos_ex := _ |}. exists (pre ++ [e]), hist'.
refine {| crt_pos_split := _; crt_pos_room := _; crt_pos_run := _; crt_pos_cons := _ |}.
- rewrite Ert, <- app_assoc; reflexivity.
- rewrite length_app. cbn [length]. rewrite Nat.add_assoc. exact HRP'.
- rewrite length_app. cbn [length]. rewrite Nat.add_assoc. cbn [length] in H2. exact H2.
- rewrite length_app. cbn [length]. rewrite Nat.add_assoc. exact C2.
Qed.

(* ---- THE HULL AT A FREE. A free's hull budget `hull_budget S []` (fuzz_free's p <> 0 and
   pj_free's v <> 0 premise; a free makes no secondary entry) at any position of the run, from its length bound HOS4:
   PresetHullPay.hull_budget_of_room_pos at the empty event list ---- *)
Lemma t7f_hull0 : forall i hist Sc, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os i rp_H0 hist Sc ->
  PresetHullBudget.hull_budget Sc [].
Proof.
intros i hist Sc HRP.
apply (PresetHullPay.hull_budget_of_room_pos rp_sm rp_x rp_os i rp_H0 hist Sc [] HOS4 HRP).
- change (PresetSecTotal.nsec []) with 0%nat. rewrite PresetSecTotal.NCALL_value. lia.
- change (PresetSecTotal.tsec []) with 0. rewrite PresetSecTotal.TCALL_value. lia.
Qed.

(* ---- the kept registers carry the B' register snapshot across a call (row T8's ct_bregs_pres) ---- *)
Lemma t7f_bregs_pres : forall rg rg' F, bregsB rg F -> aregs_preserved rg rg' -> bregsB rg' F.
Proof.
intros rg rg' F HBR HP.
refine {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _; crt_bregs_B_s1 := _;
  crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _; crt_bregs_B_s9 := _;
  crt_bregs_B_s11 := _ |}.
- rewrite (ts_ap rg rg' 2%bv HP) by ts_cs. exact (crt_bregs_B_sp HBR).
- rewrite (ts_ap rg rg' 3%bv HP) by ts_cs. exact (crt_bregs_B_gp HBR).
- rewrite (ts_ap rg rg' 4%bv HP) by ts_cs. exact (crt_bregs_B_tp HBR).
- rewrite (ts_ap rg rg' 8%bv HP) by ts_cs. exact (crt_bregs_B_s0 HBR).
- rewrite (ts_ap rg rg' 9%bv HP) by ts_cs. exact (crt_bregs_B_s1 HBR).
- rewrite (ts_ap rg rg' 18%bv HP) by ts_cs. exact (crt_bregs_B_s2 HBR).
- rewrite (ts_ap rg rg' 20%bv HP) by ts_cs. exact (crt_bregs_B_s4 HBR).
- rewrite (ts_ap rg rg' 19%bv HP) by ts_cs. exact (crt_bregs_B_s3 HBR).
- rewrite (ts_ap rg rg' 23%bv HP) by ts_cs. exact (crt_bregs_B_s7 HBR).
- rewrite (ts_ap rg rg' 25%bv HP) by ts_cs. exact (crt_bregs_B_s9 HBR).
- rewrite (ts_ap rg rg' 27%bv HP) by ts_cs. exact (crt_bregs_B_s11 HBR).
Qed.

(* ---- the rewritten tree is the model's copy_set (cm_crt_tree_obj, and MOD_AT / STAMP are the model's MOD_KEY /
   MOD_VAL by computation) ---- *)
Lemma t7f_tc : forall ms, t = PjTree.JObj ms -> tcB = PresetReqAt.copy_set ms.
Proof. intros ms ->. unfold crt_tc. rewrite cm_crt_tree_obj. reflexivity. Qed.

(* ---- a block the walk holds beyond the entry's is a live allocator block that is not the entry's (row T8's HDcb) ---- *)
Lemma t7f_dx : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc a k,
  liveB lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc -> In (a, k) Dx ->
  In (a, k) Lamc /\ 0 <= k /\ In (a - 16, k + 16) (ablocks B lyc Sc) /\ ~ In (a - 16, k + 16) (ablocks B ly S).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc a k HL Hak.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPA.
pose proof HJ as (HARc & _).
assert (HinL : In (a, k) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hak).
destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLED HinL) as (Hk0 & Hab & _).
change (@cf_head CfParams_preset) with 16 in Hab.
split; [exact HinL|]. split; [exact Hk0|]. split; [exact Hab|].
intros HinS.
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & _ & _ & _ & _ & Hpw).
assert (Hsym : forall a0 b0, zdisjoint a0 b0 -> zdisjoint b0 a0) by (intros a0 b0 [H1|H1]; [right|left]; exact H1).
assert (Hpw' : pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S ++ ck_hblks Dx))).
{ clear - Hpw HPA Hsym. revert Hpw.
  generalize (Permutation_map (fun b => (fst b, req_size (snd b))) HPA). generalize (map (fun b => (fst b, req_size (snd b))) (ablocks B lyc Sc)).
  generalize (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S ++ ck_hblks Dx)).
  intros l' l P. induction P as [|z l0 l0' P IH|z y l0|l0 l0' l0'' P1 IH1 P2 IH2]; cbn [pairwise]; intros H.
  - exact H.
  - destruct H as [Hx Hl]. split; [|exact (IH Hl)].
    rewrite Forall_forall in Hx |- *. intros w Hw. apply Hx. exact (Permutation_in _ (Permutation_sym P) Hw).
  - destruct H as [Hy [Hx Hl]]. inversion Hy as [|? ? Hyx Hyl]; subst.
    split; [constructor; [apply Hsym; exact Hyx | exact Hx] | split; [exact Hyl | exact Hl]].
  - exact (IH2 (IH1 H)). }
rewrite map_app in Hpw'.
assert (Hdup : forall (l1 l2 : list (Z * Z)) y, pairwise zdisjoint (l1 ++ l2) -> In y l1 -> In y l2 -> zdisjoint y y).
{ clear. intros l1. induction l1 as [|z l1 IH]; intros l2 y H H1 H2; [destruct H1|].
  cbn [pairwise app] in H. destruct H as [Hz Hl]. destruct H1 as [<- | H1].
  - rewrite Forall_forall in Hz. apply Hz. apply in_or_app. right. exact H2.
  - exact (IH l2 y Hl H1 H2). }
pose proof (Hdup _ _ _ Hpw' (in_map (fun b => (fst b, req_size (snd b))) _ _ HinS)
  (in_map (fun b => (fst b, req_size (snd b))) _ _
    (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) Dx (a, k) Hak))) as Hself.
unfold zdisjoint in Hself. cbn [fst snd] in Hself. change (@cf_head CfParams_preset) with 16 in *.
unfold req_size in Hself. destruct (Z.eqb_spec (k + 16) 0); lia.
Qed.

(* ---- THE FOOTPRINT OF A FREE, as the two calls have it: a window [F + flo, F + fhi) of the class-3 frame, and the
   allocator blocks of the harness blocks Dfree it frees ---- *)
Definition t7f_fpc (F flo fhi : Z) (Dfree : list (Z * Z)) (FP1 : list (Z * Z)) : Prop :=
  forall a, inFP FP1 a -> (F + flo <= a < F + fhi) \/
    exists a' k', In (a', k') Dfree /\ a' - 16 <= a < a' - 16 + req_size (k' + 16).

(* such a footprint is application memory below the ceiling and misses the frame's flag word (cb4_live_call's
   premise) *)
Lemma t7f_fp_app : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc flo fhi Dfree FP1,
  liveB lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  t7f_fpc (frame_addr lyc CRT_CID pos) flo fhi Dfree FP1 -> incl Dfree Lamc -> 0 <= flo -> fhi <= 504 ->
  forall a, inFP FP1 a -> a < YM05.alloc_ceiling /\ in_app a 1 /\
    ~ (frame_addr lyc CRT_CID pos + 504 <= a < frame_addr lyc CRT_CID pos + 512).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc flo fhi Dfree FP1 HL HFPc HDf Hflo Hfhi a Ha.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof HJ as (HARc & _).
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (HFPc a Ha) as [Hv | (a' & k' & Hak & Hb)].
- split; [lia|]. split; [|lia]. apply (in_app_sub _ _ _ _ Fb3); lia.
- destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a' k' _ _ HLED (HDf _ Hak))
    as (Hk0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in Hab.
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & Bapp & _).
  pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ CRT_CID pos HARc Hab Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite t7f_fb in Hd. fold F in Hd.
  assert (Hrq : req_size (k' + 16) = k' + 16) by (unfold req_size; destruct (Z.eqb_spec (k' + 16) 0); lia).
  rewrite Hrq in *.
  split; [lia|]. split; [|lia]. apply (in_app_sub _ _ _ _ Bapp); lia.
Qed.

(* ---- A BYTE A FREE KEEPS: a byte of a frame of Sc off the footprint's frame window, or a byte of a live harness
   block the free does not free, is the same byte (and stays writable) after the call ---- *)
Lemma t7f_keep_byte : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1
    ly2 S2 Hp2 W2 mem2 md2 k1 flo fhi Dfree y,
  liveB lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJ STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  t7f_fpc (frame_addr lyc CRT_CID pos) flo fhi Dfree FP1 -> incl Dfree Lamc -> 0 <= flo -> fhi <= 512 ->
  ((exists cid pos', In (cid, pos') (frames Sc) /\
      frame_addr lyc cid pos' <= y < frame_addr lyc cid pos' + fs_frame_bytes cid /\
      ~ (frame_addr lyc CRT_CID pos + flo <= y < frame_addr lyc CRT_CID pos + fhi)) \/
   (exists b kb, In (b, kb) Lamc /\ ~ In (b, kb) Dfree /\ In (b - 16, kb + 16) (ablocks B ly2 S2) /\
      b <= y < b + kb)) ->
  mbyte SEGS (mrestrict (w_H W2) mem2) y = mbyte SEGS (mrestrict (w_H Wc) memc) y /\
  (writable_at SEGS (mrestrict (w_H Wc) memc) y -> writable_at SEGS (mrestrict (w_H W2) mem2) y).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 flo fhi
  Dfree y HL HJ1 HFPc HDf Hflo Hfhi Hy.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof HJ as (HARc & _).
pose proof HJ1 as (HAR2 & HLY1 & _ & _ & _ & HFR1 & _ & _ & G1 & G2 & G3 & G4 & _).
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (alx_layout _ _ _ LAWS lyc Sc Hpc Wc memc mdc ly2 HARc HLY1) as (_ & Efa & _).
assert (HDfb : forall a' k', In (a', k') Dfree -> 0 <= k' /\ In (a' - 16, k' + 16) (ablocks B lyc Sc)).
{ intros a' k' H. destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a' k' _ _ HLED (HDf _ H))
    as (Hk0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in Hab. exact (conj Hk0 Hab). }
set (F := frame_addr lyc CRT_CID pos) in *.
destruct Hy as [(cid & pos' & Hinc & Hy1 & HnF) | (b & kb & HinL & HnD & Hab2 & Hy)].
- assert (HnFP : ~ inFP FP1 y).
  { intros Hf. destruct (HFPc y Hf) as [Hv | (a' & k' & Hak & Hb)]; [exact (HnF Hv)|].
    destruct (HDfb a' k' Hak) as (Hk0 & Hab).
    pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ cid pos' HARc Hab Hinc) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold req_size in *. destruct (Z.eqb_spec (k' + 16) 0); lia. }
  assert (E : aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y).
  { apply (G4 cid pos' y Hinc); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnFP]. }
  split; [apply (mbyte_of_aview SEGS); exact E|].
  intros _. apply (apresent_writable SEGS).
  assert (Hin2 : In (cid, pos') (frames S2)) by (rewrite HFR1; exact Hinc).
  destruct (alx_frames _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos' HAR2 Hin2) as (_ & _ & Ffr2 & _).
  rewrite (Efa cid pos') in Ffr2. exact (proj1 (Ffr2 y ltac:(lia))).
- destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ b kb _ _ HLED HinL) as (Hk0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in Hab.
  assert (Hrq : req_size (kb + 16) = kb + 16) by (unfold req_size; destruct (Z.eqb_spec (kb + 16) 0); lia).
  assert (HnFP : ~ inFP FP1 y).
  { intros Hf. destruct (HFPc y Hf) as [Hv | (a' & k' & Hak & Hb)].
    - pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ CRT_CID pos HARc Hab Hin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite t7f_fb in Hd. fold F in Hd. rewrite Hrq in Hd.
      lia.
    - destruct (HDfb a' k' Hak) as (Hk0' & Hab').
      assert (Hne : (b - 16, kb + 16) <> (a' - 16, k' + 16)).
      { intros E. injection E as E1 E2. apply HnD. replace b with a' by lia. replace kb with k' by lia. exact Hak. }
      pose proof (sep_blocks_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hab Hab' Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd.
      unfold req_size in Hd, Hb. destruct (Z.eqb_spec (k' + 16) 0); lia. }
  assert (E : aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y).
  { replace y with (b - 16 + (y - (b - 16))) by lia.
    apply (G2 (b - 16) (kb + 16) (y - (b - 16)) Hab Hab2); [rewrite Hrq; lia|].
    replace (b - 16 + (y - (b - 16))) with y by lia. exact HnFP. }
  split; [apply (mbyte_of_aview SEGS); exact E|].
  intros _. apply (apresent_writable SEGS).
  destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hbp & _).
  exact (proj1 (Hbp y ltac:(rewrite Hrq; lia))).
Qed.

#[local] Notation treeJ := (crt_tree_J (t := t)).

(* the rewritten tree is the join's tree on the object arm (both are copy_set ms there) *)
Lemma t7f_tcJ : forall ms, t = PjTree.JObj ms -> tcB = treeJ.
Proof. intros ms Ht. rewrite (t7f_tc ms Ht). rewrite Ht. reflexivity. Qed.

(* ---- THE SIDE FACTS AFTER A FREE: the callee's ledger (g_most / g_own_ran_out ride in it) and room, the read-only
   view kept by the inner journal's image clause (Crt102Arms.v's arms_live_after :820-824), the document's tree kept
   by frame (its header in a frame of the entry, apart from the class-3 frame; its blocks live and not freed) and over
   the new list ---- *)
Lemma t7f_side_after : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1
    ly2 S2 Hp2 W2 mem2 md2 k1 flo fhi Dfree Lam2 peak2 cnt2 own2 ran2,
  liveB lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJ STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ~ YI16.sink_open_fp FP1 ->
  t7f_fpc (frame_addr lyc CRT_CID pos) flo fhi Dfree FP1 -> incl Dfree Dx -> 0 <= flo -> fhi <= 512 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 most own2 ->
  peakc <= peak2 -> room_live_cf S2 ->
  (forall bk, In bk D -> In bk Lam2) ->
  sideB ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 own2 ran2.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 flo fhi Dfree
  Lam2 peak2 cnt2 own2 ran2 HL HJ1 HSC HFPc HDf Hflo Hfhi HLED2 Hpk2 HRL2 HDL2.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL.
pose proof (crt_live_blocks_perm HL) as HPB. pose proof (crt_live_dx_apart HL) as HAP.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK. pose proof (crt_side_room HSD) as HRL.
pose proof (crt_side_arodata HSD) as HRO. pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
pose proof HJ1 as (HAR2 & HLY1 & _ & _ & _ & HFR1 & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof HPRE as ((HAR & _) & _).
assert (HDfL : incl Dfree Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact (HDf _ Hbk). }
refine {| crt_side_ledger := HLED2; crt_side_peak := _; crt_side_room := HRL2; crt_side_arodata := _;
  crt_side_doc := _; crt_side_doc_blocks := HDL2 |}.
{ lia. }
{ intros a Hro Hno Her. rewrite (G3 a); [exact (HRO a Hro Hno Her) | exact (cb4_ro_img a Hro) | exact Hno | exact Her
  | intros Hps; exact (pst_not_ro_B a Hps Hro) | apply fp_spares_closed; exact HSC]. }
apply (t7f_nodeR_lblk SEGS t _ (prh_lin Lamc) (prh_lin Lam2) doc D); [|intros a k Hak; exact (HDL2 _ Hak)].
apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) doc D HDOC).
intros y Hy.
apply (t7f_keep_byte lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  flo fhi Dfree y HL HJ1 HFPc HDfL Hflo Hfhi).
destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- left.
  pose proof HTREE as (_ & _ & _ & (_ & (cid & pos' & Hin & H1 & H2) & _)).
  destruct (alx_layout _ _ _ LAWS ly S Hp W mem md lyc HAR HLYc) as (_ & Efa & _).
  rewrite <- (Efa cid pos') in H1, H2.
  exists cid, pos'. split; [rewrite HFRc; right; exact Hin|]. split; [lia|].
  apply in_split in Hin as (l2 & l3 & El).
  pose proof (sep_frames_pos_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc (CRT_CID, pos) (cid, pos') [] l2 l3 HARc
    ltac:(rewrite HFRc, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite t7f_fb in Hd. lia.
- right. exists b, kb. split; [exact (HDL _ Hb)|]. split; [intros Hf; exact (HAP _ (HDf _ Hf) Hb)|].
  unfold pj_holdsR in Hy. cbn [fst snd] in Hy. split; [|exact Hy].
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ b kb _ _ HLED2 (HDL2 _ Hb))
    as (_ & Hab2 & _).
  change (@cf_head CfParams_preset) with 16 in Hab2. exact Hab2.
Qed.

(* ---- a tree in the class-3 frame (copy at + CRT_OFF_COPY, back at + CRT_OFF_BACK) whose header is off the free's
   frame window and whose blocks the free does not free keeps its bytes ---- *)
Lemma t7f_tree_agree : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1
    ly2 S2 Hp2 W2 mem2 md2 k1 flo fhi Dfree Lam2 peak2 cnt2 fail2 ran2 most2 own2 off Dt,
  liveB lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJ STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  t7f_fpc (frame_addr lyc CRT_CID pos) flo fhi Dfree FP1 -> incl Dfree Lamc -> 0 <= flo -> fhi <= 512 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  incl Dt Lamc -> incl Dt Lam2 -> (forall bk, In bk Dt -> ~ In bk Dfree) ->
  0 <= off -> off + 56 <= 512 -> (off + 56 <= flo \/ fhi <= off) ->
  pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (pj_footR (frame_addr lyc CRT_CID pos + off) Dt).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 flo fhi Dfree
  Lam2 peak2 cnt2 fail2 ran2 most2 own2 off Dt HL HJ1 HFPc HDf Hflo Hfhi HLED2 HDt HDt2 HDtf Ho1 Ho2 Ho3 y Hy.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & _).
apply (t7f_keep_byte lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  flo fhi Dfree y HL HJ1 HFPc HDf Hflo Hfhi).
destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- left. exists CRT_CID, pos. split; [exact Hin|]. rewrite t7f_fb. split; lia.
- right. exists b, kb. split; [exact (HDt _ Hb)|]. split; [exact (HDtf _ Hb)|].
  unfold pj_holdsR in Hy. cbn [fst snd] in Hy. split; [|exact Hy].
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ b kb _ _ HLED2 (HDt2 _ Hb)) as (_ & Hab2 & _).
  change (@cf_head CfParams_preset) with 16 in Hab2. exact Hab2.
Qed.

(* ---- back's / v's shadow lies in the frame's 64 shadow bytes, which no free's footprint (application memory) names:
   kept by the inner journal's frame clause ---- *)
Lemma t7f_ra_keep : forall lyc Sc Hpc Wc memc mdc kj pos STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 off {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS ->
  AJ STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, inFP FP1 a -> a < YM05.alloc_ceiling /\ in_app a 1 /\
     ~ (frame_addr lyc CRT_CID pos + 504 <= a < frame_addr lyc CRT_CID pos + 512)) ->
  0 <= off -> off + 56 <= 512 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + off) 56 ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (frame_addr ly2 CRT_CID pos + off) 56.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 off WS HJ HJ1 HFP Ho1 Ho2 HR.
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof HJ as (HARc & _).
pose proof HJ1 as (_ & HLY1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & G4 & _).
destruct (alx_layout _ _ _ LAWS lyc Sc Hpc Wc memc mdc ly2 HARc HLY1) as (_ & Efa & _).
rewrite (Efa CRT_CID pos).
set (F := frame_addr lyc CRT_CID pos) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HR].
intros y Hy. unfold shadow_of_addr.
apply (G4 CRT_CID pos (SHADOW_OFF + y / 8) Hin).
- right. unfold in_zr. cbn [fst snd]. rewrite t7f_fb. change (512 / 8) with 64. fold F.
  unfold shadow_addr. lia.
- intros Hf. destruct (HFP _ Hf) as (H1 & H2 & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* ---- the symbolic states hold of the machine states at the two cuts ---- *)
Lemma t7f_entry_FF : forall (fxk : YK11.FPState) (Wc : world SEGS) memc (rg : bvmap 5 word) F saved,
  bregsB rg F -> spillB Wc memc CRT_SP_SAVED_B saved -> 0 <= saved < 2 ^ 64 ->
  st_ok_pi SEGS VAL (TEB regs rg [Z_to_bv 64 saved]) t7f_ssFF
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT7_FF_OFF_B))) memc (YK11.seg_rom SEGS))).
Proof.
intros fxk Wc memc rg F saved HBR HSV Hsv.
pose proof (crt_bregs_B_s1 HBR) as R9.
pose proof t7f_sp as (Hc & H47 & Hs1 & Hs32 & Hs0).
assert (E9 : bv_unsigned (ew (TEB regs rg [Z_to_bv 64 saved]) (xr 9)) = sp1).
{ unfold xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (U64 : bv_unsigned (ew (TEB regs rg [Z_to_bv 64 saved]) 64) = saved).
{ change (ew (TEB regs rg [Z_to_bv 64 saved]) 64) with (ew (TEB regs rg [Z_to_bv 64 saved]) (64 + 0)).
  rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth]. apply unsigned_lit_small. exact Hsv. }
apply (ts_st_ok (fx := fxk)).
- apply te_regs_ok.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  apply (ts_rok _ _ (xr 9) sp1); [exact E9 | unfold CRT_SP_SAVED_B; lia | unfold CRT_SP_SAVED_B; lia | intros o Ho; lia |].
  apply Forall_cons; [|apply Forall_nil].
  apply (ts_chunk _ _ sp1 CRT_SP_SAVED_B 8 (SOff 64 0) saved);
    [cbn [sv_denot]; rewrite U64, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
  cbn [YP09.c_off]. change (N.to_nat 8) with 8%nat. exact HSV.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [exact I | split; exact I].
Qed.
Lemma t7f_entry_PF : forall (fxk : YK11.FPState) (Wc : world SEGS) memc (rg : bvmap 5 word) F,
  bregsB rg F -> spillB Wc memc CRT_SP_BACK (F + CRT_OFF_BACK) -> 0 <= F -> F + CRT_OFF_BACK < 2 ^ 64 ->
  st_ok_pi SEGS VAL (TEB regs rg []) t7f_ssPF
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT7_PF_OFF_B))) memc (YK11.seg_rom SEGS))).
Proof.
intros fxk Wc memc rg F HBR HSV HF0 HF1.
pose proof (crt_bregs_B_s1 HBR) as R9. pose proof (crt_bregs_B_s3 HBR) as R19.
pose proof t7f_sp as (Hc & H47 & Hs1 & Hs32 & Hs0).
assert (E9 : bv_unsigned (ew (TEB regs rg []) (xr 9)) = sp1).
{ unfold xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (E19 : bv_unsigned (ew (TEB regs rg []) (xr 19)) = F).
{ unfold xr. rewrite (te_cur regs rg _ 19%bv 19) by reflexivity. rewrite R19. apply unsigned_lit_small.
  unfold CRT_OFF_BACK in HF1. lia. }
apply (ts_st_ok (fx := fxk)).
- apply te_regs_ok.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  apply (ts_rok _ _ (xr 9) sp1); [exact E9 | unfold CRT_SP_BACK; lia | unfold CRT_SP_BACK; lia | intros o Ho; lia |].
  apply Forall_cons; [|apply Forall_nil].
  apply (ts_chunk _ _ sp1 CRT_SP_BACK 8 (SOff (xr 19) CRT_OFF_BACK) (F + CRT_OFF_BACK));
    [cbn [sv_denot]; rewrite E19; reflexivity | unfold CRT_OFF_BACK in *; cbn; lia | cbn; lia |].
  cbn [YP09.c_off]. change (N.to_nat 8) with 8%nat. exact HSV.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [exact I | split; exact I].
Qed.

(* ======================================================================================================== *)
(* FF (+0x7f8): `ld a0, 0(s1)` (saved), `jal fuzz_free` (+0x7fc = CRT_FF2_CALL_B), return at PF (+0x800). back's
   free-order tie, crt_at_C_B's own conjunct (Crt102Glue.v at 7281359fe8bc), is carried across fuzz_free by
   PRH_PjOrder.pj_foR_frame with the footprint facts that carry back's tree. *)
Lemma t7_stretch_FF : AT_PF -> AT_FF.
Proof.
intros HPF fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw HCB.
pose proof (crt_at_C_B_obj HCB) as Ht. pose proof (crt_at_C_B_frm_zero HCB) as HFZ.
pose proof (crt_at_C_B_fregs HCB) as HFK. pose proof (crt_at_C_B_live HCB) as HL.
pose proof (crt_at_C_B_bregs HCB) as HBR. pose proof (crt_at_C_B_sp_saved HCB) as HSVD.
pose proof (crt_at_C_B_sp_back HCB) as HSBK. pose proof (crt_at_C_B_back_open HCB) as HRB.
pose proof (crt_at_C_B_v_open HCB) as HRV. pose proof (crt_at_C_B_cset_range HCB) as Hcs.
pose proof (crt_at_C_B_cset_mod HCB) as Hcs0. pose proof (crt_at_C_B_cnt HCB) as Hcnt.
pose proof (crt_at_C_B_saved_nz HCB) as Hsv0. pose proof (crt_at_C_B_copy HCB) as HTC.
pose proof (crt_at_C_B_copy_fd HCB) as HFD. pose proof (crt_at_C_B_back HCB) as HBK.
pose proof (crt_at_C_B_pos HCB) as HPOS. pose proof (crt_at_C_B_kw HCB) as Hkw.
pose proof (crt_at_C_B_back_tblk HCB) as HPB. destruct (crt_at_C_B_back_fo HCB) as (Fb & HFOb & HFtb).
pose proof (crt_at_C_B_copy_tblk HCB) as HPC. destruct (crt_at_C_B_copy_fo HCB) as (Fc & HFOc & HFtc).
pose proof (crt_at_C_B_copy_depth HCB) as HdJ.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL.
pose proof (crt_live_blocks_perm HL) as HPA. pose proof (crt_live_dx_apart HL) as HAP.
pose proof (crt_live_saved HL) as HSV. pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNl.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK. pose proof (crt_side_room HSD) as HRL.
pose proof (crt_side_arodata HSD) as HRO. pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof t7f_sp as (Hc & H47 & Hs1 & Hs32 & Hs0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof t7f_stk as (Hk1 & Hk2 & Hk3 & Hk4).
pose proof crt7_cuts_B as (EFF & EPF & EE & _ & _).
set (F := frame_addr lyc CRT_CID pos) in *.
(* saved's block: a block the walk holds, distinct from back's and copy's *)
assert (HinX : In (saved, kw) (Dback ++ (saved, kw) :: Dc)) by (apply in_or_app; right; left; reflexivity).
destruct (t7f_dx _ _ _ _ _ _ _ _ _ _ _ _ _ _ saved kw HL HinX) as (HinL & Hkw0 & Hab & HnS).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & Bapp & _).
assert (Hrq : req_size (kw + 16) = kw + 16) by (unfold req_size; destruct (Z.eqb_spec (kw + 16) 0); lia).
rewrite Hrq in Bce, Bapp.
pose proof HLED as (_ & Hnd & _).
apply NoDup_ListNoDup in Hnd.
pose proof (Permutation_NoDup (Permutation_map fst HPL) Hnd) as Hnd'.
rewrite <- app_assoc in Hnd'.
assert (HnB : ~ In (saved, kw) Dback).
{ intros Hb. apply (t7f_nodup_app _ _ _ Hnd' Hb). apply in_or_app. left. apply in_eq. }
assert (HnC : ~ In (saved, kw) Dc).
{ pose proof (t7f_nodup_r _ _ Hnd') as Hn2. cbn [app map] in Hn2. apply NoDup_cons_iff in Hn2 as (Hn2 & _).
  intros Hc0. apply Hn2. rewrite map_app. apply in_or_app. left. exact (in_map fst _ _ Hc0). }
(* the room position: fuzz_free (saved)'s event is next *)
destruct (t7f_pos_step Sc
  (PresetReqAt.HFr (last (PresetReqAt.wcaps (PresetReqAt.copy_set mms) true) 0 + PresetReqAt.HEAD))
  ([PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set mms))] ++
   [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set mms))]) HPOS) as (i1 & h1 & HRP1 & HRun1 & Hnext).
rewrite <- Hkw in HRun1. change PresetReqAt.HEAD with (@cf_head CfParams_preset) in HRun1.
(* the run +0x7f8 .. the jal *)
assert (Hsv : 0 <= saved < 2 ^ 64) by lia.
pose proof (t7f_entry_FF fxk Wc memc rg F saved HBR HSVD Hsv) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TEB regs rg [Z_to_bv 64 saved]) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TEB regs rg [Z_to_bv 64 saved])) by apply te_env.
pose (RUN := @Crt102Kit.crt_run_xw fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS WS_HJ).
unfold crt_cfg.
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ t7f_wr. }
apply frame_of_read_only in HF; [|vm_compute; reflexivity]. clear HFr HG.
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg _ ?mdx) _ => set (MDX := mdx) in * end.
rewrite HF in HJ.
pose proof {| crt_live_journal := ex_intro _ WS_HJ (conj HJ HB_HJ); crt_live_side := HSD; crt_live_lam_perm := HPL;
  crt_live_blocks_perm := HPA;
  crt_live_dx_apart := HAP; crt_live_saved := HSV; crt_live_frame := HFRM; crt_live_fspill := HSPF;
  crt_live_copy_open := HCR; crt_live_copy_hull := HCH; crt_live_memnorm := HMNl |} as HL1.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
assert (X10 : getr (ms_regs ms) 10 = w64 saved) by (rewrite Q10; te_close).
assert (X1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + CRT7_PF_OFF_B))) by (rewrite Q1; vm_compute; reflexivity).
assert (KR : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) rr = getr rg rr).
{ intros rr Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [t7f_keep HS |]). destruct Hr. }
assert (HBR1 : bregsB (ms_regs ms) F).
{ refine {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _; crt_bregs_B_s1 := _;
    crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _; crt_bregs_B_s9 := _;
    crt_bregs_B_s11 := _ |}; rewrite KR by (cbv; tauto).
  - exact (crt_bregs_B_sp HBR). - exact (crt_bregs_B_gp HBR). - exact (crt_bregs_B_tp HBR).
  - exact (crt_bregs_B_s0 HBR). - exact (crt_bregs_B_s1 HBR). - exact (crt_bregs_B_s2 HBR).
  - exact (crt_bregs_B_s4 HBR). - exact (crt_bregs_B_s3 HBR). - exact (crt_bregs_B_s7 HBR).
  - exact (crt_bregs_B_s9 HBR). - exact (crt_bregs_B_s11 HBR). }
assert (HLED1 : prh_ledger B lyc Sc Hpc Wc (ms_mem ms) Lamc peakc cntc SIZE_MAXZ 0 most 0) by (rewrite HF; exact HLED).
(* fuzz_free's footprint: saved's allocator block *)
assert (HFPc : t7f_fpc F 0 0 [(saved, kw)] (ablocks_fp [(saved - cf_head, kw + cf_head)])).
{ intros a (r & Hr & Ha). cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  right. exists saved, kw. split; [left; reflexivity|]. change (@cf_head CfParams_preset) with 16 in Ha. exact Ha. }
assert (HDfL : incl [(saved, kw)] Lamc) by (intros bk [<- | []]; exact HinL).
assert (HDfX : incl [(saved, kw)] (Dback ++ (saved, kw) :: Dc)) by (intros bk [<- | []]; exact HinX).
pose proof (t7f_fp_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 0 _ _ HL HFPc HDfL ltac:(lia) ltac:(lia)) as HFPapp.
refine (@cb7k_call fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D Lam peak cnt ran
  most LAWS HPRE fxk STKFF (ablocks_fp [(saved - cf_head, kw + cf_head)]) CRT7_PF_OFF_B (SIGMA AS_fuzz_free) Wc _ _ ms
  MDX lyc Sc Hpc kj pos (Dback ++ (saved, kw) :: Dc) Lamc peakc cntc 0 0 _ (prh_wk F_check_round_trip) HFZ HS _ _ _ _
  HBR1 X1 _ _ Hk2 Hk1 _ _ _).
- reflexivity.
- reflexivity.
- rewrite (te_entry regs rg _ 2%bv 2) by reflexivity. reflexivity.
- rewrite HF. exact HL1.
- rewrite EPF. lia.
- rewrite EPF. reflexivity.
- (* the callee's footprint is a temporary block: saved's, live at the call, not the entry's *)
  intros a (r & Hr & Ha). cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  right; left. exists (saved - cf_head), (kw + cf_head). change (@cf_head CfParams_preset) with 16 in *.
  split; [exact Hab|]. split; [exact HnS | exact Ha].
- (* the callee: fuzz_free's text at the call *)
  intros ch1 Ech1 HPRE1.
  assert (Hraz : raZ (ms_regs ms) = BASE + (CRT_PC_B + CRT7_PF_OFF_B)).
  { unfold raZ. rewrite X1. apply unsigned_lit_small.
    destruct (cb7k_ret CRT7_PF_OFF_B ltac:(rewrite EPF; lia) ltac:(rewrite EPF; reflexivity)) as (Hr1 & _). lia. }
  assert (HTR : In (call_trace lyc (pc_free_ra0 (as_code B)) (ms_regs ms) ch1) (as_universe B)).
  { unfold call_trace. destruct (frame0_ok lyc (ms_regs ms)).
    - rewrite t7f_unwind_trace, Hraz. destruct Ech1 as [-> | ->].
      + exact (prh_univ_closure_lit B CTX0 F_check_round_trip RT_fuzz_free _ HCL t7f_rets).
      + exact (prh_univ_closure_site B CTX0 F_check_round_trip _ RT_fuzz_free _ HCL HCTX eq_refl t7f_rets).
    - exact (proj1 HCL RT_fuzz_free). }
  (* the free's trace is a FIXED one of the universe: the call rule asks `admits` (YCbqG.admits_ct_fix), and its
     post is budgeted at that one trace, which PRH_Base.fpost_of_fpostb_fix drops again (its fpostR at wle'); the hull
     budget at the run position (t7f_hull0) *)
  pose proof (FFREE fxk most 0 lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) MDX ch1 saved kw Lamc peakc cntc SIZE_MAXZ 0
    HPRE1 (fun _ => HRL) (fun _ => t7f_ccnt24 _ _ _ _ _ _ _ HRP1) (fun _ => t7f_hull0 _ _ _ HRP1)
    (admits_ct_fix _ _ _ _ _ Sc HTR) X10 (or_intror HinL) HLED1) as HFF.
  rewrite (proj2 (Z.eqb_neq saved 0) Hsv0) in HFF.
  unfold cfg_at, w64 in HFF.
  eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf); [exact HFF|]. intros W' c' _ HP'.
  eapply fpost_of_fpostb_fix in HP'; [|exact HTR].
  (* fuzz_free leaves the float state alone (YCbqG.apost_base_x_F's argument at R) *)
  unfold fpostR, apost_base_xR in HP'.
  destruct HP' as (ly' & S' & Hp' & regs' & mem' & md' & k & Hc' & HJx & Hap & HQ).
  exists fxk, ly', S', Hp', regs', mem', md', k.
  split; [exact Hc'|]. split; [exact HFZ|]. split; [intros r _; reflexivity|]. split; [exact HJx|].
  split; [exact Hap | exact HQ].
- (* the return at PF: t7_at_PF from fuzz_free's post *)
  intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJ2 HJ1 HP2 (HQ & HMN2).
  rewrite HF in HJ1, HMN2.
  (* fuzz_free's post (the text's Q, PRH_FnAlloc.tffP_Q) read through its named projections (tffP_R and its arm
     records tffP_R1 / tffP_R2), never by position *)
  apply PRH_FnAlloc.tffP_R_of with (regs' := regs2) (md' := md2) in HQ.
  pose proof (PRH_FnAlloc.tffP_room HQ) as HRL2. pose proof (PRH_FnAlloc.tffP_pos_free HQ) as Hpos.
  destruct (PRH_FnAlloc.tffP_arm HQ) as [HA1 | HA2];
    [exfalso; exact (Hsv0 (PRH_FnAlloc.tffP1_null (PRH_FnAlloc.tffP_R1_of HA1)))|].
  destruct (PRH_FnAlloc.tffP_R2_of HA2) as (l1 & l2 & HR2).
  destruct (PRH_FnAlloc.tffP2_ablocks HR2) as (b1 & b2 & Eab1 & Eab2).
  pose proof (PRH_FnAlloc.tffP2_lam HR2) as ELam. pose proof (PRH_FnAlloc.tffP2_ledger HR2) as HLED2.
  destruct (Hpos Hsv0 rp_sm rp_x rp_os i1 rp_H0 h1 HRP1 HRun1) as (h2 & HRP2). cbn [length] in HRP2.
  pose proof HJ1 as (HAR2 & HLY1 & _ & _ & _ & HFR1 & _ & _ & G1 & G2 & G3 & G4 & _).
  destruct (alx_layout _ _ _ LAWS lyc Sc Hpc Wc memc mdc ly2 HARc HLY1) as (_ & Efa2 & _).
  assert (EF2 : frame_addr ly2 CRT_CID pos = F) by exact (Efa2 CRT_CID pos).
  (* the lists after the free *)
  assert (HDL2 : forall bk, In bk D -> In bk (l1 ++ l2)).
  { intros bk Hbk. pose proof (HDL bk Hbk) as H1. rewrite ELam in H1.
    apply in_app_or in H1 as [H1 | [<- | H1]];
      [apply in_or_app; left; exact H1 | exfalso; exact (HAP _ HinX Hbk) | apply in_or_app; right; exact H1]. }
  assert (Hsub : forall bk, In bk Lamc -> bk <> (saved, kw) -> In bk (l1 ++ l2)).
  { intros bk Hbk Hne. rewrite ELam in Hbk. apply in_app_or in Hbk as [H1 | [H1 | H1]];
      [apply in_or_app; left; exact H1 | exfalso; exact (Hne (eq_sym H1)) | apply in_or_app; right; exact H1]. }
  assert (HDcL : incl Dc Lamc).
  { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. right. right.
    exact Hbk. }
  assert (HDbL : incl Dback Lamc).
  { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. left.
    exact Hbk. }
  assert (HDc2 : incl Dc (l1 ++ l2)).
  { intros bk Hbk. apply Hsub; [exact (HDcL _ Hbk)|]. intros ->. exact (HnC Hbk). }
  assert (HDb2 : incl Dback (l1 ++ l2)).
  { intros bk Hbk. apply Hsub; [exact (HDbL _ Hbk)|]. intros ->. exact (HnB Hbk). }
  assert (HDcf : forall bk, In bk Dc -> ~ In bk [(saved, kw)]) by (intros bk Hb [<- | []]; exact (HnC Hb)).
  assert (HDbf : forall bk, In bk Dback -> ~ In bk [(saved, kw)]) by (intros bk Hb [<- | []]; exact (HnB Hb)).
  assert (HSC : ~ YI16.sink_open_fp (ablocks_fp [(saved - cf_head, kw + cf_head)])).
  { apply sink_closed_ablocks_fp. constructor; [cbn [fst]; change (@cf_head CfParams_preset) with 16; lia | constructor]. }
  assert (HPL2 : Permutation (l1 ++ l2) ((Dback ++ Dc) ++ Lam)).
  { apply (Permutation_cons_inv (a := (saved, kw))).
    eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- ELam.
    eapply Permutation_trans; [exact HPL|]. rewrite <- !app_assoc. cbn [app].
    apply Permutation_sym. apply Permutation_middle. }
  assert (HPA2 : Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks (Dback ++ Dc))).
  { rewrite Eab2. apply (Permutation_cons_inv (a := (saved - cf_head, kw + cf_head))).
    eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- Eab1.
    eapply Permutation_trans; [exact HPA|]. unfold ck_hblks. rewrite !map_app. cbn [map fst snd].
    rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle. }
  assert (HAP2 : forall bk, In bk (Dback ++ Dc) -> ~ In bk D).
  { intros bk Hbk. apply HAP. apply in_app_or in Hbk as [H1 | H1]; apply in_or_app; [left; exact H1 | right; right; exact H1]. }
  pose proof (t7f_side_after lyc Sc Hpc Wc memc MDX kj pos _ Lamc peakc cntc 0 0 STKFF _ ly2 S2 Hp2 W2 mem2 md2 k1 0 0
    [(saved, kw)] (l1 ++ l2) peakc cntc 0 0 HL1 HJ1 HSC HFPc HDfX ltac:(lia) ltac:(lia) HLED2 (Z.le_refl _)
    (HRL2 Hsv0) HDL2) as HSD2.
  pose proof (cb4_live_call B ARx ly S Hp W regs mem md ch doc t D Lam peak most LAWS HPRE lyc Sc Hpc Wc memc MDX kj pos
    _ Lamc peakc cntc 0 0 STKFF _ ly2 S2 Hp2 W2 mem2 md2 k1 (Dback ++ Dc) (l1 ++ l2) peakc cntc 0 0 HL1 HJ2 HJ1 Hk2
    HFPapp HSD2 HPL2 HPA2 HAP2 HMN2) as HL2.
  apply (HPF fx' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Dc Dback (l1 ++ l2) peakc cntc regs2 mms cset).
  unfold t7_at_PF. rewrite EF2.
  split; [exact Ht|]. split; [exact HFZ2|]. split; [exact (cb4_fregs_trans _ _ _ HFK HFK2)|].
  split; [exact HL2|].
  split; [exact (t7f_bregs_pres _ _ _ HBR1 HP2)|].
  split.
  { unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact HSBK].
    intros j Hj. apply G1; unfold CRT_SP_BACK; lia. }
  split.
  { rewrite <- EF2. exact (t7f_ra_keep lyc Sc Hpc Wc memc MDX kj pos STKFF _ ly2 S2 Hp2 W2 mem2 md2 k1 CRT_OFF_BACK
      HJ HJ1 HFPapp ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) HRB). }
  split.
  { rewrite <- EF2. exact (t7f_ra_keep lyc Sc Hpc Wc memc MDX kj pos STKFF _ ly2 S2 Hp2 W2 mem2 md2 k1 CRT_OFF_V
      HJ HJ1 HFPapp ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) HRV). }
  split; [exact Hcs|]. split; [exact Hcs0|]. split; [exact Hcnt|].
  split.
  { apply (t7f_fdR_move SEGS DOC_D (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc)
      (prh_lin (l1 ++ l2)) (F + CRT_OFF_COPY) Dc HFD); [intros a k Hak; exact (HDc2 _ Hak)|].
    exact (t7f_tree_agree lyc Sc Hpc Wc memc MDX kj pos _ Lamc peakc cntc 0 0 STKFF _ ly2 S2 Hp2 W2 mem2 md2 k1 0 0
      [(saved, kw)] (l1 ++ l2) peakc cntc SIZE_MAXZ 0 most 0 CRT_OFF_COPY Dc HL1 HJ1 HFPc HDfL ltac:(lia) ltac:(lia) HLED2
      HDcL HDc2 HDcf ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia)). }
  split.
  { rewrite <- (t7f_tcJ mms Ht).
    apply (t7f_nodeR_lblk SEGS tcB _ (prh_lin Lamc) (prh_lin (l1 ++ l2)) (F + CRT_OFF_COPY) Dc);
      [|intros a k Hak; exact (HDc2 _ Hak)].
    apply (pj_nodeR_frame SEGS tcB (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) (F + CRT_OFF_COPY)
      Dc HTC).
    exact (t7f_tree_agree lyc Sc Hpc Wc memc MDX kj pos _ Lamc peakc cntc 0 0 STKFF _ ly2 S2 Hp2 W2 mem2 md2 k1 0 0
      [(saved, kw)] (l1 ++ l2) peakc cntc SIZE_MAXZ 0 most 0 CRT_OFF_COPY Dc HL1 HJ1 HFPc HDfL ltac:(lia) ltac:(lia) HLED2
      HDcL HDc2 HDcf ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia)). }
  split; [exact HPC|].
  split.
  { unfold t7_copy_tie. rewrite EF2. exists Fc. split; [|exact HFtc].
    apply (PRH_PjOrder.pj_foR_frame SEGS DOC_D (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc)
      (prh_lin (l1 ++ l2)) (F + CRT_OFF_COPY) Dc Fc HFOc); [intros a k Hak; exact (HDc2 _ Hak)|].
    exact (t7f_tree_agree lyc Sc Hpc Wc memc MDX kj pos _ Lamc peakc cntc 0 0 STKFF _ ly2 S2 Hp2 W2 mem2 md2 k1 0 0
      [(saved, kw)] (l1 ++ l2) peakc cntc SIZE_MAXZ 0 most 0 CRT_OFF_COPY Dc HL1 HJ1 HFPc HDfL ltac:(lia) ltac:(lia)
      HLED2 HDcL HDc2 HDcf ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia)
      ltac:(unfold CRT_OFF_COPY; lia)). }
  split; [exact HdJ|].
  split.
  { apply (t7f_nodeR_lblk SEGS tcB _ (prh_lin Lamc) (prh_lin (l1 ++ l2)) (F + CRT_OFF_BACK) Dback);
      [|intros a k Hak; exact (HDb2 _ Hak)].
    apply (pj_nodeR_frame SEGS tcB (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) (F + CRT_OFF_BACK)
      Dback HBK).
    exact (t7f_tree_agree lyc Sc Hpc Wc memc MDX kj pos _ Lamc peakc cntc 0 0 STKFF _ ly2 S2 Hp2 W2 mem2 md2 k1 0 0
      [(saved, kw)] (l1 ++ l2) peakc cntc SIZE_MAXZ 0 most 0 CRT_OFF_BACK Dback HL1 HJ1 HFPc HDfL ltac:(lia) ltac:(lia) HLED2
      HDbL HDb2 HDbf ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)). }
  split; [exact HPB|].
  split; [exact (Hnext S2 h2 HRP2)|].
  unfold t7_back_tie. rewrite EF2. exists Fb. split; [|exact HFtb].
  apply (PRH_PjOrder.pj_foR_frame SEGS DOC_D (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc)
    (prh_lin (l1 ++ l2)) (F + CRT_OFF_BACK) Dback Fb HFOb); [intros a k Hak; exact (HDb2 _ Hak)|].
  exact (t7f_tree_agree lyc Sc Hpc Wc memc MDX kj pos _ Lamc peakc cntc 0 0 STKFF _ ly2 S2 Hp2 W2 mem2 md2 k1 0 0
    [(saved, kw)] (l1 ++ l2) peakc cntc SIZE_MAXZ 0 most 0 CRT_OFF_BACK Dback HL1 HJ1 HFPc HDfL ltac:(lia) ltac:(lia) HLED2
    HDbL HDb2 HDbf ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)).
Qed.

(* ======================================================================================================== *)
(* PF (+0x800): `ld a0, 0x38(s1)` (&back), `jal pj_free` (+0x804 = CRT_PJF2_CALL_B), return at E (+0x808).
   pj_free's post moves the room position only for a run whose next events are prhPj_free_evs F, F back's ORDER list;
   the boundary's t7_back_tie (Crt102B_T7_bd.v) is that list with the model event's requests fo crt_tc in order, so
   prhPj_free_evs F is the position's next event [HBulk (fo (copy_set ms))] (t7f_free_evs, t7f_fo_ne). *)
Lemma t7_stretch_PF : AT_E -> AT_PF.
Proof.
intros HE fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset HPF.
pose proof HPF as (Ht & HFZ & HFK & HL & HBR & HSBK & HRB & HRV & Hcs & Hcs0 & Hcnt & HFD & HTC & HPC &
  (Fc & HFOc & HFtc) & HdJ & HBK & HPB & HPOS & (FL & HFO & HFt)).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL.
pose proof (crt_live_blocks_perm HL) as HPA. pose proof (crt_live_dx_apart HL) as HAP.
pose proof (crt_live_saved HL) as HSV. pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNl.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK. pose proof (crt_side_room HSD) as HRL.
pose proof (crt_side_arodata HSD) as HRO. pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof t7f_sp as (Hc & H47 & Hs1 & Hs32 & Hs0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof t7f_stk as (Hk1 & Hk2 & Hk3 & Hk4).
pose proof t7f_stkc as Hkc.
pose proof crt7_cuts_B as (EFF & EPF & EE & _ & _).
set (F := frame_addr lyc CRT_CID pos) in *.
set (v := F + CRT_OFF_BACK) in *.
(* pj_free (&back)'s one event: the room position's next *)
assert (Etc : tcB = PresetReqAt.copy_set mms) by exact (t7f_tc mms Ht).
assert (Hevs : PRH_FnPj.prhPj_free_evs FL = [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set mms))]).
{ rewrite <- Etc. apply t7f_free_evs; [exact HFt | rewrite Etc; apply t7f_fo_ne]. }
destruct (t7f_pos_step Sc (PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set mms)))
  [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set mms))] HPOS) as (i1 & h1 & HRP1 & HRun1 & Hnext).
rewrite <- Hevs in HRun1.
(* back's blocks and copy's: held by the walk, apart *)
assert (HDbX : incl Dback (Dback ++ Dc)) by (intros bk Hbk; apply in_or_app; left; exact Hbk).
assert (HDbL : incl Dback Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. left.
  exact Hbk. }
assert (HDcL : incl Dc Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. right.
  exact Hbk. }
assert (HDbb : forall a' k', In (a', k') Dback ->
  0 <= k' /\ In (a' - 16, k' + 16) (ablocks B lyc Sc) /\ ~ In (a' - 16, k' + 16) (ablocks B ly S)).
{ intros a' k' Hak. destruct (t7f_dx _ _ _ _ _ _ _ _ _ _ _ _ _ _ a' k' HL (HDbX _ Hak)) as (_ & H1 & H2 & H3).
  exact (conj H1 (conj H2 H3)). }
pose proof HLED as (_ & Hnd & _).
apply NoDup_ListNoDup in Hnd.
pose proof (Permutation_NoDup (Permutation_map fst HPL) Hnd) as Hnd'.
rewrite <- app_assoc in Hnd'.
assert (HDcf : forall bk, In bk Dc -> ~ In bk Dback).
{ intros bk Hc0 Hb. apply (t7f_nodup_app _ _ _ Hnd' Hb). apply in_or_app. left. exact Hc0. }
(* the run +0x800 .. the jal *)
pose proof (t7f_entry_PF fxk Wc memc rg F HBR HSBK ltac:(lia) ltac:(unfold CRT_OFF_BACK; lia)) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TEB regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TEB regs rg [])) by apply te_env.
pose (RUN := @Crt102Kit.crt_run_xw fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS WS_HJ).
unfold crt_cfg.
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ t7f_wr. }
apply frame_of_read_only in HF; [|vm_compute; reflexivity]. clear HFr HG.
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg _ ?mdx) _ => set (MDX := mdx) in * end.
rewrite HF in HJ.
pose proof {| crt_live_journal := ex_intro _ WS_HJ (conj HJ HB_HJ); crt_live_side := HSD; crt_live_lam_perm := HPL;
  crt_live_blocks_perm := HPA;
  crt_live_dx_apart := HAP; crt_live_saved := HSV; crt_live_frame := HFRM; crt_live_fspill := HSPF;
  crt_live_copy_open := HCR; crt_live_copy_hull := HCH; crt_live_memnorm := HMNl |} as HL1.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_s3 HBR) as R19.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
assert (X10 : getr (ms_regs ms) 10 = w64 v).
{ rewrite Q10.
  assert (E19 : bv_unsigned (ew (TEB regs rg []) 51) = F).
  { change 51%nat with (32 + 19)%nat. rewrite (te_cur regs rg _ 19%bv 19) by reflexivity. rewrite R19.
    apply unsigned_lit_small. lia. }
  rewrite ?E19. unfold v, CRT_OFF_BACK, w64. reflexivity. }
assert (X1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + CRT7_E_OFF_B))) by (rewrite Q1; vm_compute; reflexivity).
assert (KR : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) rr = getr rg rr).
{ intros rr Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [t7f_keep HS |]). destruct Hr. }
assert (HBR1 : bregsB (ms_regs ms) F).
{ refine {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _; crt_bregs_B_s1 := _;
    crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _; crt_bregs_B_s9 := _;
    crt_bregs_B_s11 := _ |}; rewrite KR by (cbv; tauto).
  - exact (crt_bregs_B_sp HBR). - exact (crt_bregs_B_gp HBR). - exact (crt_bregs_B_tp HBR).
  - exact (crt_bregs_B_s0 HBR). - exact (crt_bregs_B_s1 HBR). - exact (crt_bregs_B_s2 HBR).
  - exact (crt_bregs_B_s4 HBR). - exact (crt_bregs_B_s3 HBR). - exact (crt_bregs_B_s7 HBR).
  - exact (crt_bregs_B_s9 HBR). - exact (crt_bregs_B_s11 HBR). }
assert (Hsp : spZ (ms_regs ms) = sp1).
{ unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (HLED1 : prh_ledger B lyc Sc Hpc Wc (ms_mem ms) Lamc peakc cntc SIZE_MAXZ 0 most 0) by (rewrite HF; exact HLED).
(* pj_free's footprint: back's node and its blocks *)
set (FP1 := (v, v + 56) :: ablocks_fp (PRH_FnPj.prhPj_hbl Dback)).
assert (HFPc : t7f_fpc F CRT_OFF_BACK (CRT_OFF_BACK + 56) Dback FP1).
{ intros a Ha. unfold FP1 in Ha. apply inFP_cons in Ha as [Ha | Ha]; [left; unfold v in Ha; lia|].
  right. destruct Ha as (bb & Hbb & Hab). unfold ablocks_fp, PRH_FnPj.prhPj_hbl in Hbb. rewrite map_map in Hbb.
  apply in_map_iff in Hbb as ((a' & k') & Ebb & Hak). subst bb. cbn [fst snd] in Hab.
  change (@cf_head CfParams_preset) with 16 in Hab. exists a', k'. split; [exact Hak | exact Hab]. }
pose proof (t7f_fp_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ CRT_OFF_BACK (CRT_OFF_BACK + 56) _ _ HL HFPc HDbL
  ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)) as HFPapp.
assert (HSC : ~ YI16.sink_open_fp FP1).
{ unfold FP1. apply sink_closed_cons; [cbn [fst]; unfold v, CRT_OFF_BACK; lia|].
  apply sink_closed_ablocks_fp. unfold PRH_FnPj.prhPj_hbl. apply Forall_map. apply Forall_forall.
  intros (a' & k') Hak. cbn [fst]. destruct (HDbb a' k' Hak) as (_ & Hab & _).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & _).
  change (@cf_head CfParams_preset) with 16. lia. }
refine (@cb7k_call fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D Lam peak cnt ran
  most LAWS HPRE fxk STKPF FP1 CRT7_E_OFF_B (SIGMA AS_pj_free) Wc _ _ ms
  MDX lyc Sc Hpc kj pos (Dback ++ Dc) Lamc peakc cntc 0 0 _ (prh_wk F_check_round_trip) HFZ HS _ _ _ _ HBR1 X1 _ _
  Hk4 Hk3 _ _ _).
- reflexivity.
- reflexivity.
- rewrite (te_entry regs rg _ 2%bv 2) by reflexivity. reflexivity.
- rewrite HF. exact HL1.
- rewrite EE. lia.
- rewrite EE. reflexivity.
- (* the callee's footprint: back's node in the frame this function took, and blocks the body made *)
  intros a Ha. destruct (HFPc a Ha) as [Hv | (a' & k' & Hak & Hb)].
  + right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|]. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite t7f_fb. change (frame_addr lyc CRT_CID pos) with F. unfold CRT_OFF_BACK in Hv. lia.
  + right; left. destruct (HDbb a' k' Hak) as (_ & Hab & HnS). exists (a' - 16), (k' + 16).
    split; [exact Hab|]. split; [exact HnS | exact Hb].
- (* the callee: pj_free's text at the call, window d = 0 *)
  intros ch1 Ech1 HPRE1.
  pose proof HPRE1 as ((_ & _ & _ & _ & _ & Hstk1 & _) & _).
  pose proof Hstk1 as (_ & _ & _ & _ & _ & _ & _ & Htop1 & _).
  assert (HWIN : fwin lyc Wc (ms_regs ms) (ms_mem ms) 0).
  { unfold fwin. split; [lia|]. split; [reflexivity|]. split; [lia | intros a Ha; lia]. }
  assert (HFO1 : PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc) DOC_D v Dback FL)
    by (rewrite HF; exact HFO).
  assert (HSLOT : PRH_FnPj.prhPj_slot B STKPF 0 lyc Sc Lamc Wc (ms_regs ms) (ms_mem ms) v).
  { rewrite HF. unfold PRH_FnPj.prhPj_slot. split; [unfold v, CRT_OFF_BACK; lia|].
    split.
    { right; right; left. exists CRT_CID, pos. split; [exact Hin|]. rewrite t7f_fb.
      change (frame_addr lyc CRT_CID pos) with F. unfold v, CRT_OFF_BACK. lia. }
    split.
    { split; [unfold v, CRT_OFF_BACK; lia|]. intros y Hy. apply (apresent_writable SEGS).
      exact (proj1 (Ffr y ltac:(unfold v, CRT_OFF_BACK in Hy; lia))). }
    split.
    { unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fb3. unfold kLowMemEnd, kHighMemEnd.
      destruct Fb3 as (_ & [HLo | [HH1 HH2]]); [left | right; split]; unfold v, CRT_OFF_BACK; lia. }
    split.
    { intros a Ha. split; [exact (proj2 (Ffr a ltac:(unfold v, CRT_OFF_BACK in Ha; lia)))|].
      rewrite Hsp. unfold v, CRT_OFF_BACK in Ha. lia. }
    split; [exact HRB|].
    intros s Hs.
    assert (Hs' : shadow_addr F <= s < shadow_addr F + 64) by (unfold v, CRT_OFF_BACK, shadow_addr, SHADOW_OFF in *; lia).
    replace s with (shadow_addr F + (s - shadow_addr F)) by lia.
    apply (aview_some_of_apresent SEGS). exact (proj1 (Fsh (s - shadow_addr F) ltac:(lia))). }
  assert (Hv0 : v <> 0) by (unfold v, CRT_OFF_BACK; lia).
  assert (Hvc : v < YM05.alloc_ceiling) by (unfold v, CRT_OFF_BACK; lia).
  pose proof (PJFREE fxk most 0 lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) MDX ch1 0 v Dback FL Lamc peakc cntc SIZE_MAXZ 0
    HPRE1 HCL HRL (fun _ => t7f_ccnt24 _ _ _ _ _ _ _ HRP1) (fun _ => t7f_hull0 _ _ _ HRP1) X10 HWIN
    (or_intror (conj Hv0 (conj Hvc (conj HFO1 HSLOT)))) preset_head_wide HLED1) as HPJ.
  rewrite (proj2 (Z.eqb_neq v 0) Hv0) in HPJ.
  unfold cfg_at, w64 in HPJ.
  eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf); [exact HPJ|]. intros W' c' _ HP'.
  unfold fpostWmR, fpostWR in HP'.
  destruct HP' as (ly' & S' & Hp' & regs' & mem' & md' & k & Hc' & HJx & _ & Hap & HQ).
  rewrite !Z.add_0_r in HJx.
  exists fxk, ly', S', Hp', regs', mem', md', k.
  split; [exact Hc'|]. split; [exact HFZ|]. split; [intros r _; reflexivity|]. split; [exact HJx|].
  split; [exact Hap | exact HQ].
- (* the return at E: t7_at_E from pj_free's post *)
  intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJ2 HJ1 HP2 (HQ & HMN2).
  rewrite HF in HJ1, HMN2.
  (* pj_free's post (the text's Q, PRH_FnPj.tpfP_Q) read through its named projections (tpfP_R), never by position *)
  apply PRH_FnPj.tpfP_R_of with (regs' := regs2) (md' := md2) in HQ. destruct HQ as (Lam' & HQR).
  pose proof (PRH_FnPj.tpfP_room HQR) as HRL2. pose proof (PRH_FnPj.tpfP_pos HQR) as Hpos.
  pose proof (PRH_FnPj.tpfP_lam HQR) as HPL'. pose proof (PRH_FnPj.tpfP_ablocks HQR) as HPA'.
  pose proof (PRH_FnPj.tpfP_ledger HQR) as HLED2.
  destruct (Hpos rp_sm rp_x rp_os i1 rp_H0 h1 HRP1 HRun1) as (h2 & HRP2).
  rewrite Hevs in HRP2. cbn [length] in HRP2.
  pose proof HJ1 as (HAR2 & HLY1 & _ & _ & _ & HFR1 & _ & _ & G1 & G2 & G3 & G4 & _).
  destruct (alx_layout _ _ _ LAWS lyc Sc Hpc Wc memc mdc ly2 HARc HLY1) as (_ & Efa2 & _).
  assert (EF2 : frame_addr ly2 CRT_CID pos = F) by exact (Efa2 CRT_CID pos).
  (* the lists after the free: Lam loses back's blocks exactly *)
  assert (HPL2 : Permutation Lam' (Dc ++ Lam)).
  { apply (Permutation_app_inv_l Dback). eapply Permutation_trans; [apply Permutation_sym; exact HPL'|].
    rewrite app_assoc. exact HPL. }
  assert (HPA2 : Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks Dc)).
  { apply (Permutation_app_inv_l (PRH_FnPj.prhPj_hbl Dback)).
    eapply Permutation_trans; [apply Permutation_sym; exact HPA'|].
    eapply Permutation_trans; [exact HPA|].
    unfold ck_hblks, PRH_FnPj.prhPj_hbl. rewrite map_app, !app_assoc. apply Permutation_app_tail.
    apply Permutation_app_comm. }
  assert (HAP2 : forall bk, In bk Dc -> ~ In bk D) by (intros bk Hbk; apply HAP; apply in_or_app; right; exact Hbk).
  assert (HDL2 : forall bk, In bk D -> In bk Lam').
  { intros bk Hbk. pose proof (Permutation_in _ HPL' (HDL bk Hbk)) as H1.
    apply in_app_or in H1 as [H1 | H1]; [exfalso; exact (HAP _ (HDbX _ H1) Hbk) | exact H1]. }
  assert (HDc2 : incl Dc Lam').
  { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL2)). apply in_or_app. left. exact Hbk. }
  pose proof (t7f_side_after lyc Sc Hpc Wc memc MDX kj pos _ Lamc peakc cntc 0 0 STKPF FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    CRT_OFF_BACK (CRT_OFF_BACK + 56) Dback Lam' peakc cntc 0 0 HL1 HJ1 HSC HFPc HDbX
    ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) HLED2 (Z.le_refl _) HRL2 HDL2) as HSD2.
  pose proof (cb4_live_call B ARx ly S Hp W regs mem md ch doc t D Lam peak most LAWS HPRE lyc Sc Hpc Wc memc MDX kj pos
    _ Lamc peakc cntc 0 0 STKPF FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Dc Lam' peakc cntc 0 0 HL1 HJ2 HJ1 Hk4 HFPapp HSD2 HPL2
    HPA2 HAP2 HMN2) as HL2.
  pose proof (t7f_tree_agree lyc Sc Hpc Wc memc MDX kj pos _ Lamc peakc cntc 0 0 STKPF FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    CRT_OFF_BACK (CRT_OFF_BACK + 56) Dback Lam' peakc cntc SIZE_MAXZ 0 most 0 CRT_OFF_COPY Dc HL1 HJ1 HFPc HDbL
    ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) HLED2 HDcL HDc2 HDcf
    ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY, CRT_OFF_BACK; lia))
    as HAGC.
  apply (HE fx' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Dc Lam' peakc cntc regs2 mms cset).
  unfold t7_at_E. rewrite EF2.
  split; [exact Ht|]. split; [exact HFZ2|]. split; [exact (cb4_fregs_trans _ _ _ HFK HFK2)|].
  split; [exact HL2|].
  split; [exact (t7f_bregs_pres _ _ _ HBR1 HP2)|].
  split.
  { rewrite <- EF2. exact (t7f_ra_keep lyc Sc Hpc Wc memc MDX kj pos STKPF _ ly2 S2 Hp2 W2 mem2 md2 k1 CRT_OFF_BACK
      HJ HJ1 HFPapp ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) HRB). }
  split.
  { rewrite <- EF2. exact (t7f_ra_keep lyc Sc Hpc Wc memc MDX kj pos STKPF _ ly2 S2 Hp2 W2 mem2 md2 k1 CRT_OFF_V
      HJ HJ1 HFPapp ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) HRV). }
  split; [exact Hcs|]. split; [exact Hcs0|]. split; [exact Hcnt|].
  split.
  { exact (t7f_fdR_move SEGS DOC_D (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) (prh_lin Lam')
      (F + CRT_OFF_COPY) Dc HFD (fun a k Hak => HDc2 _ Hak) HAGC). }
  split; [exact (Hnext S2 h2 HRP2)|].
  split.
  { apply (t7f_nodeR_lblk SEGS treeJ _ (prh_lin Lamc) (prh_lin Lam') (F + CRT_OFF_COPY) Dc);
      [|intros a k Hak; exact (HDc2 _ Hak)].
    exact (pj_nodeR_frame SEGS treeJ (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc)
      (F + CRT_OFF_COPY) Dc HTC HAGC). }
split; [exact HPC|].
split.
{ unfold t7_copy_tie. rewrite EF2. exists Fc. split; [|exact HFtc].
  exact (PRH_PjOrder.pj_foR_frame SEGS DOC_D (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc)
    (prh_lin Lam') (F + CRT_OFF_COPY) Dc Fc HFOc (fun a k Hak => HDc2 _ Hak) HAGC). }
exact HdJ.
Qed.

End g.
End f.
End t7f.
