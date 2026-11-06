(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/CfRBridgeRules.v, with its module paths and module names changed; 65 of its 277 lines of code are new or changed and 598 lines of the source are left out. *)
(* plugin-hostd/fuzz_reply.asan, image A: top_x's allocator rules at route R, at its room record RP_cf and the KF meter
   (a Theorem Labs lane R, CfRBridgeRules.v Section TOPK at R; new file). Rule 24: proves no function (kind: bridge lemmas
   between existing contract forms).
   At CfF1's A rule fit (fu2-mp 9118a6a96818) and part 3c at R (a Theorem Labs lane 955086633601): stated against
   CfRBridgeRules.v's names (RP_cf, cb_cf, cnt_ok_cb_cf, kf_MO_LE_R, kf_MO_OK_HULL_R, AMA_x_kf, and the helpers of its
   Sections AK / B / R), with CfRBridgeRules.v's Section R / TOPK headers verbatim (top_x's ARX with arodata_ok_cf on
   the memory; MO_OK_HULL_R; the image rows HRS / HER; MT_ok). The strndup rule at R is in CfRBridgeRulesRhStrndup.v.
   1. ARE_xR_room_of_cf: CfRBridgeRules.v ARE_x_room_of_cf at R := wle' segs RZ_cf, its Section R frame verbatim.
      The rule text is W_journal_x.v arealloc_cf_rule_c_xR's (after chain_pre: RO := arodata_ok_cf segs TfibB, then
      HA := cf_hull_adm Sc n; part 3c at R: no memnorm premise). The proof is the strict one with:
      - the live block: CfRBridgeAjReallocRh.aj_realloc_at_x_ct_rh at room index 0 over the primed realization
        YGcfInstReallocK.arealloc_realizes_cf_k .. 0 (the reply target arealloc_target_reply at k = 0), with the
        rule's HA as the realization's entry admission;
      - realloc(NULL, n): CfRBridgeAjReallocRh.aj_realloc_null_at_x_ct_rh over the unchanged
        YGcfRealloc.arealloc_null_realizes_cf;
      - the journal copies aj_to_xs_xR / aj_of_xs_xR / aj_k_le_xR (CfRBridgeRulesRh.v), and SRrG_mono for SRr_mono.
      As the strict proof: arodata at the call from the journal's ARX, cf_hull_ok from MO_OK_HULL_R, arodata at the
      post by arodata_post_keep.
   2. Section TOPK_rh, CfRBridgeRules.v Section TOPK's header verbatim (MT_ok, HRS, HER included):
      - ARE_x_kf_rh: arealloc_cf_rule_c_xR at RP_cf, MT, RO := arodata_ok_cf segs TfibB, HA := cf_hull_adm Sc n,
        R := wle' segs RZ_cf, from ARE_xR_room_of_cf;
      - AMA_x_kf_rh: amalloc_cf_rule_c_xR at RP_cf, MT, the same RO and R, from the strict AMA_x_kf by the lift
        CfRBridgeRulesRh.amalloc_cf_rule_c_xR_lift_xs over ARxs (malloc crosses no re-hide; top_x's ARX lies in
        ARxs, ARX_in_xs_rh).
   Numerals: 10, 11, 3, 4, 1 are RISC-V register numbers; 2, 3 (counts and the journal tick) and 4096, 1024, 2 ^ 15
   are CfRBridgeRules.v's texts. No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YGcfRoomPre YGcfXs YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomLive YGcfRoomKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc ReallocP YG03cf YG03dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x CfParamsReply AD2l ACk0 CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt ReplyLSCntL.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfRBridgeCtx CfRBridgePrim CfRBridgeNev.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfRBridgeAjRealloc CfRBridgeRules.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfRBridgeAjReallocRh CfRBridgeRulesRh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstReallocK.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The realloc rule at R (CfRBridgeRules.v Section R's frame, verbatim).       *)
Section R_rh. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_reply.
Variable segs : list Segment.
Hypothesis L : AR_laws_cf segs TfibB.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs TfibB.
(* The room record's two fields the rules read (W_journal_x.v Record roomp at commit 479fec81839: rp_RM, and the count
   premise cnt_ok RP), as parameters: there the bridges apply at RM := rp_RM RPi and CNT := cnt_ok RPi.  R1 (the
   ruled placement): RM is room_live_cf with the budget ignored.  The count premise gives the cf count block. *)
Variable RM : astate -> nat -> Prop.
Variable CNT : list (Z * Z) -> Prop.
Hypothesis HRM : RM = fun S _ => room_live_cf S.
Hypothesis HCNT : forall l, CNT l -> cb_cf l.
(* The meter (KF-COUNT, step 1, row 3): MT is generic; the rules' mo_le post follows from the cf model's
   count of granted secondary entries nsec_cf (YGcfNsec.v, stated here as Section hypotheses with its
   exact names and texts) through three arithmetic facts of MT (MO_LE_M / MO_LE_F / MO_LE_R).  At MT_sec they
   follow from its defining equations (Section TOPK). *)
Variable MT : ameter_ops.
Variable nsec_cf : astate -> Z.
Hypothesis nsec_malloc_cf : forall n tr s,
  cfx_ipost (malloc_cf n tr s) (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, cfx_ipost (free_cf p tr s) (fun r => nsec_cf (snd r) <= nsec_cf s).
Hypothesis MO_LE_M : forall s s' n, 0 <= n -> nsec_cf s' <= nsec_cf s + (if from_primary n then 0 else 1) ->
  mo_le MT s s' (mo_malloc MT n).
Hypothesis MO_LE_F : forall s s', nsec_cf s' <= nsec_cf s -> mo_le MT s s' (mo_free MT).
Hypothesis MO_LE_R : forall s s' n, 0 <= n -> nsec_cf s' <= nsec_cf s + (if from_primary n then 0 else 1) ->
  mo_le MT s s' (mo_malloc MT n + mo_free MT).
(* As Section B's: the hull admission from the rule's count premise; the two image rows. *)
Hypothesis MO_OK_HULL_R : forall s n, 0 <= n -> mo_ok MT s (mo_malloc MT n + mo_free MT) -> cf_hull_ok s.
Hypothesis HRS : relro_seg_t segs.
Hypothesis HER : errno_relro_t TfibB.
Local Abbreviation ARX := (fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @arodata_ok_cf CfImg_A segs TfibB mem).
Local Abbreviation ARxs := (fun ly S Hp (W : world segs) mem md => ARcf segs TfibB ly S Hp W mem md /\ xs_placed_cf ly S).

(* CfRBridgeRules.v ARE_x_room at R: W_journal_x.v arealloc_cf_rule_c_xR at top_x's instance, with RO :=
   arodata_ok_cf segs TfibB and HA := cf_hull_adm Sc n. *)
Definition ARE_xR_room (pc : Z) : Prop :=
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k p n0 n (o : Z) raw ch (kr : nat),
ajournal_xR segs TfibB [] ARX (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
(p = 0 \/ In (p, n0) (ablocks TfibB lyc Sc)) ->
getr regsT 10 = w64 p -> getr regsT 11 = w64 n ->
1 <= n < fr_MMAX -> blocks_bytes Sc + n <= LIVE_MAX ->
CNT (ablocks TfibB lyc Sc) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
ly_bot lyc + 4096 < spZ regsT ->
getr regsT 3 = w64 (as_gp TfibB) -> getr regsT 4 = w64 (as_tp TfibB) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
arodata_ok_cf segs TfibB memT ->
cf_hull_adm Sc n ->
In (raZ regsT :: spine ch) CTX_AREALLOC ->
RM Sc (2 + kr) ->
(p <> 0 -> In (p, n0) (ablocks TfibB ly S) -> forall i, 0 <= i < req_size n0 -> inFP FP (p + i)) ->
mo_ok MT Sc (mo_malloc MT n + mo_free MT) ->
SRrG segs (wle' segs RZ_cf) W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs TfibB [] ARX (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 3) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\
(p = 0 -> Permutation (ablocks TfibB ly2 S2) ((res, n) :: ablocks TfibB lyc Sc)) /\
(p <> 0 -> exists l1 l2, ablocks TfibB lyc Sc = l1 ++ (p, n0) :: l2 /\
  Permutation (ablocks TfibB ly2 S2) ((res, n) :: l1 ++ l2)) /\
(p <> 0 -> forall i, 0 <= i < Z.min n0 n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) memT (p + i)) /\
acall_kept segs TfibB lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o)
  (fun a => (res <= a < res + req_size n) \/ (p <> 0 /\ p <= a < p + req_size n0)) /\
mo_le MT Sc S2 (mo_malloc MT n + mo_free MT) /\
RM S2 kr /\
(forall i, 0 <= i < 4 -> aview segs (w_H W2) mem2 (as_errno TfibB + i) = aview segs (w_H W) memT (as_errno TfibB + i)) /\
(forall a, in_img segs a -> ~ aowned TfibB lyc Sc a -> ~ aowned TfibB ly2 S2 a ->
 ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
 ~ ((res <= a < res + req_size n) \/ (p <> 0 /\ p <= a < p + req_size n0)) ->
 apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).

(* CfRBridgeRules.v ARE_x_room_of_cf at R (changes in the header). *)
Theorem ARE_xR_room_of_cf : forall pc,
  YGcfInstReallocK.arealloc_realizes_cf_k segs TfibB [] pc 0 ->
  YGcfRealloc.arealloc_null_realizes_cf segs TfibB [] pc ->
  ARE_xR_room pc.
Proof.
intros pc AR ARN W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k p n0 n o raw ch kr
  HJ Hp0 Ha0 Ha1 Hn Hlive HCB Hsp Hal Hneg Hbud Hpfx Hgp Htp Hra Hraw Hch _ HADM HCTX HRL HFP HMO.
destruct (HCNT _ HCB) as (Hc1 & Hc2 & Hc3). rewrite HRM in HRL. cbv beta in HRL.
pose proof HJ as ([HARc [HHp HAD]] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
subst Hpc.
pose proof (proj1 (count_block_iff_cfr TfibB lyc Sc) (conj Hc1 (conj Hc2 Hc3))) as (HSEC & H24 & HB24 & HPRIM).
pose proof (room_live_room Sc HRL) as HROOM.
pose proof (MO_OK_HULL_R Sc n ltac:(lia) HMO) as HHULL.
pose proof (QMm_cf_of_room segs TfibB lyc Sc [] W memT mdc HARc HQT HROOM HHULL HAD) as HQM.
pose proof HQM as (_ & _ & _ & _ & HBR & _).
pose proof (universe_ok_of_ARcf segs TfibB lyc Sc [] W memT mdc HARc) as HU.
pose proof (amc_wf _ _ _ _ _ (proj1 HARc)) as HWF.
pose proof (cfr_ctx_arealloc lyc regsT ch Sc HCTX) as Htr. unfold cf_trace_ok, cf_tr_ok in Htr.
pose proof (aj_to_xs_xR segs (wle' segs RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJx.
assert (Hn' : 1 <= n < cf_malloc_max) by exact Hn.
assert (HARxs : ARxs lyc Sc [] W memT mdc) by exact (conj HARc (xs_placed_of_ARcf segs TfibB lyc Sc [] W memT mdc HARc)).
destruct (Z.eq_dec p 0) as [-> | Hpn].
- (* realloc(NULL, n) *)
  pose proof (aj_realloc_null_at_x_ct_rh segs TfibB [] L segs_low errno_low HU pc
    W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc [] mdc k n o raw ch ARN HJx Ha0 Ha1 Hn' Hlive
    Hsp Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr) as HSR.
  eapply SRrG_mono; [exact HSR|].
  intros W2 c2 HwleW (ly2 & S2 & regs2 & mem2 & md2 & res & Hc2' & HJ2 & Hpres & Hres & Hfrs & HPRE &
    (q & trc & Hpath & Hgf & Hleaf & Href & Hiff & Hres2 & Herrno & Hrawf) & Harms).
  assert (Hqn : q <> PNull)
    by (intros E; exact (refused_impossible n _ Sc S2 HU HWF HQT HPRIM HBR Htr (Href E))).
  destruct Harms as [(Hr0 & _) | (H4096 & Eab & Hkept)]; [exfalso; apply Hqn; apply Hiff; exact Hr0|].
  pose proof (realloc_null_tree_nev n _ Sc trc q S2 Hpath Hqn) as Hnev.
  pose proof HJ2 as (HA2 & _).
  pose proof HPRE as (_ & _ & _ & Hslo & _).
  (* the post's arodata, from the raw frame: the new block is a live block of the post, off the image *)
  assert (HAD2 : arodata_ok_cf segs TfibB mem2).
  { apply (arodata_post_keep segs TfibB lyc Sc [] W regsT memT mdc ly2 S2 [] W2 mem2 md2
      (fun x => (q <> PNull /\ res <= x < res + req_size n) \/ Exists (in_zr x) (xs_cf lyc Sc ++ xs_cf ly2 S2))
      HRS HER HARc (proj1 HA2) Hslo); [| |exact HAD].
    - intros a I1 I2 X1 X2 [[_ Hb] | Hx].
      + assert (Hinab : In (res, n) (ablocks TfibB ly2 S2)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
        exact (ablock_not_img_cfr TfibB ly2 S2 [] _ res n a (proj1 (proj1 HA2)) Hinab I2 Hb).
      + apply Exists_app in Hx as [Hx|Hx]; [exact (X1 Hx) | exact (X2 Hx)].
    - intros x NX. apply Hrawf; intros H; apply NX; tauto. }
  exists ly2, S2, [], regs2, mem2, md2, res.
  split; [exact Hc2'|].
  split.
  { apply (aj_of_xs_xR segs (wle' segs RZ_cf)); [reflexivity | exact HAD2 |]. eapply aj_k_le_xR; [|exact HJ2]; lia. }
  split; [exact Hpres|]. split; [exact Hres|]. split; [exact Hfrs|]. split; [exact H4096|].
  split; [intros _; rewrite Eab; apply Permutation_sym; apply Permutation_cons_append|].
  split; [intros Hc; exfalso; exact (Hc eq_refl)|].
  split; [intros Hc; exfalso; exact (Hc eq_refl)|].
  split; [eapply kept_mono; [|exact Hkept]; intros a Ha; left; exact Ha|].
  split; [exact (MO_LE_R Sc S2 n ltac:(lia) (cfx_ipost_apath _ _ trc (q, S2) (nsec_realloc_null_tree nsec_cf nsec_malloc_cf nsec_free_cf n _ Sc) Hpath))|].
  split.
  { rewrite HRM. exact (room_live_call_keep (as_universe TfibB) 1024 (2 ^ 15) Sc S2 HWF HQT HSEC H24 HB24 HRL
      (or_intror (or_intror (or_intror (ex_intro _ n (ex_intro _ _ (ex_intro _ trc (ex_intro _ q Hpath)))))))). }
  split.
  { intros i Hi. apply (aview_img_eq segs segs_low).
    - exact (proj1 (proj2 errno_low) (as_errno TfibB + i) ltac:(lia)).
    - exact (Herrno Hqn i Hi). }
  intros a Hi Ho1 Ho2 He Hb.
  apply (img_present_keep segs L segs_low lyc Sc W regsT memT mdc ly2 S2 W2 mem2 md2 (fun x => q <> PNull /\ res <= x < res + req_size n) a
    HARxs HA2 Hslo); [| | exact Hi | exact Ho1 | exact He].
  + intros x H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 |].
    intros [Hx | Hx]; apply H4; [left; exact Hx | right; exact Hx].
  + intros [_ Hblk] Hi'.
    assert (Hinab : In (res, n) (ablocks TfibB ly2 S2)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
    assert (LAWSx : AR_laws_x segs TfibB ARxs cf_head) by exact (AR_laws_x_xs segs TfibB L).
    destruct (alx_client_img _ _ _ LAWSx ly2 S2 [] W2 mem2 md2 a HA2
      (or_introl (ex_intro _ res (ex_intro _ n (conj Hinab Hblk))))) as (_ & Hni).
    exact (Hni Hi').
- (* realloc(p, n) of a live block *)
  destruct Hp0 as [E | Hin]; [exfalso; exact (Hpn E)|].
  pose proof (aj_realloc_at_x_ct_rh segs TfibB [] L segs_low errno_low HU 0 pc
    (amx_realloc_rp_room TfibB HU)
    W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc [] mdc k p n0 n o raw ch AR HJx Hin (fun H => H) Ha0 Ha1 Hn' Hlive
    Hsp Hal Hneg Hbud Hgp Htp Hra Hraw HQM (room_live_room_k Sc HRL) Hch Htr HADM (HFP Hpn)) as HSR.
  eapply SRrG_mono; [exact HSR|].
  intros W2 c2 HwleW (ly2 & S2 & regs2 & mem2 & md2 & res & Hc2' & HJ2 & Hpres & Hres & Hfrs & HPRE &
    (q & p' & trc & Hpq & Hpin & Hpath & Hgf & Hleaf & Href & EHp & Hiff & Hres2 & Hcopy & Herrno & Hrawf) & Harms).
  assert (Hqn : q <> PNull)
    by (intros E; exact (refused_impossible n _ Sc S2 HU HWF HQT HPRIM HBR Htr (Href E))).
  destruct Harms as [(Hr0 & _) | (H4096 & Hsplit & Hkept)]; [exfalso; apply Hqn; apply Hiff; exact Hr0|].
  pose proof (realloc_tree_nev p' n _ Sc trc q S2 Hpath Hqn) as Hnev.
  assert (Hn0 : 0 <= n < cf_malloc_max) by (destruct Hn' as [Hn1 Hn2]; split; [lia | exact Hn2]).
  pose proof HJ2 as (HA2 & _).
  pose proof HPRE as (_ & _ & _ & Hslo & _).
  (* the post's arodata, from the raw frame: the new block (live at the post) and the old one (live at the call) are
     off the image *)
  assert (HAD2 : arodata_ok_cf segs TfibB mem2).
  { apply (arodata_post_keep segs TfibB lyc Sc [] W regsT memT mdc ly2 S2 [] W2 mem2 md2
      (fun x => (q <> PNull /\ res <= x < res + req_size n) \/ (q <> PNull /\ p <= x < p + req_size n0) \/
         Exists (in_zr x) (xs_cf lyc Sc ++ xs_cf ly2 S2))
      HRS HER HARc (proj1 HA2) Hslo); [| |exact HAD].
    - intros a I1 I2 X1 X2 [[_ Hb] | [[_ Hb] | Hx]].
      + destruct Hsplit as (l1 & l2 & _ & Hperm2).
        assert (Hinab : In (res, n) (ablocks TfibB ly2 S2))
          by (apply (Permutation_in _ (Permutation_sym Hperm2)); left; reflexivity).
        exact (ablock_not_img_cfr TfibB ly2 S2 [] _ res n a (proj1 (proj1 HA2)) Hinab I2 Hb).
      + exact (ablock_not_img_cfr TfibB lyc Sc [] _ p n0 a (proj1 HARc) Hin I1 Hb).
      + apply Exists_app in Hx as [Hx|Hx]; [exact (X1 Hx) | exact (X2 Hx)].
    - intros x NX. apply Hrawf; intros H; apply NX; tauto. }
  exists ly2, S2, [], regs2, mem2, md2, res.
  split; [exact Hc2'|].
  split.
  { apply (aj_of_xs_xR segs (wle' segs RZ_cf)); [reflexivity | exact HAD2 |].
    replace (k + 3) with (k + (st_nev S2 - st_nev Sc)) by lia. exact HJ2. }
  split; [exact Hpres|]. split; [exact Hres|]. split; [exact Hfrs|]. split; [exact H4096|].
  split; [intros Hc; exfalso; exact (Hpn Hc)|].
  split; [intros _; exact Hsplit|].
  split; [intros _; exact (Hcopy Hqn)|].
  split; [eapply kept_mono; [|exact Hkept]; intros a [Ha | Ha]; [left; exact Ha | right; exact (conj Hpn Ha)]|].
  split; [exact (MO_LE_R Sc S2 n ltac:(lia) (cfx_ipost_apath _ _ trc (q, S2) (nsec_realloc_tree nsec_cf nsec_malloc_cf nsec_free_cf p' n _ Sc) Hpath))|].
  split.
  { rewrite HRM. exact (room_live_call_keep (as_universe TfibB) 1024 (2 ^ 15) Sc S2 HWF HQT HSEC H24 HB24 HRL
      (or_intror (or_intror (or_introl (ex_intro _ p' (ex_intro _ n (ex_intro _ _ (ex_intro _ trc (ex_intro _ q
        (conj HU (conj (admits_fix _ _ Sc HU Htr) (conj Hn0 (conj Hlive Hpath))))))))))))). }
  split.
  { intros i Hi. apply (aview_img_eq segs segs_low).
    - exact (proj1 (proj2 errno_low) (as_errno TfibB + i) ltac:(lia)).
    - exact (Herrno Hqn i Hi). }
  intros a Hi Ho1 Ho2 He Hb.
  apply (img_present_keep segs L segs_low lyc Sc W regsT memT mdc ly2 S2 W2 mem2 md2
    (fun x => (q <> PNull /\ res <= x < res + req_size n) \/ (q <> PNull /\ p <= x < p + req_size n0)) a
    HARxs HA2 Hslo); [| | exact Hi | exact Ho1 | exact He].
  + intros x H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 |].
    intros [Hx | [Hx | Hx]]; apply H4; [left; left; exact Hx | left; right; exact Hx | right; exact Hx].
  + intros [[_ Hblk] | [_ Hblk]] Hi'.
    * apply Hb. left. exact Hblk.
    * apply Hb. right. exact (conj Hpn Hblk).
Qed.
End R_rh.

(* ---------------------------------------------------------------------------- *)
(* 2. KF-COUNT at R: CfRBridgeRules.v Section TOPK's header verbatim.              *)
Section TOPK_rh. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_reply.
Variable segs : list Segment.
Hypothesis L : AR_laws_cf segs TfibB.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs TfibB.
Local Abbreviation ARX := (fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @arodata_ok_cf CfImg_A segs TfibB mem).
(* FIT CHECK of the relation: the rules' ARX is top_x's relation after W1, whose text is quoted
   here VERBATIM from commit b27e847023f8, lib/A/W_LLVMFuzzerTestOneInput_top_x.v:171-172
   (Definition ARX's body); it closes by reflexivity only if the two are the same term. *)
Goal ARX = (
  fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @YG0dcf.arodata_ok_cf CfImg_A segs TfibB mem).
Proof. reflexivity. Qed.
Variable MT : ameter_ops.
Variable nsec_cf : astate -> Z.
Hypothesis nsec_malloc_cf : forall n tr s,
  cfx_ipost (malloc_cf n tr s) (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, cfx_ipost (free_cf p tr s) (fun r => nsec_cf (snd r) <= nsec_cf s).
(* MT_sec's defining equations, its literal text (ReplyKfMeter.v at a968c6e24aec: mkAMeter (fun s m => nsec s + m <= KMAX)
   (fun s s' m => nsec s' <= nsec s + m) (fun n => if 64512 <? n then 1 else 0) 0); each holds by reflexivity at
   MT := MT_sec nsec_cf cf_kmax.  mo_ok is not used by these rules' posts. *)
Hypothesis MT_malloc : forall n, mo_malloc MT n = if 64512 <? n then 1 else 0.
Hypothesis MT_free : mo_free MT = 0.
Hypothesis MT_le : forall s s' m, mo_le MT s s' m <-> nsec_cf s' <= nsec_cf s + m.
(* MT_sec's fourth defining equation, its mo_ok (MT_ok, the same text route R's TOPK_rh takes, commit
   07260ccc92a1 lib/A/CfRBridgeRulesRhTop.v:267): at MT := MT_sec YGcfNames.nsec_cf cf_kmax it holds by iff_refl. *)
Hypothesis MT_ok : forall s m, mo_ok MT s m <-> YGcfNames.nsec_cf s + m <= cf_kmax.
(* The unit's two image rows (Section B's HRS / HER). *)
Hypothesis HRS : relro_seg_t segs.
Hypothesis HER : errno_relro_t TfibB.

Theorem ARE_x_kf_rh : forall pc,
  YGcfInstReallocK.arealloc_realizes_cf_k segs TfibB [] pc 0 ->
  YGcfRealloc.arealloc_null_realizes_cf segs TfibB [] pc ->
  arealloc_cf_rule_c_xR segs TfibB [] ARX MT fr_MMAX RP_cf (arodata_ok_cf segs TfibB)
    (fun (_ : alayout) (Sc : astate) (_ : bvmap 5 word) (_ : list (Z * Z * Z)) (_ : Z) (n : Z) => cf_hull_adm Sc n)
    CTX_AREALLOC (wle' segs RZ_cf) pc.
Proof.
intros pc AR ARN. eapply (ARE_xR_room_of_cf segs L segs_low errno_low (rp_RM RP_cf) (cnt_ok RP_cf) eq_refl cnt_ok_cb_cf
  MT nsec_cf); first [exact AR | exact ARN | exact nsec_malloc_cf | exact nsec_free_cf | exact HRS | exact HER
  | exact (kf_MO_LE_R MT nsec_cf MT_malloc MT_free MT_le)
  | (intros s0 n0 Hn0 H0; eapply kf_MO_OK_HULL_R; eassumption)].
Qed.

(* top_x's relation lies in YGcallcf's ARxs, which has the cf laws (AR_laws_x_xs). *)
Lemma ARX_in_xs_rh : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
  ARcf segs TfibB ly S Hp W mem md /\ xs_placed_cf ly S.
Proof. intros ly S Hp W mem md H. exact (conj (proj1 H) (xs_placed_of_ARcf segs TfibB ly S Hp W mem md (proj1 H))). Qed.

Theorem AMA_x_kf_rh : amalloc_realizes_cf segs TfibB ->
  amalloc_cf_rule_c_xR segs TfibB [] ARX MT fr_MMAX RP_cf (arodata_ok_cf segs TfibB) CTX_AMALLOC (wle' segs RZ_cf).
Proof.
intros AM.
apply (amalloc_cf_rule_c_xR_lift_xs segs TfibB [] ARX _ (AR_laws_x_xs segs TfibB L) ARX_in_xs_rh segs_low
  (wle' segs RZ_cf) (wle_wle' segs RZ_cf) (wle'_trans segs RZ_cf)).
eapply AMA_x_kf; first [exact AM | eassumption].
Qed.
End TOPK_rh.
