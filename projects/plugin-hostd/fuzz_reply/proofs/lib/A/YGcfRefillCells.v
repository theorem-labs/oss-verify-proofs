(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YGcfRefillCells.v (commit f01d79f3fb5, cf refill round 3; file sha256 97ceb340de40) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane for a Theorem Labs lane, lane refill-b2, layer c92d3ee56e6): the RESULT CELLS of a refill walk.
   refill_cells_keep_gen_cf (every refill arm but the report arm): the machine writes stay in refill_frame_cf (the stack
   window, the thread object, class c's region info, class c's user region [RB c, RB c + 2^32), the high shadow), the
   result world's hidden set agrees off that frame, the secondary table and every other class's exh flag are kept, and
   class c's exh byte reads the result's flag.  refill_cells_keep_cf (the B2 form, a corollary): the world kept, writes in
   the window, the thread object and class c's region info, class c's exh byte's view kept.
   The layer's refill leaf (YGcfInstRefill.refill_leaf_core_cf, rwalk_leaf_cf) asks for exh_cell_cf and errb_cells_cf
   at the result.  refill_cells_keep_cf gives both from the entry's, when the model keeps the secondary table and every
   region's holes (so errb_mapped_cf / errb_data_cf / errb_cap_cf / errb_size_cf and every exh_mem_cf are unchanged)
   and the memory is unchanged off [sp0 - RW, sp0), the thread object [ly_T, + kThreadObjSize) and class c's region
   info [RI c, RI c + 128), with class c's exh byte's view kept.  The placement it uses:
   - the errbuf object's 56 bytes are owned static (errb_obj_owned_t), so in Tfib_owned_static (TfibSyms.ts_owned),
     inside the image [TFIB_IMG_LO, TFIB_IMG_END), which img_cover puts in ly_img; ly_img is apart from the stack, the
     thread object and the primary reserve (layout_ok.lo_disj over static_extents);
   - the errb data range is xs_cf's one extent (a secondary map), apart from every static extent (xs_placed_cf, ARmcf's
     amc_xs_placed);
   - every exh cell lies in the primary reserve (lo_space_in), apart from the stack and the thread object (lo_disj),
     and a class c' <> c's cell is outside class c's 128-byte block (HEXO: cf_exh_off = 68).
   Users: the B2 entry / core (MnRefillB2Rcf), the uninit entry, CfW's B3 non-report path.
   EVENT-FREE.  rule 24: no function proved (kind: model / memory frame lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFis.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0qcf YG0scf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs YGcfXsMapped.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG AGif2reply AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstRefill.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis HOBJ : errb_obj_owned_t B.
Hypothesis HEXO : cf_exh_off = 68.

(* No errbuf capacity entry: the capacity is 0 (errb_e's default has length 0). *)
Lemma last_cap_some : forall l i j, last_cap_idx l i (Some j) <> None.
Proof.
induction l as [|sm t IH]; intros i j H; cbn in H; [discriminate|].
destruct (is_errb_cap sm); eapply IH; exact H.
Qed.

Lemma errb_cap_none : forall s, last_cap_idx (st_secs s) 0 None = None -> errb_cap_cf s = 0.
Proof.
intros s. unfold errb_cap_cf, errb_e. generalize 0%nat. generalize (st_secs s).
induction l as [|sm t IH]; intros i H; [reflexivity|]. cbn in H |- *.
destruct (is_errb_cap sm) eqn:E; [exfalso; exact (last_cap_some t (S i) i H)|]. exact (IH (S i) H).
Qed.

(* The errbuf object is in the image. *)
Lemma obj_in_img : forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> TFIB_IMG_LO <= a < TFIB_IMG_END.
Proof.
intros a Ha. pose proof (HOBJ a Ha) as HE. rewrite (ts_owned B TS) in HE. unfold Tfib_owned_static in HE.
unfold TFIB_IMG_LO, TFIB_IMG_END.
repeat (apply Exists_cons in HE; destruct HE as [HE|HE]; [unfold in_zr in HE; cbn [fst snd] in HE; lia|]).
apply Exists_nil in HE. destruct HE.
Qed.

(* The frame the B2 / B3 / uninit walks write: the stack window, the thread object, class c's region info, class c's
   user region [RB c, RB c + 2^32) and the high shadow. *)
Section g.
Variables (Hp : list Z) (ly : alayout) (S S' : astate) (W W' : world tfibsegs) (mem mem' : word -> option byte)
  (c sp0 RW : Z).
Hypothesis HARm : ARmcf B ly S Hp (aview tfibsegs (w_H W) mem).
Hypothesis IMG : img_cover ly.
Hypothesis HcR : 1 <= c <= 31.
Hypotheses (HRW : 0 <= RW) (HSPlo : ly_stk_lo ly + RW <= sp0) (HSPhi : sp0 <= ly_stk_hi ly).
Hypothesis HEX : exh_cell_cf B ly S (aview tfibsegs (w_H W) mem).
Hypothesis HER : errb_cells_cf B ly S (aview tfibsegs (w_H W) mem).
Hypothesis HSECS : st_secs S' = st_secs S.
Hypothesis HHOLES : forall c', c' <> c -> exh_mem_cf S' c' = exh_mem_cf S c'.
Let RI (k : Z) : Z := ly_space ly + kRegionInfoOff + 128 * k.
Let RB (k : Z) : Z := ly_space ly + k * 2 ^ 32.
Definition refill_frame_cf (a : Z) : Prop :=
  (sp0 - RW <= a < sp0) \/ (ly_T ly <= a < ly_T ly + kThreadObjSize) \/ (RI c <= a < RI c + 128) \/
  (RB c <= a < RB c + 2 ^ 32) \/ (kHighShadowBeg <= a < kHighShadowEnd).
Hypothesis HMEQ : forall x : word, ~ refill_frame_cf (bv_unsigned x) -> mem' x = mem x.
Hypothesis HWH : forall x : word, ~ refill_frame_cf (bv_unsigned x) -> w_H W' x = w_H W x.
Hypothesis HEXV : aview tfibsegs (w_H W') mem' (ly_space ly + kRegionInfoOff + 128 * c + 68) = Some (if exh_mem_cf S' c then 1 else 0).
Hypothesis HBAT : exh_mem_cf S' kBatchClass = false.

Let LY : layout_ok ly := amc_layout B ly S Hp _ HARm.

Lemma disj_ij_g : forall i d ei ej, nth_error (static_extents ly) i = Some ei ->
  nth_error (static_extents ly) (i + Datatypes.S d)%nat = Some ej -> zdisjoint ei ej.
Proof. intros i d ei ej Hi Hj. exact (pairwise_ij _ _ i d _ _ (lo_disj ly LY) Hi Hj). Qed.

Lemma keep_at_g : forall a, 0 <= a < 2 ^ 64 -> ~ refill_frame_cf a ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a.
Proof.
intros a Ra NF. assert (NF' : ~ refill_frame_cf (bv_unsigned (Z_to_bv 64 a))) by (rewrite unsigned_lit_small by exact Ra; exact NF).
unfold aview, mbyte, mrestrict. rewrite (HWH _ NF'), (HMEQ _ NF'). reflexivity.
Qed.

Lemma img_apart_g : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> 0 <= a < 2 ^ 64 /\ ~ refill_frame_cf a.
Proof.
intros a Ha. destruct IMG as [I1 I2].
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & HB).
pose proof (lo_space_in ly LY) as [SP1 SP2].
pose proof (disj_ij_g 2 6 _ _ eq_refl eq_refl) as DT. pose proof (disj_ij_g 0 8 _ _ eq_refl eq_refl) as DP.
unfold zdisjoint in DT, DP. cbn [fst snd] in DT, DP.
split; [unfold TFIB_IMG_LO, TFIB_IMG_END in Ha; lia|].
unfold refill_frame_cf, RI, RB, TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, kRegionInfoOff, kSpaceSize, kPrimResvSize,
  kHighShadowBeg, kHighShadowEnd in *.
intros [H|[H|[H|[H|H]]]]; lia.
Qed.

Lemma exh_apart_g : forall k, 1 <= k <= 31 -> k <> c -> 0 <= RI k + 68 < 2 ^ 64 /\ ~ refill_frame_cf (RI k + 68).
Proof.
intros k Hk Hkc.
pose proof (lo_top ly LY) as (_ & _ & _ & HTOP & _ & _ & HB).
pose proof (lo_space_in ly LY) as [SP1 SP2].
pose proof (disj_ij_g 0 1 _ _ eq_refl eq_refl) as DT. pose proof (disj_ij_g 0 7 _ _ eq_refl eq_refl) as DS.
unfold zdisjoint in DT, DS. cbn [fst snd] in DT, DS.
pose proof (lo_high ly LY) as HH. unfold in_high in HH. pose proof (lo_stk_ceil ly LY) as HC.
unfold refill_frame_cf, RI, RB, kRegionInfoOff, kSpaceSize, kPrimResvSize, kHighMemBeg, kHighMemEnd,
  kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *.
assert (k < c \/ c < k) by lia.
split; [lia|]. intros [H0|[H0|[H0|[H0|H0]]]]; lia.
Qed.

Lemma refill_cells_keep_gen_cf :
  exh_cell_cf B ly S' (aview tfibsegs (w_H W') mem') /\ errb_cells_cf B ly S' (aview tfibsegs (w_H W') mem').
Proof.
split.
- (* exh cells *)
  destruct HEX as [HX1 HX2]. split; [|exact HBAT].
  intros k Hk.
  destruct (Z.eq_dec k c) as [->|Hkc].
  + unfold cell_holds, z1, c1. cbn [c_val c_at c_w]. intros i Hi. destruct i as [|i]; [|lia].
    rewrite aeval_aoff by discriminate. cbn [aeval]. rewrite HEXO, Z.add_0_r.
    replace (ly_space ly + (kRegionInfoOff + 128 * c) + 68) with (ly_space ly + kRegionInfoOff + 128 * c + 68) by lia.
    rewrite HEXV. destruct (exh_mem_cf S' c); reflexivity.
  + rewrite (HHOLES k Hkc). eapply cell_holds_agree; [exact (HX1 k Hk)|].
    intros i Hi. unfold z1, c1 in Hi |- *. cbn [c_at c_w] in Hi |- *. assert (i = 0) by (cbn in Hi; lia). subst i. rewrite Z.add_0_r.
    rewrite aeval_aoff by discriminate. cbn [aeval]. rewrite HEXO.
    replace (ly_space ly + (kRegionInfoOff + 128 * k) + 68) with (RI k + 68) by (unfold RI; lia).
    destruct (exh_apart_g k Hk Hkc) as (R & NF). exact (keep_at_g _ R NF).
- (* errb cells *)
  destruct HER as (C0 & C16 & C32 & C40 & C48 & PR & SZ & CM).
  assert (EM : errb_mapped_cf S' = errb_mapped_cf S) by (unfold errb_mapped_cf; rewrite HSECS; reflexivity).
  assert (ED : errb_data_cf ly S' = errb_data_cf ly S) by (unfold errb_data_cf; rewrite HSECS; reflexivity).
  assert (EC : errb_cap_cf S' = errb_cap_cf S) by (unfold errb_cap_cf, errb_e; rewrite HSECS; reflexivity).
  assert (ES : errb_size_cf S' = errb_size_cf S) by (unfold errb_size_cf; rewrite HSECS; reflexivity).
  assert (OBJ : forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 ->
    aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
  { intros a Ha. destruct (img_apart_g a (obj_in_img a Ha)) as (R & NF). exact (keep_at_g _ R NF). }
  unfold errb_cells_cf. rewrite EM, ED, EC, ES.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  + eapply cell_holds_agree; [exact C0|]. intros k Hk. apply OBJ. cbn in Hk |- *. lia.
  + eapply cell_holds_agree; [exact C16|]. intros k Hk. apply OBJ. cbn in Hk |- *. lia.
  + eapply cell_holds_agree; [exact C32|]. intros k Hk. apply OBJ. cbn in Hk |- *. lia.
  + eapply cell_holds_agree; [exact C40|]. intros k Hk. apply OBJ. cbn in Hk |- *. lia.
  + eapply cell_holds_agree; [exact C48|]. intros k Hk. apply OBJ. cbn in Hk |- *. lia.
  + intros a Ha.
    destruct (last_cap_idx (st_secs S) 0 None) as [i|] eqn:EI.
    * pose proof (amc_xs_placed B ly S Hp _ HARm) as XP. unfold xs_placed_cf, xs_cf in XP. rewrite EI in XP.
      apply Forall_cons_iff in XP. destruct XP as [(PA & APP & CEIL & DJ) _].
      cbn [fst snd] in PA, APP, CEIL, DJ.
      assert (EDi : errb_data_cf ly S = ly_sec ly i) by (unfold errb_data_cf; rewrite EI; reflexivity).
      rewrite EDi in Ha.
      pose proof (proj1 (Forall_forall _ _) DJ) as DJ'.
      assert (DT : zdisjoint (ly_sec ly i, errb_cap_cf S) (ly_T ly, kThreadObjSize))
        by (apply DJ'; apply in_or_app; right; unfold static_extents, owned_extents; cbn; tauto).
      assert (DP : zdisjoint (ly_sec ly i, errb_cap_cf S) (ly_prim ly, kPrimResvSize))
        by (apply DJ'; apply in_or_app; right; unfold static_extents, owned_extents; cbn; tauto).
      assert (DS : zdisjoint (ly_sec ly i, errb_cap_cf S) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly))
        by (apply DJ'; apply in_or_app; right; unfold static_extents, owned_extents; cbn; tauto).
      unfold zdisjoint in DT, DP, DS. cbn [fst snd] in DT, DP, DS.
      pose proof (lo_space_in ly LY) as [SP1 SP2]. unfold in_app in APP. pose proof (lo_stk_ceil ly LY) as HC.
      pose proof (lo_top ly LY) as (_ & _ & _ & HTOP & _ & _ & HB).
      assert (Ra : 0 <= a < 2 ^ 64) by (unfold ASAN_CEIL, kHighMemEnd in *; lia).
      assert (NF : ~ refill_frame_cf a).
      { unfold refill_frame_cf, RI, RB, kRegionInfoOff, kSpaceSize, kPrimResvSize, kLowShadowBeg, kHighMemBeg,
          kHighMemEnd, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *.
        intros [H|[H|[H|[H|H]]]]; lia. }
      rewrite (keep_at_g a Ra NF). exact (PR a ltac:(rewrite EDi; exact Ha)).
    * rewrite (errb_cap_none S EI) in Ha. lia.
  + exact SZ.
  + exact CM.
Qed.
End g.

(* The B2 form (W' = W, writes in the window, T and RI c only, class c's exh byte's view kept): a corollary. *)
Section c.
Variables (Hp : list Z) (ly : alayout) (S S' : astate) (W : world tfibsegs) (mem mem' : word -> option byte)
  (c sp0 RW : Z).
Hypothesis HARm : ARmcf B ly S Hp (aview tfibsegs (w_H W) mem).
Hypothesis IMG : img_cover ly.
Hypothesis HcR : 1 <= c <= 31.
Hypotheses (HRW : 0 <= RW) (HSPlo : ly_stk_lo ly + RW <= sp0) (HSPhi : sp0 <= ly_stk_hi ly).
Hypothesis HEX : exh_cell_cf B ly S (aview tfibsegs (w_H W) mem).
Hypothesis HER : errb_cells_cf B ly S (aview tfibsegs (w_H W) mem).
Hypothesis HSECS : st_secs S' = st_secs S.
Hypothesis HHOLES : forall c', exh_mem_cf S' c' = exh_mem_cf S c'.
Let RI (k : Z) : Z := ly_space ly + kRegionInfoOff + 128 * k.
Hypothesis HMEQ : forall x : word, ~ (sp0 - RW <= bv_unsigned x < sp0) ->
  ~ (ly_T ly <= bv_unsigned x < ly_T ly + kThreadObjSize) -> ~ (RI c <= bv_unsigned x < RI c + 128) -> mem' x = mem x.
Hypothesis HEXB : aview tfibsegs (w_H W) mem' (RI c + 68) = aview tfibsegs (w_H W) mem (RI c + 68).

Lemma refill_cells_keep_cf :
  exh_cell_cf B ly S' (aview tfibsegs (w_H W) mem') /\ errb_cells_cf B ly S' (aview tfibsegs (w_H W) mem').
Proof.
apply (refill_cells_keep_gen_cf Hp ly S S' W W mem mem' c sp0 RW HARm IMG HcR HRW HSPlo HSPhi HEX HER HSECS
  (fun c' _ => HHOLES c')).
- intros x NF. apply HMEQ; intros H; apply NF; unfold refill_frame_cf; tauto.
- intros x _. reflexivity.
- (* class c's byte: the entry's cell, the view kept *)
  destruct HEX as [HX1 _]. pose proof (HX1 c HcR) as CC. unfold cell_holds, z1, c1 in CC. cbn [c_val c_at c_w] in CC.
  specialize (CC 0%nat ltac:(lia)). rewrite Z.add_0_r, aeval_aoff in CC by discriminate. cbn [aeval] in CC.
  rewrite HEXO in CC. replace (ly_space ly + (kRegionInfoOff + 128 * c) + 68) with (RI c + 68) in CC by (unfold RI; lia).
  transitivity (aview tfibsegs (w_H W) mem (RI c + 68)); [exact HEXB|].
  rewrite CC, HHOLES. destruct (exh_mem_cf S c); reflexivity.
- destruct HEX as [_ HX2]. rewrite HHOLES. exact HX2.
Qed.
End c.
End b.
End a.

Print Assumptions refill_cells_keep_gen_cf.
Print Assumptions refill_cells_keep_cf.
About refill_cells_keep_gen_cf.
