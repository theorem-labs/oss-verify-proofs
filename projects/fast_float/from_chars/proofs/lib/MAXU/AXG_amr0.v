(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfPre MngNtfC MngGM MngCtx2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM MngNtfS MngMWP MngMW0 MngMW1 MngMW2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_am1 AXG_am3 AXG_am4 AXG_am5.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt10z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt100z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am3 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am4 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am5.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_of_res1 : forall s r rg o k, region_of s r = Some rg ->
  region_of (s_res1 s r rg o) k = if Nat.eqb k r then Some (rw_page rg o) else region_of s k.
Proof.
  intros s r rg o k Hr. unfold s_res1. rewrite region_of_upd.
  destruct (Nat.eqb k r) eqn:E; [|reflexivity]. apply Nat.eqb_eq in E. subst k.
  replace (Nat.ltb r (length (st_regions s))) with true by (symmetry; apply Nat.ltb_lt; exact (region_of_lt _ _ _ Hr)). reflexivity.
Qed.

Lemma footprint_res1 : forall s r rg o, region_of s r = Some rg -> rg_kind rg <> RkMap -> footprint (s_res1 s r rg o) = footprint s.
Proof.
  intros s r rg o Hr Hk. unfold footprint. f_equal. f_equal.
  replace (length (st_regions (s_res1 s r rg o))) with (length (st_regions s)) by (unfold s_res1; cbn [st_regions set_regions]; symmetry; apply length_lupd).
  apply flat_map_ext. intros k. rewrite (region_of_res1 s r rg o k Hr).
  destruct (Nat.eqb k r) eqn:E; [|reflexivity]. apply Nat.eqb_eq in E. subst k. rewrite Hr. cbn [rw_page rg_kind].
  destruct (rg_kind rg); [reflexivity | reflexivity | exfalso; exact (Hk eq_refl)].
Qed.

Lemma image_res1 : forall s r rg o, image (s_res1 s r rg o) = image s.
Proof.
  intros s r rg o. unfold image. rewrite (areas_cells_ext s (s_res1 s r rg o) (st_areas (s_res1 s r rg o))) by (intros q; reflexivity). reflexivity.
Qed.

Lemma rgeoA_res1 : forall HTOP L s r rg o, region_of s r = Some rg -> rgeoA HTOP L s -> rgeoA HTOP L (s_res1 s r rg o).
Proof.
  intros HTOP L s r rg o Hr HG k rgk Hk Hl. rewrite (region_of_res1 s r rg o k Hr) in Hk.
  destruct (Nat.eqb k r) eqn:E; [|exact (HG k rgk Hk Hl)]. apply Nat.eqb_eq in E. subst k. injection Hk as <-.
  exact (HG r rg Hr Hl).
Qed.

Lemma rdisj_res1 : forall L s r rg o, region_of s r = Some rg -> rdisj L s -> rdisj L (s_res1 s r rg o).
Proof.
  intros L s r rg o Hr HD r1 r2 rg1 rg2 Hne H1 H2 L1 L2. rewrite (region_of_res1 s r rg o r1 Hr) in H1. rewrite (region_of_res1 s r rg o r2 Hr) in H2.
  destruct (Nat.eqb r1 r) eqn:E1; destruct (Nat.eqb r2 r) eqn:E2.
  - apply Nat.eqb_eq in E1, E2. subst. exfalso. exact (Hne eq_refl).
  - apply Nat.eqb_eq in E1. subst r1. injection H1 as <-. exact (HD r r2 rg rg2 Hne Hr H2 L1 L2).
  - apply Nat.eqb_eq in E2. subst r2. injection H2 as <-. exact (HD r1 r rg1 rg Hne H1 Hr L1 L2).
  - exact (HD r1 r2 rg1 rg2 Hne H1 H2 L1 L2).
Qed.

Lemma RMONO_res1 : forall s r rg o, region_of s r = Some rg -> RMONO s (s_res1 s r rg o).
Proof.
  intros s r rg o Hr. split.
  - unfold s_res1. cbn [st_regions set_regions]. rewrite length_lupd. lia.
  - intros k rgk Hk Hl. rewrite (region_of_res1 s r rg o k Hr). destruct (Nat.eqb k r) eqn:E.
    + apply Nat.eqb_eq in E. subst k. rewrite Hr in Hk. injection Hk as <-. exists (rw_page rg o).
      split; [reflexivity|]. split; [exact Hl|]. split; [reflexivity | cbn [rw_page rg_len]; lia].
    + exists rgk. split; [exact Hk|]. split; [exact Hl|]. split; [reflexivity | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fp_open_old : forall p s f, In f (footprint s) -> In f (footprint (open_st p s)).
Proof.
  intros p s f H. unfold footprint in H |- *. destruct H as [<-|H]; [left; reflexivity|]. right.
  apply in_app_iff in H as [H|H]; apply in_app_iff; [left | right; exact H].
  rewrite st_areas_open, map_app. apply in_app_iff. left. exact H.
Qed.

Lemma fp_open_new : forall p s, In (LMem p, PGSZ) (footprint (open_st p s)).
Proof.
  intros p s. unfold footprint. right. apply in_app_iff. left. rewrite st_areas_open, map_app. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma fp_open_inv : forall p s f, In f (footprint (open_st p s)) -> In f (footprint s) \/ f = (LMem p, PGSZ).
Proof.
  intros p s f H. unfold footprint in H |- *. destruct H as [<-|H]; [left; left; reflexivity|].
  apply in_app_iff in H as [H|H].
  - rewrite st_areas_open, map_app in H. apply in_app_iff in H as [H|H].
    + left. right. apply in_app_iff. left. exact H.
    + right. destruct H as [<-|[]]. reflexivity.
  - left. right. apply in_app_iff. right. exact H.
Qed.

(* [comment removed for export] *)
Lemma open_page_fresh : forall HTOP X R U s L p, HTOP <= 2^47 -> Inv X R U (open_st p s) -> ly_ctx L = 0x97c98 ->
  rgeoA HTOP L s -> rdisj L s ->
  forall f, In f (footprint s) -> ranges_disjoint (loc_addr L (LMem p), PGSZ) (crange L f).
Proof.
  intros HTOP X R U s L p HTB HI Hctx HG HD f Hf.
  assert (HGo : rgeoA HTOP L (open_st p s)) by (intros k rg Hk Hl; exact (HG k rg Hk Hl)).
  assert (HDo : rdisj L (open_st p s)) by (intros r1 r2 rg1 rg2 Hne H1 H2 L1 L2; exact (HD r1 r2 rg1 rg2 Hne H1 H2 L1 L2)).
  pose proof (layout_of_geo HTOP HTB X R U (open_st p s) L HI Hctx HGo HDo) as (_ & _ & HPW & _).
  pose proof (inv_areas HI) as (A1 & A2 & _). rewrite st_areas_open in A1.
  assert (Hnp : ~ In p (st_areas s)).
  { intros Hin. apply (@List.NoDup_remove_2 _ (st_areas s) [] p A1). rewrite app_nil_r. exact Hin. }
  assert (Hpa : In p (st_areas (open_st p s))) by (rewrite st_areas_open; apply in_app_iff; right; left; reflexivity).
  destruct (A2 p Hpa) as (r & o & rg & Ep & Hom & Ho & _).
  assert (Hne : (LMem p, PGSZ) <> f).
  { intros <-. destruct (footprint_inv s _ Hf) as [E | [(a & Ha & E) | (k & rgk & _ & _ & _ & E)]]; try discriminate.
    - injection E as <-. exact (Hnp Ha).
    - injection E as E1 _. rewrite Ep in E1. injection E1 as _ E2. unfold PGSZ in *. lia. }
  destruct (pairwise_map_In _ (crange L) _ _ _ HPW (fp_open_new p s) (fp_open_old p s f Hf) Hne) as [D|D]; [exact D|].
  unfold ranges_disjoint, crange in *. cbn [fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
Lemma open_no_key : forall X R U s p, Inv X R U (open_st p s) ->
  forall q, In q (keys s) -> forall k, 0 <= k < 101 -> q <> padd p (AREA_HDR + META_SIZE * k).
Proof.
  intros X R U s p HI q Hq k Hk E. pose proof (inv_keys HI) as (_ & KP & _).
  destruct (KP q Hq) as (a & j & Ha & Hj & Eq).
  pose proof (inv_areas HI) as (A1 & A2 & _).
  unfold handed in Hj. rewrite st_areas_open, last_app_single in Hj. cbn [st_avail_meta_count open_st set_avail_meta set_avail_meta_count] in Hj.
  destruct (sptr_eqb a p) eqn:Eap; [unfold METAS_PER_AREA in Hj; lia|].
  apply sptr_eqb_neq in Eap.
  destruct (A2 a Ha) as (ra & oa & rga & -> & Hoa & _).
  assert (Hpa : In p (st_areas (open_st p s))) by (rewrite st_areas_open; apply in_app_iff; right; left; reflexivity).
  destruct (A2 p Hpa) as (rp & op & rgp & -> & Hop & _).
  rewrite Eq in E. cbn [padd] in E. injection E as E1 E2. subst rp.
  apply Eap. f_equal. unfold PGSZ, AREA_HDR, META_SIZE in *. unfold handed in Hj.
  apply Z.mod_divide in Hoa; [|lia]. apply Z.mod_divide in Hop; [|lia].
  destruct Hoa as (k1 & ->). destruct Hop as (k2 & ->). unfold METAS_PER_AREA in Hj. assert (k1 = k2) by nia. subst. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma holds_after_w : forall L (m2 m : word -> option byte) l w v' a v,
  loc_addr L l = a -> (1 <= w <= 8)%nat -> (forall z, v' <> VLo5 z) -> 0 <= a -> a + Z.of_nat w <= 2^64 ->
  v mod 2^(8 * Z.of_nat w) = sval_num L v' mod 2^(8 * Z.of_nat w) ->
  (forall x, a <= x < a + Z.of_nat w -> m2 (wa x) = wbytes m (wa a) (word_to_le_bytes w (wa v)) (wa x)) ->
  cell_holds L (bview SEGS m2) (MCell l w v').
Proof.
  intros L m2 m l w v' a v Ea Hw Hv H1 H2 Hm Hx.
  apply (cell_holds_frame L (bview SEGS (wbytes m (wa a) (word_to_le_bytes w (wa v)))) (bview SEGS m2)); [cbn [mc_w]; lia | |].
  - rewrite <- Ea. apply holds_wb; cbn [mc_loc mc_w mc_val]; [exact Hv | lia | lia | lia | exact Hm].
  - intros x Hin. unfold in_rng, cell_range in Hin. cbn [fst snd mc_loc mc_w] in Hin. rewrite Ea in Hin. apply MngWb.bview_ext. apply Hx. exact Hin.
Qed.

Lemma zero_cell_holds_r : forall L (m : word -> option byte) c a n,
  (forall x, a <= x < a + n -> m (wa x) = Some (Z_to_bv 8 0)) -> 0 <= a -> a + n <= 2^64 ->
  a <= loc_addr L (mc_loc c) -> loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= a + n -> (mc_w c <= 8)%nat ->
  (forall z, mc_val c <> VLo5 z) -> sval_num L (mc_val c) = 0 -> cell_holds L (bview SEGS m) c.
Proof.
  intros L m c a n HZ Ha1 Ha2 H1 H2 Hw Hv Hz. apply holds_of_mem; [exact Hv | exact Hw | lia | lia|].
  intros k Hk. rewrite HZ by lia. rewrite Hz. change (wa 0) with (Z_to_bv 64 0).
  f_equal. unfold word_to_le_bytes. rewrite u_wa_small by lia. symmetry. apply nth_le_0.
Qed.

Lemma wbytes_zero_in : forall (m : word -> option byte) a n x, 0 <= a -> a + Z.of_nat n <= 2^64 -> a <= x < a + Z.of_nat n ->
  wbytes m (wa a) (word_to_le_bytes n (wa 0)) (wa x) = Some (Z_to_bv 8 0).
Proof.
  intros m a n x H0 H1 Hx. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
  rewrite wbytes_at_wa; [| exact H0 | rewrite length_N_to_le_bytes; exact H1 | rewrite length_N_to_le_bytes; lia].
  f_equal. unfold word_to_le_bytes. rewrite u_wa_small by lia. apply nth_le_0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.

Lemma grows_wb : forall m m' a bs, mem_grows m m' -> mem_grows m (wbytes m' a bs).
Proof. intros m m' a bs H. exact (mem_grows_trans _ _ _ H (wbytes_grows _ _ _)). Qed.

Lemma amo_grows : forall m pa ac tl sec, mem_grows m (amo_mem m pa ac tl sec).
Proof. intros. unfold amo_mem, am_ep_mem. repeat apply grows_wb. apply mem_grows_refl. Qed.

Lemma amo0_grows : forall m pa ac sec, mem_grows m (amo0_mem m pa ac sec).
Proof. intros. unfold amo0_mem, am_ep_mem. repeat apply grows_wb. apply mem_grows_refl. Qed.

Section AMO.
Variable m : word -> option byte.
Variables pa ac tl sec : Z.
Hypothesis Hpa1 : 4096 <= pa.
Hypothesis Hpa2 : pa + 4096 <= 2^47.
Hypothesis Hpa3 : pa + 4096 <= 0x10000 \/ 0x99000 <= pa.

#[using="Hpa1 Hpa2 Hpa3"] Lemma amo_zero : 4096 <= tl -> tl + 4096 <= 2^47 -> (tl + 4096 <= pa \/ pa + 4096 <= tl) -> ZP m pa ->
  forall x, (pa + 8 <= x < pa + 16 \/ pa + 24 <= x < pa + 4096) -> amo_mem m pa ac tl sec (wa x) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins (fun (Hpa1 Hpa2 Hpa3 : LiaFast.U) => LiaFast.u0).
  intros Ht1 Ht2 Ht3 HZ x Hx. unfold amo_mem, am_ep_mem.
  destruct (range_dec x (pa + 24 + 0) 8) as [A|A]; [apply wbytes_zero_in; cbn [Z.of_nat Pos.of_succ_nat]; lia|].
  rewrite MngWb.wbytes_out by side.
  destruct (range_dec x (pa + 24 + 8) 8) as [B|B]; [apply wbytes_zero_in; cbn [Z.of_nat Pos.of_succ_nat]; lia|].
  rewrite !MngWb.wbytes_out by side. apply HZ. unfold PGSZ. lia.
Qed.

#[using="Hpa1 Hpa2 Hpa3"] Lemma amo0_zero : ZP m pa ->
  forall x, (pa + 8 <= x < pa + 16 \/ pa + 24 <= x < pa + 4096) -> amo0_mem m pa ac sec (wa x) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins (fun (Hpa1 Hpa2 Hpa3 : LiaFast.U) => LiaFast.u0).
  intros HZ x Hx. unfold amo0_mem, am_ep_mem.
  destruct (range_dec x (pa + 24 + 0) 8) as [A|A]; [apply wbytes_zero_in; cbn [Z.of_nat Pos.of_succ_nat]; lia|].
  rewrite MngWb.wbytes_out by side.
  destruct (range_dec x (pa + 24 + 8) 8) as [B|B]; [apply wbytes_zero_in; cbn [Z.of_nat Pos.of_succ_nat]; lia|].
  rewrite !MngWb.wbytes_out by side. apply HZ. unfold PGSZ. lia.
Qed.

#[using="Hpa1 Hpa2 Hpa3"] Lemma amo_wo : 4096 <= tl -> tl + 4096 <= 2^47 -> (tl + 4096 <= pa \/ pa + 4096 <= tl) -> ZP m pa ->
  forall x, 0 <= x < 2^64 -> amo_mem m pa ac tl sec (wa x) <> m (wa x) ->
  (621744 <= x < 621768) \/ (621784 <= x < 621800) \/ (tl + 8 <= x < tl + 16) \/ (pa <= x < pa + 8) \/ (pa + 16 <= x < pa + 20).
Proof. LiaFast.lf_pins (fun (Hpa1 Hpa2 Hpa3 : LiaFast.U) => LiaFast.u0).
  intros Ht1 Ht2 Ht3 HZ x Hx Hne.
  destruct (range_dec x 621744 24) as [A|A]; [left; lia|].
  destruct (range_dec x 621784 16) as [B|B]; [right; left; lia|].
  destruct (range_dec x (tl + 8) 8) as [C|C]; [right; right; left; lia|].
  destruct (range_dec x pa 8) as [D|D]; [right; right; right; left; lia|].
  destruct (range_dec x (pa + 16) 4) as [E|E]; [right; right; right; right; lia|].
  exfalso. apply Hne.
  destruct (range_dec x (pa + 24) 16) as [F|F].
  - rewrite (amo_zero Ht1 Ht2 Ht3 HZ x ltac:(lia)). symmetry. apply HZ. unfold PGSZ. lia.
  - unfold amo_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
Qed.

#[using="Hpa1 Hpa2 Hpa3"] Lemma amo0_wo : ZP m pa ->
  forall x, 0 <= x < 2^64 -> amo0_mem m pa ac sec (wa x) <> m (wa x) ->
  (621744 <= x < 621768) \/ (621776 <= x < 621800) \/ (pa <= x < pa + 8) \/ (pa + 16 <= x < pa + 20).
Proof. LiaFast.lf_pins (fun (Hpa1 Hpa2 Hpa3 : LiaFast.U) => LiaFast.u0).
  intros HZ x Hx Hne.
  destruct (range_dec x 621744 24) as [A|A]; [left; lia|].
  destruct (range_dec x 621776 24) as [B|B]; [right; left; lia|].
  destruct (range_dec x pa 8) as [D|D]; [right; right; left; lia|].
  destruct (range_dec x (pa + 16) 4) as [E|E]; [right; right; right; lia|].
  exfalso. apply Hne.
  destruct (range_dec x (pa + 24) 16) as [F|F].
  - rewrite (amo0_zero HZ x ltac:(lia)). symmetry. apply HZ. unfold PGSZ. lia.
  - unfold amo0_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
Qed.

Variable L : layout.
Variable p : sptr.
Hypothesis Hctx : ly_ctx L = 0x97c98.
Hypothesis Epa : loc_addr L (LMem p) = pa.
Hypothesis Hsec : sec mod 2^64 = ly_sec L mod 2^64.

Ltac ha a v := eapply (holds_after_w _ _ _ _ _ _ a v);
  [ first [ (cbn [loc_addr]; rewrite Hctx; reflexivity) | (rewrite ?loc_padd, Epa; reflexivity) | (rewrite ?loc_padd, Epa; ring) ]
  | cbn; lia | (intros z E; discriminate) | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | | ].

#[using="Hpa1 Hpa2 Hpa3 Hctx Epa Hsec"] Lemma amo_cells : forall la h, loc_addr L (LMem la) = tl ->
  4096 <= tl -> tl + 4096 <= 2^47 -> (tl + 4096 <= 0x10000 \/ 0x99000 <= tl) -> (tl + 4096 <= pa \/ pa + 4096 <= tl) ->
  cell_holds L (bview SEGS m) (head_cell h) ->
  Forall (cell_holds L (bview SEGS (amo_mem m pa ac tl sec)))
    [am_cell (padd (padd p AREA_HDR) META_SIZE); amc_cell (METAS_PER_AREA - 1); ac_cell (ac - 1); head_cell h; tail_cell (Some p);
     ama_cell (padd p 4096); MCell (LMem p) 8 VSec; MCell (LMem (padd p 16)) 4 (VZ METAS_PER_AREA); anext_cell la (Some p)].
Proof. LiaFast.lf_pins (fun (Hpa1 Hpa2 Hpa3 Hctx Epa Hsec : LiaFast.U) => LiaFast.u0).
  intros la h Etl Ht1 Ht2 Ht3 Ht4 Hhd.
  repeat apply Forall_cons; [ | | | | | | | | | apply Forall_nil].
  - unfold am_cell. ha 621744 (pa + 64).
    + cbn [sval_num]. rewrite !loc_padd, Epa. unfold AREA_HDR, META_SIZE. first [reflexivity | (f_equal; ring)].
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - unfold amc_cell. ha 621752 100.
    + reflexivity.
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - unfold ac_cell. ha 621760 (ac + -1).
    + cbn [sval_num]. first [reflexivity | (f_equal; ring)].
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - apply (cell_holds_frame L (bview SEGS m) (bview SEGS (amo_mem m pa ac tl sec))); [cbn; lia | exact Hhd|].
    intros a Ha. unfold in_rng, cell_range, head_cell in Ha. cbn [fst snd mc_loc mc_w loc_addr Z.of_nat Pos.of_succ_nat] in Ha. rewrite Hctx in Ha.
    unfold CTX_meta_area_head in Ha.
    destruct (Z_lt_le_dec a 0) as [A0|A0]; [unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia); reflexivity|].
    apply MngWb.bview_ext. unfold amo_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - unfold tail_cell. ha 621784 pa.
    + cbn [sval_num optr]. rewrite Epa. reflexivity.
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - unfold ama_cell. ha 621792 (pa + 4096).
    + cbn [sval_num]. rewrite loc_padd, Epa. reflexivity.
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - ha (pa + 0) sec.
    + cbn [sval_num]. exact Hsec.
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - ha (pa + 16) 101.
    + reflexivity.
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - unfold anext_cell. eapply (holds_after_w _ _ _ _ _ _ (tl + 8) pa);
      [ rewrite loc_padd, Etl; reflexivity | cbn; lia | (intros z E; discriminate) | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | | ].
    + cbn [sval_num optr]. rewrite Epa. reflexivity.
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
Qed.

#[using="Hpa1 Hpa2 Hpa3 Hctx Epa Hsec"] Lemma amo0_cells :
  Forall (cell_holds L (bview SEGS (amo0_mem m pa ac sec)))
    [am_cell (padd (padd p AREA_HDR) META_SIZE); amc_cell (METAS_PER_AREA - 1); ac_cell (ac - 1); head_cell (Some p); tail_cell (Some p);
     ama_cell (padd p 4096); MCell (LMem p) 8 VSec; MCell (LMem (padd p 16)) 4 (VZ METAS_PER_AREA)].
Proof. LiaFast.lf_pins (fun (Hpa1 Hpa2 Hpa3 Hctx Epa Hsec : LiaFast.U) => LiaFast.u0).
  repeat apply Forall_cons; [ | | | | | | | | apply Forall_nil].
  - unfold am_cell. ha 621744 (pa + 64).
    + cbn [sval_num]. rewrite !loc_padd, Epa. unfold AREA_HDR, META_SIZE. first [reflexivity | (f_equal; ring)].
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo0_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - unfold amc_cell. ha 621752 100.
    + reflexivity.
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo0_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - unfold ac_cell. ha 621760 (ac + -1).
    + cbn [sval_num]. first [reflexivity | (f_equal; ring)].
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo0_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - unfold head_cell. ha 621776 pa.
    + cbn [sval_num optr]. rewrite Epa. reflexivity.
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo0_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - unfold tail_cell. ha 621784 pa.
    + cbn [sval_num optr]. rewrite Epa. reflexivity.
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo0_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - unfold ama_cell. ha 621792 (pa + 4096).
    + cbn [sval_num]. rewrite loc_padd, Epa. reflexivity.
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo0_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - ha (pa + 0) sec.
    + cbn [sval_num]. exact Hsec.
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo0_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
  - ha (pa + 16) 101.
    + reflexivity.
    + intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold amo0_mem, am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity.
Qed.
End AMO.
