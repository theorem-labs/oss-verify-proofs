(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfKf.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfFree OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngExc MngNtfPre MngNtfC MngWb MngGM AXG_ntfm AXG_ntfg MngWk.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM MngNtfS AXF_eez AXG_nQ AXG_ntfP AXG_ntf MngMk_c1 MngGeo MngRel MngNCh MngFree MngFreeMem.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngFreeProA.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_p4z AXF_tfz AXF_t0a AXG_ffstep AXG_ffpost.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngFreeProA.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngPost MngOwn MngUnm AXG_fgrp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_nQ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ntfP OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ntf OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMk_c1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngGeo OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngRel OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNCh OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFree OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeMem OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeProA.MngFreePro OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_tfz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_t0a OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ffstep OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ffpost OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeProA.MngFreeGeo OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngPost OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngOwn OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngUnm OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_fgrp.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngRz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_dq2z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_dq2z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_ff3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Mem.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bview_frame_pt : forall m m' x, 0 <= x < 2^64 -> m' (wa x) = m (wa x) -> bview SEGS m' x = bview SEGS m x.
Proof. intros m m' x _ E. apply MngWb.bview_ext. exact E. Qed.

Theorem unm_heap0 : forall L s r (m2 m5 : word -> option byte),
  WF (s_unm s r) -> repr L s (bview SEGS m2) -> markers_hold L s (bview SEGS m2) ->
  (forall rg, In rg (footprint (s_unm s r)) -> forall x, loc_addr L (fst rg) <= x < loc_addr L (fst rg) + snd rg -> m5 (wa x) = m2 (wa x)) ->
  Heap0 L (s_unm s r) m5.
Proof.
  intros L s r m2 m5 HW' (HL & HC & HFM) HM HK.
  pose proof (layout_unm L s r HL) as HL'. pose proof HL' as (_ & _ & _ & HPOS).
  assert (BV : forall rg x, In rg (footprint (s_unm s r)) -> loc_addr L (fst rg) <= x < loc_addr L (fst rg) + snd rg -> bview SEGS m5 x = bview SEGS m2 x).
  { intros rg x Hrg Hx. pose proof (HPOS rg Hrg) as P. unfold crange in P. cbn [fst snd] in P.
    apply bview_frame_pt; [lia | exact (HK rg Hrg x Hx)]. }
  split; [exact HW'|]. split; [split; [exact HL'|]; split|].
  - rewrite image_unm. apply Forall_forall. intros c Hc.
    destruct (image_in_footprint (s_unm s r) L c HW' HL' ltac:(rewrite image_unm; exact Hc)) as (rg & Hrg & Hin).
    apply (cell_holds_frame L (bview SEGS m2) (bview SEGS m5) c (image_cell_width s c Hc) (proj1 (Forall_forall _ _) HC c Hc)).
    intros a Ha. apply (BV rg a Hrg). unfold range_incl, in_rng, crange, cell_range in *. cbn [fst snd] in *. lia.
  - apply Forall_forall. intros rg Hrg x Hx. rewrite (BV rg x Hrg Hx).
    exact (proj1 (Forall_forall _ _) HFM rg (footprint_unm_In s r rg Hrg) x Hx).
  - unfold markers_hold. rewrite markers_unm. apply Forall_forall. intros c Hc.
    destruct (markers_home (s_unm s r) L c HW' ltac:(rewrite markers_unm; exact Hc)) as (rg & Hrg & Hin).
    apply (cell_holds_frame L (bview SEGS m2) (bview SEGS m5) c (markers_width' s c Hc) (proj1 (Forall_forall _ _) HM c Hc)).
    intros a Ha. apply (BV rg a Hrg). unfold range_incl, in_rng, crange, cell_range in *. cbn [fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mem_after_munmap_out : forall m a n x, 0 <= a -> 0 <= n -> a + n < 2^64 -> 0 <= x < 2^64 -> ~ (a <= x < a + n) ->
  MngWk.mem_after m (MngRz.eff_munmap a n) (wa x) = m (wa x).
Proof.
  intros m a n x Ha Hn Han Hx Hout. unfold MngWk.mem_after, MngRz.eff_munmap. cbn [eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies apply_zeros].
  unfold apply_unmaps, zeros_cover. cbn [existsb fst snd]. unfold MngWk.w64. rewrite !u_wa_small by lia.
  replace ((a <=? x) && (x <? a + n) || false) with false by (destruct (Z.leb_spec a x); destruct (Z.ltb_spec x (a + n)); cbn; first [reflexivity | lia]).
  reflexivity.
Qed.

Lemma store_ok_pt : forall n m m' (a : word), bv_unsigned a + Z.of_nat n <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> m x <> None -> m' x <> None) ->
  store_ok SEGS m a n = true -> store_ok SEGS m' a n = true.
Proof.
  intros n; induction n as [|n IH]; intros m m' a Hr Hg H; [reflexivity|].
  cbn [store_ok] in *.
  assert (Hv' : wview SEGS m' a <> None).
  { destruct (wview SEGS m a) as [b|] eqn:Hv; [|discriminate]. unfold wview in *.
    destruct (m' a) as [b'|] eqn:E'; [discriminate|]. destruct (m a) as [b0|] eqn:E0.
    - exfalso. apply (Hg a); [lia | rewrite E0; discriminate | exact E'].
    - rewrite Hv. discriminate. }
  destruct (wview SEGS m a) as [b|] eqn:Hv; [|discriminate]. destruct (wview SEGS m' a) as [b'|]; [|exfalso; exact (Hv' eq_refl)].
  destruct n as [|n']; [reflexivity|].
  pose proof (bv_unsigned_in_range _ a) as Ra. unfold bv_modulus in Ra.
  assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
  apply (IH m m' (a + 1)%bv); [rewrite Hu1; lia | | exact H].
  intros x Hx. rewrite Hu1 in Hx. apply Hg. lia.
Qed.

Lemma stk_ok_pt : forall m m' sp K, stk_ok SEGS m sp K -> bv_unsigned sp <= 2^64 ->
  (forall x : word, bv_unsigned sp - K <= bv_unsigned x < bv_unsigned sp -> m x <> None -> m' x <> None) -> stk_ok SEGS m' sp K.
Proof.
  intros m m' sp K H Hsp Hg a n H1 H2. apply (store_ok_pt n m m' a); [lia | | exact (H a n H1 H2)].
  intros x Hx. apply Hg. lia.
Qed.

Lemma bv_add_53038 : bv_add (wa 0x55310) (MngWk.w64 4) = wa 0x55314.
Proof. apply bv_eq. reflexivity. Qed.

Lemma ecall_53038 : exists w, fetch_word SEGS (wa 0x55310) = Some w /\ is_ecall w = true.
Proof. eexists. split; [vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section GRPU.
Context {fx : FPState}.

#[using="Type"] Theorem free_grpU_step : forall L s (regs : bvmap 5 word) m rom g am i fr s2 r len k,
  Heap0 L s m ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser ->
  (am_freed am = 0 \/ Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am)) ->
  ly_ctx L = 0x97c98 ->
  getr regs 10 = wa (loc_addr L (LMem (frame_ptr am i fr))) -> getr regs 4 = wa 489872 ->
  rdn SEGS m (wa 621603) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) ->
  rdn SEGS m (wa 416600) 8 = Some (word_to_le_bytes 8 (wa 0x97c00)) ->
  (exists can, 0 <= can <= 2^64 - 1 /\ rdn SEGS m (wa 621568) 8 = Some (word_to_le_bytes 8 (wa can))) ->
  rdn SEGS m (wa 621712) 4 = Some (word_to_le_bytes 4 (wa 0)) ->
  (forall j, 0 <= j < 4 -> exists b, Mem.mrd SEGS m (wa (0x778ec + j)) = Some b) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (0x778ec + d)) k = true) ->
  2^20 + 8192 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 8192 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 8192) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x89000)) ->
  (forall q rg, region_of s q = Some rg -> rg_kind rg = RkMap -> rg_live rg = true -> 0 < rg_len rg) ->
  free (Some (frame_ptr am i fr)) s = IAsk (KMunmap r len) s2 k ->
  exists R m3, msteps SEGS (mkst regs (wa 0x52f88) m rom) (mkst R (wa 0x55310) m3 rom) /\
    MngWk.at_ecall SEGS L s2 (KMunmap r len) R (wa 0x55310) /\
    (exists rg, region_of s r = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\ rg_len rg = page_round len) /\
    MallocWfKf.kf_of s2 = MallocWfKf.kf_of s /\ req_ok s2 (KMunmap r len) /\ (forall z, k z = IRet (tt, s_unm s2 r)) /\
    exists R5 m5,
      msteps SEGS (mkst (regupd R 10 (MngWk.w64 0)) (bv_add (wa 0x55310) (MngWk.w64 4))
                        (MngWk.mem_after m3 (MngRz.eff_munmap (ly_reg L r) (page_round len))) rom)
                  (mkst R5 (wa 0x53574) m5 rom) /\
      AXF_ff3.callee_same R5 regs /\ Heap0 L (s_unm s2 r) m5 /\
      (forall x, 0 <= x < 2^64 -> ~ (bv_unsigned (getr regs 2) - 8192 <= x < bv_unsigned (getr regs 2)) ->
         (forall c, In c (image s) -> ~ in_rng (cell_range L c) x) ->
         ~ (ly_reg L r <= x < ly_reg L r + page_round len) -> ~ (0x778ec <= x < 0x778f0) -> m5 (wa x) = m (wa x)) /\
      (forall x, 0 <= x < 2^64 -> ~ (ly_reg L r <= x < ly_reg L r + page_round len) -> m (wa x) <> None -> m5 (wa x) <> None).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s regs m rom g am i fr s2 r len k H0 HF Hk Hnt Hctx HP HR4 Hnl Htab Hgot Hcan Hlk Her Hew Rsp Asp HSTK8 HFP8 HAP HRP Hfree.
  pose proof H0 as (HW & HR & HM). pose proof HR as (HL & _ & _).
  destruct (free_ntf_run L s regs m rom g am i fr H0 HF Hk Hctx HP Hnl Htab Hgot Hcan Rsp Asp HSTK8 HFP8 HAP Hnt)
    as (R3 & m2 & mi & s2' & Hms & E1 & E2 & E10 & E11 & Ek & S1 & S2 & S3 & S4 & S5 & Rb & Rl & Ht & N3 & MK & RG & AR & G1 & G2 & CH1 & FR & NR).
  set (sp := bv_unsigned (getr regs 2)) in *.
  destruct mi as [[r' len']|].
  2:{ rewrite (free_ntf_none s g am i fr s2' HW HF Hnt Ht) in Hfree. discriminate Hfree. }
  pose proof (free_ntf_some s g am i fr s2' r' len' HW HF Hnt Ht) as HFS.
  rewrite HFS in Hfree. injection Hfree as Er Elen Es2 Ek'. subst r' len' s2'.
  destruct (in_frames_inv s g am i fr HF) as (Hu' & Hi' & Hfri').
  assert (Hb : In (frame_ptr am i fr, fr_n fr) (user_blocks s)).
  { unfold user_blocks. apply in_flat_map. exists (g, am). split; [exact Hu'|]. cbn [snd]. apply in_flat_map.
    exists i. split; [apply In_zseq; lia|]. rewrite Hfri', Hk. left. reflexivity. }
  (* [comment removed for export] *)
  pose proof (free_kf s (Some (frame_ptr am i fr))) as RK. rewrite HFS in RK. cbn [rk] in RK. destruct RK as (HKF & _).
  pose proof (free_reqs_ok s (frame_ptr am i fr) (fr_n fr) HW Hb) as RQ. rewrite HFS in RQ. cbn [reqs_ok] in RQ. destruct RQ as (Hrq & _).
  pose proof Hrq as (rg & Hrg2 & Hkd & Hlv & Hlen & Hl0 & _).
  assert (Ereg : st_regions s2 = st_regions s) by (unfold MallocWfKf.kf_of in HKF; injection HKF as E' _ _; exact E').
  assert (Earea : st_areas s2 = st_areas s) by (unfold MallocWfKf.kf_of in HKF; injection HKF as _ _ E'; exact E').
  assert (Hrg : region_of s r = Some rg) by (unfold region_of in *; rewrite <- Ereg; exact Hrg2).
  pose proof (HRP r rg Hrg Hkd Hlv) as Hpos.
  assert (Hlen1 : 1 <= len).
  { destruct (Z_lt_le_dec len 1) as [Hl|Hl]; [|exact Hl]. exfalso. assert (len = 0) by lia. subst len. rewrite Hlen in Hpos. replace (page_round 0) with 0 in Hpos by reflexivity. lia. }
  pose proof (footprint_region_In s r rg Hrg Hkd Hlv) as HE.
  pose proof (HFP8 _ HE) as HEtop. cbn [fst snd loc_addr] in HEtop.
  pose proof HL as (_ & _ & _ & HPOS). pose proof (HPOS _ HE) as HEpos. unfold crange in HEpos. cbn [fst snd loc_addr] in HEpos.
  pose proof (HAP _ HE ltac:(discriminate)) as HEimg. unfold ranges_disjoint, crange in HEimg. cbn [fst snd loc_addr] in HEimg.
  set (a := ly_reg L r) in *. set (n := rg_len rg) in *.
  assert (Ean : a + 0 = a) by ring. rewrite Ean in HEtop, HEpos, HEimg.
  assert (EFP : footprint s2 = footprint s) by (apply footprint_of_kf; assumption).
  (* [comment removed for export] *)
  assert (ESP : getr regs 2 = wa sp) by (unfold sp; rewrite wa_u; reflexivity).
  pose proof (NC_of_heap L s m sp 8192 HW HR Hctx
               ltac:(destruct Hcan as (can & Rcan & Mcan); split; [exact Hgot|]; split; [exact Htab|]; exists can; split; [exact Rcan | exact Mcan])
               ltac:(rewrite <- ESP; exact HSTK8) ltac:(lia) ltac:(clear - Rsp; unfold sp; lia) ltac:(clear - Rsp; unfold sp; lia) Asp HFP8 HAP) as N0.
  pose proof (ntf_path_frame L s g am i fr m _ m2 sp HW HL HF CH1 FR) as KP.
  assert (ST : forall x, 0x10000 <= x < 0x99000 -> ~ (0x97c98 <= x < 0x98038) -> m2 (wa x) = m (wa x)).
  { intros x Hx Hn. apply KP; [clear - Hx; lia | clear - Hx Rsp; unfold sp in *; lia |]. exact (static_not_cell L s m sp x N0 Hx Hn). }
  destruct (rdn_read4 m 0x778ec ltac:(lia) ltac:(lia) Her) as (ERR & RERR & HERR).
  (* [comment removed for export] *)
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1z.t1_pt1b R3 m2 rom sp (mi_base L (Some (r, len))) (mi_len (Some (r, len))) ERR (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8))
              (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)))
    as (R & Hms4 & T1 & T2 & T4 & T8 & T9 & T10 & T11 & T17 & T18 & T19 & Tk).
  { constructor.
    - exact E1.
    - rewrite E2. first [reflexivity | f_equal; ring].
    - fixgoal 4%nat. rewrite (Ek 4%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). fixreg HR4 4%nat. exact HR4.
    - exact E10.
    - exact E11.
    - exact (stk_ok_mono' m2 (wa sp) 8192 1024 (nc_stk _ _ _ _ _ _ _ N3) ltac:(lia)).
    - clear - Rsp; unfold sp in *; lia.
    - exact Rb.
    - exact Rl.
    - exact RERR.
    - pose proof (bv_unsigned_in_range _ (getr regs 1)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 8)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 9)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 18)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 19)) as B. unfold bv_modulus in B. lia.
    - exact Asp.
    - rewrite (rdn_frame_n m m2 (0 + 621712) 4) by (first [lia | intros x Hx; cbn in Hx; apply ST; lia]). exact Hlk.
    - rewrite (rdn_frame_n m m2 (0 + 489708) 4) by (first [lia | intros x Hx; cbn in Hx; apply ST; lia]). exact HERR.
    - exact S1. - exact S2. - exact S3. - exact S4. - exact S5.
    - clear - Rsp; unfold sp in *; lia.
    - clear - Rsp; unfold sp in *; lia. }
  { apply t1_scs_b.
    - clear - Rsp; unfold sp in *; lia.
    - exact Rb.
    - exact RERR.
    - pose proof (bv_unsigned_in_range _ (getr regs 1)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 8)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 9)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 18)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 19)) as B. unfold bv_modulus in B. lia.
    - cbn [mi_len] in Rl |- *. lia. }
  cbn [mi_base mi_len] in T9, T10, T8, T11. fold a in T9, T10.
  set (m3 := OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1z.t1_mem_pt1b m2 R3 sp a len ERR (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
               (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19))) in *.
  exists R, m3. split; [eapply msteps_trans; [exact Hms | exact Hms4]|].
  split.
  { split; [exact ecall_53038|]. exists 215, [ly_reg L r; len]. split; [reflexivity|]. split.
    - rewrite T17. rewrite u_wa_small by lia. reflexivity.
    - cbn [args_match]. split; [|split; [|exact I]].
      + match type of T10 with getr _ ?r0 = _ => replace (Z_to_bv 5 (10 + 0)) with r0 by (apply bv_eq; reflexivity) end.
        rewrite T10, u_wa. reflexivity.
      + match type of T11 with getr _ ?r0 = _ => replace (Z_to_bv 5 (10 + (0 + 1))) with r0 by (apply bv_eq; reflexivity) end.
        rewrite T11, u_wa. reflexivity. }
  split; [exists rg; split; [exact Hrg|]; split; [exact Hkd|]; split; [exact Hlv | exact Hlen]|].
  split; [exact HKF|]. split; [exact Hrq|]. split; [intros z; first [rewrite <- Ek'; reflexivity | rewrite Ek'; reflexivity]|].
  (* [comment removed for export] *)
  rewrite <- Hlen. fold n.
  set (m4 := MngWk.mem_after m3 (MngRz.eff_munmap a n)).
  assert (M4 : forall x, 0 <= x < 2^64 -> ~ (a <= x < a + n) -> m4 (wa x) = m3 (wa x)).
  { intros x Hx Hn. unfold m4. apply mem_after_munmap_out; [lia | lia | lia | exact Hx | exact Hn]. }
  assert (M3 : forall x, 0 <= x < 2^64 -> ~ (sp - 72 <= x < sp - 48) -> m3 (wa x) = m2 (wa x)).
  { intros x Hx Hn. unfold m3, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1z.t1_mem_pt1b.
    rewrite !MngWb.wbytes_out by (cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_wa_small by (clear - Rsp; unfold sp in *; lia); first [ (clear - Rsp; unfold sp in *; lia) | exact Hx | (clear - Hn Hx Rsp; unfold sp in *; lia) ]).
    reflexivity. }
  assert (G3 : mem_grows m2 m3) by (unfold m3, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1z.t1_mem_pt1b; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  assert (G12 : mem_grows m m2) by exact (mem_grows_trans _ _ _ G1 G2).
  assert (STK3 : stk_ok SEGS m3 (wa sp) 8192) by exact (stk_ok_grows SEGS m2 m3 (wa sp) 8192 (nc_stk _ _ _ _ _ _ _ N3) G3).
  assert (STK4 : stk_ok SEGS m4 (wa sp) 8192).
  { apply (stk_ok_pt m3 m4 (wa sp) 8192 STK3); [rewrite u_wa_small by (clear - Rsp; unfold sp in *; lia); clear - Rsp; unfold sp in *; lia|].
    intros x Hx Hne. rewrite u_wa_small in Hx by (clear - Rsp; unfold sp in *; lia). rewrite <- (wa_u x).
    pose proof (bv_unsigned_in_range _ x) as Bx. unfold bv_modulus in Bx.
    rewrite M4 by (first [lia | clear - Hx HEtop; lia]). rewrite wa_u. exact Hne. }
  set (ERR' := ext_Z true 0 4 ERR mod 2^64).
  assert (EERR : wa ERR' = wa (ext_Z true 0 4 ERR)) by (unfold ERR'; apply wa_eqm; apply Z.mod_mod; lia).
  assert (RD : forall b v, sp - 72 <= b -> b + 8 <= sp -> rdn SEGS m3 (wa b) 8 = Some (word_to_le_bytes 8 (wa v)) -> rdn SEGS m4 (wa b) 8 = Some (word_to_le_bytes 8 (wa v))).
  { intros b v B1 B2 Hv. rewrite (rdn_frame_n m3 m4 b 8) by (first [ (clear - B1 B2 Rsp; unfold sp in *; cbn; lia) | (intros x Hx; cbn in Hx; apply M4; clear - Hx B1 B2 Rsp HEtop; unfold sp in *; lia) ]).
    exact Hv. }
  assert (RD2 : forall b v, sp - 48 <= b -> b + 8 <= sp -> rdn SEGS m2 (wa b) 8 = Some (word_to_le_bytes 8 (wa v)) -> rdn SEGS m4 (wa b) 8 = Some (word_to_le_bytes 8 (wa v))).
  { intros b v B1 B2 Hv. apply RD; [lia | lia|]. rewrite (rdn_frame_n m2 m3 b 8) by (first [ (clear - B1 B2 Rsp; unfold sp in *; cbn; lia) | (intros x Hx; cbn in Hx; apply M3; clear - Hx B1 B2 Rsp; unfold sp in *; lia) ]).
    exact Hv. }
  assert (Wsp : forall d, 0 <= d <= 80 -> bv_unsigned (wa (sp + - d)) = sp - d) by (intros d Hd; rewrite u_wa_small by (clear - Rsp Hd; unfold sp in *; lia); ring).
  (* [comment removed for export] *)
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_t2z.t2_pt2 (regupd R 10 (MngWk.w64 0)) m4 rom sp a len ERR' (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
              (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)))
    as (R5 & Hms5 & U1 & U2 & U4 & U8 & U9 & U10 & U11 & U17 & U18 & U19 & Uk).
  { constructor.
    - rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). exact T1.
    - rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). exact T2.
    - rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). exact T4.
    - rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). exact T8.
    - rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). exact T9.
    - rewrite getr_same by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). reflexivity.
    - rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). exact T17.
    - rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). exact T18.
    - rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). rewrite EERR. exact T19.
    - exact (stk_ok_mono' m4 (wa sp) 8192 1024 STK4 ltac:(lia)).
    - clear - Rsp; unfold sp in *; lia.
    - cbn [mi_base] in Rb. exact Rb.
    - cbn [mi_len] in Rl. exact Rl.
    - unfold ERR'. pose proof (Z.mod_pos_bound (ext_Z true 0 4 ERR) (2^64) ltac:(lia)). lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 1)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 8)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 9)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 18)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 19)) as B. unfold bv_modulus in B. lia.
    - exact Asp.
    - apply RD; [lia | lia|]. unfold m3, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1z.t1_mem_pt1b.
      rewrite (rdn_wbytes_out SEGS _ _ (wa (sp + -72))) by (cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_wa_small by (clear - Rsp; unfold sp in *; lia); clear - Rsp; unfold sp in *; lia).
      rewrite (rdn_wbytes_out SEGS _ _ (wa (sp + -64))) by (cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_wa_small by (clear - Rsp; unfold sp in *; lia); clear - Rsp; unfold sp in *; lia).
      apply rdn_wbytes_hit8. rewrite u_wa_small by (clear - Rsp; unfold sp in *; lia). clear - Rsp; unfold sp in *; lia.
    - apply RD; [lia | lia|]. unfold m3, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1z.t1_mem_pt1b.
      rewrite (rdn_wbytes_out SEGS _ _ (wa (sp + -72))) by (cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_wa_small by (clear - Rsp; unfold sp in *; lia); clear - Rsp; unfold sp in *; lia).
      apply rdn_wbytes_hit8. rewrite u_wa_small by (clear - Rsp; unfold sp in *; lia). clear - Rsp; unfold sp in *; lia.
    - apply RD; [lia | lia|]. unfold m3, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1z.t1_mem_pt1b.
      apply rdn_wbytes_hit8. rewrite u_wa_small by (clear - Rsp; unfold sp in *; lia). clear - Rsp; unfold sp in *; lia.
    - apply RD2; [lia | lia | exact S1].
    - apply RD2; [lia | lia | exact S2].
    - apply RD2; [lia | lia | exact S3].
    - apply RD2; [lia | lia | exact S4].
    - apply RD2; [lia | lia | exact S5].
    - intros d k0 Hd Hk0. replace (0 + 489708 + d) with (0x778ec + d) by ring.
      apply (store_ok_pt k0 m3 m4); [rewrite u_wa_small by lia; lia | |].
      + intros x Hx Hne. rewrite u_wa_small in Hx by lia. rewrite <- (wa_u x). rewrite M4; [rewrite wa_u; exact Hne | pose proof (bv_unsigned_in_range _ x) as Bx; unfold bv_modulus in Bx; lia |].
        intros Hin. lia.
      + apply (store_ok_mono SEGS k0 m m3); [exact (mem_grows_trans _ _ _ G12 G3) | exact (Hew d k0 Hd Hk0)].
    - clear - Rsp; unfold sp in *; lia. }
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_t2.RES_pt2 fst snd]. apply Forall_nil. }
  set (m5 := OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_t2z.t2_mem_pt2 m4 (regupd R 10 (MngWk.w64 0)) sp a len ERR' (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
               (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19))) in *.
  assert (M5 : forall x, 0 <= x < 2^64 -> ~ (0x778ec <= x < 0x778f0) -> m5 (wa x) = m4 (wa x)).
  { intros x Hx Hn. unfold m5, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_t2z.t2_mem_pt2. rewrite MngWb.wbytes_out; [reflexivity | | exact Hx |];
      cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite u_wa_small by lia; lia. }
  assert (G45 : mem_grows m4 m5) by (unfold m5, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_t2z.t2_mem_pt2; apply wbytes_grows).
  exists R5, m5. split; [rewrite bv_add_53038; exact Hms5|].
  split.
  { intros nn Hn. cbn [In] in Hn.
    assert (OTH : forall kk, In kk [3; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (Z_to_bv 5 (Z.of_nat kk)) = getr regs (Z_to_bv 5 (Z.of_nat kk))).
    { intros kk Hkk. rewrite (Uk kk ltac:(clear - Hkk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])).
      rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; clear - Hkk E; cbn [In] in Hkk;
        repeat (destruct Hkk as [<-|Hkk]; [discriminate E|]); destruct Hkk).
      rewrite (Tk kk ltac:(clear - Hkk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])). exact (Ek kk ltac:(clear - Hkk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])). }
    destruct Hn as [<-|[<-|Hn]].
    { fixreg U1 1%nat. rewrite U1, wa_u. reflexivity. }
    { fixreg U2 2%nat. rewrite U2. exact (eq_sym ESP). }
    destruct Hn as [<-|[<-|Hn]].
    { exact (OTH 3%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). }
    { fixreg U4 4%nat. rewrite U4. fixreg HR4 4%nat. exact (eq_sym HR4). }
    destruct Hn as [<-|[<-|[<-|[<-|Hn]]]].
    { fixreg U8 8%nat. rewrite U8, wa_u. reflexivity. }
    { fixreg U9 9%nat. rewrite U9, wa_u. reflexivity. }
    { fixreg U18 18%nat. rewrite U18, wa_u. reflexivity. }
    { fixreg U19 19%nat. rewrite U19, wa_u. reflexivity. }
    exact (OTH nn ltac:(clear - Hn; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])). }
  assert (HW' : WF (s_unm s2 r)).
  { apply (free_wf s (frame_ptr am i fr) (fr_n fr) [(KMunmap r len, 1)] (s_unm s2 r) HW Hb). rewrite HFS. cbn [yields].
    split; [reflexivity|]. split; [exact I | reflexivity]. }
  split.
  { apply (unm_heap0 L s2 r m2 m5 HW' (repr_of_repr_x L s2 _ (nc_repr _ _ _ _ _ _ _ N3))
             (ntf_markers L s m _ m2 g am i fr s2 sp HW HR HM HF Hk Hctx ltac:(clear - Rsp; unfold sp in *; lia) HFP8 HAP CH1 FR MK)).
    intros rg' Hrg' x Hx.
    pose proof (proj1 (nc_repr _ _ _ _ _ _ _ N3)) as HL2.
    pose proof (unm_disjoint L s2 r rg rg' HL2 Hrg2 Hkd Hlv Hrg') as D. fold a n in D.
    assert (Hin : In rg' (footprint s)) by (rewrite <- EFP; exact (footprint_unm_In s2 r rg' Hrg')).
    pose proof (HFP8 rg' Hin) as Top'. pose proof (HPOS rg' Hin) as Pos'. unfold crange in Pos'. cbn [fst snd] in Pos'.
    assert (Herr : ~ (0x778ec <= x < 0x778f0)).
    { destruct (loc_eq_dec (fst rg') (LCtx 0)) as [Ec|Ec].
      - pose proof (footprint_ctx_len' s rg' Hin Ec) as Lc. rewrite Ec in Hx. cbn [loc_addr] in Hx. rewrite Hctx, Lc in Hx. unfold CTX_SIZE in Hx. lia.
      - pose proof (HAP rg' Hin Ec) as Dg. unfold ranges_disjoint, crange in Dg. cbn [fst snd] in Dg. lia. }
    rewrite M5 by (first [lia | exact Herr]). rewrite M4 by (unfold ranges_disjoint, crange in D; cbn [fst snd] in D; lia).
    apply M3; [lia | clear - Top' Hx Rsp; unfold sp in *; lia]. }
  split.
  { intros x Hx Hst Hc Hr Herr. rewrite M5 by assumption. rewrite M4 by assumption.
    rewrite M3 by (first [exact Hx | clear - Hst; lia]). exact (KP x Hx Hst Hc). }
  intros x Hx Hr Hne. apply G45. rewrite M4 by assumption. apply G3. apply G12. exact Hne.
Qed.
End GRPU.
