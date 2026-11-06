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
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfMalloc OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngCtx MngImage MngSurgery MngNtfPre MngNtfC MngWk MngLt MngGeoX MngExc.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits AxMalloc MngZ MngMalloc MngNtfM MngNtfS MngPost MngMWP MngMWQ MngMW0 MngMW1 MngMW2 MngMW3 MngTakeR AXG_mfpost AXF_maz AXF_mcz AXF_mb0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_mfmem AXG_mfpre AXG_ffstep MngL4 AXG_ag1 AXG_as1 AXG_as5 AXG_am8 AXG_asq AXG_kro AXG_mwm AXG_mwb AXG_mwt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxMalloc OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMalloc OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngPost OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMWQ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW3 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngTakeR OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mfpost OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_maz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mcz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb0z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_masz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mwjz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mwrz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mfmem OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mfpre OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ffstep OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngL4 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_as1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_as5 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am8 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_asq OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_kro OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mwm OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mwb OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mwt.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac lmemb := first [ AxSymRun3.memb_refl | repeat (first [left; reflexivity | right]) ].      (* [comment removed for export] *)

Lemma set_freed_same' : forall am, am_set_freed (am_freed am) am = am.
Proof. intros []. reflexivity. Qed.

(* [comment removed for export] *)
Theorem take_cut : forall HTOP L s m sp K g am,
  CUT HTOP [] None U0 L s m sp K -> usedX [] s g am -> 0 <= am_sc am < 48 -> active_hd s (am_sc am) = Some g -> am_avail am <> 0 ->
  CUT HTOP [] (Some (g, mf_idx am)) U0 L (set_meta s g (MUsed (mf_am1 am))) (mb0_mem m (loc_addr L (LMem g)) (am_avail am)) sp K.
Proof.
  intros HTOP L s m sp K g am C Hux Hsc Hhd Hav.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  pose proof (usedX_MT _ _ _ _ Hux) as [Mg _].
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  set (G := loc_addr L (LMem g)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). fold G in G1, G2, G3, G4.
  set (avail := am_avail am) in *.
  destruct (take_bit_Inv [] U0 s g am HI Hux Hsc Hhd Hav) as (Hk & Hfirst & Hbit & HI1).
  set (m' := mb0_mem m G avail).
  set (s' := set_meta s g (MUsed (mf_am1 am))).
  assert (Es' : upd_meta g (MUsed (am_set_avail (am_avail am - lowbit (am_avail am)) am)) s = s') by reflexivity.
  rewrite Es' in HI1.
  set (cn := MCell (LMem (padd g META_avail)) 4 (VZ (avail - lowbit avail))).
  assert (HKs' : KS s') by (apply KS_set_meta; [exact HK | exact Kg]).
  assert (Ks' : keys s' = keys s) by (apply keys_set_meta; exact Kg).
  assert (HRS : RS L s' s) by (apply (RS_set_used L s g am _ HK Mg); unfold mf_am1; rewrite gc_avail; reflexivity).
  assert (Ms'g : MT s' g = Some (MUsed (am_set_avail (avail - lowbit avail) am))) by apply MT_set_same.
  assert (Hcn : In cn (image s')).
  { apply (In_image_used s' g _ cn HKs' Ms'g). left. cbn [meta_slot_cells]. right. right. right. left. reflexivity. }
  assert (HR' : repr_x L s' (bview SEGS m') []).
  { apply (repr_x_wcell L s s' m [] cn (G + 24) HR eq_refl eq_refl HRS).
    - intros c Hc. unfold s', mf_am1, mf_first in Hc. rewrite <- (set_freed_same' am) in Hc.
      destruct (cov_avail_freed s g am (avail - lowbit avail) (am_freed am) c HK Mg Hc) as [H|[H|H]].
      + left. exact H.
      + right. exact H.
      + left. rewrite H. apply (In_image_used s g am _ HK Mg). left. cbn [meta_slot_cells]. right. right. right. right. left. reflexivity.
    - exact Hcn.
    - intros z E. discriminate.
    - cbn. lia.
    - unfold cn. cbn [mc_loc]. rewrite loc_padd. unfold META_avail. reflexivity.
    - lia.
    - unfold cn. cbn [mc_w Z.of_nat Pos.of_succ_nat]. lia. }
  assert (MOUT : forall x, 0 <= x < 2^64 -> ~ (G + 24 <= x < G + 28) -> m' (wa x) = m (wa x)).
  { intros x Hx Hn. unfold m', mb0_mem. rewrite MngWb.wbytes_out by (unfold word_to_le_bytes; rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat]; rewrite ?u_wa_small by lia; lia). reflexivity. }
  assert (Hgr : mem_grows m m') by apply mb0_mem_grows.
  assert (HFRM : FRM L s sp K m m').
  { intros x Hx Hne. right. exists (MCell (LMem (padd g META_avail)) 4 (VZ avail)). split; [|split; [unfold wide; right; cbn; lia|]].
    - apply (In_image_used s g am _ HK Mg). left. cbn [meta_slot_cells]. right. right. right. left. reflexivity.
    - unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_avail. fold G.
      destruct (Z_lt_le_dec x (G + 24)) as [A|A]; [exfalso; apply Hne; apply MOUT; [exact Hx | lia]|].
      destruct (Z_lt_le_dec x (G + 28)) as [B|B]; [lia|]. exfalso; apply Hne; apply MOUT; [exact Hx | lia]. }
  assert (N' : NC L [] [] s' m' sp K) by exact (NC_next L [] [] s s' m m' sp K N HR' HRS HKs' ltac:(intros x []) Hgr HFRM Ks').
  constructor; try assumption. all: intros x [].
Qed.

(* [comment removed for export] *)
Lemma markers_frame : forall HTOP R U L s m m', Inv [] R U s -> rgeoA HTOP L s -> rdisj L s -> markers_hold L s (bview SEGS m) ->
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> HTOP <= x \/
     exists r rg, region_of s r = Some rg /\ rg_live rg = true /\ rg_kind rg <> RkMap /\ ly_reg L r <= x < ly_reg L r + rg_len rg) ->
  markers_hold L s (bview SEGS m').
Proof.
  intros HTOP R U L s m m' HI HG HD HM HCH. apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) HM c Hc) as Hh.
  destruct (marker_in_region_R R U s L c HI Hc) as (r0 & rg0 & o & Hr0 & Hk0 & Hl0 & Ec & Ho & Hw).
  destruct (HG r0 rg0 Hr0 Hl0) as (A1 & _ & A3 & _).
  assert (W1 : (1 <= mc_w c)%nat).
  { unfold markers in Hc. apply in_flat_map in Hc as [[g2 a2] [_ Hc]]. cbn [snd] in Hc. unfold meta_markers in Hc.
    apply in_app_iff in Hc as [Hc|[<-|[]]]; [|cbn; lia].
    apply in_flat_map in Hc as [i [_ Hc]]. destruct (ss_fr (nth_slot a2 i)) as [f|]; [|destruct Hc].
    destruct (fr_kind f); [|destruct Hc]. unfold marker_cells in Hc. destruct Hc as [<-|Hc]; [cbn; lia|].
    apply in_app_iff in Hc as [Hc|Hc]; [destruct (0 <? _); [destruct Hc as [<-|[]]; cbn; lia | destruct Hc]|].
    destruct (5 <=? _); [destruct Hc as [<-|[<-|[]]]; cbn; lia | destruct Hc]. }
  apply (cell_holds_frame L (bview SEGS m) (bview SEGS m') c W1 Hh). intros x Hx.
  unfold in_rng, cell_range in Hx. rewrite Ec in Hx. cbn [fst snd loc_addr] in Hx.
  destruct (Z_lt_le_dec x 0) as [Hn0|Hn0].
  { unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; exact Hn0). reflexivity. }
  destruct (Z_lt_le_dec x (2^64)) as [Hx64|Hx64].
  2:{ unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; exact Hx64). reflexivity. }
  apply MngWb.bview_ext.
  destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|].
  exfalso. destruct (HCH x ltac:(lia) E) as [A|(r & rg & Hr & Hl & Hk & Hx')]; [unfold PGSZ in *; lia|].
    assert (Hne : r <> r0) by (intros ->; rewrite Hr0 in Hr; injection Hr as <-; exact (Hk Hk0)).
    pose proof (HD r r0 rg rg0 Hne Hr Hr0 Hl Hl0) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.

(* [comment removed for export] *)
Definition MENV (m : word -> option byte) : Prop := (exists can, MngL4.env m can) /\ page_env m /\ KRO m.

(* [comment removed for export] *)
Lemma mw_post_of_tail : forall HTOP L s m regs L0 s0 m0 (regs0 : bvmap 5 word) p s' R m' sp0,
  tail_post L s m regs (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) p s' R m' ->
  getr regs 2 = wa (sp0 - 48) -> bv_unsigned (getr regs0 2) = sp0 -> 2^20 <= sp0 <= 2^47 ->
  (forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr regs (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) ->
  lext L0 L s0 -> rgeo HTOP L s' ->
  (forall x, 0 <= x < 2^64 -> m (wa x) <> m0 (wa x) -> (sp0 - 8192 <= x < sp0) \/ (in_footprint L s x /\ ~ in_user_block L0 s0 x) \/ in_regs L s x \/
     exists c, In c (image s) /\ loc_addr L (mc_loc c) <= x < loc_addr L (mc_loc c) + Z.of_nat (mc_w c)) ->
  (forall x, in_user_block L0 s0 x -> in_user_block L s x) ->
  footprint s' = footprint s -> st_regions s' = st_regions s ->
  stk_ok SEGS m' (getr regs0 2) 8192 ->
  mw_post HTOP regs0 m0 L0 s0 L (Some p, s') R (wa 0x54a98) m'.
Proof.
  intros HTOP L s m regs L0 s0 m0 regs0 p s' R m' sp0 T R2 Usp Rsp K3 HE HGEO HCH HUB Efp Erg STK.
  destruct T as [A0 Ara As0 As1 As2 As3 As4 Asp Akp Hp Hrg Hfp Hch Hgr Hown Hub].
  exists p, s'. split; [reflexivity|]. split; [reflexivity|]. split.
  { intros k Hk. cbn [callee_regs' In] in Hk.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]].
    - exact Ara.
    - transitivity (v_addi (getr regs 2) 48); [exact Asp|]. rewrite R2. change (getr regs0 (Z_to_bv 5 (Z.of_nat 2))) with (getr regs0 2).
      apply bv_eq. rewrite u_vaddi''; rewrite ?u_wa_small by lia; lia.
    - rewrite (Akp 3%nat ltac:(lmemb)). exact (K3 3%nat ltac:(lmemb)).
    - rewrite (Akp 4%nat ltac:(lmemb)). exact (K3 4%nat ltac:(lmemb)).
    - exact As0.
    - exact As1.
    - exact As2.
    - exact As3.
    - exact As4.
    - rewrite (Akp 21%nat ltac:(lmemb)). exact (K3 21%nat ltac:(lmemb)).
    - rewrite (Akp 22%nat ltac:(lmemb)). exact (K3 22%nat ltac:(lmemb)).
    - rewrite (Akp 23%nat ltac:(lmemb)). exact (K3 23%nat ltac:(lmemb)).
    - rewrite (Akp 24%nat ltac:(lmemb)). exact (K3 24%nat ltac:(lmemb)).
    - rewrite (Akp 25%nat ltac:(lmemb)). exact (K3 25%nat ltac:(lmemb)).
    - rewrite (Akp 26%nat ltac:(lmemb)). exact (K3 26%nat ltac:(lmemb)).
    - rewrite (Akp 27%nat ltac:(lmemb)). exact (K3 27%nat ltac:(lmemb)). }
  split; [exact A0|]. split; [exact Hp|]. split; [exact HE|]. split; [exact HGEO|]. split; [|exact STK].
  intros x Hx Hne. rewrite Usp.
  destruct (decide (m (wa x) = m0 (wa x))) as [E|E].
  - rewrite <- E in Hne. destruct (Hch x Hx Hne) as (F & NU). right. left. split.
    + destruct F as (rg & Hrg' & Hin). exists rg. rewrite Efp. split; [exact Hrg'|exact Hin].
    + intros UB. exact (NU (HUB x UB)).
  - destruct (HCH x Hx E) as [A|[(F & NU)|[RG|(c & Hc & Hxc)]]]; [left; exact A| | |].
    + right. left. split; [|exact NU]. destruct F as (rg & Hrg' & Hin). exists rg. rewrite Efp. split; [exact Hrg'|exact Hin].
    + right. right. destruct RG as (r & rg & Hr & Hl & Hk & Hx'). exists r, rg. unfold region_of in *. rewrite Erg. auto.
    + right. left. destruct (Hown c x Hc Hxc) as (F & NU). split; [exact F|]. intros UB. exact (NU (Hub x (HUB x UB))).
Qed.

Lemma mw_sc_facts : forall s n, 1 <= n < MMAP_THRESHOLD ->
  0 <= mw_sc s n < 48 /\ n + IB <= class_size (mw_sc s n).
Proof.
  intros s n Hn. pose proof (size_to_class_range n ltac:(lia)) as [Hsc0 Hfit0].
  unfold mw_sc. destruct (_ && (usage_of s (size_to_class n) =? 0)) eqn:E; [|auto].
  apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E E32].
  apply Z.ltb_lt in E32. destruct (_ <=? 12); [|auto]. split; [lia|].
  pose proof (class_size_mono (size_to_class n) (size_to_class n + 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma growx_above : forall UB0 HTOP X R U L s m L' s' m' sp K,
  GROWX UB0 sp K L s m L' s' m' -> CUT HTOP X R U L' s' m' sp K ->
  forall x, sp <= x < 2^64 -> m' (wa x) = m (wa x).
Proof.
  intros UB0 HTOP X R U L s m L' s' m' sp K GX C x Hx.
  destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
  pose proof C as [HI HX N HG HD HT HTB]. pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  destruct GX as (_ & _ & _ & _ & CH). destruct (CH x ltac:(lia) E) as [[A|[(c & Hc & Hin)|[(r & rg & Hr & Hl & _ & Hxr)|(r & rg & Hr & Hl & _ & Hxr)]]]|((r & rg & Hr & Hl & _ & Hxr) & _)].
  - lia.
  - pose proof (HC c Hc) as P. unfold cplace, in_rng, cell_range in *. cbn [fst snd] in *. lia.
  - destruct (HG r rg Hr Hl) as (_ & _ & G3 & _). lia.
  - destruct (HG r rg Hr Hl) as (_ & _ & G3 & _). lia.
  - destruct (HG r rg Hr Hl) as (_ & _ & G3 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma wview_of_stk : forall m sp K x, stk_ok SEGS m (wa sp) K -> 0 <= sp <= 2^47 -> sp - K <= x < sp -> 0 <= x ->
  wview SEGS m (wa x) <> None.
Proof.
  intros m sp K x H Hsp Hx Hx0. pose proof (H (wa x) 1%nat ltac:(rewrite !u_wa_small by lia; lia) ltac:(rewrite !u_wa_small by lia; cbn; lia)) as S.
  cbn [store_ok] in S. destruct (wview SEGS m (wa x)); [discriminate | discriminate].
Qed.

Lemma stk_of_wview : forall m sp K, 0 <= K -> 0 <= sp - K -> sp <= 2^47 ->
  (forall x, sp - K <= x < sp -> wview SEGS m (wa x) <> None) -> stk_ok SEGS m (wa sp) K.
Proof.
  intros m sp K H0 H1 H2 H a n Ha1 Ha2. rewrite u_wa_small in Ha1, Ha2 by lia. rewrite <- (wa_u a).
  replace (bv_unsigned a) with ((sp - K) + (bv_unsigned a - (sp - K))) by ring.
  apply (store_ok_of_bytes SEGS m (sp - K) K); [|lia | lia]. intros j Hj. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma block_home : forall HTOP L s b x, WF s -> rgeoA HTOP L s -> rdisj L s -> ly_ctx L = 0x97c98 -> HTOP <= 2^47 ->
  In b (user_blocks s) -> loc_addr L (LMem (fst b)) <= x < loc_addr L (LMem (fst b)) + snd b ->
  (0x97c98 <= x < 0x98038) \/ exists r rg, region_of s r = Some rg /\ rg_live rg = true /\ ly_reg L r <= x < ly_reg L r + rg_len rg.
Proof.
  intros HTOP L s b x HW HG HD Hctx HTB Hb Hx.
  pose proof (layout_of_geo HTOP HTB [] None U0 s L HW Hctx HG HD) as HL.
  destruct (blocks_in_footprint s L b HW HL Hb) as (e & He & Hinc).
  unfold range_incl, block_range, crange in Hinc. cbn [fst snd] in Hinc.
  destruct (footprint_inv s e He) as [-> | [(a & Ha & ->) | (k & rgk & Hk & Kk & Lk & ->)]].
  - left. cbn [fst snd] in Hinc. change (loc_addr L (LCtx 0)) with (ly_ctx L + 0) in Hinc. rewrite Hctx in Hinc. unfold CTX_SIZE in Hinc. lia.
  - right. destruct (area_range HTOP [] None U0 s L a HW HG Ha) as (r & rg & _ & Hr & Hl & _ & A1 & A2 & _).
    exists r, rg. split; [exact Hr|]. split; [exact Hl|]. cbn [fst snd] in Hinc. unfold PGSZ in *. lia.
  - right. exists k, rgk. split; [exact Hk|]. split; [exact Lk|]. cbn [fst snd] in Hinc. change (loc_addr L (LMem (SP k 0))) with (ly_reg L k + 0) in Hinc. lia.
Qed.

(* [comment removed for export] *)
Lemma new_region_not_block : forall HTOP L s L' s' r rg x, WF s -> rgeoA HTOP L s -> rdisj L s -> ly_ctx L = 0x97c98 -> HTOP <= 2^47 ->
  lext L L' s -> RMONO s s' -> rgeoA HTOP L' s' -> rdisj L' s' ->
  region_of s' r = Some rg -> rg_live rg = true -> (length (st_regions s) <= r)%nat -> ly_reg L' r <= x < ly_reg L' r + rg_len rg ->
  ~ in_user_block L s x.
Proof.
  intros HTOP L s L' s' r rg x HW HG HD Hctx HTB HE RM HG' HD' Hr Hl Hge Hx (b & Hb & Hxb).
  destruct (block_home HTOP L s b x HW HG HD Hctx HTB Hb Hxb) as [C|(r0 & rg0 & Hr0 & Hl0 & Hx0)].
  - destruct (HG' r rg Hr Hl) as (_ & _ & _ & D). unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
  - destruct RM as (_ & RM). destruct (RM r0 rg0 Hr0 Hl0) as (rg0' & Hr0' & Hl0' & _ & Hlen).
    assert (Hlt : (r0 < length (st_regions s))%nat) by (unfold region_of in Hr0; apply nth_error_Some; congruence).
    assert (Ebase : ly_reg L' r0 = ly_reg L r0) by exact (proj2 (proj2 (proj2 HE)) r0 Hlt).
    assert (Hne : r0 <> r) by lia.
    pose proof (HD' r0 r rg0' rg Hne Hr0' Hr Hl0' Hl) as D. unfold ranges_disjoint in D. cbn [fst snd] in D.
    rewrite Ebase in D. lia.
Qed.

(* [comment removed for export] *)
Lemma init_env_frame : forall L m m1 AUXV RND typs lo hi, init_env L m AUXV RND typs ->
  (forall x, 0 <= x < 2^64 -> m1 (wa x) <> m (wa x) -> lo <= x < hi) -> hi <= AUXV -> hi <= RND + 8 -> 621616 <= lo ->
  init_env L m1 AUXV RND typs.
Proof.
  intros L m m1 AUXV RND typs lo hi IE CH H1 H2 H3.
  assert (RD : forall a k, 0 <= a -> a + Z.of_nat k <= 2^64 -> (a + Z.of_nat k <= lo \/ hi <= a) -> rdn SEGS m1 (wa a) k = rdn SEGS m (wa a) k).
  { intros a k Ha Hk D. apply rdn_frame_n; [exact Ha | exact Hk|]. intros x Hx.
    destruct (decide (m1 (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso. pose proof (CH x ltac:(lia) E). lia. }
  destruct IE as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  split; [rewrite RD by (cbn; lia); exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  split.
  { intros i Hi. destruct (A5 i Hi) as (T1 & T2 & T3). split; [exact T1|]. split.
    - rewrite RD by (cbn; pose proof (Nat2Z.is_nonneg i); assert (Z.of_nat i < Z.of_nat (length typs)) by lia; lia). exact T2.
    - intros E. rewrite RD by (cbn; pose proof (Nat2Z.is_nonneg i); assert (Z.of_nat i < Z.of_nat (length typs)) by lia; lia). exact (T3 E). }
  split; [rewrite RD by (cbn; pose proof (Nat2Z.is_nonneg (length typs)); lia); exact A6|].
  split; [exact A7|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|].
  rewrite RD by (cbn; lia). exact A11.
Qed.

Section CL.
Context {fx : FPState}.
Variables (FORB : list (Z * Z)) (HTOP : Z) (rom : word -> option byte).
Hypothesis HFORB : forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB -> ranges_disjoint (a, n) (0x10000, 0x89000).
Hypothesis ASWK : @as_wk_stmt fx.

#[using="HFORB ASWK"] Theorem class_wk : forall L s m (regs : bvmap 5 word) n,
  Heap0 L s m -> (forall c, 0 <= c < 48 -> usage_of s c < 2^40) -> ly_ctx L = 0x97c98 -> rgeoA HTOP L s -> rdisj L s ->
  HTOP <= 2^47 -> 2^20 <= HTOP -> MENV m ->
  1 <= n <= 131051 -> getr regs 10 = wa n ->
  bv_unsigned (getr regs 2) mod 16 = 0 -> bv_unsigned (getr regs 2) <= 2^47 -> HTOP <= bv_unsigned (getr regs 2) - 8192 ->
  stk_ok SEGS m (getr regs 2) 8192 ->
  PGSZ <= ly_brk0 L -> ly_brk0 L mod PGSZ = 0 -> ly_brk0 L <= HTOP ->
  (st_init_done s = true \/ AMI L m (bv_unsigned (getr regs 2))) ->
  wk SEGS FORB HTOP rom L regs (wa 0x530c8) m (malloc n s) (mw_post HTOP regs m L s).
Proof. LiaFast.lf_pins (fun (HFORB ASWK : LiaFast.U) => LiaFast.u0).
  intros L s m regs n H0 HUS Hctx HG HD HTB HT20 HME Hn HR10 Hsp16 Hsp47 Htop HSTK B1 B2 B3 Hini.
  pose proof H0 as (HW & HR & HM).
  destruct HME as ((can & HENV) & HPG & HKRO). pose proof (TABS_of_KRO m HKRO) as HTABS.
  pose proof HENV as (E1 & E2 & Edb & E3 & E4 & E5 & E6 & Eer & Eew).
  set (sp0 := bv_unsigned (getr regs 2)) in *.
  assert (Rsp : 2^20 + 8192 <= sp0 <= 2^47) by lia.
  assert (R2w : getr regs 2 = wa sp0) by (unfold sp0; rewrite wa_u; reflexivity).
  assert (Henv : nenv m) by (split; [exact E4 | split; [exact E2 | exists can; split; [exact E3 | exact E5]]]).
  (* [comment removed for export] *)
  assert (C0 : CUT HTOP [] None U0 L s m sp0 8192).
  { constructor; try assumption.
    - intros x [].
    - apply (NC_of_geo HTOP HTB [] None U0 s L m sp0 8192 HW ltac:(intros x []) HG HD Hctx ltac:(lia) (proj1 (proj2 HR)) (proj2 (proj2 HR))
               Henv ltac:(rewrite <- R2w; exact HSTK) ltac:(lia) ltac:(lia) ltac:(lia) Hsp16). }
  (* [comment removed for export] *)
  assert (STK1024 : stk_ok SEGS m (getr regs 2) 1024) by (apply (stk_ok_mono' m (getr regs 2) 8192 1024 HSTK); lia).
  assert (A : exists R1, msteps SEGS (mkst regs (wa 0x530c8) m rom) (mkst R1 (wa 0x53f2c) (ma_mem m regs) rom) /\ ma_regs R1 regs n (size_to_class n)).
  { destruct (Z_le_gt_dec n 156) as [Hs|Hm].
    - destruct (ma_arm regs m rom n HR10 ltac:(lia) ltac:(lia) Hsp16 STK1024) as (R1 & M1 & Q). exists R1. split; [exact M1|].
      rewrite <- (size_to_class_small n) by lia. exact Q.
    - exact (mam_arm regs m rom n HR10 ltac:(lia) ltac:(lia) Hsp16 STK1024 E2 Edb). }
  destruct A as (R1 & M1 & (Q8 & Q9 & Q19 & Q20 & Q2 & K1)).
  set (m1 := ma_mem m regs) in *.
  assert (M1out : forall x, 0 <= x < 2^64 -> ~ (sp0 - 48 <= x < sp0) -> m1 (wa x) = m (wa x)).
  { intros x Hx H. apply ma_mem_out; [lia | exact Hx | exact H]. }
  pose proof (ma_mem_grows m regs) as M1g.
  assert (C1 : CUT HTOP [] None U0 L s m1 sp0 8192).
  { apply (CUT_stack HTOP [] None U0 L s m m1 sp0 8192 C0 M1g). intros x Hx Hn'. apply M1out; [exact Hx | lia]. }
  assert (C2 : CUT HTOP [] None U0 L s m1 (sp0 - 48) (8192 - 48)).
  { apply (CUT_shift HTOP [] None U0 L s m1 sp0 8192 48 C1); [lia | reflexivity | lia]. }
  pose proof C1 as [_ _ N1 _ _ _ _].
  assert (HR1 : repr L s (bview SEGS m1)) by exact (repr_of_repr_x L s _ (nc_repr _ _ _ _ _ _ _ N1)).
  assert (HM1 : markers_hold L s (bview SEGS m1)).
  { apply (markers_frame HTOP None U0 L s m m1 HW HG HD HM). intros x Hx Hne. left.
    destruct (Z_lt_le_dec x (sp0 - 48)) as [Lt|Ge]; [exfalso; apply Hne; apply M1out; [exact Hx | lia] | lia]. }
  assert (M1lo : forall a k, 0 <= a -> a + Z.of_nat k <= sp0 - 48 -> rdn SEGS m1 (wa a) k = rdn SEGS m (wa a) k).
  { intros a k Ha Hk. apply rdn_frame_n; [lia | lia | intros x Hx; apply M1out; lia]. }
  assert (HP : forall q, In q (keys s) -> 1 <= loc_addr L (LMem q) /\ loc_addr L (LMem q) + 40 <= 2^47 /\ loc_addr L (LMem q) mod 8 = 0).
  { intros q Hq. destruct (nc_mplace _ _ _ _ _ _ _ N1 q Hq) as (A1 & A2 & _ & A4). split; [exact A1|]. split; [lia | exact A4]. }
  assert (Mnl1 : rdn SEGS m1 (wa 0x97c23) 1 = Some (word_to_le_bytes 1 (wa 0))) by (rewrite M1lo by (cbn; lia); exact E1).
  assert (Mdb1 : forall j, 0 <= j < 32 -> rdn SEGS m1 (wa (98952 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn)))).
  { intros j Hj. rewrite M1lo by (cbn; lia). exact (Edb j Hj). }
  assert (Mlock1 : rdn SEGS m1 (wa 621712) 4 = Some (word_to_le_bytes 4 (wa 0))) by (rewrite M1lo by (cbn; lia); exact E6).
  assert (SP1 : getr R1 2 = wa (sp0 - 48)).
  { rewrite Q2, R2w. apply bv_eq. rewrite u_vaddi''; rewrite ?u_wa_small by lia; lia. }
  (* [comment removed for export] *)
  assert (FR : forall k (r : bvmap 5 word -> word), In (k, r) [(8, fun R => getr R 1); (16, fun R => getr R 8); (24, fun R => getr R 9);
                  (32, fun R => getr R 18); (40, fun R => getr R 19); (48, fun R => getr R 20)] ->
               rdn SEGS m1 (wa (sp0 - k)) 8 = Some (word_to_le_bytes 8 (r regs))).
  { intros k r Hk. replace (sp0 - k) with (bv_unsigned (getr regs 2) + - k) by (unfold sp0; ring). exact (ma_rdn_save m regs ltac:(lia) k r Hk). }
  destruct (b_decide L s m1 rom n R1 HW HR1 Hctx HP HUS Mnl1 Mdb1 Hn Q8 Q9 Q19 Q20) as [(R2 & g & am & Mb & F) | (R2 & Mb & SL)].
  - (* [comment removed for export] *)
    destruct F as (Hhd & HMT & Hav & B8 & B9 & B18 & B19 & B20 & KB).
    rewrite (malloc_fast_eq n s g am ltac:(unfold MMAP_THRESHOLD; lia) Hhd HMT Hav).
    assert (Hux : usedX [] s g am) by (unfold usedX, MTX; cbn [memb]; exact HMT).
    pose proof (size_to_class_range n ltac:(unfold MMAP_THRESHOLD; lia)) as [Hsc0 _].
    assert (Hmw : 0 <= mw_sc s n < 48).
    { unfold mw_sc. destruct (_ && (usage_of s (size_to_class n) =? 0)) eqn:Ec; [|lia].
      apply andb_true_iff in Ec as [Ec _]. apply andb_true_iff in Ec as [Ec _]. apply andb_true_iff in Ec as [Ec _].
      apply andb_true_iff in Ec as [Ec E32]. apply Z.ltb_lt in E32. destruct (_ <=? 12); lia. }
    destruct (head_used [] None U0 s (mw_sc s n) g HW Hmw Hhd) as (am' & Hu' & Hsa).
    pose proof (usedX_fun _ _ _ _ _ Hu' Hux) as ->. clear Hu'.
    set (s1 := set_meta s g (MUsed (mf_am1 am))).
    set (Gv := loc_addr L (LMem g)) in *.
    set (m2 := mb0_mem m1 Gv (am_avail am)).
    assert (C3 : CUT HTOP [] (Some (g, mf_idx am)) U0 L s1 m2 (sp0 - 48) (8192 - 48)).
    { apply (take_cut HTOP L s m1 (sp0 - 48) (8192 - 48) g am C2 Hux); [rewrite Hsa; exact Hmw | rewrite Hsa; exact Hhd | exact Hav]. }
    destruct (nc_mplace _ _ _ _ _ _ _ N1 g ltac:(eapply MT_keys; exact HMT)) as (G1 & G2 & G4 & G3). fold Gv in G1, G2, G3, G4.
    assert (M2out : forall x, 0 <= x < 2^64 -> ~ (Gv + 24 <= x < Gv + 28) -> m2 (wa x) = m1 (wa x)).
    { intros x Hx H. unfold m2, mb0_mem. rewrite MngWb.wbytes_out by (unfold word_to_le_bytes; rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat]; rewrite ?u_wa_small by lia; lia). reflexivity. }
    assert (M2hi : forall a k, sp0 - 48 <= a -> a + Z.of_nat k <= sp0 -> rdn SEGS m2 (wa a) k = rdn SEGS m1 (wa a) k).
    { intros a k Ha Hk. apply rdn_frame_n; [lia | lia | intros x Hx; apply M2out; lia]. }
    assert (HM2 : markers_hold L s1 (bview SEGS m2)).
    { unfold s1, markers_hold. rewrite (markers_set_meta s g am (mf_am1 am) HMT) by (destruct am; reflexivity). fold (markers_hold L s (bview SEGS m2)).
      apply (markers_frame HTOP None U0 L s m1 m2 HW HG HD HM1). intros x Hx Hne. right.
      destruct (key_slot_range HTOP [] None U0 s L g HW HG ltac:(eapply MT_keys; exact HMT)) as (ag & j & rr & rga & Hag & Hj & Eag & Epr & Hrr & Hlv & Hkda & A1 & A2 & A3 & A4).
      exists rr, rga. split; [exact Hrr|]. split; [exact Hlv|]. split; [exact Hkda|].
      destruct (Z_lt_le_dec x (Gv + 24)) as [Lt|Ge]; [exfalso; apply Hne; apply M2out; [exact Hx | lia]|].
      destruct (Z_lt_le_dec x (Gv + 28)) as [Lt2|Ge2]; [|exfalso; apply Hne; apply M2out; [exact Hx | lia]].
      fold Gv in A4. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia. }
    assert (Hux1 : usedX [] s1 g (mf_am1 am)) by (unfold s1; apply usedX_upd; left; auto).
    destruct (mw_sc_facts s n ltac:(unfold MMAP_THRESHOLD; lia)) as (_ & Hfitc).
    destruct (lowbit_spec (am_avail am) ltac:(pose proof (bd_meta L s m1 HW HR1 g am HMT) as (_ & _ & _ & Rav & _); lia)) as (k0 & Hk0 & Hlb & Hbit & _).
    assert (Eidx : mf_idx am = k0) by (unfold mf_idx, mf_first; rewrite Hlb; apply ctz32_bit; lia).
    pose proof (avail_bit_not_undersized [] None U0 s g am (mf_idx am) HW Hux ltac:(rewrite Hsa; exact Hmw) ltac:(lia)
                  ltac:(rewrite Z.lor_spec, Eidx, Hbit; reflexivity)) as Hus.
    assert (Hfit1 : n + IB <= stride_of (mf_am1 am)) by (unfold mf_am1; rewrite stride_set_avail; rewrite Hsa in Hus; lia).
    assert (Esc1 : am_sc (mf_am1 am) = mw_sc s n) by (unfold mf_am1; destruct am; exact Hsa).
    assert (SP2 : getr R2 2 = wa (sp0 - 48)) by (transitivity (getr R1 2); [exact (KB 2%nat ltac:(lmemb)) | exact SP1]).
    assert (K3 : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr R2 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
    { intros k Hk. rewrite (KB k ltac:(clear - Hk; unfold kb_keep; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk)).
      apply K1. clear - Hk. cbn [In] in *. repeat (destruct Hk as [<-|Hk]; [lmemb|]). destruct Hk. }
    assert (Mlock2 : rdn SEGS m2 (wa 621712) 4 = Some (word_to_le_bytes 4 (wa 0))).
    { rewrite (rdn_frame_n m1 m2 621712 4%nat); [exact Mlock1 | lia | cbn; lia | intros x Hx; apply M2out; [cbn in Hx; lia | clear - Hx G4 G1; cbn in Hx; lia]]. }
    eapply wk_msteps; [exact (msteps_trans SEGS _ _ _ M1 Mb)|].
    apply (tail_wk FORB HTOP rom L s1 m2 R2 n g (mf_idx am) (mf_am1 am) (sp0 - 48) (8192 - 48)
             (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) _ C3 HM2 Hux1 ltac:(lia) Hfit1).
    { intros _. unfold MMAP_THRESHOLD. lia. }
    { rewrite Esc1. intros E. lia. }
    { rewrite Esc1. intros _ _. exact Hhd. }
    { exact SP2. }
    { exact B8. }
    { exact B9. }
    { exact B18. }
    { exact B19. }
    { rewrite M2hi by (cbn; lia). replace (sp0 - 48 + 40) with (sp0 - 8) by ring. exact (FR 8 (fun R => getr R 1) ltac:(lmemb)). }
    { rewrite M2hi by (cbn; lia). replace (sp0 - 48 + 32) with (sp0 - 16) by ring. exact (FR 16 (fun R => getr R 8) ltac:(lmemb)). }
    { rewrite M2hi by (cbn; lia). replace (sp0 - 48 + 24) with (sp0 - 24) by ring. exact (FR 24 (fun R => getr R 9) ltac:(lmemb)). }
    { rewrite M2hi by (cbn; lia). replace (sp0 - 48 + 16) with (sp0 - 32) by ring. exact (FR 32 (fun R => getr R 18) ltac:(lmemb)). }
    { rewrite M2hi by (cbn; lia). replace (sp0 - 48 + 8) with (sp0 - 40) by ring. exact (FR 40 (fun R => getr R 19) ltac:(lmemb)). }
    { rewrite M2hi by (cbn; lia). replace (sp0 - 48 + 0) with (sp0 - 48) by ring. exact (FR 48 (fun R => getr R 20) ltac:(lmemb)). }
    { exact Mlock2. }
    intros p s' R m' T.
    assert (ND : List.NoDup (keys s)) by exact (proj1 (inv_keys HW)).
    assert (ND1 : List.NoDup (keys s1)) by (unfold s1; rewrite keys_set_meta by (eapply MT_keys; exact HMT); exact ND).
    assert (UB1 : user_blocks s1 = user_blocks s).
    { apply (ub_same_user_blocks s s1 ND ND1). apply ub_same_upd_In; [eapply MT_Some_In_keys; exact HMT|]. rewrite HMT. cbn [ucontrib].
      unfold mf_am1. apply blocks_of_avail. }
    apply (mw_post_of_tail HTOP L s1 m2 R2 L s m regs p s' R m' sp0 T SP2 eq_refl ltac:(lia) K3 (lext_refl L s)).
    + apply rgeo_of_A. intros r rg Hr Hl. apply (HG r rg); [unfold region_of in *; rewrite (tl_regions _ _ _ _ _ _ _ _ _ _ _ _ _ _ T) in Hr; exact Hr | exact Hl].
    + intros x Hx Hne. destruct (decide (m1 (wa x) = m (wa x))) as [E|E].
      * rewrite <- E in Hne. right. left. destruct (Z_lt_le_dec x (Gv + 24)) as [A|A]; [exfalso; apply Hne; apply M2out; [exact Hx | lia]|].
        destruct (Z_lt_le_dec x (Gv + 28)) as [B|B]; [|exfalso; apply Hne; apply M2out; [exact Hx | lia]].
        assert (Cav : In (MCell (LMem (padd g META_avail)) 4 (VZ (am_avail am))) (image s)).
        { apply (In_image_used s g am _ (KS_of_WF s HW) HMT). left. cbn [meta_slot_cells]. right. right. right. left. reflexivity. }
        assert (Hxr : loc_addr L (LMem (padd g META_avail)) <= x < loc_addr L (LMem (padd g META_avail)) + Z.of_nat 4).
        { rewrite loc_padd. unfold META_avail. fold Gv. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
        destruct (image_owned s L _ x HW (proj1 HR) Cav Hxr) as (F1 & F2).
        split; [|exact F2]. destruct F1 as (rg & Hrg & Hin). exists rg. unfold s1. rewrite footprint_set_meta. split; [exact Hrg | exact Hin].
      * left. destruct (Z_lt_le_dec x (sp0 - 48)) as [A|A]; [exfalso; apply E; apply M1out; [exact Hx | lia]|].
        destruct (Z_lt_le_dec x sp0) as [B|B]; [lia | exfalso; apply E; apply M1out; [exact Hx | lia]].
    + intros x (b & Hb & Hxb). exists b. rewrite UB1. split; [exact Hb | exact Hxb].
    + exact (tl_fp _ _ _ _ _ _ _ _ _ _ _ _ _ _ T).
    + exact (tl_regions _ _ _ _ _ _ _ _ _ _ _ _ _ _ T).
    + intros a kk H1 H2. apply (store_ok_mono SEGS kk m m' a).
      * eapply mem_grows_trans; [exact M1g|]. eapply mem_grows_trans; [apply mb0_mem_grows|]. exact (tl_grows _ _ _ _ _ _ _ _ _ _ _ _ _ _ T).
      * exact (HSTK a kk H1 H2).
  - (* [comment removed for export] *)
    destruct SL as (Hnone & B8 & B9 & B10 & B11 & B18 & B20 & KB).
    destruct (mw_sc_facts s n ltac:(unfold MMAP_THRESHOLD; lia)) as (Hmw & Hfitc).
    set (sc := mw_sc s n) in *.
    assert (SP2 : getr R2 2 = wa (sp0 - 48)) by (transitivity (getr R1 2); [exact (KB 2%nat ltac:(lmemb)) | exact SP1]).
    destruct (mwj_pmwj R2 m1 rom 0 ltac:(constructor; lia) ltac:(apply Forall_nil)) as (R3 & Mj & J1 & KJ).
    change (mwj_mem_pmwj m1 R2 0) with m1 in Mj.
    set (UB0 := in_user_block L s).
    assert (Mtabs1 : TABS m1).
    { destruct HTABS as (T1 & T2). split.
      - intros sc' kk Hsc' Hkk. rewrite M1lo by (cbn; lia). exact (T1 sc' kk Hsc' Hkk).
      - intros kk Hkk. rewrite M1lo by (cbn; lia). exact (T2 kk Hkk). }
    assert (Mpg1 : rdn SEGS m1 (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096))) by (rewrite M1lo by (cbn; lia); exact HPG).
    assert (Hini1 : st_init_done s = true \/ AMI L m1 (sp0 - 48)).
    { destruct Hini as [Hd|(AUXV & RND & typs & IE & Ha & Hr)]; [left; exact Hd|]. right. exists AUXV, RND, typs.
      split; [|lia]. apply (init_env_frame L m m1 AUXV RND typs (sp0 - 48) sp0 IE); [|lia | lia | lia].
      intros x Hx Hne. destruct (Z_lt_le_dec x (sp0 - 48)) as [A|A]; [exfalso; apply Hne; apply M1out; [exact Hx | lia]|].
      destruct (Z_lt_le_dec x sp0) as [B|B]; [lia | exfalso; apply Hne; apply M1out; [exact Hx | lia]]. }
    apply (malloc_slow_wk SEGS FORB HTOP rom n s L regs (wa 0x530c8) m (mw_post HTOP regs m L s)
             (as_qpost UB0 HTOP [] U0 L s m1 R3 (sp0 - 48) (8192 - 48) sc n) ltac:(unfold MMAP_THRESHOLD; lia) Hnone).
    + eapply wk_msteps; [exact (msteps_trans SEGS _ _ _ M1 (msteps_trans SEGS _ _ _ Mb Mj))|].
      apply (ASWK FORB HFORB NEST_FUEL UB0 HTOP [] U0 L s m1 R3 rom (sp0 - 48) (8192 - 48) sc n C2 HM1).
      * unfold KAS, need. destruct (sc <? 24) eqn:E24; [apply Z.ltb_lt in E24; rewrite Z2Nat.id by lia; lia | cbn; lia].
      * exact Hmw.
      * lia.
      * exact Hfitc.
      * apply need_le_fuel. lia.
      * transitivity (getr R2 2); [exact (KJ 2%nat ltac:(lmemb)) | exact SP2].
      * transitivity (getr R2 10); [exact (KJ 10%nat ltac:(lmemb)) | exact B10].
      * transitivity (getr R2 11); [exact (KJ 11%nat ltac:(lmemb)) | exact B11].
      * exact HUS.
      * exact Mdb1.
      * exact Mtabs1.
      * exact Mpg1.
      * exact B1.
      * exact B2.
      * exact B3.
      * exact Hini1.
      * intros x Hx. exact Hx.
    + intros L' idx s1 R' pc' m' HQ0.
      destruct HQ0 as (idx' & s' & g & am & Eq & Epc & A10 & AK & C3 & GX & HM3 & Hhd & Hux & Hsc & Hfit & Hidx & _ & Hub & _).
      injection Eq as <- Es1. subst s1. subst pc'.
      unfold k_slow. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). fold sc. rewrite Hhd.
      pose proof C3 as [HI3 _ N3 HG3 HD3 HT3 _].
      pose proof N3 as [HRx3 HEX3 _ HK3 _ _ HSTK3 _ _ _ _ HC3 HMP3 _].
      pose proof (EXC_ok_of_z [] s' [] (proj1 HK3) HEX3) as HEO3.
      pose proof (usedX_MT _ _ _ _ Hux) as [HMT3 _].
      destruct (HMP3 g ltac:(eapply MT_keys; exact HMT3)) as (G1 & G2 & G4 & G3).
      set (Gv := loc_addr L' (LMem g)) in *.
      pose proof (inv_groups HI3 g am Hux) as ((Mlast & _) & _).
      (* [comment removed for export] *)
      assert (ABV : forall x, sp0 - 48 <= x < 2^64 -> m' (wa x) = m1 (wa x)) by (intros x Hx; exact (growx_above UB0 HTOP [] (Some (g, idx)) U0 L s m1 L' s' m' (sp0 - 48) (8192 - 48) GX C3 x Hx)).
      assert (FR' : forall k (r : bvmap 5 word -> word), In (k, r) [(8, fun R => getr R 1); (16, fun R => getr R 8); (24, fun R => getr R 9);
                  (32, fun R => getr R 18); (40, fun R => getr R 19); (48, fun R => getr R 20)] ->
               rdn SEGS m' (wa (sp0 - k)) 8 = Some (word_to_le_bytes 8 (r regs))).
      { intros k r Hk. assert (Rk : 8 <= k <= 48) by (cbn [In] in Hk; repeat (destruct Hk as [E|Hk]; [injection E as <- _; lia|]); destruct Hk).
        rewrite (rdn_frame_n m1 m' (sp0 - k) 8%nat) by (try lia; intros x Hx; apply ABV; lia). exact (FR k r Hk). }
      assert (Mlock3 : rdn SEGS m' (wa 621712) 4 = Some (word_to_le_bytes 4 (wa 0))).
      { destruct GX as (_ & _ & _ & SI3 & _). rewrite (rdn_frame_n m1 m' 621712 4%nat); [exact Mlock1 | lia | cbn; lia |].
        intros x Hx. cbn in Hx. apply SI3; lia. }
      (* [comment removed for export] *)
      destruct (mwr_pmwr R' m' rom 0 ltac:(constructor; [transitivity (getr R3 1); [exact (AK 1%nat ltac:(lmemb)) | exact J1] | lia]) ltac:(apply Forall_nil))
        as (R4 & Mr & _ & KR).
      change (mwr_mem_pmwr m' R' 0) with m' in Mr.
      assert (CH : forall k, In k [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat -> getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr R2 (Z_to_bv 5 (Z.of_nat k))).
      { intros k Hk. rewrite (KR k ltac:(clear - Hk; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk)).
        rewrite (AK k ltac:(clear - Hk; unfold callee_as; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk)).
        exact (KJ k ltac:(clear - Hk; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk)). }
      assert (MACT3 : rdn SEGS m' (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa Gv))).
      { pose proof (rx_act L' s' m' [] HRx3 HEO3 (nc_ctx _ _ _ _ _ _ _ N3) (Z.to_nat sc) ltac:(lia)) as RA.
        rewrite Z2Nat.id in RA by lia. replace (8 * sc + 621800) with (621800 + 8 * sc) by ring. rewrite RA.
        unfold active_hd in Hhd. rewrite Hhd. reflexivity. }
      assert (P5 : mas_pre R4 m' n sc idx Gv).
      { constructor.
        - transitivity (getr R2 8); [exact (CH 8%nat ltac:(lmemb)) | exact B8].
        - transitivity (getr R2 9); [exact (CH 9%nat ltac:(lmemb)) | exact B9].
        - transitivity (getr R' 10); [exact (KR 10%nat ltac:(lmemb)) | exact A10].
        - transitivity (getr R2 18); [exact (CH 18%nat ltac:(lmemb)) | exact B18].
        - transitivity (getr R2 20); [exact (CH 20%nat ltac:(lmemb)) | exact B20].
        - lia.
        - lia.
        - lia.
        - clear - G1 G2 Rsp. lia.
        - exact MACT3. }
      destruct (mas_pmas R4 m' rom n sc idx Gv P5 ltac:(apply Forall_nil)) as (R5 & Mm & C8 & C9 & C10 & C18 & C19 & C20 & KM).
      change (mas_mem_pmas m' R4 n sc idx Gv) with m' in Mm.
      assert (SP5 : getr R5 2 = wa (sp0 - 48)).
      { transitivity (getr R4 2); [exact (KM 2%nat ltac:(lmemb))|]. transitivity (getr R2 2); [exact (CH 2%nat ltac:(lmemb)) | exact SP2]. }
      eapply wk_msteps; [exact (msteps_trans SEGS _ _ _ Mr Mm)|].
      apply (tail_wk FORB HTOP rom L' s' m' R5 n g idx am (sp0 - 48) (8192 - 48)
               (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) _ C3 HM3 Hux ltac:(lia) Hfit).
      { intros _. unfold MMAP_THRESHOLD. lia. }
      { rewrite Hsc. intros E. lia. }
      { rewrite Hsc. intros _ _. exact Hhd. }
      { exact SP5. }
      { exact C8. }
      { exact C9. }
      { exact C18. }
      { exact C19. }
      { replace (sp0 - 48 + 40) with (sp0 - 8) by ring. exact (FR' 8 (fun R => getr R 1) ltac:(lmemb)). }
      { replace (sp0 - 48 + 32) with (sp0 - 16) by ring. exact (FR' 16 (fun R => getr R 8) ltac:(lmemb)). }
      { replace (sp0 - 48 + 24) with (sp0 - 24) by ring. exact (FR' 24 (fun R => getr R 9) ltac:(lmemb)). }
      { replace (sp0 - 48 + 16) with (sp0 - 32) by ring. exact (FR' 32 (fun R => getr R 18) ltac:(lmemb)). }
      { replace (sp0 - 48 + 8) with (sp0 - 40) by ring. exact (FR' 40 (fun R => getr R 19) ltac:(lmemb)). }
      { replace (sp0 - 48 + 0) with (sp0 - 48) by ring. exact (FR' 48 (fun R => getr R 20) ltac:(lmemb)). }
      { exact Mlock3. }
      intros p s'' R m'' T.
      assert (ND : List.NoDup (keys s)) by exact (proj1 (inv_keys HW)).
      assert (ND3 : List.NoDup (keys s')) by exact (proj1 (inv_keys HI3)).
      assert (UBE : user_blocks s' = user_blocks s) by exact (ub_same_user_blocks s s' ND ND3 Hub).
      destruct GX as (HE & RM & GI & SI3 & CHX).
      assert (K3 : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr R5 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
      { intros k Hk. rewrite (KM k ltac:(clear - Hk; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk)).
        rewrite (CH k ltac:(clear - Hk; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk)).
        rewrite (KB k ltac:(clear - Hk; unfold kb_keep; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk)).
        apply K1. clear - Hk. cbn [In] in *. repeat (destruct Hk as [<-|Hk]; [lmemb|]). destruct Hk. }
      apply (mw_post_of_tail HTOP L' s' m' R5 L s m regs p s'' R m'' sp0 T SP5 eq_refl ltac:(lia) K3 HE).
      { apply rgeo_of_A. intros r rg Hr Hl. apply (HG3 r rg); [unfold region_of in *; rewrite (tl_regions _ _ _ _ _ _ _ _ _ _ _ _ _ _ T) in Hr; exact Hr | exact Hl]. }
      { intros x Hx Hne. destruct (decide (m1 (wa x) = m (wa x))) as [E|E].
        * rewrite <- E in Hne.
          destruct (CHX x Hx Hne) as [[A|[(c & Hc & Hin)|[(r & rg & Hr & Hl & Hge & Hxr)|RG]]]|((r & rg & Hr & Hl & Kd & Hxr) & NUB)].
          -- left. lia.
          -- right. right. right. exists c. split; [exact Hc|]. unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. exact Hin.
          -- assert (Kd' : rg_kind rg = RkMap \/ rg_kind rg <> RkMap) by (destruct (rg_kind rg); first [left; reflexivity | right; discriminate]).
             destruct Kd' as [Kd|Kd].
             ++ right. left. split.
                ** exists (LMem (SP r 0), rg_len rg). split; [exact (footprint_region_In s' r rg Hr Kd Hl)|]. cbn [fst snd].
                   change (loc_addr L' (LMem (SP r 0))) with (ly_reg L' r + 0). lia.
                ** exact (new_region_not_block HTOP L s L' s' r rg x HW HG HD Hctx HTB HE RM HG3 HD3 Hr Hl Hge Hxr).
             ++ right. right. left. exists r, rg. auto.
          -- right. right. left. exact RG.
          -- right. left. split; [|exact NUB].
             exists (LMem (SP r 0), rg_len rg). split; [exact (footprint_region_In s' r rg Hr Kd Hl)|]. cbn [fst snd].
             change (loc_addr L' (LMem (SP r 0))) with (ly_reg L' r + 0). lia.
        * left. destruct (Z_lt_le_dec x (sp0 - 48)) as [A|A]; [exfalso; apply E; apply M1out; [exact Hx | lia]|].
          destruct (Z_lt_le_dec x sp0) as [B|B]; [lia | exfalso; apply E; apply M1out; [exact Hx | lia]]. }
      { intros x (b & Hb & Hxb). exists b. rewrite UBE. split; [exact Hb|].
        destruct (in_user_blocks_inv s b Hb) as (h & ah & j & f & Hh & Hj & Hf & Kf & Eb).
        apply (used_metas_usedX s h ah HW) in Hh.
        pose proof (used_group_prid_lt [] None U0 s h ah HW Hh) as Hlt.
        assert (Ep : prid (fst b) = prid (am_mem ah)) by (rewrite Eb; cbn [fst]; unfold frame_ptr; rewrite prid_padd, prid_slot_start; reflexivity).
        assert (EL : loc_addr L' (LMem (fst b)) = loc_addr L (LMem (fst b))).
        { destruct (fst b) as [rb ob] eqn:Ef. cbn [loc_addr]. cbn [prid] in Ep. subst rb.
          rewrite (proj2 (proj2 (proj2 HE)) (prid (am_mem ah)) Hlt). reflexivity. }
        rewrite EL. exact Hxb. }
      { exact (tl_fp _ _ _ _ _ _ _ _ _ _ _ _ _ _ T). }
      { exact (tl_regions _ _ _ _ _ _ _ _ _ _ _ _ _ _ T). }
      { rewrite R2w. apply stk_of_wview; [lia | lia | lia|]. intros x Hx.
        assert (ST1 : stk_ok SEGS m1 (wa sp0) 8192) by (intros a kk H1 H2; apply (store_ok_mono SEGS kk m m1 a M1g); rewrite <- R2w in H1, H2; exact (HSTK a kk H1 H2)).
        destruct (Z_lt_le_dec x (sp0 - 48)) as [A|A].
        * pose proof (wview_of_stk m' (sp0 - 48) (8192 - 48) x HSTK3 ltac:(lia) ltac:(lia) ltac:(lia)) as W'.
          intros W''. apply W'. destruct (wview SEGS m' (wa x)) eqn:Ew; [|reflexivity]. exfalso.
          apply (wview_grows SEGS m' m'' (wa x) (tl_grows _ _ _ _ _ _ _ _ _ _ _ _ _ _ T)); [rewrite Ew; discriminate | exact W''].
        * assert (Em : m'' (wa x) = m1 (wa x)).
          { destruct (decide (m'' (wa x) = m' (wa x))) as [E|E].
            - rewrite E. apply ABV. lia.
            - exfalso. destruct (tl_chg _ _ _ _ _ _ _ _ _ _ _ _ _ _ T x ltac:(lia) E) as ((e & He & Hxe) & _).
              destruct (footprint_inv s' e He) as [-> | [(a & Ha & ->) | (k & rgk & Hk & Kk & Lk & ->)]].
              + cbn [fst snd] in Hxe. change (loc_addr L' (LCtx 0)) with (ly_ctx L' + 0) in Hxe. rewrite (nc_ctx _ _ _ _ _ _ _ N3) in Hxe. unfold CTX_SIZE in Hxe. lia.
              + destruct (area_range HTOP [] (Some (g, idx)) U0 s' L' a HI3 HG3 Ha) as (r & rg & _ & Hr & Hl & _ & B1' & B2' & _).
                destruct (HG3 r rg Hr Hl) as (_ & _ & G3' & _). cbn [fst snd] in Hxe. unfold PGSZ in *. lia.
              + destruct (HG3 k rgk Hk Lk) as (_ & _ & G3' & _). cbn [fst snd] in Hxe. change (loc_addr L' (LMem (SP k 0))) with (ly_reg L' k + 0) in Hxe. lia. }
          unfold wview. rewrite Em. fold (wview SEGS m1 (wa x)). exact (wview_of_stk m1 sp0 8192 x ST1 ltac:(lia) ltac:(lia) ltac:(lia)). }
Qed.
End CL.
