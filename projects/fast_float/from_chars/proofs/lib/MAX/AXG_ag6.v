(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfArith MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngHeap MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfM MngNtfS MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngMW2 MngNtfPre MngCtx MngCtx2 MngShape AXG_as1 AXG_am1 AXG_amr0 AXG_ag0 AXG_ag1 AXG_ag3p AXG_ag5.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngShape OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amr0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag3p OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.

(* [comment removed for export] *)
Lemma region_of_snoc : forall s rgn k rg, region_of (set_regions (st_regions s ++ [rgn]) s) k = Some rg ->
  ((k < length (st_regions s))%nat /\ region_of s k = Some rg) \/ (k = length (st_regions s) /\ rg = rgn).
Proof.
  intros s rgn k rg H. unfold region_of in *. cbn [st_regions set_regions] in H.
  destruct (Nat.lt_ge_cases k (length (st_regions s))) as [Hk|Hk].
  - left. split; [exact Hk|]. rewrite nth_error_app1 in H by exact Hk. exact H.
  - right. rewrite nth_error_app2 in H by exact Hk. destruct (k - length (st_regions s))%nat as [|j] eqn:E.
    + cbn in H. injection H as <-. split; [lia | reflexivity].
    + cbn in H. destruct j; discriminate H.
Qed.

Lemma footprint_snoc_map : forall s len f, In f (footprint (set_regions (st_regions s ++ [mkRegion RkMap len [] true]) s)) ->
  In f (footprint s) \/ f = (LMem (SP (length (st_regions s)) 0), len).
Proof.
  intros s len f H. unfold footprint in H |- *. cbn [st_regions set_regions st_areas] in H.
  destruct H as [<-|H]; [left; left; reflexivity|]. apply in_app_iff in H as [H|H]; [left; right; apply in_app_iff; left; exact H|].
  rewrite length_app in H. cbn [length] in H. rewrite Nat.add_1_r in H. rewrite seq_S in H. rewrite flat_map_app in H.
  apply in_app_iff in H as [H|H].
  - left. right. apply in_app_iff. right. apply in_flat_map in H as (k & Hk & Hf). apply in_seq in Hk. apply in_flat_map. exists k.
    split; [apply in_seq; lia|]. unfold region_of in Hf |- *. cbn [st_regions set_regions] in Hf. rewrite nth_error_app1 in Hf by lia. exact Hf.
  - right. cbn [flat_map app] in H. unfold region_of in H. cbn [st_regions set_regions] in H. rewrite nth_error_app2 in H by lia.
    rewrite Nat.add_0_l, Nat.sub_diag in H. cbn in H. destruct H as [<-|[]]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mp_reads : forall m mt a len sc cnt aidx usage ctr, 0 <= sc <= 47 -> 1 <= mt -> mt + 40 <= 2^47 ->
  (mt + 40 <= 0x10000 \/ 0x97000 <= mt) -> 4096 <= a -> a + 9 <= 2^47 -> (a + 9 <= 0x10000 \/ 0x97000 <= a) -> (mt + 40 <= a \/ a + 9 <= mt) ->
  (forall k, (k < 8)%nat -> mp_mem m mt a len sc cnt aidx usage ctr (wa (mt + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa mt)) (Z_to_bv 8 0))) /\
  (forall k, (k < 8)%nat -> mp_mem m mt a len sc cnt aidx usage ctr (wa (mt + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa mt)) (Z_to_bv 8 0))) /\
  (forall k, (k < 8)%nat -> mp_mem m mt a len sc cnt aidx usage ctr (wa (mt + 16 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa a)) (Z_to_bv 8 0))) /\
  (forall k, (k < 4)%nat -> mp_mem m mt a len sc cnt aidx usage ctr (wa (mt + 24 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa (2 ^ (aidx + 1) - 2))) (Z_to_bv 8 0))) /\
  (forall k, (k < 4)%nat -> mp_mem m mt a len sc cnt aidx usage ctr (wa (mt + 28 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa ((2 ^ cnt - 1) - (2 ^ (aidx + 1) - 1)))) (Z_to_bv 8 0))) /\
  (forall k, (k < 8)%nat -> mp_mem m mt a len sc cnt aidx usage ctr (wa (mt + 32 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa (64 * sc + cnt + len + 31))) (Z_to_bv 8 0))) /\
  (forall k, (k < 4)%nat -> mp_mem m mt a len sc cnt aidx usage ctr (wa (614116 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa (ctr + 1))) (Z_to_bv 8 0))) /\
  (forall k, (k < 8)%nat -> mp_mem m mt a len sc cnt aidx usage ctr (wa (8 * sc + 614568 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa (cnt + usage))) (Z_to_bv 8 0))) /\
  (forall k, (k < 8)%nat -> mp_mem m mt a len sc cnt aidx usage ctr (wa (8 * sc + 614184 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa mt)) (Z_to_bv 8 0))) /\
  (forall k, (k < 8)%nat -> mp_mem m mt a len sc cnt aidx usage ctr (wa (a + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa mt)) (Z_to_bv 8 0))) /\
  mp_mem m mt a len sc cnt aidx usage ctr (wa (a + 8)) = Some (nth 0 (word_to_le_bytes 1 (wa aidx)) (Z_to_bv 8 0)).
Proof.
  intros m mt a len sc cnt aidx usage ctr Hsc H1 H2 Dm Ha1 Ha2 Da Dma. unfold mp_mem, mp_ins2, mp_ins1, mp_ai.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  all: try (intros k Hk; rewrite ?MngWb.wbytes_out by (clear - Hk Hsc H1 H2 Dm Ha1 Ha2 Da Dma; side);
            apply MngWb.wbytes_at_wa; [clear - Hsc H1 H2 Ha1 Ha2; lia | side | rewrite length_N_to_le_bytes; exact Hk]).
  rewrite !MngWb.wbytes_out by (clear - Hsc H1 H2 Dm Ha1 Ha2 Da Dma; side). apply MngWb.wbytes_at_wa0; [clear - Ha1; lia | side | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma holds_read : forall L (m : word -> option byte) l w v' v, (forall z, v' <> VLo5 z) -> (1 <= w <= 8)%nat ->
  0 <= loc_addr L l -> loc_addr L l + Z.of_nat w <= 2^64 ->
  v mod 2^(8 * Z.of_nat w) = sval_num L v' mod 2^(8 * Z.of_nat w) ->
  (forall k, (k < w)%nat -> m (wa (loc_addr L l + Z.of_nat k)) = Some (nth k (word_to_le_bytes w (wa v)) (Z_to_bv 8 0))) ->
  cell_holds L (bview SEGS m) (MCell l w v').
Proof.
  intros L m l w v' v Hv Hw H1 H2 Hm HR. apply holds_of_mem; cbn [mc_loc mc_w mc_val]; [exact Hv | lia | exact H1 | exact H2 |].
  intros k Hk. rewrite (le_wa_eqm w (sval_num L v') v) by (first [symmetry; exact Hm | lia]). exact (HR k Hk).
Qed.

Lemma nth_le_zero : forall n k, nth k (Z_to_le_bytes n 0) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  induction n as [|n IH]; intros k; [destruct k; reflexivity|]. cbn [Z_to_le_bytes]. change (Z.shiftr 0 8) with 0.
  destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH.
Qed.

Lemma le4_small : forall v k, 0 <= v < 256 -> (k < 4)%nat ->
  nth k (word_to_le_bytes 4 (wa v)) (Z_to_bv 8 0) = if Nat.eqb k 0 then nth 0 (word_to_le_bytes 1 (wa v)) (Z_to_bv 8 0) else Z_to_bv 8 0.
Proof.
  intros v k Hv Hk. unfold word_to_le_bytes. rewrite u_wa_small by lia.
  assert (E8 : Z.shiftr v 8 = 0) by (rewrite Z.shiftr_div_pow2 by lia; change (2^8) with 256; rewrite Z.div_small by lia; reflexivity).
  destruct k as [|[|[|[|k]]]]; [reflexivity | | | | lia]; cbn [Z_to_le_bytes Nat.eqb nth]; rewrite E8; reflexivity.
Qed.

Lemma ones_sub : forall k, ones k - 1 = 2 ^ (k + 1) - 2.
Proof. intros k. unfold ones. ring. Qed.

Section CUT6.
Variables (HTOP : Z) (FORB : list (Z * Z)) (X : list sptr) (U : Z -> Z) (L : layout) (s3 : astate) (m3 : word -> option byte) (sp0 K : Z).
Variables (mt : sptr) (sc cnt len a : Z).
Hypothesis C : CUT HTOP (mt :: X) None U L s3 m3 sp0 K.
Hypothesis Hsc : 0 <= sc <= 47.
Hypothesis Hcnt : 1 <= cnt <= 32.
Hypothesis Hlen : 4096 <= len <= 2^20.
Hypothesis Hlm : len mod 4096 = 0.
Hypothesis Hfit : 2 <= cnt -> 16 + class_size sc * cnt <= len.
Hypothesis FR : fresh_range FORB HTOP L s3 a (page_round len).
Hypothesis HIMG : ranges_disjoint (a, page_round len) (0x10000, 0x87000).
Hypothesis NX : ~ In mt X.

Local Notation r := (length (st_regions s3)).
Local Notation aidx := (ag_aidx sc cnt).
Local Notation s6 := (ins_st mt sc cnt aidx (len / 4096) (SP r 0) slot_zero (ag_s5 s3 len)).
Local Notation am6 := (am_set_links (Some mt) (Some mt) (new_am (SP r 0) sc cnt aidx (len / 4096) slot_zero)).
Local Notation L' := (set_reg_addr L r a).
Local Notation m1' := (mem_after m3 (mkEffect (w64 a) [] [(w64 a, w64 (page_round len))])).
Local Notation mta := (loc_addr L (LMem mt)).
Local Notation mfin := (mp_mem m1' mta a len sc cnt aidx (usage_of s3 sc) (st_mmap_counter s3)).

Hypothesis HI6 : Inv X (Some (mt, 0)) U s6.

#[using="Hlm"] Lemma prl : page_round len = len.
Proof. LiaFast.lf_pins (fun (Hlm : LiaFast.U) => LiaFast.u0). apply page_round_fixed. exact Hlm. Qed.

#[using="Type"] Lemma L'_new : ly_reg L' r = a.
Proof. LiaFast.lf_pins LiaFast.u0. unfold set_reg_addr. cbn [ly_reg]. rewrite Nat.eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma L'_old : forall k, k <> r -> ly_reg L' k = ly_reg L k.
Proof. LiaFast.lf_pins LiaFast.u0. intros k Hk. unfold set_reg_addr. cbn [ly_reg]. rewrite (proj2 (Nat.eqb_neq k _) Hk). reflexivity. Qed.

#[using="FORB C Hsc Hcnt Hlen Hlm Hfit FR HIMG NX HI6"] Theorem cut_s6 : CUT HTOP X (Some (mt, 0)) U L' s6 mfin sp0 K /\ GROW sp0 K L s3 m3 L' s6 mfin.
Proof. LiaFast.lf_pins (fun (FORB C Hsc Hcnt Hlen Hlm Hfit FR HIMG NX HI6 : LiaFast.U) => LiaFast.u0).
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2.
  pose proof prl as PRL. rewrite PRL in FR, HIMG.
  destruct FR as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (Ha : 4096 <= a) by exact F1. assert (Hal : a mod 4096 = 0) by exact F2.
  assert (Ha47 : a + len <= 2^47) by (clear - F4 HTB; lia).
  assert (Dimg : a + len <= 0x10000 \/ 0x97000 <= a) by (unfold ranges_disjoint in HIMG; cbn [fst snd] in HIMG; clear - HIMG; lia).
  (* [comment removed for export] *)
  assert (Hmt : MT s3 mt = Some MRaw \/ MT s3 mt = Some (MFree None None)) by exact (HX mt (or_introl eq_refl)).
  assert (Hraw : forall am', mlookup (st_metas s3) mt <> Some (MUsed am')).
  { intros am' E. change (mlookup (st_metas s3) mt) with (MT s3 mt) in E. destruct Hmt as [E'|E']; rewrite E' in E; discriminate E. }
  assert (Hkey : In mt (keys s3)) by (destruct Hmt as [E'|E']; exact (MT_keys s3 mt _ E')).
  assert (Hlt : plt r mt) by (destruct Hmt as [E'|E']; exact (MT_lt (mt :: X) None U s3 HI mt _ E')).
  assert (LM : loc_addr L' (LMem mt) = mta) by exact (loc_addr_ext s3 L L' (lext_set_new L s3 a) (LMem mt) Hlt).
  pose proof (nc_mplace _ _ _ _ _ _ _ N mt Hkey) as (Pm1 & Pm2 & Pm3 & Pm4).
  destruct (key_slot_range HTOP (mt :: X) None U s3 L mt HI HG Hkey) as (ar & j & rr & rga & Har & Hj & Ear & Epr & Hrr & Hlv & Hkd & A1 & A2 & A3 & A4).
  assert (Dma : mta + 40 <= a \/ a + len <= mta).
  { pose proof (F7 rr rga Hrr Hlv) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. rewrite A4.
    unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - D A2 A3 Hj. lia. }
  assert (LA : length (st_active s3) = 48%nat) by exact (proj1 (inv_ctx HI)).
  assert (LU : length (st_usage s3) = 48%nat) by exact (proj1 (proj2 (inv_ctx HI))).
  assert (KS6 : KS s6) by exact (KS_of_Inv X (Some (mt, 0)) U s6 HI6).
  assert (Lc : forall o, loc_addr L' (LCtx o) = 614104 + o) by (intros o; unfold set_reg_addr; cbn [loc_addr ly_ctx]; rewrite Hctx; reflexivity).
  assert (LR : loc_addr L' (LMem (SP r 0)) = a) by (cbn [loc_addr prid poff]; rewrite L'_new; ring).
  apply (effect_step HTOP (mt :: X) None U X (Some (mt, 0)) U L L' s3 s6 m3 m1' mfin sp0 K (Cnew6 mt sc cnt aidx (len / 4096) r s3 len) a len C
           (lext_set_new L s3 a)).
  - clear - Ha; lia.
  - clear - Hlen; lia.
  - exact F4.
  - exact Dimg.
  - intros x Hx Hn. rewrite mem_after_zero by (clear - Hx Ha Ha47 Hlen PRL; rewrite ?PRL; lia). rewrite PRL.
    replace ((a <=? x) && (x <? a + len)) with false by (symmetry; apply andb_false_iff; destruct (Z_le_dec a x); [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]).
    reflexivity.
  - exact F6.
  - exists r, (mkRegion RkMap (page_round len) [] true). split.
    { unfold region_of, ins_st, ag_s5. cbn [st_regions set_active set_metas set_usage set_mmap_counter set_regions].
      rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
    split; [reflexivity|]. split; [left; lia|]. rewrite L'_new. cbn [rg_len]. rewrite PRL. clear; lia.
  - exact HI6.
  - (* [comment removed for export] *)
    intros x Hx. unfold MT. rewrite (s6_lookup mt sc cnt aidx (len / 4096) r s3 len x) by (intros E; subst x; exact (NX Hx)).
    exact (HX x (or_intror Hx)).
  - (* [comment removed for export] *)
    intros k rg Hk Hl.
    assert (Hk' : region_of (set_regions (st_regions s3 ++ [mkRegion RkMap (page_round len) [] true]) s3) k = Some rg) by exact Hk.
    destruct (region_of_snoc s3 _ k rg Hk') as [(Hlt' & Ho)|(-> & ->)].
    + rewrite L'_old by lia. exact (HG k rg Ho Hl).
    + rewrite L'_new. cbn [rg_len]. rewrite PRL. unfold PGSZ in *. split; [exact F1|]. split; [exact F2|]. split; [exact F4 | exact HIMG].
  - (* [comment removed for export] *)
    intros k1 k2 rg1 rg2 Hne H1 H2 L1 L2.
    assert (H1' : region_of (set_regions (st_regions s3 ++ [mkRegion RkMap (page_round len) [] true]) s3) k1 = Some rg1) by exact H1.
    assert (H2' : region_of (set_regions (st_regions s3 ++ [mkRegion RkMap (page_round len) [] true]) s3) k2 = Some rg2) by exact H2.
    destruct (region_of_snoc s3 _ k1 rg1 H1') as [(Hl1 & O1)|(-> & ->)]; destruct (region_of_snoc s3 _ k2 rg2 H2') as [(Hl2 & O2)|(-> & ->)].
    + rewrite !L'_old by lia. exact (HD k1 k2 rg1 rg2 Hne O1 O2 L1 L2).
    + rewrite L'_old by lia. rewrite L'_new. cbn [rg_len]. rewrite PRL. apply ranges_disjoint_sym'. exact (F7 k1 rg1 O1 L1).
    + rewrite L'_new. rewrite L'_old by lia. cbn [rg_len]. rewrite PRL. exact (F7 k2 rg2 O2 L2).
    + exfalso. exact (Hne eq_refl).
  - (* [comment removed for export] *)
    split; [unfold ins_st, ag_s5; cbn [st_regions set_active set_metas set_usage set_mmap_counter set_regions]; rewrite length_app; cbn [length]; lia|].
    intros k rg Hk Hl. exists rg. split; [|split; [exact Hl | split; [reflexivity | lia]]].
    unfold region_of, ins_st, ag_s5. cbn [st_regions set_active set_metas set_usage set_mmap_counter set_regions].
    rewrite nth_error_app1 by exact (region_of_lt _ _ _ Hk). exact Hk.
  - (* [comment removed for export] *)
    intros f Hf.
    assert (Hf' : In f (footprint (set_regions (st_regions s3 ++ [mkRegion RkMap (page_round len) [] true]) s3))) by exact Hf.
    destruct (footprint_snoc_map s3 (page_round len) f Hf') as [A|A]; [left; exact A|right]. subst f.
    intros x Hx. cbn [fst snd] in Hx. rewrite LR, PRL in Hx.
    apply (bview_grow_n m1' mfin x (mp_mem_grows _ _ _ _ _ _ _ _ _)).
    rewrite (MngWb.bview_some_byte SEGS m1' x (Z_to_bv 8 0)); [discriminate | clear - Hx Ha Ha47; lia |].
    rewrite mem_after_zero by (clear - Hx Ha Ha47 Hlen PRL; rewrite ?PRL; lia). rewrite PRL.
    replace ((a <=? x) && (x <? a + len)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity.
  - intros c Hc. exact (cov6 mt sc cnt aidx (len / 4096) r s3 len LA LU c Hc).
  - exact (in6 mt sc cnt aidx (len / 4096) r s3 len Hsc LA LU KS6).
  - intros c Hc. exact (rev6 mt sc cnt aidx (len / 4096) r s3 len Hraw L' c Hc).
  - (* [comment removed for export] *)
    pose proof (nc_K _ _ _ _ _ _ _ N) as HK1.
    assert (Rm47 : mta + 40 <= 2^47) by (clear - Pm2 Hsp2 HK1; lia).
    assert (Ra9 : a + 9 <= 2^47) by (clear - Ha47 Hlen; lia).
    assert (Da9 : a + 9 <= 0x10000 \/ 0x97000 <= a) by (clear - Dimg Hlen; lia).
    assert (Dma9 : mta + 40 <= a \/ a + 9 <= mta) by (clear - Dma Hlen; lia).
    destruct (mp_reads m1' mta a len sc cnt aidx (usage_of s3 sc) (st_mmap_counter s3) Hsc Pm1 Rm47 Pm3 Ha Ra9 Da9 Dma9)
      as (R0 & R8 & R16 & R24 & R28 & R32 & RC & RU & RA & RG0 & RG8).
    assert (ZR : forall x, a + 9 <= x < a + len -> mfin (wa x) = Some (Z_to_bv 8 0)).
    { intros x Hx. rewrite mp_mem_out by (clear - Hx Hsc Pm1 Rm47 Pm3 Ha Ra9 Da9 Dma Dimg Ha47 Hlen; lia).
      rewrite mem_after_zero by (clear - Hx Ha Ha47 Hlen PRL; rewrite ?PRL; lia). rewrite PRL.
      replace ((a <=? x) && (x <? a + len)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
    assert (Hml : len / 4096 <> 0) by (assert (1 <= len / 4096) by (apply Z.div_le_lower_bound; lia); lia).
    assert (Hml' : 4096 * (len / 4096) = len) by (pose proof (Z_div_mod_eq_full len 4096); clear - H Hlm; lia).
    pose proof (ag_aidx_range sc cnt ltac:(pose proof (size_classes_range sc ltac:(lia)) as Hun; pose proof (class_units sc) as Ecs; rewrite Ecs; lia) Hcnt) as Hai.
    unfold Cnew6. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_app; split]]].
    + unfold ctr_cell. apply (holds_read L' mfin _ 4 _ (st_mmap_counter s3 + 1)); [intros z E; discriminate E | lia | rewrite Lc; unfold CTX_mmap_counter; lia
                                                                               | rewrite Lc; unfold CTX_mmap_counter; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
      * cbn [sval_num]. rewrite (s6_counter mt sc cnt aidx (len / 4096) r s3 len). change (8 * Z.of_nat 4) with 32.
        change (2^32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity.
      * intros k Hk. rewrite Lc. unfold CTX_mmap_counter. replace (614104 + 12 + Z.of_nat k) with (614116 + Z.of_nat k) by ring. exact (RC k Hk).
    + unfold usg_cell. apply (holds_read L' mfin _ 8 _ (cnt + usage_of s3 sc)); [intros z E; discriminate E | lia | rewrite Lc; unfold CTX_usage; lia
                                                                             | rewrite Lc; unfold CTX_usage; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
      * cbn [sval_num]. rewrite (s6_usage mt sc cnt aidx (len / 4096) r s3 len). unfold zset. rewrite nth_zupd_same by (rewrite LU; lia).
        rewrite Z.add_comm. reflexivity.
      * intros k Hk. rewrite Lc. unfold CTX_usage. rewrite Z2Nat.id by lia. replace (614104 + (464 + 8 * sc) + Z.of_nat k) with (8 * sc + 614568 + Z.of_nat k) by ring.
        exact (RU k Hk).
    + unfold act_cell. apply (holds_read L' mfin _ 8 _ mta); [intros z E; discriminate E | lia | rewrite Lc; unfold CTX_active; lia
                                                           | rewrite Lc; unfold CTX_active; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
      * cbn [sval_num optr]. rewrite LM. reflexivity.
      * intros k Hk. rewrite Lc. unfold CTX_active. rewrite Z2Nat.id by lia. replace (614104 + (80 + 8 * sc) + Z.of_nat k) with (8 * sc + 614184 + Z.of_nat k) by ring.
        exact (RA k Hk).
    + cbn [meta_slot_cells am_prev am_next am_mem am_avail am_freed am_last am_sc am_maplen am_aidx am_set_links new_am optr].
      assert (LP : forall d, loc_addr L' (LMem (padd mt d)) = mta + d) by (intros d; rewrite loc_padd, LM; reflexivity).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]].
      * apply (holds_read L' mfin _ 8 _ mta); [intros z E; discriminate E | lia | rewrite LP; unfold META_prev; lia | rewrite LP; unfold META_prev; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        { cbn [sval_num]. rewrite LM. reflexivity. }
        { intros k Hk. rewrite LP. unfold META_prev. exact (R0 k Hk). }
      * apply (holds_read L' mfin _ 8 _ mta); [intros z E; discriminate E | lia | rewrite LP; unfold META_next; lia | rewrite LP; unfold META_next; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        { cbn [sval_num]. rewrite LM. reflexivity. }
        { intros k Hk. rewrite LP. unfold META_next. exact (R8 k Hk). }
      * apply (holds_read L' mfin _ 8 _ a); [intros z E; discriminate E | lia | rewrite LP; unfold META_mem; lia | rewrite LP; unfold META_mem; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        { cbn [sval_num]. rewrite LR. reflexivity. }
        { intros k Hk. rewrite LP. unfold META_mem. exact (R16 k Hk). }
      * apply (holds_read L' mfin _ 4 _ (2 ^ (aidx + 1) - 2)); [intros z E; discriminate E | lia | rewrite LP; unfold META_avail; lia | rewrite LP; unfold META_avail; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        { cbn [sval_num]. rewrite ones_sub. reflexivity. }
        { intros k Hk. rewrite LP. unfold META_avail. exact (R24 k Hk). }
      * apply (holds_read L' mfin _ 4 _ ((2 ^ cnt - 1) - (2 ^ (aidx + 1) - 1))); [intros z E; discriminate E | lia | rewrite LP; unfold META_freed; lia
                                                                                | rewrite LP; unfold META_freed; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        { cbn [sval_num]. unfold ones. replace (cnt - 1 + 1) with cnt by ring. reflexivity. }
        { intros k Hk. rewrite LP. unfold META_freed. exact (R28 k Hk). }
      * apply (holds_read L' mfin _ 8 _ (64 * sc + cnt + len + 31)); [intros z E; discriminate E | lia | rewrite LP; unfold META_bits; lia
                                                                      | rewrite LP; unfold META_bits; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        { cbn [sval_num]. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links new_am]. rewrite Hml'. f_equal. ring. }
        { intros k Hk. rewrite LP. unfold META_bits. exact (R32 k Hk). }
    + unfold group_cells. replace (am_maplen am6 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hml).
      cbn [am_mem am_maplen am_aidx am_last am_set_links new_am].
      apply Forall_cons; [|apply Forall_cons; [|]].
      * apply (holds_read L' mfin _ 8 _ mta); [intros z E; discriminate E | lia | rewrite LR; lia | rewrite LR; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        { cbn [sval_num]. rewrite LM. reflexivity. }
        { intros k Hk. rewrite LR. replace (a + Z.of_nat k) with (a + 0 + Z.of_nat k) by ring. exact (RG0 k Hk). }
      * apply (holds_read L' mfin _ 4 _ aidx); [intros z E; discriminate E | lia | rewrite loc_padd, LR; lia | rewrite loc_padd, LR; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
        intros k Hk. rewrite loc_padd, LR. rewrite le4_small by (first [lia | exact Hk]).
        destruct (Nat.eqb k 0) eqn:Ek.
        { apply Nat.eqb_eq in Ek. subst k. rewrite Z.add_0_r. exact RG8. }
        { apply Nat.eqb_neq in Ek. apply ZR. first [(clear - Hk Ek Hlen; lia) | (clear - Hk Ek Hlen Ra9; lia) | lia]. }
      * apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (i & Hi & Hc). apply In_zseq in Hi.
        assert (Hsl : nth_slot am6 i = slot_zero).
        { unfold nth_slot. cbn [am_slots am_set_links new_am]. rewrite nth_repeat'. destruct (Nat.ltb (Z.to_nat i) (Z.to_nat cnt)) eqn:E; [reflexivity|].
          apply Nat.ltb_ge in E. lia. }
        assert (Hst : 0 <= stride_of am6 * i /\ 16 + stride_of am6 * i <= len).
        { unfold stride_of. cbn [am_last am_sc am_maplen am_set_links new_am].
          pose proof (size_classes_range sc ltac:(clear - Hsc; lia)) as Hun. pose proof (class_units sc) as Ecs.
          destruct (Z.eq_dec cnt 1) as [E1|E1].
          - assert (i = 0) by (clear - E1 Hi; lia). subst i. rewrite Z.mul_0_r. clear - Hlen. lia.
          - replace (cnt - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; clear - E1 Hcnt; lia). cbn [andb].
            specialize (Hfit ltac:(clear - E1 Hcnt; lia)). rewrite Ecs in *. clear - Hfit Hi Hun Hcnt E1. nia. }
        unfold slot_cells in Hc. rewrite Hsl in Hc. cbn [ss_hdr ss_fr slot_zero app In] in Hc.
        assert (LS : forall d, loc_addr L' (LMem (padd (slot_start am6 i) d)) = a + 16 + stride_of am6 * i + d).
        { intros d. rewrite loc_padd. unfold slot_start. rewrite loc_padd. cbn [am_mem am_set_links new_am]. rewrite LR. unfold UNIT. ring. }
        assert (ZR' : forall x, a + 9 <= x < a + 9 + (len - 9) -> mfin (wa x) = Some (Z_to_bv 8 0)) by (intros x Hx; apply ZR; clear - Hx; lia).
        assert (B1 : 0 <= a + 9) by (clear - Ha; lia). assert (B2 : a + 9 + (len - 9) <= 2^64) by (clear - Ha47; lia).
        clear - Hc LS ZR' B1 B2 Hst.
        destruct Hc as [<-|[<-|[<-|[]]]];
          (apply (zero_cell_holds_r L' mfin _ (a + 9) (len - 9) ZR' B1 B2); [cbn [mc_loc]; rewrite LS; lia | cbn [mc_loc mc_w]; rewrite LS; cbn [Z.of_nat Pos.of_succ_nat]; lia
                                                                | cbn [mc_w]; lia | intros z E; discriminate E | reflexivity]).
  - apply mp_mem_grows.
  - (* [comment removed for export] *)
    intros x Hx Hne. right.
    assert (LP : forall d, loc_addr L' (LMem (padd mt d)) = mta + d) by (intros d; rewrite loc_padd, LM; reflexivity).
    assert (INM : forall c, In c (meta_slot_cells mt (Some (MUsed am6))) -> In c (Cnew6 mt sc cnt aidx (len / 4096) r s3 len)).
    { intros c Hc. unfold Cnew6. apply in_app_iff. right. apply in_app_iff. left. exact Hc. }
    assert (ING : forall c, In c (group_cells mt am6) -> In c (Cnew6 mt sc cnt aidx (len / 4096) r s3 len)).
    { intros c Hc. unfold Cnew6. apply in_app_iff. right. apply in_app_iff. right. exact Hc. }
    assert (Hml : len / 4096 <> 0) by (assert (1 <= len / 4096) by (apply Z.div_le_lower_bound; lia); lia).
    destruct (range_dec x mta 40) as [M|M].
    { destruct (range_dec x mta 8) as [M1|M1].
      { exists (MCell (LMem (padd mt META_prev)) 8 (optr (am_prev am6))). split; [apply INM; cbn [meta_slot_cells In]; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_prev. cbn [Z.of_nat Pos.of_succ_nat]. clear - M1; lia. }
      destruct (range_dec x (mta + 8) 8) as [M2|M2].
      { exists (MCell (LMem (padd mt META_next)) 8 (optr (am_next am6))). split; [apply INM; cbn [meta_slot_cells In]; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_next. cbn [Z.of_nat Pos.of_succ_nat]. clear - M2; lia. }
      destruct (range_dec x (mta + 16) 8) as [M3|M3].
      { exists (MCell (LMem (padd mt META_mem)) 8 (VP (am_mem am6))). split; [apply INM; cbn [meta_slot_cells In]; right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_mem. cbn [Z.of_nat Pos.of_succ_nat]. clear - M3; lia. }
      destruct (range_dec x (mta + 24) 4) as [M4|M4].
      { exists (MCell (LMem (padd mt META_avail)) 4 (VZ (am_avail am6))). split; [apply INM; cbn [meta_slot_cells In]; right; right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_avail. cbn [Z.of_nat Pos.of_succ_nat]. clear - M4; lia. }
      destruct (range_dec x (mta + 28) 4) as [M5|M5].
      { exists (MCell (LMem (padd mt META_freed)) 4 (VZ (am_freed am6))). split; [apply INM; cbn [meta_slot_cells In]; right; right; right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_freed. cbn [Z.of_nat Pos.of_succ_nat]. clear - M5; lia. }
      exists (MCell (LMem (padd mt META_bits)) 8 (VZ (meta_bits am6))). split; [apply INM; cbn [meta_slot_cells In]; right; right; right; right; right; left; reflexivity|].
      unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_bits. cbn [Z.of_nat Pos.of_succ_nat]. clear - M M1 M2 M3 M4 M5; lia. }
    destruct (range_dec x 614116 4) as [C1|C1].
    { exists (ctr_cell (st_mmap_counter s6)). split; [unfold Cnew6; left; reflexivity|].
      unfold in_rng, cell_range, ctr_cell. cbn [mc_loc mc_w fst snd]. rewrite Lc. unfold CTX_mmap_counter. cbn [Z.of_nat Pos.of_succ_nat]. clear - C1; lia. }
    destruct (range_dec x (8 * sc + 614568) 8) as [C2|C2].
    { exists (usg_cell (Z.to_nat sc) (nth (Z.to_nat sc) (st_usage s6) 0)). split; [unfold Cnew6; right; left; reflexivity|].
      unfold in_rng, cell_range, usg_cell. cbn [mc_loc mc_w fst snd]. rewrite Lc. unfold CTX_usage. rewrite Z2Nat.id by lia. cbn [Z.of_nat Pos.of_succ_nat]. clear - C2; lia. }
    destruct (range_dec x (8 * sc + 614184) 8) as [C3|C3].
    { exists (act_cell (Z.to_nat sc) (Some mt)). split; [unfold Cnew6; right; right; left; reflexivity|].
      unfold in_rng, cell_range, act_cell. cbn [mc_loc mc_w fst snd]. rewrite Lc. unfold CTX_active. rewrite Z2Nat.id by lia. cbn [Z.of_nat Pos.of_succ_nat]. clear - C3; lia. }
    destruct (range_dec x a 8) as [G1|G1].
    { exists (MCell (LMem (am_mem am6)) 8 (VP mt)). split; [apply ING; unfold group_cells; left; reflexivity|].
      unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd am_mem am_set_links new_am]. rewrite LR. cbn [Z.of_nat Pos.of_succ_nat]. clear - G1; lia. }
    destruct (range_dec x (a + 8) 1) as [G2|G2].
    { exists (MCell (LMem (padd (am_mem am6) 8)) 4 (VZ (am_aidx am6))). split.
      - apply ING. unfold group_cells. replace (am_maplen am6 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hml). right. left. reflexivity.
      - unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd am_mem am_set_links new_am]. rewrite loc_padd, LR. cbn [Z.of_nat Pos.of_succ_nat]. clear - G2; lia. }
    pose proof (nc_K _ _ _ _ _ _ _ N) as HK1.
    exfalso. apply Hne. apply mp_mem_out; clear - Hx M C1 C2 C3 G1 G2 Hsc Pm1 Pm2 Hsp2 HK1 Ha Ha47 Hlen; lia.
Qed.
End CUT6.
