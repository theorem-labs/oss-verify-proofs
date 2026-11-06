(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits AxMalloc MngZ MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngExc MngNtfPre MngNtfC MngWb MngNtfM MngNtfS
                        MngGM AXF_mb0z AXG_ntfm AXG_ntfg AXG_nQ AXG_nD AXG_tam AXG_as1 AXG_as2 AXG_as4 AxTry.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_actbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_actbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_actbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_actbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_tkz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_tkz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bnc_cell (k : nat) (v : Z) : mcell := MCell (LCtx (CTX_bounces + Z.of_nat k)) 1 (VZ v).

Lemma cov_bounces : forall s k v c, (k < length (st_bounces s))%nat ->
  In c (image (set_bounces (zupd (st_bounces s) k v) s)) -> In c (image s) \/ c = bnc_cell k v.
Proof.
  intros s k v c Hk Hc. destruct (cov_ctx_only s (set_bounces (zupd (st_bounces s) k v) s) c eq_refl eq_refl Hc) as [H|H]; [left; exact H|].
  unfold ctx_cells in H. cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage
      st_unmap_seq st_bounces set_bounces] in H.
  apply in_app_iff in H as [H|H]; [left; apply ctx_in_image; unfold ctx_cells; apply in_app_iff; left; exact H|].
  apply in_app_iff in H as [H|H]; [left; apply ctx_in_image; unfold ctx_cells; apply in_app_iff; right; apply in_app_iff; left; exact H|].
  apply in_app_iff in H as [H|H]; [left; apply ctx_in_image; unfold ctx_cells; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact H|].
  apply in_app_iff in H as [H|H]; [left; apply ctx_in_image; unfold ctx_cells; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact H|].
  apply in_map_iff in H as (k' & <- & Hk'). destruct (Nat.eq_dec k' k) as [->|Hne].
  - right. unfold bnc_cell. rewrite nth_zupd_same by exact Hk. reflexivity.
  - left. apply ctx_in_image. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
    rewrite nth_zupd_other by exact Hne.
    apply (in_map (fun k0 => MCell (LCtx (CTX_bounces + Z.of_nat k0)) 1 (VZ (nth k0 (st_bounces s) 0)))). exact Hk'.
Qed.

Lemma bnc_cell_in : forall s k, (k < 32)%nat -> In (bnc_cell k (nth k (st_bounces s) 0)) (image s).
Proof. intros s k Hk. apply ctx_in_image. exact (bounce_in_ctx s k Hk). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fin_meta (am3 : ameta) : ameta :=
  am_set_avail (ta_mask am3 - lowbit (ta_mask am3)) (am_set_freed (Z.ldiff (am_freed am3) (ones (am_aidx am3))) am3).

Lemma s_fin_norm : forall s m3 am3, s_fin s m3 am3 = set_meta (s_decay s (am_sc am3)) m3 (MUsed (fin_meta am3)).
Proof.
  intros s m3 am3. unfold s_fin, s_decay, fin_meta, act_meta, ta_mask. destruct (bounce_idx (am_sc am3)) as [k|].
  - cbn [st_bounces set_meta set_metas]. destruct (znth k (st_bounces s) =? 0).
    + unfold set_meta. cbn. rewrite mupdate_twice''. reflexivity.
    + unfold set_meta, set_bounces. cbn. rewrite mupdate_twice''. reflexivity.
  - unfold set_meta. cbn. rewrite mupdate_twice''. reflexivity.
Qed.

Lemma KS_decay : forall s sc, KS s -> KS (s_decay s sc).
Proof. intros s sc H. unfold s_decay. destruct (bounce_idx sc); [destruct (_ =? 0)|]; exact H. Qed.
Lemma keys_decay : forall s sc, keys (s_decay s sc) = keys s.
Proof. intros s sc. unfold s_decay. destruct (bounce_idx sc); [destruct (_ =? 0)|]; reflexivity. Qed.
Lemma RS_decay : forall L s sc, RS L (s_decay s sc) s.
Proof. intros L s sc. unfold s_decay. destruct (bounce_idx sc); [destruct (_ =? 0)|]; try apply RS_refl. apply RS_ctx_only; reflexivity. Qed.
Lemma areas_decay : forall s sc, st_areas (s_decay s sc) = st_areas s.
Proof. intros s sc. unfold s_decay. destruct (bounce_idx sc); [destruct (_ =? 0)|]; reflexivity. Qed.
Lemma regions_decay : forall s sc, st_regions (s_decay s sc) = st_regions s.
Proof. intros s sc. unfold s_decay. destruct (bounce_idx sc); [destruct (_ =? 0)|]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma cov_decay : forall s sc c, length (st_bounces s) = 32%nat -> In c (image (s_decay s sc)) ->
  In c (image s) \/ exists k, bounce_idx sc = Some k /\ znth k (st_bounces s) <> 0 /\ c = bnc_cell (Z.to_nat k) (znth k (st_bounces s) - 1).
Proof.
  intros s sc c Hl Hc. unfold s_decay in Hc. destruct (bounce_idx sc) as [k|] eqn:Eb; [|left; exact Hc].
  destruct (znth k (st_bounces s) =? 0) eqn:Ez; [left; exact Hc|].
  assert (Rk : 0 <= k < 32) by (unfold bounce_idx in Eb; destruct ((7 <=? sc) && (sc <? 39)) eqn:E; [|discriminate];
    injection Eb as <-; apply andb_prop in E as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2; lia).
  unfold zset in Hc. destruct (cov_bounces s (Z.to_nat k) _ c ltac:(rewrite Hl; lia) Hc) as [H|H]; [left; exact H|].
  right. exists k. split; [reflexivity|]. split; [apply Z.eqb_neq; exact Ez | exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FINNC.
Context {fx : FPState}.

#[using="Type"] Lemma fin_nc : forall L s m m' sp0 K m3 am3,
  NC L [] [] s m sp0 K -> MT s m3 = Some (MUsed am3) -> length (st_bounces s) = 32%nat -> 0 <= am_freed am3 <= 2^32-1 ->
  (forall k, (k < 4)%nat -> m' (wa (loc_addr L (LMem m3) + 24 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa (ta_mask am3 - lowbit (ta_mask am3)))) (Z_to_bv 8 0))) ->
  (forall k, (k < 4)%nat -> m' (wa (loc_addr L (LMem m3) + 28 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa (Z.ldiff (am_freed am3) (ones (am_aidx am3))))) (Z_to_bv 8 0))) ->
  (forall j, bounce_idx (am_sc am3) = Some j -> znth j (st_bounces s) <> 0 ->
     m' (wa (614984 + j)) = Some (nth 0 (word_to_le_bytes 1 (wa (znth j (st_bounces s) - 1))) (Z_to_bv 8 0))) ->
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (loc_addr L (LMem m3) + 24 <= x < loc_addr L (LMem m3) + 32) \/
     exists j, bounce_idx (am_sc am3) = Some j /\ znth j (st_bounces s) <> 0 /\ x = 614984 + j) ->
  mem_grows m m' ->
  NC L [] [] (s_fin s m3 am3) m' sp0 K /\ RS L (s_fin s m3 am3) s /\ FRM L s sp0 K m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m m' sp0 K m3 am3 N M3 Hbl Rfr MAV MFN MBN CHG Hgrow.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  assert (K3 : In m3 (keys s)) by (eapply MT_keys; exact M3).
  set (G3 := loc_addr L (LMem m3)) in *.
  destruct (HMP m3 K3) as (G1 & G2 & G3' & G4). fold G3 in G1, G2, G3', G4.
  set (S4 := s_decay s (am_sc am3)).
  assert (HKS4 : KS S4) by (apply KS_decay; exact HK).
  assert (M4 : MT S4 m3 = Some (MUsed am3)) by (unfold S4; rewrite MT_decay; exact M3).
  assert (K4 : keys S4 = keys s) by apply keys_decay.
  assert (Es' : s_fin s m3 am3 = set_meta S4 m3 (MUsed (fin_meta am3))) by apply s_fin_norm.
  set (s' := s_fin s m3 am3) in *.
  assert (HKs' : KS s') by (rewrite Es'; apply KS_set_meta; [exact HKS4 | rewrite K4; exact K3]).
  assert (Ks' : keys s' = keys s) by (rewrite Es', keys_set_meta by (rewrite K4; exact K3); exact K4).
  assert (Ms' : MT s' m3 = Some (MUsed (fin_meta am3))) by (rewrite Es'; apply MT_set_same).
  assert (HRS : RS L s' s).
  { rewrite Es'. apply (RS_trans L s S4); [|apply RS_decay].
    apply (RS_set_used L S4 m3 am3 _ HKS4 M4). unfold fin_meta. rewrite gc_avail, gc_freed. reflexivity. }
  set (AV := ta_mask am3 - lowbit (ta_mask am3)). set (FN := Z.ldiff (am_freed am3) (ones (am_aidx am3))).
  set (CAV := MCell (LMem (padd m3 META_avail)) 4 (VZ AV)).
  set (CFN := MCell (LMem (padd m3 META_freed)) 4 (VZ FN)).
  set (CB := fun j => bnc_cell (Z.to_nat j) (znth j (st_bounces s) - 1)).
  set (Cnew := [CAV; CFN] ++ match bounce_idx (am_sc am3) with
                             | Some j => if znth j (st_bounces s) =? 0 then [] else [CB j]
                             | None => [] end).
  assert (HGr : 1 <= G3 /\ G3 + 40 <= 2^47) by (clear - G1 G2 Hsp2 HK1; lia).
  assert (Rbj : forall j, bounce_idx (am_sc am3) = Some j -> 0 <= j < 32).
  { intros j Eb. unfold bounce_idx in Eb. destruct ((7 <=? am_sc am3) && (am_sc am3 <? 39)) eqn:E; [|discriminate].
    injection Eb as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia. }
  assert (Hs'b : forall j, bounce_idx (am_sc am3) = Some j -> znth j (st_bounces s) <> 0 ->
            nth (Z.to_nat j) (st_bounces s') 0 = znth j (st_bounces s) - 1).
  { intros j Eb Ez. rewrite Es'. cbn [st_bounces set_meta set_metas]. unfold S4, s_decay. rewrite Eb.
    replace (znth j (st_bounces s) =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ez).
    cbn [st_bounces set_bounces]. unfold zset. apply nth_zupd_same. rewrite Hbl. pose proof (Rbj j Eb). lia. }
  assert (ECB : forall j, bounce_idx (am_sc am3) = Some j -> loc_addr L (mc_loc (CB j)) = 614984 + j).
  { intros j Eb. pose proof (Rbj j Eb). unfold CB, bnc_cell. cbn [mc_loc loc_addr]. rewrite Hctx. unfold CTX_bounces. rewrite Z2Nat.id by lia. ring. }
  assert (HNew : Forall (cell_holds L (bview SEGS m')) Cnew).
  { unfold Cnew. apply Forall_app. split.
    - repeat (first [apply Forall_nil | apply Forall_cons]); apply holds_of_mem.
      all: try (intros z E; discriminate).
      all: try (cbn [mc_w]; clear; lia).
      all: cbn [mc_loc mc_w mc_val sval_num CAV CFN] in *; rewrite ?loc_padd; unfold META_avail, META_freed; fold G3.
      all: try (clear - HGr; lia).
      + exact MAV.
      + exact MFN.
    - destruct (bounce_idx (am_sc am3)) as [j|] eqn:Eb; [|constructor].
      destruct (znth j (st_bounces s) =? 0) eqn:Ez; [constructor|]. apply Z.eqb_neq in Ez.
      constructor; [|constructor]. apply holds_of_mem.
      + intros z E. discriminate.
      + cbn. lia.
      + rewrite (ECB j eq_refl). pose proof (Rbj j eq_refl). lia.
      + rewrite (ECB j eq_refl). pose proof (Rbj j eq_refl). cbn. lia.
      + intros n Hn. rewrite (ECB j eq_refl). assert (n = 0%nat) as -> by (cbn in Hn; lia). rewrite Z.add_0_r.
        cbn [CB bnc_cell mc_w mc_val sval_num]. exact (MBN j eq_refl Ez). }
  assert (REPR : repr_x L s' (bview SEGS m') []).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') [] Cnew HR); [| |exact HRS | exact (fun a E => bview_grow_n m m' a Hgrow E) | | | exact HNew |].
    - rewrite Es'. cbn [st_areas set_meta set_metas]. apply areas_decay.
    - rewrite Es'. cbn [st_regions set_meta set_metas]. apply regions_decay.
    - intros c Hc. rewrite Es' in Hc. unfold fin_meta in Hc.
      destruct (cov_avail_freed S4 m3 am3 AV FN c HKS4 M4 Hc) as [Hc1|[E|E]].
      + destruct (cov_decay s (am_sc am3) c Hbl Hc1) as [Hc2|(j & Eb & Ez & E)]; [left; exact Hc2|].
        right. unfold Cnew. rewrite Eb. replace (znth j (st_bounces s) =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ez).
        apply in_app_iff. right. left. rewrite E. reflexivity.
      + right. unfold Cnew. apply in_app_iff. left. left. symmetry. exact E.
      + right. unfold Cnew. apply in_app_iff. left. right. left. symmetry. exact E.
    - intros c Hc. unfold Cnew in Hc. apply in_app_iff in Hc as [Hc|Hc].
      + destruct Hc as [<-|[<-|[]]].
        * apply (In_image_used s' m3 _ _ HKs' Ms'). left. cbn [meta_slot_cells In]. unfold fin_meta. cbn [am_set_avail am_set_freed am_avail]. memb.
        * apply (In_image_used s' m3 _ _ HKs' Ms'). left. cbn [meta_slot_cells In]. unfold fin_meta. cbn [am_set_avail am_set_freed am_freed]. memb.
      + destruct (bounce_idx (am_sc am3)) as [j|] eqn:Eb; [|destruct Hc].
        destruct (znth j (st_bounces s) =? 0) eqn:Ez; [destruct Hc|]. apply Z.eqb_neq in Ez.
        destruct Hc as [<-|[]]. pose proof (Rbj j eq_refl) as Rj.
        pose proof (bnc_cell_in s' (Z.to_nat j) ltac:(lia)) as E. rewrite (Hs'b j eq_refl Ez) in E. exact E.
    - intros a Ha. left. pose proof (bview_ne_range m m' a Ha) as Ra.
      assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
      destruct (CHG a Ra Ha') as [A|(j & Eb & Ez & ->)].
      + destruct (Z_lt_le_dec a (G3 + 28)) as [B|B].
        * exists CAV. split; [unfold Cnew; apply in_app_iff; left; left; reflexivity|]. unfold CAV. cellr. fold G3. clear - A B; lia.
        * exists CFN. split; [unfold Cnew; apply in_app_iff; left; right; left; reflexivity|]. unfold CFN. cellr. fold G3. clear - A B; lia.
      + exists (CB j). split.
        * unfold Cnew. rewrite Eb. replace (znth j (st_bounces s) =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ez).
          apply in_app_iff. right. left. reflexivity.
        * unfold in_rng, cell_range. rewrite (ECB j Eb). cbn [CB bnc_cell mc_w fst snd Z.of_nat Pos.of_succ_nat]. lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. destruct (CHG x Hx Hne) as [A|(j & Eb & Ez & ->)].
    - destruct (Z_lt_le_dec x (G3 + 28)) as [B|B].
      + exists (MCell (LMem (padd m3 META_avail)) 4 (VZ (am_avail am3))). split; [apply (In_image_used s m3 am3 _ HK M3); left; cbn [meta_slot_cells In]; memb|].
        split; [wide_tac Hctx|]. cellr. fold G3. clear - A B; lia.
      + exists (MCell (LMem (padd m3 META_freed)) 4 (VZ (am_freed am3))). split; [apply (In_image_used s m3 am3 _ HK M3); left; cbn [meta_slot_cells In]; memb|].
        split; [wide_tac Hctx|]. cellr. fold G3. clear - A B; lia.
    - pose proof (Rbj j Eb) as Rj. exists (bnc_cell (Z.to_nat j) (nth (Z.to_nat j) (st_bounces s) 0)). split; [exact (bnc_cell_in s (Z.to_nat j) ltac:(lia))|].
      split; [unfold bnc_cell; wide_tac Hctx|]. unfold in_rng, cell_range, bnc_cell. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat loc_addr].
      rewrite Hctx. unfold CTX_bounces. rewrite Z2Nat.id by lia. lia. }
  split; [exact (NC_next L [] [] s s' m m' sp0 K N REPR HRS HKs' ltac:(intros x []) Hgrow FR Ks')|].
  split; [exact HRS | exact FR].
Qed.

End FINNC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma act_mask_cond : forall f h, 0 <= f < 2^32 -> 0 <= h ->
  (Z.land (ext_Z true 0 4 f mod 2^64) (bv_swrap 32 (bv_swrap 32 (Z.shiftl 2 (h mod 32)) + -1) mod 2^64) mod 2^64 =? 0)
  = (Z.land f (2^(Z.land h 31 + 1) - 1) =? 0).
Proof.
  intros f h Hf Hh. rewrite Z.land_comm. pose proof (m2_cond f h Hf Hh) as E. change (0 mod 2^64) with 0 in E. exact E.
Qed.

Lemma lrsc_cond : forall f, (bv_swrap 32 (ext_Z true 0 4 f + 0) mod 2^64 =? ext_Z true 0 4 f mod 2^64) = true.
Proof.
  intros f. apply Z.eqb_eq. rewrite Z.add_0_r, ext4_swrap. f_equal. apply swrap32_eqm. apply swrap32_mod.
Qed.

Lemma bnc_cond : forall sc3, 0 <= sc3 <= 63 -> (31 <? (sc3 + -7) mod 2^64) = match bounce_idx sc3 with Some _ => false | None => true end.
Proof.
  intros sc3 H. unfold bounce_idx.
  destruct (Z_lt_le_dec sc3 7) as [A|A].
  - replace ((7 <=? sc3) && (sc3 <? 39)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
    replace ((sc3 + -7) mod 2^64) with (sc3 + -7 + 1 * 2^64) by (rewrite <- (Z_mod_plus_full (sc3 + -7) 1); symmetry; apply Z.mod_small; lia).
    apply Z.ltb_lt. lia.
  - destruct (Z_lt_le_dec sc3 39) as [B|B].
    + replace ((7 <=? sc3) && (sc3 <? 39)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
    + replace ((7 <=? sc3) && (sc3 <? 39)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia).
      rewrite Z.mod_small by lia. apply Z.ltb_lt. lia.
Qed.

Lemma scw_mod32 : forall W, SCW (W mod 2^32) = SCW W.
Proof.
  intros W. unfold SCW. f_equal. rewrite (Z_div_mod_eq_full W (2^32)) at 2.
  replace (4503599627370496 * (2 ^ 32 * (W / 2 ^ 32) + W mod 2 ^ 32)) with (4503599627370496 * (W mod 2^32) + (2^20 * (W / 2^32)) * 2^64) by ring.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma keeps22 : forall (R R' : bvmap 5 word) m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9,
  as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  (forall k, In k [2;8;18;20;21;23]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
  getr R' 22 = wa 614096 ->
  forall k, In k [2;8;18;20;21;22;23]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k)).
Proof.
  intros R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F K Q22 k Hk.
  destruct (Nat.eq_dec k 22) as [->|Hne]; [|apply K; clear - Hk Hne; cbn [In] in *; intuition lia].
  destruct F as [_ _ _ _ _ R22 _]. litr2 Q22. symmetry. litr2 R22. reflexivity.
Qed.

Section ACT.
Context {fx : FPState}.

Ltac actscs Z35 Z36 Z37 Z38 :=
  repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z35, ?Z36, ?Z37, ?Z38;
  rewrite ?br_eq_z, ?br_ne_z, ?br_ltu_z; litmods.

(* [comment removed for export] *)
#[using="Type"] Lemma act_run : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m3 am3,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 10 = wa (loc_addr L (LMem m3)) -> MT s m3 = Some (MUsed am3) -> ta_mask am3 <> 0 ->
  0 <= am_freed am3 <= 2^32-1 -> 0 <= am_aidx am3 <= 31 -> 0 <= am_last am3 <= 31 -> 0 <= am_sc am3 < 64 -> 0 <= am_maplen am3 ->
  length (st_bounces s) = 32%nat -> (forall u, In u (st_bounces s) -> 0 <= u <= 255) ->
  exists R1 m1, msteps SEGS (mkst R (wa 0x52418) m rom) (mkst R1 (wa 0x52490) m1 rom) /\
    getr R1 10 = wa (loc_addr L (LMem m3)) /\ getr R1 11 = wa (ext_Z true 0 4 (ta_mask am3)) /\
    as_frame R1 m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    (forall k, (k < 4)%nat -> m1 (wa (loc_addr L (LMem m3) + 28 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa (Z.ldiff (am_freed am3) (ones (am_aidx am3))))) (Z_to_bv 8 0))) /\
    (forall j, bounce_idx (am_sc am3) = Some j -> znth j (st_bounces s) <> 0 ->
       m1 (wa (614984 + j)) = Some (nth 0 (word_to_le_bytes 1 (wa (znth j (st_bounces s) - 1))) (Z_to_bv 8 0))) /\
    (forall x, 0 <= x < 2^64 -> m1 (wa x) <> m (wa x) -> (loc_addr L (LMem m3) + 24 <= x < loc_addr L (LMem m3) + 32) \/
       exists j, bounce_idx (am_sc am3) = Some j /\ znth j (st_bounces s) <> 0 /\ x = 614984 + j) /\
    mem_grows m m1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m3 am3 N F R10 M3 Hmask Rfr Rai Rl Rs Rm Hbl Hbr.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (K3 : In m3 (keys s)) by (eapply MT_keys; exact M3).
  set (G3 := loc_addr L (LMem m3)) in *.
  destruct (HMP m3 K3) as (G1 & G2 & G3' & G4). fold G3 in G1, G2, G3', G4.
  destruct (rx_aidx L s m [] m3 am3 HR HEO HK M3 Rai) as (hb & Rhb & Mhb & Ehb).
  set (MEM := loc_addr L (LMem (am_mem am3))) in *.
  assert (RMEM : 1 <= MEM <= 2^63-1).
  { set (CH := MCell (LMem (am_mem am3)) 8 (VP m3)).
    assert (CHi : In CH (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; apply (group_in_gpart s m3 am3 CH M3 (proj1 HK)); left; reflexivity).
    pose proof (HC CH CHi) as (P1 & P2 & _). unfold CH in P1, P2. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in P1, P2. fold MEM in P1, P2.
    clear - P1 P2 Hsp2 HK1. lia. }
  set (W3 := meta_bits am3 mod 2^32).
  assert (RW3 : 0 <= W3 <= 2^32-1) by (unfold W3; pose proof (Z.mod_pos_bound (meta_bits am3) (2^32) ltac:(lia)); lia).
  assert (MW3 : rdn SEGS m (wa (G3 + 32)) 4 = Some (word_to_le_bytes 4 (wa W3))) by (apply rdn_lo4; exact (rx_bits L s m [] HR HEO HK m3 am3 M3)).
  assert (SW3 : SCW W3 = am_sc am3) by (unfold W3; rewrite scw_mod32; apply mb_scw; lia).
  assert (Espan : 2 ^ (Z.land hb 31 + 1) - 1 = ones (am_aidx am3)) by (unfold ones; rewrite Ehb; reflexivity).
  set (FN := Z.ldiff (am_freed am3) (ones (am_aidx am3))). set (MASK := ta_mask am3).
  assert (EMASK : Z.land (am_freed am3) (2 ^ (Z.land hb 31 + 1) - 1) = MASK) by (rewrite Espan; reflexivity).
  assert (EFN : Z.ldiff (am_freed am3) (2 ^ (Z.land hb 31 + 1) - 1) = FN) by (rewrite Espan; reflexivity).
  assert (Rmask : Z.land (am_freed am3) (ones (am_aidx am3)) <> 0) by exact Hmask.
  assert (WR : forall d n, 0 <= d -> d + Z.of_nat n <= 8 -> store_ok SEGS m (wa (G3 + 24 + d)) n = true).
  { intros d n Hd Hn. replace (G3 + 24 + d) with (G3 + (24 + d)) by ring. apply (rx_msc_wr L s m [] HR HEO HK m3 _ M3); lia. }
  assert (HGr : 1 <= G3 /\ G3 + 40 <= 2^47) by (clear - G1 G2 Hsp2 HK1; lia).
  pose proof F as [R2 R8 R18 R20 R21 R22 R23 Rsp Asp Rsc' Rreq Rcan Rra Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Rs8 Rs9 Mra Ms0 Ms1 Ms2 Ms3 Ms4 Ms5 Ms6 Ms7 Ms8 Ms9 Mcan Mgd].
  assert (FRAME : forall (R1 : bvmap 5 word), getr R1 22 = wa 614096 ->
            (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
            as_frame R1 m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\
            (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k)))).
  { intros R1 Q22 Qk. split.
    - apply (as_frame_move R R1 m m); [exact F | | intros; reflexivity | intros; reflexivity].
      apply (keeps22 R R1 m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F); [|exact Q22].
      intros k Hk. apply Qk. clear - Hk. cbn [In] in *. tauto.
    - intros k Hk. apply Qk. clear - Hk. cbn [In] in *. tauto. }
  destruct (bounce_idx (am_sc am3)) as [j|] eqn:Eb.
  2:{ (* [comment removed for export] *)
    assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_actbz.AXF_actz.act_pre R m sc G3 MEM hb (am_freed am3) W3).
    { constructor; try assumption; try (clear - Rsc'; lia); try (clear - HGr; lia); try (clear - RMEM; lia); try (clear - Rhb; lia); try (clear - Rfr; lia).
      exact (rx_mem L s m [] HR HEO HK m3 am3 M3). exact (rx_freed L s m [] HR HEO HK m3 am3 M3). }
    destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_actbz.AXF_actz.act_pact R m rom sc G3 MEM hb (am_freed am3) W3 P) as (R1 & Hms & Q10 & Q11 & Q22 & Qk).
    { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_actbz.AXF_act.RES_pact fst snd]. set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_actbz.AXF_actz.VALS_act sc G3 MEM hb (am_freed am3) W3)).
      assert (Z35 : bv_unsigned (ev E 35) = hb) by (apply zatom; [reflexivity | reflexivity | clear - Rhb; lia]).
      assert (Z36 : bv_unsigned (ev E 36) = am_freed am3) by (apply zatom; [reflexivity | reflexivity | clear - Rfr; lia]).
      assert (Z37 : bv_unsigned (ev E 37) = W3) by (apply zatom; [reflexivity | reflexivity | clear - RW3; lia]).
      actscs Z35 Z36 Z37 Z37. all: rewrite ?(Z.mod_small (am_freed am3)), ?(Z.mod_small hb), ?(Z.mod_small W3) by (clear - Rfr Rhb RW3; lia).
      all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w); rewrite ?scw_ext32 by (clear - RW3; lia).
      - rewrite SW3, bnc_cond by lia. rewrite Eb. reflexivity.
      - rewrite act_mask_cond by (clear - Rfr Rhb; lia). rewrite EMASK. apply negb_true_iff. apply Z.eqb_neq. exact Hmask.
      - rewrite lrsc_cond. reflexivity. }
    change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_actbz.AXF_actz.act_mem_pact m R sc G3 MEM hb (am_freed am3) W3) with
      (wbytes (wbytes m (wa (G3 + 28)) (word_to_le_bytes 4 (wa (Z.ldiff (am_freed am3) (2 ^ (Z.land hb 31 + 1) - 1))))) (wa (G3 + 24))
         (word_to_le_bytes 4 (wa (Z.land (am_freed am3) (2 ^ (Z.land hb 31 + 1) - 1))))) in Hms.
    rewrite EMASK, EFN in Hms. rewrite EMASK in Q11.
    destruct (FRAME R1 Q22 Qk) as (F1 & K1).
    eexists R1, _. split; [exact Hms|]. split; [exact Q10|]. split; [exact Q11|]. split; [exact F1|]. split; [exact K1|]. split.
    { intros k Hk. peel. apply wbytes_at_wa; cbn [length word_to_le_bytes Z_to_le_bytes]; lia. }
    split; [intros j' E; discriminate|]. split.
    { intros x Hx Hne. left. destruct (Z_lt_le_dec x (G3 + 24)) as [A|A]; [exfalso; apply Hne; do 2 peel; reflexivity|].
      destruct (Z_lt_le_dec x (G3 + 32)) as [B|B]; [lia|]. exfalso; apply Hne; do 2 peel; reflexivity. }
    wgrow. }
  (* [comment removed for export] *)
  assert (Rj : 0 <= j < 32).
  { unfold bounce_idx in Eb. destruct ((7 <=? am_sc am3) && (am_sc am3 <? 39)) eqn:E; [|discriminate].
    injection Eb as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia. }
  assert (Ej : am_sc am3 = j + 7).
  { unfold bounce_idx in Eb. destruct ((7 <=? am_sc am3) && (am_sc am3 <? 39)) eqn:E; [|discriminate]. injection Eb as <-. ring. }
  set (bnc := znth j (st_bounces s)).
  assert (Rbnc : 0 <= bnc <= 255).
  { apply Hbr. unfold bnc, znth. apply nth_In. rewrite Hbl. lia. }
  assert (MB : rdn SEGS m (wa (SCW W3 + 614977)) 1 = Some (word_to_le_bytes 1 (wa bnc))).
  { rewrite SW3, Ej. pose proof (rx_bounce L s m [] HR HEO Hctx (Z.to_nat j) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
    replace (j + 7 + 614977) with (614984 + j) by ring. exact E. }
  assert (WB : forall d n, 0 <= d -> d + Z.of_nat n <= 1 -> store_ok SEGS m (wa (SCW W3 + 614977 + d)) n = true).
  { intros d n Hd Hn. rewrite SW3, Ej. replace (j + 7 + 614977 + d) with (614104 + (880 + j + d)) by ring.
    apply (rx_ctx_wr L s m [] HR Hctx); lia. }
  assert (P : AXF_actbz.actb_pre R m sc G3 MEM hb (am_freed am3) W3 bnc).
  { constructor; try assumption; try (clear - Rsc'; lia); try (clear - HGr; lia); try (clear - RMEM; lia); try (clear - Rhb; lia); try (clear - Rfr; lia); try (clear - Rbnc; lia).
    - exact (rx_mem L s m [] HR HEO HK m3 am3 M3).
    - exact (rx_freed L s m [] HR HEO HK m3 am3 M3).
    - rewrite SW3. clear - Rs. lia.
    - rewrite SW3, Ej. clear - Rj G3' HGr. lia. }
  destruct (Z.eq_dec bnc 0) as [Bz|Bnz].
  - destruct (AXF_actbz.actb_pactz R m rom sc G3 MEM hb (am_freed am3) W3 bnc P) as (R1 & Hms & Q10 & Q11 & Q22 & Qk).
    { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_actbz.AXF_actb.RES_pactz fst snd]. set (E := Ez R (AXF_actbz.VALS_actb sc G3 MEM hb (am_freed am3) W3 bnc)).
      assert (Z35 : bv_unsigned (ev E 35) = hb) by (apply zatom; [reflexivity | reflexivity | clear - Rhb; lia]).
      assert (Z36 : bv_unsigned (ev E 36) = am_freed am3) by (apply zatom; [reflexivity | reflexivity | clear - Rfr; lia]).
      assert (Z37 : bv_unsigned (ev E 37) = W3) by (apply zatom; [reflexivity | reflexivity | clear - RW3; lia]).
      assert (Z38 : bv_unsigned (ev E 38) = bnc) by (apply zatom; [reflexivity | reflexivity | clear - Rbnc; lia]).
      actscs Z35 Z36 Z37 Z38. all: rewrite ?(Z.mod_small (am_freed am3)), ?(Z.mod_small hb), ?(Z.mod_small W3), ?(Z.mod_small bnc) by (clear - Rfr Rhb RW3 Rbnc; lia).
      all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w); rewrite ?scw_ext32 by (clear - RW3; lia).
      - rewrite Bz. reflexivity.
      - rewrite SW3, bnc_cond by lia. rewrite Eb. reflexivity.
      - rewrite act_mask_cond by (clear - Rfr Rhb; lia). rewrite EMASK. apply negb_true_iff. apply Z.eqb_neq. exact Hmask.
      - rewrite lrsc_cond. reflexivity. }
    change (AXF_actbz.actb_mem_pactz m R sc G3 MEM hb (am_freed am3) W3 bnc) with
      (wbytes (wbytes m (wa (G3 + 28)) (word_to_le_bytes 4 (wa (Z.ldiff (am_freed am3) (2 ^ (Z.land hb 31 + 1) - 1))))) (wa (G3 + 24))
         (word_to_le_bytes 4 (wa (Z.land (am_freed am3) (2 ^ (Z.land hb 31 + 1) - 1))))) in Hms.
    rewrite EMASK, EFN in Hms. rewrite EMASK in Q11.
    destruct (FRAME R1 Q22 Qk) as (F1 & K1).
    eexists R1, _. split; [exact Hms|]. split; [exact Q10|]. split; [exact Q11|]. split; [exact F1|]. split; [exact K1|]. split.
    { intros k Hk. peel. apply wbytes_at_wa; cbn [length word_to_le_bytes Z_to_le_bytes]; lia. }
    split; [intros j' E Hz; injection E as <-; exfalso; exact (Hz Bz)|]. split.
    { intros x Hx Hne. left. destruct (Z_lt_le_dec x (G3 + 24)) as [A|A]; [exfalso; apply Hne; do 2 peel; reflexivity|].
      destruct (Z_lt_le_dec x (G3 + 32)) as [B|B]; [lia|]. exfalso; apply Hne; do 2 peel; reflexivity. }
    wgrow.
  - destruct (AXF_actbz.actb_pactd R m rom sc G3 MEM hb (am_freed am3) W3 bnc P) as (R1 & Hms & Q10 & Q11 & Q22 & Qk).
    { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_actbz.AXF_actb.RES_pactd fst snd]. set (E := Ez R (AXF_actbz.VALS_actb sc G3 MEM hb (am_freed am3) W3 bnc)).
      assert (Z35 : bv_unsigned (ev E 35) = hb) by (apply zatom; [reflexivity | reflexivity | clear - Rhb; lia]).
      assert (Z36 : bv_unsigned (ev E 36) = am_freed am3) by (apply zatom; [reflexivity | reflexivity | clear - Rfr; lia]).
      assert (Z37 : bv_unsigned (ev E 37) = W3) by (apply zatom; [reflexivity | reflexivity | clear - RW3; lia]).
      assert (Z38 : bv_unsigned (ev E 38) = bnc) by (apply zatom; [reflexivity | reflexivity | clear - Rbnc; lia]).
      actscs Z35 Z36 Z37 Z38. all: rewrite ?(Z.mod_small (am_freed am3)), ?(Z.mod_small hb), ?(Z.mod_small W3), ?(Z.mod_small bnc) by (clear - Rfr Rhb RW3 Rbnc; lia).
      all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w); rewrite ?scw_ext32 by (clear - RW3; lia).
      - apply Z.eqb_neq. exact Bnz.
      - rewrite SW3, bnc_cond by lia. rewrite Eb. reflexivity.
      - rewrite act_mask_cond by (clear - Rfr Rhb; lia). rewrite EMASK. apply negb_true_iff. apply Z.eqb_neq. exact Hmask.
      - rewrite lrsc_cond. reflexivity. }
    change (AXF_actbz.actb_mem_pactd m R sc G3 MEM hb (am_freed am3) W3 bnc) with
      (wbytes (wbytes (wbytes m (wa (G3 + 28)) (word_to_le_bytes 4 (wa (Z.ldiff (am_freed am3) (2 ^ (Z.land hb 31 + 1) - 1))))) (wa (G3 + 24))
         (word_to_le_bytes 4 (wa (Z.land (am_freed am3) (2 ^ (Z.land hb 31 + 1) - 1))))) (wa (SCW W3 + 614977)) (word_to_le_bytes 1 (wa (bnc + -1)))) in Hms.
    rewrite EMASK, EFN, SW3, Ej in Hms. rewrite EMASK in Q11.
    replace (j + 7 + 614977) with (614984 + j) in Hms by ring.
    destruct (FRAME R1 Q22 Qk) as (F1 & K1).
    eexists R1, _. split; [exact Hms|]. split; [exact Q10|]. split; [exact Q11|]. split; [exact F1|]. split; [exact K1|]. split.
    { intros k Hk. do 2 peel. apply wbytes_at_wa; cbn [length word_to_le_bytes Z_to_le_bytes]; lia. }
    split.
    { intros j' E Hz. injection E as <-. replace (znth j (st_bounces s) - 1) with (bnc + -1) by (unfold bnc; ring).
      apply wbytes_at_wa0; cbn [length word_to_le_bytes Z_to_le_bytes]; lia. }
    split.
    { intros x Hx Hne. destruct (Z.eq_dec x (614984 + j)) as [->|Hx1]; [right; exists j; split; [reflexivity|]; split; [exact Bnz | reflexivity]|].
      left. destruct (Z_lt_le_dec x (G3 + 24)) as [A|A]; [exfalso; apply Hne; do 3 peel; reflexivity|].
      destruct (Z_lt_le_dec x (G3 + 32)) as [B|B]; [lia|]. exfalso; apply Hne; do 3 peel; reflexivity. }
    wgrow.
Qed.

(* [comment removed for export] *)
Definition DBT (m : word -> option byte) : Prop :=
  forall j, 0 <= j < 32 -> rdn SEGS m (wa (90368 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn))).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem seg_fin : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m3 am3,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 10 = wa (loc_addr L (LMem m3)) -> MT s m3 = Some (MUsed am3) -> am_avail am3 = 0 -> ta_mask am3 <> 0 ->
  0 <= am_freed am3 <= 2^32-1 -> 0 <= am_aidx am3 <= 31 -> 0 <= am_last am3 <= 31 -> 0 <= am_sc am3 < 64 -> 0 <= am_maplen am3 ->
  length (st_bounces s) = 32%nat -> (forall u, In u (st_bounces s) -> 0 <= u <= 255) -> DBT m ->
  exists R' m', msteps SEGS (mkst R (wa 0x52418) m rom) (mkst R' (wa 0x52b50) m' rom) /\
    ta_fin m3 s = IRet (lowbit (ta_mask am3), s_fin s m3 am3) /\ NC L [] [] (s_fin s m3 am3) m' sp0 K /\
    as_frame R' m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\ RS L (s_fin s m3 am3) s /\
    mem_grows m m' /\ FRM L s sp0 K m m' /\ getr R' 10 = wa (ctz32 (ta_mask am3)) /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\ DBT m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m3 am3 N F R10 M3 Hav Hmask Rfr Rai Rl Rs Rm Hbl Hbr Mdb.
  destruct (act_run L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m3 am3 N F R10 M3 Hmask Rfr Rai Rl Rs Rm Hbl Hbr)
    as (R1 & m1 & Hms1 & Q10 & Q11 & F1 & K1 & MFN1 & MBN1 & CHG1 & G1).
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (K3 : In m3 (keys s)) by (eapply MT_keys; exact M3).
  set (G3 := loc_addr L (LMem m3)) in *.
  destruct (HMP m3 K3) as (Ga & Gb & Gc & Gd). fold G3 in Ga, Gb, Gc, Gd.
  set (MASK := ta_mask am3) in *.
  assert (RMASK : 1 <= MASK <= 2^32-1).
  { assert (A1 : Z.land (am_freed am3) (ones (am_aidx am3)) <= am_freed am3) by (apply land_le_l; [lia | unfold ones; pose proof (Z.pow_pos_nonneg 2 (am_aidx am3 + 1) ltac:(lia) ltac:(lia)); lia]).
    assert (A2 : 0 <= Z.land (am_freed am3) (ones (am_aidx am3))) by (apply Z.land_nonneg; lia). unfold MASK, ta_mask in *. lia. }
  destruct (lowbit_pow MASK ltac:(lia)) as (LP & Rj).
  (* [comment removed for export] *)
  assert (OUT1 : forall x, 0 <= x < 2^64 -> ~ (G3 + 24 <= x < G3 + 32) -> ~ (614984 <= x < 615016) -> m1 (wa x) = m (wa x)).
  { intros x Hx H1 H2. destruct (decide (m1 (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
    destruct (CHG1 x Hx E) as [A|(j & Eb & Ez & ->)]; [exact (H1 A)|].
    apply H2. unfold bounce_idx in Eb. destruct ((7 <=? am_sc am3) && (am_sc am3 <? 39)) eqn:Ec; [|discriminate].
    injection Eb as <-. apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia. }
  assert (Mdb1 : DBT m1).
  { intros j Hj. rewrite (rdn_frame_n m m1); [exact (Mdb j Hj) | lia | cbn; lia | intros x Hx; apply OUT1; [lia | clear - Hx Gc Ga Hj; cbn in Hx; lia | clear - Hx Hj; cbn in Hx; lia]]. }
  assert (P2 : AXF_tkz.tk_pre R1 m1 G3 MASK (ctz32 MASK)).
  { constructor; try assumption.
    all: try (clear - Ga Gb Hsp2 HK1; lia). all: try (clear - RMASK; lia). all: try (clear - Rj; lia).
    all: try (rewrite db_mach_ok by lia; pose proof (db_table_ok (ctz32 MASK) Rj) as (D1 & _); exact D1).
    all: try (rewrite db_mach_ok by lia; pose proof (db_table_ok (ctz32 MASK) Rj) as (D1 & D2); rewrite Z.add_comm, Mdb1 by lia; rewrite D2; reflexivity).
    all: try (intros d k Hd Hk; apply (store_ok_mono SEGS k m m1 _ G1); replace (G3 + 24 + d) with (G3 + (24 + d)) by ring;
              apply (rx_msc_wr L s m [] HR HEO HK m3 _ M3); lia).
    all: rewrite db_mach_ok by lia; pose proof (db_table_ok (ctz32 MASK) Rj) as (D1 & _); clear - D1 Gc Ga; lia. }
  destruct (AXF_tkz.tk_arm R1 m1 rom G3 MASK (ctz32 MASK) P2) as (R2 & Hms2 & B10 & K2).
  set (m2 := mb0_mem m1 G3 MASK).
  assert (OUT2 : forall x, 0 <= x < 2^64 -> ~ (G3 + 24 <= x < G3 + 28) -> m2 (wa x) = m1 (wa x)).
  { intros x Hx Hn. unfold m2, mb0_mem. rewrite MngWb.wbytes_out by side. reflexivity. }
  assert (G2 : mem_grows m m2) by (apply (mem_grows_trans _ _ _ G1); unfold m2, mb0_mem; apply wbytes_grows).
  assert (HGr : 1 <= G3 /\ G3 + 40 <= 2^47) by (clear - Ga Gb Hsp2 HK1; lia).
  destruct (fin_nc L s m m2 sp0 K m3 am3 N M3 Hbl Rfr) as (N' & HRS & FR).
  { intros k Hk. unfold m2, mb0_mem. apply wbytes_at_wa; cbn [length word_to_le_bytes Z_to_le_bytes]; lia. }
  { intros k Hk. rewrite OUT2 by (cbn [Z.of_nat] in *; lia). exact (MFN1 k Hk). }
  { intros j Eb Ez. rewrite OUT2; [exact (MBN1 j Eb Ez) | | ].
    - unfold bounce_idx in Eb. destruct ((7 <=? am_sc am3) && (am_sc am3 <? 39)) eqn:Ec; [|discriminate].
      injection Eb as <-. apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
    - unfold bounce_idx in Eb. destruct ((7 <=? am_sc am3) && (am_sc am3 <? 39)) eqn:Ec; [|discriminate].
      injection Eb as <-. apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. clear - Gc Ga E1 E2. lia. }
  { intros x Hx Hne. destruct (decide (m1 (wa x) = m (wa x))) as [E|E].
    - left. destruct (decide (G3 + 24 <= x < G3 + 28)) as [A|A]; [lia|]. exfalso. apply Hne. rewrite OUT2 by assumption. exact E.
    - exact (CHG1 x Hx E). }
  { exact G2. }
  exists R2, m2. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|].
  split; [exact (ta_fin_eq s m3 am3 M3 Hav Hmask)|]. split; [exact N'|]. split.
  { apply (as_frame_move R1 R2 m m2); [exact F1 | | |].
    - intros k Hk. apply K2. clear - Hk. cbn [In] in *. tauto.
    - intros x Hx. rewrite OUT2 by (clear - Hx Ga Gb Hsp1 Hsp2 HK1; lia). apply OUT1; clear - Hx Ga Gb Hsp1 Hsp2 HK1; lia.
    - intros x Hx. rewrite OUT2 by (clear - Hx Ga Gc; lia). apply OUT1; clear - Hx Ga Gc; lia. }
  split; [exact HRS|]. split; [exact G2|]. split; [exact FR|]. split; [exact B10|]. split.
  - intros k Hk. rewrite (K2 k ltac:(clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])). apply K1. exact Hk.
  - intros j Hj. rewrite (rdn_frame_n m1 m2); [exact (Mdb1 j Hj) | lia | cbn; lia | intros x Hx; apply OUT2; [lia | clear - Hx Gc Ga Hj; cbn in Hx; lia]].
Qed.

End ACT.
