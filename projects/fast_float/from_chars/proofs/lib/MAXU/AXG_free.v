(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngImage MngHeap MngWb MngSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngFree MngPost MngMeta AXF_ff3 AXG_ffpost AXG_ffstep.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngFreeProA.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_p4z AXF_tfz MngFreeMem.

Module AXG_tf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngImage MngHeap MngWb MngSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngFree MngPost MngMeta AXF_ff3 AXG_ffpost AXG_ffstep.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngFreeProA.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_p4z AXF_tfz MngFreeMem.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFree OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngPost OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMeta OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ffpost OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ffstep OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeProA.MngFreeGeo OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_tfz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeMem.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma cell_in_footprint : forall L s c x, WF s -> layout_ok L s -> In c (image s) -> in_rng (cell_range L c) x -> in_footprint L s x.
Proof.
  intros L s c x HW HL Hc Hx. destruct (image_in_footprint s L c HW HL Hc) as (rg & Hrg & Hincl). exists rg. split; [exact Hrg|].
  unfold range_incl, cell_range, crange, in_rng in *. cbn [fst snd] in *. lia.
Qed.

Lemma free_cells_fp : forall L s g am i fr x, WF s -> layout_ok L s -> In (g, am, i, fr) (frames s) ->
  (loc_addr L (LMem (frame_ptr am i fr)) - 3 <= x < loc_addr L (LMem (frame_ptr am i fr))) \/
  (loc_addr L (LMem g) + 28 <= x < loc_addr L (LMem g) + 32) -> in_footprint L s x.
Proof.
  intros L s g am i fr x HW HL HF Hx.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (_ & Ch3 & Ch16 & _ & _ & _ & Cfr & _).
  destruct Hx as [Hx|Hx].
  - destruct (Z.eq_dec x (loc_addr L (LMem (frame_ptr am i fr)) - 3)) as [->|Hne].
    + apply (cell_in_footprint L s _ _ HW HL Ch3). unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. lia.
    + apply (cell_in_footprint L s _ _ HW HL Ch16). unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. lia.
  - apply (cell_in_footprint L s _ _ HW HL Cfr). unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. unfold META_freed. lia.
Qed.

Section Step.
Context {fx : FPState}.

#[using="Type"] Theorem free_fast_step2 : forall L s (regs : bvmap 5 word) m rom g am i fr,
  Heap0 L s m ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser -> am_maplen am = 0 -> rsv_code am fr < 5 ->
  am_freed am <> 0 -> Z.lor (am_freed am) (am_avail am) + bit i <> ones (am_last am) ->
  ly_ctx L = 0x97c98 ->
  getr regs 10 = wa (loc_addr L (LMem (frame_ptr am i fr))) ->
  rdn SEGS m (wa 621603) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) ->
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 1024 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 1024) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x89000)) ->
  exists R m', msteps SEGS (mkst regs (wa 0x52f88) m rom) (mkst R (wa 0x53574) m' rom)
     /\ callee_same R regs
     /\ free (Some (frame_ptr am i fr)) s = IRet (tt, s_fast s g am i fr)
     /\ Heap0 L (s_fast s g am i fr) m'
     /\ (forall x, 0 <= x < 2^64 -> ~ (bv_unsigned (getr regs 2) - 1024 <= x < bv_unsigned (getr regs 2)) -> ~ in_footprint L s x ->
           m' (wa x) = m (wa x)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s regs m rom g am i fr (HW & HR & HM) HF Hk Hml Hrc Hf0 Hnall Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP.
  pose proof (free_pre_of_model L s regs m g am i fr HW HR HM HF Hk Hml Hrc Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP) as FP.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hland & _ & _).
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  apply (used_metas_usedX s g am HW) in Hu as Hux.
  destruct (p4_arm regs m rom _ _ _ _ _ _ _ _ _ FP) as (R1 & Hms1 & PRO).
  pose proof (p4_tail_pre regs R1 m _ _ _ _ _ _ _ _ _ FP PRO) as TP.
  pose proof (fp_Rsp _ _ _ _ _ _ _ _ _ _ _ FP) as Rsp'.
  pose proof (fp_D5 _ _ _ _ _ _ _ _ _ _ _ FP) as D5. pose proof (fp_RG _ _ _ _ _ _ _ _ _ _ _ FP) as RG.
  assert (Rsc : 0 <= am_last am <= 31 /\ 0 <= am_sc am < 48).
  { pose proof (inv_groups HW g am Hux) as (Gm & _). destruct Gm as (Mlast & _).
    pose proof (fp_RW _ _ _ _ _ _ _ _ _ _ _ FP) as RW. unfold meta_bits in *. rewrite Hml in *. clear - Mlast RW; lia. }
  assert (EW : Z.land (meta_bits am) 31 = am_last am).
  { unfold meta_bits. rewrite Hml. replace (am_last am + 32 + 64 * am_sc am + 4096 * 0) with (am_last am + 32 * (1 + 2 * am_sc am)) by ring.
    apply land31; clear - Rsc; lia. }
  set (pa := loc_addr L (LMem (frame_ptr am i fr))) in *. set (G := loc_addr L (LMem g)) in *.
  destruct (tf_arm R1 (p4_mem m regs) rom G (meta_bits am) (Z.land (hdr_byte3 am i fr) 31) _ (am_avail am) (am_freed am) _ _ _ _ _ _ TP)
    as (R2 & Hms2 & TPOST).
  - exact (fp_Rav _ _ _ _ _ _ _ _ _ _ _ FP).
  - exact (fp_Rfr _ _ _ _ _ _ _ _ _ _ _ FP).
  - rewrite p4_rdn_other by (first [exact Rsp | clear - D5 RG; lia]). exact (fp_Mav _ _ _ _ _ _ _ _ _ _ _ FP).
  - rewrite p4_rdn_other by (first [exact Rsp | clear - D5 RG; lia]). exact (fp_Mfr _ _ _ _ _ _ _ _ _ _ _ FP).
  - rewrite p4_rdn_other by (first [exact Rsp | clear - Rsp; lia]). exact Hnl.
  - intros d k Hd Hk2. apply (store_ok_mono SEGS k m); [apply p4_mem_grows|].
    replace (G + 28 + d) with (G + 24 + (4 + d)) by ring. apply (fp_Wmeta _ _ _ _ _ _ _ _ _ _ _ FP); clear - Hd Hk2; lia.
  - exact (fp_A2 _ _ _ _ _ _ _ _ _ _ _ FP).
  - exact (fp_A3 _ _ _ _ _ _ _ _ _ _ _ FP).
  - exact Hf0.
  - rewrite Hland, EW, Z.lor_comm. unfold bit, ones in Hnall. exact Hnall.
  - pose proof (fp_HP _ _ _ _ _ _ _ _ _ _ _ FP) as HP'.
    pose proof HR as (HL & HC & HFM).
    destruct (free_cells_geom L s g am i fr (bv_unsigned (getr regs 2)) HW HL HF HFP) as (Gp & GG1 & GG2 & HpG).
    assert (EP : pa = 16 * hdr_off16 am i fr + loc_addr L (LMem (am_mem am)) + 16).
    { rewrite HP in HP'. pose proof (f_equal bv_unsigned HP') as E. rewrite !u_wa in E.
      pose proof (fp_RPB _ _ _ _ _ _ _ _ _ _ _ FP) as R1'.
      rewrite (Z.mod_small pa) in E by (clear - Gp Rsp; lia).
      rewrite Z.mod_small in E by (clear - R1'; lia). exact E. }
    rewrite <- EP, Hland in Hms2.
    set (m' := tf_mem (p4_mem m regs) pa G (am_freed am + 2 ^ i)) in *.
    exists R2, m'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split.
    { destruct TPOST as (T1 & T8 & T9 & T18 & T19 & T2 & Toth). destruct PRO as (_ & _ & _ & _ & _ & Poth).
      intros n Hn. cbn [In] in Hn.
      destruct Hn as [<-|[<-|Hn]].
      { match type of T1 with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat 1)) with r by (apply bv_eq; reflexivity) end. rewrite T1, wa_u. reflexivity. }
      { match type of T2 with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat 2)) with r by (apply bv_eq; reflexivity) end. rewrite T2, wa_u. reflexivity. }
      destruct Hn as [<-|[<-|Hn]]; [rewrite (Toth 3%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])); exact (Poth 3%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ]))
                                   | rewrite (Toth 4%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])); exact (Poth 4%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ]))|].
      destruct Hn as [<-|[<-|[<-|[<-|Hn]]]].
      { match type of T8 with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat 8)) with r by (apply bv_eq; reflexivity) end. rewrite T8, wa_u. reflexivity. }
      { match type of T9 with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat 9)) with r by (apply bv_eq; reflexivity) end. rewrite T9, wa_u. reflexivity. }
      { match type of T18 with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat 18)) with r by (apply bv_eq; reflexivity) end. rewrite T18, wa_u. reflexivity. }
      { match type of T19 with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat 19)) with r by (apply bv_eq; reflexivity) end. rewrite T19, wa_u. reflexivity. }
      assert (Hn' : In n [3;4;20;21;22;23;24;25;26;27]%nat) by (clear - Hn; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ]).
      rewrite (Toth n Hn'). apply Poth. clear - Hn'; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ]. }
    pose proof (free_fast_itree s g am i fr HW HF Hf0 Hnall) as Hit.
    split; [exact Hit|].
    assert (MO : forall x, 0 <= x < 2^64 -> ~ (bv_unsigned (getr regs 2) - 1024 <= x < bv_unsigned (getr regs 2)) -> ~ (pa - 3 <= x < pa) ->
                   ~ (G + 28 <= x < G + 32) -> m' (wa x) = m (wa x)).
    { intros x Hx H1 H2 H3. unfold m'. rewrite tf_mem_out; try assumption; try (clear - Gp Rsp; lia); try (clear - GG1 GG2 Rsp; lia).
      apply p4_mem_out; [exact Rsp | exact Hx | clear - H1; lia]. }
    assert (BV : forall x, ~ (bv_unsigned (getr regs 2) - 1024 <= x < bv_unsigned (getr regs 2)) -> ~ (pa - 3 <= x < pa) ->
                   ~ (G + 28 <= x < G + 32) -> bview SEGS m' x = bview SEGS m x).
    { intros x H1 H2 H3. destruct (Z_lt_le_dec x 0) as [Hn|Hn].
      { unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; exact Hn). reflexivity. }
      destruct (Z_lt_le_dec x (2^64)) as [Hx|Hx].
      2:{ unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; exact Hx). reflexivity. }
      apply bview_ext. apply MO; try assumption. split; assumption. }
    assert (WR3 : bview SEGS m' (pa - 3) = Some 255).
    { rewrite (bview_some_byte SEGS m' (pa - 3) (Z_to_bv 8 255) ltac:(clear - Gp Rsp; lia)); [reflexivity|]. unfold m'.
      apply tf_mem_p3; first [exact HpG | clear - Gp Rsp; lia | clear - GG1 GG2 Rsp; lia]. }
    assert (WR2 : forall k, (k < 2)%nat -> bview SEGS m' (pa - 2 + Z.of_nat k) = Some 0).
    { intros k Hk2. rewrite (bview_some_byte SEGS m' (pa - 2 + Z.of_nat k) (Z_to_bv 8 0) ltac:(clear - Gp Rsp Hk2; lia)); [reflexivity|]. unfold m'.
      apply tf_mem_p2; first [exact HpG | exact Hk2 | clear - Gp Rsp; lia | clear - GG1 GG2 Rsp; lia]. }
    assert (WRF : forall k, (k < 4)%nat -> bview SEGS m' (G + 28 + Z.of_nat k) = Some (le_byte (am_freed am + bit i) 4 k)).
    { intros k Hk2. rewrite (bview_some_byte SEGS m' (G + 28 + Z.of_nat k) (nth k (word_to_le_bytes 4 (wa (am_freed am + 2 ^ i))) (Z_to_bv 8 0)) ltac:(clear - GG1 GG2 Rsp Hk2; lia)).
      - f_equal. rewrite le_byte_Z_to_le_bytes by (clear - Hk2; lia). unfold bit. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
        unfold le_byte. rewrite Z.mod_mod by (clear; lia). reflexivity.
      - unfold m'. apply tf_mem_G28; first [exact Hk2 | clear - Gp Rsp; lia | clear - GG1 GG2 Rsp; lia]. }
    split; [split; [|split]|].
    + destruct (in_frames_inv s g am i fr HF) as (Hu' & Hi' & Hfri').
      assert (Hb : In (frame_ptr am i fr, fr_n fr) (user_blocks s)).
      { unfold user_blocks. apply in_flat_map. exists (g, am). split; [exact Hu'|]. cbn [snd]. apply in_flat_map.
        exists i. split; [apply In_zseq; lia|]. rewrite Hfri', Hk. left. reflexivity. }
      apply (free_wf s (frame_ptr am i fr) (fr_n fr) [] (s_fast s g am i fr) HW Hb). rewrite Hit. reflexivity.
    + exact (freed_slot_repr SEGS L s m m' g am i fr _ HW HR HF HFP BV WR3 WR2 WRF).
    + exact (freed_slot_markers SEGS L s m m' g am i fr _ HW HR HM HF Hk HFP BV).
    + intros x Hx H1 H2. apply MO; try assumption.
      * intros H3. apply H2. apply (free_cells_fp L s g am i fr x HW HL HF). left. exact H3.
      * intros H3. apply H2. apply (free_cells_fp L s g am i fr x HW HL HF). right. exact H3.
Qed.
End Step.
End AXG_tf.

From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngFreeProA.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngFreeProA.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngFreeProA.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFree OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngPost OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMeta OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ffpost OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ffstep OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeProA.MngFreeGeo OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_tfz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeMem OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_free.AXG_tf OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeProA.MngFreePro OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeProA.MngFreeM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeProA.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Ltac wgrow := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.

Section Free.
Context {fx : FPState}.

#[using="Type"] Theorem free_fast_step : forall L s (regs : bvmap 5 word) m rom g am i fr,
  Heap0 L s m ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser ->
  am_freed am <> 0 -> Z.lor (am_freed am) (am_avail am) + bit i <> ones (am_last am) ->
  ly_ctx L = 0x97c98 ->
  getr regs 10 = wa (loc_addr L (LMem (frame_ptr am i fr))) ->
  rdn SEGS m (wa 621603) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) ->
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 1024 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 1024) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x89000)) ->
  exists R m', msteps SEGS (mkst regs (wa 0x52f88) m rom) (mkst R (wa 0x53574) m' rom)
     /\ callee_same R regs
     /\ free (Some (frame_ptr am i fr)) s = IRet (tt, s_fast s g am i fr)
     /\ Heap0 L (s_fast s g am i fr) m'
     /\ (forall x, 0 <= x < 2^64 -> ~ (bv_unsigned (getr regs 2) - 1024 <= x < bv_unsigned (getr regs 2)) -> (forall c, In c (image s) -> ~ in_rng (cell_range L c) x) ->
           m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s regs m rom g am i fr (HW & HR & HM) HF Hk Hf0 Hnall Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP.
  destruct (free_prologue_any L s regs m rom g am i fr (conj HW (conj HR HM)) HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP) as (R1 & Hms1 & PRO & TP & FC).
  pose proof FC as [Rav Rfr RG RW D5 Mav Mfr MW Wmeta A2 A3].
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hland & _ & _).
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  apply (used_metas_usedX s g am HW) in Hu as Hux.
  destruct (frame_shape s g am i fr HW HF) as (Rl0 & Rs0 & Rm0 & _ & _ & _).
  assert (Rsc : 0 <= am_last am <= 31 /\ 0 <= am_sc am <= 63) by (split; assumption).
  destruct (meta_bits_fields am Rl0 Rs0 Rm0) as (EW & _ & _).
  set (pa := loc_addr L (LMem (frame_ptr am i fr))) in *. set (G := loc_addr L (LMem g)) in *.
  destruct (tf_arm R1 (p4_mem m regs) rom G (meta_bits am) i _ (am_avail am) (am_freed am) _ _ _ _ _ _ TP)
    as (R2 & Hms2 & TPOST).
  - exact Rav.
  - exact Rfr.
  - rewrite p4_rdn_other by (first [exact Rsp | clear - D5 RG; lia]). exact Mav.
  - rewrite p4_rdn_other by (first [exact Rsp | clear - D5 RG; lia]). exact Mfr.
  - rewrite p4_rdn_other by (first [exact Rsp | clear - Rsp; lia]). exact Hnl.
  - intros d k Hd Hk2. apply (store_ok_mono SEGS k m); [apply p4_mem_grows|].
    replace (G + 28 + d) with (G + 24 + (4 + d)) by ring. apply Wmeta; clear - Hd Hk2; lia.
  - exact A2.
  - exact A3.
  - exact Hf0.
  - rewrite EW, Z.lor_comm. unfold bit, ones in Hnall. exact Hnall.
  - pose proof HR as (HL & HC & HFM).
    destruct (free_cells_geom L s g am i fr (bv_unsigned (getr regs 2)) HW HL HF HFP) as (Gp & GG1 & GG2 & HpG).
    set (m' := tf_mem (p4_mem m regs) pa G (am_freed am + 2 ^ i)) in *.
    exists R2, m'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split.
    { destruct TPOST as (T1 & T8 & T9 & T18 & T19 & T2 & Toth). destruct PRO as (_ & _ & _ & _ & _ & Poth).
      intros n Hn. cbn [In] in Hn.
      destruct Hn as [<-|[<-|Hn]].
      { match type of T1 with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat 1)) with r by (apply bv_eq; reflexivity) end. rewrite T1, wa_u. reflexivity. }
      { match type of T2 with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat 2)) with r by (apply bv_eq; reflexivity) end. rewrite T2, wa_u. reflexivity. }
      destruct Hn as [<-|[<-|Hn]]; [rewrite (Toth 3%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])); exact (Poth 3%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ]))
                                   | rewrite (Toth 4%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])); exact (Poth 4%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ]))|].
      destruct Hn as [<-|[<-|[<-|[<-|Hn]]]].
      { match type of T8 with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat 8)) with r by (apply bv_eq; reflexivity) end. rewrite T8, wa_u. reflexivity. }
      { match type of T9 with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat 9)) with r by (apply bv_eq; reflexivity) end. rewrite T9, wa_u. reflexivity. }
      { match type of T18 with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat 18)) with r by (apply bv_eq; reflexivity) end. rewrite T18, wa_u. reflexivity. }
      { match type of T19 with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat 19)) with r by (apply bv_eq; reflexivity) end. rewrite T19, wa_u. reflexivity. }
      assert (Hn' : In n [3;4;20;21;22;23;24;25;26;27]%nat) by (clear - Hn; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ]).
      rewrite (Toth n Hn'). apply Poth. clear - Hn'; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ]. }
    pose proof (free_fast_itree s g am i fr HW HF Hf0 Hnall) as Hit.
    split; [exact Hit|].
    assert (MO : forall x, 0 <= x < 2^64 -> ~ (bv_unsigned (getr regs 2) - 1024 <= x < bv_unsigned (getr regs 2)) -> ~ (pa - 3 <= x < pa) ->
                   ~ (G + 28 <= x < G + 32) -> m' (wa x) = m (wa x)).
    { intros x Hx H1 H2 H3. unfold m'. rewrite tf_mem_out; try assumption; try (clear - Gp Rsp; lia); try (clear - GG1 GG2 Rsp; lia).
      apply p4_mem_out; [exact Rsp | exact Hx | clear - H1; lia]. }
    assert (BV : forall x, ~ (bv_unsigned (getr regs 2) - 1024 <= x < bv_unsigned (getr regs 2)) -> ~ (pa - 3 <= x < pa) ->
                   ~ (G + 28 <= x < G + 32) -> bview SEGS m' x = bview SEGS m x).
    { intros x H1 H2 H3. destruct (Z_lt_le_dec x 0) as [Hn|Hn].
      { unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; exact Hn). reflexivity. }
      destruct (Z_lt_le_dec x (2^64)) as [Hx|Hx].
      2:{ unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; exact Hx). reflexivity. }
      apply bview_ext. apply MO; try assumption. split; assumption. }
    assert (WR3 : bview SEGS m' (pa - 3) = Some 255).
    { rewrite (bview_some_byte SEGS m' (pa - 3) (Z_to_bv 8 255) ltac:(clear - Gp Rsp; lia)); [reflexivity|]. unfold m'.
      apply tf_mem_p3; first [exact HpG | clear - Gp Rsp; lia | clear - GG1 GG2 Rsp; lia]. }
    assert (WR2 : forall k, (k < 2)%nat -> bview SEGS m' (pa - 2 + Z.of_nat k) = Some 0).
    { intros k Hk2. rewrite (bview_some_byte SEGS m' (pa - 2 + Z.of_nat k) (Z_to_bv 8 0) ltac:(clear - Gp Rsp Hk2; lia)); [reflexivity|]. unfold m'.
      apply tf_mem_p2; first [exact HpG | exact Hk2 | clear - Gp Rsp; lia | clear - GG1 GG2 Rsp; lia]. }
    assert (WRF : forall k, (k < 4)%nat -> bview SEGS m' (G + 28 + Z.of_nat k) = Some (le_byte (am_freed am + bit i) 4 k)).
    { intros k Hk2. rewrite (bview_some_byte SEGS m' (G + 28 + Z.of_nat k) (nth k (word_to_le_bytes 4 (wa (am_freed am + 2 ^ i))) (Z_to_bv 8 0)) ltac:(clear - GG1 GG2 Rsp Hk2; lia)).
      - f_equal. rewrite le_byte_Z_to_le_bytes by (clear - Hk2; lia). unfold bit. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
        unfold le_byte. rewrite Z.mod_mod by (clear; lia). reflexivity.
      - unfold m'. apply tf_mem_G28; first [exact Hk2 | clear - Gp Rsp; lia | clear - GG1 GG2 Rsp; lia]. }
    split; [split; [|split]|].
    + destruct (in_frames_inv s g am i fr HF) as (Hu' & Hi' & Hfri').
      assert (Hb : In (frame_ptr am i fr, fr_n fr) (user_blocks s)).
      { unfold user_blocks. apply in_flat_map. exists (g, am). split; [exact Hu'|]. cbn [snd]. apply in_flat_map.
        exists i. split; [apply In_zseq; lia|]. rewrite Hfri', Hk. left. reflexivity. }
      apply (free_wf s (frame_ptr am i fr) (fr_n fr) [] (s_fast s g am i fr) HW Hb). rewrite Hit. reflexivity.
    + exact (freed_slot_repr SEGS L s m m' g am i fr _ HW HR HF HFP BV WR3 WR2 WRF).
    + exact (freed_slot_markers SEGS L s m m' g am i fr _ HW HR HM HF Hk HFP BV).
    + split; [|unfold m', tf_mem, p4_mem; wgrow]. intros x Hx H1 H2. apply MO; try assumption.
      * intros H3. destruct (free_cells_img L s g am i fr x HW HL HF (or_introl H3)) as (cc & Hcc & Hrr). exact (H2 cc Hcc Hrr).
      * intros H3. destruct (free_cells_img L s g am i fr x HW HL HF (or_intror H3)) as (cc & Hcc & Hrr). exact (H2 cc Hcc Hrr).
Qed.
End Free.
