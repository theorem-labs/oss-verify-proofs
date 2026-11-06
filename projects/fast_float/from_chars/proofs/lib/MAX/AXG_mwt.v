(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfMalloc OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits AxMalloc MngRepr MngHeap MngWb MngImage MngSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngCtx.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMalloc MngTake MngTakeRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efz AXF_efmem.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_mfmem AXG_mfpost AXG_ffstep MngZ MngWk MngGeoX MngExc MngNtfPre MngNtfM MngNtfS.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngTakeR MngTakeR2 AXG_mwm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMalloc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngImage OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx.MngMeta OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMalloc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTake OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTakeRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efz.AXF_efa1z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efz.AXF_efa2z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efz.AXF_efa1mz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efz.AXF_efa1dz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efmem OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_mtz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_mfmem OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_mfpost OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ffstep OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTakeR OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTakeR2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_mwm.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Record tail_post (L : layout) (s : astate) (m : word -> option byte) (regs : bvmap 5 word) (wra ws0 ws1 ws2 ws3 ws4 : word)
    (p : sptr) (s' : astate) (R : bvmap 5 word) (m' : word -> option byte) : Prop := {
  tl_a0 : getr R 10 = wa (loc_addr L (LMem p)) ;
  tl_ra : getr R 1 = wra ; tl_s0 : getr R 8 = ws0 ; tl_s1 : getr R 9 = ws1 ; tl_s2 : getr R 18 = ws2 ; tl_s3 : getr R 19 = ws3 ;
  tl_s4 : getr R 20 = ws4 ;
  tl_sp : getr R 2 = v_addi (getr regs 2) 48 ;
  tl_keep : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)) ;
  tl_heap : Heap0 L s' m' ;
  tl_regions : st_regions s' = st_regions s ;
  tl_fp : footprint s' = footprint s ;
  tl_chg : forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> in_footprint L s x /\ ~ in_user_block L s x ;
  tl_grows : mem_grows m m' ;
  tl_owned : forall c x, In c (image s) -> loc_addr L (mc_loc c) <= x < loc_addr L (mc_loc c) + Z.of_nat (mc_w c) ->
     in_footprint L s' x /\ ~ in_user_block L s' x ;
  tl_ub : forall x, in_user_block L s x -> in_user_block L s' x
}.

Lemma footprint_set_meta_used : forall s g x, KS s -> In g (keys s) -> footprint (set_meta s g x) = footprint s.
Proof. intros s g x _ _. apply footprint_set_meta. Qed.

Section TAIL.
Context {fx : FPState}.
Variables (FORB : list (Z * Z)) (HTOP : Z) (rom : word -> option byte).

#[using="Type"] Theorem tail_wk : forall L s m (regs : bvmap 5 word) n g idx am sp K (wra ws0 ws1 ws2 ws3 ws4 : word)
    (Q : @wpost (option sptr * astate)),
  CUT HTOP [] (Some (g, idx)) U0 L s m sp K -> markers_hold L s (bview SEGS m) ->
  usedX [] s g am -> 1 <= n <= 2^26 -> n + IB <= stride_of am ->
  (am_sc am < 48 -> n < MMAP_THRESHOLD) ->
  (am_sc am = 63 -> MMAP_THRESHOLD <= n /\ am_maplen am * PGSZ < n + UNIT + IB + PGSZ) ->
  (am_sc am < 48 -> (am_prev am, am_next am) <> (None, None) -> active_hd s (am_sc am) = Some g) ->
  getr regs 2 = wa sp -> getr regs 8 = wa n -> getr regs 9 = wa 614096 ->
  getr regs 18 = wa (loc_addr L (LMem g)) -> getr regs 19 = wa idx ->
  rdn SEGS m (wa (sp + 40)) 8 = Some (word_to_le_bytes 8 wra) -> rdn SEGS m (wa (sp + 32)) 8 = Some (word_to_le_bytes 8 ws0) ->
  rdn SEGS m (wa (sp + 24)) 8 = Some (word_to_le_bytes 8 ws1) -> rdn SEGS m (wa (sp + 16)) 8 = Some (word_to_le_bytes 8 ws2) ->
  rdn SEGS m (wa (sp + 8)) 8 = Some (word_to_le_bytes 8 ws3) -> rdn SEGS m (wa (sp + 0)) 8 = Some (word_to_le_bytes 8 ws4) ->
  rdn SEGS m (wa 614096) 4 = Some (word_to_le_bytes 4 (wa 0)) ->
  (forall p s' R m', tail_post L s m regs wra ws0 ws1 ws2 ws3 ws4 p s' R m' -> Q L (Some p, s') R (wa 0x52ce0) m') ->
  wk SEGS FORB HTOP rom L regs (wa 0x522a4) m (ef_tail g idx n s) Q.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m regs n g idx am sp K wra ws0 ws1 ws2 ws3 ws4 Q C HM Hux Hn Hfit Hcl H63 Hhd R2 R8 R9 R18 R19 Mra Ms0 Ms1 Ms2 Ms3 Ms4 Mlock HQ.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof N as [HRx HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HCP HMP HMD].
  pose proof HRx as (HL & HPW & HCS & HFM).
  assert (HR : repr L s (bview SEGS m)) by exact (repr_of_repr_x L s (bview SEGS m) HRx).
  assert (HC : Forall (cell_holds L (bview SEGS m)) (image s)) by exact (proj1 (proj2 HR)).
  pose proof HL as (_ & Lal & Ldisj & Lrng).
  assert (Usp : bv_unsigned (getr regs 2) = sp) by (rewrite R2; apply u_wa_small; lia).
  (* [comment removed for export] *)
  pose proof (usedX_MT _ _ _ _ Hux) as [HMT _].
  pose proof (inv_groups HI g am Hux) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as (Gm & Gml & Gsl & Gcl & Gmp & Gns). destruct Gm as (Mlast & Maidx & Mlen & Mav0 & Mfr0 & Mdisj & Mabove & Mabove2 & _).
  destruct (inv_reserved HI g idx eq_refl) as (am' & Hu' & Hk & Hfree & Hal).
  pose proof (usedX_fun _ _ _ _ _ Hu' Hux) as ->. clear Hu'.
  set (k := idx) in *.
  (* [comment removed for export] *)
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact HMT).
  destruct (HMP g Kg) as (GR1 & GSP & GIMG & GAL).
  set (Gv := loc_addr L (LMem g)) in *.
  (* [comment removed for export] *)
  destruct (used_group_region [] (Some (g, k)) U0 s g am HI Hux) as (rg & Hr & Hkd & Hl & Ho & Hext & Hml0).
  pose proof (footprint_region_In s _ rg Hr Hkd Hl) as FR.
  pose proof (Lrng _ FR) as RR.
  destruct (HG (prid (am_mem am)) rg Hr Hl) as (GA1 & GA2 & GA5 & GA6).
  set (memv := loc_addr L (LMem (am_mem am))).
  assert (Ememv : memv = ly_reg L (prid (am_mem am)) + poff (am_mem am)) by (unfold memv; destruct (am_mem am); reflexivity).
  set (stv := loc_addr L (LMem (slot_start am k))).
  assert (Est : stv = memv + 16 + stride_of am * k) by (unfold stv, memv, slot_start; rewrite loc_padd; unfold UNIT; ring).
  pose proof (slot_in_span [] (Some (g, k)) U0 s HI g am k Hux Hk) as [S1 S1']. rewrite poff_slot_start in S1, S1'.
  assert (Hsk : 0 <= stride_of am * k <= stride_of am * am_last am) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
  assert (RSt : 16 <= stv - memv /\ stv + stride_of am <= memv + group_extent am + IB /\ 0 < memv /\ memv + group_extent am + IB <= HTOP).
  { clear - Est Ememv GA1 GA5 S1 S1' Ho Hext Hsk. rewrite Est. rewrite Ememv in *. unfold PGSZ, UNIT, IB, group_extent in *. lia. }
  assert (RSsp : memv + group_extent am + IB <= sp - K) by (clear - RSt HT; lia).
  (* [comment removed for export] *)
  assert (BV0 : forall x z, bview SEGS m x = Some z -> 0 <= z < 256).
  { intros x z E. unfold bview in E. destruct ((0 <=? x) && (x <? 2^64)); [|discriminate].
    destruct (wview SEGS m (wa x)); [|discriminate]. destruct (ov_read_bytes SEGS m (wa x) 1) as [[|bb [|]]|]; try discriminate.
    injection E as <-. pose proof (bv_unsigned_in_range 8 bb) as Rb. unfold bv_modulus in Rb. cbn in Rb. lia. }
  assert (MAPPED : forall x, memv <= x < memv + group_extent am + IB -> exists z, bview SEGS m x = Some z /\ 0 <= z < 256).
  { intros x Hx. pose proof (proj1 (Forall_forall _ _) HFM _ FR x) as Hm. cbn [fst snd loc_addr] in Hm.
    destruct (bview SEGS m x) as [z|] eqn:E; [exists z; split; [reflexivity | exact (BV0 x z E)]|].
    exfalso. apply Hm; [rewrite Ememv in Hx; lia | reflexivity]. }
  assert (RD1 : forall x z, bview SEGS m x = Some z -> 0 <= z < 256 -> 0 <= x < 2^64 -> rdn SEGS m (wa x) 1 = Some (word_to_le_bytes 1 (wa z))).
  { intros x z E Hz Hx. set (c := MCell (LCtx (x - ly_ctx L)) 1 (VZ z)).
    assert (Hc : cell_holds L (bview SEGS m) c).
    { unfold cell_holds, c. cbn [mc_loc mc_w mc_val loc_addr sval_num]. intros j Hj. assert (j = 0%nat) as -> by lia.
      replace (ly_ctx L + (x - ly_ctx L) + Z.of_nat 0) with x by lia. rewrite E. f_equal. unfold le_byte. cbn.
      rewrite Z.shiftr_0_r, !Z.mod_small by lia. reflexivity. }
    pose proof (holds_rdn SEGS L m c Hc ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as HRd.
    unfold c in HRd. cbn [mc_loc mc_w mc_val loc_addr sval_num] in HRd. replace (ly_ctx L + (x - ly_ctx L)) with x in HRd by lia. exact HRd. }
  assert (RD2 : forall x z1 z2, bview SEGS m x = Some z1 -> bview SEGS m (x + 1) = Some z2 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= x -> x + 2 <= 2^64 ->
             rdn SEGS m (wa x) 2 = Some (word_to_le_bytes 2 (wa (z1 + 256 * z2)))).
  { intros x z1 z2 E1 E2 Hz1 Hz2 Hx Hx2. set (c := MCell (LCtx (x - ly_ctx L)) 2 (VZ (z1 + 256 * z2))).
    assert (Hc : cell_holds L (bview SEGS m) c).
    { unfold cell_holds, c. cbn [mc_loc mc_w mc_val loc_addr sval_num]. intros j Hj.
      assert (j = 0%nat \/ j = 1%nat) as [-> | ->] by lia.
      - replace (ly_ctx L + (x - ly_ctx L) + Z.of_nat 0) with x by lia. rewrite E1. f_equal. unfold le_byte. cbn.
        rewrite Z.shiftr_0_r. rewrite (Z.mod_small (z1 + 256 * z2)) by lia.
        replace (z1 + 256 * z2) with (z1 + z2 * 256) by ring. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
      - replace (ly_ctx L + (x - ly_ctx L) + Z.of_nat 1) with (x + 1) by lia. rewrite E2. f_equal. unfold le_byte. cbn.
        rewrite (Z.mod_small (z1 + 256 * z2)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
        replace (z1 + 256 * z2) with (z1 + z2 * 256) by ring. rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l.
        symmetry. apply Z.mod_small. lia. }
    pose proof (holds_rdn SEGS L m c Hc ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as HRd.
    unfold c in HRd. cbn [mc_loc mc_w mc_val loc_addr sval_num] in HRd. replace (ly_ctx L + (x - ly_ctx L)) with x in HRd by lia. exact HRd. }
  assert (HDR : exists h3 h16, 0 <= h3 <= 255 /\ 0 <= h16 <= 65535 /\
             rdn SEGS m (wa (stv - 3)) 1 = Some (word_to_le_bytes 1 (wa h3)) /\ rdn SEGS m (wa (stv - 2)) 2 = Some (word_to_le_bytes 2 (wa h16)) /\
             (forall a b, ss_hdr (nth_slot am k) = Some (a, b) -> a = h3 /\ b = h16)).
  { destruct (ss_hdr (nth_slot am k)) as [[a b]|] eqn:EH.
    - pose proof (Gsl k Hk) as (_ & Hhr & _). destruct (Hhr a b EH) as (Ra & Rb).
      assert (C3 : In (MCell (LMem (padd (slot_start am k) (-3))) 1 (VZ a)) (image s)).
      { apply (In_image_used s g am _ HK HMT). right. unfold group_cells. apply in_app_iff. right.
        apply in_flat_map. exists k. split; [apply In_zseq; lia|]. unfold slot_cells. rewrite EH. right. left. reflexivity. }
      assert (C16 : In (MCell (LMem (padd (slot_start am k) (-2))) 2 (VZ b)) (image s)).
      { apply (In_image_used s g am _ HK HMT). right. unfold group_cells. apply in_app_iff. right.
        apply in_flat_map. exists k. split; [apply In_zseq; lia|]. unfold slot_cells. rewrite EH. right. right. left. reflexivity. }
      pose proof (repr_rdn SEGS L s m _ HR C3 ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as R3.
      pose proof (repr_rdn SEGS L s m _ HR C16 ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as R16.
      cbn [mc_loc mc_w mc_val sval_num] in R3, R16. rewrite loc_padd in R3, R16. fold stv in R3, R16.
      exists a, b. split; [lia|]. split; [lia|]. split; [exact R3|]. split; [exact R16|]. intros a' b' E. injection E; auto.
    - destruct (MAPPED (stv - 3) ltac:(rewrite Est; unfold group_extent, UNIT, IB; lia)) as (z3 & E3 & Rz3).
      destruct (MAPPED (stv - 2) ltac:(rewrite Est; unfold group_extent, UNIT, IB; lia)) as (z1 & E1 & Rz1).
      destruct (MAPPED (stv - 2 + 1) ltac:(rewrite Est; unfold group_extent, UNIT, IB; lia)) as (z2 & E2 & Rz2).
      exists z3, (z1 + 256 * z2). split; [lia|]. split; [lia|].
      split; [apply RD1; [exact E3 | clear - Rz3; lia | clear - RSt Sp HTB; unfold IB, group_extent in *; lia]|].
      split; [apply RD2; [exact E1 | exact E2 | clear - Rz1; lia | clear - Rz2; lia | clear - RSt Sp; unfold IB, group_extent in *; lia
                          | clear - RSt Sp HTB; unfold IB, group_extent in *; lia]|].
      intros a' b' E. discriminate. }
  destruct HDR as (h3 & h16 & Rh3 & Rh16 & MH3 & MH16 & HH).
  (* [comment removed for export] *)
  assert (MS : forall c, In c (meta_slot_cells g (Some (MUsed am))) -> In c (image s)).
  { intros c Hc. apply (In_image_used s g am c HK HMT). left. exact Hc. }
  assert (CX : forall c, In c (ctx_cells s) -> In c (image s)).
  { intros c Hc. unfold image. apply in_app_iff. left. exact Hc. }
  pose proof (repr_rdn SEGS L s m (MCell (LMem (padd g META_mem)) 8 (VP (am_mem am))) HR (MS _ ltac:(right; right; left; reflexivity))
                ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as MMEM.
  pose proof (repr_rdn SEGS L s m (MCell (LMem (padd g META_bits)) 8 (VZ (meta_bits am))) HR (MS _ ltac:(right; right; right; right; right; left; reflexivity))
                ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as MBITS.
  cbn [mc_loc mc_w mc_val sval_num] in MMEM, MBITS. rewrite loc_padd in MMEM, MBITS. fold Gv memv in MMEM, MBITS.
  unfold META_mem, META_bits in MMEM, MBITS.
  pose proof (inv_ctx HI) as (Lact & _ & _ & _ & _ & _ & _ & _ & Rctr & _).
  assert (Cctr : In (MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter s))) (image s)).
  { apply CX. unfold ctx_cells. apply in_app_iff. left. cbn [In]. tauto. }
  pose proof (repr_rdn SEGS L s m _ HR Cctr ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as MCTR.
  cbn [mc_loc mc_w mc_val sval_num optr loc_addr] in MCTR. rewrite Hctx in MCTR. unfold CTX_mmap_counter in MCTR.
  (* [comment removed for export] *)
  assert (PT : mt_pre regs m n Gv k (st_mmap_counter s) wra ws0 ws1 ws2 ws3 ws4).
  { constructor.
    - exact R8.
    - exact R9.
    - exact R18.
    - exact R19.
    - rewrite Usp. clear - Hsp1 Hsp2 HK1. lia.
    - rewrite Usp. exact Hsp3.
    - exact Hn.
    - clear - GR1 GSP GIMG HTB HT Hsp2 HK1. lia.
    - clear - Hk Mlast. lia.
    - clear - Rctr. lia.
    - replace (0 + 614116) with (614104 + 12) by reflexivity. exact MCTR.
    - exact Mlock.
    - rewrite Usp. exact Mra.
    - rewrite Usp. exact Ms0.
    - rewrite Usp. exact Ms1.
    - rewrite Usp. exact Ms2.
    - rewrite Usp. exact Ms3.
    - rewrite Usp. exact Ms4. }
  destruct (mt_arm regs m rom n Gv k (st_mmap_counter s) wra ws0 ws1 ws2 ws3 ws4 PT) as (R3 & M3 & T10 & T11 & T12 & T13 & TRA & TS0 & TS1 & TS2 & TS3 & TS4 & TSP & TK).
  (* [comment removed for export] *)
  assert (SLMETA : stv - 4 + stride_of am <= Gv + 16 \/ Gv + 40 <= stv - 4).
  { destruct (key_slot_range HTOP [] (Some (g, k)) U0 s L g HI HG Kg) as (ag & j & rr & rga & Hag & Hj & Eag & Epr & Hrr & Hlv & Hkda & A1 & A2 & A3 & A4).
    fold Gv in A4.
    assert (Hne : rr <> prid (am_mem am)).
    { intros E. rewrite E in Hrr. rewrite Hr in Hrr. injection Hrr as <-. exact (Hkda Hkd). }
    pose proof (HD rr (prid (am_mem am)) rga rg Hne Hrr Hr Hlv Hl) as D. unfold ranges_disjoint in D. cbn [fst snd] in D.
    unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
    clear - D A2 A3 A4 Hj S1 S1' Ho Hext Est Ememv Sp Hsk. rewrite Est. rewrite Ememv in *. unfold group_extent, UNIT, IB in *. lia. }
  set (ctr' := bv_swrap 32 (st_mmap_counter s) mod 2^64).
  assert (Rctr' : 0 <= ctr' <= 2^64 - 1) by (unfold ctr'; pose proof (Z.mod_pos_bound (bv_swrap 32 (st_mmap_counter s)) (2^64) ltac:(lia)); lia).
  assert (E13 : getr R3 13 = wa ctr') by (rewrite T13; unfold ctr'; apply wa_eqm; rewrite Z.mod_mod by lia; reflexivity).
  assert (Eoff0 : ef_off0 ctr' h3 h16 = ef_off0 (st_mmap_counter s) h3 h16).
  { unfold ef_off0, ctr'. destruct (h3 =? 0); [|reflexivity].
    change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. change (2 ^ 8) with 256.
    assert (A : forall x, x mod 256 = (x mod 2^32) mod 256) by (intros x; change (2^32) with (256 * 16777216); rewrite mod_mod_div by lia; reflexivity).
    rewrite (A (bv_swrap 32 (st_mmap_counter s) mod 2 ^ 64)), (A (st_mmap_counter s)). rewrite mod64_32, swrap32_mod. reflexivity. }
  assert (Mck : rdn SEGS m (wa (stv - 4)) 1 = Some (word_to_le_bytes 1 (wa 0))).
  { assert (C4 : In (MCell (LMem (padd (slot_start am k) (-4))) 1 (VZ 0)) (image s)).
    { apply (In_image_used s g am _ HK HMT). right. unfold group_cells. apply in_app_iff. right.
      apply in_flat_map. exists k. split; [apply In_zseq; lia|]. unfold slot_cells. left. reflexivity. }
    pose proof (repr_rdn SEGS L s m _ HR C4 ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as R4'.
    cbn [mc_loc mc_w mc_val sval_num] in R4'. rewrite loc_padd in R4'. exact R4'. }
  assert (MWIN : forall d kk, 0 <= d -> d + Z.of_nat kk <= stride_of am -> store_ok SEGS m (wa (stv - 4 + d)) kk = true).
  { intros d kk Hd Hkk. apply (store_ok_of_bytes SEGS m (stv - 4) (stride_of am)); [|lia|lia].
    intros j Hj. destruct (MAPPED (stv - 4 + j) ltac:(clear - Hj RSt Sp; unfold IB in *; lia)) as (z & E & _).
    unfold bview in E. destruct ((0 <=? stv - 4 + j) && (stv - 4 + j <? 2^64)); [|discriminate].
    destruct (wview SEGS m (wa (stv - 4 + j))); [discriminate | discriminate]. }
  (* [comment removed for export] *)
  assert (EF : exists R4 sz, 16 * sz = stride_of am /\ 1 <= sz /\
     msteps SEGS (mkst R3 (wa 0x52b94) m rom) (mkst R4 (wa 0x52ce0) (efb_mem m k n memv sz stv (ef_offv sz n ctr' h3 h16)) rom) /\
     getr R4 10 = wa (stv + 16 * ef_offv sz n ctr' h3 h16) /\
     (forall kk, In kk callee_regs -> getr R4 (Z_to_bv 5 (Z.of_nat kk)) = getr R3 (Z_to_bv 5 (Z.of_nat kk)))).
  { assert (MBITS2 := MBITS). assert (MMEM2 := MMEM).
    destruct Gcl as [(Esc & El0 & Ml1 & Av0 & Fr0 & _) | (Hsc' & Cund & C26 & Cbig)].
    - (* [comment removed for export] *)
      pose proof (H63 Esc) as (Hbig & Hml63).
      assert (Ek0 : k = 0) by lia.
      destruct (Gmp ltac:(lia)) as (r0 & rg0 & Em0 & Hr0 & _ & _ & Len0 & _ & Small0).
      assert (Erg : rg0 = rg).
      { rewrite Em0 in Hr. cbn [prid] in Hr. rewrite Hr in Hr0. injection Hr0 as <-. reflexivity. }
      subst rg0.
      assert (Rml : 4096 * am_maplen am <= 2^47) by (clear - GA1 GA5 Len0 HTB; unfold PGSZ in *; lia).
      assert (Estr : stride_of am = am_maplen am * 4096 - 16).
      { unfold stride_of. rewrite El0. replace (am_maplen am =? 0) with false by (symmetry; apply Z.eqb_neq; lia). unfold UNIT. reflexivity. }
      assert (EW12 : Z.shiftr (meta_bits am) 12 = am_maplen am).
      { unfold meta_bits. rewrite El0, Esc. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
        replace (0 + 32 + 64 * 63 + 4096 * am_maplen am) with ((32 + 64 * 63) + am_maplen am * 4096) by ring.
        rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring. }
      assert (EWl0 : Z.land (meta_bits am) 31 = 0).
      { unfold meta_bits. rewrite El0, Esc. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
        replace (0 + 32 + 64 * 63 + 4096 * am_maplen am) with ((1 + 2 * 63 + 128 * am_maplen am) * 32) by ring. apply Z.mod_mul. lia. }
      assert (RWv : 4096 <= meta_bits am <= 2^63-1) by (unfold meta_bits; rewrite El0, Esc; clear - Ml1 Rml; lia).
      assert (Edst : ef_dstride (meta_bits am) = stride_of am) by (unfold ef_dstride; rewrite EW12, Estr; ring).
      assert (Esz16 : 16 * ef_dsz (meta_bits am) = stride_of am) by (unfold ef_dsz; rewrite EW12, Estr; ring).
      assert (Estv : stv = memv + 16) by (rewrite Est, Ek0; ring).
      assert (P : efd_pre R3 m Gv n ctr' (meta_bits am) memv h3 h16).
      { constructor; [constructor| | | |].
        - exact T10.
        - rewrite T11, Ek0. reflexivity.
        - exact T12.
        - exact E13.
        - clear - GR1 GSP GIMG HTB HT Hsp2 HK1. lia.
        - exact GAL.
        - exact Hn.
        - exact Rctr'.
        - exact RWv.
        - exact EWl0.
        - clear - RSt HTB Sp. lia.
        - exact Rh3.
        - exact Rh16.
        - exact MBITS2.
        - exact MMEM2.
        - replace (memv + 12) with (stv - 4) by lia. exact Mck.
        - replace (memv + 13) with (stv - 3) by lia. exact MH3.
        - replace (memv + 14) with (stv - 2) by lia. exact MH16.
        - rewrite Edst. clear - Hfit. unfold IB in Hfit. lia.
        - clear - RSt Estv Sp HTB. lia.
        - rewrite Edst, Estr. clear - Hml63 Hn. unfold PGSZ, UNIT, IB in Hml63. lia.
        - intros d kk Hd Hkk. replace (memv + 12 + d) with (stv - 4 + d) by lia. apply MWIN; [exact Hd | rewrite <- Edst; exact Hkk].
        - rewrite Edst. clear - RSt Estv Sp HTB. lia.
        - rewrite Edst. replace (memv + 12) with (stv - 4) by lia. lia. }
      destruct (ef_direct_arm R3 m rom Gv n ctr' (meta_bits am) memv h3 h16 P) as (R4 & M4 & A4 & K4').
      exists R4, (ef_dsz (meta_bits am)). split; [exact Esz16|]. split; [unfold ef_dsz; rewrite EW12; lia|].
      assert (Est0 : ef_st memv (ef_dsz (meta_bits am)) 0 = stv) by (unfold ef_st; rewrite Estv; ring).
      rewrite Est0 in M4, A4. rewrite Ek0. split; [exact M4|]. split; [exact A4|]. exact K4'.
    - pose proof (Hcl ltac:(lia)) as Hsm.
      pose proof (class_size_bounds (am_sc am) Hsc') as CSB.
      set (szc := znth (am_sc am) size_classes).
      assert (Ecs : class_size (am_sc am) = 16 * szc) by (unfold class_size, UNIT; reflexivity).
      assert (MTAB2 : rdn SEGS m (wa (98984 + 2 * am_sc am)) 2 = Some (word_to_le_bytes 2 (wa szc))).
      { destruct Henv as (_ & Etab & _). exact (Etab _ Hsc'). }
      destruct (Z.eq_dec (am_maplen am) 0) as [Eml|Nml].
      + (* [comment removed for export] *)
        assert (Estr : stride_of am = 16 * szc).
        { unfold stride_of. rewrite Eml. replace ((am_last am =? 0) && negb (0 =? 0)) with false by (destruct (am_last am =? 0); reflexivity).
          exact Ecs. }
        assert (RWv : 0 <= meta_bits am <= 3071) by (unfold meta_bits; rewrite Eml; lia).
        assert (EW6 : Z.shiftr (meta_bits am) 6 = am_sc am).
        { unfold meta_bits. rewrite Eml. rewrite Z.shiftr_div_pow2 by lia. change (2^6) with 64.
          replace (am_last am + 32 + 64 * am_sc am + 4096 * 0) with ((am_last am + 32) + am_sc am * 64) by ring.
          rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring. }
        assert (Estv : stv = ef_st memv szc k) by (unfold ef_st; rewrite Est, Estr; ring).
        assert (P : ef_pre R3 m Gv k n ctr' (meta_bits am) memv szc h3 h16).
        { constructor; [constructor| | |].
          - exact T10.
          - exact T11.
          - exact T12.
          - exact E13.
          - clear - GR1 GSP GIMG HTB HT Hsp2 HK1. lia.
          - exact GAL.
          - clear - Hk Mlast. lia.
          - clear - Hsm Hn. unfold MMAP_THRESHOLD in Hsm. lia.
          - exact Rctr'.
          - exact RWv.
          - clear - RSt HTB Sp. lia.
          - unfold szc. lia.
          - exact Rh3.
          - exact Rh16.
          - rewrite Estr in Est. clear - Est RSt Sp HTB. lia.
          - exact MBITS2.
          - exact MMEM2.
          - rewrite EW6. replace (2 * am_sc am + 98984) with (98984 + 2 * am_sc am) by ring. exact MTAB2.
          - replace (memv + 16 * szc * k + 12) with (stv - 4) by (rewrite Est, Estr; ring). exact Mck.
          - replace (memv + 16 * szc * k + 13) with (stv - 3) by (rewrite Est, Estr; ring). exact MH3.
          - replace (memv + 16 * szc * k + 14) with (stv - 2) by (rewrite Est, Estr; ring). exact MH16.
          - rewrite <- Estr. clear - Hfit. unfold IB in Hfit. lia.
          - rewrite <- Estv. rewrite <- Estr. clear - RSt Sp HTB. lia.
          - intros d kk Hd Hkk. rewrite <- Estv. apply MWIN; [exact Hd | rewrite Estr; exact Hkk].
          - rewrite <- Estv. rewrite Estr in SLMETA. lia. }
        destruct (ef_class0_arm R3 m rom Gv k n ctr' (meta_bits am) memv szc h3 h16 P) as (R4 & M4 & A4 & K4').
        exists R4, szc. split; [exact (eq_sym Estr)|]. split; [lia|].
        rewrite <- Estv in M4, A4. split; [exact M4|]. split; [exact A4|]. exact K4'.
      + (* [comment removed for export] *)
        assert (Hml : 0 < am_maplen am) by lia.
        destruct (Gmp Hml) as (r0 & rg0 & Em0 & Hr0 & _ & _ & Len0 & _ & Small0).
        assert (Erg : rg0 = rg).
        { rewrite Em0 in Hr. cbn [prid] in Hr. rewrite Hr in Hr0. injection Hr0 as <-. reflexivity. }
        subst rg0.
        assert (Rml : 4096 * am_maplen am <= 2^47) by (clear - GA1 GA5 Len0 HTB; unfold PGSZ in *; lia).
        destruct (Z.eq_dec (am_last am) 0) as [El0|Hl0].
        * (* [comment removed for export] *)
          assert (Ek0 : k = 0) by lia.
          assert (Estr : stride_of am = am_maplen am * 4096 - 16).
          { unfold stride_of. rewrite El0. replace (am_maplen am =? 0) with false by (symmetry; apply Z.eqb_neq; lia). unfold UNIT. reflexivity. }
          assert (EW12 : Z.shiftr (meta_bits am) 12 = am_maplen am).
          { unfold meta_bits. rewrite El0. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
            replace (0 + 32 + 64 * am_sc am + 4096 * am_maplen am) with ((32 + 64 * am_sc am) + am_maplen am * 4096) by ring.
            rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring. }
          assert (EWl0 : Z.land (meta_bits am) 31 = 0).
          { unfold meta_bits. rewrite El0. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
            replace (0 + 32 + 64 * am_sc am + 4096 * am_maplen am) with ((1 + 2 * am_sc am + 128 * am_maplen am) * 32) by ring. apply Z.mod_mul. lia. }
          assert (RWv : 4096 <= meta_bits am <= 2^63-1) by (unfold meta_bits; clear - Mlast Hsc' Hml Rml; lia).
          assert (Edst : ef_dstride (meta_bits am) = stride_of am) by (unfold ef_dstride; rewrite EW12, Estr; ring).
          assert (Esz16 : 16 * ef_dsz (meta_bits am) = stride_of am) by (unfold ef_dsz; rewrite EW12, Estr; ring).
          assert (Estv : stv = memv + 16) by (rewrite Est, Ek0; ring).
          assert (Sm : am_maplen am * 4096 <= 131072).
          { pose proof (Small0 El0 ltac:(lia)) as SB. unfold page_round, PGSZ, UNIT in SB.
            assert (Q0 : (class_size (am_sc am) + 16 + 4096 - 1) / 4096 < 33) by (apply Z.div_lt_upper_bound; lia). lia. }
          assert (P : efd_pre R3 m Gv n ctr' (meta_bits am) memv h3 h16).
          { constructor; [constructor| | | |].
            - exact T10.
            - rewrite T11, Ek0. reflexivity.
            - exact T12.
            - exact E13.
            - clear - GR1 GSP GIMG HTB HT Hsp2 HK1. lia.
            - exact GAL.
            - exact Hn.
            - exact Rctr'.
            - exact RWv.
            - exact EWl0.
            - clear - RSt HTB Sp. lia.
            - exact Rh3.
            - exact Rh16.
            - exact MBITS2.
            - exact MMEM2.
            - replace (memv + 12) with (stv - 4) by lia. exact Mck.
            - replace (memv + 13) with (stv - 3) by lia. exact MH3.
            - replace (memv + 14) with (stv - 2) by lia. exact MH16.
            - rewrite Edst. clear - Hfit. unfold IB in Hfit. lia.
            - clear - RSt Estv Sp HTB. lia.
            - rewrite Edst, Estr. lia.
            - intros d kk Hd Hkk. replace (memv + 12 + d) with (stv - 4 + d) by lia. apply MWIN; [exact Hd | rewrite <- Edst; exact Hkk].
            - rewrite Edst. clear - RSt Estv Sp HTB. lia.
            - rewrite Edst. replace (memv + 12) with (stv - 4) by lia. lia. }
          destruct (ef_direct_arm R3 m rom Gv n ctr' (meta_bits am) memv h3 h16 P) as (R4 & M4 & A4 & K4').
          exists R4, (ef_dsz (meta_bits am)). split; [exact Esz16|]. split; [unfold ef_dsz; rewrite EW12; lia|].
          assert (Est0 : ef_st memv (ef_dsz (meta_bits am)) 0 = stv) by (unfold ef_st; rewrite Estv; ring).
          rewrite Est0 in M4, A4. rewrite Ek0. split; [exact M4|]. split; [exact A4|]. exact K4'.
        * (* [comment removed for export] *)
          assert (Estr : stride_of am = 16 * szc).
          { unfold stride_of. replace ((am_last am =? 0) && negb (am_maplen am =? 0)) with false
              by (replace (am_last am =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hl0); reflexivity).
            exact Ecs. }
          assert (RWv : 4096 <= meta_bits am <= 2^63-1).
          { unfold meta_bits. clear - Mlast Hsc' Hml Rml. lia. }
          assert (EWl : Z.land (meta_bits am) 31 <> 0).
          { unfold meta_bits. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
            replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with (am_last am + (1 + 2 * am_sc am + 128 * am_maplen am) * 32) by ring.
            rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. exact Hl0. }
          assert (ETB : Z.land (Z.shiftr (meta_bits am) 5) 126 = 2 * am_sc am).
          { pose proof (TB1_SCW (meta_bits am) ltac:(lia)) as T.
            rewrite (Z.mod_small (Z.shiftr (meta_bits am) 5)) in T
              by (split; [apply Z.shiftr_nonneg; lia | rewrite Z.shiftr_div_pow2 by lia; apply Z.div_lt_upper_bound; lia]).
            rewrite T, SCW_bits by lia. f_equal.
            unfold meta_bits. rewrite Z.shiftr_div_pow2 by lia. change (2^6) with 64.
            replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with ((am_last am + 32) + (am_sc am + 64 * am_maplen am) * 64) by ring.
            rewrite Z.div_add by lia. rewrite (Z.div_small (am_last am + 32)) by lia. rewrite Z.add_0_l.
            change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2^6) with 64.
            replace (am_sc am + 64 * am_maplen am) with (am_sc am + am_maplen am * 64) by ring. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
          assert (Estv : stv = ef_st memv szc k) by (unfold ef_st; rewrite Est, Estr; ring).
          assert (P : efm_pre R3 m Gv k n ctr' (meta_bits am) memv szc h3 h16).
          { constructor; [constructor| | |].
            - exact T10.
            - exact T11.
            - exact T12.
            - exact E13.
            - clear - GR1 GSP GIMG HTB HT Hsp2 HK1. lia.
            - exact GAL.
            - clear - Hk Mlast. lia.
            - clear - Hsm Hn. unfold MMAP_THRESHOLD in Hsm. lia.
            - exact Rctr'.
            - exact RWv.
            - exact EWl.
            - clear - RSt HTB Sp. lia.
            - unfold szc. lia.
            - exact Rh3.
            - exact Rh16.
            - rewrite Estr in Est. clear - Est RSt Sp HTB. lia.
            - exact MBITS2.
            - exact MMEM2.
            - rewrite ETB. replace (2 * am_sc am + 98984) with (98984 + 2 * am_sc am) by ring. exact MTAB2.
            - replace (memv + 16 * szc * k + 12) with (stv - 4) by (rewrite Est, Estr; ring). exact Mck.
            - replace (memv + 16 * szc * k + 13) with (stv - 3) by (rewrite Est, Estr; ring). exact MH3.
            - replace (memv + 16 * szc * k + 14) with (stv - 2) by (rewrite Est, Estr; ring). exact MH16.
            - rewrite <- Estr. clear - Hfit. unfold IB in Hfit. lia.
            - rewrite <- Estv. rewrite <- Estr. clear - RSt Sp HTB. lia.
            - intros d kk Hd Hkk. rewrite <- Estv. apply MWIN; [exact Hd | rewrite Estr; exact Hkk].
            - rewrite <- Estv. rewrite Estr in SLMETA. lia. }
          destruct (ef_classm_arm R3 m rom Gv k n ctr' (meta_bits am) memv szc h3 h16 P) as (R4 & M4 & A4 & K4').
          exists R4, szc. split; [exact (eq_sym Estr)|]. split; [lia|].
          rewrite <- Estv in M4, A4. split; [exact M4|]. split; [exact A4|]. exact K4'. }
  destruct EF as (R4 & sz & Esz & Rsz & M4 & R4a0 & K4).
  (* [comment removed for export] *)
  set (off0 := ef_off0 (st_mmap_counter s) h3 h16).
  assert (Roff0 : 0 <= off0 < 256).
  { unfold off0, ef_off0. pose proof (land255_range (if h3 =? 0 then st_mmap_counter s else h16 + 1)). lia. }
  assert (Fit0 : n + 4 <= stride_of am) by (clear - Hfit; unfold IB in Hfit; lia).
  assert (Eslk : ef_slackm am n = ef_slack sz n).
  { unfold ef_slackm, ef_slack. rewrite Z.shiftr_div_pow2 by lia. rewrite <- Esz. unfold IB, UNIT. f_equal. ring. }
  assert (Eoff : ef_offv sz n ctr' h3 h16 = ef_offm am n off0) by (unfold ef_offv, ef_offm; rewrite Eslk, Eoff0; reflexivity).
  rewrite Eoff in M4, R4a0.
  assert (Slk0 : 0 <= ef_slackm am n) by (unfold ef_slackm, UNIT, IB; apply Z.div_pos; lia).
  assert (OR : (0 <= ef_offm am n off0 <= ef_slackm am n) /\ ef_offm am n off0 <= 255) by exact (ef_off_rng (ef_slackm am n) off0 Slk0 ltac:(lia)). destruct OR as (OR1 & OR2).
  set (off := ef_offm am n off0) in *.
  assert (Fit : n + 4 + 16 * off <= 16 * sz).
  { pose proof (Z.mul_div_le (stride_of am - IB - n) UNIT ltac:(unfold UNIT; lia)) as MD. unfold ef_slackm in OR1.
    clear - MD OR1 Esz. unfold UNIT, IB in *. lia. }
  assert (Roff : 0 <= off <= 255) by lia.
  assert (Rst : 17 <= stv <= 2^63 - 1) by (clear - RSt Est Sp Hsk HTB; lia).
  assert (Rend : stv + 16 * sz <= 2^63) by (rewrite Esz; clear - RSt Sp HTB; unfold IB in *; lia).
  assert (Rn1 : 1 <= n) by lia.
  (* [comment removed for export] *)
  unfold ef_tail.
  apply (enframe_wk SEGS FORB HTOP rom L regs (wa 0x522a4) m g k n (st_mmap_counter s) s am off0 _ Q (fun r => Inv [] None U0 (snd r))).
  { apply (enframe_spec [] U0 s g k n (st_mmap_counter s) FUser am (fun r => Inv [] None U0 (snd r)) HI Hux ltac:(lia)
             ltac:(clear - Hfit; lia) ltac:(clear - Rctr; lia) ltac:(intros E; discriminate)).
    - intros E. destruct (H63 E) as (A & B). split; [reflexivity | split; [exact A | exact B]].
    - exact Hhd.
    - intros off' s' hdr' _ _ _ _ HI'. exact HI'. }
  { exact HMT. }
  { exact Hk. }
  { exact Slk0. }
  { exact Roff0. }
  { intros a b Hab _. destruct (HH a b Hab) as [-> ->]. reflexivity. }
  intros HW'. cbn [snd] in HW'. fold off in HW' |- *. cbn [ibind].
  set (m'' := efb_mem m k n memv sz stv off) in *.
  exists R4, (wa 0x52ce0), m''. split; [exact (msteps_trans SEGS _ _ _ M3 M4)|].
  apply HQ.
  assert (MOUT : forall x, 0 <= x < 2^64 -> ~ (stv - 3 <= x < stv + stride_of am - 4) -> m'' (wa x) = m (wa x)).
  { intros x Hx H3. unfold m''. rewrite (efb_mem_out_raw m k n memv sz stv off Rst Rend Roff Rn1 Fit x Hx) by (rewrite Esz; exact H3). reflexivity. }
  assert (BVall : forall x, ~ (stv - 3 <= x < stv + stride_of am - 4) -> bview SEGS m'' x = bview SEGS m x).
  { intros x H3. destruct (Z_lt_le_dec x 0) as [Hn0|Hn0].
    { unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; exact Hn0). reflexivity. }
    destruct (Z_lt_le_dec x (2^64)) as [Hx|Hx].
    2:{ unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; exact Hx). reflexivity. }
    apply bview_ext. apply MOUT; [lia | exact H3]. }
  assert (Mgrows : mem_grows m m'') by (unfold m''; apply efb_mem_grows).
  assert (BM : forall x, bview SEGS m x <> None -> bview SEGS m'' x <> None) by (intros x; apply bview_grows; exact Mgrows).
  pose proof (tr_cnew_holds L am k n off m sz Esz Rst Rend Roff Rn1 Fit) as HNew.
  pose proof (tr_mnew_holds L am k n off m sz Esz Rst Rend Roff Rn1 Fit) as HNewM.
  assert (HR' : repr L (set_meta s g (MUsed (ef_am am k n off))) (bview SEGS m''))
    by exact (reserved_slot_repr L g am k n off s (Some (g, k)) U0 HI Hux Hk Hfree (bview SEGS m) (bview SEGS m'') HR HW' BVall BM HNew).
  assert (HM' : markers_hold L (set_meta s g (MUsed (ef_am am k n off))) (bview SEGS m''))
    by exact (reserved_slot_markers L g am k n off s (Some (g, k)) U0 HI Hux Hk Hfree (bview SEGS m) (bview SEGS m'') HR HM BVall HNewM).
  constructor.
  - rewrite R4a0. unfold ef_ptr. rewrite loc_padd. unfold UNIT. reflexivity.
  - transitivity (getr R3 1); [exact (K4 1%nat ltac:(clear; cbn; tauto)) | exact TRA].
  - transitivity (getr R3 8); [exact (K4 8%nat ltac:(clear; cbn; tauto)) | exact TS0].
  - transitivity (getr R3 9); [exact (K4 9%nat ltac:(clear; cbn; tauto)) | exact TS1].
  - transitivity (getr R3 18); [exact (K4 18%nat ltac:(clear; cbn; tauto)) | exact TS2].
  - transitivity (getr R3 19); [exact (K4 19%nat ltac:(clear; cbn; tauto)) | exact TS3].
  - transitivity (getr R3 20); [exact (K4 20%nat ltac:(clear; cbn; tauto)) | exact TS4].
  - transitivity (getr R3 2); [exact (K4 2%nat ltac:(clear; cbn; tauto)) | exact TSP].
  - intros kk Hkk. rewrite (K4 kk ltac:(clear - Hkk; cbn [In] in *; unfold callee_regs; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). exact (TK kk Hkk).
  - exact (conj HW' (conj HR' HM')).
  - reflexivity.
  - apply footprint_set_meta.
  - intros x Hx Hne.
    destruct (Z_lt_le_dec x (stv - 3)) as [A|A]; [exfalso; apply Hne; apply MOUT; [exact Hx | lia]|].
    destruct (Z_lt_le_dec x (stv + stride_of am - 4)) as [B|B]; [|exfalso; apply Hne; apply MOUT; [exact Hx | lia]].
    exact (reserved_slot_owned L g am k s (Some (g, k)) U0 HI Hux Hk Hfree x HL ltac:(lia)).
  - exact Mgrows.
  - intros c x Hc Hx.
    assert (HL'' : layout_ok L (set_meta s g (MUsed (ef_am am k n off)))) by (apply layout_ok_set_meta; exact HL).
    destruct (reserved_slot_cover L g am k n off s (Some (g, k)) U0 HI Hux Hk Hfree c Hc) as [Hc'|(c' & Hc' & Erng)].
    + exact (image_owned _ L c x HW' HL'' Hc' Hx).
    + pose proof (tr_cnew_in g am k n off s (Some (g, k)) U0 HI Hux Hk c' Hc') as Hc''.
      unfold cell_range in Erng. injection Erng as E1 E2.
      apply (image_owned _ L c' x HW' HL'' Hc''). rewrite E1, E2. exact Hx.
  - intros x (b & Hb & Hxb). exists b. split; [exact (reserved_slot_blocks g am k n off s (Some (g, k)) U0 HI Hux Hk Hfree b Hb) | exact Hxb].
Qed.
End TAIL.
