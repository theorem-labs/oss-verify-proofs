(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfArith MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngGM MngNtfPre MngCtx MngCtx2 MngShape.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxMalloc MngNtfM MngNtfS MngMWP MngMWQ MngMW0 MngMW1 MngMW2 MngMW3 MngMK MngL4 AXF_maz AXG_mfmem AXF_md0z AXF_mmwz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_dq2z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_dq2z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_dq2z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_nM AXG_am1 AXG_amr AXG_am7 AXG_am8 AXG_amw AXG_ag0 AXG_ag1 AXG_ag5 AXG_ag6 AXG_ag7 AXG_ag14 AXG_asc AXG_asw0 AXG_kro AXG_mwm AXG_mwt AXG_mwc AXG_mwk AXG_mwd0 AXG_mwd1 AXG_mwd2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxMalloc OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMWQ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW3 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMK OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngL4 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_maz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mfmem OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_md0z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mmwz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_mmrdz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_md1z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_md2z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_nM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_amr OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am7 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am8 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_amw OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag5 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag6 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag7 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag14 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_asc OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_asw0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_kro OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mwm OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mwt OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mwc OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mwk OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mwd0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mwd1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mwd2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section DW.
Context {fx : FPState}.

#[using="Type"] Theorem direct_wk : direct_wk_stmt.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros FORB HFORB HTOP rom L s m regs n P Hn.
  destruct P as (H0 & HUS & Hctx & HG & HD & HTB & HT20 & HME & HR10 & Hsp16 & Hsp47 & Htop & HSTK & B1 & B2 & B3 & Hini).
  pose proof H0 as (HW & HR & HM).
  destruct HME as ((can & HENV) & HPG & HKRO).
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
  destruct (md0_arm regs m rom n HR10 Hn ltac:(lia) Hsp16 STK1024) as (R1 & M1 & (Q1 & Q2 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q18 & Q19 & QK)).
  set (m1 := ma_mem m regs) in *.
  assert (M1out : forall x, 0 <= x < 2^64 -> ~ (sp0 - 48 <= x < sp0) -> m1 (wa x) = m (wa x)).
  { intros x Hx H. apply ma_mem_out; [lia | exact Hx | exact H]. }
  pose proof (ma_mem_grows m regs) as M1g.
  assert (R1sp : getr R1 2 = wa (sp0 - 48)).
  { rewrite Q2, R2w. apply bv_eq. rewrite u_vaddi''; rewrite ?u_wa_small by lia; lia. }
  assert (STK1 : stk_ok SEGS m1 (wa (sp0 - 48)) 1024).
  { apply (stk_ok_mono' m1 _ (8192 - 48) 1024); [|lia]. apply stk_ok_shift; [|lia|lia|lia].
    rewrite <- R2w. exact (stk_ok_grows SEGS m m1 _ 8192 HSTK M1g). }
  (* [comment removed for export] *)
  assert (P2 : mmw_pre R1 m1 (sp0 - 48) 0 (n + 20) 3 34).
  { constructor; [exact R1sp | exact Q10 | exact Q11 | exact Q12 | exact Q13 | exact Q14 | exact Q15 | exact STK1 | lia | lia | lia | lia | lia |].
    unfold sp0 in *. apply Z.mod_divide in Hsp16; [|lia]. destruct Hsp16 as (k & E). rewrite E. replace (k * 16 - 48) with ((k - 3) * 16) by ring. apply Z.mod_mul. lia. }
  destruct (mmw_pnf R1 m1 rom (sp0 - 48) 0 (n + 20) 3 34 P2) as (R2 & M2 & F2 & F5 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & FK).
  { scs_go; zats. reflexivity. }
  set (m2 := mmw_mem_pnf m1 R1 (sp0 - 48) 0 (n + 20) 3 34) in *.
  assert (M2out : forall x, 0 <= x < 2^64 -> ~ (sp0 - 112 <= x < sp0 - 48) -> m2 (wa x) = m1 (wa x)).
  { intros x Hx H. unfold m2, mmw_mem_pnf. rewrite !MngWb.wbytes_out by (cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_wa_small by lia; lia). reflexivity. }
  assert (M2g : mem_grows m1 m2) by (unfold m2, mmw_mem_pnf; do 7 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  assert (C1 : CUT HTOP [] None U0 L s m2 sp0 8192).
  { apply (CUT_stack HTOP [] None U0 L s m m2 sp0 8192 C0 (mem_grows_trans _ _ _ M1g M2g)). intros x Hx Hn'.
    rewrite M2out by (first [exact Hx | lia]). apply M1out; [exact Hx | lia]. }
  (* [comment removed for export] *)
  destruct (malloc_direct_tree n s ltac:(unfold MMAP_THRESHOLD; lia)) as (Kt & Kd & Et & EK1 & EKd).
  rewrite Et. cbn [wk]. exists R2, (wa 0x551a4), m2. split; [exact (msteps_trans SEGS _ _ _ M1 M2)|]. split.
  { split; [exact ecall_52ecc|]. exists SYS_mmap, [0; n + IB + UNIT; 3; 34; 2 ^ 64 - 1; 0]. split; [reflexivity|].
    split; [rewrite F17; reflexivity|].
    Ltac argk3 T := match type of T with getr _ ?r0 = _ => match goal with |- bv_unsigned (getr _ ?r1) = _ =>
      replace r1 with r0 by (apply bv_eq; reflexivity) end end; rewrite T, u_wa; unfold IB, UNIT; try reflexivity; f_equal; ring.
    split; [argk3 F10|]. split; [argk3 F11|]. split; [argk3 F12|]. split; [argk3 F13|]. split; [argk3 F14|]. split; [argk3 F15|]. exact I. }
  intros eff ans L' Ho. destruct (kout_mmap_rw FORB HTOP L s (n + IB + UNIT) eff ans L' Ho) as (a & FR & -> & -> & ->).
  rewrite add4_52ecc. cbn [eff_ret]. rewrite EK1.
  (* [comment removed for export] *)
  set (plen := page_round (n + IB + UNIT)) in *.
  assert (Hpl : plen mod 4096 = 0 /\ n + 20 <= plen <= n + 20 + 4095).
  { unfold plen, page_round, PGSZ, IB, UNIT. pose proof (Z.div_mod (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)) as Hd.
    pose proof (Z.mod_pos_bound (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)) as Hb. split; [apply Z.mod_mul; lia | lia]. }
  assert (Hplr : 131072 <= plen <= 2^27) by (clear - Hpl Hn; lia).
  pose proof FR as (F1' & F2' & F3' & F4' & F5' & F6' & F7').
  assert (HIMG : ranges_disjoint (a, plen) (0x10000, 0x89000)) by (apply HFORB; [lia | exact F5']).
  assert (Dimg : a + plen <= 0x10000 \/ 0x99000 <= a) by (unfold ranges_disjoint in HIMG; cbn [fst snd] in HIMG; clear - HIMG; lia).
  assert (Ha : 4096 <= a) by (unfold PGSZ in F1'; exact F1').
  assert (Ha47 : a + plen <= 2^47) by (clear - F4' HTB; lia).
  set (m3 := mem_after m2 (mkEffect (w64 a) [] [(w64 a, w64 plen)])) in *.
  assert (OUT3 : forall x, 0 <= x < 2^64 -> ~ (a <= x < a + plen) -> m3 (wa x) = m2 (wa x)).
  { intros x Hx Hn'. unfold m3. rewrite mem_after_zero by (clear - Hx Ha Ha47 Hplr; lia).
    replace ((a <=? x) && (x <? a + plen)) with false by (symmetry; apply andb_false_iff; destruct (Z_le_dec a x); [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]).
    reflexivity. }
  assert (IN3 : forall x, a <= x < a + plen -> m3 (wa x) = Some (Z_to_bv 8 0)).
  { intros x Hx. unfold m3. rewrite mem_after_zero by (clear - Hx Ha Ha47 Hplr; lia).
    replace ((a <=? x) && (x <? a + plen)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
  assert (G23 : mem_grows m2 m3) by (apply mem_after_zero_grows'; clear - Ha Ha47 Hplr; lia).
  set (L1 := set_reg_addr L (length (st_regions s)) a) in *.
  assert (EL1n : ly_reg L1 (length (st_regions s)) = a) by exact (L'_new L s a).
  assert (EL1o : forall k, k <> length (st_regions s) -> ly_reg L1 k = ly_reg L k) by exact (L'_old L s a).
  set (s1 := dr_s1 s n) in *.
  assert (Rs1 : st_regions s1 = st_regions s ++ [mkRegion RkMap plen [] true]) by reflexivity.
  assert (HI1 : Inv [] None U0 s1) by (apply Inv_new_map; [exact HW | lia]).
  assert (EIM1 : image s1 = image s) by exact (image_dr_s1 s n).
  destruct (effect_step HTOP [] None U0 [] None U0 L L1 s s1 m2 m3 m3 sp0 8192 [] a plen C1 (lext_set_new L s a)) as (C3 & G3).
  { clear - Ha; lia. }
  { clear - Hplr; lia. }
  { exact F4'. }
  { exact Dimg. }
  { exact OUT3. }
  { exact F6'. }
  { exists (length (st_regions s)), (mkRegion RkMap plen [] true). split.
    { unfold region_of. rewrite Rs1. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
    split; [reflexivity|]. split; [left; lia|]. rewrite EL1n. cbn [rg_len]. clear; lia. }
  { exact HI1. }
  { apply XNM_nil. }
  { intros k rg Hk Hl.
    assert (Hk' : region_of (set_regions (st_regions s ++ [mkRegion RkMap plen [] true]) s) k = Some rg) by exact Hk.
    destruct (region_of_snoc s _ k rg Hk') as [(Hlt' & Hok)|(-> & ->)].
    + rewrite EL1o by lia. exact (HG k rg Hok Hl).
    + rewrite EL1n. cbn [rg_len]. unfold PGSZ in *. split; [exact F1'|]. split; [exact F2'|]. split; [exact F4' | exact HIMG]. }
  { intros k1 k2 rg1 rg2 Hne H1 H2 L1' L2'.
    assert (H1' : region_of (set_regions (st_regions s ++ [mkRegion RkMap plen [] true]) s) k1 = Some rg1) by exact H1.
    assert (H2' : region_of (set_regions (st_regions s ++ [mkRegion RkMap plen [] true]) s) k2 = Some rg2) by exact H2.
    destruct (region_of_snoc s _ k1 rg1 H1') as [(Hl1 & O1)|(-> & ->)]; destruct (region_of_snoc s _ k2 rg2 H2') as [(Hl2 & O2)|(-> & ->)].
    + rewrite !EL1o by lia. exact (HD k1 k2 rg1 rg2 Hne O1 O2 L1' L2').
    + rewrite EL1o by lia. rewrite EL1n. cbn [rg_len]. apply ranges_disjoint_sym'. exact (F7' k1 rg1 O1 L1').
    + rewrite EL1n. rewrite EL1o by lia. cbn [rg_len]. exact (F7' k2 rg2 O2 L2').
    + exfalso. exact (Hne eq_refl). }
  { split; [rewrite Rs1, length_app; cbn [length]; lia|].
    intros k rg Hk Hl. exists rg. split; [|split; [exact Hl | split; [reflexivity | lia]]].
    unfold region_of. rewrite Rs1. rewrite nth_error_app1 by exact (region_of_lt _ _ _ Hk). exact Hk. }
  { intros f Hf.
    assert (Hf' : In f (footprint (set_regions (st_regions s ++ [mkRegion RkMap plen [] true]) s))) by exact Hf.
    destruct (footprint_snoc_map s plen f Hf') as [A|A]; [left; exact A|right]. subst f.
    intros x Hx. cbn [fst snd] in Hx. change (loc_addr L1 (LMem (SP (length (st_regions s)) 0))) with (ly_reg L1 (length (st_regions s)) + 0) in Hx. rewrite EL1n in Hx.
    rewrite (MngWb.bview_some_byte SEGS m3 x (Z_to_bv 8 0)); [discriminate | clear - Hx Ha Ha47; lia |]. apply IN3. lia. }
  { intros c Hc. left. rewrite EIM1 in Hc. exact Hc. }
  { intros c []. }
  { intros c Hc. left. rewrite EIM1. exact Hc. }
  { apply Forall_nil. }
  { apply mem_grows_refl. }
  { intros x _ E. exfalso. exact (E eq_refl). }
  (* [comment removed for export] *)
  assert (G1E : forall x, sp0 - 112 <= x < sp0 - 48 -> 0 <= x) by (intros; lia).
  destruct (pnf_reads m1 R1 (sp0 - 48) 0 (n + 20) 3 34 ltac:(lia)) as (W1 & W2 & W3 & W4 & W5 & W6 & W7). fold m2 in W1, W2, W3, W4, W5, W6, W7.
  assert (TR3 : forall x k, sp0 - 112 <= x -> x + Z.of_nat k <= sp0 - 48 -> rdn SEGS m3 (wa x) k = rdn SEGS m2 (wa x) k).
  { intros x k H1 H2. apply rdn_frame_n; [lia | lia |]. intros y Hy. apply OUT3; [lia|]. clear - Hy H1 H2 F4' HTB Htop Rsp. lia. }
  rewrite <- TR3 in W1, W2, W3, W4, W5, W6, W7 by (cbn [Z.of_nat Pos.of_succ_nat]; lia).
  assert (U1 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 1))) = 343504) by (replace (getr R1 (Z_to_bv 5 (Z.of_nat 1))) with (wa (343504)) by (symmetry; litr2 Q1; reflexivity); rewrite u_wa_small by lia; reflexivity).
  assert (U8 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 8))) = n) by (replace (getr R1 (Z_to_bv 5 (Z.of_nat 8))) with (wa (n)) by (symmetry; litr2 Q8; reflexivity); rewrite u_wa_small by lia; reflexivity).
  assert (U9 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 9))) = 621712) by (replace (getr R1 (Z_to_bv 5 (Z.of_nat 9))) with (wa (621712)) by (symmetry; litr2 Q9; reflexivity); rewrite u_wa_small by lia; reflexivity).
  assert (U18 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 18))) = 18446744073709551615) by (replace (getr R1 (Z_to_bv 5 (Z.of_nat 18))) with (wa (18446744073709551615)) by (symmetry; litr2 Q18; reflexivity); rewrite u_wa_small by lia; reflexivity).
  assert (U19 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 19))) = n + 20) by (replace (getr R1 (Z_to_bv 5 (Z.of_nat 19))) with (wa (n + 20)) by (symmetry; litr2 Q19; reflexivity); rewrite u_wa_small by lia; reflexivity).
  assert (U20 : getr R1 (Z_to_bv 5 (Z.of_nat 20)) = getr regs (Z_to_bv 5 (Z.of_nat 20))) by exact (QK 20%nat ltac:(lmemb)).
  assert (U21 : getr R1 (Z_to_bv 5 (Z.of_nat 21)) = getr regs (Z_to_bv 5 (Z.of_nat 21))) by exact (QK 21%nat ltac:(lmemb)).
  rewrite U1 in W1. rewrite U8 in W2. rewrite U9 in W3. rewrite U18 in W4. rewrite U19 in W5. rewrite U20 in W6. rewrite U21 in W7.
  assert (P3 : mmrd_pre (regupd R2 10 (w64 a)) m3 (sp0 - 48) a 0 n 621712 18446744073709551615 (n + 20)
                 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))).
  { constructor.
    - rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). rewrite F2; first [reflexivity | f_equal; ring].
    - rewrite getr_same by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). reflexivity.
    - rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). exact F16.
    - lia.
    - clear - Ha Ha47 Hplr; lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - pose proof (u64_range (getr regs (Z_to_bv 5 (Z.of_nat 20)))); lia.
    - pose proof (u64_range (getr regs (Z_to_bv 5 (Z.of_nat 21)))); lia.
    - unfold sp0 in *. apply Z.mod_divide in Hsp16; [|lia]. destruct Hsp16 as (k & E). rewrite E. replace (k * 16 - 48) with ((k - 3) * 16) by ring. apply Z.mod_mul. lia.
    - exact W1.
    - exact W2.
    - exact W3.
    - exact W4.
    - exact W5.
    - exact W6.
    - exact W7. }
  destruct (mmrd_pmrd _ m3 rom _ _ _ _ _ _ _ _ _ P3) as (R3 & M3 & S1 & S2 & S8 & S9 & S10 & S11 & S16 & S18 & S19 & S20 & S21 & SK).
  { scs_go; zats. }
  (* [comment removed for export] *)
  assert (BK3 : forall x, 0 <= x < 2^64 -> (x < sp0 - 112 \/ sp0 <= x) -> ~ (a <= x < a + plen) -> m3 (wa x) = m (wa x)).
  { intros x Hx H1 H2. rewrite OUT3 by (first [exact Hx | exact H2]). rewrite M2out by (first [exact Hx | lia]). apply M1out; [exact Hx | lia]. }
  pose proof C3 as [HI3 HX3 N3 HG3 HD3 HT3 HTB3].
  assert (P3' : PCUT HTOP L1 [] s1 m3 sp0 8192) by exact (PCUT_of_CUT HTOP [] None U0 L1 s1 m3 sp0 8192 C3).
  assert (Lc1 : forall o, loc_addr L1 (LCtx o) = 621720 + o) by (intros o; unfold L1, set_reg_addr; cbn [loc_addr ly_ctx]; rewrite Hctx; reflexivity).
  assert (WC3 : forall o k0, 0 <= o -> o + k0 <= 928 -> forall d k, 0 <= d -> d + Z.of_nat k <= k0 -> store_ok SEGS m3 (wa (621720 + o + d)) k = true).
  { intros o k0 Ho' Hn' d k Hd Hk.
    refine (pc_wr HTOP L1 [] s1 m3 sp0 8192 (LCtx 0, CTX_SIZE) P3' (or_introl eq_refl) (621720 + o) k0 _ _ _ _ d k Hd Hk);
      cbn [fst snd]; rewrite ?Lc1; unfold CTX_SIZE; clear - Ho' Hn'; lia. }
  assert (Mseq3 : rdn SEGS m3 (wa (0 + 622632)) 1 = Some (word_to_le_bytes 1 (wa (st_seq s)))).
  { pose proof (nc_ctx_rd L1 s1 m3 sp0 8192 _ N3 (seq_in_ctx s1) ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite Lc1 in H. unfold CTX_seq in H. exact H. }
  assert (Mnl3 : rdn SEGS m3 (wa (0 + 621603)) 1 = Some (word_to_le_bytes 1 (wa 0))).
  { rewrite (rdn_frame_n m m3 (0 + 621603) 1) by (first [lia | (intros y Hy; cbn [Z.of_nat Pos.of_succ_nat] in Hy; apply BK3; clear - Hy Dimg Rsp; lia)]). exact E1. }
  pose proof (inv_ctx HW) as (CC1 & CC2 & CC3 & CC4 & CC5 & CC6 & CC7 & CC8 & _).
  assert (P4 : md1_pre R3 m3 n a (st_seq s)).
  { constructor; [exact S8 | exact S9 | exact S10 | exact S18 | exact S19 | lia | clear - Ha Ha47 Hplr; lia | exact CC8 | exact Mnl3 | exact Mseq3 | |].
    - intros d k Hd Hk. replace (0 + 622632 + d) with (621720 + 912 + d) by ring. apply (WC3 912 1); clear - Hd Hk; lia.
    - intros d k Hd Hk. replace (0 + 622568 + d) with (621720 + 848 + d) by ring. apply (WC3 848 32); clear - Hd Hk; lia. }
  assert (MD1 : exists R4 m4, msteps SEGS (mkst R3 (wa 0x53dd0) m3 rom) (mkst R4 (wa 0x53a60) m4 rom) /\
            getr R4 1 = wa 343748 /\ getr R4 8 = wa n /\ getr R4 9 = wa 621712 /\ getr R4 18 = wa 18446744073709551615 /\
            getr R4 19 = wa (n + 20) /\ getr R4 20 = wa a /\
            (forall k, In k [2; 3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat ->
               getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr R3 (Z_to_bv 5 (Z.of_nat k))) /\
            ((st_seq s1 <> 255 /\ m4 = wbytes m3 (wa (0 + 622632)) (word_to_le_bytes 1 (wa (st_seq s1 + 1)))) \/
             (st_seq s1 = 255 /\ m4 = wbytes (unm0m m3) (wa (0 + 622632)) (word_to_le_bytes 1 (wa 1))))).
  { destruct (Z.eq_dec (st_seq s) 255) as [Hw|Hw].
    - destruct (md1_pmd1w R3 m3 rom n a (st_seq s) P4) as (R4 & M4 & T1 & T8 & T9 & T10 & T11 & T18 & T19 & T20 & TK).
      { scs_go; zats. rewrite Hw. reflexivity. }
      exists R4, (md1_mem_pmd1w m3 R3 n a (st_seq s)). split; [exact M4|]. do 6 (split; [assumption|]). split; [exact TK|].
      right. split; [exact Hw | reflexivity].
    - destruct (md1_pmd1i R3 m3 rom n a (st_seq s) P4) as (R4 & M4 & T1 & T8 & T9 & T10 & T11 & T18 & T19 & T20 & TK).
      { scs_go; zats. rewrite !Z.mod_small by lia. apply negb_true_iff. apply Z.eqb_neq. exact Hw. }
      exists R4, (md1_mem_pmd1i m3 R3 n a (st_seq s)). split; [exact M4|]. do 6 (split; [assumption|]). split; [exact TK|].
      left. split; [exact Hw | reflexivity]. }
  destruct MD1 as (R4 & m4 & M4 & T1 & T8 & T9 & T18 & T19 & T20 & TK & Hm4).
  destruct (cut_seq HTOP L1 s1 m3 m4 sp0 8192 C3 Hm4) as (C4 & G4 & G34).
  set (s2 := sq_st s1) in *.
  apply (wk_msteps SEGS FORB HTOP rom _ L1 R4 (wa 0x53a60) m4 _ (wa 0x551a8) m3 _ (msteps_trans SEGS _ _ _ M3 M4)).
  (* [comment removed for export] *)
  change (dr_s2 s n) with s2.
  pose proof C4 as [HI4 HX4 N4 HG4 HD4 HT4 HTB4].
  assert (C4s : CUT HTOP [] None U0 L1 s2 m4 (sp0 - 48) (8192 - 48)) by (apply CUT_shift; [exact C4 | lia | reflexivity | lia]).
  assert (R4_2 : getr R4 2 = wa (sp0 - 48)) by (regk TK 2%nat; exact S2).
  assert (G02 : GROW sp0 8192 L s m L s m2).
  { apply GROW_stack; [|lia]. intros x Hx Hne. destruct (Z_lt_le_dec x (sp0 - 112)) as [A|A].
    - exfalso. apply Hne. rewrite M2out by (first [exact Hx | lia]). apply M1out; [exact Hx | lia].
    - destruct (Z_lt_le_dec x sp0) as [B|B]; [lia|]. exfalso. apply Hne. rewrite M2out by (first [exact Hx | lia]). apply M1out; [exact Hx | lia]. }
  assert (HINIT4 : st_init_done s2 = true \/ AMI L1 m4 (sp0 - 48)).
  { destruct Hini as [H|H]; [left; unfold s2, sq_st; destruct (st_seq s1 =? 255); exact H|]. right. apply (AMI_mono L1 m4 sp0); [lia|].
    exact (AMI_GROW HTOP [] None U0 L1 s1 m3 L1 s2 m4 sp0 8192 C4 G4 (AMI_GROW HTOP [] None U0 L s m2 L1 s1 m3 sp0 8192 C3 G3 (AMI_GROW HTOP [] None U0 L s m L s m2 sp0 8192 C1 G02 H))). }
  pose proof G4 as (_ & _ & _ & SI4 & _).
  assert (Mpg4 : rdn SEGS m4 (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m3 m4 621648 8) by (first [lia | (intros y Hy; apply SI4; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia)]).
    rewrite (rdn_frame_n m m3 621648 8) by (first [lia | (intros y Hy; cbn [Z.of_nat Pos.of_succ_nat] in Hy; apply BK3; clear - Hy Dimg Rsp; lia)]).
    exact HPG. }
  pose proof (am_wk FORB HFORB HTOP [] None U0 L1 s2 m4 R4 rom (sp0 - 48) (8192 - 48) 0x53ec4 C4s ltac:(lia) R4_2 T1 (or_intror eq_refl) Mpg4 B1 B2 B3 HINIT4) as AW.
  set (QMa := fun r : option sptr * astate => match fst r with None => True | Some mt =>
                Inv [mt] None U0 (snd r) /\ memb mt [] = false /\ MallocWfMeta.am_frame s2 (snd r) /\
                (forall g am, usedX [mt] (snd r) g am <-> usedX [] s2 g am) /\ ub_same s2 (snd r) end).
  pose proof (wk_itok SEGS FORB HTOP rom _ L1 R4 (wa 0x53a60) m4 _ QMa AW
                (alloc_meta_spec [] None U0 s2 QMa HI4 (fun s' _ _ _ _ => I) (fun mt s' H1 H2 _ _ H5 H6 H7 => conj H1 (conj H2 (conj H5 (conj H6 H7)))))) as AW2.
  apply wk_ibind. eapply wk_mono; [| exact AW2].
  intros L3 rr R5 pc5 m5 (AQ & AMS).
  destruct AQ as (mt & s3 & -> & -> & R5_10 & R5K & C5s & G5s).
  cbn [fst snd QMa] in AMS. destruct AMS as (HI5' & NX5 & Fr5 & EU5 & UB5).
  rewrite EKd.
  (* [comment removed for export] *)
  assert (ABOVE5 : forall x, sp0 - 48 <= x < 2^64 -> m5 (wa x) = m4 (wa x))
    by exact (growx_above (fun _ => False) HTOP [mt] None U0 L1 s2 m4 L3 s3 m5 (sp0 - 48) (8192 - 48) (GROWX_of_GROW _ _ _ _ _ _ _ _ _ G5s) C5s).
  assert (STK5 : stk_ok SEGS m5 (wa sp0) 8192).
  { pose proof C5s as [_ _ N5s _ _ _ _].
    apply (stk_ok_join m4 m5 sp0 8192 48); [exact (nc_stk _ _ _ _ _ _ _ N5s) | exact (nc_stk _ _ _ _ _ _ _ N4) | intros x Hx; apply ABOVE5; lia | lia | lia]. }
  assert (C5 : CUT HTOP [mt] None U0 L3 s3 m5 sp0 8192) by exact (CUT_unshift HTOP [mt] None U0 L3 s3 m5 sp0 8192 48 C5s ltac:(lia) STK5 ltac:(lia) Hsp16).
  assert (G5 : GROW sp0 8192 L1 s2 m4 L3 s3 m5) by exact (GROW_unshift sp0 8192 48 L1 s2 m4 L3 s3 m5 G5s ltac:(lia)).
  pose proof C5 as [HI5 HX5 N5 HG5 HD5 HT5 HTB5].
  pose proof G5 as (HE5 & RM5 & _ & SI5 & _).
  (* [comment removed for export] *)
  assert (Hr1 : region_of s1 (length (st_regions s)) = Some (mkRegion RkMap plen [] true)).
  { unfold region_of. rewrite Rs1. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  assert (Hr2 : region_of s2 (length (st_regions s)) = Some (mkRegion RkMap plen [] true)) by (unfold s2, sq_st; destruct (st_seq s1 =? 255); exact Hr1).
  pose proof Fr5 as (Eac5 & Eus5 & Erg5 & Elen5 & Ectr5).
  assert (Hr3 : region_of s3 (length (st_regions s)) = Some (mkRegion RkMap plen [] true)) by exact (Erg5 _ _ Hr2 eq_refl).
  assert (XU5 : XNU [mt] s3) by exact (XNU_of_XNM [mt] s3 HX5).
  assert (OLD3 : forall q a', In (q, a') (used_metas s3) -> (prid (am_mem a') < length (st_regions s))%nat).
  { intros q a' H. apply (used_metas_usedX_X [mt] None U0 s3 q a' HI5 XU5) in H. apply EU5 in H.
    assert (Hu : usedX [] s q a') by (unfold usedX, MTX, MT in H |- *; cbn [memb] in *; unfold s2, sq_st, s1, dr_s1 in H; destruct (st_seq _ =? 255); exact H).
    exact (used_group_prid_lt [] None U0 s q a' HW Hu). }
  assert (Ha3 : ly_reg L3 (length (st_regions s)) = a).
  { rewrite (proj2 (proj2 (proj2 HE5)) (length (st_regions s))); [exact EL1n|]. unfold s2, sq_st; destruct (st_seq s1 =? 255); cbn [st_regions set_seq set_unmap_seq]; rewrite Rs1, length_app; cbn; lia. }
  assert (ZR5 : forall x, a <= x < a + plen -> m5 (wa x) = Some (Z_to_bv 8 0)).
  { intros x Hx. rewrite (GROW_region_keep HTOP [] None U0 [mt] None U0 L1 s2 m4 L3 s3 m5 sp0 8192 (length (st_regions s)) _ C4 C5 G5 Hr2 eq_refl eq_refl).
    - destruct Hm4 as [(_ & ->) | (_ & ->)].
      + rewrite MngWb.wbytes_out by (cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_wa_small by lia; clear - Hx Dimg Ha Ha47 Hplr; cbn; lia). apply IN3. exact Hx.
      + rewrite MngWb.wbytes_out by (cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_wa_small by lia; clear - Hx Dimg Ha Ha47 Hplr; cbn; lia).
        rewrite unm0_out by (clear - Hx Dimg Ha Ha47 Hplr; lia). apply IN3. exact Hx.
    - intros q a' H Eq. pose proof (OLD3 q a' H) as H'. rewrite Eq in H'. lia.
    - rewrite EL1n. cbn [rg_len]. exact Hx. }
  (* [comment removed for export] *)
  set (mta := loc_addr L3 (LMem mt)) in *.
  assert (Hmt5 : MT s3 mt = Some MRaw \/ MT s3 mt = Some (MFree None None)) by exact (HX5 mt (or_introl eq_refl)).
  assert (Kmt : In mt (keys s3)) by (destruct Hmt5 as [E'|E']; exact (MT_keys s3 mt _ E')).
  pose proof (nc_mplace _ _ _ _ _ _ _ N5 mt Kmt) as (Pm1 & Pm2 & Pm3 & Pm4). fold mta in Pm1, Pm2, Pm3, Pm4.
  destruct (key_slot_range HTOP [mt] None U0 s3 L3 mt HI5 HG5 Kmt) as (ar & j & rr & rga & Har & Hj & Ear & Epr & Hrr & Hlv & Hkd & A1 & A2 & A3 & A4).
  fold mta in A4.
  assert (Dma : mta + 40 <= a \/ a + plen <= mta).
  { assert (Hne' : rr <> length (st_regions s)) by (intros E; rewrite E in Hrr; rewrite Hr3 in Hrr; injection Hrr as <-; exact (Hkd eq_refl)).
    pose proof (HD5 rr (length (st_regions s)) rga _ Hne' Hrr Hr3 Hlv eq_refl) as D. unfold ranges_disjoint in D. cbn [fst snd rg_len] in D. rewrite Ha3 in D.
    rewrite A4. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - D A2 A3 Hj. lia. }
  pose proof (inv_ctx HI5) as (_ & _ & _ & _ & _ & _ & _ & _ & C9 & _).
  assert (P5' : PCUT HTOP L3 [] s3 m5 sp0 8192) by exact (PCUT_of_CUT HTOP [mt] None U0 L3 s3 m5 sp0 8192 C5).
  assert (Lc3 : forall o, loc_addr L3 (LCtx o) = 621720 + o) by (intros o; cbn [loc_addr]; rewrite (nc_ctx _ _ _ _ _ _ _ N5); reflexivity).
  assert (Mctr5 : rdn SEGS m5 (wa (0 + 621732)) 4 = Some (word_to_le_bytes 4 (wa (st_mmap_counter s3)))).
  { pose proof (nc_ctx_rd L3 s3 m5 sp0 8192 (MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter s3))) N5
                  ltac:(unfold ctx_cells; apply in_app_iff; left; cbn [In]; repeat first [ (left; reflexivity) | right ])
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite Lc3 in H. unfold CTX_mmap_counter in H. exact H. }
  assert (P6 : md2_pre R5 m5 n a mta (st_mmap_counter s3)).
  { constructor.
    - regk R5K 8%nat. exact T8.
    - regk R5K 9%nat. exact T9.
    - exact R5_10.
    - regk R5K 18%nat. exact T18.
    - regk R5K 19%nat. exact T19.
    - regk R5K 20%nat. exact T20.
    - lia.
    - clear - Ha Ha47 Hplr; lia.
    - pose proof (nc_sp2 _ _ _ _ _ _ _ N5) as SP2'. clear - Pm1 Pm2 SP2'; lia.
    - clear - C9; lia.
    - unfold PGSZ in F2'. exact F2'.
    - exact Pm4.
    - intros d k Hd Hk. refine (pc_wr HTOP L3 [] s3 m5 sp0 8192 (LMem ar, PGSZ) P5' _ (mta + 16) 24 _ _ _ _ d k Hd Hk).
      + right. apply in_app_iff. left. apply (in_map (fun a0 => (LMem a0, PGSZ))). exact Har.
      + cbn [fst snd]. rewrite A4. unfold AREA_HDR, META_SIZE. clear - Hj; lia.
      + cbn [fst snd]. rewrite A4. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - Hj; lia.
      + clear - Pm1; lia.
      + pose proof (nc_sp2 _ _ _ _ _ _ _ N5) as SP2'. clear - Pm2 SP2'; lia.
    - intros d k Hd Hk. apply (store_ok_of_bytes SEGS m5 (a + 0) 8); [|exact Hd | exact Hk].
      intros jj Hjj. unfold wview. rewrite (ZR5 (a + 0 + jj)) by (clear - Hjj Hplr; lia). discriminate.
    - clear - Dma Hplr; lia.
    - exact Mctr5.
    - intros d k Hd Hk. replace (0 + 621732 + d) with (621720 + 12 + d) by ring.
      refine (pc_wr HTOP L3 [] s3 m5 sp0 8192 (LCtx 0, CTX_SIZE) P5' (or_introl eq_refl) (621720 + 12) 4 _ _ _ _ d k Hd Hk);
        cbn [fst snd]; rewrite ?Lc3; unfold CTX_SIZE; lia.
    - clear - Pm3 Pm1; lia.
    - clear - Dimg Hplr; lia. }
  destruct (md2_pmd2 R5 m5 rom n a mta (st_mmap_counter s3) P6) as (R6 & M6 & V8 & V9 & V10 & V11 & V18 & V19 & V20 & VK).
  { scs_go; zats. }
  (* [comment removed for export] *)
  set (rN := length (st_regions s)) in *.
  set (ml := plen / 4096) in *.
  assert (Eml : plen = ml * PGSZ).
  { unfold ml, PGSZ. destruct Hpl as (Hpm & _). pose proof (Z.div_mod plen 4096 ltac:(lia)) as Hd. rewrite Hpm in Hd. lia. }
  assert (Hml1 : 1 <= ml) by (unfold ml; apply Z.div_le_lower_bound; lia).
  assert (HI4' : Inv [] (Some (mt, 0)) U0 (dr_s4 mt s3 rN ml) /\ ub_same s3 (dr_s4 mt s3 rN ml)).
  { pose proof (install_direct_spec [] U0 s3 mt rN (mkRegion RkMap plen [] true) ml
                  (fun r0 => Inv [] (Some (mt, 0)) U0 (snd r0) /\ ub_same s3 (snd r0)) HI5 NX5 Hr3 eq_refl eq_refl Eml Hml1
                  ltac:(intros q a' Hu Ep; apply (used_metas_usedX_X [mt] None U0 s3 q a' HI5 XU5) in Hu; pose proof (OLD3 q a' Hu) as H'; rewrite Ep in H'; lia)
                  ltac:(intros s' -> HI' _ UB'; split; [exact HI' | exact UB'])) as IT.
    exact IT. }
  destruct HI4' as (HI4' & UB4').
  assert (HI6 : Inv [] (Some (mt, 0)) U0 (dr_s5 mt s3 rN ml)) by (apply Inv_set_mmap_counter; [exact HI4' | apply land32_range; unfold dr_s4; cbn [st_mmap_counter set_metas]; clear - C9; lia]).
  destruct (cut_direct HTOP L3 s3 m5 R5 sp0 8192 mt n a rN C5 ltac:(lia) Hr3 Ha3 ZR5 HI6) as (C6 & G6 & G56).
  fold mta in C6, G6, G56.
  set (s5 := dr_s5 mt s3 rN ml) in *.
  set (m6 := md2_mem_pmd2 m5 R5 n a mta (st_mmap_counter s3)) in *.
  assert (GTOT : GROW sp0 8192 L s m L3 s5 m6).
  { apply (GROW_trans sp0 8192 L s m L s m2 L3 s5 m6 G02). apply (GROW_trans sp0 8192 L s m2 L1 s1 m3 L3 s5 m6 G3).
    apply (GROW_trans sp0 8192 L1 s1 m3 L1 s2 m4 L3 s5 m6 G4). exact (GROW_trans sp0 8192 L1 s2 m4 L3 s3 m5 L3 s5 m6 G5 G6). }
  (* [comment removed for export] *)
  assert (ND5 : List.NoDup (keys s5)) by exact (proj1 (inv_keys HI6)).
  assert (USED5 : forall q a', In (q, a') (used_metas s5) -> (q = mt /\ a' = direct_am rN ml) \/ In (q, a') (used_metas s)).
  { intros q a' H. unfold used_metas in H. change (st_metas s5) with (mupdate (st_metas s3) mt (MUsed (direct_am rN ml))) in H.
    destruct (used_cov (st_metas s3) mt (direct_am rN ml) q a' H) as [A|A]; [left; exact A|]. right.
    assert (Hu : In (q, a') (used_metas s3)) by exact A.
    apply (used_metas_usedX_X [mt] None U0 s3 q a' HI5 XU5) in Hu. apply EU5 in Hu.
    assert (Hu' : usedX [] s q a') by (unfold usedX, MTX, MT in Hu |- *; cbn [memb] in *; unfold s2, sq_st, s1, dr_s1 in Hu; destruct (st_seq _ =? 255); exact Hu).
    exact (proj2 (used_metas_usedX_X [] None U0 s q a' HW (XNU_nil s)) Hu'). }
  assert (MK6 : markers_hold L3 s5 (bview SEGS m6)).
  { unfold markers_hold. apply Forall_forall. intros c Hc. unfold markers in Hc. apply in_flat_map in Hc as [[q a'] [Hq Hc]]. cbn [snd] in Hc.
    destruct (USED5 q a' Hq) as [(-> & ->) | Hold].
    - unfold meta_markers in Hc. apply in_app_iff in Hc as [Hc|[<-|[]]].
      + exfalso. apply in_flat_map in Hc as [i [Hi Hc]]. apply In_zseq in Hi. cbn [direct_am am_last] in Hi. assert (i = 0) as -> by lia.
        cbn [nth_slot direct_am am_slots Z.to_nat nth slot_zero ss_fr] in Hc. destruct Hc.
      + (* [comment removed for export] *)
        assert (Est : stride_of (direct_am rN ml) = ml * 4096 - 16).
        { unfold stride_of. cbn [direct_am am_last am_maplen]. replace (ml =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
        assert (LK : loc_addr L3 (mc_loc (gend_cell (direct_am rN ml))) = a + plen - 4).
        { cbn [gend_cell mc_loc]. unfold slot_end. rewrite loc_padd. unfold slot_start. rewrite loc_padd. rewrite Est.
          cbn [direct_am am_mem am_last]. change (loc_addr L3 (LMem (SP rN 0))) with (ly_reg L3 rN + 0). rewrite Ha3.
          rewrite Eml. unfold UNIT, IB, PGSZ. ring. }
        unfold gend_cell in LK |- *. cbn [mc_loc] in LK.
        apply (holds_read L3 m6 _ 1 _ 0); [intros z E; discriminate E | lia | rewrite LK; clear - Ha Hplr; lia | rewrite LK; clear - Ha47 Hplr; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
        intros k Hk. assert (k = 0%nat) as -> by lia. rewrite LK, Z.add_0_r.
        unfold m6, md2_mem_pmd2. rewrite !MngWb.wbytes_out by (clear - Dma Dimg Pm1 Pm2 Pm3 Rsp Ha Ha47 Hplr; side2).
        rewrite ZR5 by (clear - Hplr; lia). reflexivity.
    - refine (markers_keep HTOP [] None U0 [] (Some (mt, 0)) U0 L s m L3 s5 m6 sp0 8192 C0 HM C6 GTOT _ c _).
      + intros q' a'' H. destruct (USED5 q' a'' H) as [(-> & ->) | Hold']; [right; cbn [direct_am am_mem prid]; lia | left; exists a''; split; [exact Hold' | apply gshape_refl]].
      + unfold markers. apply in_flat_map. exists (q, a'). split; [exact Hold | exact Hc]. }
  (* [comment removed for export] *)
  pose proof C6 as [HI6' HX6 N6 HG6 HD6 HT6 HTB6].
  assert (C6s : CUT HTOP [] (Some (mt, 0)) U0 L3 s5 m6 (sp0 - 48) (8192 - 48)) by (apply CUT_shift; [exact C6 | lia | reflexivity | lia]).
  assert (Umd : usedX [] s5 mt (direct_am rN ml)) by (apply usedX_intro; [reflexivity | exact (sd_lookup_mt mt rN ml s3)]).
  assert (R6_2 : getr R6 2 = wa (sp0 - 48)) by (regk VK 2%nat; regk R5K 2%nat; exact R4_2).
  assert (OUT6 : forall x, 0 <= x < 2^64 -> ~ (mta + 16 <= x < mta + 40) -> ~ (a <= x < a + 8) -> ~ (621732 <= x < 621736) -> m6 (wa x) = m5 (wa x)).
  { intros x Hx Nx1 Nx2 Nx3. unfold m6, md2_mem_pmd2. rewrite !MngWb.wbytes_out by (clear - Hx Nx1 Nx2 Nx3 Pm1 Pm2 Rsp Ha Ha47 Hplr; side2). reflexivity. }
  assert (M46 : forall x, sp0 - 48 <= x < sp0 -> m6 (wa x) = m1 (wa x)).
  { intros x Hx. rewrite OUT6 by (clear - Hx Pm1 Pm2 Rsp Ha Ha47 Hplr HTB Htop F4'; lia). rewrite ABOVE5 by lia.
    destruct Hm4 as [(_ & ->) | (_ & ->)].
    - rewrite MngWb.wbytes_out by (cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_wa_small by lia; clear - Hx Rsp; cbn; lia).
      rewrite OUT3 by (clear - Hx Rsp F4' HTB Htop; lia). apply M2out; lia.
    - rewrite MngWb.wbytes_out by (cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_wa_small by lia; clear - Hx Rsp; cbn; lia).
      rewrite unm0_out by (clear - Hx Rsp; lia). rewrite OUT3 by (clear - Hx Rsp F4' HTB Htop; lia). apply M2out; lia. }
  assert (FRM6 : forall k (r0 : bvmap 5 word -> word), In (k, r0) [(8, fun R => getr R 1); (16, fun R => getr R 8); (24, fun R => getr R 9);
                  (32, fun R => getr R 18); (40, fun R => getr R 19); (48, fun R => getr R 20)] ->
               rdn SEGS m6 (wa (sp0 - k)) 8 = Some (word_to_le_bytes 8 (r0 regs))).
  { intros k r0 Hk. assert (Rk : 8 <= k <= 48) by (cbn [In] in Hk; repeat (destruct Hk as [E|Hk]; [injection E as <- _; lia|]); destruct Hk).
    rewrite (rdn_frame_n m1 m6 (sp0 - k) 8%nat);
      [| clear - Rk Htop HT20; lia | clear - Rk Hsp47; cbn; lia | intros x Hx; apply M46; cbn [Z.of_nat Pos.of_succ_nat] in Hx; clear - Hx Rk; lia].
    replace (sp0 - k) with (bv_unsigned (getr regs 2) + - k) by (unfold sp0; ring). exact (ma_rdn_save m regs ltac:(lia) k r0 Hk). }
  pose proof GTOT as (HE & RM & _ & SITOT & CHT).
  assert (Mlock6 : rdn SEGS m6 (wa 621712) 4 = Some (word_to_le_bytes 4 (wa 0))).
  { rewrite (rdn_frame_n m m6 621712 4%nat); [exact E6 | lia | cbn; lia |]. intros x Hx. cbn in Hx. apply SITOT; lia. }
  apply (wk_msteps SEGS FORB HTOP rom _ L3 R6 (wa 0x5405c) m6 R5 (wa 0x53ec4) m5 _ M6).
  apply (tail_wk FORB HTOP rom L3 s5 m6 R6 n mt 0 (direct_am rN ml) (sp0 - 48) (8192 - 48)
           (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) _ C6s MK6 Umd ltac:(lia)).
  { unfold stride_of. cbn [direct_am am_last am_maplen]. replace (ml =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb Z.eqb].
    clear - Eml Hpl. unfold PGSZ, UNIT, IB in *. lia. }
  { cbn [direct_am am_sc]. intros H. lia. }
  { cbn [direct_am am_sc am_maplen]. intros _. clear - Eml Hpl Hn. unfold MMAP_THRESHOLD, UNIT, IB, PGSZ in *. lia. }
  { cbn [direct_am am_sc]. intros H. lia. }
  { exact R6_2. }
  { exact V8. }
  { exact V9. }
  { exact V18. }
  { exact V19. }
  { replace (sp0 - 48 + 40) with (sp0 - 8) by ring. exact (FRM6 8 (fun R => getr R 1) ltac:(lmemb)). }
  { replace (sp0 - 48 + 32) with (sp0 - 16) by ring. exact (FRM6 16 (fun R => getr R 8) ltac:(lmemb)). }
  { replace (sp0 - 48 + 24) with (sp0 - 24) by ring. exact (FRM6 24 (fun R => getr R 9) ltac:(lmemb)). }
  { replace (sp0 - 48 + 16) with (sp0 - 32) by ring. exact (FRM6 32 (fun R => getr R 18) ltac:(lmemb)). }
  { replace (sp0 - 48 + 8) with (sp0 - 40) by ring. exact (FRM6 40 (fun R => getr R 19) ltac:(lmemb)). }
  { replace (sp0 - 48 + 0) with (sp0 - 48) by ring. exact (FRM6 48 (fun R => getr R 20) ltac:(lmemb)). }
  { exact Mlock6. }
  intros p s' R m' T.
  assert (K3 : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr R6 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk.
    rewrite (VK k ltac:(clear - Hk; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk)).
    rewrite (R5K k ltac:(clear - Hk; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk)).
    rewrite (TK k ltac:(clear - Hk; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk)).
    destruct (Nat.eq_dec k 21) as [->|Hk21].
    - litr2 S21. apply wa_u.
    - assert (Hk' : In k [3; 4; 5; 6; 7; 12; 13; 14; 15; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat).
      { clear - Hk Hk21. klist Hk. }
      rewrite (SK k Hk').
      rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; clear - Hk E; cbn [In] in Hk; repeat (destruct Hk as [<-|Hk]; [discriminate E|]); destruct Hk).
      rewrite (FK k ltac:(clear - Hk; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk)).
      exact (QK k ltac:(clear - Hk; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk)). }
  assert (UBs : ub_same s s5).
  { apply (ub_same_trans s s3 s5); [apply (ub_same_trans s s2 s3); [apply ub_same_metas; unfold s2, sq_st, s1, dr_s1; destruct (st_seq _ =? 255); reflexivity | exact UB5]|].
    apply (ub_same_trans s3 (dr_s4 mt s3 rN ml) s5 UB4'). apply ub_same_metas. reflexivity. }
  apply (mw_post_of_tail HTOP L3 s5 m6 R6 L s m regs p s' R m' sp0 T R6_2 eq_refl ltac:(lia) K3 HE).
  { apply rgeo_of_A. intros r0 rg Hr Hl. apply (HG6 r0 rg); [unfold region_of in *; rewrite (tl_regions _ _ _ _ _ _ _ _ _ _ _ _ _ _ T) in Hr; exact Hr | exact Hl]. }
  { intros x Hx Hne.
    destruct (CHT x Hx Hne) as [A|[(c & Hc & Hin)|[(r0 & rg & Hr & Hl & Hge & Hxr)|RG]]].
    - left. exact A.
    - right. right. right. exists c. split; [exact Hc|]. unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. exact Hin.
    - assert (Kd' : rg_kind rg = RkMap \/ rg_kind rg <> RkMap) by (destruct (rg_kind rg); first [left; reflexivity | right; discriminate]).
      destruct Kd' as [Kdm|Kdm].
      + right. left. split.
        * exists (LMem (SP r0 0), rg_len rg). split; [exact (footprint_region_In s5 r0 rg Hr Kdm Hl)|]. cbn [fst snd].
          change (loc_addr L3 (LMem (SP r0 0))) with (ly_reg L3 r0 + 0). lia.
        * exact (new_region_not_block HTOP L s L3 s5 r0 rg x HW HG HD Hctx HTB HE RM HG6 HD6 Hr Hl Hge Hxr).
      + right. right. left. exists r0, rg. auto.
    - right. right. left. exact RG. }
  { intros x Hx. exact (in_user_block_ext [] None U0 s s5 L L3 x HW (XNU_nil s) HE UBs ND5 Hx). }
  { exact (tl_fp _ _ _ _ _ _ _ _ _ _ _ _ _ _ T). }
  { exact (tl_regions _ _ _ _ _ _ _ _ _ _ _ _ _ _ T). }
  { rewrite R2w. apply stk_of_wview; [lia | lia | lia|]. intros x Hx.
    assert (ST1 : stk_ok SEGS m1 (wa sp0) 8192) by (intros a0 kk H1 H2; apply (store_ok_mono SEGS kk m m1 a0 M1g); rewrite <- R2w in H1, H2; exact (HSTK a0 kk H1 H2)).
    pose proof C6s as [_ _ N6s _ _ _ _].
    destruct (Z_lt_le_dec x (sp0 - 48)) as [A|A].
    - pose proof (wview_of_stk m6 (sp0 - 48) (8192 - 48) x (nc_stk _ _ _ _ _ _ _ N6s) ltac:(lia) ltac:(lia) ltac:(lia)) as W'.
      intros W''. apply W'. destruct (wview SEGS m6 (wa x)) eqn:Ew; [|reflexivity]. exfalso.
      apply (wview_grows SEGS m6 m' (wa x) (tl_grows _ _ _ _ _ _ _ _ _ _ _ _ _ _ T)); [rewrite Ew; discriminate | exact W''].
    - assert (Em : m' (wa x) = m1 (wa x)).
      { destruct (decide (m' (wa x) = m6 (wa x))) as [E|E].
        - rewrite E. apply M46. lia.
        - exfalso. destruct (tl_chg _ _ _ _ _ _ _ _ _ _ _ _ _ _ T x ltac:(lia) E) as ((e & He & Hxe) & _).
          destruct (footprint_inv s5 e He) as [-> | [(a0 & Ha0 & ->) | (k & rgk & Hk & Kk & Lk & ->)]].
          + cbn [fst snd] in Hxe. change (loc_addr L3 (LCtx 0)) with (ly_ctx L3 + 0) in Hxe. rewrite (nc_ctx _ _ _ _ _ _ _ N6) in Hxe. unfold CTX_SIZE in Hxe. lia.
          + destruct (area_range HTOP [] (Some (mt, 0)) U0 s5 L3 a0 HI6' HG6 Ha0) as (r1 & rg1 & _ & Hr1' & Hl1' & _ & B1' & B2' & _).
            destruct (HG6 r1 rg1 Hr1' Hl1') as (_ & _ & G3' & _). cbn [fst snd] in Hxe. unfold PGSZ in *. lia.
          + destruct (HG6 k rgk Hk Lk) as (_ & _ & G3' & _). cbn [fst snd] in Hxe. change (loc_addr L3 (LMem (SP k 0))) with (ly_reg L3 k + 0) in Hxe. lia. }
      unfold wview. rewrite Em. fold (wview SEGS m1 (wa x)). exact (wview_of_stk m1 sp0 8192 x ST1 ltac:(lia) ltac:(lia) ltac:(lia)). }
Qed.
End DW.
