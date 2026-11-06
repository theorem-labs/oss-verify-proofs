(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngHeap MngWb MngGeoX MngLt MngSurgery MngExc MngNtfM MngNtfS MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngNtfPre MngNtfC MngImage MngCtx MngCtx2 MngShape AxBits AXF_mmwz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_nM AXG_ag0 AXG_ag5 AXG_ag6 AXG_ag7 AXG_asc AXG_mwd0 AXG_mwd1.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngImage OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngShape OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_mmwz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_md2z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_nM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag6 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag7 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_asc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_mwd0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_mwd1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac side2 := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.

(* [comment removed for export] *)
Lemma pnf_reads : forall m (regs : bvmap 5 word) spm ad len prot flags, 2^20 <= spm <= 2^47 ->
  let M := mmw_mem_pnf m regs spm ad len prot flags in
  rdn SEGS M (wa (spm + -8)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))))) /\
  rdn SEGS M (wa (spm + -16)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))))) /\
  rdn SEGS M (wa (spm + -24)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))) /\
  rdn SEGS M (wa (spm + -32)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))))) /\
  rdn SEGS M (wa (spm + -40)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))))) /\
  rdn SEGS M (wa (spm + -48)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))) /\
  rdn SEGS M (wa (spm + -56)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))))).
Proof.
  intros m regs spm ad len prot flags Hs M. unfold M, mmw_mem_pnf.
  split; [|split; [|split; [|split; [|split; [|split]]]]];
    (apply rdn_read8; [lia | lia |]); intros k Hk; rewrite ?MngWb.wbytes_out by (clear - Hk Hs; side2);
    (apply MngWb.wbytes_at_wa; [lia | side2 | rewrite length_N_to_le_bytes; exact Hk]).
Qed.

(* [comment removed for export] *)
Theorem cut_seq : forall HTOP L s1 (m3 m4 : word -> option byte) sp0 K, CUT HTOP [] None U0 L s1 m3 sp0 K ->
  (st_seq s1 <> 255 /\ m4 = wbytes m3 (wa (0 + 615016)) (word_to_le_bytes 1 (wa (st_seq s1 + 1)))) \/
  (st_seq s1 = 255 /\ m4 = wbytes (unm0m m3) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1))) ->
  CUT HTOP [] None U0 L (sq_st s1) m4 sp0 K /\ GROW sp0 K L s1 m3 L (sq_st s1) m4 /\ mem_grows m3 m4.
Proof.
  intros HTOP L s1 m3 m4 sp0 K C Hm.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_repr _ _ _ _ _ _ _ N) as HRx.
  pose proof (inv_ctx HI) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
  assert (E : exists v l, sq_st s1 = set_seq v l /\ 0 <= v <= 255 /\ Inv [] None U0 (sq_st s1) /\
                repr_x L (sq_st s1) (bview SEGS m4) [] /\ mem_grows m3 m4 /\
                (forall x, 0 <= x < 2^64 -> m4 (wa x) <> m3 (wa x) -> 614952 <= x < 614984 \/ x = 615016)).
  { destruct Hm as [(Hs & ->) | (Hs & ->)].
    - exists (st_seq s1 + 1), s1. unfold sq_st. replace (st_seq s1 =? 255) with false by (symmetry; apply Z.eqb_neq; exact Hs).
      split; [reflexivity|]. split; [lia|]. split; [apply Inv_set_seq; [exact HI | lia]|].
      split; [exact (step_seq L [] Hctx s1 m3 (st_seq s1 + 1) 615016 (st_seq s1 + 1) HRx eq_refl eq_refl)|].
      split; [apply wbytes_grows|]. intros x Hx Hne. right.
      pose proof (chg_wbytes m3 615016 (word_to_le_bytes 1 (wa (st_seq s1 + 1))) x ltac:(lia) ltac:(cbn; lia) Hx Hne) as H. cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat] in H. lia.
    - exists 1, (set_unmap_seq (repeat 0 32) s1). unfold sq_st. replace (st_seq s1 =? 255) with true by (symmetry; apply Z.eqb_eq; exact Hs).
      split; [reflexivity|]. split; [lia|].
      split; [apply Inv_set_seq; [|lia]; destruct repeat0_32_range as [A B]; apply Inv_set_unmap_seq; [exact HI | exact A | exact B]|].
      split; [exact (step_seq L [] Hctx _ (unm0m m3) 1 615016 1 (step_unm0 L [] Hctx s1 m3 HRx C3) eq_refl eq_refl)|].
      split; [eapply mem_grows_trans; [|apply wbytes_grows]; unfold unm0m; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|].
      intros x Hx Hne. destruct (decide (unm0m m3 (wa x) = m3 (wa x))) as [E1|E1].
      + right. rewrite <- E1 in Hne. pose proof (chg_wbytes (unm0m m3) 615016 (word_to_le_bytes 1 (wa 1)) x ltac:(lia) ltac:(cbn; lia) Hx Hne) as H.
        cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat] in H. lia.
      + left. exact (chg_unm0 m3 x Hx E1). }
  destruct E as (v & l & Esq & Hv & HI' & HR' & Hg & CHG).
  assert (FR : FRM L s1 sp0 K m3 m4) by (apply (map_frm L s1 sp0 K m3 m4 48 Hctx ltac:(lia)); [intros x Hx Hne; right; exact (CHG x Hx Hne) | exact C2 | exact C3]).
  assert (SH : SHP s1 (sq_st s1)) by (apply SHP_ctx; unfold sq_st; destruct (st_seq s1 =? 255); reflexivity).
  destruct (ctx_seg_finish L [] [] s1 (sq_st s1) m3 m4 sp0 K N HR' ltac:(unfold sq_st; destruct (st_seq s1 =? 255); reflexivity)
              ltac:(unfold sq_st; destruct (st_seq s1 =? 255); reflexivity) Hg FR) as (N' & _ & _).
  split; [|split; [exact (GROW_shape HTOP [] None U0 L s1 m3 (sq_st s1) m4 sp0 K C SH FR) | exact Hg]].
  constructor; [exact HI' | apply XNM_nil | exact N' | | | exact HT | exact HTB].
  - exact (rgeoA_regions HTOP L s1 (sq_st s1) ltac:(unfold sq_st; destruct (st_seq s1 =? 255); reflexivity) HG).
  - exact (rdisj_regions L s1 (sq_st s1) ltac:(unfold sq_st; destruct (st_seq s1 =? 255); reflexivity) HD).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma footprint_dr_s5 : forall mt s3 r ml, footprint (dr_s5 mt s3 r ml) = footprint s3.
Proof.
  intros mt s3 r ml. unfold dr_s5, dr_s4. change (set_metas (mupdate (st_metas s3) mt (MUsed (direct_am r ml))) s3) with (set_meta s3 mt (MUsed (direct_am r ml))).
  rewrite <- (footprint_set_meta s3 mt (MUsed (direct_am r ml))). reflexivity.
Qed.

Section CD.
Context {fx : FPState}.
Variables (HTOP : Z) (L : layout) (s3 : astate) (m5 : word -> option byte) (R5 : bvmap 5 word) (sp0 K : Z) (mt : sptr) (n a : Z) (r : nat).
Local Notation plen := (page_round (n + IB + UNIT)).
Local Notation ml := (plen / 4096).
Local Notation s5 := (dr_s5 mt s3 r ml).
Local Notation amd := (direct_am r ml).
Local Notation mta := (loc_addr L (LMem mt)).
Local Notation m6 := (md2_mem_pmd2 m5 R5 n a mta (st_mmap_counter s3)).

Hypothesis C3 : CUT HTOP [mt] None U0 L s3 m5 sp0 K.
Hypothesis Hn : 131052 <= n <= 2^26.
Hypothesis Hr : region_of s3 r = Some (mkRegion RkMap plen [] true).
Hypothesis Ha : ly_reg L r = a.
Hypothesis ZR : forall x, a <= x < a + plen -> m5 (wa x) = Some (Z_to_bv 8 0).
Hypothesis HI5 : Inv [] (Some (mt, 0)) U0 s5.

#[using="C3 Hn Hr Ha ZR HI5"] Theorem cut_direct : CUT HTOP [] (Some (mt, 0)) U0 L s5 m6 sp0 K /\ GROW sp0 K L s3 m5 L s5 m6 /\ mem_grows m5 m6.
Proof. LiaFast.lf_pins (fun (C3 Hn Hr Ha ZR HI5 : LiaFast.U) => LiaFast.u0).
  pose proof C3 as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2.
  pose proof (nc_K _ _ _ _ _ _ _ N) as HK1. pose proof (nc_repr _ _ _ _ _ _ _ N) as HRx.
  assert (Hpl : plen mod 4096 = 0 /\ n + 20 <= plen <= n + 20 + 4095 /\ plen = (n + 4115) / 4096 * 4096).
  { unfold page_round, PGSZ, IB, UNIT. pose proof (Z.div_mod (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)) as Hd.
    pose proof (Z.mod_pos_bound (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)) as Hb. split; [apply Z.mod_mul; lia|]. split; [lia|].
    f_equal. f_equal. ring. }
  destruct Hpl as (Hpm & Hpr & Hpe).
  destruct (HG r _ Hr eq_refl) as (G1 & G2 & G3 & G4). cbn [rg_len] in G3, G4. rewrite Ha in G1, G2, G3, G4. unfold PGSZ in G1, G2.
  unfold ranges_disjoint in G4. cbn [fst snd] in G4.
  (* [comment removed for export] *)
  assert (Hmt : MT s3 mt = Some MRaw \/ MT s3 mt = Some (MFree None None)) by exact (HX mt (or_introl eq_refl)).
  assert (Hraw : forall am', mlookup (st_metas s3) mt <> Some (MUsed am')).
  { intros am' E. change (mlookup (st_metas s3) mt) with (MT s3 mt) in E. destruct Hmt as [E'|E']; rewrite E' in E; discriminate E. }
  assert (Hkey : In mt (keys s3)) by (destruct Hmt as [E'|E']; exact (MT_keys s3 mt _ E')).
  pose proof (nc_mplace _ _ _ _ _ _ _ N mt Hkey) as (Pm1 & Pm2 & Pm3 & Pm4).
  destruct (key_slot_range HTOP [mt] None U0 s3 L mt HI HG Hkey) as (ar & j & rr & rga & Har & Hj & Ear & Epr & Hrr & Hlv & Hkd & A1 & A2 & A3 & A4).
  assert (Hne : rr <> r) by (intros E; rewrite E in Hrr; rewrite Hr in Hrr; injection Hrr as <-; exact (Hkd eq_refl)).
  assert (Dma : mta + 40 <= a \/ a + plen <= mta).
  { pose proof (HD rr r rga _ Hne Hrr Hr Hlv eq_refl) as D. unfold ranges_disjoint in D. cbn [fst snd rg_len] in D. rewrite Ha in D. rewrite A4.
    unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - D A2 A3 Hj. lia. }
  assert (Ha47 : a + plen <= 2^47) by (clear - G3 HTB; lia).
  assert (Hmta47 : mta + 40 <= 2^47) by (clear - Pm2 Hsp2 HK1; lia).
  assert (Dimg : a + plen <= 0x10000 \/ 0x97000 <= a) by (clear - G4; lia).
  assert (Lc : forall o, loc_addr L (LCtx o) = 614104 + o) by (intros o; cbn [loc_addr]; rewrite Hctx; reflexivity).
  assert (LP : forall d, loc_addr L (LMem (padd mt d)) = mta + d) by (intros d; rewrite loc_padd; reflexivity).
  assert (LR : forall d, loc_addr L (LMem (SP r d)) = a + d) by (intros d; cbn [loc_addr prid poff]; rewrite Ha; reflexivity).
  assert (KS5 : KS s5) by exact (KS_of_Inv [] (Some (mt, 0)) U0 s5 HI5).
  assert (G56 : mem_grows m5 m6) by (unfold md2_mem_pmd2; do 6 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  assert (OUT6 : forall x, 0 <= x < 2^64 -> ~ (mta + 16 <= x < mta + 40) -> ~ (a <= x < a + 8) -> ~ (614116 <= x < 614120) -> m6 (wa x) = m5 (wa x)).
  { intros x Hx N1 N2 N3. unfold md2_mem_pmd2. rewrite !MngWb.wbytes_out by (clear - Hx N1 N2 N3 Pm1 Hmta47 G1 Ha47 Hpr Hn; side2). reflexivity. }
  assert (CG : CUT HTOP [] (Some (mt, 0)) U0 L s5 m6 sp0 K /\ GROW sp0 K L s3 m5 L s5 m6).
  { apply (silent_step' HTOP [mt] None U0 [] (Some (mt, 0)) U0 L s3 s5 m5 m6 sp0 K (CnewD mt r ml s3) C3); [exact HI5 | apply XNM_nil | | | | | | | | | | ].
    - exact (rgeoA_regions HTOP L s3 s5 (sd_regions mt r ml s3) HG).
    - exact (rdisj_regions L s3 s5 (sd_regions mt r ml s3) HD).
    - exact (RMONO_regions s3 s5 (sd_regions mt r ml s3)).
    - intros f Hf. left. rewrite footprint_dr_s5 in Hf. exact Hf.
    - intros c Hc. exact (covD mt r ml s3 c Hc).
    - exact (inD mt r ml s3 KS5).
    - intros c Hc. exact (revD mt r ml s3 Hraw L c Hc).
    - (* [comment removed for export] *)
      set (BITS := 4096 * Z.shiftr ((n + 4115) mod 2^64) 12 + 4064).
      assert (RD : (forall k, (k < 8)%nat -> m6 (wa (mta + 16 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa a)) (Z_to_bv 8 0))) /\
                   (forall k, (k < 8)%nat -> m6 (wa (a + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa mta)) (Z_to_bv 8 0))) /\
                   (forall k, (k < 8)%nat -> m6 (wa (mta + 32 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa BITS)) (Z_to_bv 8 0))) /\
                   (forall k, (k < 4)%nat -> m6 (wa (mta + 28 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa 0)) (Z_to_bv 8 0))) /\
                   (forall k, (k < 4)%nat -> m6 (wa (mta + 24 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa 0)) (Z_to_bv 8 0))) /\
                   (forall k, (k < 4)%nat -> m6 (wa (0 + 614116 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa (AX2.ext_Z true 0 4 (st_mmap_counter s3) + 1))) (Z_to_bv 8 0)))).
      { unfold md2_mem_pmd2. split; [|split; [|split; [|split; [|split]]]].
        all: intros k Hk; rewrite ?MngWb.wbytes_out by (clear - Hk Pm1 Pm3 Hmta47 G1 Ha47 Dma Dimg Hpr Hn; side2);
               apply MngWb.wbytes_at_wa; [clear - Pm1 G1; lia | side2 | rewrite length_N_to_le_bytes; exact Hk]. }
      destruct RD as (RM16 & RA0 & RM32 & RM28 & RM24 & RC).
      assert (ZB : forall x, a + 8 <= x < a + 16 -> m6 (wa x) = Some (Z_to_bv 8 0)).
      { intros x Hx. rewrite OUT6 by (clear - Hx Dma Dimg G1 Ha47 Hpr Hn; lia). apply ZR. lia. }
      assert (Z0 : forall w k, (k < w)%nat -> nth k (word_to_le_bytes w (wa 0)) (Z_to_bv 8 0) = Z_to_bv 8 0).
      { intros w k Hk. unfold word_to_le_bytes. rewrite u_wa_small by lia. revert k Hk. induction w as [|w IH]; intros k Hk; [lia|].
        destruct k as [|k]; [reflexivity|]. cbn [Z_to_le_bytes nth]. rewrite Z.shiftr_0_l. apply IH. lia. }
      (* [comment removed for export] *)
      assert (RAWC : forall d, d = 0 \/ d = 8 -> cell_holds L (bview SEGS m6) (MCell (LMem (padd mt d)) 8 (VZ 0))).
      { intros d Hd. assert (Hc : In (MCell (LMem (padd mt d)) 8 (VZ 0)) (image s3)).
        { destruct Hmt as [E0|E0]; apply (msc_key_in_image s3 mt _ _ (KS_of_Inv [mt] None U0 s3 HI) E0); cbn [meta_slot_cells optr];
            destruct Hd as [-> | ->]; cbn [In]; unfold META_prev, META_next; repeat first [ (left; reflexivity) | right ]. }
        pose proof (repr_x_holds L s3 (bview SEGS m5) [] _ HRx Hc (fun H => H)) as HH.
        apply (cell_holds_frame L (bview SEGS m5) (bview SEGS m6) (MCell (LMem (padd mt d)) 8 (VZ 0)) ltac:(cbn; lia) HH). intros x Hx. apply MngWb.bview_ext.
        unfold in_rng, cell_range in Hx. cbn [mc_loc mc_w fst snd] in Hx. rewrite LP in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
        apply OUT6; clear - Hx Hd Pm1 Pm3 Hmta47 Dma Dimg G1 Ha47 Hpr Hn; lia. }
      assert (EML : ml = (n + 4115) / 4096) by (rewrite Hpe; rewrite Z.div_mul by lia; reflexivity).
      assert (EBITS : BITS = meta_bits amd).
      { unfold BITS, meta_bits, direct_am. cbn [am_last am_sc am_maplen]. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
        rewrite EML. ring. }
      unfold CnewD. cbn [app]. apply Forall_cons; [|apply Forall_app; split].
      + unfold ctr_cell. apply (holds_read L m6 _ 4 _ (AX2.ext_Z true 0 4 (st_mmap_counter s3) + 1)); [intros z E; discriminate E | lia | rewrite Lc; unfold CTX_mmap_counter; lia
                                                                                       | rewrite Lc; unfold CTX_mmap_counter; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        * cbn [sval_num]. unfold dr_s5. cbn [st_mmap_counter set_mmap_counter]. change (8 * Z.of_nat 4) with 32.
          change (2^32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_mod by lia.
          unfold dr_s4. cbn [st_mmap_counter set_metas]. unfold AX2.ext_Z. cbn [Z.of_nat N.of_nat Pos.of_succ_nat]. rewrite Z.pow_0_r, Z.div_1_r.
          rewrite Z.add_mod by lia. rewrite swrap32_mod. rewrite Z.mod_mod by lia. rewrite <- Z.add_mod by lia. reflexivity.
        * intros k Hk. rewrite Lc. unfold CTX_mmap_counter. replace (614104 + 12 + Z.of_nat k) with (0 + 614116 + Z.of_nat k) by ring. exact (RC k Hk).
      + cbn [meta_slot_cells direct_am am_prev am_next am_mem am_avail am_freed optr].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]].
        * unfold META_prev. exact (RAWC 0 (or_introl eq_refl)).
        * unfold META_next. exact (RAWC 8 (or_intror eq_refl)).
        * apply (holds_read L m6 _ 8 _ a); [intros z E; discriminate E | lia | rewrite LP; unfold META_mem; lia | rewrite LP; unfold META_mem; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
          { cbn [sval_num]. rewrite LR. rewrite Z.add_0_r. reflexivity. }
          { intros k Hk. rewrite LP. unfold META_mem. exact (RM16 k Hk). }
        * apply (holds_read L m6 _ 4 _ 0); [intros z E; discriminate E | lia | rewrite LP; unfold META_avail; lia | rewrite LP; unfold META_avail; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
          intros k Hk. rewrite LP. unfold META_avail. exact (RM24 k Hk).
        * apply (holds_read L m6 _ 4 _ 0); [intros z E; discriminate E | lia | rewrite LP; unfold META_freed; lia | rewrite LP; unfold META_freed; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
          intros k Hk. rewrite LP. unfold META_freed. exact (RM28 k Hk).
        * apply (holds_read L m6 _ 8 _ BITS); [intros z E; discriminate E | lia | rewrite LP; unfold META_bits; lia | rewrite LP; unfold META_bits; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
          { cbn [sval_num]. rewrite EBITS. reflexivity. }
          { intros k Hk. rewrite LP. unfold META_bits. exact (RM32 k Hk). }
      + unfold group_cells. cbn [direct_am am_mem am_maplen am_aidx am_last].
        replace (ml =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite EML; assert (1 <= (n + 4115) / 4096) by (apply Z.div_le_lower_bound; lia); lia).
        apply Forall_cons; [|apply Forall_cons; [|]].
        * apply (holds_read L m6 _ 8 _ mta); [intros z E; discriminate E | lia | rewrite LR; lia | rewrite LR; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
          intros k Hk. rewrite LR. exact (RA0 k Hk).
        * apply (holds_read L m6 _ 4 _ 0); [intros z E; discriminate E | lia | rewrite loc_padd, LR; lia | rewrite loc_padd, LR; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
          intros k Hk. rewrite loc_padd, LR. rewrite ZB by lia. rewrite (Z0 4%nat k Hk). reflexivity.
        * replace (zseq 0 (0 + 1)) with [0] by reflexivity. cbn [flat_map]. rewrite app_nil_r.
          assert (LS : forall d, loc_addr L (LMem (padd (slot_start amd 0) d)) = a + 16 + d).
          { intros d. rewrite loc_padd. unfold slot_start. rewrite loc_padd. cbn [direct_am am_mem]. rewrite LR. unfold UNIT. ring. }
          unfold slot_cells. cbn [nth_slot direct_am am_slots Z.to_nat nth slot_zero ss_hdr ss_fr app].
          apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
          { apply (holds_read L m6 _ 1 _ 0); [intros z E; discriminate E | lia | rewrite LS; lia | rewrite LS; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
            intros k Hk. rewrite LS. rewrite ZB by (cbn [Z.of_nat Pos.of_succ_nat] in *; lia). rewrite (Z0 1%nat k Hk). reflexivity. }
          { apply (holds_read L m6 _ 1 _ 0); [intros z E; discriminate E | lia | rewrite LS; lia | rewrite LS; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
            intros k Hk. rewrite LS. rewrite ZB by (cbn [Z.of_nat Pos.of_succ_nat] in *; lia). rewrite (Z0 1%nat k Hk). reflexivity. }
          { apply (holds_read L m6 _ 2 _ 0); [intros z E; discriminate E | lia | rewrite LS; lia | rewrite LS; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
            intros k Hk. rewrite LS. rewrite ZB by (cbn [Z.of_nat Pos.of_succ_nat] in *; lia). rewrite (Z0 2%nat k Hk). reflexivity. }
    - exact G56.
    - (* [comment removed for export] *)
      intros x Hx Hnx. right.
      assert (INM : forall c, In c (meta_slot_cells mt (Some (MUsed amd))) -> In c (CnewD mt r ml s3)).
      { intros c Hc. unfold CnewD. apply in_app_iff. right. apply in_app_iff. left. exact Hc. }
      assert (ING : forall c, In c (group_cells mt amd) -> In c (CnewD mt r ml s3)).
      { intros c Hc. unfold CnewD. apply in_app_iff. right. apply in_app_iff. right. exact Hc. }
      destruct (range_dec x (mta + 16) 24) as [M|M].
      + destruct (range_dec x (mta + 16) 8) as [M1|M1].
        { eexists. split; [apply INM; cbn [meta_slot_cells In]; right; right; left; reflexivity|].
          unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_mem. cbn [Z.of_nat Pos.of_succ_nat]. clear - M1; lia. }
        destruct (range_dec x (mta + 24) 4) as [M2|M2].
        { eexists. split; [apply INM; cbn [meta_slot_cells In]; right; right; right; left; reflexivity|].
          unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_avail. cbn [Z.of_nat Pos.of_succ_nat]. clear - M2; lia. }
        destruct (range_dec x (mta + 28) 4) as [M3|M3].
        { eexists. split; [apply INM; cbn [meta_slot_cells In]; right; right; right; right; left; reflexivity|].
          unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_freed. cbn [Z.of_nat Pos.of_succ_nat]. clear - M3; lia. }
        eexists. split; [apply INM; cbn [meta_slot_cells In]; right; right; right; right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_bits. cbn [Z.of_nat Pos.of_succ_nat]. clear - M M1 M2 M3; lia.
      + destruct (range_dec x a 8) as [A|A].
        { eexists. split; [apply ING; unfold group_cells; left; reflexivity|].
          unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd direct_am am_mem]. rewrite LR. cbn [Z.of_nat Pos.of_succ_nat]. clear - A; lia. }
        destruct (range_dec x 614116 4) as [Cc|Cc].
        { exists (ctr_cell (st_mmap_counter s5)). split; [unfold CnewD; left; reflexivity|].
          unfold in_rng, cell_range, ctr_cell. cbn [mc_loc mc_w fst snd]. rewrite Lc. unfold CTX_mmap_counter. cbn [Z.of_nat Pos.of_succ_nat]. clear - Cc; lia. }
        exfalso. apply Hnx. apply OUT6; [exact Hx | clear - M; lia | clear - A; lia | clear - Cc; lia]. }
  destruct CG as (CC & GG). split; [exact CC|]. split; [exact GG | exact G56].
Qed.
End CD.

(* [comment removed for export] *)
Lemma GROW_region_keep : forall HTOP X R U X' R' U' L s m L' s' m' sp0 K r rg,
  CUT HTOP X R U L s m sp0 K -> CUT HTOP X' R' U' L' s' m' sp0 K -> GROW sp0 K L s m L' s' m' ->
  region_of s r = Some rg -> rg_live rg = true -> rg_kind rg = RkMap ->
  (forall q a', In (q, a') (used_metas s') -> prid (am_mem a') <> r) ->
  forall x, ly_reg L r <= x < ly_reg L r + rg_len rg -> m' (wa x) = m (wa x).
Proof.
  intros HTOP X R U X' R' U' L s m L' s' m' sp0 K r rg C C' GR Hr Hl Hk NOG x Hx.
  pose proof C as [HI HX N HG HD HT HTB]. pose proof C' as [HI' HX' N' HG' HD' HT' HTB'].
  pose proof (XNU_of_XNM X' s' HX') as XU'. pose proof (nc_ctx _ _ _ _ _ _ _ N') as Hctx'.
  pose proof GR as (HE & RM & _ & _ & CH).
  assert (Hlt : (r < length (st_regions s))%nat) by exact (region_of_lt s r rg Hr).
  pose proof RM as (Rlen & RMl). destruct (RMl r rg Hr Hl) as (rg' & Hr' & Lr' & Kr' & Len').
  destruct (HG r rg Hr Hl) as (B1 & _ & B3 & B4). unfold ranges_disjoint in B4. cbn [fst snd] in B4.
  assert (ELr : ly_reg L' r = ly_reg L r) by exact (proj2 (proj2 (proj2 HE)) r Hlt).
  assert (Hx64 : 0 <= x < 2^64) by (unfold PGSZ in *; lia).
  destruct (decide (m' (wa x) = m (wa x))) as [E|Hne]; [exact E|]. exfalso.
  assert (OTHER : forall r2 rg2, region_of s' r2 = Some rg2 -> rg_live rg2 = true -> r2 <> r ->
                    ly_reg L' r2 <= x < ly_reg L' r2 + rg_len rg2 -> False).
  { intros r2 rg2 Hr2 Hl2 Hne2 Hx2. pose proof (HD' r2 r rg2 rg' Hne2 Hr2 Hr' Hl2 Lr') as D. unfold ranges_disjoint in D. cbn [fst snd] in D.
    rewrite ELr in D. lia. }
  destruct (CH x Hx64 Hne) as [A | [(c' & Hc' & Hin) | [(r2 & rg2 & Hr2 & Hl2 & Hge & Hx2) | (r2 & rg2 & Hr2 & Hl2 & Hk2 & Hx2)]]].
  - lia.
  - destruct (In_image_inv s' c' Hc') as [Hcx | [(a0 & next & Ha0 & Hca) | (g' & a' & Hg' & Hcg)]].
    + destruct (In_ctx_cells s' c' Hcx) as (off & E & Ho & Hw). unfold in_rng, cell_range in Hin. rewrite E in Hin. cbn [fst snd loc_addr] in Hin.
      rewrite Hctx' in Hin. unfold CTX_SIZE in Hw. lia.
    + destruct (In_area_cells s' a0 next c' Hca) as (d & E & Hd & Hw).
      destruct (area_range HTOP X' R' U' s' L' a0 HI' HG' Ha0) as (ra & rga & Ea0 & Hra & Hla & Hka & A1 & A2 & _ & _).
      apply (OTHER ra rga Hra Hla).
      * intros Eq. rewrite Eq in Hra. rewrite Hr' in Hra. injection Hra as <-. exact (Hka (eq_trans Kr' Hk)).
      * unfold in_rng, cell_range in Hin. rewrite E, loc_padd in Hin. cbn [fst snd] in Hin. unfold PGSZ in *. lia.
    + apply (used_metas_usedX_X X' R' U' s' g' a' HI' XU') in Hg' as Ug'.
      destruct (group_cell_home_X L' X' R' U' s' g' a' c' HI' Ug' Hcg) as (rgn & Hrn & Hkn & Hln & _ & Incl).
      apply (OTHER (prid (am_mem a')) rgn Hrn Hln (NOG g' a' Hg')).
      unfold range_incl, in_rng, cell_range, crange in *. cbn [fst snd] in *. cbn [loc_addr prid poff] in Incl. lia.
  - apply (OTHER r2 rg2 Hr2 Hl2 ltac:(lia) Hx2).
  - apply (OTHER r2 rg2 Hr2 Hl2); [|exact Hx2]. intros Eq. rewrite Eq in Hr2. rewrite Hr' in Hr2. injection Hr2 as <-. exact (Hk2 (eq_trans Kr' Hk)).
Qed.
