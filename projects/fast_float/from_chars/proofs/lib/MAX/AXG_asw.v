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
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfArith MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngHeap MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfM MngNtfS MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngMW2 MngMW3 MngNtfPre MngCtx MngCtx2 MngShape MngMK AXG_as1 AXG_as5 AXG_as7 AXG_asc AXG_am1 AXG_am5 AXG_am8 AXG_amw.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_ag0 AXG_ag1 AXG_ag7 AXG_asq AXG_ag14 AXG_ag16 AXG_asw0.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngShape OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMK OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as7 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_asc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am8 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amw OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1.AXF_agmz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag7 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_asq OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag14 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag16 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_asw0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section ASW.
Context {fx : FPState}.
Variable FORB : list (Z * Z).
Hypothesis HFORB : forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB -> ranges_disjoint (a, n) (0x10000, 0x87000).

(* [comment removed for export] *)
Definition as_wpost (UB0 : Z -> Prop) (HTOP : Z) (X : list sptr) (U : Z -> Z) (L0 : layout) (s0 : astate) (m0 : word -> option byte)
    (regs0 : bvmap 5 word) (sp0 K sc : Z) : @wpost (Z * astate) :=
  fun L' r R' pc m' => exists idx s' g, r = (idx, s') /\ 0 <= idx /\ pc = wa 0x52b8c /\ getr R' 10 = wa idx /\
    (forall k, In k callee_as -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) /\
    (Inv X (Some (g, idx)) U s' ->
       CUT HTOP X (Some (g, idx)) U L' s' m' sp0 K /\ GROWX UB0 sp0 K L0 s0 m0 L' s' m' /\ markers_hold L' s' (bview SEGS m')) /\
    active_hd s' sc = Some g /\ UGROW s0 s' sc.

#[using="HFORB"] Lemma as_wk_step : forall fuel, (forall f, (f < fuel)%nat -> as_wk_f FORB f) -> as_wk_f FORB fuel.
Proof. LiaFast.lf_pins (fun (HFORB : LiaFast.U) => LiaFast.u0).
  intros fuel IHf UB0 HTOP X U L s m regs rom sp0 K sc req C MK HKAS Hsc Hreq Hfit Hf R2 R10 R11 UB Mdb TB Mpg B1 B2 B3 Hin UBI.
  pose proof (need_ge2 sc) as Hn2.
  destruct fuel as [|fuel]; [lia|].
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (XNU_of_XNM X s HX) as XU.
  pose proof (class_size_bounds sc Hsc) as (CS1 & CS2).
  assert (W : wk SEGS FORB HTOP rom L regs (wa 0x522f0) m (alloc_slot (S fuel) sc req s) (as_wpost UB0 HTOP X U L s m regs sp0 K sc)).
  { destruct (as_cut HTOP X U L s m regs rom sp0 K sc req fuel C Hsc R2 R10 R11 ltac:(clear - Hreq Hfit CS2; unfold IB in *; lia) Mdb)
      as (R1 & m1 & first & s1 & Et & Mdb1 & G1 & Gm1 & Hoth & UB1 & BR).
    assert (SH : SHP s s1) by exact (try_avail_shape sc s first s1 Et).
    pose proof SH as (_ & Ereg1 & _ & Eus1 & Ein1).
    destruct BR as [(g & am & Hf0 & C1 & Hhd1 & U1 & Sc1 & Str1 & Hidx1 & Hms1 & R1_10 & R1K & Eas) | (Hf0 & C1 & Hhd1 & Hms1 & (can & F1) & R1K & Eas)].
    - (* [comment removed for export] *)
      rewrite Eas. exists R1, (wa 0x52b8c), m1. split; [exact Hms1|].
      unfold as_wpost. exists (ctz32 first), s1, g. split; [reflexivity|]. split; [clear - Hidx1; lia|]. split; [reflexivity|].
      split; [exact R1_10|]. split; [exact R1K|].
      split; [|split; [exact Hhd1 | exact (UGROW_same s s1 sc Eus1)]].
      intros _. split; [exact C1|]. split; [exact (GROWX_of_GROW UB0 sp0 K L s m L s1 m1 G1)|].
      unfold markers_hold. apply Forall_forall. intros c Hc. rewrite (markers_shape s s1 SH) in Hc.
      exact (markers_keep HTOP X None U X (Some (g, ctz32 first)) U L s m L s1 m1 sp0 K C MK C1 G1
               (fun q a' H => or_introl (used_shape s s1 SH q a' H)) c Hc).
    - (* [comment removed for export] *)
      rewrite Eas. destruct fuel as [|f]; [clear - Hf Hn2; lia|].
      rewrite as_group_eq, alloc_group_S.
      apply (wk_msteps SEGS FORB HTOP rom _ L R1 (wa 0x524d0) m1 regs (wa 0x522f0) m _ Hms1).
      pose proof C1 as [HI1 HX1 N1 HG1 HD1 HT1 HTB1].
      pose proof (XNU_of_XNM X s1 HX1) as XU1.
      pose proof F1 as [A2 A8 A18 A20 A21 A22 A23 Hsp Asp Hsc' Hreq' Hcan Hra Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9
                        Fra Fs0 Fs1 Fs2 Fs3 Fs4 Fs5 Fs6 Fs7 Fs8 Fs9 Fcan Fgd].
      pose proof (nc_env _ _ _ _ _ _ _ N1) as HENV1. pose proof (nc_K _ _ _ _ _ _ _ N1) as HK1. pose proof (nc_stk _ _ _ _ _ _ _ N1) as HSTK1.
      pose proof (nc_sp1 _ _ _ _ _ _ _ N1) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N1) as Hsp2. pose proof (nc_sp3 _ _ _ _ _ _ _ N1) as Hsp3.
      assert (HK1584 : 1584 <= K) by (unfold KAS in HKAS; clear - HKAS Hn2; lia).
      (* [comment removed for export] *)
      pose proof (size_classes_range sc Hsc) as Hun.
      destruct (agm_pagm R1 m1 rom sc (znth sc size_classes)
                  ltac:(constructor; [exact A8 | clear - Hsc; lia | clear - Hun; lia | replace (2 * sc + 98984) with (98984 + 2 * sc) by ring; exact (proj1 (proj2 HENV1) sc Hsc)])
                  ltac:(constructor))
        as (R1a & Hmsa & Q1 & Q8 & Q10 & Q19 & Q24 & Q25 & QK).
      unfold agm_mem_pagm in Hmsa.
      apply (wk_msteps SEGS FORB HTOP rom _ L R1a (wa 0x51ca8) m1 R1 (wa 0x524d0) m1 _ Hmsa).
      apply wk_ibind. apply wk_ibind.
      (* [comment removed for export] *)
      assert (C1s : CUT HTOP X None U L s1 m1 (sp0 - 144) (K - 144)) by (apply CUT_shift; [exact C1 | lia | reflexivity | lia]).
      assert (R1a_2 : getr R1a 2 = wa (sp0 - 144)) by (regk QK 2%nat; litr2 A2; f_equal; ring).
      assert (HINIT1 : st_init_done s1 = true \/ AMI L m1 (sp0 - 144)).
      { destruct Hin as [H|H]; [left; rewrite Ein1; exact H|]. right. apply (AMI_mono L m1 sp0); [lia|].
        exact (AMI_GROW HTOP X None U L s m L s1 m1 sp0 K C1 G1 H). }
      pose proof G1 as (_ & _ & _ & SI1 & _).
      assert (Mpg1 : rdn SEGS m1 (wa 614032) 8 = Some (word_to_le_bytes 8 (wa 4096))) by (rewrite (rdn_SI m m1) by (first [exact SI1 | cbn; lia]); exact Mpg).
      pose proof (am_wk FORB HFORB HTOP X None U L s1 m1 R1a rom (sp0 - 144) (K - 144) 0x524e8 C1s ltac:(lia) R1a_2 Q1 (or_introl eq_refl) Mpg1 B1 B2 B3 HINIT1) as AW.
      set (QMa := fun r : option sptr * astate => match fst r with None => True | Some mt =>
                    Inv (mt :: X) None U (snd r) /\ memb mt X = false /\ MallocWfMeta.am_frame s1 (snd r) /\
                    (forall g am, usedX (mt :: X) (snd r) g am <-> usedX X s1 g am) /\ ub_same s1 (snd r) end).
      pose proof (wk_itok SEGS FORB HTOP rom _ L R1a (wa 0x51ca8) m1 _ QMa AW
                    (alloc_meta_spec X None U s1 QMa HI1 (fun s' _ _ _ _ => I) (fun mt s' H1 H2 _ _ H5 H6 H7 => conj H1 (conj H2 (conj H5 (conj H6 H7)))))) as AW2.
      pose proof (wk_itok SEGS FORB HTOP rom _ L R1a (wa 0x51ca8) m1 _ _ AW2 (alloc_meta_init X None U s1 HI1)) as AW3.
      eapply wk_mono; [| exact AW3].
      intros L2 r R2' pc2 m2 ((AQ & AMS) & AIN).
      destruct AQ as (mt & s2 & -> & -> & R2_10 & R2K & C2s & G2s).
      cbn [fst snd QMa] in AMS, AIN. destruct AMS as (HI2 & NX2 & Fr2 & EU2 & UB2).
      pose proof Fr2 as (Eac2 & Eus2 & _ & _ & _).
      (* [comment removed for export] *)
      assert (ABOVE2 : forall x, sp0 - 144 <= x < 2^64 -> m2 (wa x) = m1 (wa x))
        by exact (GROWX_above (fun _ => False) HTOP (mt :: X) None U L s1 m1 L2 s2 m2 (sp0 - 144) (K - 144) (GROWX_of_GROW _ _ _ _ _ _ _ _ _ G2s) C2s).
      assert (STK2 : stk_ok SEGS m2 (wa sp0) K).
      { pose proof C2s as [_ _ N2s _ _ _ _].
        apply (stk_ok_join m1 m2 sp0 K 144); [exact (nc_stk _ _ _ _ _ _ _ N2s) | exact HSTK1 | intros x Hx; apply ABOVE2; lia | lia | lia]. }
      assert (C2 : CUT HTOP (mt :: X) None U L2 s2 m2 sp0 K) by exact (CUT_unshift HTOP (mt :: X) None U L2 s2 m2 sp0 K 144 C2s ltac:(lia) STK2 Hsp2 Hsp3).
      assert (G2 : GROW sp0 K L s1 m1 L2 s2 m2) by exact (GROW_unshift sp0 K 144 L s1 m1 L2 s2 m2 G2s ltac:(lia)).
      assert (G02 : GROW sp0 K L s m L2 s2 m2) by exact (GROW_trans sp0 K L s m L s1 m1 L2 s2 m2 G1 G2).
      pose proof G02 as (HE02 & _ & _ & SI02 & _). pose proof G2 as (_ & _ & _ & SI12 & _).
      pose proof C2 as [_ HX2 N2 HG2 HD2 HT2 HTB2]. pose proof (XNU_of_XNM (mt :: X) s2 HX2) as XU2.
      (* [comment removed for export] *)
      assert (MK1 : markers_hold L s1 (bview SEGS m1)).
      { unfold markers_hold. apply Forall_forall. intros c Hc. rewrite (markers_shape s s1 SH) in Hc.
        exact (markers_keep HTOP X None U X None U L s m L s1 m1 sp0 K C MK C1 G1 (fun q a' H => or_introl (used_shape s s1 SH q a' H)) c Hc). }
      assert (MK2 : markers_hold L2 s2 (bview SEGS m2)).
      { unfold markers_hold. apply Forall_forall. intros c Hc.
        pose proof (used_after_am X None U s1 s2 mt HI1 XU1 HI2 XU2 EU2) as UA.
        exact (markers_keep HTOP X None U (mt :: X) None U L s1 m1 L2 s2 m2 sp0 K C1 MK1 C2 G2
                 (fun q a' H => or_introl (ex_intro _ a' (conj (UA q a' H) (gshape_refl a')))) c (markers_incl s1 s2 UA c Hc)). }
      (* [comment removed for export] *)
      assert (EK : forall k, In k [2; 8; 18; 20; 21; 22; 23]%nat -> getr R2' (Z_to_bv 5 (Z.of_nat k)) = getr R1 (Z_to_bv 5 (Z.of_nat k))).
      { intros k Hk. rewrite (R2K k ltac:(clear - Hk; klist Hk)). destruct (Nat.eq_dec k 8) as [->|Hk8].
        - litr2 Q8. symmetry. litr2 A8. reflexivity.
        - apply QK. clear - Hk Hk8. klist Hk. }
      pose proof (as_frame_regs R1 R2' m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (as_frame_mem R1 m1 m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 ltac:(intros x Hx; apply ABOVE2; lia) ltac:(intros x Hx; apply SI12; lia)) EK) as F2.
      assert (Hhd2 : active_hd s2 sc = None) by (unfold active_hd; rewrite Eac2; exact Hhd1).
      assert (Eus02 : st_usage s2 = st_usage s) by (rewrite Eus2; exact Eus1).
      assert (UB2' : forall c, 0 <= c < 48 -> usage_of s2 c < 2^40) by (intros c Hc; unfold usage_of, znth; rewrite Eus02; exact (UB c Hc)).
      assert (TB2 : TABS m2) by exact (TABS_SI m m2 SI02 TB).
      assert (Mdb2 : DBT m2) by exact (DBT_SI m m2 SI02 Mdb).
      assert (Mpg2 : rdn SEGS m2 (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096))) by (rewrite (rdn_SI m m2) by (first [exact SI02 | cbn; lia]); exact Mpg).
      assert (NX2' : ~ In mt X) by exact (proj1 (memb_false_notIn mt X) NX2).
      assert (R2_19 : getr R2' 19 = wa (2 * sc)) by (regk R2K 19%nat; exact Q19).
      assert (R2_24 : getr R2' 24 = wa (znth sc size_classes)) by (regk R2K 24%nat; exact Q24).
      assert (R2_25 : getr R2' 25 = wa 98984) by (regk R2K 25%nat; exact Q25).
      assert (UBI2 : forall x, UB0 x -> in_user_block L2 s2 x)
        by (intros x Hx; exact (in_user_block_ext X None U s s2 L L2 x HI XU HE02 (ub_same_trans s s1 s2 UB1 UB2) (proj1 (inv_keys HI2)) (UBI x Hx))).
      assert (EB : ly_brk0 L2 = ly_brk0 L) by exact (proj1 (proj2 HE02)).
      assert (KEEPK : forall k, In k [3; 4; 26; 27]%nat -> getr R2' (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
      { intros k Hk. rewrite (R2K k ltac:(clear - Hk; klist Hk)). rewrite (QK k ltac:(clear - Hk; klist Hk)). exact (R1K k Hk). }
      cbv beta iota.
      assert (CALLEE : forall (R4 : bvmap 5 word), getr R4 1 = wa (bv_unsigned (getr regs 1)) -> getr R4 2 = wa sp0 ->
                 getr R4 8 = wa (bv_unsigned (getr regs 8)) -> getr R4 9 = wa (bv_unsigned (getr regs 9)) ->
                 getr R4 18 = wa (bv_unsigned (getr regs 18)) -> getr R4 19 = wa (bv_unsigned (getr regs 19)) ->
                 getr R4 20 = wa (bv_unsigned (getr regs 20)) -> getr R4 21 = wa (bv_unsigned (getr regs 21)) ->
                 getr R4 22 = wa (bv_unsigned (getr regs 22)) -> getr R4 23 = wa (bv_unsigned (getr regs 23)) ->
                 getr R4 24 = wa (bv_unsigned (getr regs 24)) -> getr R4 25 = wa (bv_unsigned (getr regs 25)) ->
                 (forall k, In k [3; 4; 26; 27]%nat -> getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr R2' (Z_to_bv 5 (Z.of_nat k))) ->
                 forall k, In k callee_as -> getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
      { intros R4 E1 E2 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 EKK k Hk.
        assert (KK : In k [3; 4; 26; 27]%nat -> getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)))
          by (intros H; rewrite (EKK k H); exact (KEEPK k H)).
        unfold callee_as in Hk. cbn [In] in Hk.
        repeat (destruct Hk as [<-|Hk]; [first [ (litr2 E1; apply wa_u) | (litr2 E2; symmetry; litr2 R2; reflexivity) | (litr2 E8; apply wa_u)
                                                | (litr2 E9; apply wa_u) | (litr2 E18; apply wa_u) | (litr2 E19; apply wa_u) | (litr2 E20; apply wa_u)
                                                | (litr2 E21; apply wa_u) | (litr2 E22; apply wa_u) | (litr2 E23; apply wa_u) | (litr2 E24; apply wa_u)
                                                | (litr2 E25; apply wa_u) | (apply KK; cbn [In]; repeat first [ (left; reflexivity) | right ]) ] |]).
        destruct Hk. }
      destruct (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s2 sc) + UNIT) eqn:Hbr.
      + (* [comment removed for export] *)
        pose proof (ag_mmap_wk FORB HFORB HTOP X U L2 s2 m2 R2' rom sp0 K sc req mt f _ _ _ _ _ _ _ _ _ _ _ _ C2 ltac:(lia) F2 R2_10 R2_19 R2_24 R2_25
                      Mpg2 TB2 UB2' Hhd2 Hbr Hfit NX2') as AGW.
        unfold AGC in AGW. eapply wk_mono; [| exact (wk_ibind_inv SEGS FORB HTOP rom _ _ L2 R2' (wa 0x524e8) m2 _ AGW)].
        intros L3 b R3 pc3 m3 H. eapply wk_mono; [| exact H]. clear H.
        intros L4 r R4 pc4 m4 (-> & -> & Q10' & Qra & Qsp & Q8' & Q9' & Q18' & Q19' & Q20' & Q21' & Q22' & Q23' & Q24' & Q25' & QK' & IMP).
        unfold as_wpost. exists 0, (ag_s6 mt s2 sc req), mt. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [exact Q10'|].
        split; [exact (CALLEE R4 Qra Qsp Q8' Q9' Q18' Q19' Q20' Q21' Q22' Q23' Q24' Q25' QK')|].
        assert (ND2 : List.NoDup (keys s2)) by exact (proj1 (inv_keys HI2)).
        assert (Kmt2 : In mt (keys s2)).
        { destruct (HX2 mt (or_introl eq_refl)) as [E'|E']; exact (MT_keys s2 mt _ E'). }
        pose proof (inv_ctx HI2) as (L1' & L2' & _).
        split.
        { intros HI6. destruct (IMP HI6) as (C6 & G26 & GEND). split; [exact C6|].
          split; [exact (GROWX_of_GROW UB0 sp0 K L s m L4 _ m4 (GROW_trans sp0 K L s m L2 s2 m2 L4 _ m4 G02 G26))|].
          unfold markers_hold. apply Forall_forall. intros c Hc. destruct (s6_markers mt s2 sc req ND2 Kmt2 c Hc) as [Hold | ->].
          - refine (markers_keep HTOP (mt :: X) None U X (Some (mt, 0)) U L2 s2 m2 L4 _ m4 sp0 K C2 MK2 C6 G26 _ c Hold).
            intros q a' H. destruct (s6_used mt s2 sc req ND2 Kmt2 q a' H) as [Ho | (-> & ->)].
            + left. exists a'. split; [exact Ho | apply gshape_refl].
            + right. cbn [am_mem am_set_links new_am prid]. lia.
          - exact (GEND _ (s6_lookup_mt mt s2 sc req)). }
        split; [exact (s6_active mt s2 sc req L1' ltac:(clear - Hsc; lia))|].
        apply (UGROW_pre s s2 _ sc Eus02).
        destruct (ag_plan s2 sc req) as [cnt needed] eqn:Ep.
        pose proof (initial_cnt_facts sc (usage_of s2 sc) Hsc) as (Hc0 & Hc0s & Hc026).
        unfold ag_plan, ag_cnt0 in Ep.
        pose proof (mmap_plan_facts s2 sc req (initial_cnt sc (usage_of s2 sc)) (usage_of s2 sc) cnt needed Hsc Hc0 Hc0s Hreq Hfit Hc026 Ep) as (Hcnt & _).
        split; intros c Hc; rewrite (s6_usage mt s2 sc req L2' ltac:(clear - Hsc; lia) c ltac:(lia)); unfold ag_plan, ag_cnt0; rewrite Ep; cbn [fst].
        * replace (c =? sc) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
        * destruct (c =? sc) eqn:E; [apply Z.eqb_eq in E; subst c; lia | lia].
      + (* [comment removed for export] *)
        pose proof (ag_nest_wk FORB f UB0 HTOP X U L2 s2 m2 R2' rom sp0 K sc req mt _ _ _ _ _ _ _ _ _ _ _ _ (IHf f ltac:(lia)) C2 MK2 HKAS F2
                      R2_10 R2_19 R2_24 R2_25 Mpg2 TB2 Mdb2 UB2' Hhd2 Hbr Hf ltac:(rewrite EB; exact B1) ltac:(rewrite EB; exact B2)
                      ltac:(rewrite EB; exact B3) AIN UBI2 NX2') as AGW.
        unfold AGC in AGW. eapply wk_mono; [| exact (wk_ibind_inv SEGS FORB HTOP rom _ _ L2 R2' (wa 0x524e8) m2 _ AGW)].
        intros L3 b R3 pc3 m3 H. eapply wk_mono; [| exact H]. clear H.
        intros L4 r R4 pc4 m4 (s6 & -> & -> & Q10' & Qra & Qsp & Q8' & Q9' & Q18' & Q19' & Q20' & Q21' & Q22' & Q23' & Q24' & Q25' & QK' & IMP & MK6 & Hhd6 & UG6).
        unfold as_wpost. exists 0, s6, mt. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [exact Q10'|].
        split; [exact (CALLEE R4 Qra Qsp Q8' Q9' Q18' Q19' Q20' Q21' Q22' Q23' Q24' Q25' QK')|].
        split.
        { intros HI6. destruct (IMP HI6) as (C6 & G26). split; [exact C6|].
          split; [exact (GROWX_trans UB0 sp0 K L s m L2 s2 m2 L4 s6 m4 (GROWX_of_GROW UB0 sp0 K L s m L2 s2 m2 G02) G26) | exact MK6]. }
        split; [exact Hhd6 | exact (UGROW_pre s s2 s6 sc Eus02 UG6)]. }
  pose proof (wk_itok SEGS FORB HTOP rom _ L regs (wa 0x522f0) m _ (slot_post X U s sc req) W
                (proj1 (alloc_mutual (S fuel)) X U s sc req _ HI Hsc Hreq Hfit Hf (fun r H => H))) as W2.
  eapply wk_mono; [| exact W2].
  intros L' r R' pc m' ((idx & s' & g & -> & Hidx & -> & R10' & RK & IMP & Hhd & UG) & SP).
  destruct SP as (HB & UBs & [(Hm1 & _) | (_ & g' & am & HI' & Hhd' & Ug & Sca & Fita & Hla)]); cbn [fst snd] in *; [lia|].
  rewrite Hhd in Hhd'. injection Hhd' as <-.
  destruct (IMP HI') as (C' & G' & MK').
  unfold as_qpost. exists idx, s', g, am. split; [reflexivity|]. split; [reflexivity|]. split; [exact R10'|]. split; [exact RK|].
  split; [exact C'|]. split; [exact G'|]. split; [exact MK'|]. split; [exact Hhd|]. split; [exact Ug|]. split; [exact Sca|]. split; [exact Fita|].
  split; [lia|]. split; [exact HB|]. split; [exact UBs|]. exact UG.
Qed.

#[using="HFORB"] Theorem as_wk_all : forall fuel, as_wk_f FORB fuel.
Proof. LiaFast.lf_pins (fun (HFORB : LiaFast.U) => LiaFast.u0). intros fuel. induction fuel as [fuel IH] using (well_founded_induction lt_wf). apply as_wk_step. exact IH. Qed.

End ASW.

(* [comment removed for export] *)
Theorem as_wk : forall {fx : FPState}, as_wk_stmt.
Proof. intros fx. apply as_wk_of_f. intros FORB HFORB fuel. exact (as_wk_all FORB HFORB fuel). Qed.
