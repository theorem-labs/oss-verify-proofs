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
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngShape MngGeoX MngLt AxMng AxBits AxMalloc MngZ MngRepr MngHeap MngImage MngSurgery MngCtx MngExc MngNtfPre MngNtfC MngWb MngNtfM MngNtfS
                        MngGM AXG_ntfm AXG_ntfg AXG_nQ AXG_nD AXG_tam AXG_as1 AXG_as2 AXG_as3 AXG_as4 AXG_as5 AXG_as6 AxTry.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DEQ.
Variables (s : astate) (sc : Z) (g : sptr) (am : ameta).
Hypothesis Hhd : active_hd s sc = Some g.
Hypothesis Mg : MT s g = Some (MUsed am).
Hypothesis Hlen : length (st_active s) = 48%nat.
Hypothesis Hsc : 0 <= sc < 48.

#[using="Hhd Mg"] Lemma deq_n : forall pr ampr nx amnx, am_next am = Some nx -> am_prev am = Some pr -> nx <> g -> pr <> g -> pr <> nx ->
  MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) ->
  dequeue (HActive sc) g s = IRet (tt, s_tdn s g sc am pr ampr nx amnx).
Proof. LiaFast.lf_pins (fun (Hhd Mg : LiaFast.U) => LiaFast.u0).
  intros pr ampr nx amnx Hnx Hpr Hnxg Hprg Hprnx Mpr Mnx.
  unfold active_hd in Hhd. unfold MT in Mg, Mpr, Mnx.
  unfold dequeue. do 12 (mrun1; rewrite ?Mg, ?Mpr, ?Mnx, ?Hhd, ?Hnx, ?Hpr, ?sptr_eqb_refl; cbn [osptr_eqb];
     rewrite ?(proj2 (sptr_eqb_neq nx g) Hnxg); try (rewrite nth_lupd_same by (rewrite ?length_lupd, Hlen; lia))).
  unfold s_tdn, set_meta, set_active. cbn. reflexivity.
Qed.

#[using="Hhd Mg"] Lemma deq_2 : forall h amh, am_next am = Some h -> am_prev am = Some h -> h <> g ->
  MT s h = Some (MUsed amh) -> dequeue (HActive sc) g s = IRet (tt, s_td2 s g sc am h amh).
Proof. LiaFast.lf_pins (fun (Hhd Mg : LiaFast.U) => LiaFast.u0).
  intros h amh Hnx Hpr Hhg Mh.
  unfold active_hd in Hhd. unfold MT in Mg, Mh.
  unfold dequeue. do 12 (mrun1; rewrite ?Mg, ?Mh, ?Hhd, ?Hnx, ?Hpr, ?sptr_eqb_refl; cbn [osptr_eqb];
     rewrite ?(proj2 (sptr_eqb_neq h g) Hhg); try (rewrite nth_lupd_same by (rewrite ?length_lupd, Hlen; lia))).
  unfold s_td2, set_meta, set_active. cbn. rewrite !mupdate_twice''. reflexivity.
Qed.

#[using="Mg"] Lemma deq_1 : am_next am = Some g -> dequeue (HActive sc) g s = IRet (tt, s_dq1 s g sc am).
Proof. LiaFast.lf_pins (fun (Mg : LiaFast.U) => LiaFast.u0).
  intros Hnx. unfold active_hd in Hhd. unfold MT in Mg.
  unfold dequeue. do 6 (mrun1; rewrite ?Mg, ?Hhd, ?Hnx, ?sptr_eqb_refl; cbn [osptr_eqb]).
  unfold s_dq1, set_meta, set_active. cbn. reflexivity.
Qed.

#[using="Hhd Mg"] Lemma ta_take_eq : am_avail am <> 0 -> try_avail sc s = IRet (lowbit (am_avail am), s_take s g am).
Proof. LiaFast.lf_pins (fun (Hhd Mg : LiaFast.U) => LiaFast.u0).
  intros Hav. unfold active_hd in Hhd. unfold MT in Mg. rewrite try_avail_eq.
  unfold get_head, getm, setm, modify, bind, get, ret. cbn [ibind]. rewrite Hhd. cbn [ibind]. rewrite Mg. cbn [ibind].
  replace (negb (am_avail am =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact Hav). reflexivity.
Qed.
End DEQ.

(* [comment removed for export] *)
Lemma grp_ranges : forall X U s g am, Inv X None U s -> usedX X s g am ->
  0 <= am_avail am <= 2^32-1 /\ 0 <= am_freed am <= 2^32-1 /\ 0 <= am_last am <= 31 /\ 0 <= am_aidx am <= am_last am /\
  0 <= am_sc am <= 63 /\ 0 <= am_maplen am.
Proof.
  intros X U s g am HI Hu. destruct (masks_range_inv X None U s g am HI Hu) as (A1 & A2 & A3 & A4 & A5).
  pose proof (inv_groups HI g am Hu) as ((_ & Gaidx & _) & _). tauto.
Qed.

Lemma ctx_bounces : forall X U s, Inv X None U s -> length (st_bounces s) = 32%nat /\ (forall u, In u (st_bounces s) -> 0 <= u <= 255) /\
  length (st_active s) = 48%nat.
Proof.
  intros X U s HI. pose proof (inv_ctx HI) as (C1 & _ & _ & C4 & _ & _ & C7 & _). tauto.
Qed.

Section WALKS.
Context {fx : FPState}.

(* [comment removed for export] *)
#[using="Type"] Theorem walk_fin : forall X U L s3 m R rom sp0 K sc req can ra s0 s1 s2 s3' s4 s5 s6 s7 s8 s9 m3 am3,
  Inv X None U s3 -> 0 <= sc < 48 -> active_hd s3 sc = Some m3 -> usedX X s3 m3 am3 -> am_sc am3 = sc ->
  Z.land (am_freed am3) (ones (am_aidx am3)) <> 0 -> allzero X s3 sc ->
  NC L [] [] s3 m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3' s4 s5 s6 s7 s8 s9 ->
  getr R 10 = wa (loc_addr L (LMem m3)) -> DBT m ->
  exists R' m', msteps SEGS (mkst R (wa 0x52418) m rom) (mkst R' (wa 0x52b50) m' rom) /\
    ta_fin m3 s3 = IRet (lowbit (ta_mask am3), s_fin s3 m3 am3) /\ NC L [] [] (s_fin s3 m3 am3) m' sp0 K /\
    as_frame R' m' sp0 sc req can ra s0 s1 s2 s3' s4 s5 s6 s7 s8 s9 /\ RS L (s_fin s3 m3 am3) s3 /\
    mem_grows m m' /\ FRM L s3 sp0 K m m' /\ getr R' 10 = wa (ctz32 (ta_mask am3)) /\ ta_mask am3 <> 0 /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\ DBT m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X U L s3 m R rom sp0 K sc req can ra s0 s1 s2 s3' s4 s5 s6 s7 s8 s9 m3 am3 HI Hsc Hhd Hu Hsca Hmask Hz N F R10 Mdb.
  pose proof (usedX_MT _ _ _ _ Hu) as [M3 _].
  destruct (grp_ranges X U s3 m3 am3 HI Hu) as (Rav & Rfr & Rl & Rai & Rs & Rm).
  destruct (ctx_bounces X U s3 HI) as (Hbl & Hbr & _).
  destruct (seg_fin L s3 m R rom sp0 K sc req can ra s0 s1 s2 s3' s4 s5 s6 s7 s8 s9 m3 am3 N F R10 M3 (Hz m3 am3 Hu Hsca) Hmask
              Rfr ltac:(lia) Rl ltac:(lia) Rm Hbl Hbr Mdb) as (R' & m' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  exists R', m'. repeat (split; [assumption|]). exact H10.
Qed.

#[using="Type"] Lemma mask_range : forall am, 0 <= am_freed am <= 2^32-1 -> 0 <= am_aidx am -> ta_mask am <> 0 -> 0 < ta_mask am < 2^32.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros am Rf Ra Hm. unfold ta_mask in *. assert (A1 : Z.land (am_freed am) (ones (am_aidx am)) <= am_freed am).
  { apply land_le_l; [lia|]. unfold ones. pose proof (Z.pow_pos_nonneg 2 (am_aidx am + 1) ltac:(lia) ltac:(lia)). lia. }
  assert (A2 : 0 <= Z.land (am_freed am) (ones (am_aidx am))) by (apply Z.land_nonneg; lia). lia.
Qed.

#[using="Type"] Lemma lowbit_nz : forall x, 0 < x < 2^32 -> lowbit x <> 0.
Proof. LiaFast.lf_pins LiaFast.u0. intros x Hx. destruct (lowbit_pow x Hx) as (LP & R). rewrite LP. apply Z.pow_nonzero; lia. Qed.

#[using="Type"] Lemma ctz_lowbit : forall x, 0 < x < 2^32 -> ctz32 (lowbit x) = ctz32 x.
Proof. LiaFast.lf_pins LiaFast.u0. intros x Hx. unfold ctz32 at 1. rewrite lowbit_lowbit by exact Hx. reflexivity. Qed.

(* [comment removed for export] *)
Definition pcg (s : astate) : Prop := forall g am, MT s g = Some (MUsed am) -> am_aidx am < am_last am -> 0 < am_maplen am /\ am_sc am <> 0.

#[using="Type"] Lemma pcg_metas : forall s s', st_metas s' = st_metas s -> pcg s -> pcg s'.
Proof. LiaFast.lf_pins LiaFast.u0. intros s s' E P g am H. unfold MT in H. rewrite E in H. exact (P g am H). Qed.

#[using="Type"] Lemma layout_of_NC : forall L X EXC s m sp0 K, NC L X EXC s m sp0 K -> layout_ok L s.
Proof. LiaFast.lf_pins LiaFast.u0. intros L X EXC s m sp0 K N. exact (proj1 (nc_repr _ _ _ _ _ _ _ N)). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma DBT_FRM : forall L X EXC s m m' sp0 K, NC L X EXC s m sp0 K -> FRM L s sp0 K m m' -> DBT m -> DBT m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m m' sp0 K N FR D j Hj. pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  rewrite (rdn_frame_n m m'); [exact (D j Hj) | lia | cbn; lia |].
  intros x Hx. cbn in Hx. apply (FRM_static L s sp0 K m m' x FR HC Hsp1); lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem walk_choose : forall X U L s2 m R rom sp0 K sc req can ra s0 s1 s2' s3 s4 s5 s6 s7 s8 s9 m2 am2,
  Inv X None U s2 -> 0 <= sc < 48 -> active_hd s2 sc = Some m2 -> usedX X s2 m2 am2 -> am_sc am2 = sc ->
  am_freed am2 <> 0 -> allzero X s2 sc -> pcg s2 ->
  NC L [] [] s2 m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2' s3 s4 s5 s6 s7 s8 s9 ->
  getr R 10 = wa (loc_addr L (LMem m2)) -> getr R 13 = wa (ext_Z true 0 4 (am_freed am2)) -> getr R 14 = wa 2 -> DBT m ->
  exists R' m' first s', msteps SEGS (mkst R (wa 0x523e4) m rom) (mkst R' (wa 0x52b50) m' rom) /\
    ta_m2 sc m2 s2 = IRet (first, s') /\ first <> 0 /\ NC L [] [] s' m' sp0 K /\
    as_frame R' m' sp0 sc req can ra s0 s1 s2' s3 s4 s5 s6 s7 s8 s9 /\ RS L s' s2 /\
    mem_grows m m' /\ FRM L s2 sp0 K m m' /\ getr R' 10 = wa (ctz32 first) /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\ DBT m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X U L s2 m R rom sp0 K sc req can ra s0 s1 s2' s3 s4 s5 s6 s7 s8 s9 m2 am2 HI2 Hsc Hhd2 Hu2 Hs2 Hfr2 Hz2 Hpcg N F R10 R13 R14 Mdb.
  pose proof (usedX_MT _ _ _ _ Hu2) as [M2 NX2].
  destruct (grp_ranges X U s2 m2 am2 HI2 Hu2) as (Rav & Rfr & Rl & Rai & Rs & Rm).
  destruct (ctx_bounces X U s2 HI2) as (Hbl & Hbr & Hlen).
  pose proof (inv_groups HI2 m2 am2 Hu2) as (Gm2 & _). pose proof Gm2 as (Glast & Gaidx & Glen & Gav & Gfr0 & Gdisj & Gabove & Gavp & Gfra).
  destruct (Z.land (am_freed am2) (ones (am_aidx am2)) =? 0) eqn:Ec.
  - apply Z.eqb_eq in Ec.
    assert (Haidx : am_aidx am2 < am_last am2).
    { destruct (Z_lt_dec (am_aidx am2) (am_last am2)) as [|Hge]; [assumption|]. exfalso. apply Hfr2.
      apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
      destruct (Z_le_dec i (am_last am2)).
      - apply (f_equal (fun z => Z.testbit z i)) in Ec. rewrite Z.land_spec, Z.bits_0, testbit_ones in Ec by lia.
        replace (0 <=? i) with true in Ec by (symmetry; apply Z.leb_le; lia).
        replace (i <=? am_aidx am2) with true in Ec by (symmetry; apply Z.leb_le; lia).
        rewrite andb_true_r in Ec. exact Ec.
      - apply (proj2 (Gabove i ltac:(lia))). }
    destruct (head_links X U s2 sc m2 am2 HI2 Hsc Hhd2 Hu2 Hs2) as (pr & nx & Hpr & Hnx & amn & Hun & Hsn & Hnxf).
    destruct (sptr_eq_dec nx m2) as [->|Enx].
    + (* [comment removed for export] *)
      destruct (Hpcg m2 am2 M2 Haidx) as (Hml & Hsc0).
      assert (RW : meta_bits am2 <= 2^63-1) by (apply (meta_bits_r63 X None U s2 m2 am2 L HI2 Hu2 (layout_of_NC L [] [] s2 m sp0 K N))).
      destruct (seg_span L s2 m R rom sp0 K sc req can ra s0 s1 s2' s3 s4 s5 s6 s7 s8 s9 m2 am2 N F R10 R13 R14 Hsc M2 Ec Hnx
                  (Hz2 m2 am2 Hu2 Hs2) Rfr ltac:(lia) Rl ltac:(lia) Hml RW) as (R1 & m1 & H1 & E1 & N1 & F1 & RS1 & G1 & FR1 & Q10 & K1).
      set (ai := span_cnt am2 - 1) in *.
      pose proof (span_loop_ge 300 (am_aidx am2 + 2) (UNIT + class_size (am_sc am2) * (am_aidx am2 + 2)) (class_size (am_sc am2))) as Hsp.
      assert (Hai : am_aidx am2 + 1 <= ai <= am_last am2).
      { unfold ai, span_cnt. destruct (am_last am2 + 1 <? span_loop 300 (am_aidx am2 + 2) (UNIT + class_size (am_sc am2) * (am_aidx am2 + 2)) (class_size (am_sc am2))) eqn:E;
          [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia. }
      set (s3x := set_meta s2 m2 (MUsed (am_set_aidx ai am2))) in *.
      assert (HI3 : Inv X None U s3x).
      { change s3x with (upd_meta m2 (MUsed (am_set_aidx ai am2)) s2). eapply extend_aidx_Inv; eauto; [lia | rewrite Hs2; exact Hhd2 | lia]. }
      assert (Hhd3 : active_hd s3x sc = Some m2) by exact Hhd2.
      assert (Hu3 : usedX X s3x m2 (am_set_aidx ai am2)) by (apply usedX_intro; [exact NX2 | apply MT_set_same]).
      assert (Hmask3 : Z.land (am_freed (am_set_aidx ai am2)) (ones (am_aidx (am_set_aidx ai am2))) <> 0).
      { cbn [am_freed am_aidx am_set_aidx]. intros E0.
        apply (f_equal (fun z => Z.testbit z (am_aidx am2 + 1))) in E0.
        rewrite Z.land_spec, Z.bits_0, testbit_ones, (Gfra (am_aidx am2 + 1)) in E0 by lia.
        replace (0 <=? am_aidx am2 + 1) with true in E0 by (symmetry; apply Z.leb_le; lia).
        replace (am_aidx am2 + 1 <=? ai) with true in E0 by (symmetry; apply Z.leb_le; lia). discriminate. }
      assert (Hz3 : allzero X s3x sc).
      { intros g am Hg Hs'. destruct (sptr_eq_dec g m2) as [->|Hne].
        - pose proof (usedX_fun _ _ _ _ _ Hg Hu3) as ->. cbn. apply (Hz2 _ _ Hu2 Hs2).
        - apply (Hz2 g am); [|exact Hs']. unfold usedX, MTX in *. destruct (memb g X); [discriminate Hg|]. unfold s3x in Hg. rewrite MT_set_other in Hg by exact Hne. exact Hg. }
      destruct (walk_fin X U L s3x m1 R1 rom sp0 K sc req can ra s0 s1 s2' s3 s4 s5 s6 s7 s8 s9 m2 (am_set_aidx ai am2) HI3 Hsc Hhd3 Hu3 Hs2 Hmask3 Hz3
                  N1 F1 Q10 (DBT_FRM L [] [] s2 m m1 sp0 K N FR1 Mdb)) as (R2 & m2' & H2 & E2 & N2 & F2 & RS2 & G2 & FR2 & B10 & Hm2 & K2 & D2).
      exists R2, m2', (lowbit (ta_mask (am_set_aidx ai am2))), (s_fin s3x m2 (am_set_aidx ai am2)).
      split; [exact (msteps_trans SEGS _ _ _ H1 H2)|]. split; [rewrite E1; exact E2|]. split.
      { apply lowbit_nz. apply mask_range; [cbn; lia | cbn; lia | exact Hmask3]. }
      split; [exact N2|]. split; [exact F2|]. split; [exact (RS_trans L s2 s3x _ RS2 RS1)|]. split; [exact (mem_grows_trans _ _ _ G1 G2)|].
      split; [exact (FRM_trans L s2 s3x sp0 K m m1 m2' RS1 FR1 FR2)|]. split; [rewrite ctz_lowbit by (apply mask_range; [cbn; lia | cbn; lia | exact Hmask3]); exact B10|].
      split; [intros k Hk; rewrite (K2 k Hk); exact (K1 k Hk)|]. exact D2.
    + (* [comment removed for export] *)
      destruct (Hnxf Enx) as [Hfrn Havn].
      pose proof (usedX_MT _ _ _ _ Hun) as [Mnx NXn].
      destruct (seg_m2b L s2 m R rom sp0 K sc req can ra s0 s1 s2' s3 s4 s5 s6 s7 s8 s9 m2 am2 nx amn N F R10 R13 R14 Hsc Hlen M2 Ec Hnx Enx Mnx Havn
                  Rfr ltac:(lia)) as (R1 & m1 & H1 & E1 & N1 & F1 & RS1 & G1 & FR1 & Q10 & K1).
      set (s3x := s_head s2 sc (Some nx)) in *.
      assert (HI3 : Inv X None U s3x) by (exact (Inv_rotate_head X None U s2 sc m2 am2 nx HI2 Hsc Hu2 Hs2 Hhd2 (Hz2 _ _ Hu2 Hs2) Hfr2 Hnx)).
      assert (Hhd3 : active_hd s3x sc = Some nx) by (apply active_hd_set_active_same; rewrite Hlen; lia).
      assert (Hmask3 : Z.land (am_freed amn) (ones (am_aidx amn)) <> 0).
      { intros E0.
        assert (Hnp : ~ am_aidx amn < am_last amn).
        { intros Hp. apply Enx. eapply (inv_partial HI2 nx amn m2 am2); eauto. congruence. }
        pose proof (inv_groups HI2 nx amn Hun) as ((Nlast & Naidx & _ & _ & _ & _ & Nabove & _) & _).
        apply Hfrn. apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
        destruct (Z_le_dec i (am_last amn)).
        - apply (f_equal (fun z => Z.testbit z i)) in E0. rewrite Z.land_spec, Z.bits_0, testbit_ones in E0 by lia.
          replace (0 <=? i) with true in E0 by (symmetry; apply Z.leb_le; lia).
          replace (i <=? am_aidx amn) with true in E0 by (symmetry; apply Z.leb_le; lia).
          rewrite andb_true_r in E0. exact E0.
        - apply (proj2 (Nabove i ltac:(lia))). }
      destruct (grp_ranges X U s2 nx amn HI2 Hun) as (Rav' & Rfr' & Rl' & Rai' & Rs' & Rm').
      destruct (walk_fin X U L s3x m1 R1 rom sp0 K sc req can ra s0 s1 s2' s3 s4 s5 s6 s7 s8 s9 nx amn HI3 Hsc Hhd3 Hun Hsn Hmask3 Hz2
                  N1 F1 Q10 (DBT_FRM L [] [] s2 m m1 sp0 K N FR1 Mdb)) as (R2 & m2' & H2 & E2 & N2 & F2 & RS2 & G2 & FR2 & B10 & Hm2 & K2 & D2).
      exists R2, m2', (lowbit (ta_mask amn)), (s_fin s3x nx amn).
      split; [exact (msteps_trans SEGS _ _ _ H1 H2)|]. split; [rewrite E1; exact E2|]. split.
      { apply lowbit_nz. apply mask_range; [lia | lia | exact Hmask3]. }
      split; [exact N2|]. split; [exact F2|]. split; [exact (RS_trans L s2 s3x _ RS2 RS1)|]. split; [exact (mem_grows_trans _ _ _ G1 G2)|].
      split; [exact (FRM_trans L s2 s3x sp0 K m m1 m2' RS1 FR1 FR2)|]. split; [rewrite ctz_lowbit by (apply mask_range; [lia | lia | exact Hmask3]); exact B10|].
      split; [intros k Hk; rewrite (K2 k Hk); exact (K1 k Hk)|]. exact D2.
  - (* [comment removed for export] *)
    apply Z.eqb_neq in Ec.
    destruct (seg_m2a L s2 m R rom sp0 K sc req can ra s0 s1 s2' s3 s4 s5 s6 s7 s8 s9 m2 am2 N F R10 R13 R14 Hsc M2 Ec (Hz2 m2 am2 Hu2 Hs2)
                Rfr ltac:(lia)) as (R1 & H1 & E1 & F1 & Q10 & K1).
    destruct (walk_fin X U L s2 m R1 rom sp0 K sc req can ra s0 s1 s2' s3 s4 s5 s6 s7 s8 s9 m2 am2 HI2 Hsc Hhd2 Hu2 Hs2 Ec Hz2
                N F1 Q10 Mdb) as (R2 & m2' & H2 & E2 & N2 & F2 & RS2 & G2 & FR2 & B10 & Hm2 & K2 & D2).
    exists R2, m2', (lowbit (ta_mask am2)), (s_fin s2 m2 am2).
    split; [exact (msteps_trans SEGS _ _ _ H1 H2)|]. split; [rewrite E1; exact E2|]. split.
    { apply lowbit_nz. apply mask_range; [lia | lia | exact Ec]. }
    split; [exact N2|]. split; [exact F2|]. split; [exact RS2|]. split; [exact G2|]. split; [exact FR2|].
    split; [rewrite ctz_lowbit by (apply mask_range; [lia | lia | exact Ec]); exact B10|].
    split; [intros k Hk; rewrite (K2 k Hk); exact (K1 k Hk)|]. exact D2.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem walk_select : forall X U L s1 m R rom sp0 K sc req can ra s0 s1' s2 s3 s4 s5 s6 s7 s8 s9 m1 am1,
  Inv X None U s1 -> 0 <= sc < 48 -> active_hd s1 sc = Some m1 -> usedX X s1 m1 am1 -> am_sc am1 = sc ->
  am_freed am1 <> 0 -> allzero X s1 sc -> pcg s1 ->
  NC L [] [] s1 m sp0 K -> as_frame R m sp0 sc req can ra s0 s1' s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 10 = wa (loc_addr L (LMem m1)) -> DBT m ->
  exists R' m' first s', msteps SEGS (mkst R (wa 0x523b8) m rom) (mkst R' (wa 0x52b50) m' rom) /\
    ta_m1 sc m1 s1 = IRet (first, s') /\ first <> 0 /\ NC L [] [] s' m' sp0 K /\
    as_frame R' m' sp0 sc req can ra s0 s1' s2 s3 s4 s5 s6 s7 s8 s9 /\ RS L s' s1 /\
    mem_grows m m' /\ FRM L s1 sp0 K m m' /\ getr R' 10 = wa (ctz32 first) /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\ DBT m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X U L s1 m R rom sp0 K sc req can ra s0 s1' s2 s3 s4 s5 s6 s7 s8 s9 m1 am1 HI Hsc Hhd Hu Hsca Hfr Hz Hpcg N F R10 Mdb.
  pose proof (usedX_MT _ _ _ _ Hu) as [M1 NX1].
  destruct (grp_ranges X U s1 m1 am1 HI Hu) as (Rav & Rfr & Rl & Rai & Rs & Rm).
  destruct (ctx_bounces X U s1 HI) as (Hbl & Hbr & Hlen).
  assert (RW : meta_bits am1 <= 2^63-1) by (apply (meta_bits_r63 X None U s1 m1 am1 L HI Hu (layout_of_NC L [] [] s1 m sp0 K N))).
  destruct (Z.eq_dec (am_freed am1) (ones (am_last am1))) as [Eall|Eall].
  - (* [comment removed for export] *)
    destruct (head_links X U s1 sc m1 am1 HI Hsc Hhd Hu Hsca) as (pr & nx & Hpr & Hnx & amn & Hun & Hsn & Hnxf).
    pose proof (usedX_MT _ _ _ _ Hun) as [Mnx NXn].
    destruct (grp_ranges X U s1 nx amn HI Hun) as (Rav' & Rfr' & Rl' & Rai' & Rs' & Rm').
    destruct (seg_m1f L s1 m R rom sp0 K sc req can ra s0 s1' s2 s3 s4 s5 s6 s7 s8 s9 m1 am1 nx amn N F R10 Hsc Hlen M1 Eall Hnx Mnx
                Rfr Rl ltac:(lia) Rm RW Rfr') as (R1 & m1' & H1 & E1 & N1 & F1 & RS1 & G1 & FR1 & Q10 & Q13 & Q14 & K1).
    set (s2x := s_head s1 sc (Some nx)) in *.
    assert (HI2 : Inv X None U s2x) by (exact (Inv_rotate_head X None U s1 sc m1 am1 nx HI Hsc Hu Hsca Hhd (Hz _ _ Hu Hsca) Hfr Hnx)).
    assert (Hhd2 : active_hd s2x sc = Some nx) by (apply active_hd_set_active_same; rewrite Hlen; lia).
    assert (Hfrn : am_freed amn <> 0).
    { destruct (sptr_eq_dec nx m1) as [->|Hne]; [| apply (proj1 (Hnxf Hne))]. pose proof (usedX_fun _ _ _ _ _ Hun Hu) as ->. exact Hfr. }
    destruct (walk_choose X U L s2x m1' R1 rom sp0 K sc req can ra s0 s1' s2 s3 s4 s5 s6 s7 s8 s9 nx amn HI2 Hsc Hhd2 Hun Hsn Hfrn Hz
                (pcg_metas s1 s2x eq_refl Hpcg) N1 F1 Q10 Q13 Q14 (DBT_FRM L [] [] s1 m m1' sp0 K N FR1 Mdb))
      as (R2 & m2' & first & s' & H2 & E2 & Hf & N2 & F2 & RS2 & G2 & FR2 & B10 & K2 & D2).
    exists R2, m2', first, s'. split; [exact (msteps_trans SEGS _ _ _ H1 H2)|]. split; [rewrite E1; exact E2|]. split; [exact Hf|].
    split; [exact N2|]. split; [exact F2|]. split; [exact (RS_trans L s1 s2x _ RS2 RS1)|]. split; [exact (mem_grows_trans _ _ _ G1 G2)|].
    split; [exact (FRM_trans L s1 s2x sp0 K m m1' m2' RS1 FR1 FR2)|]. split; [exact B10|].
    split; [intros k Hk; rewrite (K2 k Hk); exact (K1 k Hk)|]. exact D2.
  - destruct (seg_m1n L s1 m R rom sp0 K sc req can ra s0 s1' s2 s3 s4 s5 s6 s7 s8 s9 m1 am1 N F R10 Hsc M1 Eall Rfr Rl ltac:(lia) Rm RW)
      as (R1 & H1 & E1 & F1 & Q10 & Q13 & Q14 & K1).
    destruct (walk_choose X U L s1 m R1 rom sp0 K sc req can ra s0 s1' s2 s3 s4 s5 s6 s7 s8 s9 m1 am1 HI Hsc Hhd Hu Hsca Hfr Hz Hpcg N F1 Q10 Q13 Q14 Mdb)
      as (R2 & m2' & first & s' & H2 & E2 & Hf & N2 & F2 & RS2 & G2 & FR2 & B10 & K2 & D2).
    exists R2, m2', first, s'. split; [exact (msteps_trans SEGS _ _ _ H1 H2)|]. split; [rewrite E1; exact E2|]. split; [exact Hf|].
    split; [exact N2|]. split; [exact F2|]. split; [exact RS2|]. split; [exact G2|]. split; [exact FR2|]. split; [exact B10|].
    split; [intros k Hk; rewrite (K2 k Hk); exact (K1 k Hk)|]. exact D2.
Qed.

#[using="Type"] Lemma last_In' : forall (l : list sptr) d, l <> [] -> In (last l d) l.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction l as [|a l IH]; intros d H; [contradiction|]. destruct l as [|b l']; [left; reflexivity|].
  right. change (last (a :: b :: l') d) with (last (b :: l') d). apply IH. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma deq_facts : forall X U s sc g am S,
  Inv X None U s -> 0 <= sc < 48 -> usedX X s g am -> am_sc am = sc -> active_hd s sc = Some g -> am_avail am = 0 -> am_freed am = 0 ->
  allzero X s sc -> pcg s -> XNU X s -> dequeue (HActive sc) g s = IRet (tt, S) ->
  Inv X None U S /\ allzero X S sc /\ pcg S /\ st_metas S <> [] /\
  match active_hd S sc with
  | None => True
  | Some m1 => exists am1, usedX X S m1 am1 /\ am_sc am1 = sc /\ am_freed am1 <> 0
  end.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X U s sc g am S HI Hsc Hu Hsca Hhd Hav Hfr Hz Hpcg HXU Edq.
  assert (HXS : XNU X S) by exact (XNU_shape X s S (ileaf_ret_eq _ _ _ (PRES_dequeue (HActive sc) g s) Edq) HXU).
  pose proof (Inv_dequeue_full_head X None U s sc g am
    (fun r => XNU X (snd r) -> Inv X None U (snd r) /\ allzero X (snd r) sc /\ pcg (snd r) /\ st_metas (snd r) <> [] /\
       match active_hd (snd r) sc with
       | None => True
       | Some m1 => exists am1, usedX X (snd r) m1 am1 /\ am_sc am1 = sc /\ am_freed am1 <> 0
       end) HI Hsc Hu Hsca Hhd Hav Hfr Hz ltac:(intros q i; discriminate)) as H.
  rewrite Edq in H. cbn [itok fst snd] in H. refine (H _ HXS).
  intros s' HI' Sb Hse Bwd Fwd M0' Hnew UB1 HX'. cbn [snd]. split; [exact HI'|]. split.
  { intros g' am' Hg Hsg. destruct (Bwd _ _ Hg) as (am0 & Hga & E). pose proof (strip_fields _ _ E) as (_&Eav'&_&_&Es&_).
    rewrite Eav'. apply (Hz g' am0 Hga). congruence. }
  split.
  { intros g' am' Mg' Hp. assert (Hg : usedX X s' g' am').
    { apply usedX_intro; [|exact Mg']. destruct (memb g' X) eqn:Em; [|reflexivity]. exfalso. exact (HX' g' (memb_In' g' X Em) am' Mg'). }
    destruct (Bwd _ _ Hg) as (am0 & Hga & E). pose proof (strip_fields _ _ E) as (_&_&_&El&Es&Em&Ea&_).
    pose proof (usedX_MT _ _ _ _ Hga) as [M0 _]. rewrite El, Ea in Hp. destruct (Hpcg g' am0 M0 Hp) as [P1 P2]. rewrite Em, Es. tauto. }
  split; [intros E; unfold MT in M0'; rewrite E in M0'; discriminate|].
  destruct (active_hd s' sc) as [m1|]; [|exact I].
  destruct Hnew as (_ & am1 & Hu1 & Hs1 & Hf1 & _). exists am1. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem ta_walk : forall X U L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9,
  Inv X None U s -> 0 <= sc < 48 -> pcg s -> XNU X s ->
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 12 = wa (onum L (active_hd s sc)) -> DBT m ->
  exists R' m' first s', try_avail sc s = IRet (first, s') /\ NC L [] [] s' m' sp0 K /\
    as_frame R' m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\ RS L s' s /\ mem_grows m m' /\ FRM L s sp0 K m m' /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\ DBT m' /\
    ((first <> 0 /\ msteps SEGS (mkst R (wa 0x52350) m rom) (mkst R' (wa 0x52b50) m' rom) /\ getr R' 10 = wa (ctz32 first)) \/
     (first = 0 /\ msteps SEGS (mkst R (wa 0x52350) m rom) (mkst R' (wa 0x524d0) m' rom))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X U L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 HI Hsc Hpcg HXU N F R12 Mdb.
  destruct (ctx_bounces X U s HI) as (Hbl & Hbr & Hlen).
  destruct (active_hd s sc) as [g|] eqn:Ehd.
  2:{ (* [comment removed for export] *)
    destruct (seg_ta0 L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 N F R12 Ehd) as (R' & H1 & E1 & F1 & K1).
    exists R', m, 0, s. split; [exact E1|]. split; [exact N|]. split; [exact F1|]. split; [apply RS_refl|]. split; [apply mem_grows_refl|].
    split; [apply FRM_refl|]. split; [exact K1|]. split; [exact Mdb|]. right. split; [reflexivity | exact H1]. }
  cbn [onum] in R12.
  destruct (inv_rings HI) as (FRg & A & D). destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
  rewrite Ehd in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin0 _].
  destruct (ring_members_used _ _ _ _ _ g Rg Hin0) as (am & Hu & Hsca).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg].
  destruct (grp_ranges X U s g am HI Hu) as (Rav & Rfr & Rl & Rai & Rs & Rm).
  destruct (Z.eq_dec (am_avail am) 0) as [Eav|Eav].
  2:{ (* [comment removed for export] *)
    destruct (seg_tk L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am N F R12 Mg ltac:(lia) Mdb)
      as (R' & m' & H1 & B10 & N1 & F1 & RS1 & G1 & FR1 & K1 & D1).
    exists R', m', (lowbit (am_avail am)), (s_take s g am). split; [exact (ta_take_eq s sc g am Ehd Mg Eav)|].
    split; [exact N1|]. split; [exact F1|]. split; [exact RS1|]. split; [exact G1|]. split; [exact FR1|]. split; [exact K1|]. split; [exact D1|].
    left. split; [apply lowbit_nz; lia|]. split; [exact H1|]. rewrite ctz_lowbit by lia. exact B10. }
  (* [comment removed for export] *)
  assert (Hz : allzero X s sc).
  { intros g' am' Hg Hsg. destruct (Z.eq_dec (am_avail am') 0) as [E|E]; [exact E|]. exfalso.
    pose proof (Q1 g' am' Hg Hsg E) as E2. rewrite Ehd in E2. injection E2 as ->.
    pose proof (usedX_fun _ _ _ _ _ Hg Hu) as ->. exact (E Eav). }
  destruct (head_links X U s sc g am HI Hsc Ehd Hu Hsca) as (pr & nx & Hpr & Hnx & amn & Hun & Hsn & Hnxf).
  pose proof (usedX_MT _ _ _ _ Hun) as [Mnx NXn].
  destruct (grp_ranges X U s nx amn HI Hun) as (Rav' & Rfr' & Rl' & Rai' & Rs' & Rm').
  destruct (Z.eq_dec (am_freed am) 0) as [Efr|Efr].
  - (* [comment removed for export] *)
    destruct (sptr_eq_dec nx g) as [->|Enx].
    + (* [comment removed for export] *)
      destruct (seg_tad1 L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am N F R12 ltac:(lia) Hlen Ehd Mg Eav Efr Hnx)
        as (R' & m' & H1 & E1 & N1 & F1 & RS1 & G1 & FR1 & K1).
      exists R', m', 0, (s_dq1 s g sc am). split; [exact E1|]. split; [exact N1|]. split; [exact F1|]. split; [exact RS1|]. split; [exact G1|].
      split; [exact FR1|]. split; [exact K1|]. split; [exact (DBT_FRM L [] [] s m m' sp0 K N FR1 Mdb)|]. right. split; [reflexivity | exact H1].
    + (* [comment removed for export] *)
      destruct (ring_head_links _ _ _ _ _ _ Rg Hu) as (rest & Ems & Hpr' & Hnx').
      rewrite Hpr in Hpr'. injection Hpr' as Epr. rewrite Hnx in Hnx'. injection Hnx' as Enx'.
      assert (Hrest : rest <> []) by (intros E; rewrite E in Enx'; cbn in Enx'; exact (Enx Enx')).
      assert (Hprg : pr <> g).
      { intros E. destruct Rg as ((ND & _) & _). rewrite Ems in ND. apply NoDup_cons_iff in ND as [NI _]. apply NI.
        rewrite <- E, Epr. apply last_In'. exact Hrest. }
      assert (Kpr : In pr ms) by (rewrite Ems, Epr; right; apply last_In'; exact Hrest).
      destruct (ring_members_used _ _ _ _ _ pr Rg Kpr) as (ampr & Hupr & Hspr).
      pose proof (usedX_MT _ _ _ _ Hupr) as [Mpr NXpr].
      destruct (sptr_eq_dec pr nx) as [->|Eprnx].
      * (* [comment removed for export] *)
        destruct (seg_tad2 L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am nx amn N F R12 ltac:(lia) Hlen Ehd Mg Eav Efr Hnx Hpr Enx Mnx)
          as (R1 & m1 & H1 & E1 & N1 & F1 & RS1 & G1 & FR1 & Q10 & K1).
        set (S := s_td2 s g sc am nx amn) in *.
        destruct (deq_facts X U s sc g am S HI Hsc Hu Hsca Ehd Eav Efr Hz Hpcg HXU (deq_2 s sc g am Ehd Mg nx amn Hnx Hpr Enx Mnx))
          as (HIS & HzS & HpS & _ & HmS).
        assert (HhdS : active_hd S sc = Some nx).
        { unfold S, s_td2, active_hd. cbn [st_active set_meta set_metas set_active]. apply nth_lupd_same.
          change (st_active (set_meta s nx (MUsed (am_set_links (Some nx) (Some nx) amn)))) with (st_active s). rewrite Hlen. lia. }
        rewrite HhdS in HmS. destruct HmS as (am1 & Hu1 & Hs1 & Hf1).
        destruct (walk_select X U L S m1 R1 rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 nx am1 HIS Hsc HhdS Hu1 Hs1 Hf1 HzS HpS N1 F1 Q10
                    (DBT_FRM L [] [] s m m1 sp0 K N FR1 Mdb)) as (R2 & m2 & first & s' & H2 & E2 & Hf & N2 & F2 & RS2 & G2 & FR2 & B10 & K2 & D2).
        exists R2, m2, first, s'. split; [rewrite E1; exact E2|]. split; [exact N2|]. split; [exact F2|]. split; [exact (RS_trans L s S _ RS2 RS1)|].
        split; [exact (mem_grows_trans _ _ _ G1 G2)|]. split; [exact (FRM_trans L s S sp0 K m m1 m2 RS1 FR1 FR2)|].
        split; [intros k Hk; rewrite (K2 k Hk); exact (K1 k Hk)|]. split; [exact D2|].
        left. split; [exact Hf|]. split; [exact (msteps_trans SEGS _ _ _ H1 H2)|]. exact B10.
      * (* [comment removed for export] *)
        destruct (seg_tadn L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am pr ampr nx amn N F R12 ltac:(lia) Hlen Ehd Mg Eav Efr Hnx Hpr
                    Enx Hprg Eprnx Mpr Mnx) as (R1 & m1 & H1 & E1 & N1 & F1 & RS1 & G1 & FR1 & Q10 & K1).
        set (S := s_tdn s g sc am pr ampr nx amn) in *.
        destruct (deq_facts X U s sc g am S HI Hsc Hu Hsca Ehd Eav Efr Hz Hpcg HXU (deq_n s sc g am Ehd Mg pr ampr nx amn Hnx Hpr Enx Hprg Eprnx Mpr Mnx))
          as (HIS & HzS & HpS & _ & HmS).
        assert (HhdS : active_hd S sc = Some nx).
        { unfold S, s_tdn, active_hd. cbn [st_active set_meta set_metas set_active]. apply nth_lupd_same.
          change (st_active (set_meta (set_meta s pr (MUsed (am_set_links (am_prev ampr) (Some nx) ampr))) nx (MUsed (am_set_links (Some pr) (am_next amn) amn))))
            with (st_active s). rewrite Hlen. lia. }
        rewrite HhdS in HmS. destruct HmS as (am1 & Hu1 & Hs1 & Hf1).
        destruct (walk_select X U L S m1 R1 rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 nx am1 HIS Hsc HhdS Hu1 Hs1 Hf1 HzS HpS N1 F1 Q10
                    (DBT_FRM L [] [] s m m1 sp0 K N FR1 Mdb)) as (R2 & m2 & first & s' & H2 & E2 & Hf & N2 & F2 & RS2 & G2 & FR2 & B10 & K2 & D2).
        exists R2, m2, first, s'. split; [rewrite E1; exact E2|]. split; [exact N2|]. split; [exact F2|]. split; [exact (RS_trans L s S _ RS2 RS1)|].
        split; [exact (mem_grows_trans _ _ _ G1 G2)|]. split; [exact (FRM_trans L s S sp0 K m m1 m2 RS1 FR1 FR2)|].
        split; [intros k Hk; rewrite (K2 k Hk); exact (K1 k Hk)|]. split; [exact D2|].
        left. split; [exact Hf|]. split; [exact (msteps_trans SEGS _ _ _ H1 H2)|]. exact B10.
  - (* [comment removed for export] *)
    destruct (seg_tar L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am nx N F R12 ltac:(lia) Hlen Ehd Mg Eav Efr Rfr Hnx
                ltac:(eapply MT_keys; exact Mnx)) as (R1 & m1 & H1 & E1 & N1 & F1 & RS1 & G1 & FR1 & Q10 & K1).
    set (S := s_head s sc (Some nx)) in *.
    assert (HIS : Inv X None U S) by (exact (Inv_rotate_head X None U s sc g am nx HI Hsc Hu Hsca Ehd Eav Efr Hnx)).
    assert (HhdS : active_hd S sc = Some nx) by (apply active_hd_set_active_same; rewrite Hlen; lia).
    assert (Hfrn : am_freed amn <> 0).
    { destruct (sptr_eq_dec nx g) as [->|Hne]; [| apply (proj1 (Hnxf Hne))]. pose proof (usedX_fun _ _ _ _ _ Hun Hu) as ->. exact Efr. }
    destruct (walk_select X U L S m1 R1 rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 nx amn HIS Hsc HhdS Hun Hsn Hfrn Hz
                (pcg_metas s S eq_refl Hpcg) N1 F1 Q10 (DBT_FRM L [] [] s m m1 sp0 K N FR1 Mdb))
      as (R2 & m2 & first & s' & H2 & E2 & Hf & N2 & F2 & RS2 & G2 & FR2 & B10 & K2 & D2).
    exists R2, m2, first, s'. split; [rewrite E1; exact E2|]. split; [exact N2|]. split; [exact F2|]. split; [exact (RS_trans L s S _ RS2 RS1)|].
    split; [exact (mem_grows_trans _ _ _ G1 G2)|]. split; [exact (FRM_trans L s S sp0 K m m1 m2 RS1 FR1 FR2)|].
    split; [intros k Hk; rewrite (K2 k Hk); exact (K1 k Hk)|]. split; [exact D2|].
    left. split; [exact Hf|]. split; [exact (msteps_trans SEGS _ _ _ H1 H2)|]. exact B10.
Qed.

(* [comment removed for export] *)
Definition as_group (fuel : nat) (sc req : Z) : M Z :=
  og <- alloc_group fuel sc req ;;
  match og with
  | None => ret (-1)
  | Some _ => ret 0
  end.

#[using="Type"] Lemma alloc_slot_eq : forall fuel sc req s first s', try_avail sc s = IRet (first, s') ->
  alloc_slot (S fuel) sc req s = if first =? 0 then as_group fuel sc req s' else IRet (ctz32 first, s').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fuel sc req s first s' E. cbn [alloc_slot]. unfold bind. rewrite E. cbn [ibind].
  destruct (first =? 0); reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem as_walk : forall X U L s m regs rom sp0 K sc req fuel,
  Inv X None U s -> 0 <= sc < 48 -> pcg s -> XNU X s -> NC L [] [] s m sp0 K ->
  getr regs 2 = wa sp0 -> getr regs 10 = wa sc -> getr regs 11 = wa req -> 0 <= req <= 2^26 -> DBT m ->
  exists R m' first s', try_avail sc s = IRet (first, s') /\ NC L [] [] s' m' sp0 K /\ RS L s' s /\ mem_grows m m' /\ FRM L s sp0 K m m' /\ DBT m' /\
    ((first <> 0 /\ msteps SEGS (mkst regs (wa 0x522f0) m rom) (mkst R (wa 0x52b8c) m' rom) /\ getr R 10 = wa (ctz32 first) /\
      (forall k, In k callee_as -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
      alloc_slot (S fuel) sc req s = IRet (ctz32 first, s')) \/
     (first = 0 /\ msteps SEGS (mkst regs (wa 0x522f0) m rom) (mkst R (wa 0x524d0) m' rom) /\
      (exists can, as_frame R m' sp0 sc req can (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
         (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21))
         (bv_unsigned (getr regs 22)) (bv_unsigned (getr regs 23)) (bv_unsigned (getr regs 24)) (bv_unsigned (getr regs 25))) /\
      (forall k, In k [3;4;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
      alloc_slot (S fuel) sc req s = as_group fuel sc req s')).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X U L s m regs rom sp0 K sc req fuel HI Hsc Hpcg HXU N R2 R10 R11 Rreq Mdb.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  destruct (ctx_bounces X U s HI) as (Hbl & Hbr & Hlen).
  assert (Hhk : forall q, active_hd s sc = Some q -> In q (keys s)).
  { intros q Hq. destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & _).
    rewrite Hq in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin0 _].
    destruct (ring_members_used _ _ _ _ _ q Rg Hin0) as (amq & Huq & _). pose proof (usedX_MT _ _ _ _ Huq) as [Mq _]. eapply MT_keys; exact Mq. }
  destruct (seg_ap L s m regs rom sp0 K sc req N R2 R10 R11 ltac:(lia) Rreq Hlen Hhk) as (R1 & can & M1 & A12 & F1 & K1 & MO1 & G1).
  set (m1 := as_mem0 m regs sp0 can) in *.
  assert (HFRM1 : FRM L s sp0 K m m1).
  { intros x Hx Hne. left. destruct (Z_lt_le_dec x (sp0 - 96)) as [A|A]; [exfalso; apply Hne; apply MO1; [exact Hx | lia]|].
    destruct (Z_lt_le_dec x sp0) as [B|B]; [lia|]. exfalso; apply Hne; apply MO1; [exact Hx | lia]. }
  assert (HR1 : repr_x L s (bview SEGS m1) []).
  { apply (repr_x_same L s (bview SEGS m) (bview SEGS m1) [] HR (fun x E => bview_grow_n m m1 x G1 E)).
    intros a Ha c Hc _ Hin. apply Ha.
    pose proof (bview_ne_range m m1 a Ha) as Ra.
    pose proof (HC c Hc) as (P1 & P2 & _). unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin.
    apply MngWb.bview_ext. apply MO1; [exact Ra | clear - Hin P2 HK1; lia]. }
  assert (N1 : NC L [] [] s m1 sp0 K) by (apply (NC_next L [] [] s s m m1 sp0 K N HR1 (RS_refl L s) HK ltac:(intros x []) G1 HFRM1 eq_refl)).
  destruct (ta_walk X U L s m1 R1 rom sp0 K sc req can _ _ _ _ _ _ _ _ _ _ _ HI Hsc Hpcg HXU N1 F1 A12 (DBT_FRM L [] [] s m m1 sp0 K N HFRM1 Mdb))
    as (R3 & m3 & first & s' & E3 & N3 & F3 & RS3 & G3 & FR3 & K3 & D3 & [(Hf & H3 & B10) | (Hf & H3)]).
  - destruct (seg_ep R3 m3 rom sp0 sc req can _ _ _ _ _ _ _ _ _ _ _ F3)
      as (R4 & M4 & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & K4).
    exists R4, m3, first, s'. split; [exact E3|]. split; [exact N3|]. split; [exact RS3|]. split; [exact (mem_grows_trans _ _ _ G1 G3)|].
    split; [exact (FRM_trans L s s sp0 K m m1 m3 (RS_refl L s) HFRM1 FR3)|]. split; [exact D3|]. left. split; [exact Hf|].
    split; [exact (msteps_trans SEGS _ _ _ M1 (msteps_trans SEGS _ _ _ H3 M4))|].
    split; [match goal with |- getr ?Rx ?r = _ => rewrite (kp_lit Rx R3 _ K4 10%nat r ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)) end; exact B10|].
    split.
    { assert (KK : forall k, In k [3;4;26;27]%nat -> getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
      { intros k Hk. rewrite (K4 k ltac:(clear - Hk; cbn [In] in *; intuition lia)), (K3 k ltac:(clear - Hk; cbn [In] in *; intuition lia)),
          (K1 k ltac:(clear - Hk; cbn [In] in *; intuition lia)). reflexivity. }
      intros k Hk. cbn [callee_as In] in Hk.
      repeat (destruct Hk as [<-|Hk];
        [ first [ (litr2 E1; apply wa_u) | (litr2 E2; symmetry; exact R2) | (litr2 E8; apply wa_u) | (litr2 E9; apply wa_u)
                | (litr2 E18; apply wa_u) | (litr2 E19; apply wa_u) | (litr2 E20; apply wa_u) | (litr2 E21; apply wa_u)
                | (litr2 E22; apply wa_u) | (litr2 E23; apply wa_u) | (litr2 E24; apply wa_u) | (litr2 E25; apply wa_u)
                | (apply KK; cbn [In]; memb) ] |]).
      destruct Hk. }
    rewrite (alloc_slot_eq fuel sc req s first s' E3). replace (first =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hf). reflexivity.
  - exists R3, m3, first, s'. split; [exact E3|]. split; [exact N3|]. split; [exact RS3|]. split; [exact (mem_grows_trans _ _ _ G1 G3)|].
    split; [exact (FRM_trans L s s sp0 K m m1 m3 (RS_refl L s) HFRM1 FR3)|]. split; [exact D3|]. right. split; [exact Hf|].
    split; [exact (msteps_trans SEGS _ _ _ M1 H3)|]. split; [exists can; exact F3|]. split.
    { intros k Hk. rewrite (K3 k ltac:(clear - Hk; cbn [In] in *; intuition lia)), (K1 k ltac:(clear - Hk; cbn [In] in *; intuition lia)). reflexivity. }
    rewrite (alloc_slot_eq fuel sc req s first s' E3). rewrite Hf. reflexivity.
Qed.

End WALKS.
