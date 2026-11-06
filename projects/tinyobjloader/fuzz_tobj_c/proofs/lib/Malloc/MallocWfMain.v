(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "frame"; "ameta"; "mslot"; "free"; "malloc"; "kreq"; "nth_slot"; "st_regions"; "am_last"; "fkind"; "ss_fr"; "MUsed"; "fr_kind"; "FUser"; "UNIT"; "fr_n"; "st_active"; "st_areas"; "st_brk"; "st_metas"; "st_usage"; "brkst"; "fr_off"; "padd"; "poff"; "region"; "slot_start"; "slotst"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "option"; "list"; "Some"; "unit"; "snd"; "app"; "cons"; "fst"; "nil"; "tt"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "False"; "True"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "WF"; "user_blocks"; "shape_eq"; "yields"; "frame_ptr"; "frames"; "MT"; "erase_slot"; "footprint"; "regions_after"; "reqs_ok"; "safe"; "same_shape_regions"; "tsim"; "usedX"; "loc"; "zseq"; "@Stdlib.Lists.List"; "In"; "flat_map"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "mul"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSim"; "sheq"; "hdr_known_at"; "mrel"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame
  MallocWfRingOps MallocWfSurgery MallocWfRings MallocWfMeta MallocWfSlot MallocWfGeom MallocWfArith
  MallocWfGroup MallocWfMalloc MallocWfFree MallocWfRepr MallocWfSim MallocWfTrace.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma user_blocks_frame s p n : ltac2:(tb__ "0|0|
S31Vs;A1S42S1fS0S1eA2S20S0S1eVp;Vn;A4S32Vs;A1A3S2dS0S0S2dS3S3S2dS1eS1eS2dS2S2S2cS3fS29S0A1Vs;R4R3A4S2cS2cS44Z0R2A2S44R2SaR3A1A2A2S2cS2bS21S2A1ScS8R3R2A2A1S23S2R1A2A3S2cS2bSbSeR1A1SfA3S2cS2bS1eS11R1A1Vn;A3S2bS0Vp;S35R3R2R1A3A3A2A2A2A2A2Lfr;A2Lidx;A2Lam;A2Lg;A2F_;F_;").
Proof.
  intros HW Hin. unfold user_blocks in Hin. apply in_flat_map in Hin as [[g am] [Hg Hin]]. cbn [snd] in Hin.
  apply in_flat_map in Hin as [idx [Hidx Hin]]. apply In_zseq in Hidx.
  destruct (ss_fr (nth_slot am idx)) as [fr|] eqn:Efr; [|destruct Hin].
  destruct (fr_kind fr) eqn:Ek; [|destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
  exists g, am, idx, fr. split; [|split; [lia|split; [exact Efr|split; [exact Ek|split; reflexivity]]]].
  apply usedX_intro; [reflexivity|]. apply (used_metas_iff s g am (proj1 (inv_keys HW))). exact Hg.
Qed.

Theorem malloc_safe : ltac2:(tb__ "0|0|
S1S1eS31R2A1S44Z0R2A2S3cS1fS21S0A1S1A2S6R3R4A2A2F_;F_;Fn;Fs;").
Proof. intros s n HW Hn. eapply itok_safe. apply (malloc_spec U0 s n (fun _ => True) HW Hn). intros; exact I. Qed.

Theorem malloc_reqs_ok : ltac2:(tb__ "0|0|
S1S1eS31R2A1S44Z0R2A2S3bS1fS21S0A1S1A2S6R3R4A2A2F_;F_;Fn;Fs;").
Proof. intros s n HW Hn. eapply itok_reqs_ok. apply (malloc_spec U0 s n (fun _ => True) HW Hn). intros; exact I. Qed.

Theorem malloc_wf : ltac2:(tb__ "0|1|
S1S1eS22S1fS7S1eA2A1S21S0A1M0S1S31R5A1S44Z0R5A2S34S1fG0S1A2S6R6R7A2R5S20G0S1R4R3A4A4S31R4A1F_;F_;F_;Fs';Fp;Ftr;Fn;Fs;").
Proof.
  intros s n tr p s' HW Hn Hy.
  exact (proj1 (itok_yields _ _ tr (p, s') (malloc_spec U0 s n _ HW Hn (fun r H => H)) Hy)).
Qed.

Lemma U0_nonneg : forall c, 0 <= U0 c.
Proof. intros c. unfold U0. lia. Qed.

Theorem free_safe : ltac2:(tb__ "0|0|
S1S0S1eS31R3A1S42S1fS0S1eA2S20S0S1eR3R2A4S32R4A1A3S3cS1fS24S1A2S5S23S0R4A2R5A2A2F_;F_;Fn;Fp;Fs;").
Proof.
  intros s p n HW Hin. destruct (user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & _ & ->).
  eapply itok_safe. apply (free_spec U0 s g am idx fr (fun _ => True) HW U0_nonneg Hu Hi Hfr Hk). intros; exact I.
Qed.

Theorem free_reqs_ok : ltac2:(tb__ "0|0|
S1S0S1eS31R3A1S42S1fS0S1eA2S20S0S1eR3R2A4S32R4A1A3S3bS1fS24S1A2S5S23S0R4A2R5A2A2F_;F_;Fn;Fp;Fs;").
Proof.
  intros s p n HW Hin. destruct (user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & _ & ->).
  eapply itok_reqs_ok. apply (free_spec U0 s g am idx fr (fun _ => True) HW U0_nonneg Hu Hi Hfr Hk). intros; exact I.
Qed.

Theorem free_wf : ltac2:(tb__ "0|0|
S1S0S1eS22S1fS7S1eA2A1S1S31R5A1S42S1fS0S1eA2S20S0S1eR5R4A4S32R6A1A3S34S1fS24S1A2S5S23S0R6A2R7A2R4S20S24S1S2aR3A4A4S31R4A1F_;F_;F_;Fs';Ftr;Fn;Fp;Fs;").
Proof.
  intros s p n tr s' HW Hin Hy. destruct (user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & _ & ->).
  exact (itok_yields _ (fun r => WF (snd r)) tr (tt, s')
           (free_spec U0 s g am idx fr _ HW U0_nonneg Hu Hi Hfr Hk (fun s1 H _ _ => H)) Hy).
Qed.

Theorem malloc_blocks : ltac2:(tb__ "0|5|
S1S1eS22S1fS7S1eA2A1S21S0A1M0S1S31R5A1S44Z0M1R5A2S34S1fG0S1A2S6R6R7A2R5S20G0S1R4R3A4A4G0OLp;R5S0S2dS22S1fS0S1eA2M2A1M3G3S2dG3G3S2cS2bG3S32R7A1S26G2R2S27G2S20S0S1eR3RaA4R1A3A3A3S2cS2bG3S32RbA1M4S26G2R2R1A3A3S2cS2bS1eS46S1aR3A1S10A2G1A3S30S42S0R3S48G2S0S28S0S1eA2G4A4A3A1A2A2A2Ll2;A2Ll1;A2Lq;S2bG3S32R4A1S32R8A1A3X21x2F_;F_;F_;Fs';Fp;Ftr;Fn;Fs;").
Proof.
  intros s n tr p s' HW Hn Hy.
  pose proof (itok_yields _ _ tr (p, s') (malloc_spec U0 s n _ HW Hn (fun r H => H)) Hy) as [HW' Hp]. cbn [fst snd] in HW', Hp.
  destruct p as [q|].
  - destruct Hp as (g & am & idx & off & (Hu & Hi & Hfr & ->) & (l1 & l2 & E1 & E2)).
    rewrite (user_blocks_ublist s (proj1 (inv_keys HW))), (user_blocks_ublist s' (proj1 (inv_keys HW'))).
    exists (map fst l1), (map fst l2). rewrite E1, E2, !map_app. cbn [map fst]. split; [reflexivity|]. split; [reflexivity|]. split.
    + pose proof (used_group_aligned [] None U0 s' HW' _ g am Hu (Nat.le_refl _)) as Hal.
      pose proof (stride_mod16 _ _ _ _ _ _ HW' Hu) as Hst.
      apply Z.div_exact in Hal; [|lia]. apply Z.div_exact in Hst; [|lia].
      rewrite poff_padd, poff_slot_start. unfold UNIT.
      replace (poff (am_mem am) + 16 + stride_of am * idx + 16 * off) with ((poff (am_mem am) / 16 + 1 + stride_of am / 16 * idx + off) * 16) by lia.
      apply Z_mod_mult.
    + pose proof (user_block_ptrs_NoDup s' HW') as ND. rewrite (user_blocks_ublist s' (proj1 (inv_keys HW'))), E1, !map_app in ND. cbn [map fst] in ND.
      apply NoDup_remove_2 in ND. rewrite <- !map_app in ND. rewrite <- !map_app. exact ND.
  - rewrite (user_blocks_ublist s (proj1 (inv_keys HW))), (user_blocks_ublist s' (proj1 (inv_keys HW'))). f_equal. apply ub_same_ublist. exact Hp.
Qed.

Theorem free_blocks : ltac2:(tb__ "0|3|
S1S0S1eS22S1fS7S1eA2A1S1S31R5A1S42S1fS0S1eA2M0S20S0S1eR5R4A4S32R6A1M1A3S34S1fS24S1A2S5S23S0R6A2R7A2R4S20S24S1S2aR3A4A4S2dS22G0A1M2G2S2dG2G2S2cS2bG2S32RaA1S26G0R2S27G0S20S0S1eR9R8A4R1A3A3A3S2bG2G1S26G0R2R1A3A3A2Ll2;A2Ll1;A2F_;F_;F_;Fs';Ftr;Fn;Fp;Fs;").
Proof.
  intros s p n tr s' HW Hin Hy. destruct (user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & <- & ->).
  pose proof (itok_yields _ (fun r => WF (snd r) /\ exists l1 l2, ublist s = l1 ++ ((frame_ptr am idx fr, fr_n fr), (g, idx)) :: l2 /\ ublist (snd r) = l1 ++ l2)
                tr (tt, s') (free_spec U0 s g am idx fr _ HW U0_nonneg Hu Hi Hfr Hk (fun s1 H _ B => conj H B)) Hy) as [HW' (l1 & l2 & E1 & E2)].
  cbn [snd] in HW', E2.
  rewrite (user_blocks_ublist s (proj1 (inv_keys HW))), (user_blocks_ublist s' (proj1 (inv_keys HW'))). exists (map fst l1), (map fst l2).
  rewrite E1, E2, !map_app. cbn [map fst]. auto.
Qed.

Lemma WF_sheq s t : ltac2:(tb__ "0|0|
S31Vs;A1S33Vs;Vt;A2S49Vs;Vt;A2F_;F_;").
Proof. intros HW E. split; [exact E | exact (proj1 (inv_keys HW))]. Qed.

Lemma frames_inv s g am i fr : ltac2:(tb__ "0|2|
S31Vs;A1S42S1fS1fS1fS0S3A2M0S1eA2M1S2A2S20G1S2S20G0S1eS20S0S3Vg;Vam;A4Vi;A4Vfr;A4S36Vs;A1A3S2cS3fS29S0A1Vs;Vg;Vam;A4S2cS2cS44Z0Vi;A2S44Vi;SaVam;A1A2A2S2bS21S2A1ScS8Vam;Vi;A2A1S23S2Vfr;A2A3A2A2F_;F_;").
Proof.
  intros HW Hin. unfold frames in Hin. apply in_flat_map in Hin as [[g0 am0] [Hg Hin]].
  apply in_flat_map in Hin as [j [Hj Hin]]. apply In_zseq in Hj.
  destruct (ss_fr (nth_slot am0 j)) as [fr0|] eqn:Efr; [|destruct Hin]. destruct Hin as [E|[]]. injection E as -> -> -> ->.
  split; [|split; [lia | exact Efr]].
  apply usedX_intro; [reflexivity|]. apply (used_metas_iff s g am (proj1 (inv_keys HW))). exact Hg.
Qed.

Lemma frames_intro s g am i fr : ltac2:(tb__ "0|2|
S31Vs;A1S2bS21S4A1S37Vs;Vg;A2S23S4SdVam;A1A2A3S2cS44Z0Vi;A2S44Vi;SaVam;A1A2A2S2bS21S2A1ScS8Vam;Vi;A2A1S23S2Vfr;A2A3S42S1fS1fS1fS0S3A2M0S1eA2M1S2A2S20G1S2S20G0S1eS20S0S3Vg;Vam;A4Vi;A4Vfr;A4S36Vs;A1A3F_;F_;F_;F_;").
Proof.
  intros HW Mg Hi Hfr. unfold frames. apply in_flat_map. exists (g, am). split.
  - apply (used_metas_iff s g am (proj1 (inv_keys HW))). exact Mg.
  - apply in_flat_map. exists i. split; [apply In_zseq; lia|]. rewrite Hfr. left. reflexivity.
Qed.

Theorem malloc_tsim : ltac2:(tb__ "0|8|
S1S1S1eS31R3A1M0G0S33R5R4A2S44Z0R4A2S3eS1fS21S0A1M1S1A2M2G2G2G2S2cS33S25G1S1R2A3S25G1S1R1A3A2G1OLx;M3S28G1S1R2A3M4S0G3G4S0S2dS0S0S2dS3S3S2dS3S3S2dS1eS1eS2dS2S2S2dS2S2S2cS42S1fS1fS1fS0S3A2M5S1eA2M6S2A2M7S20G6S2S20G5S1eS20S0S3R6R5A4R3A4R2A4S36S25G1S1RaA3A1A3S2cS42G7S20G6S2S20G5S1eS20S0S3R6R4A4R3A4R1A4S36S25G1S1R9A3A1A3S2cS2bS0R8S35R5R3R2A3A3S2bS0R7S35R4R3R1A3A3A2A2A2Lfr';A2Lfr;A2Li;A2Lam';A2Lam;A2Lg;A2Lp';S2eX21x2Lp;G3S28G1S1R1A3S0S2eLs0;S2fX21x2X21x2A2Ly;Lx;S6R5R7A2S6R5R6A2A5F_;F_;F_;F_;Fn;Ft;Fs;").
Proof.
  intros s t n HWs HWt E Hn.
  pose proof (malloc_spec U0 s n _ HWs Hn (fun r Hr => Hr)) as Ts.
  pose proof (malloc_spec U0 t n _ HWt Hn (fun r Hr => Hr)) as Tt.
  pose proof (rsim_malloc n s t (WF_sheq s t HWs E) _ _ Ts Tt) as SIM.
  eapply tsim_mono; [|exact SIM]. cbn beta. intros [p s'] [p' t'] ([HS RES] & [HW' _] & [HWt' _]). cbn [fst snd] in *.
  split; [exact (proj1 HS)|].
  destruct p as [p|], p' as [p'|]; try exact RES.
  destruct RES as (g & idx & s0 & t0 & HR). enr_intro HR.
  match type of E1 with s' = set_metas (mupdate _ _ (MUsed ?a)) _ => set (am1 := a) in E1 end.
  match type of E2 with t' = set_metas (mupdate _ _ (MUsed ?a)) _ => set (am1' := a) in E2 end.
  assert (M1 : MT s' g = Some (MUsed am1)) by (rewrite E1; unfold MT; cbn [st_metas set_metas]; apply mlookup_mupdate_same).
  assert (M1' : MT t' g = Some (MUsed am1')) by (rewrite E2; unfold MT; cbn [st_metas set_metas]; apply mlookup_mupdate_same).
  pose proof (inv_groups HW' g am1 (usedX_intro [] s' g am1 eq_refl M1)) as ((_ & _ & Glen & _) & _).
  pose proof (inv_groups HWt' g am1' (usedX_intro [] t' g am1' eq_refl M1')) as ((_ & _ & Glen' & _) & _).
  subst am1 am1'. unfold upd_slot in Glen, Glen'. cbn [am_slots am_last am_set_slots] in Glen, Glen'. rewrite length_lupd in Glen, Glen'.
  exists g. match type of M1 with _ = Some (MUsed ?a) => exists a end. match type of M1' with _ = Some (MUsed ?a) => exists a end.
  exists idx, (mkFrame off n FUser), (mkFrame off' n FUser).
  split; [|split; [|split; [rewrite P1; reflexivity | rewrite P2; reflexivity]]].
  - eapply frames_intro; [exact HW' | exact M1 | cbn [am_last upd_slot am_set_slots]; exact Hidx |].
    rewrite nth_slot_upd_slot; [rewrite Z.eqb_refl; reflexivity | lia | lia | cbn [am_slots]; lia].
  - eapply frames_intro; [exact HWt' | exact M1' | cbn [am_last upd_slot am_set_slots]; exact Hidx |].
    rewrite nth_slot_upd_slot; [rewrite Z.eqb_refl; reflexivity | lia | lia | cbn [am_slots]; lia].
Qed.

Lemma sheq_slot s t g am am' i : ltac2:(tb__ "0|1|
S49Vs;Vt;A2S2bS21S4A1M0S37Vs;Vg;A2S23S4SdVam;A1A2A3S2bG0S37Vt;Vg;A2S23S4SdVam';A1A2A3S2bS1dS38S8Vam;Vi;A2A1S38S8Vam';Vi;A2A1A3F_;F_;F_;").
Proof.
  intros H Ms Mt. pose proof (sheq_MT s t g H) as OR. rewrite Ms, Mt in OR. cbn [orel] in OR.
  pose proof (erase_meta_inv _ _ OR) as (sl' & E & ES). injection E as ->. unfold nth_slot. cbn [am_slots]. apply map_erase_nth. exact ES.
Qed.

Lemma WF_hdr_known s g i : ltac2:(tb__ "0|0|
S31Vs;A1S4aVs;Vg;Vi;A3F_;").
Proof.
  intros HW am fr Mg Hfr Hoff.
  assert (Hu : usedX [] s g am) by (apply usedX_intro; [reflexivity | exact Mg]).
  pose proof (inv_groups HW g am Hu) as ((Glast & _ & Glen & _) & _ & Gsl & _).
  destruct (Z_le_dec 0 i) as [Hi0|Hi0]; [destruct (Z_le_dec i (am_last am)) as [Hi1|Hi1]|].
  - pose proof (Gsl i ltac:(lia)) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & _ & S4). rewrite (S4 Hoff). discriminate.
  - unfold nth_slot in Hfr. rewrite nth_overflow in Hfr; [discriminate|]. rewrite Glen. lia.
  - pose proof (Gsl 0 ltac:(lia)) as (_ & _ & S3). unfold nth_slot in *. replace (Z.to_nat i) with (Z.to_nat 0) in * by lia.
    rewrite Hfr in S3. destruct S3 as (_ & _ & _ & S4). rewrite (S4 Hoff). discriminate.
Qed.

Theorem free_tsim : ltac2:(tb__ "0|6|
S1S1S0S3S3S1eS2S2S31R8A1M0G0S33RaR9A2S42S1fS1fS1fS0S3A2M1S1eA2M2S2A2M3S20G2S2S20G1S1eS20S0S3R9R8A4R6A4R5A4S36RbA1M4A3S42G3S20G2S2S20G1S1eS20S0S3RaR8A4R7A4R5A4G4A3S2bSbSeR7A1SfA3S3eS1fS24S1A2M5G5G5G5S33S25S24S1R2A3S25S24S1R1A3A2Ly;Lx;S5S23S0S35RbR9R8A3A2ReA2S5S23S0S35RaR9R7A3A2RdA2A5F_;F_;F_;F_;F_;F_;Ffr';Ffr;Fi;Fam';Fam;Fg;Ft;Fs;").
Proof.
  intros s t g am am' i fr fr' HWs HWt E Fs Ft Hk.
  pose proof (WF_sheq s t HWs E) as SH.
  destruct (frames_inv s g am i fr HWs Fs) as (Hu & Hi & Hfr). destruct (frames_inv t g am' i fr' HWt Ft) as (Hu' & Hi' & Hfr').
  assert (Hk' : fr_kind fr' = FUser).
  { pose proof (sheq_slot s t g am am' i SH (proj1 (usedX_MT _ _ _ _ Hu)) (proj1 (usedX_MT _ _ _ _ Hu'))) as EN.
    apply erase_slot_inv in EN as [_ FR]. rewrite Hfr, Hfr' in FR. destruct FR as (_ & Ek & _). rewrite Ek. exact Hk. }
  pose proof (free_spec U0 s g am i fr (fun r => WF (snd r)) HWs U0_nonneg Hu Hi Hfr Hk (fun s1 H _ _ => H)) as Ts.
  pose proof (free_spec U0 t g am' i fr' (fun r => WF (snd r)) HWt U0_nonneg Hu' Hi' Hfr' Hk' (fun s1 H _ _ => H)) as Tt.
  assert (SIM : rsim eqr (free (Some (frame_ptr am i fr)) s) (free (Some (frame_ptr am' i fr')) t)).
  { apply (rsim_free _ _ g i); [exact SH | | | apply WF_hdr_known; exact HWs | apply WF_hdr_known; exact HWt].
    - exact (find_frame_in_spec [] None U0 s HWs g am i fr Hu Hi Hfr).
    - exact (find_frame_in_spec [] None U0 t HWt g am' i fr' Hu' Hi' Hfr'). }
  eapply tsim_mono; [|exact (SIM _ _ Ts Tt)]. cbn beta. intros [[] s'] [[] t'] ([_ HS] & _ & _). exact (proj1 HS).
Qed.

Lemma mrel_user_blocks_sizes ms mt : ltac2:(tb__ "0|b|
S4bVms;Vmt;A2S2bS22S1eA1S48S1fS0S1eA2M0S1eS25S0S1eA2M1S43S1fS0S3A2M2G0G2S25S0S3R1A3S3S43S1eG0S1eS21S2A1S22G0A1M3Lx;ScS8R2R1A2A1S2SbG3Lx;SeR1A1S27G0S20S0S1eS19S1cR3R2A2S47S10S18R1A1A2A2S11R1A1A4S29G0A1M4A3G4Xbx2Lfr;G4X21x2Li;S41Z0S45SaR1A1Z1A2A2A4Tam;Lgm;M5S43S1fS0S4A2M6G2G6G6S22G2A1M7Le;R1S0S4S4G7Lm;R1S21S0A1M8G8S29G2A1M9Lnext;Lprev;G9S3S27G2S20S0S3R3R1A4G9A3Lam;X4x3Lm;Lp;X1fx1Le;MaVms;A4A4A4S48G0S1eG1S43G2G0G5S43G6G2GaVmt;A4A4A4A3F_;").
Proof.
  unfold mrel. revert mt. induction ms as [|[q x] ms IH]; intros [|[q' x'] mt] H; cbn [map flat_map] in H |- *; try discriminate; [reflexivity|].
  apply cons_inj in H as [Eqx Et]. unfold ef in Eqx. cbn [fst snd] in Eqx. injection Eqx as Eq Ex. subst q'.
  pose proof (erase_meta_inv _ _ Ex) as INV.
  destruct x as [pr0 nx0| |am]; [subst x'; cbn [flat_map app]; apply IH; exact Et .. |].
  destruct INV as (sl' & -> & ES). cbn [flat_map app]. rewrite !map_app. f_equal; [|apply IH; exact Et]. cbn [snd].
  destruct am as [pr nx mem av frd la sc ml ai sl]. cbn [am_last am_slots am_prev am_next am_mem am_avail am_freed am_sc am_maplen am_aidx] in ES |- *.
  induction (zseq 0 (la + 1)) as [|i is IHi]; cbn [flat_map]; [reflexivity|]. rewrite !map_app. f_equal; [|exact IHi].
  pose proof (map_erase_nth sl sl' (Z.to_nat i) ES) as EN. apply erase_slot_inv in EN as [_ FR]. unfold nth_slot. cbn [am_slots].
  destruct (ss_fr (nth (Z.to_nat i) sl slot_junk)) as [fr|], (ss_fr (nth (Z.to_nat i) sl' slot_junk)) as [fr'|]; try contradiction; [|reflexivity].
  destruct FR as (En & Ek & _). rewrite Ek. destruct (fr_kind fr); cbn; [rewrite En|]; reflexivity.
Qed.

Theorem shape_eq_erases_only_offsets : ltac2:(tb__ "0|6|
S1S1S33R2R1A2S2cS2bS22S1bA1S9R3A1S9R2A1A3S2cS2bS22S0A1M0S13R3A1S13R2A1A3S2cS2bS22S21S0A1A1S12R3A1S12R2A1A3S2cS2bS22S1eA1M1S16R3A1S16R2A1A3S2cS2bS17S14R3A1S14R2A1A3S2cS2bG0S48S1fS0S4A2M2S0S28S0S4A2M3S15R3A1A4S48G2S0G3S15R2A1A4A3S2cS2bS22S1fS40S1eA2A1S39R3A1S39R2A1A3S2bG1S48S1fS0S1eA2M4S1eS25S0S1eA2M5S32R3A1A4S48G4S1eG5S32R2A1A4A3A2A2A2A2A2A2A2F_;Ft;Fs;").
Proof.
  intros s t E. pose proof (proj1 (sq_fields s t) E) as F.
  destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eact & Eus & _ & _ & _ & Ebrk & Ereg & Ear & EM).
  split; [exact Ereg|]. split; [exact Ear|]. split; [exact Eact|]. split; [exact Eus|]. split; [exact Ebrk|].
  split; [apply mrel_keys; exact EM|]. split.
  - unfold footprint, region_of. rewrite Ear, Ereg. reflexivity.
  - unfold user_blocks, used_metas. apply mrel_user_blocks_sizes. exact EM.
Qed.

Theorem malloc_regions : ltac2:(tb__ "0|1|
S1S1eS22S1fS7S1eA2A1S21S0A1M0S1S31R5A1S44Z0R5A2S34S1fG0S1A2S6R6R7A2R5S20G0S1R4R3A4A4S3dS9R4A1S3aS9R8A1R6A2A2F_;F_;F_;Fs';Fp;Ftr;Fn;Fs;").
Proof.
  intros s n tr p s' HW Hn Y. apply same_shape_shp.
  exact (rt_yields _ _ _ tr (p, s') (rt_malloc (st_regions s) n s eq_refl) (malloc_reqs_ok s n HW Hn) Y).
Qed.

Theorem free_regions : ltac2:(tb__ "0|0|
S1S0S1eS22S1fS7S1eA2A1S1S31R5A1S42S1fS0S1eA2S20S0S1eR5R4A4S32R6A1A3S34S1fS24S1A2S5S23S0R6A2R7A2R4S20S24S1S2aR3A4A4S3dS9R4A1S3aS9R8A1R5A2A2F_;F_;F_;Fs';Ftr;Fn;Fp;Fs;").
Proof.
  intros s p n tr s' HW Hin Y. apply same_shape_shp.
  exact (rt_yields _ _ _ tr (tt, s') (rt_free (st_regions s) (Some p) s eq_refl) (free_reqs_ok s p n HW Hin) Y).
Qed.
