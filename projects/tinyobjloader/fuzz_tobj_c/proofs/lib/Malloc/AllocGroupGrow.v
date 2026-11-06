(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupGrow.GG"; "grown"; "geN'"; "rgN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "keys"; "loc"; "MT"; "LCtx"; "image"; "active_hd"; "footprint"; "user_blocks"; "CTX_mmap_counter"; "LMem"; "ctx_cells"; "mc_loc"; "mc_w"; "CTX_active"; "CTX_usage"; "group_cells"; "used_metas"; "Inv"; "MCell"; "VZ"; "ly_ctx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "usage_of"; "region"; "st_regions"; "st_mmap_counter"; "slot_zero"; "st_areas"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_bounces"; "st_brk"; "st_free_meta_head"; "st_init_done"; "st_meta_alloc_shift"; "st_seq"; "st_unmap_seq"; "MUsed"; "st_usage"; "frame"; "st_active"; "st_area_head"; "st_area_tail"; "st_avail_meta"; "st_avail_meta_count"; "am_set_links"; "ameta"; "brkst"; "META_SIZE"; "astate"; "nth_slot"; "padd"; "sptr_eqb"; "ss_fr"; "st_metas"; "zset"; "RkMap"; "SP"; "lupd"; "mkRegion"; "set_usage"; "@Corelib.Init.Datatypes"; "list"; "option"; "Some"; "bool"; "app"; "prod"; "nil"; "cons"; "None"; "length"; "nat"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupGrow.IG"; "ig"; "ig_new"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupGrow.Post"; "gg_post"; "memN"; "gg_new"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "div"; "of_nat"; "eqb"; "land"; "lt"; "mul"; "pow"; "sub"; "to_nat"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "trailing_cell"; "group_footer_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost"; "ig_am"; "ctr_post"; "ig_post"; "nr_post"; "nr_id"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupGrow"; "ctr_cell"; "gg_amL"; "gg_amS"; "geN'"; "gg_am"; "grown"; "ig"; "rgN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "set_hd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "cmeets"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfRepr MallocFooter MallocLayout
  ImageUpd ImageDelta TryAvailPost FreeNtPost FreeNtImage AllocGroupPost AllocGroupImage AllocMetaImage MapGrow Zones2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition gg_am (mem : sptr) (sc cnt aidx maplen : Z) : ameta := ltac2:(tb__ "0|1|
S38S50S1fA1M0G0S69Vmem;Vsc;Vcnt;Vaidx;Vmaplen;S25A6A3").
Definition gg_amL (m mem : sptr) (sc cnt aidx maplen : Z) : ameta := ltac2:(tb__ "0|1|
S38S4aS1fVm;A2M0G0S69Vmem;Vsc;Vcnt;Vaidx;Vmaplen;S25A6A3").

Definition gg_amS (m mem : sptr) (sc cnt aidx maplen : Z) (sl : slotst) : ameta := ltac2:(tb__ "0|1|
S38S4aS1fVm;A2M0G0S69Vmem;Vsc;Vcnt;Vaidx;Vmaplen;Vsl;A6A3").
Lemma gg_amS_zero m mem sc cnt aidx maplen : ltac2:(tb__ "0|0|
S0S39S70Vm;Vmem;Vsc;Vcnt;Vaidx;Vmaplen;S25A7S6fVm;Vmem;Vsc;Vcnt;Vaidx;Vmaplen;A6A3").
Proof. reflexivity. Qed.

Lemma gg_am_eq mem sc cnt aidx maplen : ltac2:(tb__ "0|0|
S0S39S72Vmem;Vsc;Vcnt;Vaidx;Vmaplen;A5S69Vmem;Vsc;Vcnt;Vaidx;Vmaplen;S25A6A3").
Proof. reflexivity. Qed.

Definition ctr_cell (t : astate) : mcell := ltac2:(tb__ "0|0|
S1cSdS12A1U4S1dS24Vt;A1A1A3").

Section IG.
  Variables (t : astate) (m mem : sptr) (sc cnt aidx maplen : Z) (sl : slotst) (xold : mslot).
  Hypothesis Hsl : ss_fr sl = None.
  Hypothesis ND : NoDup (keys t).
  Hypothesis Hm : ltac2:(tb__ "0|0|
S0S49S20A1ScVt;Vm;A2S4aS20Vxold;A2A3").
  Hypothesis Hold : not_used xold.
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hlen_act : length (st_active t) = 48%nat.
  Hypothesis Hlen_usg : length (st_usage t) = 48%nat.

  Let am1 : ameta := ltac2:(tb__ "0|0|
S69Vmem;Vsc;Vcnt;Vaidx;Vmaplen;Vsl;A6").
  Let amL : ameta := ltac2:(tb__ "0|0|
S70Vm;Vmem;Vsc;Vcnt;Vaidx;Vmaplen;Vsl;A7").
  Let t1 : astate := ltac2:(tb__ "0|0|
S47S42Vsc;S5aS21Vt;Vsc;A2Vcnt;A2S31Vt;A1A3Vt;A2").
  Let t2 : astate := ltac2:(tb__ "0|0|
S76Vm;S30Vam1;A1Vt1;A3").
  Let t3 : astate := ltac2:(tb__ "0|0|
S76Vm;S30VamL;A1Vt2;A3").
  Definition ig : astate := ltac2:(tb__ "0|0|
S77Vsc;S4aS1fVm;A2Vt3;A3").

  Lemma ig_eq : ltac2:(tb__ "0|0|
S0S3cS6bVm;Vsc;Vcnt;Vaidx;Vmaplen;Vmem;Vsl;Vt;A8S55A3").
  Proof using . reflexivity. Qed.

  Lemma ig_keys1 : ltac2:(tb__ "0|0|
S0S48S1fA1SaVt1;A1SaVt;A1A3"). Proof using cnt sc. reflexivity. Qed.
  Lemma ig_MT1 : ltac2:(tb__ "0|0|
S0S49S20A1ScVt1;Vm;A2S4aS20Vxold;A2A3"). Proof using Hm cnt sc. exact Hm. Qed.
  Lemma ig_ND1 : NoDup (keys t1). Proof using ND cnt sc. exact ND. Qed.
  Lemma ig_keys2 : ltac2:(tb__ "0|0|
S0S48S1fA1SaVt2;A1SaVt;A1A3").
  Proof using Hm am1 t1. unfold t2. rewrite (keys_upd_In m (MUsed am1) t1); [reflexivity|]. eapply MT_Some_In_keys. exact ig_MT1. Qed.
  Lemma ig_ND2 : NoDup (keys t2). Proof using Hm ND am1 t1. rewrite ig_keys2. exact ND. Qed.
  Lemma ig_MT2 : ltac2:(tb__ "0|0|
S0S49S20A1ScVt2;Vm;A2S4aS20S30Vam1;A1A2A3"). Proof using aidx maplen mem sl t1. apply MT_upd_same. Qed.
  Lemma ig_keys3 : ltac2:(tb__ "0|0|
S0S48S1fA1SaVt3;A1SaVt;A1A3").
  Proof using Hm amL t2. unfold t3. rewrite (keys_upd_In m (MUsed amL) t2); [exact ig_keys2|]. eapply MT_Some_In_keys. exact ig_MT2. Qed.

  Lemma ig_keys : ltac2:(tb__ "0|0|
S0S48S1fA1SaS55A1SaVt;A1A3"). Proof using Hm. exact ig_keys3. Qed.

  Lemma ig_MT q : ltac2:(tb__ "0|1|
S0S49S20A1M0ScS55Vq;A2S4bG0L_;S3fVq;Vm;A2S4aS20S30VamL;A1A2ScVt;Vq;A2X4bx2A3").
  Proof using .
    unfold ig. rewrite sh_MT. unfold t3, t2.
    destruct (sptr_eqb q m) eqn:E.
    - apply sptr_eqb_eq in E. subst q. apply MT_upd_same.
    - apply sptr_eqb_neq in E. rewrite (MT_upd_other m _ _ q E), (MT_upd_other m _ _ q E). reflexivity.
  Qed.

  Lemma ig_fields : ltac2:(tb__ "0|2|
S1S0S48S22A1S23S55A1S23Vt;A1A3S1S0S48S1fA1S26S55A1S26Vt;A1A3S1S0S3aS2aS55A1S2aVt;A1A3S1S0S4bS2cS55A1S2cVt;A1A3S1S0S5S2dS55A1S2dVt;A1A3S1S0S5S27S55A1S27Vt;A1A3S1S0S1fS28S55A1S28Vt;A1A3S1S0S5S24S55A1S24Vt;A1A3S1S0S5S2eS55A1S2eVt;A1A3S1S0S48S5A1M0S2fS55A1S2fVt;A1A3S1S0G0S29S55A1S29Vt;A1A3S1S0S49S1fA1M1S2bS55A1S2bVt;A1A3S1S0S1fS36S55A1S36Vt;A1A3S1S0S5S37S55A1S37Vt;A1A3S1S0G1S34S55A1S34Vt;A1A3S1S0G1S35S55A1S35Vt;A1A3S1S0G0S31S55A1S42Vsc;S5aS21Vt;Vsc;A2Vcnt;A2S31Vt;A1A3A3S0S48G1A1S33S55A1S45G1S33Vt;A1S64Vsc;A1S4aS1fVm;A2A4A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using . repeat split; reflexivity. Qed.

  Lemma ig_footprint : ltac2:(tb__ "0|0|
S0S48S4dSbS5A2A1S10S55A1S10Vt;A1A3"). Proof using . reflexivity. Qed.

  Lemma ig_usage_sc : ltac2:(tb__ "0|0|
S0S5S21S55Vsc;A2S5aS21Vt;Vsc;A2Vcnt;A2A3").
  Proof using Hlen_act Hlen_usg Hsc.
    unfold usage_of at 1. unfold znth. change (st_usage ig) with (zset sc (usage_of t sc + cnt) (st_usage t)). unfold zset. rewrite nth_zupd, Hlen_usg.
    rewrite Nat.eqb_refl. replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
  Qed.
  Lemma ig_usage_other c : ltac2:(tb__ "0|0|
S5bZ0Vc;A2S4S0S5Vc;Vsc;A3A1S0S5S21S55Vc;A2S21Vt;Vc;A2A3F_;F_;").
  Proof using Hlen_act Hlen_usg Hsc.
    intros Hc NE. unfold usage_of, znth. change (st_usage ig) with (zset sc (usage_of t sc + cnt) (st_usage t)). unfold zset. rewrite nth_zupd.
    replace (Nat.eqb (Z.to_nat c) (Z.to_nat sc)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
  Qed.

  Lemma ig_active_hd c : ltac2:(tb__ "0|1|
S5bZ0Vc;A2S0S49S1fA1M0SfS55Vc;A2S4bG0L_;S5eVc;Vsc;A2S4aS1fVm;A2SfVt;Vc;A2X4bx2A3F_;").
  Proof using Hlen_act Hlen_usg Hsc.
    intros Hc. unfold active_hd, znth. change (st_active ig) with (lupd (st_active t) (Z.to_nat sc) (Some m)). rewrite nth_lupd, Hlen_act.
    destruct (Z.eqb_spec c sc) as [->|NE].
    - rewrite Nat.eqb_refl. replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
    - replace (Nat.eqb (Z.to_nat c) (Z.to_nat sc)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
  Qed.

  Lemma gg_frameless j : ltac2:(tb__ "0|0|
S0S49S32A1S40S3dVamL;Vj;A2A1S50S32A1A3").
  Proof using Hsl aidx cnt m maplen mem sc.
    unfold amL, gg_amS, ig_am, nth_slot. cbn [am_slots am_set_links].
    destruct (nth_in_or_default (Z.to_nat j) (repeat sl (Z.to_nat cnt)) slot_junk) as [H|H]; [|rewrite H; reflexivity].
    apply repeat_spec in H. rewrite H. exact Hsl.
  Qed.
  Lemma gg_frameless1 j : ltac2:(tb__ "0|0|
S0S49S32A1S40S3dVam1;Vj;A2A1S50S32A1A3").
  Proof using Hsl amL. exact (gg_frameless j). Qed.

  Lemma ig_user_blocks : ltac2:(tb__ "0|0|
S0S48S4dS1fS5A2A1S11S55A1S11Vt;A1A3").
  Proof using Hm Hold Hsl ND.
    unfold ig. rewrite sh_user_blocks. unfold t3.
    rewrite (su_user_blocks t2 m am1 amL ig_ND2 ig_MT2 (same_shape_links _ _ _)).
    unfold t2. rewrite (ui_user_blocks t1 m xold am1 ig_ND1 ig_MT1 Hold gg_frameless1). reflexivity.
  Qed.

  Lemma gg_group_footer_cells : ltac2:(tb__ "0|0|
S0S48S9A1S68VamL;A1S4fS9S67VamL;A1S4eS9A1A3A3").
  Proof using Hsl aidx cnt m maplen mem sc.
    unfold group_footer_cells. f_equal. apply flat_map_nil'. intros i _. rewrite gg_frameless. reflexivity.
  Qed.

  Lemma ig_footer_In c : ltac2:(tb__ "0|0|
S65S9Vc;S66S55A1A3S2S65S9Vc;S66Vt;A1A3S0S9Vc;S67VamL;A1A3A2F_;").
  Proof using Hm Hsl ND.
    unfold ig. rewrite sh_footers. unfold t3. rewrite (su_footers t2 m am1 amL ig_ND2 ig_MT2 (same_shape_links _ _ _)).
    intros Hin. destruct (ui_footer_In t1 m xold am1 ig_ND1 ig_MT1 c Hin) as [H|H].
    - left. exact H.
    - right. rewrite <- (group_footer_cells_same am1 amL (same_shape_links _ _ _)) in H. fold amL in H. rewrite gg_group_footer_cells in H.
      destruct H as [<-|[]]. reflexivity.
  Qed.

  Definition ig_new (c : mcell) : Prop := ltac2:(tb__ "0|2|
S2S0SbS15Vc;A1M0SdS5aS18S61Z8Vsc;A2M1A2A1A3S2S0SbG0SdS5aS17G1A2A1A3S2S3S5S5S1S0SbG0S13S3eVm;R1A2A1A3S1S5bZ0R1A2S5bS5aR1S5dS16Vc;A1A1A2S3bA2A2A2Ld;A2S65S9Vc;S19Vm;VamL;A2A3A2A2A2").

  Lemma ig_image_In c : ltac2:(tb__ "0|0|
S65S9Vc;SeS55A1A3S2S65S9Vc;SeVt;A1A3S56Vc;A1A2F_;").
  Proof using Hlen_act Hlen_usg Hm Hsc ND.
    intros Hin. unfold ig_new.
    destruct (sh_image_In t3 sc (Some m) c ltac:(lia) Hin) as [H3|H3].
    2:{ right. right. left. rewrite H3. unfold active_cell. cbn [mc_loc]. reflexivity. }
    destruct (su_image_In t2 m am1 amL ig_ND2 ig_MT2 (same_shape_links _ _ _) c H3) as [H2|[H2|H2]].
    - destruct (ui_image_In t1 m xold am1 ig_ND1 ig_MT1 c H2) as [H1|[H1|H1]].
      + destruct (su_image_In' t sc (usage_of t sc + cnt) c ltac:(lia) H1) as [H0|H0]; [left; exact H0|].
        right. left. rewrite H0. unfold usage_cell. cbn [mc_loc]. reflexivity.
      + right. right. right. left. exact (In_meta_slot_cells m _ c H1).
      + right. right. right. right. destruct (group_cells_same_In m am1 amL c (same_shape_links _ _ _) H1) as [Ho|Ha].
        * exact Ho.
        * rewrite Ha. rewrite (group_cells_eq m amL). right. left. reflexivity.
    - right. right. right. left. exact (In_meta_slot_cells m _ c H2).
    - right. right. right. right. rewrite H2. rewrite (group_cells_eq m amL). right. left. reflexivity.
  Qed.
End IG.

Lemma gg_group_footer_cellsZ m mem sc cnt aidx maplen : ltac2:(tb__ "0|1|
S0S48S9A1S68S6fVm;Vmem;Vsc;Vcnt;Vaidx;Vmaplen;A6M0A1S4fS9S67G0A1S4eS9A1A3A3").
Proof. exact (gg_group_footer_cells m mem sc cnt aidx maplen slot_zero eq_refl). Qed.

Section GG.
  Variables (cur : astate) (len : Z).
  Definition grown : astate := ltac2:(tb__ "0|0|
S6aS6cVlen;Vcur;A2A1").
  Definition rgN : region := ltac2:(tb__ "0|0|
S46S43Vlen;S4eS5A1S54A4").
  Definition geN' : loc * Z := ltac2:(tb__ "0|0|
S53SbS5S13S44S51S22S23Vcur;A1A2Z0A2A1Vlen;A4").

  Lemma grown_fields : ltac2:(tb__ "0|3|
S1S0S48S22A1S23S6A1S4cS22S23Vcur;A1S4fS22S8S4eS22A1A3A3A3S1S0S48S1fA1S26S6A1S26Vcur;A1A3S1S0S48S4dS1fS20A2A1S41S6A1S41Vcur;A1A3S1S0S3aS2aS6A1S2aVcur;A1A3S1S0S48S5A1M0S31S6A1S31Vcur;A1A3S1S0S48S49S1fA1M1A1S33S6A1S33Vcur;A1A3S1S0S4bS2cS6A1S2cVcur;A1A3S1S0S5S2dS6A1S2dVcur;A1A3S1S0S5S27S6A1S27Vcur;A1A3S1S0S1fS28S6A1S28Vcur;A1A3S1S0S5S2eS6A1S2eVcur;A1A3S1S0G0S2fS6A1S2fVcur;A1A3S1S0G0S29S6A1S29Vcur;A1A3S1S0G1S2bS6A1S2bVcur;A1A3S1S0S1fS36S6A1S36Vcur;A1A3S1S0S5S37S6A1S37Vcur;A1A3S1S0G1S34S6A1S34Vcur;A1A3S1S0G1S35S6A1S35Vcur;A1A3S0S5S24S6A1S5fS5aS24Vcur;A1Z1M2A2S63S62Z2Z20A2G2A2A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using . repeat split; reflexivity. Qed.

  Lemma grown_keys : ltac2:(tb__ "0|0|
S0S48S1fA1SaS6A1SaVcur;A1A3"). Proof using . reflexivity. Qed.
  Lemma grown_MT q : ltac2:(tb__ "0|0|
S0S49S20A1ScS6Vq;A2ScVcur;Vq;A2A3"). Proof using . reflexivity. Qed.
  Lemma grown_used_metas : ltac2:(tb__ "0|0|
S0S48S4dS1fS39A2A1S1aS6A1S1aVcur;A1A3"). Proof using . reflexivity. Qed.
  Lemma grown_user_blocks : ltac2:(tb__ "0|0|
S0S48S4dS1fS5A2A1S11S6A1S11Vcur;A1A3"). Proof using . reflexivity. Qed.
  Lemma grown_footers : ltac2:(tb__ "0|0|
S0S48S9A1S66S6A1S66Vcur;A1A3"). Proof using . reflexivity. Qed.
  Lemma grown_usage_of c : ltac2:(tb__ "0|0|
S0S5S21S6Vc;A2S21Vcur;Vc;A2A3"). Proof using . reflexivity. Qed.
  Lemma grown_active_hd c : ltac2:(tb__ "0|0|
S0S49S1fA1SfS6Vc;A2SfVcur;Vc;A2A3"). Proof using . reflexivity. Qed.
  Lemma grown_nr_id : ltac2:(tb__ "0|0|
S0S52S51S22S23Vcur;A1A2S6dVcur;A1A3"). Proof using . reflexivity. Qed.

  Lemma grown_footprint : ltac2:(tb__ "0|1|
S0S48S4dSbS5A2M0A1S10S6A1S4cG0S10Vcur;A1S4fG0S7S4eG0A1A3A3A3").
  Proof using .
    rewrite (footprint_eq grown), (footprint_eq cur). change (st_areas grown) with (st_areas cur).
    pose proof (map_fp_app_map cur rgN eq_refl eq_refl) as E.
    assert (E' : map_fp grown = map_fp (set_regions (st_regions cur ++ [rgN]) cur)) by reflexivity.
    rewrite E', E. cbn [app]. rewrite app_assoc. reflexivity.
  Qed.

  Local Ltac ctx_offs := unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
    CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk,
    CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces in *.

  Lemma grown_ctx_cells_In c : ltac2:(tb__ "0|0|
S65S9Vc;S14S6A1A3S2S65S9Vc;S14Vcur;A1A3S0S9Vc;S6eS6A1A3A2F_;").
  Proof using .
    intros Hin. unfold ctx_cells in Hin |- *.
    pose proof grown_fields as (_ & Far & _ & Fbrk & Fus & Fact & Fini & Fsh & Fac & Fap & Fsq & Fusq & Fbn & Fhd & Fav & Favc & Fah & Fat & Fctr).
    rewrite Far, Fbrk, Fus, Fact, Fini, Fsh, Fac, Fap, Fsq, Fusq, Fbn, Fhd, Fav, Favc, Fah, Fat in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [|left; apply in_app_iff; right; exact Hin].
    cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
      try (left; apply in_app_iff; left; cbn [In]; tauto).
    right. reflexivity.
  Qed.

  Lemma grown_image_In c : ltac2:(tb__ "0|0|
S65S9Vc;S4cS9SeS6A1S66S6A1A3A3S2S65S9Vc;S4cS9SeVcur;A1S66Vcur;A1A3A3S0S9Vc;S6eS6A1A3A2F_;").
  Proof using .
    intros Hin. rewrite grown_footers in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|left; apply in_app_iff; right; exact Hin].
    unfold image in Hin |- *. rewrite grown_used_metas in Hin. change (st_areas grown) with (st_areas cur) in Hin.
    rewrite (areas_cells_metas grown cur (st_areas cur) eq_refl) in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct (grown_ctx_cells_In c Hin) as [H|H]; [left; apply in_app_iff; left; apply in_app_iff; left; exact H | right; exact H].
    - left. apply in_app_iff. left. apply in_app_iff. right. exact Hin.
  Qed.
End GG.

Section Post.
  Variables (cur : astate) (m : sptr) (sc cnt aidx len : Z) (xold : mslot).
  Hypothesis ND : NoDup (keys cur).
  Hypothesis Hm : ltac2:(tb__ "0|0|
S0S49S20A1ScVcur;Vm;A2S4aS20Vxold;A2A3").
  Hypothesis Hold : not_used xold.
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hlen_act : length (st_active cur) = 48%nat.
  Hypothesis Hlen_usg : length (st_usage cur) = 48%nat.

  Definition memN : sptr := SP (nr_id cur) 0.
  Definition gg_post : astate := ltac2:(tb__ "0|0|
S74S73Vcur;Vlen;A2Vm;S58Vsc;Vcnt;Vaidx;S5cVlen;Z1000A2S25A8").
  Let amL : ameta := ltac2:(tb__ "0|0|
S6fVm;S58Vsc;Vcnt;Vaidx;S5cVlen;Z1000A2A6").

  Lemma gg_post_eq : ltac2:(tb__ "0|0|
S0S3cS6bVm;Vsc;Vcnt;Vaidx;S5cVlen;Z1000A2S58S25S6aS6cVlen;Vcur;A2A1A8S57A3").
  Proof using . reflexivity. Qed.

  Let NDg : NoDup (keys (grown cur len)) := ND.
  Let Hmg : MT (grown cur len) m = Some xold := Hm.

  Lemma gg_keys : ltac2:(tb__ "0|0|
S0S48S1fA1SaS57A1SaVcur;A1A3").
  Proof using Hmg. unfold gg_post. rewrite (ig_keys (grown cur len) m memN sc cnt aidx (len / 4096) slot_zero xold Hmg). reflexivity. Qed.
  Lemma gg_MT q : ltac2:(tb__ "0|1|
S0S49S20A1M0ScS57Vq;A2S4bG0L_;S3fVq;Vm;A2S4aS20S30VamL;A1A2ScVcur;Vq;A2X4bx2A3").
  Proof using . unfold gg_post. rewrite (ig_MT (grown cur len) m memN sc cnt aidx (len / 4096) slot_zero). reflexivity. Qed.
  Lemma gg_footprint : ltac2:(tb__ "0|1|
S0S48S4dSbS5A2M0A1S10S57A1S4cG0S10Vcur;A1S4fG0S71Vcur;Vlen;A2S4eG0A1A3A3A3").
  Proof using . unfold gg_post. rewrite (ig_footprint (grown cur len) m memN sc cnt aidx (len / 4096) slot_zero). apply grown_footprint. Qed.
  Lemma gg_user_blocks : ltac2:(tb__ "0|0|
S0S48S4dS1fS5A2A1S11S57A1S11Vcur;A1A3").
  Proof using Hmg Hold NDg. unfold gg_post. rewrite (ig_user_blocks (grown cur len) m memN sc cnt aidx (len / 4096) slot_zero xold eq_refl NDg Hmg Hold). reflexivity. Qed.
  Lemma gg_usage_sc : ltac2:(tb__ "0|0|
S0S5S21S57Vsc;A2S5aS21Vcur;Vsc;A2Vcnt;A2A3").
  Proof using Hlen_act Hlen_usg Hsc. unfold gg_post. rewrite (ig_usage_sc (grown cur len) m memN sc cnt aidx (len / 4096) slot_zero Hsc Hlen_act Hlen_usg). reflexivity. Qed.
  Lemma gg_usage_other c : ltac2:(tb__ "0|0|
S5bZ0Vc;A2S4S0S5Vc;Vsc;A3A1S0S5S21S57Vc;A2S21Vcur;Vc;A2A3F_;F_;").
  Proof using Hlen_act Hlen_usg Hsc. intros Hc NE. unfold gg_post. rewrite (ig_usage_other (grown cur len) m memN sc cnt aidx (len / 4096) slot_zero Hsc Hlen_act Hlen_usg c Hc NE). reflexivity. Qed.
  Lemma gg_active_hd c : ltac2:(tb__ "0|1|
S5bZ0Vc;A2S0S49S1fA1M0SfS57Vc;A2S4bG0L_;S5eVc;Vsc;A2S4aS1fVm;A2SfVcur;Vc;A2X4bx2A3F_;").
  Proof using Hlen_act Hlen_usg Hsc. intros Hc. unfold gg_post. rewrite (ig_active_hd (grown cur len) m memN sc cnt aidx (len / 4096) slot_zero Hsc Hlen_act Hlen_usg c Hc). reflexivity. Qed.

  Lemma gg_fields : ltac2:(tb__ "0|2|
S1S0S48S22A1S23S57A1S4cS22S23Vcur;A1S4fS22S75Vlen;A1S4eS22A1A3A3A3S1S0S48S1fA1S26S57A1S26Vcur;A1A3S1S0S3aS2aS57A1S2aVcur;A1A3S1S0S4bS2cS57A1S2cVcur;A1A3S1S0S5S2dS57A1S2dVcur;A1A3S1S0S5S27S57A1S27Vcur;A1A3S1S0S1fS28S57A1S28Vcur;A1A3S1S0S5S24S57A1S5fS5aS24Vcur;A1Z1M0A2S63S62Z2Z20A2G0A2A2A3S1S0S5S2eS57A1S2eVcur;A1A3S1S0S48S5A1M1S2fS57A1S2fVcur;A1A3S1S0G1S29S57A1S29Vcur;A1A3S0S49S1fA1S2bS57A1S2bVcur;A1A3A2A2A2A2A2A2A2A2A2A2A2").
  Proof using . repeat split; reflexivity. Qed.

  Definition gg_new (c : mcell) : Prop := ltac2:(tb__ "0|2|
S2S0SbS15Vc;A1M0SdS12A1A3S2S0SbG0SdS5aS18S61Z8Vsc;A2M1A2A1A3S2S0SbG0SdS5aS17G1A2A1A3S2S3S5S5S1S0SbG0S13S3eVm;R1A2A1A3S1S5bZ0R1A2S5bS5aR1S5dS16Vc;A1A1A2S3bA2A2A2Ld;A2S2S65S9Vc;S19Vm;VamL;A2A3S0S9Vc;S67VamL;A1A3A2A2A2A2A2").

  Theorem gg_image_In c : ltac2:(tb__ "0|0|
S65S9Vc;S4cS9SeS57A1S66S57A1A3A3S2S65S9Vc;S4cS9SeVcur;A1S66Vcur;A1A3A3S59Vc;A1A2F_;").
  Proof using Hlen_act Hlen_usg Hmg Hsc NDg.
    intros Hin. unfold gg_new. apply in_app_iff in Hin as [Hin|Hin].
    - destruct (ig_image_In (grown cur len) m memN sc cnt aidx (len / 4096) slot_zero xold NDg Hmg Hsc Hlen_act Hlen_usg c Hin) as [H|H].
      + destruct (grown_image_In cur len c ltac:(apply in_app_iff; left; exact H)) as [H0|H0]; [left; exact H0|].
        right. left. rewrite H0. reflexivity.
      + right. right. unfold ig_new in H. fold amL in H. tauto.
    - destruct (ig_footer_In (grown cur len) m memN sc cnt aidx (len / 4096) slot_zero xold eq_refl NDg Hmg c Hin) as [H|H].
      + left. rewrite grown_footers in H. apply in_app_iff. right. exact H.
      + right. right. right. right. right. right. exact H.
  Qed.
End Post.

Section CtrCell.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
  Hypothesis HI : ltac2:(tb__ "0|0|
S1bVX;VR;VU;Vs;A4").
  Hypothesis HX : xraw X s.
  Hypothesis HL : layout_ok L s.

  Lemma ctx_cells_at_ctr c o : ltac2:(tb__ "0|0|
S65S9Vc;S14Vs;A1A3S0SbS15Vc;A1SdVo;A1A3S60Vo;S5aS12Z4A2A2S60S12S5aVo;S5dS16Vc;A1A1A2A2S0S9Vc;S6eVs;A1A3F_;F_;F_;F_;").
  Proof using .
    intros Hin Ho O1 O2. unfold ctr_cell, CTX_mmap_counter in *. unfold ctx_cells in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    - unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
        CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas,
        CTX_seq, CTX_brk in Hin. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc mc_w] in Ho, O2; injection Ho as <-; cbn in O1, O2; try lia. reflexivity.
    - apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]]];
        apply in_map_iff in Hin as (kk & EK & Hkk); apply in_seq in Hkk; subst; cbn [mc_loc mc_w] in Ho, O2; injection Ho as <-;
        unfold CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces in *; lia.
  Qed.

  Lemma ctx_ctr_cell c : ltac2:(tb__ "0|0|
S65S9Vc;S4cS9SeVs;A1S66Vs;A1A3A3S78VL;Vc;S5aS1eVL;A1S12A2Z4A4S0S9Vc;S6eVs;A1A3F_;F_;").
  Proof using HI HL HX.
    intros Hin Hm.
    destruct (ctx_zone X R U s L HI HX HL c CTX_mmap_counter 4 Hin ltac:(unfold CTX_mmap_counter; lia) ltac:(unfold CTX_mmap_counter, CTX_SIZE; lia) Hm) as [Hc (o & E & O1 & O2)].
    exact (ctx_cells_at_ctr c o Hc E O1 O2).
  Qed.
End CtrCell.
