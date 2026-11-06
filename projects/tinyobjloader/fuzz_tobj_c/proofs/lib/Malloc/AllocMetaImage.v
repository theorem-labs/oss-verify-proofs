(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "area_cells"; "image"; "loc"; "user_blocks"; "LMem"; "ctx_cells"; "areas_cells"; "meta_slot_cells"; "used_metas"; "MT"; "footprint"; "MCell"; "VP"; "CTX_SIZE"; "LCtx"; "layout_ok"; "region_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "st_areas"; "region"; "SP"; "rkind"; "st_metas"; "st_regions"; "ameta"; "padd"; "PGSZ"; "rg_kind"; "rg_len"; "rg_live"; "st_active"; "st_avail_meta"; "st_avail_meta_area_count"; "st_avail_meta_count"; "st_brk"; "st_free_meta_head"; "st_init_done"; "st_meta_alloc_shift"; "st_usage"; "MRaw"; "astate"; "brkst"; "sptr_eqb"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "cons"; "Some"; "nil"; "option"; "pair"; "app"; "None"; "nat"; "length"; "@Stdlib.Lists.List"; "In"; "flat_map"; "last"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage"; "map_fp"; "nonused"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfFrame MallocWfRepr MallocWfMeta MallocFooter MallocLayout ImageUpd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition nonused (x : option mslot) : Prop :=
  match x with Some (MUsed _) => False | _ => True end.

Section UpdFree.
  Variables (s : astate) (g : sptr) (y : mslot).
  Hypothesis Hx : ltac2:(tb__ "0|0|
S45SeVs;Vg;A2A1").
  Hypothesis Hy : nonused (Some y).
  Let s' : ltac2:(tb__ "0|0|
S2e") := ltac2:(tb__ "0|0|
S46Vg;Vy;Vs;A3").

  Lemma uf_fields : ltac2:(tb__ "0|1|
S1S0S31S16A1S18Vs';A1S18Vs;A1A3S1S0S31S19A1S1dVs';A1S1dVs;A1A3S1S0S2fS28Vs';A1S28Vs;A1A3S1S0S33S2aVs';A1S2aVs;A1A3S1S0S31S40A1S2cVs';A1S2cVs;A1A3S1S0S40S2bVs';A1S2bVs;A1A3S1S0S31S37S16A1M0A1S24Vs';A1S24Vs;A1A3S1S0G0S29Vs';A1S29Vs;A1A3S1S0S16S25Vs';A1S25Vs;A1A3S1S0S40S27Vs';A1S27Vs;A1A3S0S40S26Vs';A1S26Vs;A1A3A2A2A2A2A2A2A2A2A2A2").
  Proof using g y. repeat split; reflexivity. Qed.

  Lemma uf_footprint : ltac2:(tb__ "0|0|
S0S31S32S7S40A2A1SfVs';A1SfVs;A1A3").
  Proof using g y. reflexivity. Qed.
  Lemma uf_ctx_cells : ltac2:(tb__ "0|0|
S0S31S4A1SaVs';A1SaVs;A1A3").
  Proof using g y. reflexivity. Qed.
  Lemma uf_MT q : ltac2:(tb__ "0|1|
S0S37S17A1M0SeVs';Vq;A2S33G0L_;S30Vq;Vg;A2S35S17Vy;A2SeVs;Vq;A2X33x2A3").
  Proof using . unfold s'. apply MT_upd. Qed.

  Lemma uf_used_metas : ltac2:(tb__ "0|0|
S0S31S32S16S1eA2A1SdVs';A1SdVs;A1A3").
  Proof using Hx Hy.
    unfold s', upd_meta, used_metas. cbn [st_metas set_metas].
    unfold MT in Hx. revert Hx. generalize (st_metas s) as l. clear s'.
    induction l as [|[q x] t IH]; cbn; intros Hx.
    - destruct y as [| |am]; [reflexivity|reflexivity|destruct Hy].
    - change (mlookup ((q, x) :: t) g) with (if sptr_eqb g q then Some x else mlookup t g) in Hx.
      destruct (sptr_eqb g q) eqn:E.
      + apply sptr_eqb_eq in E. subst q. cbn in Hx. destruct x as [| |am]; [| |destruct Hx];
          destruct y as [| |am']; try destruct Hy; reflexivity.
      + cbn. rewrite (IH Hx). reflexivity.
  Qed.

  Lemma uf_user_blocks : ltac2:(tb__ "0|0|
S0S31S32S16S40A2A1S8Vs';A1S8Vs;A1A3").
  Proof using Hx Hy. unfold user_blocks. rewrite uf_used_metas. reflexivity. Qed.
  Lemma uf_footers : ltac2:(tb__ "0|0|
S0S31S4A1S41Vs';A1S41Vs;A1A3").
  Proof using Hx Hy. unfold footer_cells. rewrite uf_used_metas. reflexivity. Qed.

  Lemma uf_area_cells_In a next c : ltac2:(tb__ "0|0|
S3dS4Vc;S5Vs';Va;Vnext;A3A3S2S3dS4Vc;S5Vs;Va;Vnext;A3A3S3dS4Vc;ScVg;S35S17Vy;A2A2A3A2F_;").
  Proof using .
    intros Hin. unfold area_cells in *. apply in_app_iff in Hin as [Hin|Hin]; [left; apply in_app_iff; left; exact Hin|].
    apply in_flat_map in Hin as [k [Hk Hin]].
    change (st_metas s') with (mupdate (st_metas s) g y) in Hin.
    rewrite mlookup_mupdate in Hin.
    destruct (sptr_eqb (padd a (AREA_HDR + META_SIZE * Z.of_nat k)) g) eqn:E.
    - apply sptr_eqb_eq in E. rewrite E in Hin. right. exact Hin.
    - left. apply in_app_iff. right. apply in_flat_map. exists k. split; [exact Hk | exact Hin].
  Qed.

  Lemma uf_areas_cells_In l c : ltac2:(tb__ "0|0|
S3dS4Vc;SbVs';Vl;A2A3S2S3dS4Vc;SbVs;Vl;A2A3S3dS4Vc;ScVg;S35S17Vy;A2A2A3A2F_;").
  Proof using .
    induction l as [|a t IH]; cbn [areas_cells]; intros Hin; [destruct Hin|].
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct (uf_area_cells_In a (hd_error t) c Hin) as [H|H]; [left; apply in_app_iff; left; exact H | right; exact H].
    - destruct (IH Hin) as [H|H]; [left; apply in_app_iff; right; exact H | right; exact H].
  Qed.

  Theorem uf_image_In c : ltac2:(tb__ "0|0|
S3dS4Vc;S6Vs';A1A3S2S3dS4Vc;S6Vs;A1A3S3dS4Vc;ScVg;S35S17Vy;A2A2A3A2F_;").
  Proof using Hx Hy.
    intros Hin. unfold image in Hin. rewrite uf_ctx_cells, uf_used_metas in Hin.
    change (st_areas s') with (st_areas s) in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [left; unfold image; apply in_app_iff; left; exact Hin|].
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct (uf_areas_cells_In _ c Hin) as [H|H]; [left | right; exact H].
      unfold image. apply in_app_iff. right. apply in_app_iff. left. exact H.
    - left. unfold image. rewrite !in_app_iff. right. right. exact Hin.
  Qed.

  Lemma uf_area_cells_keep a next c : ltac2:(tb__ "0|0|
S3dS4Vc;S5Vs;Va;Vnext;A3A3S3S3dS4Vc;ScVg;SeVs;Vg;A2A2A3A1S3dS4Vc;S5Vs';Va;Vnext;A3A3F_;F_;").
  Proof using y.
    intros Hin Hng. unfold area_cells in *. apply in_app_iff in Hin as [Hin|Hin]; [apply in_app_iff; left; exact Hin|].
    apply in_flat_map in Hin as [k [Hk Hin]]. apply in_app_iff. right. apply in_flat_map. exists k. split; [exact Hk|].
    change (st_metas s') with (mupdate (st_metas s) g y). rewrite mlookup_mupdate.
    destruct (sptr_eqb (padd a (AREA_HDR + META_SIZE * Z.of_nat k)) g) eqn:E; [|exact Hin].
    apply sptr_eqb_eq in E. rewrite E in Hin. exfalso. apply Hng. unfold MT. exact Hin.
  Qed.

  Lemma uf_layout_ok L : ltac2:(tb__ "0|0|
S14VL;Vs;A2S14VL;Vs';A2F_;").
  Proof using g y. intros H. exact H. Qed.
End UpdFree.

Lemma meta_slot_cells_raw q : ltac2:(tb__ "0|0|
S0S31S4A1ScVq;S35S17S2dA2A2ScVq;S3aS17A1A2A3").
Proof. reflexivity. Qed.

Section CtxOnly.
  Variables (s s' : astate).
  Hypothesis Eareas : ltac2:(tb__ "0|0|
S0S31S16A1S18Vs';A1S18Vs;A1A3").
  Hypothesis Emetas : ltac2:(tb__ "0|0|
S0S31S32S16S17A2A1S1cVs';A1S1cVs;A1A3").

  Lemma co_used_metas : ltac2:(tb__ "0|0|
S0S31S32S16S1eA2A1SdVs';A1SdVs;A1A3").
  Proof using Emetas. unfold used_metas. rewrite Emetas. reflexivity. Qed.
  Lemma co_user_blocks : ltac2:(tb__ "0|0|
S0S31S32S16S40A2A1S8Vs';A1S8Vs;A1A3").
  Proof using Emetas. unfold user_blocks. rewrite co_used_metas. reflexivity. Qed.
  Lemma co_footers : ltac2:(tb__ "0|0|
S0S31S4A1S41Vs';A1S41Vs;A1A3").
  Proof using Emetas. unfold footer_cells. rewrite co_used_metas. reflexivity. Qed.
  Lemma co_area_cells a next : ltac2:(tb__ "0|0|
S0S31S4A1S5Vs';Va;Vnext;A3S5Vs;Va;Vnext;A3A3").
  Proof using Emetas. unfold area_cells. rewrite Emetas. reflexivity. Qed.
  Lemma co_areas_cells l : ltac2:(tb__ "0|0|
S0S31S4A1SbVs';Vl;A2SbVs;Vl;A2A3").
  Proof using Emetas. induction l as [|a t IH]; cbn [areas_cells]; [reflexivity|]. rewrite co_area_cells, IH. reflexivity. Qed.

  Theorem co_image_In c : ltac2:(tb__ "0|0|
S3dS4Vc;S6Vs';A1A3S2S3dS4Vc;S6Vs;A1A3S3dS4Vc;SaVs';A1A3A2F_;").
  Proof using Eareas Emetas.
    intros Hin. unfold image in Hin. rewrite Eareas, co_areas_cells, co_used_metas in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [right; exact Hin|].
    left. unfold image. apply in_app_iff. right. exact Hin.
  Qed.

  Theorem co_image_keep c : ltac2:(tb__ "0|0|
S3dS4Vc;S6Vs;A1A3S3S3dS4Vc;SaVs;A1A3A1S3dS4Vc;S6Vs';A1A3F_;F_;").
  Proof using Eareas Emetas.
    intros Hin Hn. unfold image in *. rewrite Eareas, co_areas_cells, co_used_metas.
    apply in_app_iff in Hin as [Hin|Hin]; [exfalso; exact (Hn Hin)|]. apply in_app_iff. right. exact Hin.
  Qed.
End CtxOnly.

Lemma area_cells_next s a p c : ltac2:(tb__ "0|0|
S3dS4Vc;S5Vs;Va;S35S16Vp;A2A3A3S2S3dS4Vc;S5Vs;Va;S3aS16A1A3A3S0S4Vc;S10S9S1fVa;Z8A2A1U8S11Vp;A1A3A3A2F_;").
Proof.
  intros Hin. unfold area_cells in *. cbn [app optr] in *.
  destruct Hin as [<-|[<-|[<-|Hin]]]; [left; left; reflexivity | right; reflexivity | left; right; right; left; reflexivity |].
  left. right. right. right. exact Hin.
Qed.

Section Append.
  Variables (s s' : astate) (p : sptr).
  Hypothesis Emetas : ltac2:(tb__ "0|0|
S0S31S32S16S17A2A1S1cVs';A1S1cVs;A1A3").
  Hypothesis Eareas : ltac2:(tb__ "0|0|
S0S31S16A1S18Vs';A1S39S16S18Vs;A1S34S16Vp;S36S16A1A3A3A3").

  Lemma ap_used_metas : ltac2:(tb__ "0|0|
S0S31S32S16S1eA2A1SdVs';A1SdVs;A1A3").
  Proof using Emetas. unfold used_metas. rewrite Emetas. reflexivity. Qed.
  Lemma ap_user_blocks : ltac2:(tb__ "0|0|
S0S31S32S16S40A2A1S8Vs';A1S8Vs;A1A3").
  Proof using Emetas. unfold user_blocks. rewrite ap_used_metas. reflexivity. Qed.
  Lemma ap_footers : ltac2:(tb__ "0|0|
S0S31S4A1S41Vs';A1S41Vs;A1A3").
  Proof using Emetas. unfold footer_cells. rewrite ap_used_metas. reflexivity. Qed.
  Lemma ap_area_cells a next : ltac2:(tb__ "0|0|
S0S31S4A1S5Vs';Va;Vnext;A3S5Vs;Va;Vnext;A3A3").
  Proof using Emetas. unfold area_cells. rewrite Emetas. reflexivity. Qed.

  Lemma ap_areas_cells_In l c : ltac2:(tb__ "0|1|
S3dS4Vc;SbVs';S39S16Vl;S34S16Vp;S36S16A1M0A3A3A2A3S2S3dS4Vc;SbVs;Vl;A2A3S2S1S3S0S31S16A1Vl;G0A3A1S0S4Vc;S10S9S1fS3fS16Vl;S1aU0Z0A2A3Z8A2A1U8S11Vp;A1A3A3A2S3dS4Vc;S5Vs;Vp;S3aS16A1A3A3A2A2F_;").
  Proof using Emetas.
    induction l as [|a t IH]; cbn [areas_cells app]; intros Hin.
    - rewrite ap_area_cells in Hin. apply in_app_iff in Hin as [Hin|[]]. right; right. exact Hin.
    - apply in_app_iff in Hin as [Hin|Hin].
      + rewrite ap_area_cells in Hin. destruct t as [|b t'].
        * cbn [hd_error app] in Hin. destruct (area_cells_next s a p c Hin) as [H| ->].
          -- left. apply in_app_iff. left. exact H.
          -- right; left. split; [discriminate | reflexivity].
        * left. apply in_app_iff. left. exact Hin.
      + destruct (IH Hin) as [H|[[Ht ->]|H]].
        * left. apply in_app_iff. right. exact H.
        * right; left. split; [discriminate|]. destruct t as [|b t']; [exfalso; exact (Ht eq_refl)|reflexivity].
        * right; right. exact H.
  Qed.

  Theorem ap_image_In c : ltac2:(tb__ "0|1|
S3dS4Vc;S6Vs';A1A3S2S3dS4Vc;S6Vs;A1A3S2S3dS4Vc;SaVs';A1A3S2S1S3S0S31S16A1S18Vs;A1M0S36S16A1A3A1S0S4Vc;S10S9S1fS3fS16G0S1aU0Z0A2A3Z8A2A1U8S11Vp;A1A3A3A2S3dS4Vc;S5Vs;Vp;S3aS16A1A3A3A2A2A2F_;").
  Proof using Eareas Emetas.
    intros Hin. unfold image in Hin. rewrite Eareas, ap_used_metas in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [right; left; exact Hin|].
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct (ap_areas_cells_In _ c Hin) as [H|[H|H]]; [left | right; right; left; exact H | right; right; right; exact H].
      unfold image. apply in_app_iff. right. apply in_app_iff. left. exact H.
    - left. unfold image. rewrite !in_app_iff. right; right. exact Hin.
  Qed.

  Lemma ap_footprint : ltac2:(tb__ "0|4|
S0S31S32S7S40A2M0A1M1SfVs';A1S34G0S38S7S40S13Z0M2A1S12A4S39G0S42S16G0S16S38S7S40S9R1A1S20A4La;S39S16S18Vs;A1S34S16Vp;S36S16A1A3A3A4S3eS3bG0S3bS37S19A1G1Lx;S15Vs';R1A2S19S1bG1Lx;S21R1A1S36G0A1M3G3S33G1L_;S23R1A1S34G0S38S7S40S9S1aR2G2A2A1S22R1A1A4G3A3G3X33x2X1bx3Lrg;G3X37x2Lk;S43U0S3cS19S1dVs';A1A2A2A4A3A3A3").
  Proof using Eareas. unfold footprint. rewrite Eareas. reflexivity. Qed.
End Append.

Section Regions.
  Variables (s : astate) (rs : list region).
  Let s' := set_regions rs s.
  Lemma rg_ctx_cells : ltac2:(tb__ "0|0|
S0S31S4A1SaVs';A1SaVs;A1A3"). Proof using rs. reflexivity. Qed.
  Lemma rg_image : ltac2:(tb__ "0|0|
S0S31S4A1S6Vs';A1S6Vs;A1A3").
  Proof using rs. unfold image. rewrite rg_ctx_cells, (co_areas_cells s s' eq_refl), (co_used_metas s s' eq_refl). reflexivity. Qed.
  Lemma rg_footers : ltac2:(tb__ "0|0|
S0S31S4A1S41Vs';A1S41Vs;A1A3"). Proof using rs. exact (co_footers s s' eq_refl). Qed.
  Lemma rg_user_blocks : ltac2:(tb__ "0|0|
S0S31S32S16S40A2A1S8Vs';A1S8Vs;A1A3"). Proof using rs. exact (co_user_blocks s s' eq_refl). Qed.
End Regions.

Definition map_fp (s : astate) : list (loc * Z) := ltac2:(tb__ "0|3|
S3eS3bS32S7S40A2M0S3bS37S19A1S31G0A1M1Lx;S15Vs;R1A2S19S1bG1Lx;S21R1A1S36G0A1M2G2S33G1L_;S23R1A1S34G0S38S7S40S9S1aR2Z0A2A1S22R1A1A4G2A3G2X33x2X1bx3Lrg;G2X37x2Lk;S43U0S3cS19S1dVs;A1A2A2A4").

Lemma footprint_eq s : ltac2:(tb__ "0|1|
S0S31S32S7S40A2M0A1SfVs;A1S34G0S38S7S40S13Z0A1S12A4S39G0S42S16G0S16S38S7S40S9R1A1S20A4La;S18Vs;A1A4S44Vs;A1A3A3A3").
Proof. reflexivity. Qed.

