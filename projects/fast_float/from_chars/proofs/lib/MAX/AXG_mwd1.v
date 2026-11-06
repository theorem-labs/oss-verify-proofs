(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngNtfPre MngNtfC AXG_ag0 AXG_ag5 AXG_mwd0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section SD.
Variables (mt : sptr) (r : nat) (maplen : Z) (s3 : astate).

Local Notation amd := (direct_am r maplen).
Local Notation s5 := (dr_s5 mt s3 r maplen).

#[using="Type"] Lemma sd_same : ctx_same6 s3 s5.
Proof. LiaFast.lf_pins LiaFast.u0. unfold dr_s5, dr_s4. cbn. repeat split; reflexivity. Qed.

#[using="Type"] Lemma sd_metas : st_metas s5 = mupdate (st_metas s3) mt (MUsed amd).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma sd_active : st_active s5 = st_active s3.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma sd_usage : st_usage s5 = st_usage s3.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma sd_regions : st_regions s5 = st_regions s3.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma sd_areas : st_areas s5 = st_areas s3.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma sd_lookup : forall q, q <> mt -> mlookup (st_metas s5) q = mlookup (st_metas s3) q.
Proof. LiaFast.lf_pins LiaFast.u0. intros q Hq. rewrite sd_metas. apply mlookup_mupdate_other. exact Hq. Qed.

#[using="Type"] Lemma sd_lookup_mt : mlookup (st_metas s5) mt = Some (MUsed amd).
Proof. LiaFast.lf_pins LiaFast.u0. rewrite sd_metas. apply mlookup_mupdate_same. Qed.

Definition CnewD : list mcell :=
  [ctr_cell (st_mmap_counter s5)] ++ meta_slot_cells mt (Some (MUsed amd)) ++ group_cells mt amd.

Hypothesis Hraw : forall am', mlookup (st_metas s3) mt <> Some (MUsed am').

#[using="Type"] Theorem covD : forall c, In c (image s5) -> In c (image s3) \/ In c CnewD.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (cov_ctx6 s3 s5 c sd_same Hc) as [A|[A|[(k & Hk & A)|(k & Hk & A)]]].
    + left. apply ctx_in_image. exact A.
    + right. unfold CnewD. left. symmetry. exact A.
    + left. rewrite sd_active in A. subst c. apply act_in_ctx_img. exact Hk.
    + left. rewrite sd_usage in A. subst c. apply ctx_in_image. apply usage_in_ctx. exact Hk.
  - apply in_app_iff in Hc as [Hc|Hc].
    + rewrite sd_areas in Hc. destruct (areas_cov1 s3 s5 mt (st_areas s3) c sd_lookup Hc) as [A|A].
      * left. unfold image. apply in_app_iff. right. apply in_app_iff. left. exact A.
      * right. rewrite sd_lookup_mt in A. unfold CnewD. apply in_app_iff. right. apply in_app_iff. left. exact A.
    + apply in_flat_map in Hc as ((q & a) & Hq & Hcq). unfold used_metas in Hq. rewrite sd_metas in Hq.
      destruct (used_cov (st_metas s3) mt amd q a Hq) as [(-> & ->)|A].
      * right. unfold CnewD. apply in_app_iff. right. apply in_app_iff. right. exact Hcq.
      * left. unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (q, a). split; [exact A | exact Hcq].
Qed.

#[using="Hraw"] Theorem revD : forall L c, In c (image s3) -> In c (image s5) \/ exists c', In c' CnewD /\ cell_range L c' = cell_range L c.
Proof. LiaFast.lf_pins (fun (Hraw : LiaFast.U) => LiaFast.u0).
  intros L c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (rev_ctx6 s3 s5 c sd_same Hc) as [A|[A|[(k & Hk & A)|(k & Hk & A)]]].
    + left. apply ctx_in_image. exact A.
    + right. exists (ctr_cell (st_mmap_counter s5)). split; [unfold CnewD; left; reflexivity|]. subst c. reflexivity.
    + left. subst c. rewrite <- sd_active. apply act_in_ctx_img. exact Hk.
    + left. subst c. unfold usg_cell. rewrite <- sd_usage. apply ctx_in_image. apply usage_in_ctx. exact Hk.
  - apply in_app_iff in Hc as [Hc|Hc].
    + destruct (areas_rev1 s3 s5 mt (st_areas s3) c sd_lookup Hc) as [A|A].
      * left. unfold image. apply in_app_iff. right. apply in_app_iff. left. rewrite sd_areas. exact A.
      * right. destruct (msc_shape mt (mlookup (st_metas s3) mt) (Some (MUsed amd)) c A) as (c' & Hc' & E1 & E2).
        exists c'. split; [unfold CnewD; apply in_app_iff; right; apply in_app_iff; left; exact Hc'|]. unfold cell_range. rewrite E1, E2. reflexivity.
    + left. apply in_flat_map in Hc as ((q & a) & Hq & Hcq). unfold image. apply in_app_iff. right. apply in_app_iff. right.
      apply in_flat_map. exists (q, a). split; [|exact Hcq]. unfold used_metas. rewrite sd_metas. exact (used_rev (st_metas s3) mt amd q a Hraw Hq).
Qed.

#[using="Type"] Theorem inD : KS s5 -> forall c, In c CnewD -> In c (image s5).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HK c Hc. unfold CnewD in Hc. cbn [In app] in Hc. destruct Hc as [<-|Hc].
  - apply ctx_in_image. unfold ctx_cells. apply in_app_iff. left. cbn [In]. unfold ctr_cell. repeat first [ (left; reflexivity) | right ].
  - apply in_app_iff in Hc as [Hc|Hc].
    + exact (msc_key_in_image s5 mt (MUsed amd) c HK sd_lookup_mt Hc).
    + unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (mt, amd). split; [|exact Hc].
      unfold used_metas. rewrite sd_metas. apply used_new.
Qed.
End SD.
