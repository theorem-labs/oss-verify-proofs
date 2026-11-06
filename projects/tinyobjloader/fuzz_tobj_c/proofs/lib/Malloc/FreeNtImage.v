(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "st_free_meta_head"; "MUsed"; "MFree"; "astate"; "st_usage"; "ameta"; "st_seq"; "am_set_links"; "am_next"; "frame"; "st_areas"; "st_brk"; "st_init_done"; "st_meta_alloc_shift"; "st_regions"; "st_unmap_seq"; "am_prev"; "st_active"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_bounces"; "brkst"; "nth_slot"; "osptr_eqb"; "region"; "ss_fr"; "am_slots"; "set_seq"; "sptr_eqb"; "st_metas"; "zset"; "bounce_idx"; "set_unmap_seq"; "set_usage"; "slotst"; "@Corelib.Init.Datatypes"; "Some"; "option"; "list"; "app"; "None"; "bool"; "cons"; "nil"; "prod"; "nat"; "pair"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "mcell"; "MT"; "LCtx"; "keys"; "ctx_cells"; "image"; "MCell"; "CTX_seq"; "mc_loc"; "CTX_free_meta_head"; "VZ"; "active_hd"; "CTX_unmap_seq"; "footprint"; "mc_w"; "used_metas"; "CTX_usage"; "ly_ctx"; "user_blocks"; "CTX_active"; "meta_slot_cells"; "area_cells"; "areas_cells"; "optr"; "CTX_SIZE"; "Inv"; "@Stdlib.Lists.List"; "In"; "NoDup"; "flat_map"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "le"; "of_nat"; "mul"; "to_nat"; "eqb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "delta"; "meta_locs"; "set_hd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost"; "fq_post"; "dq_post"; "fgm_s1"; "shape_kept"; "fgd_post"; "fgd_s2"; "fgm_s5"; "seq_post"; "act_post"; "fgm_s2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.FgmDelta.Gen"; "an1"; "dq_s1b"; "dq_s1c"; "dq_s1a"; "dq_locs"; "@Corelib.Lists.ListDef"; "nth"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage"; "deltaU"; "seq_locs_b"; "seq_locs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "cmeets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.FqDelta.Ring"; "fq_next'"; "fq_t3"; "fq_t4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.Seq"; "seq_locs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.FgmDelta.Tail"; "rec_locs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.SetUsage"; "usage_cell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.SetUseq"; "useq_cell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost"; "am_activate"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfRepr MallocFooter ImageUpd ImageDelta TryAvailPost FreeNtPost Zones2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition not_used (x : mslot) : Prop := match x with MUsed _ => False | _ => True end.

Lemma flat_map_nil' {A B} (f : A -> list B) l : ltac2:(tb__ "0|2|
VA;S51VA;R1Vl;A3S0S2cVB;A1M0Vf;R2A1S31VB;A1M1A3F_;Fa;S0G0S53VA;VB;Vf;Vl;A4G1A3F_;").
Proof. induction l as [|a t IH]; intros H; [reflexivity|]. cbn. rewrite (H a ltac:(left; reflexivity)), IH; [reflexivity|]. intros b Hb. apply H. right. exact Hb. Qed.

Section NonUsedUpd.
  Variables (s : astate) (g : sptr) (xold xnew : mslot).
  Hypothesis ND : NoDup (keys s).
  Hypothesis Hg : ltac2:(tb__ "0|0|
S0S2bS6A1S38Vs;Vg;A2S2aS6Vxold;A2A3").
  Hypothesis Hnew : not_used xnew.
  Let s' : ltac2:(tb__ "0|0|
Sa") := ltac2:(tb__ "0|0|
S6aVg;Vxnew;Vs;A3").

  Lemma nu_used_metas_In q a : ltac2:(tb__ "0|2|
S51S32S5ScA2M0S34S5ScVq;Va;A4M1S46Vs';A1A3S1S2S0S5Vq;Vg;A3A1S51G0G1S46Vs;A1A3A2F_;").
  Proof using Hg Hnew ND.
    unfold s', upd_meta, used_metas. cbn [st_metas set_metas]. unfold MT in Hg. unfold keys in ND.
    revert ND Hg. generalize (st_metas s) as l. clear s'.
    induction l as [|[q' x] t IH]; intros ND Hl Hin; [discriminate|].
    cbn [mupdate] in Hin. cbn [mlookup] in Hl. inversion ND as [|q0 t0 Hq Ht]; subst.
    destruct (sptr_eqb g q') eqn:E.
    - apply sptr_eqb_eq in E. subst q'. cbn [flat_map] in Hin. apply in_app_iff in Hin as [Hin|Hin].
      + exfalso. destruct xnew; cbn in Hin; first [exact Hin | exact Hnew].
      + split.
        * intros ->. apply Hq. apply in_flat_map in Hin as [[p m] [Hp Hm]]. apply in_map_iff. exists (p, m). split; [|exact Hp].
          destruct m; cbn in Hm; try (destruct Hm as [Hm|[]]; injection Hm as -> _; reflexivity); destruct Hm.
        * cbn [flat_map]. apply in_app_iff. right. exact Hin.
    - cbn [flat_map] in Hin |- *. apply in_app_iff in Hin as [Hin|Hin].
      + split; [|apply in_app_iff; left; exact Hin]. intros ->.
        destruct x; cbn in Hin; try (exact Hin). destruct Hin as [Hin|[]]. injection Hin as E1 E2. rewrite E1, sptr_eqb_refl in E. discriminate.
      + destruct (IH Ht Hl Hin) as [A B]. split; [exact A | apply in_app_iff; right; exact B].
  Qed.

  Lemma nu_used_metas_back q a : ltac2:(tb__ "0|2|
S2S0S5Vq;Vg;A3A1S51S32S5ScA2M0S34S5ScVq;Va;A4M1S46Vs;A1A3S51G0G1S46Vs';A1A3F_;F_;").
  Proof using xnew.
    unfold s', upd_meta, used_metas. cbn [st_metas set_metas]. generalize (st_metas s) as l. clear s' Hg ND.
    induction l as [|[q' x] t IH]; intros Hq Hin; [destruct Hin|].
    cbn [mupdate]. cbn [flat_map] in Hin. apply in_app_iff in Hin as [Hin|Hin].
    - destruct x; cbn in Hin; try (exact (False_ind _ Hin)). destruct Hin as [Hin|[]]. injection Hin as -> ->.
      replace (sptr_eqb g q) with false by (symmetry; apply sptr_eqb_neq; intros E; exact (Hq (eq_sym E))). cbn. left. reflexivity.
    - destruct (sptr_eqb g q'); cbn [flat_map]; apply in_app_iff; right; [exact Hin | apply IH; assumption].
  Qed.

  Lemma nu_fields : ltac2:(tb__ "0|1|
S1S0S2cS5A1M0S11Vs';A1S11Vs;A1A3S1S0S2cS1fA1S15Vs';A1S15Vs;A1A3S1S0S1cS12Vs';A1S12Vs;A1A3S1S0S2fS13Vs';A1S13Vs;A1A3S1S0S2cS5bA1SbVs';A1SbVs;A1A3S1S0S5bS14Vs';A1S14Vs;A1A3S1S0S2cS32S36S5bA2A1S44Vs';A1S44Vs;A1A3S1S0S2cS37A1S3bVs';A1S3bVs;A1A3S0G0S3aVs';A1S3aVs;A1A3A2A2A2A2A2A2A2A2").
  Proof using Hg xnew. repeat split; try reflexivity. unfold s'. apply keys_upd_In. eapply MT_Some_In_keys. exact Hg. Qed.

  Lemma nu_area_cells_In a next c : ltac2:(tb__ "0|0|
S51S37Vc;S4cVs';Va;Vnext;A3A3S3S51S37Vc;S4cVs;Va;Vnext;A3A3S51S37Vc;S4bVg;S2aS6Vxnew;A2A2A3A2F_;").
  Proof using .
    intros Hin. unfold area_cells in *. apply in_app_iff in Hin as [Hin|Hin]; [left; apply in_app_iff; left; exact Hin|].
    apply in_flat_map in Hin as [k [Hk Hin]].
    change (st_metas s') with (mupdate (st_metas s) g xnew) in Hin.
    rewrite mlookup_mupdate in Hin.
    destruct (sptr_eqb (padd a (AREA_HDR + META_SIZE * Z.of_nat k)) g) eqn:E.
    - apply sptr_eqb_eq in E. rewrite E in Hin. right. exact Hin.
    - left. apply in_app_iff. right. apply in_flat_map. exists k. split; [exact Hk | exact Hin].
  Qed.

  Lemma nu_areas_cells_In l c : ltac2:(tb__ "0|0|
S51S37Vc;S4dVs';Vl;A2A3S3S51S37Vc;S4dVs;Vl;A2A3S51S37Vc;S4bVg;S2aS6Vxnew;A2A2A3A2F_;").
  Proof using .
    induction l as [|a t IH]; cbn [areas_cells]; intros Hin; [destruct Hin|].
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct (nu_area_cells_In a (hd_error t) c Hin) as [H|H]; [left; apply in_app_iff; left; exact H | right; exact H].
    - destruct (IH Hin) as [H|H]; [left; apply in_app_iff; right; exact H | right; exact H].
  Qed.

  Theorem nu_image_In c : ltac2:(tb__ "0|0|
S51S37Vc;S3cVs';A1A3S3S51S37Vc;S3cVs;A1A3S51S37Vc;S4bVg;S2aS6Vxnew;A2A2A3A2F_;").
  Proof using Hg Hnew ND.
    intros Hin. unfold image in Hin. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 nu_fields)))))))) in Hin.
    change (st_areas s') with (st_areas s) in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [left; unfold image; apply in_app_iff; left; exact Hin|].
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct (nu_areas_cells_In _ c Hin) as [H|H]; [left | right; exact H].
      unfold image. apply in_app_iff. right. apply in_app_iff. left. exact H.
    - apply in_flat_map in Hin as [[q a] [Hq Hc]]. cbn [fst snd] in Hc.
      destruct (nu_used_metas_In q a Hq) as [Hne Hold]. left. apply (In_image_group s q a c Hold Hc).
  Qed.

  Theorem nu_footer_In c : ltac2:(tb__ "0|0|
S51S37Vc;S69Vs';A1A3S51S37Vc;S69Vs;A1A3F_;").
  Proof using Hg Hnew ND.
    intros Hin. unfold footer_cells in *. apply in_flat_map in Hin as [[q a] [Hq Hc]]. cbn [snd] in Hc.
    destruct (nu_used_metas_In q a Hq) as [Hne Hold]. apply in_flat_map. exists (q, a). auto.
  Qed.

  Hypothesis Hframeless : ltac2:(tb__ "0|0|
ScS0S6Vxold;S8R1A1A3S5bS0S2bS10A1S20S1dR3R1A2A1S2eS10A1A3Fj;F_;Fam;").

  Lemma nu_user_blocks : ltac2:(tb__ "0|0|
S0S2cS32S5S5bA2A1S49Vs';A1S49Vs;A1A3").
  Proof using Hframeless Hg Hnew ND.
    unfold user_blocks, s', upd_meta, used_metas. cbn [st_metas set_metas]. unfold MT in Hg. unfold keys in ND.
    revert ND Hg. generalize (st_metas s) as l. clear s'.
    induction l as [|[q' x] t IH]; intros ND Hl; [discriminate|].
    cbn [mupdate]. cbn [mlookup] in Hl. inversion ND as [|q0 t0 Hq Ht]; subst.
    destruct (sptr_eqb g q') eqn:E.
    - apply sptr_eqb_eq in E. subst q'. injection Hl as ->. cbn [flat_map].
      assert (L0 : forall am0, xold = MUsed am0 ->
                flat_map (fun i0 => match ss_fr (nth_slot am0 i0) with
                                    | Some fr => match fr_kind fr with FUser => [(padd (slot_start am0 i0) (UNIT * fr_off fr), fr_n fr)] | FGroup => [] end
                                    | None => [] end) (zseq 0 (am_last am0 + 1)) = []).
      { intros am0 E0. apply flat_map_nil'. intros j _. rewrite (Hframeless am0 E0 j). reflexivity. }
      destruct xnew; try (exfalso; exact Hnew); destruct xold as [| |am0]; cbn [flat_map app snd]; try reflexivity; rewrite (L0 am0 eq_refl); reflexivity.
    - cbn [flat_map]. rewrite !flat_map_app, (IH Ht Hl). reflexivity.
  Qed.

  Theorem delta_nu : ltac2:(tb__ "0|0|
S5cVs;Vs';S5dVg;A1A3").
  Proof using Hframeless Hg Hnew ND.
    pose proof nu_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    unfold delta. rewrite nu_user_blocks. repeat split; try assumption; try reflexivity.
    intros c Hc. apply in_app_iff in Hc as [Hc|Hc].
    - destruct (nu_image_In c Hc) as [H|H]; [left; apply in_app_iff; left; exact H | right; exact (meta_slot_cells_locs g _ c H)].
    - left. apply in_app_iff. right. exact (nu_footer_In c Hc).
  Qed.

  Lemma nu_shape : shape_kept s s'.
  Proof using Hnew g.
    intros q aq Hq. unfold s' in Hq. destruct (sptr_eq_dec q g) as [->|Hne].
    - rewrite MT_upd_same in Hq. exfalso. injection Hq as E. subst xnew. exact Hnew.
    - rewrite (MT_upd_other g _ s q Hne) in Hq. exists aq. auto 7.
  Qed.
End NonUsedUpd.

Section Seq.
  Variable s : astate.
  Let s' := seq_post s.

  Lemma seq_fields : ltac2:(tb__ "0|3|
S1S0S2cS5A1M0S11Vs';A1S11Vs;A1A3S1S0S2cS1fA1S15Vs';A1S15Vs;A1A3S1S0S1cS12Vs';A1S12Vs;A1A3S1S0S2fS13Vs';A1S13Vs;A1A3S1S0S2cS5bA1M1SbVs';A1SbVs;A1A3S1S0S5bS14Vs';A1S14Vs;A1A3S1S0S2cS32S36S5bA2A1S44Vs';A1S44Vs;A1A3S1S0G0S3aVs';A1S3aVs;A1A3S1S0S2cS32S5S6A2A1S24Vs';A1S24Vs;A1A3S1S0S2bS5A1M2S7Vs';A1S7Vs;A1A3S1S0S2cG2A1S18Vs';A1S18Vs;A1A3S1S0G1S1bVs';A1S1bVs;A1A3S1S0S5bS19Vs';A1S19Vs;A1A3S0S5S1aVs';A1S1aVs;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using . unfold s', seq_post. destruct (st_seq s =? 255); repeat split; reflexivity. Qed.

  Lemma seq_MT q : ltac2:(tb__ "0|0|
S0S2bS6A1S38Vs';Vq;A2S38Vs;Vq;A2A3").
  Proof using . unfold MT. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 seq_fields))))))))). reflexivity. Qed.
  Lemma seq_used_metas : ltac2:(tb__ "0|0|
S0S2cS32S5ScA2A1S46Vs';A1S46Vs;A1A3").
  Proof using . unfold used_metas. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 seq_fields))))))))). reflexivity. Qed.

  Definition seq_locs : list loc := ltac2:(tb__ "0|0|
S30S36S39S3eA1S71S33S36S33S39S54S43S57R1A1A2A1Lk;S72U0U20A2A4A3").

  Lemma seq_ctx_cells_In c : ltac2:(tb__ "0|0|
S51S37Vc;S3bVs';A1A3S3S51S37Vc;S3bVs;A1A3S51S36S3fVc;A1S7aA3A2F_;").
  Proof using .
    unfold s', seq_post. intros Hin.
    assert (GEN : forall sq usq, In c (ctx_cells (set_seq sq (set_unmap_seq usq s))) -> In c (ctx_cells s) \/ In (mc_loc c) seq_locs).
    { clear Hin. intros sq usq Hin. unfold ctx_cells in Hin |- *.
      cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count st_avail_meta_area_count
           st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage st_unmap_seq st_bounces set_seq set_unmap_seq] in Hin.
      apply in_app_iff in Hin as [Hin|Hin].
      - cbn [In] in Hin.
        repeat (destruct Hin as [<-|Hin]; [first [right; left; reflexivity | left; apply in_app_iff; left; cbn; tauto]|]). destruct Hin.
      - apply in_app_iff in Hin as [Hin|Hin]; [left; apply in_app_iff; right; apply in_app_iff; left; exact Hin|].
        apply in_app_iff in Hin as [Hin|Hin]; [left; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hin|].
        apply in_app_iff in Hin as [Hin|Hin].
        + right. right. apply in_map_iff in Hin as (k & <- & Hk). apply in_map_iff. exists k. auto.
        + left. apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right. exact Hin. }
    destruct (st_seq s =? 255).
    - exact (GEN _ _ Hin).
    - apply (GEN (st_seq s + 1) (st_unmap_seq s)).
      replace (set_unmap_seq (st_unmap_seq s) s) with s by (destruct s; reflexivity). exact Hin.
  Qed.

  Theorem delta_seq : ltac2:(tb__ "0|0|
S5cVs;Vs';S7aA3").
  Proof using .
    pose proof seq_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14).
    unfold delta. unfold user_blocks, footer_cells. rewrite seq_used_metas. repeat split; try assumption; try reflexivity.
    intros c Hc. apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; right; exact Hc].
    unfold image in Hc. rewrite F1 in Hc. apply in_app_iff in Hc as [Hc|Hc].
    - destruct (seq_ctx_cells_In c Hc) as [H|H]; [left; apply in_app_iff; left; unfold image; apply in_app_iff; left; exact H | right; exact H].
    - left. apply in_app_iff. left. unfold image. apply in_app_iff. right.
      rewrite (areas_cells_metas s' s (st_areas s) F9) in Hc. rewrite seq_used_metas in Hc. exact Hc.
  Qed.

  Lemma seq_shape : shape_kept s s'.
  Proof using . intros q aq Hq. rewrite seq_MT in Hq. exists aq. auto 7. Qed.
End Seq.

Section Fhead.
  Variables (s : astate) (v : option sptr).
  Let s' := set_free_meta_head v s.

  Lemma fh_ctx_cells_In c : ltac2:(tb__ "0|0|
S51S37Vc;S3bVs';A1A3S3S51S37Vc;S3bVs;A1A3S0S36S3fVc;A1S39S40A1A3A2F_;").
  Proof using v.
    intros Hin. unfold ctx_cells in Hin |- *. cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage st_unmap_seq st_bounces set_free_meta_head s'] in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [|left; apply in_app_iff; right; exact Hin].
    cbn [In] in Hin.
    repeat (destruct Hin as [<-|Hin]; [first [right; reflexivity | left; apply in_app_iff; left; cbn; tauto]|]). destruct Hin.
  Qed.

  Theorem delta_fhead : ltac2:(tb__ "0|0|
S5cVs;Vs';S30S36S39S40A1S31S36A1A3A3").
  Proof using v.
    unfold delta. repeat split; try reflexivity.
    intros c Hc. apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; right; exact Hc].
    unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
    - destruct (fh_ctx_cells_In c Hc) as [H|H]; [left; apply in_app_iff; left; unfold image; apply in_app_iff; left; exact H | right; left; symmetry; exact H].
    - left. apply in_app_iff. left. unfold image. apply in_app_iff. right.
      change (st_areas s') with (st_areas s) in Hc. change (used_metas s') with (used_metas s) in Hc.
      rewrite (areas_cells_metas s' s (st_areas s) eq_refl) in Hc. exact Hc.
  Qed.

  Lemma fh_MT q : ltac2:(tb__ "0|0|
S0S2bS6A1S38Vs';Vq;A2S38Vs;Vq;A2A3"). Proof using v. reflexivity. Qed.
  Lemma fh_shape : shape_kept s s'.
  Proof using v. intros q aq Hq. exists aq. auto 7. Qed.
End Fhead.

Section CtxCells.
  Variable s : astate.

  Lemma ctx_cells_at_hdr c o (off : Z) (w : nat) val : ltac2:(tb__ "0|3|
S51S37S3dS39Voff;A1Vw;Vval;A3M0S3bVs;A1M1A3S51S37Vc;G1A3S0S36S3fVc;A1S39Vo;A1A3S55Vo;S54Voff;S57Vw;A1A2M2A2S55Voff;S54Vo;S57S45Vc;A1A1A2A2S3S56G2S4aA2S56S3eVoff;A2A2S56G2S4fA2S37S51S37R1G1A3S5bS0S36S3fR3A1S39R1A1A3S55R2G2A2S55Voff;S54R3S57S45R5A1A1A2A2S0S37R6G0A3F_;F_;F_;Fo';F_;Fc';S0S37Vc;G0A3F_;F_;F_;F_;F_;F_;F_;F_;").
  Proof using . intros _ Hc Ho O1 O2 _ _ UNIQ. exact (UNIQ c Hc o Ho O1 O2). Qed.

  Ltac hdr_cases Hin :=
    unfold ctx_cells in Hin; apply in_app_iff in Hin as [Hin|Hin];
    [ unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
        CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas,
        CTX_seq, CTX_brk in Hin; cbn [In] in Hin
    | apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]]];
      apply in_map_iff in Hin as (kk & EK & Hkk); apply in_seq in Hkk; subst ].

  Lemma ctx_cells_at_seq c o : ltac2:(tb__ "0|0|
S51S37Vc;S3bVs;A1A3S0S36S3fVc;A1S39Vo;A1A3S55Vo;S54S3eZ1A2A2S55S3eS54Vo;S57S45Vc;A1A1A2A2S0S37Vc;S3dS39S3eA1U1S41SdVs;A1A1A3A3F_;F_;F_;F_;").
  Proof using .
    intros Hin Ho O1 O2. unfold CTX_seq in *. hdr_cases Hin.
    - destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc mc_w] in Ho, O2; injection Ho as <-; cbn in O1, O2; try lia. reflexivity.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_active in *. lia.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_usage in *. lia.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_unmap_seq in *. lia.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_bounces in *. lia.
  Qed.

  Lemma ctx_cells_at_fmh c o : ltac2:(tb__ "0|0|
S51S37Vc;S3bVs;A1A3S0S36S3fVc;A1S39Vo;A1A3S55Vo;S54S40Z8A2A2S55S40S54Vo;S57S45Vc;A1A1A2A2S0S37Vc;S3dS39S40A1U8S4eS7Vs;A1A1A3A3F_;F_;F_;F_;").
  Proof using .
    intros Hin Ho O1 O2. unfold CTX_free_meta_head in *. hdr_cases Hin.
    - destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc mc_w] in Ho, O2; injection Ho as <-; cbn in O1, O2; try lia. reflexivity.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_active in *. lia.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_usage in *. lia.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_unmap_seq in *. lia.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_bounces in *. lia.
  Qed.

  Lemma ctx_cells_at_usage c (k : Z) o : ltac2:(tb__ "0|3|
S1S56Z0M0Vk;A2S55Vk;Z30A2A2S51S37Vc;S3bVs;A1A3S0S36S3fVc;A1S39Vo;A1A3S55Vo;S54S54S47S58Z8M1Vk;A2A2M2G1A2A2S55G2S54Vo;S57S45Vc;A1A1A2A2S0S37Vc;S3dS39G2A1U8S41S70S5bS59Vk;A1SbVs;A1G0A4A1A3A3F_;F_;F_;F_;F_;").
  Proof using .
    intros Hk Hin Ho O1 O2. unfold CTX_usage in *. hdr_cases Hin.
    - destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc mc_w] in Ho, O2; injection Ho as <-; cbn in O1, O2; lia.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_active in *. lia.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as Eo. unfold CTX_usage in *. assert (Z.of_nat kk = k) as <- by lia. rewrite Nat2Z.id. reflexivity.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_unmap_seq in *. lia.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_bounces in *. lia.
  Qed.

  Lemma ctx_cells_at_useq c (k : Z) o : ltac2:(tb__ "0|2|
S1S56Z0M0Vk;A2S55Vk;Z20A2A2S51S37Vc;S3bVs;A1A3S0S36S3fVc;A1S39Vo;A1A3S55Vo;S54S54S43Vk;A2M1Z1A2A2S55G1S54Vo;S57S45Vc;A1A1A2A2S0S37Vc;S3dS39G1A1U1S41S70S5bS59Vk;A1S16Vs;A1G0A4A1A3A3F_;F_;F_;F_;F_;").
  Proof using .
    intros Hk Hin Ho O1 O2. unfold CTX_unmap_seq in *. hdr_cases Hin.
    - destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc mc_w] in Ho, O2; injection Ho as <-; cbn in O1, O2; lia.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_active in *. lia.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_usage in *. lia.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as Eo. unfold CTX_unmap_seq in *. assert (Z.of_nat kk = k) as <- by lia. rewrite Nat2Z.id. reflexivity.
    - cbn [mc_loc mc_w] in Ho, O2. injection Ho as <-. unfold CTX_bounces in *. lia.
  Qed.
End CtxCells.

Section CtxZone.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
  Hypothesis HI : ltac2:(tb__ "0|0|
S50VX;VR;VU;Vs;A4").
  Hypothesis HX : xraw X s.
  Hypothesis HL : layout_ok L s.

  Lemma ctx_seq_cell c : ltac2:(tb__ "0|0|
S51S37Vc;S2dS37S3cVs;A1S69Vs;A1A3A3S76VL;Vc;S54S48VL;A1S3eA2Z1A4S0S37Vc;S3dS39S3eA1U1S41SdVs;A1A1A3A3F_;F_;").
  Proof using HI HL HX.
    intros Hin Hm.
    destruct (ctx_zone X R U s L HI HX HL c CTX_seq 1 Hin ltac:(unfold CTX_seq; lia) ltac:(unfold CTX_seq, CTX_SIZE; lia) Hm) as [Hc (o & E & O1 & O2)].
    exact (ctx_cells_at_seq s c o Hc E O1 O2).
  Qed.
  Lemma ctx_fmh_cell c : ltac2:(tb__ "0|0|
S51S37Vc;S2dS37S3cVs;A1S69Vs;A1A3A3S76VL;Vc;S54S48VL;A1S40A2Z8A4S0S37Vc;S3dS39S40A1U8S4eS7Vs;A1A1A3A3F_;F_;").
  Proof using HI HL HX.
    intros Hin Hm.
    destruct (ctx_zone X R U s L HI HX HL c CTX_free_meta_head 8 Hin ltac:(unfold CTX_free_meta_head; lia) ltac:(unfold CTX_free_meta_head, CTX_SIZE; lia) Hm) as [Hc (o & E & O1 & O2)].
    exact (ctx_cells_at_fmh s c o Hc E O1 O2).
  Qed.
  Lemma ctx_usage_cell c k : ltac2:(tb__ "0|3|
S1S56Z0M0Vk;A2S55Vk;Z30A2A2S51S37Vc;S2dS37S3cVs;A1S69Vs;A1A3A3S76VL;Vc;S54S48VL;A1S54S47S58Z8M1Vk;A2A2M2A2G1A4S0S37Vc;S3dS39G2A1U8S41S70S5bS59Vk;A1SbVs;A1G0A4A1A3A3F_;F_;F_;").
  Proof using HI HL HX.
    intros Hk Hin Hm.
    destruct (ctx_zone X R U s L HI HX HL c (CTX_usage + 8 * k) 8 Hin ltac:(unfold CTX_usage; lia) ltac:(unfold CTX_usage, CTX_SIZE; lia) Hm) as [Hc (o & E & O1 & O2)].
    exact (ctx_cells_at_usage s c k o Hk Hc E O1 O2).
  Qed.
  Lemma ctx_useq_cell c k : ltac2:(tb__ "0|2|
S1S56Z0M0Vk;A2S55Vk;Z20A2A2S51S37Vc;S2dS37S3cVs;A1S69Vs;A1A3A3S76VL;Vc;S54S48VL;A1S54S43Vk;A2M1A2Z1A4S0S37Vc;S3dS39G1A1U1S41S70S5bS59Vk;A1S16Vs;A1G0A4A1A3A3F_;F_;F_;").
  Proof using HI HL HX.
    intros Hk Hin Hm.
    destruct (ctx_zone X R U s L HI HX HL c (CTX_unmap_seq + k) 1 Hin ltac:(unfold CTX_unmap_seq; lia) ltac:(unfold CTX_unmap_seq, CTX_SIZE; lia) Hm) as [Hc (o & E & O1 & O2)].
    exact (ctx_cells_at_useq s c k o Hk Hc E O1 O2).
  Qed.
End CtxZone.

Section SeqInc.
  Variable s : astate.
  Hypothesis Hne : st_seq s <> 255.
  Lemma seq_post_inc : ltac2:(tb__ "0|0|
S0SaS66Vs;A1S22S54SdVs;A1Z1A2Vs;A2A3").
  Proof using Hne. unfold seq_post. rewrite (proj2 (Z.eqb_neq _ _) Hne). reflexivity. Qed.
  Lemma seq_inc_ctx_cells_In c : ltac2:(tb__ "0|0|
S51S37Vc;S3bS22S54SdVs;A1Z1A2Vs;A2A1A3S3S51S37Vc;S3bVs;A1A3S0S36S3fVc;A1S39S3eA1A3A2F_;").
  Proof using .
    intros Hin. unfold ctx_cells in Hin |- *. cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage st_unmap_seq st_bounces set_seq] in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [|left; apply in_app_iff; right; exact Hin].
    cbn [In] in Hin.
    repeat (destruct Hin as [<-|Hin]; [first [right; reflexivity | left; apply in_app_iff; left; cbn; tauto]|]). destruct Hin.
  Qed.
  Theorem delta_seq_inc : ltac2:(tb__ "0|0|
S5cVs;S66Vs;A1S30S36S39S3eA1S31S36A1A3A3").
  Proof using Hne.
    rewrite seq_post_inc. unfold delta. repeat split; try reflexivity.
    intros c Hc. apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; right; exact Hc].
    unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
    - destruct (seq_inc_ctx_cells_In c Hc) as [H|H]; [left; apply in_app_iff; left; unfold image; apply in_app_iff; left; exact H | right; left; symmetry; exact H].
    - left. apply in_app_iff. left. unfold image. apply in_app_iff. right.
      change (st_areas (set_seq (st_seq s + 1) s)) with (st_areas s) in Hc. change (used_metas (set_seq (st_seq s + 1) s)) with (used_metas s) in Hc.
      rewrite (areas_cells_metas (set_seq (st_seq s + 1) s) s (st_areas s) eq_refl) in Hc. exact Hc.
  Qed.
End SeqInc.

Definition seq_locs_b (s : astate) : list loc := ltac2:(tb__ "0|0|
S2fS2cS36A1L_;S5aSdVs;A1ZffA2S75S30S36S39S3eA1S31S36A1A3X2fx2").
Lemma delta_seq_b s : ltac2:(tb__ "0|0|
S5cVs;S66Vs;A1S74Vs;A1A3").
Proof.
  unfold seq_locs_b. destruct (st_seq s =? 255) eqn:E; [apply delta_seq|]. apply delta_seq_inc. apply Z.eqb_neq. exact E.
Qed.

Section FgdDelta.
  Variables (s : astate) (g : sptr) (am : ameta).
  Hypothesis ND : NoDup (keys s).
  Hypothesis Mg : ltac2:(tb__ "0|0|
S0S2bS6A1S38Vs;Vg;A2S2aS6S8Vam;A1A2A3").
  Hypothesis Hfr0 : ltac2:(tb__ "0|0|
S5bS0S2bS10A1S20S1dVam;R1A2A1S2eS10A1A3Fj;").

  Lemma ND_seq : NoDup (keys (seq_post s)). Proof using ND. unfold seq_post. destruct (st_seq s =? 255); exact ND. Qed.
  Lemma Mg_seq : ltac2:(tb__ "0|0|
S0S2bS6A1S38S66Vs;A1Vg;A2S2aS6S8Vam;A1A2A3"). Proof using Mg. rewrite seq_post_MT. exact Mg. Qed.
  Lemma keys_s2 : ltac2:(tb__ "0|0|
S0S2cS5A1S3aS64Vs;Vg;A2A1S3aVs;A1A3").
  Proof using Mg. unfold fgd_s2. rewrite keys_upd_In; [|eapply MT_Some_In_keys; exact Mg_seq]. unfold seq_post. destruct (st_seq s =? 255); reflexivity. Qed.
  Lemma ND_s2 : ltac2:(tb__ "0|0|
S52S5S3aS64Vs;Vg;A2A1A2"). Proof using Mg ND. rewrite keys_s2. exact ND. Qed.

  Lemma delta_s2 : ltac2:(tb__ "0|0|
S5cVs;S64Vs;Vg;A2S2dS36S74Vs;A1S5dVg;A1A3A3").
  Proof using Hfr0 Mg ND.
    apply (delta_trans s (seq_post s)); [apply delta_seq_b|]. unfold fgd_s2.
    apply (delta_nu (seq_post s) g (MUsed am) (MFree None None) ND_seq Mg_seq I).
    intros am0 E j. injection E as <-. apply Hfr0.
  Qed.
  Lemma shape_s2 : ltac2:(tb__ "0|0|
S62Vs;S64Vs;Vg;A2A2").
  Proof using . apply (shape_kept_trans s (seq_post s)); [apply seq_shape|]. unfold fgd_s2. apply nu_shape. exact I. Qed.

  Theorem delta_fgd_empty : ltac2:(tb__ "0|1|
S0S2bS5A1S7Vs;A1S2eS5A1A3S5cVs;S63Vs;Vg;A2S2dS36S2dS36S74Vs;A1S5dVg;A1M0A3S2dS36G0S30S36S39S40A1S31S36A1A3A3A3A3F_;").
  Proof using Hfr0 Mg ND.
    intros Hfh. rewrite (fgd_post_empty s g Hfh).
    apply (delta_trans s (fgd_s2 s g)); [apply delta_s2|].
    apply (delta_trans (fgd_s2 s g) (upd_meta g (MFree (Some g) (Some g)) (fgd_s2 s g))).
    - apply (delta_nu (fgd_s2 s g) g (MFree None None) (MFree (Some g) (Some g)) ND_s2 (fgd_s2_MT_g s g) I). intros am0 E. discriminate E.
    - apply delta_fhead.
  Qed.
  Theorem shape_fgd_empty : ltac2:(tb__ "0|0|
S0S2bS5A1S7Vs;A1S2eS5A1A3S62Vs;S63Vs;Vg;A2A2F_;").
  Proof using .
    intros Hfh. rewrite (fgd_post_empty s g Hfh). apply (shape_kept_trans s (fgd_s2 s g)); [apply shape_s2|].
    eapply shape_kept_trans; [apply (nu_shape _ g (MFree (Some g) (Some g))); exact I | apply fh_shape].
  Qed.

  Section Ring.
    Variables (fm hp nx pr2 nx2 : sptr).
    Hypothesis Hfh : ltac2:(tb__ "0|0|
S0S2bS5A1S7Vs;A1S2aS5Vfm;A2A3").
    Hypothesis Mfm : ltac2:(tb__ "0|0|
S0S2bS6A1S38Vs;Vfm;A2S2aS6S9S2aS5Vhp;A2S2aS5Vnx;A2A2A2A3").
    Hypothesis Mhp : ltac2:(tb__ "0|0|
S0S2bS6A1S38Vs;Vhp;A2S2aS6S9S2aS5Vpr2;A2S2aS5Vnx2;A2A2A2A3").
    Hypothesis Hfg : fm <> g.
    Hypothesis Hhg : hp <> g.
    Theorem delta_fgd_ring : ltac2:(tb__ "0|1|
S5cVs;S63Vs;Vg;A2S2dS36S2dS36S2dS36S2dS36S74Vs;A1S5dVg;A1M0A3G0A3S5dVhp;A1A3S5dVfm;A1A3A3").
    Proof using Hfg Hfh Hfr0 Hhg Mfm Mg Mhp ND.
      rewrite (fgd_post_ring s g fm hp nx pr2 nx2 Hfh Mfm Mhp Hfg Hhg).
      assert (M3 : MT (fgd_t3 s g fm hp) hp = Some (MFree (Some pr2) (Some nx2))).
      { unfold fgd_t3. rewrite (MT_upd_other g _ _ hp Hhg). rewrite (fgd_s2_MT_other s g hp Hhg). exact Mhp. }
      assert (K3 : keys (fgd_t3 s g fm hp) = keys s).
      { unfold fgd_t3. rewrite keys_upd_In; [apply keys_s2|]. rewrite keys_s2. eapply MT_Some_In_keys. exact Mg. }
      assert (K4 : keys (fgd_t4 s g fm hp pr2) = keys s).
      { unfold fgd_t4. rewrite keys_upd_In; [exact K3|]. rewrite K3. eapply MT_Some_In_keys. exact Mhp. }
      assert (M4 : exists x, MT (fgd_t4 s g fm hp pr2) fm = Some (MFree x (if sptr_eqb fm hp then Some g else Some nx))).
      { unfold fgd_t4. destruct (sptr_eqb fm hp) eqn:E.
        - apply sptr_eqb_eq in E. rewrite E. rewrite MT_upd_same. eexists. reflexivity.
        - rewrite (MT_upd_other hp _ _ fm) by (intros EE; rewrite EE, sptr_eqb_refl in E; discriminate).
          unfold fgd_t3. rewrite (MT_upd_other g _ _ fm Hfg). rewrite (fgd_s2_MT_other s g fm Hfg), Mfm. eexists. reflexivity. }
      destruct M4 as [x M4].
      apply (delta_trans s (fgd_t4 s g fm hp pr2)); [apply (delta_trans s (fgd_t3 s g fm hp)); [apply (delta_trans s (fgd_s2 s g)); [apply delta_s2|]|]|].
      - unfold fgd_t3. apply (delta_nu (fgd_s2 s g) g (MFree None None) (MFree (Some hp) (Some fm)) ND_s2 (fgd_s2_MT_g s g) I). intros am0 E. discriminate E.
      - unfold fgd_t4. apply (delta_nu (fgd_t3 s g fm hp) hp (MFree (Some pr2) (Some nx2)) (MFree (Some pr2) (Some g)) ltac:(rewrite K3; exact ND) M3 I). intros am0 E. discriminate E.
      - apply (delta_nu (fgd_t4 s g fm hp pr2) fm _ (MFree (Some g) (fm_next' g fm hp nx)) ltac:(rewrite K4; exact ND) M4 I). intros am0 E. discriminate E.
    Qed.
    Theorem shape_fgd_ring : ltac2:(tb__ "0|0|
S62Vs;S63Vs;Vg;A2A2").
    Proof using Hfg Hfh Hhg Mfm Mhp.
      rewrite (fgd_post_ring s g fm hp nx pr2 nx2 Hfh Mfm Mhp Hfg Hhg).
      apply (shape_kept_trans s (fgd_s2 s g)); [apply shape_s2|].
      eapply shape_kept_trans; [|apply (nu_shape _ fm (MFree _ _)); exact I]. eapply shape_kept_trans; [|apply (nu_shape _ hp (MFree _ _)); exact I]. apply (nu_shape _ g (MFree _ _)); exact I.
    Qed.
    Lemma keys_fgd_ring : ltac2:(tb__ "0|0|
S0S2cS5A1S3aS63Vs;Vg;A2A1S3aVs;A1A3").
    Proof using Hfg Hfh Hfr0 Hhg Mfm Mg Mhp ND. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 delta_fgd_ring))))))). Qed.
  End Ring.
  Lemma keys_fgd_empty : ltac2:(tb__ "0|0|
S0S2bS5A1S7Vs;A1S2eS5A1A3S0S2cS5A1S3aS63Vs;Vg;A2A1S3aVs;A1A3F_;").
  Proof using Hfr0 Mg ND. intros Hfh. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (delta_fgd_empty Hfh)))))))). Qed.
End FgdDelta.

Definition deltaU (s s' : astate) (locs : list loc) : Prop := ltac2:(tb__ "0|1|
S1S0S2cS32S36S5bA2A1S44Vs';A1S44Vs;A1A3S1S0S2cS32S5S5bA2A1S49Vs';A1S49Vs;A1A3S1S0S2fS13Vs';A1S13Vs;A1A3S1S0S2cS5A1M0S11Vs';A1S11Vs;A1A3S1S0S2cS1fA1S15Vs';A1S15Vs;A1A3S1S0S1cS12Vs';A1S12Vs;A1A3S1S0G0S3aVs';A1S3aVs;A1A3S1S0S5bS14Vs';A1S14Vs;A1A3S1S0S5bS19Vs';A1S19Vs;A1A3S1S0S5S1aVs';A1S1aVs;A1A3S37S51S37R1S2dS37S3cVs';A1S69Vs';A1A3A3S3S51S37R2S2dS37S3cVs;A1S69Vs;A1A3A3S51S36S3fR2A1Vlocs;A3A2F_;Fc;A2A2A2A2A2A2A2A2A2A2").
Lemma delta_U s s' l : ltac2:(tb__ "0|0|
S5cVs;Vs';Vl;A3S73Vs;Vs';Vl;A3F_;").
Proof. intros (A1&A2&A3&A4&A5&A6&A7&A8&A9&A9a&A9b&A10). repeat split; assumption. Qed.
Lemma deltaU_trans s s' s'' l1 l2 : ltac2:(tb__ "0|0|
S73Vs;Vs';Vl1;A3S73Vs';Vs'';Vl2;A3S73Vs;Vs'';S2dS36Vl1;Vl2;A3A3F_;F_;").
Proof.
  intros (A1&A2&A3&A4&A5&A6&A7&A8&A8a&A8b&A9) (B1&B2&B3&B4&B5&B6&B7&B8&B8a&B8b&B9).
  repeat split; try congruence.
  intros c Hc. destruct (B9 c Hc) as [H|H]; [|right; apply in_app_iff; right; exact H].
  destruct (A9 c H) as [H'|H']; [left; exact H' | right; apply in_app_iff; left; exact H'].
Qed.

Section SetUsage.
  Variables (s : astate) (sc : Z) (u : Z).
  Let s' : ltac2:(tb__ "0|0|
Sa") := ltac2:(tb__ "0|0|
S28S25Vsc;Vu;SbVs;A1A3Vs;A2").
  Definition usage_cell (t : astate) (c : Z) : mcell := ltac2:(tb__ "0|0|
S3dS39S54S47S58Z8Vc;A2A2A1U8S41S70S5bS59Vc;A1SbVt;A1Z0A4A1A3").
  Lemma su_image_In' c : ltac2:(tb__ "0|0|
S56Z0Vsc;A2S51S37Vc;S3cVs';A1A3S3S51S37Vc;S3cVs;A1A3S0S37Vc;S7cVs';Vsc;A2A3A2F_;F_;").
  Proof using u.
    intros Hsc Hin. unfold image in *. change (st_areas s') with (st_areas s) in Hin.
    rewrite (areas_cells_metas s' s (st_areas s) eq_refl) in Hin. change (used_metas s') with (used_metas s) in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    2:{ left. apply in_app_iff. right. exact Hin. }
    unfold ctx_cells in Hin |- *.
    cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_seq st_brk st_usage st_unmap_seq st_bounces st_active
      s' set_usage] in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    { left. apply in_app_iff. left. apply in_app_iff. left. exact Hin. }
    apply in_app_iff in Hin as [Hin|Hin].
    { left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
    apply in_app_iff in Hin as [Hin|Hin].
    2:{ left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hin. }
    apply in_map_iff in Hin as [j [Hj Hinj]]. unfold zset in Hj. rewrite nth_zupd in Hj.
    destruct (Nat.eqb j (Z.to_nat sc) && Nat.ltb (Z.to_nat sc) (length (st_usage s)))%bool eqn:E.
    - right. apply andb_prop in E as [E1 E2]. apply Nat.eqb_eq in E1. subst j. unfold usage_cell.
      change (st_usage s') with (zset sc u (st_usage s)). unfold zset. rewrite nth_zupd, Nat.eqb_refl, E2. cbn [andb].
      rewrite Z2Nat.id in Hj by lia. symmetry. exact Hj.
    - left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
      apply in_map_iff. exists j. auto.
  Qed.
  Theorem deltaU_usage : ltac2:(tb__ "0|0|
S56Z0Vsc;A2S73Vs;Vs';S30S36S39S54S47S58Z8Vsc;A2A2A1S31S36A1A3A3F_;").
  Proof using u.
    intros Hsc. unfold deltaU. repeat split; try reflexivity.
    intros c Hc. apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; right; exact Hc].
    destruct (su_image_In' c Hsc Hc) as [H|H]; [left; apply in_app_iff; left; exact H|].
    right. subst c. left. reflexivity.
  Qed.
  Lemma su_MT q : ltac2:(tb__ "0|0|
S0S2bS6A1S38Vs';Vq;A2S38Vs;Vq;A2A3"). Proof using sc u. reflexivity. Qed.
  Lemma su_shape : shape_kept s s'. Proof using sc u. intros q aq Hq. exists aq. auto 7. Qed.
End SetUsage.

Section SetUseq.
  Variables (s : astate) (k : Z) (b : Z).
  Let s' : ltac2:(tb__ "0|0|
Sa") := ltac2:(tb__ "0|0|
S27S25Vk;Vb;S16Vs;A1A3Vs;A2").
  Definition useq_cell (t : astate) (j : Z) : mcell := ltac2:(tb__ "0|0|
S3dS39S54S43Vj;A2A1U1S41S70S5bS59Vj;A1S16Vt;A1Z0A4A1A3").
  Lemma sq_image_In c : ltac2:(tb__ "0|0|
S56Z0Vk;A2S51S37Vc;S3cVs';A1A3S3S51S37Vc;S3cVs;A1A3S0S37Vc;S7dVs';Vk;A2A3A2F_;F_;").
  Proof using b.
    intros Hk Hin. unfold image in *. change (st_areas s') with (st_areas s) in Hin.
    rewrite (areas_cells_metas s' s (st_areas s) eq_refl) in Hin. change (used_metas s') with (used_metas s) in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    2:{ left. apply in_app_iff. right. exact Hin. }
    unfold ctx_cells in Hin |- *.
    cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_seq st_brk st_usage st_unmap_seq st_bounces st_active
      s' set_unmap_seq] in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    { left. apply in_app_iff. left. apply in_app_iff. left. exact Hin. }
    apply in_app_iff in Hin as [Hin|Hin].
    { left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
    apply in_app_iff in Hin as [Hin|Hin].
    { left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
    apply in_app_iff in Hin as [Hin|Hin].
    2:{ left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hin. }
    apply in_map_iff in Hin as [j [Hj Hinj]]. unfold zset in Hj. rewrite nth_zupd in Hj.
    destruct (Nat.eqb j (Z.to_nat k) && Nat.ltb (Z.to_nat k) (length (st_unmap_seq s)))%bool eqn:E.
    - right. apply andb_prop in E as [E1 E2]. apply Nat.eqb_eq in E1. subst j. unfold useq_cell.
      change (st_unmap_seq s') with (zset k b (st_unmap_seq s)). unfold zset. rewrite nth_zupd, Nat.eqb_refl, E2. cbn [andb].
      rewrite Z2Nat.id in Hj by lia. symmetry. exact Hj.
    - left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
      apply in_map_iff. exists j. auto.
  Qed.
  Theorem delta_useq : ltac2:(tb__ "0|0|
S56Z0Vk;A2S5cVs;Vs';S30S36S39S54S43Vk;A2A1S31S36A1A3A3F_;").
  Proof using b.
    intros Hk. unfold delta. repeat split; try reflexivity.
    intros c Hc. apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; right; exact Hc].
    destruct (sq_image_In c Hk Hc) as [H|H]; [left; apply in_app_iff; left; exact H|].
    right. subst c. left. reflexivity.
  Qed.
  Lemma sq_shape : shape_kept s s'. Proof using b k. intros q aq Hq. exists aq. auto 7. Qed.
End SetUseq.

Section FqDelta.
  Variables (t : astate) (g : sptr).
  Hypothesis ND : NoDup (keys t).
  Hypothesis Mg : ltac2:(tb__ "0|1|
S0S2bS6A1S38Vt;Vg;A2S2aS6S9S2eS5A1M0G0A2A2A3").
  Theorem delta_fq_empty : ltac2:(tb__ "0|0|
S0S2bS5A1S7Vt;A1S2eS5A1A3S5cVt;S5fVt;Vg;A2S2dS36S5dVg;A1S30S36S39S40A1S31S36A1A3A3A3F_;").
  Proof using Mg ND.
    intros Hfh. unfold fq_post. rewrite Hfh.
    apply (delta_trans t (upd_meta g (MFree (Some g) (Some g)) t)).
    - apply (delta_nu t g (MFree None None) (MFree (Some g) (Some g)) ND Mg I). intros am0 E. discriminate E.
    - apply delta_fhead.
  Qed.
  Theorem shape_fq_empty : ltac2:(tb__ "0|0|
S0S2bS5A1S7Vt;A1S2eS5A1A3S62Vt;S5fVt;Vg;A2A2F_;").
  Proof using .
    intros Hfh. unfold fq_post. rewrite Hfh. eapply shape_kept_trans; [apply (nu_shape _ g (MFree (Some g) (Some g))); exact I | apply fh_shape].
  Qed.
  Lemma MT_fq_empty_g : ltac2:(tb__ "0|1|
S0S2bS5A1S7Vt;A1S2eS5A1A3S0S2bS6A1S38S5fVt;Vg;A2Vg;A2S2aS6S9S2aS5Vg;A2M0G0A2A2A3F_;").
  Proof using . intros Hfh. unfold fq_post. rewrite Hfh. cbn [MT set_free_meta_head st_metas upd_meta set_metas]. apply mlookup_mupdate_same. Qed.
  Lemma MT_fq_empty_other q : ltac2:(tb__ "0|0|
S0S2bS5A1S7Vt;A1S2eS5A1A3S2S0S5Vq;Vg;A3A1S0S2bS6A1S38S5fVt;Vg;A2Vq;A2S38Vt;Vq;A2A3F_;F_;").
  Proof using .
    intros Hfh Hq. unfold fq_post. rewrite Hfh.
    change (MT (set_free_meta_head (Some g) (upd_meta g (MFree (Some g) (Some g)) t)) q) with (MT (upd_meta g (MFree (Some g) (Some g)) t) q). apply MT_upd_other. exact Hq.
  Qed.
  Lemma head_fq_empty : ltac2:(tb__ "0|1|
S0S2bS5A1M0S7Vt;A1S2eS5A1A3S0G0S7S5fVt;Vg;A2A1S2aS5Vg;A2A3F_;").
  Proof using . intros Hfh. unfold fq_post. rewrite Hfh. reflexivity. Qed.

  Section Ring.
    Variables (fm hp nx pr2 nx2 : sptr).
    Hypothesis Hfh : ltac2:(tb__ "0|0|
S0S2bS5A1S7Vt;A1S2aS5Vfm;A2A3").
    Hypothesis Mfm : ltac2:(tb__ "0|0|
S0S2bS6A1S38Vt;Vfm;A2S2aS6S9S2aS5Vhp;A2S2aS5Vnx;A2A2A2A3").
    Hypothesis Mhp : ltac2:(tb__ "0|0|
S0S2bS6A1S38Vt;Vhp;A2S2aS6S9S2aS5Vpr2;A2S2aS5Vnx2;A2A2A2A3").
    Hypothesis Hfg : fm <> g.
    Hypothesis Hhg : hp <> g.
    Definition fq_t3 : astate := ltac2:(tb__ "0|0|
S6aVg;S9S2aS5Vhp;A2S2aS5Vfm;A2A2Vt;A3").
    Definition fq_t4 : astate := ltac2:(tb__ "0|0|
S6aVhp;S9S2aS5Vpr2;A2S2aS5Vg;A2A2S78A3").
    Definition fq_next' : option sptr := ltac2:(tb__ "0|0|
S2fS2bS5A1L_;S23Vfm;Vhp;A2S2aS5Vg;A2S2aS5Vnx;A2X2fx2").
    Lemma fq_post_ring : ltac2:(tb__ "0|0|
S0SaS5fVt;Vg;A2S6aVfm;S9S2aS5Vg;A2S77A2S79A3A3").
    Proof using Hfg Hfh Hhg Mfm Mhp.
      unfold fq_post. rewrite Hfh, Mfm. cbn [links_of fst]. fold fq_t3.
      assert (M3 : MT fq_t3 hp = Some (MFree (Some pr2) (Some nx2))) by (unfold fq_t3; rewrite (MT_upd_other g _ _ hp Hhg); exact Mhp).
      rewrite M3. cbn [with_links links_of fst]. fold fq_t4.
      assert (M4 : MT fq_t4 fm = Some (if sptr_eqb fm hp then MFree (Some pr2) (Some g) else MFree (Some hp) (Some nx))).
      { unfold fq_t4. destruct (sptr_eqb fm hp) eqn:E.
        - apply sptr_eqb_eq in E. rewrite E. apply MT_upd_same.
        - rewrite (MT_upd_other hp _ _ fm) by (intros EE; rewrite EE, sptr_eqb_refl in E; discriminate). unfold fq_t3. rewrite (MT_upd_other g _ _ fm Hfg). exact Mfm. }
      rewrite M4. unfold fq_next'. destruct (sptr_eqb fm hp); reflexivity.
    Qed.
    Theorem delta_fq_ring : ltac2:(tb__ "0|0|
S5cVt;S5fVt;Vg;A2S2dS36S2dS36S5dVg;A1S5dVhp;A1A3S5dVfm;A1A3A3").
    Proof using Hfg Hfh Hhg Mfm Mg Mhp ND.
      rewrite fq_post_ring.
      assert (K3 : keys fq_t3 = keys t) by (unfold fq_t3; apply keys_upd_In; eapply MT_Some_In_keys; exact Mg).
      assert (M3 : MT fq_t3 hp = Some (MFree (Some pr2) (Some nx2))) by (unfold fq_t3; rewrite (MT_upd_other g _ _ hp Hhg); exact Mhp).
      assert (K4 : keys fq_t4 = keys t) by (unfold fq_t4; rewrite keys_upd_In; [exact K3|]; rewrite K3; eapply MT_Some_In_keys; exact Mhp).
      assert (M4 : exists x, MT fq_t4 fm = Some (MFree x (if sptr_eqb fm hp then Some g else Some nx))).
      { unfold fq_t4. destruct (sptr_eqb fm hp) eqn:E.
        - apply sptr_eqb_eq in E. rewrite E. rewrite MT_upd_same. eexists. reflexivity.
        - rewrite (MT_upd_other hp _ _ fm) by (intros EE; rewrite EE, sptr_eqb_refl in E; discriminate).
          unfold fq_t3. rewrite (MT_upd_other g _ _ fm Hfg), Mfm. eexists. reflexivity. }
      destruct M4 as [x M4].
      apply (delta_trans t fq_t4); [apply (delta_trans t fq_t3)|].
      - unfold fq_t3. apply (delta_nu t g (MFree None None) (MFree (Some hp) (Some fm)) ND Mg I). intros am0 E. discriminate E.
      - unfold fq_t4. apply (delta_nu fq_t3 hp (MFree (Some pr2) (Some nx2)) (MFree (Some pr2) (Some g)) ltac:(rewrite K3; exact ND) M3 I). intros am0 E. discriminate E.
      - apply (delta_nu fq_t4 fm _ (MFree (Some g) fq_next') ltac:(rewrite K4; exact ND) M4 I). intros am0 E. discriminate E.
    Qed.
    Theorem shape_fq_ring : ltac2:(tb__ "0|0|
S62Vt;S5fVt;Vg;A2A2").
    Proof using Hfg Hfh Hhg Mfm Mhp.
      rewrite fq_post_ring.
      eapply shape_kept_trans; [|apply (nu_shape _ fm (MFree _ _)); exact I]. eapply shape_kept_trans; [|apply (nu_shape _ hp (MFree _ _)); exact I]. apply (nu_shape _ g (MFree _ _)); exact I.
    Qed.
    Lemma MT_fq_fm : ltac2:(tb__ "0|0|
S0S2bS6A1S38S5fVt;Vg;A2Vfm;A2S2aS6S9S2aS5Vg;A2S77A2A2A3").
    Proof using Hfg Hfh Hhg Mfm Mhp. rewrite fq_post_ring. apply MT_upd_same. Qed.
    Lemma MT_fq_hp : ltac2:(tb__ "0|0|
S2S0S5Vhp;Vfm;A3A1S0S2bS6A1S38S5fVt;Vg;A2Vhp;A2S2aS6S9S2aS5Vpr2;A2S2aS5Vg;A2A2A2A3F_;").
    Proof using Hfg Hfh Hhg Mfm Mhp. intros Hne. rewrite fq_post_ring. rewrite (MT_upd_other fm _ _ hp Hne). unfold fq_t4. apply MT_upd_same. Qed.
    Lemma MT_fq_g : ltac2:(tb__ "0|0|
S0S2bS6A1S38S5fVt;Vg;A2Vg;A2S2aS6S9S2aS5Vhp;A2S2aS5Vfm;A2A2A2A3").
    Proof using Hfg Hfh Hhg Mfm Mhp.
      rewrite fq_post_ring. rewrite (MT_upd_other fm _ _ g) by (intros E; exact (Hfg (eq_sym E))).
      unfold fq_t4. rewrite (MT_upd_other hp _ _ g) by (intros E; exact (Hhg (eq_sym E))). unfold fq_t3. apply MT_upd_same.
    Qed.
    Lemma MT_fq_other q : ltac2:(tb__ "0|0|
S2S0S5Vq;Vg;A3A1S2S0S5Vq;Vfm;A3A1S2S0S5Vq;Vhp;A3A1S0S2bS6A1S38S5fVt;Vg;A2Vq;A2S38Vt;Vq;A2A3F_;F_;F_;").
    Proof using Hfg Hfh Hhg Mfm Mhp.
      intros H1 H2 H3. rewrite fq_post_ring. rewrite (MT_upd_other fm _ _ q H2). unfold fq_t4. rewrite (MT_upd_other hp _ _ q H3).
      unfold fq_t3. apply (MT_upd_other g _ _ q H1).
    Qed.
    Lemma head_fq_ring : ltac2:(tb__ "0|0|
S0S2bS5A1S7S5fVt;Vg;A2A1S2aS5Vfm;A2A3").
    Proof using Hfg Hfh Hhg Mfm Mhp. rewrite fq_post_ring. cbn [upd_meta set_metas st_free_meta_head]. unfold fq_t4, fq_t3. cbn [upd_meta set_metas st_free_meta_head]. exact Hfh. Qed.
  End Ring.
  Lemma fq_fields : ltac2:(tb__ "0|2|
S1S0S2cS5bA1M0SbS5fVt;Vg;A2M1A1SbVt;A1A3S1S0S5bSdG1A1SdVt;A1A3S1S0G0S16G1A1S16Vt;A1A3S1S0S2cS2bS5A1A1S18G1A1S18Vt;A1A3S0G0S1bG1A1S1bVt;A1A3A2A2A2A2").
  Proof using .
    unfold fq_post. destruct (st_free_meta_head t) as [fm|]; [|repeat split; reflexivity].
    destruct (MT t fm) as [xf|]; [|repeat split; reflexivity]. destruct (fst (links_of xf)) as [hp|]; repeat split; reflexivity.
  Qed.
End FqDelta.

Section FgmDelta.
  Variables (s : astate) (g : sptr) (am : ameta).
  Hypothesis ND : NoDup (keys s).
  Hypothesis Mg : ltac2:(tb__ "0|0|
S0S2bS6A1S38Vs;Vg;A2S2aS6S8Vam;A1A2A3").
  Hypothesis Hfr0 : ltac2:(tb__ "0|0|
S5bS0S2bS10A1S20S1dVam;R1A2A1S2eS10A1A3Fj;").
  Hypothesis Hsc : 0 <= am_sc am < 48.
  Hypothesis LenA : length (st_active s) = 48%nat.
  Let sc : Z := am_sc am.

  Lemma delta_dq1 : ltac2:(tb__ "0|0|
S0S2bS5A1SfVam;A1S2aS5Vg;A2A3S5cVs;S60Vs;Vg;Vam;A3S2dS36S30S36S39S54S4aS58Z8Vsc;A2A2A1S31S36A1A3S5dVg;A1A3A3F_;").
  Proof using Hsc LenA Mg ND.
    intros En. unfold dq_post. rewrite En, sptr_eqb_refl.
    apply (delta_trans s (set_hd sc None s)); [apply delta_sh; unfold sc; lia|].
    apply (delta_su_keep (set_hd sc None s) g am); [exact ND | rewrite MT_set_hd; exact Mg | apply same_shape_links | reflexivity].
  Qed.

  Section Gen.
    Variables (p n : sptr) (ap an : ameta).
    Hypothesis Ep : ltac2:(tb__ "0|0|
S0S2bS5A1S17Vam;A1S2aS5Vp;A2A3").
    Hypothesis En : ltac2:(tb__ "0|0|
S0S2bS5A1SfVam;A1S2aS5Vn;A2A3").
    Hypothesis Hng : n <> g.
    Hypothesis Hpg : p <> g.
    Hypothesis Mp : ltac2:(tb__ "0|0|
S0S2bS6A1S38Vs;Vp;A2S2aS6S8Vap;A1A2A3").
    Hypothesis Mn : ltac2:(tb__ "0|0|
S0S2bS6A1S38Vs;Vn;A2S2aS6S8Van;A1A2A3").
    Definition dq_s1a : astate := ltac2:(tb__ "0|0|
S6aVp;S8SeS17Vap;A1S2aS5Vn;A2Vap;A3A1Vs;A3").
    Definition an1 : ameta := ltac2:(tb__ "0|0|
S2fScL_;S23Vn;Vp;A2SeS17Vap;A1S2aS5Vn;A2Vap;A3Van;X2fx2").
    Lemma MT_s1a_n : ltac2:(tb__ "0|0|
S0S2bS6A1S38S6eVn;A2S2aS6S8S6bA1A2A3").
    Proof using Mn.
      unfold dq_s1a, an1. destruct (sptr_eqb n p) eqn:E.
      - apply sptr_eqb_eq in E. rewrite E. apply MT_upd_same.
      - rewrite (MT_upd_other p _ _ n) by (intros EE; rewrite EE, sptr_eqb_refl in E; discriminate). exact Mn.
    Qed.
    Definition dq_s1b : astate := ltac2:(tb__ "0|0|
S6aVn;S8SeS2aS5Vp;A2SfS6bA1S6bA3A1S6eA3").
    Definition dq_s1c : astate := ltac2:(tb__ "0|0|
S2fSaL_;S1eS42Vs;Vsc;A2S2aS5Vg;A2A2S5eVsc;S2aS5Vn;A2S6cA3S6cX2fx2").
    Lemma dq_post_gen : ltac2:(tb__ "0|1|
S0SaS60Vs;Vg;Vam;A3S6aVg;S8SeS2eS5A1M0G0Vam;A3A1S6dA3A3").
    Proof using En Ep Hng Mn Mp.
      unfold dq_post. rewrite En. replace (sptr_eqb n g) with false by (symmetry; apply sptr_eqb_neq; exact Hng). rewrite Ep, Mp.
      cbn [with_links links_of fst]. fold dq_s1a. rewrite MT_s1a_n. cbn [with_links links_of snd]. fold dq_s1b. fold sc. fold dq_s1c. reflexivity.
    Qed.
    Lemma keys_s1b : ltac2:(tb__ "0|0|
S0S2cS5A1S3aS6cA1S3aVs;A1A3").
    Proof using Mn Mp.
      unfold dq_s1b. rewrite keys_upd_In; unfold dq_s1a; rewrite keys_upd_In; try reflexivity; try (eapply MT_Some_In_keys; exact Mp).
      eapply MT_Some_In_keys. exact Mn.
    Qed.
    Lemma keys_s1c : ltac2:(tb__ "0|0|
S0S2cS5A1S3aS6dA1S3aVs;A1A3").
    Proof using Mn Mp. unfold dq_s1c. destruct (osptr_eqb (active_hd s sc) (Some g)); [change (keys (set_hd sc (Some n) dq_s1b)) with (keys dq_s1b)|]; apply keys_s1b. Qed.
    Lemma MT_s1c q : ltac2:(tb__ "0|0|
S0S2bS6A1S38S6dVq;A2S38S6cVq;A2A3").
    Proof using . unfold dq_s1c. destruct (osptr_eqb (active_hd s sc) (Some g)); [apply MT_set_hd | reflexivity]. Qed.
    Lemma MT_s1b_other q : ltac2:(tb__ "0|0|
S2S0S5Vq;Vp;A3A1S2S0S5Vq;Vn;A3A1S0S2bS6A1S38S6cVq;A2S38Vs;Vq;A2A3F_;F_;").
    Proof using . intros H1 H2. unfold dq_s1b. rewrite (MT_upd_other n _ _ q H2). unfold dq_s1a. apply (MT_upd_other p _ _ q H1). Qed.
    Definition dq_locs : list loc := ltac2:(tb__ "0|1|
S2dS36S2dS36S2dS36S5dVp;A1S5dVn;A1A3S2fS2cS36A1L_;S1eS42Vs;Vsc;A2S2aS5Vg;A2A2S30S36S39S54S4aS58Z8Vsc;A2A2A1S31S36A1M0A3G0X2fx2A3S5dVg;A1A3").
    Theorem delta_dq_gen : ltac2:(tb__ "0|0|
S5cVs;S60Vs;Vg;Vam;A3S6fA3").
    Proof using En Ep Hng Hpg Hsc LenA Mg Mn Mp ND.
      rewrite dq_post_gen. unfold dq_locs.
      apply (delta_trans s dq_s1c); [apply (delta_trans s dq_s1b); [apply (delta_trans s dq_s1a)|]|].
      - unfold dq_s1a. apply (delta_su_keep s p ap); [exact ND | exact Mp | apply same_shape_links | reflexivity].
      - unfold dq_s1b. apply (delta_su_keep dq_s1a n an1); [unfold dq_s1a; rewrite keys_upd_In; [exact ND | eapply MT_Some_In_keys; exact Mp] | apply MT_s1a_n | apply same_shape_links | reflexivity].
      - unfold dq_s1c. destruct (osptr_eqb (active_hd s sc) (Some g)); [apply delta_sh; unfold sc; lia | apply delta_refl].
      - apply (delta_su_keep dq_s1c g am); [rewrite keys_s1c; exact ND | rewrite MT_s1c, MT_s1b_other; [exact Mg | exact (fun E => Hpg (eq_sym E)) | exact (fun E => Hng (eq_sym E))] | apply same_shape_links | reflexivity].
    Qed.
    Lemma MT_dq_n : ltac2:(tb__ "0|0|
S0S2bS6A1S38S60Vs;Vg;Vam;A3Vn;A2S2aS6S8SeS2aS5Vp;A2SfS6bA1S6bA3A1A2A3").
    Proof using En Ep Hng Mn Mp. rewrite dq_post_gen. rewrite (MT_upd_other g _ _ n Hng), MT_s1c. unfold dq_s1b. apply MT_upd_same. Qed.
    Lemma MT_dq_p : ltac2:(tb__ "0|0|
S2S0S5Vp;Vn;A3A1S0S2bS6A1S38S60Vs;Vg;Vam;A3Vp;A2S2aS6S8SeS17Vap;A1S2aS5Vn;A2Vap;A3A1A2A3F_;").
    Proof using En Ep Hng Hpg Mn Mp. intros Hpn. rewrite dq_post_gen. rewrite (MT_upd_other g _ _ p Hpg), MT_s1c. unfold dq_s1b. rewrite (MT_upd_other n _ _ p Hpn). unfold dq_s1a. apply MT_upd_same. Qed.
    Lemma MT_dq_g' : ltac2:(tb__ "0|1|
S0S2bS6A1S38S60Vs;Vg;Vam;A3Vg;A2S2aS6S8SeS2eS5A1M0G0Vam;A3A1A2A3").
    Proof using En Ep Hng Mn Mp. rewrite dq_post_gen. apply MT_upd_same. Qed.
    Lemma hd_dq_gen c : ltac2:(tb__ "0|1|
S56Z0Vc;A2S0S2bS5A1M0S42S60Vs;Vg;Vam;A3Vc;A2S2fG0L_;S35S1eS42Vs;Vsc;A2S2aS5Vg;A2A2S5aVc;Vsc;A2A2S2aS5Vn;A2S42Vs;Vc;A2X2fx2A3F_;").
    Proof using En Ep Hng Hsc LenA Mn Mp.
      intros Hc. rewrite dq_post_gen. rewrite active_hd_upd_meta. unfold dq_s1c.
      destruct (osptr_eqb (active_hd s sc) (Some g)); cbn [andb].
      - destruct (c =? sc) eqn:E.
        + apply Z.eqb_eq in E. subst c. apply active_hd_set_hd_same; [unfold sc; lia | unfold dq_s1b, dq_s1a; exact LenA].
        + apply Z.eqb_neq in E. rewrite active_hd_set_hd_other by (unfold sc in *; lia). unfold dq_s1b, dq_s1a. rewrite !active_hd_upd_meta. reflexivity.
      - unfold dq_s1b, dq_s1a. rewrite !active_hd_upd_meta. reflexivity.
    Qed.

    Lemma act_post_gen : ltac2:(tb__ "0|1|
S0S2bS5A1S42Vs;Vsc;A2S2aS5Vg;A2A3S0SaS67Vs;Vg;Vam;S60Vs;Vg;Vam;A3M0A4S6aVn;S8S7eSeS2aS5Vp;A2SfS6bA1S6bA3A1A1G0A3A3F_;").
    Proof using En Ep Hng Mn Mp.
      intros Hhd. unfold act_post. rewrite En. replace (sptr_eqb n g) with false by (symmetry; apply sptr_eqb_neq; exact Hng).
      fold sc. rewrite Hhd. cbn [osptr_eqb negb andb]. rewrite sptr_eqb_refl. rewrite MT_dq_n. reflexivity.
    Qed.
    Lemma act_post_skip : ltac2:(tb__ "0|1|
S2S0S2bS5A1S42Vs;Vsc;A2S2aS5Vg;A2A3A1S0SaS67Vs;Vg;Vam;S60Vs;Vg;Vam;A3M0A4G0A3F_;").
    Proof using En.
      intros Hhd. unfold act_post. rewrite En. fold sc. destruct (active_hd s sc) as [h|]; cbn [osptr_eqb negb andb].
      - replace (sptr_eqb h g) with false by (symmetry; apply sptr_eqb_neq; intros E; apply Hhd; rewrite E; reflexivity). rewrite Bool.andb_false_r. reflexivity.
      - rewrite Bool.andb_false_r. reflexivity.
    Qed.
    Theorem delta_act_gen : ltac2:(tb__ "0|1|
S0S2bS5A1S42Vs;Vsc;A2S2aS5Vg;A2A3S5cS60Vs;Vg;Vam;A3M0S67Vs;Vg;Vam;G0A4S5dVn;A1A3F_;").
    Proof using En Ep Hng Hpg Hsc LenA Mg Mn Mp ND.
      intros Hhd. rewrite (act_post_gen Hhd).
      apply (delta_su_keep (dq_post s g am) n (am_set_links (Some p) (am_next an1) an1)).
      - rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 delta_dq_gen))))))). exact ND.
      - apply MT_dq_n.
      - unfold am_activate. eapply same_shape_trans; [apply same_shape_freed | apply same_shape_avail].
      - reflexivity.
    Qed.
  End Gen.

  Lemma fgm_s1_D0 : ltac2:(tb__ "0|0|
S0S2bS5A1SfVam;A1S2eS5A1A3S0SaS61Vs;Vg;Vam;A3Vs;A3F_;").
  Proof using . intros En. unfold fgm_s1, act_post, dq_post. rewrite En. reflexivity. Qed.
  Lemma fgm_s1_D1 : ltac2:(tb__ "0|0|
S0S2bS5A1SfVam;A1S2aS5Vg;A2A3S0SaS61Vs;Vg;Vam;A3S60Vs;Vg;Vam;A3A3F_;").
  Proof using . intros En. unfold fgm_s1, act_post. rewrite En, sptr_eqb_refl. reflexivity. Qed.
  Lemma st_seq_s2 : ltac2:(tb__ "0|0|
S0S5bSdS68Vs;Vg;Vam;A3A1SdS61Vs;Vg;Vam;A3A1A3"). Proof using . reflexivity. Qed.

  Section Tail.
    Variable l1 : list loc.
    Hypothesis D1 : ltac2:(tb__ "0|0|
S5cVs;S61Vs;Vg;Vam;A3Vl1;A3").
    Hypothesis M1 : ltac2:(tb__ "0|0|
S4ScScS1S0S2bS6A1S38S61Vs;Vg;Vam;A3Vg;A2S2aS6S8R1A1A2A3S0S2cS29A1S21R1A1S21Vam;A1A3A2La1;A2").
    Definition rec_locs : list loc := ltac2:(tb__ "0|1|
S2bS5bA1S2cS36A1Lx;S26Vsc;A1S5bS30S36S39S54S43R1A2A1S31S36A1M0A3Lk;G0X2bx2").
    Theorem deltaU_fgm5 : ltac2:(tb__ "0|0|
S73Vs;S65Vs;Vg;Vam;A3S2dS36S2dS36S2dS36S2dS36Vl1;S30S36S39S54S47S58Z8Vsc;A2A2A1S31S36A1A3A3S74S61Vs;Vg;Vam;A3A1A3S7bA3S5dVg;A1A3A3").
    Proof using D1 Hfr0 Hsc LenA M1 ND.
      destruct M1 as (a1 & Ma1 & Sl1).
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 D1))))))) as K1.
      apply (deltaU_trans s (fgm_s4 s g am)); [apply (deltaU_trans s (fgm_s3 s g am)); [apply (deltaU_trans s (fgm_s2 s g am)); [apply (deltaU_trans s (fgm_s1 s g am)); [apply delta_U; exact D1|]|]|]|].
      - unfold fgm_s2. apply deltaU_usage. unfold sc; lia.
      - apply delta_U. unfold fgm_s3. replace (seq_locs_b (fgm_s1 s g am)) with (seq_locs_b (fgm_s2 s g am)) by reflexivity. apply delta_seq_b.
      - apply delta_U. unfold fgm_s4, rec_locs. fold sc. destruct (bounce_idx sc) as [k|] eqn:Ek; [|apply delta_refl].
        apply delta_useq. unfold bounce_idx in Ek. destruct ((7 <=? sc) && (sc <? 39))%bool eqn:E; [|discriminate]. injection Ek as <-. apply andb_prop in E as [E _]. apply Z.leb_le in E. lia.
      - apply delta_U. unfold fgm_s5.
        assert (M4 : MT (fgm_s4 s g am) g = Some (MUsed a1)).
        { unfold fgm_s4, fgm_s3, fgm_s2. destruct (bounce_idx (am_sc am)); rewrite ?MT_set_unmap_seq, MT_seq_post, MT_set_usage; exact Ma1. }
        assert (K4 : keys (fgm_s4 s g am) = keys s).
        { unfold fgm_s4, fgm_s3, fgm_s2. destruct (bounce_idx (am_sc am)); cbn [keys st_metas set_unmap_seq set_usage]; unfold seq_post; destruct (st_seq _ =? 255); cbn [keys st_metas set_seq set_unmap_seq set_usage]; exact K1. }
        apply (delta_nu (fgm_s4 s g am) g (MUsed a1) (MFree None None) ltac:(rewrite K4; exact ND) M4 I).
        intros am0 E j. injection E as <-. unfold nth_slot. rewrite Sl1. apply Hfr0.
    Qed.
    Theorem shape_fgm5 : ltac2:(tb__ "0|0|
S62Vs;S61Vs;Vg;Vam;A3A2S62Vs;S65Vs;Vg;Vam;A3A2F_;").
    Proof using .
      intros S1. unfold fgm_s5, fgm_s4, fgm_s3, fgm_s2.
      eapply shape_kept_trans; [|apply (nu_shape _ g (MFree None None)); exact I].
      destruct (bounce_idx (am_sc am)); (eapply shape_kept_trans; [|try apply sq_shape; try apply shape_kept_refl]);
        (eapply shape_kept_trans; [|apply seq_shape]); (eapply shape_kept_trans; [exact S1 | apply su_shape]).
    Qed.
    Lemma keys_fgm5 : ltac2:(tb__ "0|0|
S0S2cS5A1S3aS65Vs;Vg;Vam;A3A1S3aVs;A1A3").
    Proof using D1 Hfr0 Hsc LenA M1 ND. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 deltaU_fgm5))))))). Qed.
    Lemma MT_fgm5_g : ltac2:(tb__ "0|1|
S0S2bS6A1S38S65Vs;Vg;Vam;A3Vg;A2S2aS6S9S2eS5A1M0G0A2A2A3").
    Proof using . unfold fgm_s5. apply MT_upd_same. Qed.
  End Tail.
End FgmDelta.
