(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.Lists.List"; "In"; "flat_map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "image"; "used_metas"; "meta_slot_cells"; "user_blocks"; "MT"; "area_cells"; "areas_cells"; "ctx_cells"; "group_cells"; "keys"; "zseq"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "ameta"; "MUsed"; "frame"; "fkind"; "nth_slot"; "ss_fr"; "st_areas"; "st_brk"; "st_init_done"; "st_meta_alloc_shift"; "st_regions"; "st_usage"; "UNIT"; "am_last"; "astate"; "brkst"; "fr_kind"; "fr_n"; "fr_off"; "padd"; "region"; "slot_start"; "sptr_eqb"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "Some"; "prod"; "option"; "pair"; "app"; "bool"; "None"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "group_footer_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupImage.UsedIns"; "blocks_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfRepr MallocFooter ImageUpd ImageDelta FreeNtImage.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section UsedIns.
  Variables (s : astate) (m : sptr) (xold : mslot) (am1 : ameta).
  Hypothesis ND : NoDup (keys s).
  Hypothesis Hm : ltac2:(tb__ "0|0|
SeS30S14A1S7Vs;Vm;A2S2eS14Vxold;A2A3").
  Hypothesis Hold : not_used xold.
  Let s' : ltac2:(tb__ "0|0|
S23") := ltac2:(tb__ "0|0|
S3aVm;S16Vam1;A1Vs;A3").

  Lemma ui_used_metas_In q a : ltac2:(tb__ "0|3|
S0S2fS13S15A2M0S31S13S15Vq;Va;A4M1S4Vs';A1A3S10SfSeS13Vq;Vm;A3M2SeS15Va;Vam1;A3A2SfS12G2A1S0G0G1S4Vs;A1A3A2A2F_;").
  Proof using Hm ND.
    unfold s', upd_meta, used_metas. cbn [st_metas set_metas]. unfold MT in Hm. unfold keys in ND.
    revert ND Hm. generalize (st_metas s) as l. clear s'.
    induction l as [|[q' x] t IH]; intros ND Hl Hin; [discriminate|].
    cbn [mupdate] in Hin. cbn [mlookup] in Hl. inversion ND as [|q0 t0 Hq Ht]; subst.
    destruct (sptr_eqb m q') eqn:E.
    - apply sptr_eqb_eq in E. subst q'. cbn [flat_map] in Hin. apply in_app_iff in Hin as [Hin|Hin].
      + left. destruct Hin as [Hin|[]]. injection Hin as -> ->. auto.
      + right. split.
        * intros ->. apply Hq. apply in_flat_map in Hin as [[p mm] [Hp Hmm]]. apply in_map_iff. exists (p, mm). split; [|exact Hp].
          destruct mm; cbn in Hmm; try (destruct Hmm as [Hmm|[]]; injection Hmm as -> _; reflexivity); destruct Hmm.
        * cbn [flat_map]. apply in_app_iff. right. exact Hin.
    - cbn [flat_map] in Hin |- *. apply in_app_iff in Hin as [Hin|Hin].
      + right. split; [|apply in_app_iff; left; exact Hin]. intros ->.
        destruct x; cbn in Hin; try (exact Hin). destruct Hin as [Hin|[]]. injection Hin as E1 E2. rewrite E1, sptr_eqb_refl in E. discriminate.
      + destruct (IH Ht Hl Hin) as [A|[A B]]; [left; exact A | right]. split; [exact A | apply in_app_iff; right; exact B].
  Qed.

  Lemma ui_used_metas_new : ltac2:(tb__ "0|0|
S0S2fS13S15A2S31S13S15Vm;Vam1;A4S4Vs';A1A3").
  Proof using Hm.
    unfold s', upd_meta, used_metas. cbn [st_metas set_metas]. unfold MT in Hm.
    revert Hm. generalize (st_metas s) as l. clear s' ND.
    induction l as [|[q' x] t IH]; intros Hl; [discriminate|].
    cbn [mupdate]. cbn [mlookup] in Hl. destruct (sptr_eqb m q') eqn:E.
    - cbn [flat_map]. apply in_app_iff. left. left. apply sptr_eqb_eq in E. subst. reflexivity.
    - cbn [flat_map]. apply in_app_iff. right. apply IH. exact Hl.
  Qed.

  Lemma ui_used_metas_back q a : ltac2:(tb__ "0|2|
S0S2fS13S15A2M0S31S13S15Vq;Va;A4M1S4Vs;A1A3S0G0G1S4Vs';A1A3F_;").
  Proof using Hm Hold ND am1.
    intros Hin.
    assert (Hq : q <> m).
    { intros ->. pose proof (proj1 (used_metas_iff s m a ND) Hin) as M. rewrite Hm in M. injection M as ->. exact Hold. }
    unfold s', upd_meta, used_metas. cbn [st_metas set_metas]. revert Hin. unfold used_metas. generalize (st_metas s) as l. clear s' Hm ND.
    induction l as [|[q' x] t IH]; intros Hin; [destruct Hin|].
    cbn [mupdate]. cbn [flat_map] in Hin. apply in_app_iff in Hin as [Hin|Hin].
    - destruct x; cbn in Hin; try (exact (False_ind _ Hin)). destruct Hin as [Hin|[]]. injection Hin as -> ->.
      replace (sptr_eqb m q) with false by (symmetry; apply sptr_eqb_neq; intros E; exact (Hq (eq_sym E))). cbn. left. reflexivity.
    - destruct (sptr_eqb m q'); cbn [flat_map]; apply in_app_iff; right; [exact Hin | apply IH; assumption].
  Qed.

  Lemma ui_fields : ltac2:(tb__ "0|1|
SfSeS2dS13A1M0S1bVs';A1S1bVs;A1A3SfSeS2dS29A1S1fVs';A1S1fVs;A1A3SfSeS24S1cVs';A1S1cVs;A1A3SfSeS33S1dVs';A1S1dVs;A1A3SfSeS2dS2cA1S20Vs';A1S20Vs;A1A3SfSeS2cS1eVs';A1S1eVs;A1A3SfSeS2dS2A1SaVs';A1SaVs;A1A3SeG0ScVs';A1ScVs;A1A3A2A2A2A2A2A2A2").
  Proof using Hm am1. repeat split; try reflexivity. unfold s'. apply keys_upd_In. eapply MT_Some_In_keys. exact Hm. Qed.

  Lemma ui_MT q : ltac2:(tb__ "0|1|
SeS30S14A1M0S7Vs';Vq;A2S33G0L_;S2bVq;Vm;A2S2eS14S16Vam1;A1A2S7Vs;Vq;A2X33x2A3").
  Proof using . unfold s'. destruct (sptr_eqb q m) eqn:E; [apply sptr_eqb_eq in E; subst; apply MT_upd_same | apply MT_upd_other; apply sptr_eqb_neq; exact E]. Qed.

  Lemma ui_area_cells_In a next c : ltac2:(tb__ "0|0|
S0S2Vc;S8Vs';Va;Vnext;A3A3S10S0S2Vc;S8Vs;Va;Vnext;A3A3S0S2Vc;S5Vm;S2eS14S16Vam1;A1A2A2A3A2F_;").
  Proof using .
    unfold area_cells. intros Hin. apply in_app_iff in Hin as [Hin|Hin]; [left; apply in_app_iff; left; exact Hin|].
    apply in_flat_map in Hin as [k [Hk Hc]].
    set (q := padd a (AREA_HDR + META_SIZE * Z.of_nat k)) in Hc.
    change (mlookup (st_metas s') q) with (MT s' q) in Hc. rewrite ui_MT in Hc.
    destruct (sptr_eqb q m) eqn:E.
    - apply sptr_eqb_eq in E. rewrite E in Hc. right. exact Hc.
    - left. apply in_app_iff. right. apply in_flat_map. exists k. split; [exact Hk|]. exact Hc.
  Qed.

  Lemma ui_areas_cells_In l c : ltac2:(tb__ "0|0|
S0S2Vc;S9Vs';Vl;A2A3S10S0S2Vc;S9Vs;Vl;A2A3S0S2Vc;S5Vm;S2eS14S16Vam1;A1A2A2A3A2F_;").
  Proof using .
    induction l as [|a t IH]; cbn [areas_cells]; intros Hin; [left; exact Hin|].
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct (ui_area_cells_In a (hd_error t) c Hin) as [H|H]; [left; apply in_app_iff; left; exact H | right; exact H].
    - destruct (IH Hin) as [H|H]; [left; apply in_app_iff; right; exact H | right; exact H].
  Qed.

  Theorem ui_image_In c : ltac2:(tb__ "0|0|
S0S2Vc;S3Vs';A1A3S10S0S2Vc;S3Vs;A1A3S10S0S2Vc;S5Vm;S2eS14S16Vam1;A1A2A2A3S0S2Vc;SbVm;Vam1;A2A3A2A2F_;").
  Proof using Hm ND.
    intros Hin. unfold image in Hin. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ui_fields))))))) in Hin.
    change (st_areas s') with (st_areas s) in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [left; unfold image; apply in_app_iff; left; exact Hin|].
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct (ui_areas_cells_In _ c Hin) as [H|H]; [left | right; left; exact H].
      unfold image. apply in_app_iff. right. apply in_app_iff. left. exact H.
    - apply in_flat_map in Hin as [[q a] [Hq Hc]]. cbn [fst snd] in Hc.
      destruct (ui_used_metas_In q a Hq) as [[-> ->]|[Hne Hold']]; [right; right; exact Hc|].
      left. apply (In_image_group s q a c Hold' Hc).
  Qed.

  Theorem ui_image_back c : ltac2:(tb__ "0|0|
S0S2Vc;S3Vs;A1A3S12S0S2Vc;S5Vm;S2eS14Vxold;A2A2A3A1S0S2Vc;S3Vs';A1A3F_;F_;").
  Proof using Hm Hold ND am1.
    intros Hin Hnot. unfold image in Hin |- *. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ui_fields))))))).
    change (st_areas s') with (st_areas s).
    apply in_app_iff in Hin as [Hin|Hin]; [apply in_app_iff; left; exact Hin|].
    apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; right; apply in_app_iff; [left|right].
    - revert Hin. generalize (st_areas s) as l. induction l as [|a t IH]; cbn [areas_cells]; intros Hin; [exact Hin|].
      apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left|right; apply IH; exact Hin].
      unfold area_cells in Hin |- *. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin|right].
      apply in_flat_map in Hin as [k [Hk Hc]]. apply in_flat_map. exists k. split; [exact Hk|].
      set (q := padd a (AREA_HDR + META_SIZE * Z.of_nat k)) in Hc |- *.
      change (mlookup (st_metas s') q) with (MT s' q). change (mlookup (st_metas s) q) with (MT s q) in Hc. rewrite ui_MT.
      destruct (sptr_eqb q m) eqn:E; [|exact Hc]. apply sptr_eqb_eq in E. rewrite E, Hm in Hc. exfalso. exact (Hnot Hc).
    - apply in_flat_map in Hin as [[q a] [Hq Hc]]. apply in_flat_map. exists (q, a). split; [apply ui_used_metas_back; exact Hq | exact Hc].
  Qed.

  Theorem ui_group_cells_In c : ltac2:(tb__ "0|0|
S0S2Vc;SbVm;Vam1;A2A3S0S2Vc;S3Vs';A1A3F_;").
  Proof using Hm.
    intros Hc. unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (m, am1). split; [apply ui_used_metas_new | exact Hc].
  Qed.

  Theorem ui_footer_In c : ltac2:(tb__ "0|0|
S0S2Vc;S37Vs';A1A3S10S0S2Vc;S37Vs;A1A3S0S2Vc;S38Vam1;A1A3A2F_;").
  Proof using Hm ND.
    intros Hin. unfold footer_cells in *. apply in_flat_map in Hin as [[q a] [Hq Hc]]. cbn [snd] in Hc.
    destruct (ui_used_metas_In q a Hq) as [[-> ->]|[Hne Hold']]; [right; exact Hc|].
    left. apply in_flat_map. exists (q, a). auto.
  Qed.

  Hypothesis Hframeless : ltac2:(tb__ "0|0|
S2cSeS30S17A1S1aS19Vam1;R1A2A1S34S17A1A3Fj;").

  Lemma ui_user_blocks : ltac2:(tb__ "0|0|
SeS2dS2fS13S2cA2A1S6Vs';A1S6Vs;A1A3").
  Proof using Hframeless Hm Hold ND.
    unfold user_blocks, s', upd_meta, used_metas. cbn [st_metas set_metas]. unfold MT in Hm. unfold keys in ND.
    revert ND Hm. generalize (st_metas s) as l. clear s'.
    induction l as [|[q' x] t IH]; intros ND Hl; [discriminate|].
    cbn [mupdate]. cbn [mlookup] in Hl. inversion ND as [|q0 t0 Hq Ht]; subst.
    destruct (sptr_eqb m q') eqn:E.
    - apply sptr_eqb_eq in E. subst q'. injection Hl as ->. cbn [flat_map].
      assert (L0 : flat_map (fun i0 => match ss_fr (nth_slot am1 i0) with
                                     | Some fr => match fr_kind fr with FUser => [(padd (slot_start am1 i0) (UNIT * fr_off fr), fr_n fr)] | FGroup => [] end
                                     | None => [] end) (zseq 0 (am_last am1 + 1)) = []).
      { apply flat_map_nil'. intros j _. rewrite (Hframeless j). reflexivity. }
      destruct xold as [| |am0]; try (exfalso; exact Hold); cbn [flat_map app snd]; rewrite L0; reflexivity.
    - cbn [flat_map]. rewrite !flat_map_app, (IH Ht Hl). reflexivity.
  Qed.

  Definition blocks_of (am : ameta) : list (sptr * Z) := ltac2:(tb__ "0|3|
S1S2cS2fS13S2cA2M0S2cS30S17A1S2dG0A1M1Lx;S1aS19Vam;R1A2A1S17S18G1Lx;S25R1A1S35G0S31S13S2cS28S2aVam;R2A2S3cS21S27R1A1A2A2S26R1A1A4S36G0A1M2A3G2X18x2Lfr;G2X30x2Li;SdZ0S3bS22Vam;A1Z1A2A2A4").

  Lemma ui_user_blocks_gen : ltac2:(tb__ "0|2|
S11S2dS2fS13S2cA2M0A1M1G1S11G1G1SfSeG1S6Vs;A1S32G0R2R1A3A3SeG1S6Vs';A1S32G0R2S32G0S39Vam1;A1R1A3A3A3A2Ll2;A2Ll1;A2").
  Proof using Hm Hold ND.
    unfold user_blocks, s', upd_meta, used_metas. cbn [st_metas set_metas]. unfold MT in Hm. unfold keys in ND.
    revert ND Hm. generalize (st_metas s) as l. clear s' Hframeless.
    induction l as [|[q' x] t IH]; intros ND Hl; [discriminate|].
    cbn [mupdate]. cbn [mlookup] in Hl. inversion ND as [|q0 t0 Hq Ht]; subst.
    destruct (sptr_eqb m q') eqn:E.
    - apply sptr_eqb_eq in E. subst q'. injection Hl as ->. exists []. eexists. split; [reflexivity|]. cbn [app].
      destruct xold as [| |am0]; try (exfalso; exact Hold); cbn [flat_map app snd]; reflexivity.
    - destruct (IH Ht Hl) as (l1 & l2 & E1 & E2).
      destruct x as [| |amx]; cbn [flat_map app]; rewrite ?E1, ?E2.
      + exists l1, l2. auto.
      + exists l1, l2. auto.
      + match goal with |- exists l0 l3, ?bx ++ _ = _ /\ _ => exists (bx ++ l1), l2; split; [rewrite app_assoc; reflexivity | rewrite (app_assoc bx l1); reflexivity] end.
  Qed.
End UsedIns.

