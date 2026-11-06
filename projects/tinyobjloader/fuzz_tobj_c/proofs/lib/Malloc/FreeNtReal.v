(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "astate"; "am_next"; "am_sc"; "MUsed"; "am_prev"; "ameta"; "MFree"; "st_free_meta_head"; "IRet"; "itree"; "nontrivial_free"; "am_freed"; "am_set_links"; "okay_to_free"; "am_last"; "bit"; "links_of"; "ones"; "st_init_done"; "st_seq"; "st_unmap_seq"; "st_usage"; "mlookup"; "mupdate"; "am_avail"; "region"; "set_free_meta_head"; "set_seq"; "set_unmap_seq"; "set_usage"; "st_active"; "st_area_head"; "st_area_tail"; "st_areas"; "st_avail_meta"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_avail_meta_count"; "st_bounces"; "st_brk"; "st_meta_alloc_shift"; "st_mmap_counter"; "st_regions"; "usage_of"; "with_links"; "brkst"; "@Corelib.Init.Datatypes"; "option"; "Some"; "bool"; "prod"; "false"; "pair"; "None"; "list"; "S"; "nat"; "fst"; "true"; "andb"; "nil"; "option_map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "memb"; "active_hd"; "usedX"; "keys"; "Inv"; "region_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb"; "zomb"; "zmetas"; "zmeta"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.Lists.List"; "In"; "NoDup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost"; "or_post"; "nmask"; "dq_post"; "fgd_post"; "fgm_post"; "fq_post"; "q0_mid"; "q1_s3"; "q2_s3"; "act_post"; "fgd_res"; "fgm_res"; "fgm_s5"; "seq_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree"; "fneed"; "nf_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "set_hd"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfFrame MallocWfRings MallocWfFree MallocLayout Zones2 ImageDelta FreeNtPost Zomb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition zomb_rel (X : list sptr) (sr s : astate) : Prop := ltac2:(tb__ "0|0|
S0S7Vs;S4bVX;Vsr;A2A3").

Lemma zmetas_fst X l : ltac2:(tb__ "0|2|
S0S3cS5A1S60S38S5S6A2M0S5S3fS5S6A2M1S4cVX;Vl;A2A4S60G0S5G1Vl;A4A3").
Proof. induction l as [|[q x] l IH]; [reflexivity|]. cbn. f_equal. exact IH. Qed.

Lemma keys_zomb X s : ltac2:(tb__ "0|0|
S0S3cS5A1S48S4bVX;Vs;A2A1S48Vs;A1A3").
Proof. unfold keys, zomb. destruct s; cbn. apply zmetas_fst. Qed.

Lemma mlookup_zmetas X l q : ltac2:(tb__ "0|0|
S0S35S6A1S1dS4cVX;Vl;A2Vq;A2S43S6S6S4dVX;Vq;A2S1dVl;Vq;A2A4A3").
Proof.
  induction l as [|[p x] l IH]; [reflexivity|]. cbn. destruct (sptr_eqb q p) eqn:E; [|exact IH].
  apply sptr_eqb_eq in E. subst p. reflexivity.
Qed.

Lemma MT_zomb X s q : ltac2:(tb__ "0|0|
S0S35S6A1S44S4bVX;Vs;A2Vq;A2S43S6S6S4dVX;Vq;A2S44Vs;Vq;A2A4A3").
Proof. unfold MT, zomb. destruct s; cbn. apply mlookup_zmetas. Qed.

Lemma MT_zomb_notX X s q : ltac2:(tb__ "0|0|
S0S37S45Vq;VX;A2S39A3S0S35S6A1S44S4bVX;Vs;A2Vq;A2S44Vs;Vq;A2A3F_;").
Proof. intros H. rewrite MT_zomb. unfold zmeta. rewrite H. destruct (MT s q); reflexivity. Qed.

Lemma MT_zomb_X X s q : ltac2:(tb__ "0|1|
S0S37S45Vq;VX;A2S40A3S4fS5Vq;S48Vs;A1A3S0S35S6A1S44S4bVX;Vs;A2Vq;A2S36S6SdS3bS5A1M0G0A2A2A3F_;F_;").
Proof.
  intros H Hk. rewrite MT_zomb. unfold zmeta. rewrite H.
  destruct (MT s q) eqn:E; [reflexivity|]. exfalso. unfold MT in E. apply (proj1 (mlookup_None_iff _ _) E). exact Hk.
Qed.

Lemma zomb_exempt X s : ltac2:(tb__ "0|2|
S5S4fS5R1VX;A3M0S4fS5R2S48Vs;A1A3F_;Fx;S5G0S0S35S6A1S44S4bVX;Vs;A2R2A2S36S6SdS3bS5A1M1G1A2A2A3F_;Fx;F_;").
Proof. intros HX x Hx. apply MT_zomb_X; [apply (proj2 (memb_In _ _)); exact Hx | exact (HX x Hx)]. Qed.

Lemma zmetas_nil l : ltac2:(tb__ "0|0|
S0S3cS38S5S6A2A1S4cS42S5A1Vl;A2Vl;A3").
Proof. induction l as [|[q x] l IH]; [reflexivity|]. cbn. f_equal. exact IH. Qed.
Lemma zomb_nil s : ltac2:(tb__ "0|0|
S0S7S4bS42S5A1Vs;A2Vs;A3").
Proof. unfold zomb. rewrite zmetas_nil. destruct s; reflexivity. Qed.

Lemma zmetas_id X l : ltac2:(tb__ "0|3|
S50S5S60S38S5S6A2M0S5S3fS5S6A2Vl;A4M1A2S5S0S37S45R1VX;A2S40A3S4fS5R2G1A3S0S35S6A1S1dVl;R3A2S36S6SdS3bS5A1M2G2A2A2A3F_;F_;Fq;S0S3cG0A1S4cVX;Vl;A2Vl;A3F_;F_;").
Proof.
  induction l as [|[q x] l IH]; cbn; intros ND H; [reflexivity|].
  inversion ND as [|q0 l0 Hq Hl]; subst. f_equal.
  - unfold zmeta. destruct (memb q X) eqn:B; [|reflexivity].
    specialize (H q B ltac:(left; reflexivity)). rewrite sptr_eqb_refl in H. injection H as ->. reflexivity.
  - apply IH; [exact Hl|]. intros q' B' Hin. specialize (H q' B' ltac:(right; exact Hin)).
    destruct (sptr_eqb q' q) eqn:E; [|exact H]. apply sptr_eqb_eq in E. subst q'. exfalso. exact (Hq Hin).
Qed.
Lemma zomb_id X s : ltac2:(tb__ "0|2|
S50S5S48Vs;A1M0A2S5S4fS5R1VX;A3S4fS5R2G0A3S0S35S6A1S44Vs;R3A2S36S6SdS3bS5A1M1G1A2A2A3F_;F_;Fx;S0S7S4bVX;Vs;A2Vs;A3F_;F_;").
Proof.
  intros ND H. unfold zomb, keys, MT in *. destruct s; cbn -[zmetas] in *. rewrite (zmetas_id X _ ND); [reflexivity|].
  intros q B Hin. apply H; [apply memb_In; exact B | exact Hin].
Qed.

Lemma MT_virt_notX X s q m : ltac2:(tb__ "0|1|
S0S35S6A1S44S4bVX;Vs;A2Vq;A2S36S6Vm;A2A3S2S0S6Vm;SdS3bS5A1M0G0A2A3A1S0S37S45Vq;VX;A2S39A3F_;F_;").
Proof.
  intros E Hm. destruct (memb q X) eqn:B; [|reflexivity]. exfalso. rewrite MT_zomb in E. unfold zmeta in E. rewrite B in E.
  destruct (MT s q); [|discriminate]. cbn in E. injection E as <-. exact (Hm eq_refl).
Qed.

Lemma usedX_zomb X s q a : ltac2:(tb__ "0|0|
S4S47VX;S4bVX;Vs;A2Vq;Va;A4S47VX;Vs;Vq;Va;A4A2").
Proof.
  unfold usedX, MTX. split; intros H.
  - destruct (memb q X) eqn:B; [exact H|]. rewrite (MT_zomb_notX X s q B) in H. exact H.
  - destruct (memb q X) eqn:B; [exact H|]. rewrite (MT_zomb_notX X s q B). exact H.
Qed.

Lemma mupdate_zmetas_notX X l q x : ltac2:(tb__ "0|0|
S0S37S45Vq;VX;A2S39A3S0S3cS38S5S6A2A1S1eS4cVX;Vl;A2Vq;Vx;A3S4cVX;S1eVl;Vq;Vx;A3A2A3F_;").
Proof.
  intros H. induction l as [|[p y] l IH]; cbn.
  - unfold zmeta. rewrite H. reflexivity.
  - destruct (sptr_eqb q p) eqn:E; cbn; [|rewrite IH; reflexivity].
    apply sptr_eqb_eq in E. subst p. unfold zmeta. rewrite H. reflexivity.
Qed.

Lemma upd_meta_zomb X s q x : ltac2:(tb__ "0|0|
S0S37S45Vq;VX;A2S39A3S0S7S5fVq;Vx;S4bVX;Vs;A2A3S4bVX;S5fVq;Vx;Vs;A3A2A3F_;").
Proof. intros H. unfold upd_meta, zomb. destruct s; cbn -[zmetas mupdate]. rewrite (mupdate_zmetas_notX X _ q x H). reflexivity. Qed.

Lemma mupdate_zmetas_X X l q x : ltac2:(tb__ "0|1|
S0S37S45Vq;VX;A2S40A3S4fS5Vq;S60S38S5S6A2M0S5S3fS5S6A2Vl;A4A3S0S3cG0A1S4cVX;S1eVl;Vq;Vx;A3A2S4cVX;Vl;A2A3F_;F_;").
Proof.
  intros H. induction l as [|[p y] l IH]; cbn; intros Hin; [destruct Hin|].
  destruct (sptr_eqb q p) eqn:E; cbn.
  - apply sptr_eqb_eq in E. subst p. unfold zmeta. rewrite H. reflexivity.
  - rewrite IH; [reflexivity|]. destruct Hin as [->|Hin]; [rewrite sptr_eqb_refl in E; discriminate | exact Hin].
Qed.
Lemma upd_meta_zomb_X X s q x : ltac2:(tb__ "0|0|
S0S37S45Vq;VX;A2S40A3S4fS5Vq;S48Vs;A1A3S0S7S4bVX;S5fVq;Vx;Vs;A3A2S4bVX;Vs;A2A3F_;F_;").
Proof. intros H Hk. unfold upd_meta, zomb, keys in *. destruct s; cbn -[zmetas mupdate] in *. rewrite (mupdate_zmetas_X X _ q x H Hk). reflexivity. Qed.

Lemma zomb_ctx X s : ltac2:(tb__ "0|3|
S1S0S37S19S4bVX;Vs;A2M0A1S19Vs;A1A3S1S0S4eS30G0A1S30Vs;A1A3S1S0S35S5A1M1SeG0A1SeVs;A1A3S1S0S5S29G0A1S29Vs;A1A3S1S0S4eS2cG0A1S2cVs;A1A3S1S0S4eS2aG0A1S2aVs;A1A3S1S0S4eS2fG0A1S2fVs;A1A3S1S0G1S26G0A1S26Vs;A1A3S1S0G1S27G0A1S27Vs;A1A3S1S0S5S2bG0A1S2bVs;A1A3S1S0S3cG1A1S25G0A1S25Vs;A1A3S1S0S3cS4eA1M2S1cG0A1S1cVs;A1A3S1S0G2S1bG0A1S1bVs;A1A3S1S0G2S2dG0A1S2dVs;A1A3S1S0S4eS1aG0A1S1aVs;A1A3S1S0S34S2eG0A1S2eVs;A1A3S1S0S3cS20A1S31G0A1S31Vs;A1A3S0S3cS5A1S28G0A1S28Vs;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. destruct s; repeat split; reflexivity. Qed.

Lemma region_of_zomb X s k : ltac2:(tb__ "0|0|
S0S35S20A1S4aS4bVX;Vs;A2Vk;A2S4aVs;Vk;A2A3").
Proof. unfold region_of. destruct s; reflexivity. Qed.
Lemma st_init_done_zomb X s : ltac2:(tb__ "0|0|
S0S37S19S4bVX;Vs;A2A1S19Vs;A1A3").
Proof. destruct s; reflexivity. Qed.
Lemma active_hd_zomb X s c : ltac2:(tb__ "0|0|
S0S35S5A1S46S4bVX;Vs;A2Vc;A2S46Vs;Vc;A2A3").
Proof. unfold active_hd. destruct s; reflexivity. Qed.
Lemma usage_of_zomb X s c : ltac2:(tb__ "0|0|
S0S4eS32S4bVX;Vs;A2Vc;A2S32Vs;Vc;A2A3").
Proof. unfold usage_of. destruct s; reflexivity. Qed.
Lemma okay_to_free_zomb X s g am : ltac2:(tb__ "0|0|
S0S37S14S4bVX;Vs;A2Vg;Vam;A3S14Vs;Vg;Vam;A3A3").
Proof. unfold okay_to_free, is_bouncing, usage_of. destruct s; reflexivity. Qed.

Lemma set_hd_zomb X s c v : ltac2:(tb__ "0|0|
S0S7S67Vc;Vv;S4bVX;Vs;A2A3S4bVX;S67Vc;Vv;Vs;A3A2A3").
Proof. unfold set_hd, zomb. destruct s; reflexivity. Qed.
Lemma set_usage_zomb X s v : ltac2:(tb__ "0|0|
S0S7S24Vv;S4bVX;Vs;A2A2S4bVX;S24Vv;Vs;A2A2A3").
Proof. unfold zomb. destruct s; reflexivity. Qed.
Lemma set_seq_zomb X s v : ltac2:(tb__ "0|0|
S0S7S22Vv;S4bVX;Vs;A2A2S4bVX;S22Vv;Vs;A2A2A3").
Proof. unfold zomb. destruct s; reflexivity. Qed.
Lemma set_unmap_seq_zomb X s v : ltac2:(tb__ "0|0|
S0S7S23Vv;S4bVX;Vs;A2A2S4bVX;S23Vv;Vs;A2A2A3").
Proof. unfold zomb. destruct s; reflexivity. Qed.
Lemma set_free_meta_head_zomb X s v : ltac2:(tb__ "0|0|
S0S7S21Vv;S4bVX;Vs;A2A2S4bVX;S21Vv;Vs;A2A2A3").
Proof. unfold zomb. destruct s; reflexivity. Qed.

Lemma addr_of_injective X R U s L (HI : Inv X R U s) (HL : layout_ok L s) q q' : ltac2:(tb__ "0|1|
S4fS5Vq;S48Vs;A1M0A3S4fS5Vq';G0A3S0S4eS61VL;Vq;A2S61VL;Vq';A2A3S0S5Vq;Vq';A3F_;F_;F_;").
Proof.
  intros Hq Hq' E. destruct (sptr_eq_dec q q') as [H|H]; [exact H|]. exfalso.
  pose proof (Zones2.meta_ranges_disjoint X R U s L HI HL q q' Hq Hq' H) as D. unfold META_SIZE in D. lia.
Qed.

Lemma used_at_addr X R U s L (HI : Inv X R U s) (HL : layout_ok L s) g am g' am' : ltac2:(tb__ "0|0|
S47VX;Vs;Vg;Vam;A4S47VX;Vs;Vg';Vam';A4S0S4eS61VL;Vg';A2S61VL;Vg;A2A3S1S0S5Vg';Vg;A3S0ScVam';Vam;A3A2F_;F_;F_;").
Proof.
  intros Hu Hu' E. pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as M. pose proof (proj1 (usedX_MT _ _ _ _ Hu')) as M'.
  pose proof (addr_of_injective X R U s L HI HL g' g (MT_Some_In_keys _ _ _ M') (MT_Some_In_keys _ _ _ M) E) as ->.
  split; [reflexivity|]. rewrite M in M'. injection M' as ->. reflexivity.
Qed.

Section WithInv.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (sr : astate).
  Hypothesis HIr : ltac2:(tb__ "0|0|
S49VX;VR;VU;Vsr;A4").
  Lemma X_keys x : ltac2:(tb__ "0|0|
S4fS5Vx;VX;A3S4fS5Vx;S48Vsr;A1A3F_;").
  Proof using HIr. intros Hx. exact (proj1 (inv_X HIr x Hx)). Qed.
  Lemma xzomb_real : ltac2:(tb__ "0|1|
S5S4fS5R1VX;A3S0S35S6A1S44S4bVX;Vsr;A2R2A2S36S6SdS3bS5A1M0G0A2A2A3F_;Fx;").
  Proof using HIr. exact (zomb_exempt X sr X_keys). Qed.

  Lemma used_notX q a : ltac2:(tb__ "0|0|
S47VX;S4bVX;Vsr;A2Vq;Va;A4S0S37S45Vq;VX;A2S39A3F_;").
  Proof using . intros Hu. exact (proj2 (usedX_MT _ _ _ _ Hu)). Qed.
End WithInv.

Section RealElse.
  Variables (X : list sptr) (U : Z -> Z) (sr : astate) (g : sptr) (am : ameta) (i : Z).
  Let s : astate := zomb X sr.
  Hypothesis HIr : ltac2:(tb__ "0|0|
S49VX;S36S38S5S4eA2S3aS5S4eVg;Vi;A4A2VU;Vsr;A4").
  Hypothesis Hu : ltac2:(tb__ "0|0|
S47VX;Vs;Vg;Vam;A4").
  Hypothesis HU : forall c, 0 <= U c.
  Hypothesis HR2g : ltac2:(tb__ "0|2|
S2S0S38S35S5A1M0G0A2S3aG0G0SbVam;A1S8Vam;A1A4S3aG0G0S3bS5A1M1G1A4A3A1S2S0G0S46Vs;S9Vam;A1A2S36S5Vg;A2A3A1S2S0S4eS12Vam;A1Z0A3A1F_;F_;").
  Hypothesis Helse : ltac2:(tb__ "0|0|
S0S37S41S63S62S52Vam;A1S16Vi;A1A2S18S15Vam;A1A1A2S14Vs;Vg;Vam;A3A2S39A3").

  Lemma Hu_r : ltac2:(tb__ "0|0|
S47VX;Vsr;Vg;Vam;A4"). Proof using Hu. exact (proj1 (usedX_zomb X sr g am) Hu). Qed.
  Lemma gX : ltac2:(tb__ "0|0|
S0S37S45Vg;VX;A2S39A3"). Proof using Hu. exact (proj2 (usedX_MT _ _ _ _ Hu)). Qed.
  Lemma HR2g_r : ltac2:(tb__ "0|2|
S2S0S38S35S5A1M0G0A2S3aG0G0SbVam;A1S8Vam;A1A4S3aG0G0S3bS5A1M1G1A4A3A1S2S0G0S46Vsr;S9Vam;A1A2S36S5Vg;A2A3A1S2S0S4eS12Vam;A1Z0A3A1F_;F_;").
  Proof using HR2g. intros H1 H2. apply HR2g; [exact H1|]. unfold s. rewrite active_hd_zomb. exact H2. Qed.
  Lemma Helse_r : ltac2:(tb__ "0|0|
S0S37S41S63S62S52Vam;A1S16Vi;A1A2S18S15Vam;A1A1A2S14Vsr;Vg;Vam;A3A2S39A3").
  Proof using Helse. unfold s in Helse. rewrite okay_to_free_zomb in Helse. exact Helse. Qed.

  Lemma MT_used_r q a : ltac2:(tb__ "0|2|
S0S35S6A1M0S44Vs;Vq;A2S36S6SaVa;A1A2M1A3S0G0S44Vsr;Vq;A2G1A3F_;").
  Proof using X.
    intros M. assert (B : memb q X = false) by (apply (MT_virt_notX X sr q (MUsed a) M); discriminate).
    unfold s in M. rewrite (MT_zomb_notX X sr q B) in M. exact M.
  Qed.
  Lemma notX_used q a : ltac2:(tb__ "0|0|
S0S35S6A1S44Vs;Vq;A2S36S6SaVa;A1A2A3S0S37S45Vq;VX;A2S39A3F_;").
  Proof using sr. intros M. apply (MT_virt_notX X sr q (MUsed a) M). discriminate. Qed.

  Lemma or_post_zomb t a : ltac2:(tb__ "0|0|
S0S7S4bVX;S51Vg;Vi;Vt;Va;A4A2S51Vg;Vi;S4bVX;Vt;A2Va;A4A3").
  Proof using Hu. unfold or_post. symmetry. apply upd_meta_zomb. exact gX. Qed.

  Theorem or_real fuel : ltac2:(tb__ "0|4|
S2S0S4eS52Vam;A1Z0A3A1S1S0S10S7S38S35S38S3eS4eA2M0A1M1S7A2M2A2S11S3dVfuel;A1Vg;Vi;Vsr;A4SfS7G2S3aG1S7S3bG0A1S51Vg;Vi;Vsr;Vam;A4M3A4A3A3S0S7S4bVX;G3A2S51Vg;Vi;Vs;Vam;A4A3A2F_;").
  Proof using Helse Hu. intros Hm. split; [exact (or_eq X sr g am i Hu_r Helse_r fuel Hm) | apply or_post_zomb]. Qed.

  Theorem qg_real fuel : ltac2:(tb__ "0|4|
S0S4eS52Vam;A1Z0A3S0S35S5A1S46Vs;S9Vam;A1A2S36S5Vg;A2A3S1S0S10S7S38S35S38S3eS4eA2M0A1M1S7A2M2A2S11S3dVfuel;A1Vg;Vi;Vsr;A4SfS7G2S3aG1S7S3bG0A1S51Vg;Vi;Vsr;Vam;A4M3A4A3A3S0S7S4bVX;G3A2S51Vg;Vi;Vs;Vam;A4A3A2F_;F_;").
  Proof using HIr Helse Hu.
    intros Hm Hhd. split; [|apply or_post_zomb].
    apply (qg_eq X U sr g am i HIr Hu_r Helse_r fuel Hm). unfold s in Hhd. rewrite active_hd_zomb in Hhd. exact Hhd.
  Qed.

  Theorem q0_real fuel : ltac2:(tb__ "0|8|
S0S4eS52Vam;A1Z0A3S0S35S5A1M0S46Vs;S9Vam;A1A2S3bS5A1M1A3S0G0SbVam;A1G1A3S0G0S8Vam;A1G1A3S1S0S10S7S38S35S38S3eS4eA2M2A1M3S7A2M4A2S11S3dVfuel;A1Vg;Vi;Vsr;A4SfS7G4S3aG3S7S3bG2A1S51Vg;Vi;S57Vsr;Vg;Vam;A3S13S36S5Vg;A2M5G5Vam;A3M6A4M7A4A3A3S0S7S4bVX;G7A2S51Vg;Vi;S57Vs;Vg;Vam;A3G6A4A3A2F_;F_;F_;F_;").
  Proof using HIr Helse Hu.
    intros Hm Hhd Hp Hn. split.
    - apply (q0_eq X U sr g am i HIr Hu_r Helse_r fuel Hm); [|exact Hp|exact Hn]. unfold s in Hhd. rewrite active_hd_zomb in Hhd. exact Hhd.
    - rewrite or_post_zomb. f_equal. unfold q0_mid, s. rewrite <- set_hd_zomb, (upd_meta_zomb X sr g _ gX). reflexivity.
  Qed.

  Section WithHead.
    Variables (h : sptr) (ah : ameta).
    Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S35S5A1S46Vs;S9Vam;A1A2S36S5Vh;A2A3").
    Hypothesis Hhg : h <> g.
    Hypothesis Mh : ltac2:(tb__ "0|0|
S0S35S6A1S44Vs;Vh;A2S36S6SaVah;A1A2A3").
    Hypothesis Hp : am_prev am = None.
    Hypothesis Hn : am_next am = None.
    Lemma Hhd_r : ltac2:(tb__ "0|0|
S0S35S5A1S46Vsr;S9Vam;A1A2S36S5Vh;A2A3"). Proof using Hhd. unfold s in Hhd. rewrite active_hd_zomb in Hhd. exact Hhd. Qed.
    Lemma Mh_r : ltac2:(tb__ "0|0|
S0S35S6A1S44Vsr;Vh;A2S36S6SaVah;A1A2A3"). Proof using Mh. exact (MT_used_r h ah Mh). Qed.
    Lemma hX : ltac2:(tb__ "0|0|
S0S37S45Vh;VX;A2S39A3"). Proof using Mh. exact (notX_used h ah Mh). Qed.

    Theorem q1_real fuel : ltac2:(tb__ "0|6|
S0S4eS52Vam;A1Z0A3S0S35S5A1SbVah;A1S36S5Vh;A2M0A3S1S0S10S7S38S35S38S3eS4eA2M1A1M2S7A2M3A2S11S3dVfuel;A1Vg;Vi;Vsr;A4SfS7G3S3aG2S7S3bG1A1S51Vg;Vi;S58Vsr;Vg;Vam;Vh;Vah;A5S13G0G0Vam;A3M4A4M5A4A3A3S0S7S4bVX;G5A2S51Vg;Vi;S58Vs;Vg;Vam;Vh;Vah;A5G4A4A3A2F_;F_;").
    Proof using HIr Helse Hhd Hhg Hn Hp Hu Mh.
      intros Hm Hhp. split.
      - exact (q1_eq X U sr g am i HIr Hu_r Helse_r h ah Hhd_r Hhg Mh_r Hp Hn fuel Hm Hhp).
      - rewrite or_post_zomb. f_equal. unfold q1_s3, q1_s1, s. rewrite <- (upd_meta_zomb X _ h _ hX), <- (upd_meta_zomb X sr g _ gX). reflexivity.
    Qed.

    Variables (t : sptr) (at_ : ameta).
    Hypothesis Htg : t <> g.
    Hypothesis Hth : t <> h.
    Hypothesis Mt : ltac2:(tb__ "0|0|
S0S35S6A1S44Vs;Vt;A2S36S6SaVat_;A1A2A3").
    Lemma Mt_r : ltac2:(tb__ "0|0|
S0S35S6A1S44Vsr;Vt;A2S36S6SaVat_;A1A2A3"). Proof using Mt. exact (MT_used_r t at_ Mt). Qed.
    Lemma tX : ltac2:(tb__ "0|0|
S0S37S45Vt;VX;A2S39A3"). Proof using Mt. exact (notX_used t at_ Mt). Qed.
    Theorem q2_real fuel : ltac2:(tb__ "0|6|
S0S4eS52Vam;A1Z0A3S0S35S5A1SbVah;A1S36S5Vt;A2M0A3S1S0S10S7S38S35S38S3eS4eA2M1A1M2S7A2M3A2S11S3dVfuel;A1Vg;Vi;Vsr;A4SfS7G3S3aG2S7S3bG1A1S51Vg;Vi;S59Vsr;Vg;Vam;Vh;Vah;Vt;Vat_;A7S13G0S36S5Vh;A2Vam;A3M4A4M5A4A3A3S0S7S4bVX;G5A2S51Vg;Vi;S59Vs;Vg;Vam;Vh;Vah;Vt;Vat_;A7G4A4A3A2F_;F_;").
    Proof using HIr Helse Hhd Hhg Hn Hp Htg Hth Hu Mh Mt.
      intros Hm Hhp. split.
      - exact (q2_eq X U sr g am i HIr Hu_r Helse_r h ah Hhd_r Hhg Mh_r Hp Hn t at_ Htg Hth Mt_r fuel Hm Hhp).
      - rewrite or_post_zomb. f_equal. unfold q2_s3, q2_s2, q2_s1, s.
        rewrite <- (upd_meta_zomb X _ h _ hX), <- (upd_meta_zomb X _ t _ tX), <- (upd_meta_zomb X sr g _ gX). reflexivity.
    Qed.
  End WithHead.

  Lemma xne q x : ltac2:(tb__ "0|0|
S0S37S45Vq;VX;A2S39A3S4fS5Vx;VX;A3S2S0S5Vq;Vx;A3A1F_;F_;").
  Proof using . intros Hq Hx ->. rewrite (proj2 (memb_In x X) Hx) in Hq. discriminate. Qed.
  Lemma or_X t a x : ltac2:(tb__ "0|0|
S4fS5Vx;VX;A3S0S35S6A1S44S51Vg;Vi;Vt;Va;A4Vx;A2S44Vt;Vx;A2A3F_;").
  Proof using Hu. intros Hx. apply MT_or_other. exact (fun E => xne g x gX Hx (eq_sym E)). Qed.
  Lemma q0_X x : ltac2:(tb__ "0|1|
S4fS5Vx;VX;A3S0S35S6A1S44S51Vg;Vi;S57Vsr;Vg;Vam;A3S13S36S5Vg;A2M0G0Vam;A3A4Vx;A2S44Vsr;Vx;A2A3F_;").
  Proof using Hu. intros Hx. rewrite (or_X _ _ x Hx). apply MT_q0_other. exact (fun E => xne g x gX Hx (eq_sym E)). Qed.
  Section WithHeadX.
    Variables (h : sptr) (ah : ameta).
    Hypothesis Mh : ltac2:(tb__ "0|0|
S0S35S6A1S44Vs;Vh;A2S36S6SaVah;A1A2A3").
    Lemma q1_X x : ltac2:(tb__ "0|1|
S4fS5Vx;VX;A3S0S35S6A1S44S51Vg;Vi;S58Vsr;Vg;Vam;Vh;Vah;A5S13S36S5Vh;A2M0G0Vam;A3A4Vx;A2S44Vsr;Vx;A2A3F_;").
    Proof using Hu Mh. intros Hx. rewrite (or_X _ _ x Hx). apply MT_q1_other; [exact (fun E => xne g x gX Hx (eq_sym E)) | exact (fun E => xne h x (notX_used h ah Mh) Hx (eq_sym E))]. Qed.
    Variables (t : sptr) (at_ : ameta).
    Hypothesis Mt : ltac2:(tb__ "0|0|
S0S35S6A1S44Vs;Vt;A2S36S6SaVat_;A1A2A3").
    Lemma q2_X x : ltac2:(tb__ "0|0|
S4fS5Vx;VX;A3S0S35S6A1S44S51Vg;Vi;S59Vsr;Vg;Vam;Vh;Vah;Vt;Vat_;A7S13S36S5Vt;A2S36S5Vh;A2Vam;A3A4Vx;A2S44Vsr;Vx;A2A3F_;").
    Proof using Hu Mh Mt. intros Hx. rewrite (or_X _ _ x Hx). apply MT_q2_other; [exact (fun E => xne g x gX Hx (eq_sym E)) | exact (fun E => xne h x (notX_used h ah Mh) Hx (eq_sym E)) | exact (fun E => xne t x (notX_used t at_ Mt) Hx (eq_sym E))]. Qed.
  End WithHeadX.

  Theorem nf_real fuel r : ltac2:(tb__ "0|2|
S0S10S7S38S35S38S3eS4eA2A1S7A2M0A2S11S3dVfuel;A1M1Vg;Vi;Vsr;A4SfS7G0Vr;A3A3S64S65S9Vam;A1A1G1A2S66VX;VU;Vsr;Vr;A4F_;F_;").
  Proof using HIr HR2g HU Hu. exact (else_nf_post X U sr g am i HIr Hu_r HU HR2g_r fuel r). Qed.
End RealElse.

Lemma st_free_meta_head_zomb X t : ltac2:(tb__ "0|0|
S0S35S5A1SeS4bVX;Vt;A2A1SeVt;A1A3").
Proof. destruct t; reflexivity. Qed.
Lemma st_seq_zomb X t : ltac2:(tb__ "0|0|
S0S4eS1aS4bVX;Vt;A2A1S1aVt;A1A3").
Proof. destruct t; reflexivity. Qed.
Lemma st_usage_zomb X t : ltac2:(tb__ "0|0|
S0S3cS4eA1S1cS4bVX;Vt;A2A1S1cVt;A1A3").
Proof. destruct t; reflexivity. Qed.
Lemma st_unmap_seq_zomb X t : ltac2:(tb__ "0|0|
S0S3cS4eA1S1bS4bVX;Vt;A2A1S1bVt;A1A3").
Proof. destruct t; reflexivity. Qed.
Lemma seq_post_zomb X t : ltac2:(tb__ "0|0|
S0S7S5eS4bVX;Vt;A2A1S4bVX;S5eVt;A1A2A3").
Proof. unfold seq_post. rewrite st_seq_zomb. destruct (st_seq t =? 255); rewrite <- ?set_seq_zomb, <- ?set_unmap_seq_zomb; reflexivity. Qed.

Lemma fq_post_zomb X t g : ltac2:(tb__ "0|1|
S0S37S45Vg;VX;A2S39A3S5S0S35S5A1M0SeVt;A1S36S5R1A2A3S1S0S37S45R2VX;A2S39A3S6S5S0S35S6A1S44Vt;R4A2S36S6R2A2A3S0G0S3fG0G0S17R3A1A3S36S5R2A2A3S0S37S45R3VX;A2S39A3F_;F_;Fhp;Fxf;A2F_;Ffm;S0S7S56S4bVX;Vt;A2Vg;A2S4bVX;S56Vt;Vg;A2A2A3F_;F_;").
Proof.
  intros Hg Hring. unfold fq_post. rewrite st_free_meta_head_zomb.
  destruct (st_free_meta_head t) as [fm|] eqn:Eh.
  - destruct (Hring fm eq_refl) as [Hfm Hhp]. rewrite (MT_zomb_notX X t fm Hfm).
    destruct (MT t fm) as [xf|] eqn:Mf; [|reflexivity].
    destruct (fst (links_of xf)) as [hp|] eqn:El; [|reflexivity].
    specialize (Hhp xf hp eq_refl El). cbn zeta.
    rewrite (upd_meta_zomb X t g _ Hg), (MT_zomb_notX X _ hp Hhp), (upd_meta_zomb X _ hp _ Hhp), (MT_zomb_notX X _ fm Hfm), (upd_meta_zomb X _ fm _ Hfm).
    reflexivity.
  - rewrite (upd_meta_zomb X t g _ Hg), <- set_free_meta_head_zomb. reflexivity.
Qed.

Lemma fq_post_X X t g x : ltac2:(tb__ "0|2|
S0S37S45Vg;VX;A2S39A3S5S0S35S5A1M0SeVt;A1S36S5R1A2A3S1S0S37S45R2VX;A2S39A3S6S5S0S35S6A1M1S44Vt;R4A2S36S6R2A2A3S0G0S3fG0G0S17R3A1A3S36S5R2A2A3S0S37S45R3VX;A2S39A3F_;F_;Fhp;Fxf;A2F_;Ffm;S0S37S45Vx;VX;A2S40A3S0G1S44S56Vt;Vg;A2Vx;A2S44Vt;Vx;A2A3F_;F_;F_;").
Proof.
  intros Hg Hring Hx. assert (NE : forall q, memb q X = false -> q <> x) by (intros q Hq ->; rewrite Hx in Hq; discriminate).
  unfold fq_post. destruct (st_free_meta_head t) as [fm|] eqn:Eh.
  - destruct (Hring fm eq_refl) as [Hfm Hhp]. destruct (MT t fm) as [xf|] eqn:Mf; [|reflexivity].
    destruct (fst (links_of xf)) as [hp|] eqn:El; [|reflexivity]. specialize (Hhp xf hp eq_refl El). cbn zeta.
    rewrite (MT_upd_other fm _ _ x (fun E => NE fm Hfm (eq_sym E))), (MT_upd_other hp _ _ x (fun E => NE hp Hhp (eq_sym E))), (MT_upd_other g _ _ x (fun E => NE g Hg (eq_sym E))). reflexivity.
  - unfold MT, upd_meta. destruct t; cbn -[mupdate mlookup]. apply mlookup_mupdate_other. exact (fun E => NE g Hg (eq_sym E)).
Qed.

Section RealDirect.
  Variables (X : list sptr) (U : Z -> Z) (sr : astate) (g : sptr) (am : ameta) (i : Z).
  Let s : astate := zomb X sr.
  Hypothesis HIr : ltac2:(tb__ "0|0|
S49VX;S36S38S5S4eA2S3aS5S4eVg;Vi;A4A2VU;Vsr;A4").
  Hypothesis Hu : ltac2:(tb__ "0|0|
S47VX;Vs;Vg;Vam;A4").
  Hypothesis HU : forall c, 0 <= U c.
  Hypothesis HR2g : ltac2:(tb__ "0|2|
S2S0S38S35S5A1M0G0A2S3aG0G0SbVam;A1S8Vam;A1A4S3aG0G0S3bS5A1M1G1A4A3A1S2S0G0S46Vs;S9Vam;A1A2S36S5Vg;A2A3A1S2S0S4eS12Vam;A1Z0A3A1F_;F_;").
  Hypothesis Hall : ltac2:(tb__ "0|0|
S0S4eS62S52Vam;A1S16Vi;A1A2S18S15Vam;A1A1A3").
  Hypothesis Hsc63 : am_sc am = 63.
  Hypothesis Hnx : am_next am = None.
  Hypothesis Hml : am_maplen am <> 0.

  Hypothesis Hfree_ringX : ltac2:(tb__ "0|3|
S5S0S35S5A1M0SeVs;A1S36S5R1A2M1A3S1S2S0S5R2Vg;A3A1S3G0G0S3G0G0S3S5S5S1S0S35S6A1M2S44Vs;R5A2S36S6SdR3R2A2A2A3S1S0G0R3G1A3S1S2S0S5R1Vg;A3A1S1S2S0G2S44Vs;R1A2S3bS6A1A3A1S0S37S45R1VX;A2S39A3A2A2A2A2Lhp;A2Lnx;A2Lpr;A2A2F_;Ffm;").

  Lemma dgX : ltac2:(tb__ "0|0|
S0S37S45Vg;VX;A2S39A3"). Proof using Hu. exact (proj2 (usedX_MT _ _ _ _ Hu)). Qed.
  Lemma dHu_r : ltac2:(tb__ "0|0|
S47VX;Vsr;Vg;Vam;A4"). Proof using Hu. exact (proj1 (usedX_zomb X sr g am) Hu). Qed.
  Lemma dHR2g_r : ltac2:(tb__ "0|2|
S2S0S38S35S5A1M0G0A2S3aG0G0SbVam;A1S8Vam;A1A4S3aG0G0S3bS5A1M1G1A4A3A1S2S0G0S46Vsr;S9Vam;A1A2S36S5Vg;A2A3A1S2S0S4eS12Vam;A1Z0A3A1F_;F_;").
  Proof using HR2g. intros H1 H2. apply HR2g; [exact H1|]. unfold s. rewrite active_hd_zomb. exact H2. Qed.
  Lemma fmX fm : ltac2:(tb__ "0|0|
S0S35S5A1SeVsr;A1S36S5Vfm;A2A3S1S0S37S45Vfm;VX;A2S39A3S0S35S6A1S44Vsr;Vfm;A2S44Vs;Vfm;A2A3A2F_;").
  Proof using Hfree_ringX.
    intros Hfh. destruct (Hfree_ringX fm ltac:(unfold s; rewrite st_free_meta_head_zomb; exact Hfh)) as (_ & pr & nx & hp & M & -> & _).
    assert (B : memb fm X = false) by (apply (MT_virt_notX X sr fm _ M); discriminate).
    split; [exact B|]. unfold s. rewrite (MT_zomb_notX X sr fm B). reflexivity.
  Qed.
  Lemma Hfree_ring_r : ltac2:(tb__ "0|3|
S5S0S35S5A1M0SeVsr;A1S36S5R1A2M1A3S1S2S0S5R2Vg;A3A1S3G0G0S3G0G0S3S5S5S1S0S35S6A1M2S44Vsr;R5A2S36S6SdR3R2A2A2A3S1S0G0R3G1A3S1S2S0S5R1Vg;A3A1S2S0G2S44Vsr;R1A2S3bS6A1A3A1A2A2A2Lhp;A2Lnx;A2Lpr;A2A2F_;Ffm;").
  Proof using Hfree_ringX.
    intros fm Hfh. destruct (fmX fm Hfh) as [B E].
    destruct (Hfree_ringX fm ltac:(unfold s; rewrite st_free_meta_head_zomb; exact Hfh)) as (NE & pr & nx & hp & M & Ep & NEh & Mh & Bh).
    split; [exact NE|]. exists pr, nx, hp. split; [rewrite E; exact M|]. split; [exact Ep|]. split; [exact NEh|].
    unfold s in Mh. rewrite (MT_zomb_notX X sr hp Bh) in Mh. exact Mh.
  Qed.

  Theorem fgd_real fuel : ltac2:(tb__ "0|3|
S1S0S10S7S38S35S38S3eS4eA2A1M0S7A2M1A2S11S3dVfuel;A1Vg;Vi;Vsr;A4SfS7G1S3aG0S7S5bVam;A1S54Vsr;Vg;A2M2A4A3A3S0S7S4bVX;G2A2S54Vs;Vg;A2A3A2").
  Proof using Hall Hfree_ringX Hml Hnx Hsc63 Hu.
    split.
    - exact (fgd_eq X sr g am i dHu_r Hall Hsc63 Hnx Hml Hfree_ring_r fuel).
    - unfold fgd_post, fgd_s2, s. rewrite seq_post_zomb, (upd_meta_zomb X _ g _ dgX). symmetry. apply fq_post_zomb; [exact dgX|].
      intros fm Hfh. rewrite head_upd_meta in Hfh.
      assert (Hfh0 : st_free_meta_head sr = Some fm) by (rewrite <- (seq_post_head sr); exact Hfh).
      destruct (fmX fm Hfh0) as [B E]. split; [exact B|].
      intros xf hp M El. rewrite MT_upd in M. destruct (sptr_eqb fm g) eqn:Efg.
      + injection M as <-. cbn in El. discriminate.
      + rewrite MT_seq_post in M.
        destruct (Hfree_ringX fm ltac:(unfold s; rewrite st_free_meta_head_zomb; exact Hfh0)) as (_ & pr & nx & hp' & M' & Ep & _ & _ & Bh).
        rewrite <- E, M in M'. injection M' as ->. cbn in El. rewrite Ep in El. injection El as <-. exact Bh.
  Qed.
  Theorem fgd_nf_real fuel : ltac2:(tb__ "0|0|
S64S65S9Vam;A1A1S3dVfuel;A1A2S66VX;VU;Vsr;S3aS35S38S3eS4eA2A1S7S5bVam;A1S54Vsr;Vg;A2A4A4F_;").
  Proof using HIr HR2g HU Hall Hfree_ringX Hml Hnx Hsc63 Hu. exact (fgd_nf_post X U sr g am i HIr dHu_r HU dHR2g_r Hall Hsc63 Hnx Hml Hfree_ring_r fuel). Qed.
  Theorem fgd_X x : ltac2:(tb__ "0|0|
S4fS5Vx;VX;A3S0S35S6A1S44S54Vsr;Vg;A2Vx;A2S44Vsr;Vx;A2A3F_;").
  Proof using Hfree_ringX Hu.
    intros Hx. assert (Bx : memb x X = true) by (apply memb_In; exact Hx).
    unfold fgd_post, fgd_s2. rewrite (fq_post_X X _ g x dgX).
    - rewrite MT_upd_other; [apply MT_seq_post|]. intros E. pose proof dgX as B. rewrite <- E, Bx in B. discriminate.
    - intros fm Hfh. rewrite head_upd_meta in Hfh.
      assert (Hfh0 : st_free_meta_head sr = Some fm) by (rewrite <- (seq_post_head sr); exact Hfh).
      destruct (fmX fm Hfh0) as [B E]. split; [exact B|].
      intros xf hp M El. rewrite MT_upd in M. destruct (sptr_eqb fm g) eqn:Efg.
      + injection M as <-. cbn in El. discriminate.
      + rewrite MT_seq_post in M.
        destruct (Hfree_ringX fm ltac:(unfold s; rewrite st_free_meta_head_zomb; exact Hfh0)) as (_ & pr & nx & hp' & M' & Ep & _ & _ & Bh).
        rewrite <- E, M in M'. injection M' as ->. cbn in El. rewrite Ep in El. injection El as <-. exact Bh.
    - exact Bx.
  Qed.
End RealDirect.

Section RealDq.
  Variables (X : list sptr) (t : astate) (g : sptr) (am : ameta).
  Hypothesis gX : ltac2:(tb__ "0|0|
S0S37S45Vg;VX;A2S39A3").
  Hypothesis nX : ltac2:(tb__ "0|0|
S5S0S35S5A1S8Vam;A1S36S5R1A2A3S0S37S45R2VX;A2S39A3F_;Fn;").
  Hypothesis pX : ltac2:(tb__ "0|0|
S5S0S35S5A1SbVam;A1S36S5R1A2A3S0S37S45R2VX;A2S39A3F_;Fp;").
  Lemma dq_post_zomb : ltac2:(tb__ "0|0|
S0S7S53S4bVX;Vt;A2Vg;Vam;A3S4bVX;S53Vt;Vg;Vam;A3A2A3").
  Proof using gX nX pX.
    unfold dq_post. destruct (am_next am) as [n|] eqn:En; [|reflexivity].
    destruct (sptr_eqb n g).
    - rewrite set_hd_zomb, (upd_meta_zomb X _ g _ gX). reflexivity.
    - destruct (am_prev am) as [p|] eqn:Ep; [|reflexivity]. cbn zeta.
      pose proof (nX n eq_refl) as Bn. pose proof (pX p eq_refl) as Bp.
      rewrite (MT_zomb_notX X t p Bp), (upd_meta_zomb X t p _ Bp), (MT_zomb_notX X _ n Bn), (upd_meta_zomb X _ n _ Bn), active_hd_zomb.
      destruct (osptr_eqb (active_hd t (am_sc am)) (Some g)); rewrite ?set_hd_zomb, (upd_meta_zomb X _ g _ gX); reflexivity.
  Qed.
  Lemma act_post_zomb s0 u : ltac2:(tb__ "0|0|
S0S7S5aS4bVX;Vs0;A2Vg;Vam;S4bVX;Vu;A2A4S4bVX;S5aVs0;Vg;Vam;Vu;A4A2A3").
  Proof using nX.
    unfold act_post. destruct (am_next am) as [n|] eqn:En; [|reflexivity]. rewrite active_hd_zomb.
    destruct (negb (sptr_eqb n g) && osptr_eqb (active_hd s0 (am_sc am)) (Some g)); [|reflexivity].
    pose proof (nX n eq_refl) as Bn. rewrite (MT_zomb_notX X u n Bn).
    destruct (MT u n) as [[| |an]|]; try reflexivity. apply upd_meta_zomb. exact Bn.
  Qed.
  Lemma fgm_s5_zomb : ltac2:(tb__ "0|0|
S0S7S5dS4bVX;Vt;A2Vg;Vam;A3S4bVX;S5dVt;Vg;Vam;A3A2A3").
  Proof using gX nX pX.
    unfold fgm_s5, fgm_s4, fgm_s3, fgm_s2, fgm_s1.
    rewrite dq_post_zomb, act_post_zomb, usage_of_zomb, st_usage_zomb, set_usage_zomb, seq_post_zomb.
    destruct (bounce_idx (am_sc am)) as [k|]; rewrite ?st_seq_zomb, ?st_unmap_seq_zomb, ?set_unmap_seq_zomb; apply upd_meta_zomb; exact gX.
  Qed.
End RealDq.

Section RealMapped.
  Variables (X : list sptr) (U : Z -> Z) (sr : astate) (g : sptr) (am : ameta) (i : Z).
  Let s : astate := zomb X sr.
  Hypothesis HIr : ltac2:(tb__ "0|0|
S49VX;S36S38S5S4eA2S3aS5S4eVg;Vi;A4A2VU;Vsr;A4").
  Hypothesis Hu : ltac2:(tb__ "0|0|
S47VX;Vs;Vg;Vam;A4").
  Hypothesis HU : forall c, 0 <= U c.
  Hypothesis HR2g : ltac2:(tb__ "0|2|
S2S0S38S35S5A1M0G0A2S3aG0G0SbVam;A1S8Vam;A1A4S3aG0G0S3bS5A1M1G1A4A3A1S2S0G0S46Vs;S9Vam;A1A2S36S5Vg;A2A3A1S2S0S4eS12Vam;A1Z0A3A1F_;F_;").
  Hypothesis Hall : ltac2:(tb__ "0|0|
S0S4eS62S52Vam;A1S16Vi;A1A2S18S15Vam;A1A1A3").
  Hypothesis Hsc : 0 <= am_sc am < 48.
  Hypothesis Hml : am_maplen am <> 0.
  Hypothesis Hok : ltac2:(tb__ "0|0|
S0S37S14Vs;Vg;Vam;A3S40A3").
  Hypothesis Hlinks : ltac2:(tb__ "0|2|
S5S0S35S5A1M0S8Vam;A1S36S5R1A2A3S2S0S5R2Vg;A3A1S3S5S5S3S6S6S3S6S6S1S0G0SbVam;A1S36S5R3A2A3S1S2S0S5R3Vg;A3A1S1S0S35S6A1M1S44Vs;R3A2S36S6R2A2A3S0G1S44S5fR3S33R2S3fG0G0S17R2A1A3S36S5R6A2A3Vs;A3R6A2S36S6R1A2A3A2A2A2Lxn;A2Lxp;A2Lp;A2F_;F_;Fn;").
  Hypothesis HnU : ltac2:(tb__ "0|0|
S5S0S35S5A1S8Vam;A1S36S5R1A2A3S3ScScS0S35S6A1S44Vs;R3A2S36S6SaR1A1A2A3Lan;A2F_;Fn;").
  Hypothesis HpU : ltac2:(tb__ "0|0|
S5S0S35S5A1SbVam;A1S36S5R1A2A3S3ScScS0S35S6A1S44Vs;R3A2S36S6SaR1A1A2A3Lap;A2F_;Fp;").
  Hypothesis Hact : ltac2:(tb__ "0|1|
S5ScS0S35S5A1M0S8Vam;A1S36S5R2A2A3S2S0S5R3Vg;A3A1S0G0S46Vs;S9Vam;A1A2S36S5Vg;A2A3S0S35S6A1S44S53Vs;Vg;Vam;A3R5A2S36S6SaR4A1A2A3S0S4eS1fR5A1Z0A3F_;F_;F_;F_;Fan;Fn;").
  Hypothesis HactU : ltac2:(tb__ "0|1|
S5S0S35S5A1M0S8Vam;A1S36S5R1A2A3S2S0S5R2Vg;A3A1S0G0S46Vs;S9Vam;A1A2S36S5Vg;A2A3S3ScScS0S35S6A1S44S53Vs;Vg;Vam;A3R5A2S36S6SaR1A1A2A3Lan;A2F_;F_;F_;Fn;").
  Hypothesis Hfree_ringX : ltac2:(tb__ "0|2|
S5S0S35S5A1M0SeVs;A1S36S5R1A2A3S1S2S0S5R2Vg;A3A1S3S5S5S3G0G0S3G0G0S3G0G0S1S0S35S6A1M1S44Vs;R6A2S36S6SdS36S5R4A2R3A2A2A3S1S2S0S5R4Vg;A3A1S1S0G1S44Vs;R4A2S36S6SdR2R1A2A2A3S0S37S45R4VX;A2S39A3A2A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2A2F_;Ffm;").

  Lemma mgX : ltac2:(tb__ "0|0|
S0S37S45Vg;VX;A2S39A3"). Proof using Hu. exact (proj2 (usedX_MT _ _ _ _ Hu)). Qed.
  Lemma mnX n : ltac2:(tb__ "0|0|
S0S35S5A1S8Vam;A1S36S5Vn;A2A3S0S37S45Vn;VX;A2S39A3F_;").
  Proof using HnU. intros En. destruct (HnU n En) as [an M]. apply (MT_virt_notX X sr n _ M). discriminate. Qed.
  Lemma mpX p : ltac2:(tb__ "0|0|
S0S35S5A1SbVam;A1S36S5Vp;A2A3S0S37S45Vp;VX;A2S39A3F_;").
  Proof using HpU. intros Ep. destruct (HpU p Ep) as [ap M]. apply (MT_virt_notX X sr p _ M). discriminate. Qed.
  Lemma mHu_r : ltac2:(tb__ "0|0|
S47VX;Vsr;Vg;Vam;A4"). Proof using Hu. exact (proj1 (usedX_zomb X sr g am) Hu). Qed.
  Lemma mHR2g_r : ltac2:(tb__ "0|2|
S2S0S38S35S5A1M0G0A2S3aG0G0SbVam;A1S8Vam;A1A4S3aG0G0S3bS5A1M1G1A4A3A1S2S0G0S46Vsr;S9Vam;A1A2S36S5Vg;A2A3A1S2S0S4eS12Vam;A1Z0A3A1F_;F_;").
  Proof using HR2g. intros H1 H2. apply HR2g; [exact H1|]. unfold s. rewrite active_hd_zomb. exact H2. Qed.
  Lemma mHok_r : ltac2:(tb__ "0|0|
S0S37S14Vsr;Vg;Vam;A3S40A3"). Proof using Hok. unfold s in Hok. rewrite okay_to_free_zomb in Hok. exact Hok. Qed.
  Lemma MTr q : ltac2:(tb__ "0|0|
S0S37S45Vq;VX;A2S39A3S0S35S6A1S44Vsr;Vq;A2S44Vs;Vq;A2A3F_;"). Proof using . intros B. unfold s. rewrite (MT_zomb_notX X sr q B). reflexivity. Qed.
  Lemma dq_r : ltac2:(tb__ "0|0|
S0S7S53Vs;Vg;Vam;A3S4bVX;S53Vsr;Vg;Vam;A3A2A3"). Proof using HnU HpU Hu. unfold s. apply dq_post_zomb; [exact mgX | exact mnX | exact mpX]. Qed.
  Lemma mHlinks_r : ltac2:(tb__ "0|2|
S5S0S35S5A1M0S8Vam;A1S36S5R1A2A3S2S0S5R2Vg;A3A1S3S5S5S3S6S6S3S6S6S1S0G0SbVam;A1S36S5R3A2A3S1S2S0S5R3Vg;A3A1S1S0S35S6A1M1S44Vsr;R3A2S36S6R2A2A3S0G1S44S5fR3S33R2S3fG0G0S17R2A1A3S36S5R6A2A3Vsr;A3R6A2S36S6R1A2A3A2A2A2Lxn;A2Lxp;A2Lp;A2F_;F_;Fn;").
  Proof using Hlinks HnU HpU.
    intros n En Hng. destruct (Hlinks n En Hng) as (p & xp & xn & Ep & Hpg & Mp & Mn). exists p, xp, xn.
    split; [exact Ep|]. split; [exact Hpg|]. split; [rewrite (MTr p (mpX p Ep)); exact Mp|].
    rewrite <- (MT_zomb_notX X _ n (mnX n En)), <- (upd_meta_zomb X sr p _ (mpX p Ep)). exact Mn.
  Qed.
  Lemma mHnU_r : ltac2:(tb__ "0|0|
S5S0S35S5A1S8Vam;A1S36S5R1A2A3S3ScScS0S35S6A1S44Vsr;R3A2S36S6SaR1A1A2A3Lan;A2F_;Fn;").
  Proof using HnU. intros n En. destruct (HnU n En) as [an M]. exists an. rewrite (MTr n (mnX n En)). exact M. Qed.
  Lemma mHpU_r : ltac2:(tb__ "0|0|
S5S0S35S5A1SbVam;A1S36S5R1A2A3S3ScScS0S35S6A1S44Vsr;R3A2S36S6SaR1A1A2A3Lap;A2F_;Fp;").
  Proof using HpU. intros p Ep. destruct (HpU p Ep) as [ap M]. exists ap. rewrite (MTr p (mpX p Ep)). exact M. Qed.
  Lemma mHact_r : ltac2:(tb__ "0|1|
S5ScS0S35S5A1M0S8Vam;A1S36S5R2A2A3S2S0S5R3Vg;A3A1S0G0S46Vsr;S9Vam;A1A2S36S5Vg;A2A3S0S35S6A1S44S53Vsr;Vg;Vam;A3R5A2S36S6SaR4A1A2A3S0S4eS1fR5A1Z0A3F_;F_;F_;F_;Fan;Fn;").
  Proof using Hact HnU HpU Hu.
    intros n an En Hng Hhd M. apply (Hact n an En Hng); [unfold s; rewrite active_hd_zomb; exact Hhd|].
    rewrite dq_r, (MT_zomb_notX X _ n (mnX n En)). exact M.
  Qed.
  Lemma mHactU_r : ltac2:(tb__ "0|1|
S5S0S35S5A1M0S8Vam;A1S36S5R1A2A3S2S0S5R2Vg;A3A1S0G0S46Vsr;S9Vam;A1A2S36S5Vg;A2A3S3ScScS0S35S6A1S44S53Vsr;Vg;Vam;A3R5A2S36S6SaR1A1A2A3Lan;A2F_;F_;F_;Fn;").
  Proof using HactU HnU HpU Hu.
    intros n En Hng Hhd. destruct (HactU n En Hng ltac:(unfold s; rewrite active_hd_zomb; exact Hhd)) as [an M]. exists an.
    rewrite dq_r, (MT_zomb_notX X _ n (mnX n En)) in M. exact M.
  Qed.
  Lemma mfmX fm : ltac2:(tb__ "0|0|
S0S35S5A1SeVsr;A1S36S5Vfm;A2A3S0S37S45Vfm;VX;A2S39A3F_;").
  Proof using Hfree_ringX.
    intros Hfh. destruct (Hfree_ringX fm ltac:(unfold s; rewrite st_free_meta_head_zomb; exact Hfh)) as (_ & hp & nx & pr2 & nx2 & M & _).
    apply (MT_virt_notX X sr fm _ M). discriminate.
  Qed.
  Lemma mHfree_ring_r : ltac2:(tb__ "0|2|
S5S0S35S5A1M0SeVsr;A1S36S5R1A2A3S1S2S0S5R2Vg;A3A1S3S5S5S3G0G0S3G0G0S3G0G0S1S0S35S6A1M1S44Vsr;R6A2S36S6SdS36S5R4A2R3A2A2A3S1S2S0S5R4Vg;A3A1S0G1S44Vsr;R4A2S36S6SdR2R1A2A2A3A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2A2F_;Ffm;").
  Proof using Hfree_ringX.
    intros fm Hfh. pose proof (mfmX fm Hfh) as B.
    destruct (Hfree_ringX fm ltac:(unfold s; rewrite st_free_meta_head_zomb; exact Hfh)) as (NE & hp & nx & pr2 & nx2 & M & NEh & Mh & Bh).
    split; [exact NE|]. exists hp, nx, pr2, nx2. rewrite (MTr fm B), (MTr hp Bh). auto.
  Qed.

  Theorem fgm_real fuel : ltac2:(tb__ "0|3|
S1S0S10S7S38S35S38S3eS4eA2A1M0S7A2M1A2S11S3dVfuel;A1Vg;Vi;Vsr;A4SfS7G1S3aG0S7S5cVam;A1S55Vsr;Vg;Vam;A3M2A4A3A3S0S7S4bVX;G2A2S55Vs;Vg;Vam;A3A3A2").
  Proof using HIr HR2g Hact HactU Hall Hfree_ringX Hlinks Hml HnU Hok HpU Hsc Hu.
    split.
    - exact (fgm_eq X U sr g am i HIr mHu_r mHR2g_r Hall Hsc Hml mHok_r mHlinks_r mHnU_r mHpU_r mHact_r mHactU_r mHfree_ring_r fuel).
    - unfold fgm_post, s. rewrite (fgm_s5_zomb X sr g am mgX mnX mpX). symmetry. apply fq_post_zomb; [exact mgX|].
      intros fm Hfh. rewrite (head_fgm5 sr g am mHR2g_r mHlinks_r mHnU_r mHpU_r mHact_r mHactU_r) in Hfh. pose proof (mfmX fm Hfh) as B. split; [exact B|].
      destruct (mHfree_ring_r fm Hfh) as (NE & hp & nx & pr2 & nx2 & M & NEh & Mh).
      destruct (Hfree_ringX fm ltac:(unfold s; rewrite st_free_meta_head_zomb; exact Hfh)) as (_ & hp' & nx' & _ & _ & M' & _ & _ & Bh').
      rewrite <- (MTr fm B), M in M'. injection M' as <- <-.
      intros xf hp0 Mf El.
      assert (NEn : forall n, am_next am = Some n -> fm <> n) by (intros n En ->; destruct (mHnU_r n En) as [an Mn]; rewrite Mn in M; discriminate).
      assert (NEp : forall p, am_prev am = Some p -> fm <> p) by (intros p Ep ->; destruct (mHpU_r p Ep) as [ap Mp]; rewrite Mp in M; discriminate).
      rewrite (MT_fgm5_other sr g am mHR2g_r mHlinks_r mHnU_r mHpU_r mHact_r mHactU_r fm NE NEn NEp), M in Mf. injection Mf as <-. cbn in El. injection El as <-. exact Bh'.
  Qed.
  Theorem fgm_nf_real fuel : ltac2:(tb__ "0|0|
S64S65S9Vam;A1A1S3dVfuel;A1A2S66VX;VU;Vsr;S3aS35S38S3eS4eA2A1S7S5cVam;A1S55Vsr;Vg;Vam;A3A4A4F_;").
  Proof using HIr HR2g HU Hact HactU Hall Hfree_ringX Hlinks Hml HnU Hok HpU Hsc Hu. exact (fgm_nf_post X U sr g am i HIr mHu_r HU mHR2g_r Hall Hsc Hml mHok_r mHlinks_r mHnU_r mHpU_r mHact_r mHactU_r mHfree_ring_r fuel). Qed.
  Theorem fgm_X x : ltac2:(tb__ "0|0|
S4fS5Vx;VX;A3S0S35S6A1S44S55Vsr;Vg;Vam;A3Vx;A2S44Vsr;Vx;A2A3F_;").
  Proof using HR2g Hact HactU Hfree_ringX Hlinks HnU HpU Hu.
    intros Hx. assert (Bx : memb x X = true) by (apply memb_In; exact Hx).
    assert (NE : forall q, memb q X = false -> q <> x) by (intros q Hq ->; rewrite Bx in Hq; discriminate).
    unfold fgm_post. rewrite (fq_post_X X _ g x mgX).
    - apply (MT_fgm5_other sr g am mHR2g_r mHlinks_r mHnU_r mHpU_r mHact_r mHactU_r x).
      + exact (fun E => NE g mgX (eq_sym E)).
      + intros n En. exact (fun E => NE n (mnX n En) (eq_sym E)).
      + intros p Ep. exact (fun E => NE p (mpX p Ep) (eq_sym E)).
    - intros fm Hfh. rewrite (head_fgm5 sr g am mHR2g_r mHlinks_r mHnU_r mHpU_r mHact_r mHactU_r) in Hfh. pose proof (mfmX fm Hfh) as B. split; [exact B|].
      destruct (mHfree_ring_r fm Hfh) as (NEg & hp & nx & pr2 & nx2 & M & NEh & Mh).
      destruct (Hfree_ringX fm ltac:(unfold s; rewrite st_free_meta_head_zomb; exact Hfh)) as (_ & hp' & nx' & _ & _ & M' & _ & _ & Bh').
      rewrite <- (MTr fm B), M in M'. injection M' as <- <-.
      intros xf hp0 Mf El.
      assert (NEn : forall n, am_next am = Some n -> fm <> n) by (intros n En ->; destruct (mHnU_r n En) as [an Mn]; rewrite Mn in M; discriminate).
      assert (NEp : forall p, am_prev am = Some p -> fm <> p) by (intros p Ep ->; destruct (mHpU_r p Ep) as [ap Mp]; rewrite Mp in M; discriminate).
      rewrite (MT_fgm5_other sr g am mHR2g_r mHlinks_r mHnU_r mHpU_r mHact_r mHactU_r fm NEg NEn NEp), M in Mf. injection Mf as <-. cbn in El. injection El as <-. exact Bh'.
    - exact Bx.
  Qed.
End RealMapped.
