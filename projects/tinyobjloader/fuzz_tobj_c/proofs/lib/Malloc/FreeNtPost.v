(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "astate"; "MUsed"; "st_free_meta_head"; "am_sc"; "MFree"; "am_next"; "am_set_links"; "itree"; "IRet"; "ameta"; "am_prev"; "bind"; "nontrivial_free"; "st_seq"; "am_freed"; "am_last"; "st_unmap_seq"; "bit"; "with_links"; "am_maplen"; "am_mem"; "links_of"; "osptr_eqb"; "set_unmap_seq"; "MRaw"; "am_aidx"; "am_set_freed"; "ret"; "set_seq"; "set_usage"; "zset"; "HActive"; "HFreeMeta"; "get_head"; "ones"; "set_free_meta_head"; "sptr_eqb"; "M"; "am_avail"; "bounce_idx"; "dequeue"; "getm"; "massert"; "okay_to_free"; "prid"; "queue"; "setm"; "slot_start"; "st_active"; "st_usage"; "activate_group"; "class_size"; "record_seq"; "set_head"; "set_usage_of"; "setslot"; "step_seq"; "stride_of"; "usage_of"; "@Corelib.Init.Logic"; "eq"; "not"; "and"; "ex"; "@Corelib.Init.Datatypes"; "option"; "Some"; "prod"; "unit"; "pair"; "None"; "bool"; "nat"; "S"; "tt"; "list"; "app"; "fst"; "snd"; "andb"; "length"; "cons"; "false"; "negb"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "active_hd"; "keys"; "loc"; "Inv"; "usedX"; "CTX_active"; "LCtx"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.FreeGroupDirect"; "fgd_post"; "fgd_s2"; "fgd_res"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost"; "or_post"; "shape_kept"; "seq_post"; "q0_mid"; "nmask"; "fq_post"; "q1_s3"; "q2_s1"; "q2_s2"; "q2_s3"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lor"; "eqb"; "lt"; "mul"; "ltb"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "set_hd"; "meta_locs"; "delta"; "same_shape"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.ElseBranch"; "nmask"; "or_post"; "else_tail"; "q0_mid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.FreeGroupMapped"; "dq_post"; "fgm_s1"; "fgm_s3"; "act_post"; "fgm_post"; "fgm_res"; "fgm_s5"; "fgm_s4"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree"; "fneed"; "nf_post"; "@Corelib.Lists.ListDef"; "repeat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.FreeGroupDirect.Ring"; "fm_next'"; "fgd_t3"; "fgd_t4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "hosts_ok"; "reach_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.ElseBranch.WithHead"; "q1_s1"; "q1_s3"; "q2_s1"; "q2_s2"; "q2_s3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost"; "am_activate"; "@Stdlib.Lists.List"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfArith MallocWfInv MallocWfFrame MallocWfRings
  MallocWfRingOps MallocWfFree ImageUpd ImageDelta TryAvailPost NestTier.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition shape_kept (s s' : astate) : Prop := ltac2:(tb__ "0|2|
S0SbS3dS41S1A1M0S56Vs';R2A2S42S1S3R1A1A2M1A3S40SbSbS3fS3dG0S56Vs;R4A2G1A3S3fS3dS0S16R3A1S16R1A1A3S3fS3dS5eS15R3A1S15R1A1A3S3fS3dS5eS11R3A1S11R1A1A3S3fS3dS5eS5R3A1S5R1A1A3S3dS5eS1bR3A1S1bR1A1A3A2A2A2A2A2Lam;A2F_;Fam';Fg;").

Lemma slot_start_fields am am' i : ltac2:(tb__ "0|0|
S3dS0S16Vam';A1S16Vam;A1A3S3dS5eS15Vam';A1S15Vam;A1A3S3dS5eS11Vam';A1S11Vam;A1A3S3dS5eS5Vam';A1S5Vam;A1A3S3dS0S31Vam';Vi;A2S31Vam;Vi;A2A3F_;F_;F_;F_;").
Proof. intros E1 E2 E3 E4. unfold slot_start, stride_of. rewrite E1, E2, E3, E4. reflexivity. Qed.

Lemma hosts_ok_kept s s' : ltac2:(tb__ "0|0|
S64Vs;Vs';A2S8cVs;A1S8cVs';A1F_;F_;").
Proof.
  intros K H g am g' am' i' Hg Hml Hg' Hi' Hmem.
  destruct (K g am Hg) as (a & Ha & E1 & E2 & E3 & E4 & _).
  destruct (K g' am' Hg') as (a' & Ha' & F1 & F2 & F3 & F4 & _).
  rewrite F4. apply (H g a g' a' i' Ha ltac:(congruence) Ha' ltac:(lia)).
  rewrite <- E1, Hmem. apply slot_start_fields; assumption.
Qed.

Lemma reach_ok_kept s s' : ltac2:(tb__ "0|0|
S64Vs;Vs';A2S8dVs;A1S8dVs';A1F_;F_;").
Proof.
  intros K H. apply (reach_ok_mono s s'); [|exact H].
  intros g am' Hg. destruct (K g am' Hg) as (am & Ha & E1 & E2 & E3 & E4 & E5). exists am. split; [exact Ha|].
  unfold reach_fields. rewrite E1, E2, E3, E4, E5. split; [reflexivity | lia].
Qed.

Lemma shape_kept_refl s : shape_kept s s.
Proof. intros g am H. exists am. auto 7. Qed.

Lemma shape_kept_trans s1 s2 s3 : ltac2:(tb__ "0|0|
S64Vs1;Vs2;A2S64Vs2;Vs3;A2S64Vs1;Vs3;A2F_;F_;").
Proof.
  intros A B g am H. destruct (B g am H) as (a2 & H2 & E1 & E2 & E3 & E4 & E5).
  destruct (A g a2 H2) as (a1 & H1 & F1 & F2 & F3 & F4 & F5). exists a1. split; [exact H1|]. repeat split; congruence.
Qed.

Lemma shape_kept_upd s g am am' : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs;Vg;A2S42S1S3Vam;A1A2A3S3fS78Vam;Vam';A2S3dS5eS1bVam';A1S1bVam;A1A3A2S64Vs;S5fVg;S3Vam';A1Vs;A3A2F_;F_;").
Proof.
  intros Hg [SH EA] q aq Hq. destruct (sptr_eq_dec q g) as [->|Hne].
  - rewrite MT_upd_same in Hq. injection Hq as <-. exists am. split; [exact Hg|].
    destruct SH as (E1 & E2 & E3 & E4 & E5). repeat split; congruence.
  - rewrite (MT_upd_other g _ s q Hne) in Hq. exists aq. auto 7.
Qed.

Lemma shape_kept_set_hd s sc v : ltac2:(tb__ "0|0|
S64Vs;S75Vsc;Vv;Vs;A3A2").
Proof. intros q aq Hq. rewrite MT_set_hd in Hq. exists aq. auto 7. Qed.

Lemma fneed_pos sc : (1 <= fneed sc)%nat.
Proof. unfold fneed. destruct (sc <? 48) eqn:E; [apply Z.ltb_lt in E|]; lia. Qed.

Section ElseBranch.
  Variables (X : list sptr) (U : Z -> Z) (s : astate) (g : sptr) (am : ameta) (i : Z).
  Hypothesis HI : ltac2:(tb__ "0|0|
S5aVX;S42S43S0S5eA2S45S0S5eVg;Vi;A4A2VU;Vs;A4").
  Hypothesis Hu : ltac2:(tb__ "0|0|
S5bVX;Vs;Vg;Vam;A4").
  Hypothesis HU : forall c, 0 <= U c.
  Hypothesis HR2g : ltac2:(tb__ "0|2|
S3eS3dS43S41S0A1M0G0A2S45G0G0ScVam;A1S7Vam;A1A4S45G0G0S46S0A1M1G1A4A3A1S3eS3dG0S57Vs;S5Vam;A1A2S42S0Vg;A2A3A1S3eS3dS5eS10Vam;A1Z0A3A1F_;F_;").

  Definition nmask : Z := ltac2:(tb__ "0|0|
S6fS10Vam;A1S28Vam;A1A2").

  Hypothesis Helse : ltac2:(tb__ "0|0|
S3dS47S4fS70S6eS79S13Vi;A1A2S24S11Vam;A1A1A2S2dVs;Vg;Vam;A3A2S52A3").

  Lemma HMg : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs;Vg;A2S42S1S3Vam;A1A2A3"). Proof using Hu. exact (proj1 (usedX_MT _ _ _ _ Hu)). Qed.
  Lemma NDk : List.NoDup (keys s). Proof using HI. exact (proj1 (inv_keys HI)). Qed.
  Lemma else_sc : ltac2:(tb__ "0|1|
S3fS3fS6dZ0S5Vam;A1M0A2S71G0Z30A2A2S6dS35G0A1S3bVam;A1A2A2").
  Proof using HI Helse Hu. exact (else_branch_facts X U s g i am HI Hu Helse). Qed.

  Definition else_tail : M (option (nat * Z)) := ltac2:(tb__ "0|7|
SdS44S41S43S48S5eA2M0A1M1S47S27S44A1L_;M2S70S79Z0A2SdS44S44S2cS73S5Vam;A1M3Z30A2Z6A2S44SdS41S0A1M4S44S23S21G3A1M5A1G4G2S18R1S42S0Vg;A2A2S1dS44S4aA2M6S2fG5Vg;A2X47x2Lhd;A4L_;A4G6X47x2S44SdSbG1S2bVg;A1SbSdS44G1S30Vg;S1cS6fS10R1A1S13Vi;A1A2R1A2A2S44S1dG1S46G0A1A2L_;A4Lam0;A4L_;A4").

  Lemma else_prefix fuel : ltac2:(tb__ "0|0|
S3dS9S2S43S41S43S48S5eA2A1S2A2A2SeS49Vfuel;A1Vg;Vi;Vs;A4S7bVs;A1A3").
  Proof using Helse Hu.
    pose proof HMg as Mg.
    cbn fix beta iota delta [nontrivial_free].
    rewrite (bind_eq _ _ s am s (getm_eq s g am Mg)). rewrite (bind_eq _ _ s s s (get_eq s)). cbn zeta.
    fold nmask. rewrite Helse. reflexivity.
  Qed.

  Definition or_post (t : astate) (a : ameta) : astate := ltac2:(tb__ "0|0|
S5fVg;S3S1cS6fS10Va;A1S13Vi;A1A2Va;A2A1Vt;A3").

  Lemma or_tail_eq t a : ltac2:(tb__ "0|4|
S3dS41S1A1S56Vt;Vg;A2S42S1S3Va;A1A2A3S3dS9S2S43S41S43S48S5eA2M0A1M1S2A2M2A2SdSbG1S2bVg;A1SbSdS44G1S30Vg;S1cS6fS10R1A1S13Vi;A1A2R1A2A2S44S1dG1S46G0A1M3A2L_;A4Lam0;Vt;A5SaS2G2S45G1S2G3S7aVt;Va;A2A4A3A3F_;").
  Proof using .
    intros Ht. rewrite (bind_eq _ _ t a t (getm_eq t g a Ht)). rewrite (bind_eq _ _ t tt _ (setm_eq t g _)). reflexivity.
  Qed.

  Theorem or_eq fuel : ltac2:(tb__ "0|3|
S3eS3dS5eS79Z0A3A1S3dS9S2S43S41S43S48S5eA2M0A1M1S2A2M2A2SeS49Vfuel;A1Vg;Vi;Vs;A4SaS2G2S45G1S2S46G0A1S7aVs;Vam;A2A4A3A3F_;").
  Proof using Helse Hu.
    intros Hm. rewrite else_prefix. unfold else_tail. rewrite (proj2 (Z.eqb_neq _ _) Hm).
    rewrite (bind_eq _ _ s tt s (ret_eq tt s)). apply or_tail_eq. exact HMg.
  Qed.

  Theorem qg_eq fuel : ltac2:(tb__ "0|3|
S3dS5eS79Z0A3S3dS41S0A1S57Vs;S5Vam;A1A2S42S0Vg;A2A3S3dS9S2S43S41S43S48S5eA2M0A1M1S2A2M2A2SeS49Vfuel;A1Vg;Vi;Vs;A4SaS2G2S45G1S2S46G0A1S7aVs;Vam;A2A4A3A3F_;F_;").
  Proof using HI Helse Hu.
    intros Hm Hhd. pose proof else_sc as [Hsc _]. rewrite else_prefix. unfold else_tail. rewrite (proj2 (Z.eqb_eq _ _) Hm).
    rewrite (bind_eq _ _ s tt s).
    2:{ rewrite (bind_eq _ _ s tt s) by (apply massert_true_eq; apply Z.ltb_lt; lia).
        rewrite (bind_eq _ _ s _ s (get_head_eq s (am_sc am))). rewrite Hhd. cbn [osptr_eqb]. rewrite sptr_eqb_refl. reflexivity. }
    apply or_tail_eq. exact HMg.
  Qed.

  Definition q0_mid : astate := ltac2:(tb__ "0|1|
S75S5Vam;A1S42S0Vg;A2M0S5fVg;S3S8G0G0Vam;A3A1Vs;A3A3").
  Theorem q0_eq fuel : ltac2:(tb__ "0|6|
S3dS5eS79Z0A3S3dS41S0A1M0S57Vs;S5Vam;A1A2S46S0A1M1A3S3dG0ScVam;A1G1A3S3dG0S7Vam;A1G1A3S3dS9S2S43S41S43S48S5eA2M2A1M3S2A2M4A2SeS49Vfuel;A1Vg;Vi;Vs;A4SaS2G4S45G3S2S46G2A1S7aS7cS8S42S0Vg;A2M5G5Vam;A3A2A4A3A3F_;F_;F_;F_;").
  Proof using HI Helse Hu.
    intros Hm Hhd Hp Hn. pose proof else_sc as [Hsc _]. pose proof HMg as Mg. rewrite else_prefix. unfold else_tail. rewrite (proj2 (Z.eqb_eq _ _) Hm).
    rewrite (bind_eq _ _ s tt q0_mid).
    2:{ rewrite (bind_eq _ _ s tt s) by (apply massert_true_eq; apply Z.ltb_lt; lia).
        rewrite (bind_eq _ _ s _ s (get_head_eq s (am_sc am))). rewrite Hhd. cbn [osptr_eqb].
        unfold queue. rewrite (bind_eq _ _ s _ s (get_links_eq s g _ Mg)). cbn [links_of fst snd]. rewrite Hp, Hn. cbn [osptr_eqb andb].
        rewrite (bind_eq _ _ s tt s) by (apply massert_true_eq; reflexivity).
        rewrite (bind_eq _ _ s _ s (get_head_eq s (am_sc am))). rewrite Hhd.
        rewrite (bind_eq _ _ s tt _ (set_links_eq s g _ (Some g) (Some g) Mg)). cbn [with_links].
        apply set_head_eq. }
    apply or_tail_eq. unfold q0_mid. rewrite MT_set_hd. apply MT_upd_same.
  Qed.

  Section WithHead.
    Variables (h : sptr) (ah : ameta).
    Hypothesis Hhd : ltac2:(tb__ "0|0|
S3dS41S0A1S57Vs;S5Vam;A1A2S42S0Vh;A2A3").
    Hypothesis Hhg : h <> g.
    Hypothesis Mh : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs;Vh;A2S42S1S3Vah;A1A2A3").
    Hypothesis Hp : am_prev am = None.
    Hypothesis Hn : am_next am = None.

    Definition q1_s1 : astate := ltac2:(tb__ "0|1|
S5fVg;S3S8S42S0Vh;A2M0G0Vam;A3A1Vs;A3").
    Definition q1_s3 : astate := ltac2:(tb__ "0|1|
S5fVh;S3S8S42S0Vg;A2M0G0Vah;A3A1S8eA3").
    Theorem q1_eq fuel : ltac2:(tb__ "0|4|
S3dS5eS79Z0A3S3dS41S0A1ScVah;A1S42S0Vh;A2M0A3S3dS9S2S43S41S43S48S5eA2M1A1M2S2A2M3A2SeS49Vfuel;A1Vg;Vi;Vs;A4SaS2G3S45G2S2S46G1A1S7aS8fS8G0G0Vam;A3A2A4A3A3F_;F_;").
    Proof using HI Helse Hhd Hhg Hn Hp Hu Mh.
      intros Hm Hhp. pose proof else_sc as [Hsc _]. pose proof HMg as Mg. rewrite else_prefix. unfold else_tail. rewrite (proj2 (Z.eqb_eq _ _) Hm).
      assert (M1h : MT q1_s1 h = Some (MUsed ah)) by (unfold q1_s1; rewrite (MT_upd_other g _ s h Hhg); exact Mh).
      rewrite (bind_eq _ _ s tt q1_s3).
      2:{ rewrite (bind_eq _ _ s tt s) by (apply massert_true_eq; apply Z.ltb_lt; lia).
          rewrite (bind_eq _ _ s _ s (get_head_eq s (am_sc am))). rewrite Hhd. cbn [osptr_eqb].
          rewrite (proj2 (sptr_eqb_neq h g) Hhg).
          unfold queue. rewrite (bind_eq _ _ s _ s (get_links_eq s g _ Mg)). cbn [links_of fst snd]. rewrite Hp, Hn. cbn [osptr_eqb andb].
          rewrite (bind_eq _ _ s tt s) by (apply massert_true_eq; reflexivity).
          rewrite (bind_eq _ _ s _ s (get_head_eq s (am_sc am))). rewrite Hhd.
          rewrite (bind_eq _ _ s _ s (get_links_eq s h _ Mh)). cbn [links_of fst]. rewrite Hhp.
          rewrite (bind_eq _ _ s tt _ (set_links_eq s g _ (Some h) (Some h) Mg)). cbn [with_links]. fold q1_s1.
          rewrite (bind_eq _ _ q1_s1 tt _ (set_next_eq q1_s1 h _ (Some g) M1h)). cbn [with_links links_of fst].
          rewrite (set_prev_eq _ h (MUsed (am_set_links (am_prev ah) (Some g) ah)) (Some g)) by apply MT_upd_same.
          cbn [with_links links_of snd am_next am_set_links]. rewrite upd_meta_twice. reflexivity. }
      apply or_tail_eq. unfold q1_s3. rewrite (MT_upd_other h _ _ g ltac:(intros E; exact (Hhg (eq_sym E)))). apply MT_upd_same.
    Qed.

    Variables (t : sptr) (at_ : ameta).
    Hypothesis Htg : t <> g.
    Hypothesis Hth : t <> h.
    Hypothesis Mt : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs;Vt;A2S42S1S3Vat_;A1A2A3").
    Definition q2_s1 : astate := ltac2:(tb__ "0|0|
S5fVg;S3S8S42S0Vt;A2S42S0Vh;A2Vam;A3A1Vs;A3").
    Definition q2_s2 : astate := ltac2:(tb__ "0|0|
S5fVt;S3S8ScVat_;A1S42S0Vg;A2Vat_;A3A1S90A3").
    Definition q2_s3 : astate := ltac2:(tb__ "0|0|
S5fVh;S3S8S42S0Vg;A2S7Vah;A1Vah;A3A1S91A3").
    Theorem q2_eq fuel : ltac2:(tb__ "0|4|
S3dS5eS79Z0A3S3dS41S0A1ScVah;A1S42S0Vt;A2M0A3S3dS9S2S43S41S43S48S5eA2M1A1M2S2A2M3A2SeS49Vfuel;A1Vg;Vi;Vs;A4SaS2G3S45G2S2S46G1A1S7aS92S8G0S42S0Vh;A2Vam;A3A2A4A3A3F_;F_;").
    Proof using HI Helse Hhd Hhg Hn Hp Htg Hth Hu Mh Mt.
      intros Hm Hhp. pose proof else_sc as [Hsc _]. pose proof HMg as Mg. rewrite else_prefix. unfold else_tail. rewrite (proj2 (Z.eqb_eq _ _) Hm).
      assert (M1t : MT q2_s1 t = Some (MUsed at_)) by (unfold q2_s1; rewrite (MT_upd_other g _ s t Htg); exact Mt).
      assert (M2h : MT q2_s2 h = Some (MUsed ah)).
      { unfold q2_s2, q2_s1. rewrite (MT_upd_other t _ _ h ltac:(intros E; exact (Hth (eq_sym E)))). rewrite (MT_upd_other g _ s h Hhg). exact Mh. }
      rewrite (bind_eq _ _ s tt q2_s3).
      2:{ rewrite (bind_eq _ _ s tt s) by (apply massert_true_eq; apply Z.ltb_lt; lia).
          rewrite (bind_eq _ _ s _ s (get_head_eq s (am_sc am))). rewrite Hhd. cbn [osptr_eqb].
          rewrite (proj2 (sptr_eqb_neq h g) Hhg).
          unfold queue. rewrite (bind_eq _ _ s _ s (get_links_eq s g _ Mg)). cbn [links_of fst snd]. rewrite Hp, Hn. cbn [osptr_eqb andb].
          rewrite (bind_eq _ _ s tt s) by (apply massert_true_eq; reflexivity).
          rewrite (bind_eq _ _ s _ s (get_head_eq s (am_sc am))). rewrite Hhd.
          rewrite (bind_eq _ _ s _ s (get_links_eq s h _ Mh)). cbn [links_of fst]. rewrite Hhp.
          rewrite (bind_eq _ _ s tt _ (set_links_eq s g _ (Some t) (Some h) Mg)). cbn [with_links]. fold q2_s1.
          rewrite (bind_eq _ _ q2_s1 tt _ (set_next_eq q2_s1 t _ (Some g) M1t)). cbn [with_links links_of fst]. fold q2_s2.
          rewrite (set_prev_eq q2_s2 h _ (Some g) M2h). cbn [with_links links_of snd]. reflexivity. }
      apply or_tail_eq. unfold q2_s3. rewrite (MT_upd_other h _ _ g ltac:(intros E; exact (Hhg (eq_sym E)))).
      unfold q2_s2. rewrite (MT_upd_other t _ _ g ltac:(intros E; exact (Htg (eq_sym E)))). apply MT_upd_same.
    Qed.
  End WithHead.

  Theorem else_nf_post fuel r : ltac2:(tb__ "0|2|
S3dS9S2S43S41S43S48S5eA2A1S2A2M0A2SeS49Vfuel;A1M1Vg;Vi;Vs;A4SaS2G0Vr;A3A3S85S86S5Vam;A1A1G1A2S87VX;VU;Vs;Vr;A4F_;F_;").
  Proof using HI HR2g HU Hu.
    intros E Hf.
    pose proof (nontrivial_free_spec (S fuel) X U s g i am (nf_post X U s) HI Hu HU HR2g Hf (fun r Hr => Hr)) as T.
    rewrite E in T. exact T.
  Qed.
End ElseBranch.

Section ElsePosts.
  Variables (s : astate) (g : sptr) (am : ameta) (i : Z).
  Hypothesis ND : List.NoDup (keys s).
  Hypothesis Mg : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs;Vg;A2S42S1S3Vam;A1A2A3").

  Lemma keys_or t a : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vt;Vg;A2S42S1S3Va;A1A2A3S3dS4bS0A1S58S63Vg;Vi;Vt;Va;A4A1S58Vt;A1A3F_;").
  Proof using . intros Mt. unfold or_post. apply keys_upd_In. eapply MT_Some_In_keys. exact Mt. Qed.

  Lemma delta_or t a : ltac2:(tb__ "0|0|
S94S0S58Vt;A1A2S3dS41S1A1S56Vt;Vg;A2S42S1S3Va;A1A2A3S77Vt;S63Vg;Vi;Vt;Va;A4S76Vg;A1A3F_;F_;").
  Proof using . intros NDt Mt. unfold or_post. apply (delta_su_keep t g a); [exact NDt | exact Mt | apply same_shape_freed | reflexivity]. Qed.

  Lemma shape_or t a : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vt;Vg;A2S42S1S3Va;A1A2A3S64Vt;S63Vg;Vi;Vt;Va;A4A2F_;").
  Proof using . intros Mt. unfold or_post. apply (shape_kept_upd t g a); [exact Mt | split; [apply same_shape_freed | reflexivity]]. Qed.

  Lemma MT_or_g t a : ltac2:(tb__ "0|0|
S3dS41S1A1S56S63Vg;Vi;Vt;Va;A4Vg;A2S42S1S3S1cS6fS10Va;A1S13Vi;A1A2Va;A2A1A2A3").
  Proof using . unfold or_post. apply MT_upd_same. Qed.
  Lemma MT_or_other t a q : ltac2:(tb__ "0|0|
S3eS3dS0Vq;Vg;A3A1S3dS41S1A1S56S63Vg;Vi;Vt;Va;A4Vq;A2S56Vt;Vq;A2A3F_;").
  Proof using . intros Hq. unfold or_post. apply MT_upd_other. exact Hq. Qed.
  Lemma hd_or t a c : ltac2:(tb__ "0|0|
S3dS41S0A1S57S63Vg;Vi;Vt;Va;A4Vc;A2S57Vt;Vc;A2A3").
  Proof using . unfold or_post. apply active_hd_upd_meta. Qed.

  Let am0 : ameta := ltac2:(tb__ "0|1|
S8S42S0Vg;A2M0G0Vam;A3").
  Lemma MT_q0_g : ltac2:(tb__ "0|0|
S3dS41S1A1S56S66Vs;Vg;Vam;A3Vg;A2S42S1S3Vam0;A1A2A3").
  Proof using . unfold q0_mid. rewrite MT_set_hd. apply MT_upd_same. Qed.
  Lemma MT_q0_other q : ltac2:(tb__ "0|0|
S3eS3dS0Vq;Vg;A3A1S3dS41S1A1S56S66Vs;Vg;Vam;A3Vq;A2S56Vs;Vq;A2A3F_;").
  Proof using . intros Hq. unfold q0_mid. rewrite MT_set_hd. apply MT_upd_other. exact Hq. Qed.
  Lemma keys_q0 : ltac2:(tb__ "0|0|
S3dS4bS0A1S58S66Vs;Vg;Vam;A3A1S58Vs;A1A3").
  Proof using Mg. unfold q0_mid, set_hd, keys. cbn [st_metas]. fold (keys (upd_meta g (MUsed am0) s)). apply keys_upd_In. eapply MT_Some_In_keys. exact Mg. Qed.
  Lemma hd_q0 : ltac2:(tb__ "0|2|
S6dZ0S5Vam;A1M0A2S3dS48S50S41S0A1M1S32Vs;A1A2U30A3S71G0Z30A2S3dG1S57S66Vs;Vg;Vam;A3G0A2S42S0Vg;A2A3F_;F_;F_;").
  Proof using .
    intros H0 Hlen H48. unfold q0_mid, active_hd, set_hd. cbn [st_active set_active upd_meta set_metas]. rewrite nth_lupd, Nat.eqb_refl, Hlen.
    replace (Nat.ltb (Z.to_nat (am_sc am)) 48) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
  Qed.
  Lemma hd_q0_other c : ltac2:(tb__ "0|2|
S6dZ0M0Vc;A2S3eS3dS5eVc;S5Vam;A1M1A3A1S6dG0G1A2S3dS41S0A1S57S66Vs;Vg;Vam;A3Vc;A2S57Vs;Vc;A2A3F_;F_;F_;").
  Proof using .
    intros Hc Hne H0. unfold q0_mid, active_hd, set_hd. cbn [st_active set_active upd_meta set_metas]. rewrite nth_lupd.
    replace (Nat.eqb (Z.to_nat c) (Z.to_nat (am_sc am))) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
  Qed.
  Lemma delta_q0 : ltac2:(tb__ "0|2|
S6dZ0S5Vam;A1M0A2S77Vs;S63Vg;Vi;S66Vs;Vg;Vam;A3Vam0;A4S4cS59S4cS59S76Vg;A1M1S51S59S5dS6eS5cS72Z8G0A2A2A1S54S59A1A3A3G1A3A3F_;").
  Proof using Mg ND.
    intros Hsc. eapply delta_trans; [| apply delta_or; [rewrite keys_q0; exact ND | apply MT_q0_g]].
    unfold q0_mid. eapply delta_trans; [| apply delta_sh; exact Hsc].
    apply (delta_su_keep s g am am0 ND Mg); [apply same_shape_links | reflexivity].
  Qed.
  Lemma shape_q0 : ltac2:(tb__ "0|0|
S64Vs;S63Vg;Vi;S66Vs;Vg;Vam;A3Vam0;A4A2").
  Proof using Mg.
    eapply shape_kept_trans; [| apply shape_or; apply MT_q0_g].
    unfold q0_mid. eapply shape_kept_trans; [apply (shape_kept_upd s g am am0 Mg); (split; [apply same_shape_links | reflexivity]) | apply shape_kept_set_hd].
  Qed.

  Section Q1.
    Variables (h : sptr) (ah : ameta).
    Hypothesis Hhg : h <> g.
    Hypothesis Mh : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs;Vh;A2S42S1S3Vah;A1A2A3").
    Let am1 : ameta := ltac2:(tb__ "0|1|
S8S42S0Vh;A2M0G0Vam;A3").
    Let ah1 : ameta := ltac2:(tb__ "0|1|
S8S42S0Vg;A2M0G0Vah;A3").
    Let s3 : astate := ltac2:(tb__ "0|0|
S69Vs;Vg;Vam;Vh;Vah;A5").
    Lemma MT_q1_g : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs3;Vg;A2S42S1S3Vam1;A1A2A3").
    Proof using Hhg ah am s. unfold s3, q1_s3, q1_s1. rewrite (MT_upd_other h _ _ g ltac:(intros E; exact (Hhg (eq_sym E)))). apply MT_upd_same. Qed.
    Lemma MT_q1_h : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs3;Vh;A2S42S1S3Vah1;A1A2A3").
    Proof using ah am g s. unfold s3, q1_s3. apply MT_upd_same. Qed.
    Lemma MT_q1_other q : ltac2:(tb__ "0|0|
S3eS3dS0Vq;Vg;A3A1S3eS3dS0Vq;Vh;A3A1S3dS41S1A1S56Vs3;Vq;A2S56Vs;Vq;A2A3F_;F_;").
    Proof using ah am. intros Hq1 Hq2. unfold s3, q1_s3, q1_s1. rewrite (MT_upd_other h _ _ q Hq2). apply MT_upd_other. exact Hq1. Qed.
    Lemma keys_q1 : ltac2:(tb__ "0|0|
S3dS4bS0A1S58Vs3;A1S58Vs;A1A3").
    Proof using Mg Mh.
      unfold s3, q1_s3, q1_s1. rewrite keys_upd_In; [apply keys_upd_In; eapply MT_Some_In_keys; exact Mg|].
      rewrite keys_upd_In; [|eapply MT_Some_In_keys; exact Mg]. eapply MT_Some_In_keys. exact Mh.
    Qed.
    Lemma hd_q1 c : ltac2:(tb__ "0|0|
S3dS41S0A1S57Vs3;Vc;A2S57Vs;Vc;A2A3").
    Proof using ah am g h. unfold s3, q1_s3, q1_s1. rewrite !active_hd_upd_meta. reflexivity. Qed.
    Lemma delta_q1 : ltac2:(tb__ "0|1|
S77Vs;S63Vg;Vi;Vs3;Vam1;A4S4cS59S4cS59S76Vg;A1M0S76Vh;A1A3G0A3A3").
    Proof using Hhg Mg Mh ND ah1.
      assert (ND1 : List.NoDup (keys (q1_s1 s g am h))) by (unfold q1_s1; rewrite keys_upd_In; [exact ND | eapply MT_Some_In_keys; exact Mg]).
      assert (M1h : MT (q1_s1 s g am h) h = Some (MUsed ah)) by (unfold q1_s1; rewrite (MT_upd_other g _ s h Hhg); exact Mh).
      eapply delta_trans; [| apply delta_or; [rewrite keys_q1; exact ND | apply MT_q1_g]].
      unfold s3, q1_s3. eapply delta_trans.
      - unfold q1_s1. apply (delta_su_keep s g am am1 ND Mg); [apply same_shape_links | reflexivity].
      - apply (delta_su_keep _ h ah ah1 ND1 M1h); [apply same_shape_links | reflexivity].
    Qed.
    Lemma shape_q1 : ltac2:(tb__ "0|0|
S64Vs;S63Vg;Vi;Vs3;Vam1;A4A2").
    Proof using Hhg Mg Mh ah1.
      eapply shape_kept_trans; [| apply shape_or; apply MT_q1_g].
      unfold s3, q1_s3. eapply shape_kept_trans; [unfold q1_s1; apply (shape_kept_upd s g am am1 Mg); (split; [apply same_shape_links | reflexivity])|].
      apply (shape_kept_upd _ h ah ah1); [| (split; [apply same_shape_links | reflexivity])]. unfold q1_s1. rewrite (MT_upd_other g _ s h Hhg). exact Mh.
    Qed.
  End Q1.

  Section Q2.
    Variables (h : sptr) (ah : ameta) (t : sptr) (at_ : ameta).
    Hypothesis Hhg : h <> g.
    Hypothesis Mh : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs;Vh;A2S42S1S3Vah;A1A2A3").
    Hypothesis Htg : t <> g.
    Hypothesis Hth : t <> h.
    Hypothesis Mt : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs;Vt;A2S42S1S3Vat_;A1A2A3").
    Let am2 : ameta := ltac2:(tb__ "0|0|
S8S42S0Vt;A2S42S0Vh;A2Vam;A3").
    Let at2 : ameta := ltac2:(tb__ "0|0|
S8ScVat_;A1S42S0Vg;A2Vat_;A3").
    Let ah2 : ameta := ltac2:(tb__ "0|0|
S8S42S0Vg;A2S7Vah;A1Vah;A3").
    Let s3 : astate := ltac2:(tb__ "0|0|
S6cVs;Vg;Vam;Vh;Vah;Vt;Vat_;A7").
    Lemma MT_q2_g : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs3;Vg;A2S42S1S3Vam2;A1A2A3").
    Proof using Hhg Htg ah am at_ s.
      unfold s3, q2_s3, q2_s2, q2_s1. rewrite (MT_upd_other h _ _ g ltac:(intros E; exact (Hhg (eq_sym E)))).
      rewrite (MT_upd_other t _ _ g ltac:(intros E; exact (Htg (eq_sym E)))). apply MT_upd_same.
    Qed.
    Lemma MT_q2_h : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs3;Vh;A2S42S1S3Vah2;A1A2A3").
    Proof using ah am at_ g s t. unfold s3, q2_s3. apply MT_upd_same. Qed.
    Lemma MT_q2_t : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs3;Vt;A2S42S1S3Vat2;A1A2A3").
    Proof using Hth ah am at_ g s. unfold s3, q2_s3, q2_s2. rewrite (MT_upd_other h _ _ t Hth). apply MT_upd_same. Qed.
    Lemma MT_q2_other q : ltac2:(tb__ "0|0|
S3eS3dS0Vq;Vg;A3A1S3eS3dS0Vq;Vh;A3A1S3eS3dS0Vq;Vt;A3A1S3dS41S1A1S56Vs3;Vq;A2S56Vs;Vq;A2A3F_;F_;F_;").
    Proof using ah am at_.
      intros Hq1 Hq2 Hq3. unfold s3, q2_s3, q2_s2, q2_s1. rewrite (MT_upd_other h _ _ q Hq2), (MT_upd_other t _ _ q Hq3). apply MT_upd_other. exact Hq1.
    Qed.
    Lemma keys_q2_s1 : ltac2:(tb__ "0|0|
S3dS4bS0A1S58S6aVs;Vg;Vam;Vh;Vt;A5A1S58Vs;A1A3").
    Proof using Mg. unfold q2_s1. apply keys_upd_In. eapply MT_Some_In_keys. exact Mg. Qed.
    Lemma keys_q2_s2 : ltac2:(tb__ "0|0|
S3dS4bS0A1S58S6bVs;Vg;Vam;Vh;Vt;Vat_;A6A1S58Vs;A1A3").
    Proof using Mg Mt. unfold q2_s2. rewrite keys_upd_In; [apply keys_q2_s1|]. rewrite keys_q2_s1. eapply MT_Some_In_keys. exact Mt. Qed.
    Lemma keys_q2 : ltac2:(tb__ "0|0|
S3dS4bS0A1S58Vs3;A1S58Vs;A1A3").
    Proof using Mg Mh Mt. unfold s3, q2_s3. rewrite keys_upd_In; [apply keys_q2_s2|]. rewrite keys_q2_s2. eapply MT_Some_In_keys. exact Mh. Qed.
    Lemma hd_q2 c : ltac2:(tb__ "0|0|
S3dS41S0A1S57Vs3;Vc;A2S57Vs;Vc;A2A3").
    Proof using ah am at_ g h t. unfold s3, q2_s3, q2_s2, q2_s1. rewrite !active_hd_upd_meta. reflexivity. Qed.
    Lemma delta_q2 : ltac2:(tb__ "0|1|
S77Vs;S63Vg;Vi;Vs3;Vam2;A4S4cS59S4cS59S4cS59S76Vg;A1M0S76Vt;A1A3S76Vh;A1A3G0A3A3").
    Proof using Hhg Htg Hth Mg Mh Mt ND ah2 at2.
      pose proof keys_q2_s1 as K1. pose proof keys_q2_s2 as K2.
      assert (ND1 : List.NoDup (keys (q2_s1 s g am h t))) by (rewrite K1; exact ND).
      assert (ND2 : List.NoDup (keys (q2_s2 s g am h t at_))) by (rewrite K2; exact ND).
      assert (M1t : MT (q2_s1 s g am h t) t = Some (MUsed at_)) by (unfold q2_s1; rewrite (MT_upd_other g _ s t Htg); exact Mt).
      assert (M2h : MT (q2_s2 s g am h t at_) h = Some (MUsed ah)).
      { unfold q2_s2, q2_s1. rewrite (MT_upd_other t _ _ h ltac:(intros E; exact (Hth (eq_sym E)))), (MT_upd_other g _ s h Hhg). exact Mh. }
      eapply delta_trans; [| apply delta_or; [rewrite keys_q2; exact ND | apply MT_q2_g]].
      unfold s3, q2_s3. eapply delta_trans.
      - unfold q2_s2. eapply delta_trans.
        + unfold q2_s1. apply (delta_su_keep s g am am2 ND Mg); [apply same_shape_links | reflexivity].
        + apply (delta_su_keep _ t at_ at2 ND1 M1t); [apply same_shape_links | reflexivity].
      - apply (delta_su_keep _ h ah ah2 ND2 M2h); [apply same_shape_links | reflexivity].
    Qed.
    Lemma shape_q2 : ltac2:(tb__ "0|0|
S64Vs;S63Vg;Vi;Vs3;Vam2;A4A2").
    Proof using Hhg Htg Hth Mg Mh Mt ah2 at2.
      eapply shape_kept_trans; [| apply shape_or; apply MT_q2_g].
      unfold s3, q2_s3. eapply shape_kept_trans.
      - unfold q2_s2. eapply shape_kept_trans; [unfold q2_s1; apply (shape_kept_upd s g am am2 Mg); (split; [apply same_shape_links | reflexivity])|].
        apply (shape_kept_upd _ t at_ at2); [| (split; [apply same_shape_links | reflexivity])]. unfold q2_s1. rewrite (MT_upd_other g _ s t Htg). exact Mt.
      - apply (shape_kept_upd _ h ah ah2); [| (split; [apply same_shape_links | reflexivity])].
        unfold q2_s2, q2_s1. rewrite (MT_upd_other t _ _ h ltac:(intros E; exact (Hth (eq_sym E)))), (MT_upd_other g _ s h Hhg). exact Mh.
    Qed.
  End Q2.
End ElsePosts.

Lemma get_fhead_eq s : ltac2:(tb__ "0|2|
S3dS9S2S43S41S0A1M0S2A2M1A2S23S22Vs;A2SaS2G1S45G0S2S4Vs;A1Vs;A4A3A3").
Proof. reflexivity. Qed.
Lemma set_fhead_eq s v : ltac2:(tb__ "0|1|
S3dS9S2S43S44S2A2M0A2S37S22Vv;Vs;A3SaS2G0S45S44S2S4aS25Vv;Vs;A2A4A3A3").
Proof. reflexivity. Qed.
Lemma setslot_eq s p x : ltac2:(tb__ "0|1|
S3dS9S2S43S44S2A2M0A2S39Vp;Vx;Vs;A3SaS2G0S45S44S2S4aS5fVp;Vx;Vs;A3A4A3A3").
Proof. reflexivity. Qed.
Definition seq_post (s : astate) : astate := ltac2:(tb__ "0|2|
S47S2L_;S70SfVs;A1M0ZffA2S1eZ1M1S19S88S5eZ0U20A3Vs;A2A2S1eS6eG0G1A2Vs;A2X47x2").
Lemma step_seq_eq s : ltac2:(tb__ "0|1|
S3dS9S2S43S44S2A2M0A2S3aVs;A1SaS2G0S45S44S2S4aS65Vs;A1A4A3A3").
Proof. unfold step_seq, seq_post, modify. destruct (st_seq s =? 255); reflexivity. Qed.

Definition fq_post (t : astate) (g : sptr) : astate := ltac2:(tb__ "0|8|
S41S0A1M0S2Lx;M1S4Vt;A1S0S41S1A1M2S2Lx;S56Vt;R1A2S1G1S4dG0G0S17R1A1M3A3M4S0S5fVg;S6S42S0R1A2S42S0R3A2A2Vt;A3S2G2S1Lx;M5S56R1R2A2S1R1Lx;M6S1aX41x2S1S5fR3S14R1G4S42S0Vg;A2M7A3R2A3S2G5S56R1R6A2G6S1aX41x2S1S5fR7S14R1G7S4eG0G0G3A3A3R2A3Txfm;Tt2;Txhp;Tt1;Lhp;Vt;X41x2Lxf;Vt;X41x2Lfm;S25G7S5fVg;S6G7G7A2Vt;A3A2X41x2").

Lemma queue_free_eq t g : ltac2:(tb__ "0|5|
S3dS41S1A1M0S56Vt;Vg;A2S42S1S6S46S0A1M1G1A2A2A3S0S3dS41S0A1M2S4Vt;A1S42S0R1A2M3A3S3fS3eS3dS0R2Vg;A3A1S40S1S1S40S0S0S3fS3dG0S56Vt;R4A2S42S1R2A2A3S3fS3dG2S4dG2G2S17R2A1A3G3A3S3fS3eS3dS0R1Vg;A3A1S3eS3dG0S56Vt;R1A2S46S1A1A3A1A2A2A2Lhp;A2Lxf;A2A2F_;Ffm;S3dS9S2S43S44S2A2M4A2S2fS22Vg;Vt;A3SaS2G4S45S44S2S4aS68Vt;Vg;A2A4A3A3F_;F_;").
Proof.
  intros Mg Hhd. unfold queue. rewrite (bind_eq _ _ t _ t (get_links_eq t g _ Mg)). cbn [links_of fst snd osptr_eqb andb].
  rewrite (bind_eq _ _ t tt t) by (apply massert_true_eq; reflexivity).
  rewrite (bind_eq _ _ t _ t (get_fhead_eq t)). unfold fq_post.
  destruct (st_free_meta_head t) as [fm|] eqn:Efh.
  - destruct (Hhd fm eq_refl) as (Hfg & xf & hp & Mf & Hhp & Hpg & Mhp). rewrite (bind_eq _ _ t _ t (get_links_eq t fm xf Mf)). rewrite Mf, Hhp.
    rewrite (bind_eq _ _ t tt _ (set_links_eq t g _ (Some hp) (Some fm) Mg)). cbn [with_links].
    set (t1 := upd_meta g (MFree (Some hp) (Some fm)) t).
    assert (M1 : MT t1 hp = Some (match MT t1 hp with Some x => x | None => MRaw end)).
    { unfold t1. rewrite (MT_upd_other g _ t hp Hpg). destruct (MT t hp) as [x|]; [reflexivity | exfalso; exact (Mhp eq_refl)]. }
    rewrite (bind_eq _ _ t1 tt _ (set_next_eq t1 hp _ (Some g) M1)).
    set (t2 := upd_meta hp _ t1).
    assert (M2 : MT t2 fm = Some (match MT t2 fm with Some x => x | None => MRaw end)).
    { unfold t2. destruct (sptr_eq_dec fm hp) as [->|Hne]; [rewrite MT_upd_same; reflexivity|].
      rewrite (MT_upd_other hp _ t1 fm Hne). unfold t1. rewrite (MT_upd_other g _ t fm Hfg). rewrite Mf. reflexivity. }
    exact (set_prev_eq t2 fm _ (Some g) M2).
  - rewrite (bind_eq _ _ t tt _ (set_links_eq t g _ (Some g) (Some g) Mg)). cbn [with_links]. apply set_fhead_eq.
Qed.

Section FreeGroupDirect.
  Variables (X : list sptr) (U : Z -> Z) (s : astate) (g : sptr) (am : ameta) (i : Z).
  Hypothesis HI : ltac2:(tb__ "0|0|
S5aVX;S42S43S0S5eA2S45S0S5eVg;Vi;A4A2VU;Vs;A4").
  Hypothesis Hu : ltac2:(tb__ "0|0|
S5bVX;Vs;Vg;Vam;A4").
  Hypothesis HU : forall c, 0 <= U c.
  Hypothesis HR2g : ltac2:(tb__ "0|2|
S3eS3dS43S41S0A1M0G0A2S45G0G0ScVam;A1S7Vam;A1A4S45G0G0S46S0A1M1G1A4A3A1S3eS3dG0S57Vs;S5Vam;A1A2S42S0Vg;A2A3A1S3eS3dS5eS10Vam;A1Z0A3A1F_;F_;").
  Hypothesis Hall : ltac2:(tb__ "0|0|
S3dS5eS6eS67Vam;A1S13Vi;A1A2S24S11Vam;A1A1A3").
  Hypothesis Hsc63 : am_sc am = 63.
  Hypothesis Hnx : am_next am = None.
  Hypothesis Hml : am_maplen am <> 0.

  Definition fgd_s2 : astate := ltac2:(tb__ "0|1|
S5fVg;S6S46S0A1M0G0A2S65Vs;A1A3").
  Definition fgd_post : astate := fq_post fgd_s2 g.
  Definition fgd_res : option (nat * Z) := ltac2:(tb__ "0|0|
S42S43S48S5eA2S45S48S5eS2eS16Vam;A1A1S72S15Vam;A1Z1000A2A4A2").

  Hypothesis Hfree_ring : ltac2:(tb__ "0|3|
S0S3dS41S0A1M0S4Vs;A1S42S0R1A2M1A3S3fS3eS3dS0R2Vg;A3A1S40G0G0S40G0G0S40S0S0S3fS3dS41S1A1M2S56Vs;R5A2S42S1S6R3R2A2A2A3S3fS3dG0R3G1A3S3fS3eS3dS0R1Vg;A3A1S3eS3dG2S56Vs;R1A2S46S1A1A3A1A2A2A2Lhp;A2Lnx;A2Lpr;A2A2F_;Ffm;").

  Theorem fgd_eq fuel : ltac2:(tb__ "0|2|
S3dS9S2S43S41S43S48S5eA2A1M0S2A2M1A2SeS49Vfuel;A1Vg;Vi;Vs;A4SaS2G1S45G0S2S62S60A4A3A3").
  Proof using Hall Hfree_ring Hml Hnx Hsc63 Hu.
    pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
    cbn fix beta iota delta [nontrivial_free].
    rewrite (bind_eq _ _ s am s (getm_eq s g am Mg)). rewrite (bind_eq _ _ s s s (get_eq s)). cbn zeta.
    fold (nmask am). rewrite Hall, Z.eqb_refl.
    replace (okay_to_free s g am) with true by (unfold okay_to_free; rewrite Hsc63; reflexivity). cbn [andb].
    rewrite Hnx. rewrite (bind_eq _ _ s tt s (ret_eq tt s)).
    rewrite (bind_eq _ _ s am s (getm_eq s g am Mg)).
    rewrite Hsc63. cbn [Z.ltb Z.compare Pos.compare]. rewrite (bind_eq _ _ s tt s (ret_eq tt s)).
    replace (negb (am_maplen am =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Hml).
    rewrite (bind_eq _ _ s fgd_res (seq_post s)).
    2:{ rewrite (bind_eq _ _ s tt (seq_post s) (step_seq_eq s)). unfold record_seq, bounce_idx. cbn. reflexivity. }
    unfold free_meta. rewrite (bind_eq _ _ (seq_post s) tt fgd_post); [reflexivity|].
    rewrite (bind_eq _ _ (seq_post s) tt fgd_s2 (setslot_eq _ g _)). apply queue_free_eq.
    - unfold fgd_s2. apply MT_upd_same.
    - intros fm Hfm. unfold fgd_s2 in Hfm |- *. change (st_free_meta_head (upd_meta g (MFree None None) (seq_post s))) with (st_free_meta_head (seq_post s)) in Hfm.
      assert (Efh : st_free_meta_head (seq_post s) = st_free_meta_head s) by (unfold seq_post; destruct (st_seq s =? 255); reflexivity).
      rewrite Efh in Hfm. destruct (Hfree_ring fm Hfm) as (Hfg & pr & nx & hp & Mf & -> & Hpg & Mhp).
      assert (MTs : forall q, MT (seq_post s) q = MT s q) by (intros q; unfold seq_post; destruct (st_seq s =? 255); reflexivity).
      split; [exact Hfg|]. exists (MFree (Some hp) nx), hp.
      rewrite (MT_upd_other g _ _ fm Hfg), MTs, Mf. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hpg|].
      rewrite (MT_upd_other g _ _ hp Hpg), MTs. exact Mhp.
  Qed.

  Theorem fgd_nf_post fuel : ltac2:(tb__ "0|0|
S85S86S5Vam;A1A1S49Vfuel;A1A2S87VX;VU;Vs;S45S41S43S48S5eA2A1S2S62S60A4A4F_;").
  Proof using HI HR2g HU Hall Hfree_ring Hml Hnx Hsc63 Hu.
    intros Hf. pose proof (nontrivial_free_spec (S fuel) X U s g i am (nf_post X U s) HI Hu HU HR2g Hf (fun r Hr => Hr)) as T.
    rewrite fgd_eq in T. exact T.
  Qed.

  Lemma seq_post_MT q : ltac2:(tb__ "0|0|
S3dS41S1A1S56S65Vs;A1Vq;A2S56Vs;Vq;A2A3").
  Proof using . unfold seq_post. destruct (st_seq s =? 255); reflexivity. Qed.
  Lemma seq_post_head : ltac2:(tb__ "0|0|
S3dS41S0A1S4S65Vs;A1A1S4Vs;A1A3").
  Proof using . unfold seq_post. destruct (st_seq s =? 255); reflexivity. Qed.
  Lemma seq_post_seq : ltac2:(tb__ "0|5|
S3fS3dS5eSfS65Vs;A1M0A1S47S5eL_;S70SfVs;A1M1ZffA2M2Z1M3S6eG1G3A2X47x2A3S3dS4bS5eA1M4S12G0A1S47G4L_;G2S88S5eZ0U20A3S12Vs;A1X47x2A3A2").
  Proof using . unfold seq_post. destruct (st_seq s =? 255); split; reflexivity. Qed.
  Lemma fgd_s2_MT_g : ltac2:(tb__ "0|1|
S3dS41S1A1S56S61Vg;A2S42S1S6S46S0A1M0G0A2A2A3").
  Proof using . unfold fgd_s2. apply MT_upd_same. Qed.
  Lemma fgd_s2_MT_other q : ltac2:(tb__ "0|0|
S3eS3dS0Vq;Vg;A3A1S3dS41S1A1S56S61Vq;A2S56Vs;Vq;A2A3F_;").
  Proof using . intros Hq. unfold fgd_s2. rewrite (MT_upd_other g _ _ q Hq). apply seq_post_MT. Qed.
  Lemma fgd_s2_head : ltac2:(tb__ "0|0|
S3dS41S0A1S4S61A1S4Vs;A1A3").
  Proof using . unfold fgd_s2. cbn [upd_meta set_metas st_free_meta_head]. change (st_free_meta_head (upd_meta g (MFree None None) (seq_post s))) with (st_free_meta_head (seq_post s)). apply seq_post_head. Qed.

  Lemma fgd_post_empty : ltac2:(tb__ "0|1|
S3dS41S0A1S4Vs;A1S46S0A1A3S3dS2S60S25S42S0Vg;A2M0S5fVg;S6G0G0A2S61A3A2A3F_;").
  Proof using . intros Hfh. unfold fgd_post, fq_post. rewrite fgd_s2_head, Hfh. reflexivity. Qed.

  Section Ring.
    Variables (fm hp nx pr2 nx2 : sptr).
    Hypothesis Hfh : ltac2:(tb__ "0|0|
S3dS41S0A1S4Vs;A1S42S0Vfm;A2A3").
    Hypothesis Mfm : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs;Vfm;A2S42S1S6S42S0Vhp;A2S42S0Vnx;A2A2A2A3").
    Hypothesis Mhp : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs;Vhp;A2S42S1S6S42S0Vpr2;A2S42S0Vnx2;A2A2A2A3").
    Hypothesis Hfg : fm <> g.
    Hypothesis Hhg : hp <> g.
    Definition fgd_t3 : astate := ltac2:(tb__ "0|0|
S5fVg;S6S42S0Vhp;A2S42S0Vfm;A2A2S61A3").
    Definition fgd_t4 : astate := ltac2:(tb__ "0|0|
S5fVhp;S6S42S0Vpr2;A2S42S0Vg;A2A2S8aA3").
    Definition fm_next' : option sptr := ltac2:(tb__ "0|0|
S47S41S0A1L_;S26Vfm;Vhp;A2S42S0Vg;A2S42S0Vnx;A2X47x2").
    Lemma fgd_post_ring : ltac2:(tb__ "0|0|
S3dS2S60S5fVfm;S6S42S0Vg;A2S89A2S8bA3A3").
    Proof using Hfg Hfh Hhg Mfm Mhp.
      unfold fgd_post, fq_post. rewrite fgd_s2_head, Hfh. rewrite (fgd_s2_MT_other fm Hfg), Mfm. cbn [links_of fst].
      fold fgd_t3.
      assert (M3 : MT fgd_t3 hp = Some (MFree (Some pr2) (Some nx2))).
      { unfold fgd_t3. rewrite (MT_upd_other g _ _ hp Hhg). rewrite (fgd_s2_MT_other hp Hhg). exact Mhp. }
      rewrite M3. cbn [with_links links_of fst]. fold fgd_t4.
      assert (M4 : MT fgd_t4 fm = Some (if sptr_eqb fm hp then MFree (Some pr2) (Some g) else MFree (Some hp) (Some nx))).
      { unfold fgd_t4. destruct (sptr_eqb fm hp) eqn:E.
        - apply sptr_eqb_eq in E. rewrite E. apply MT_upd_same.
        - rewrite (MT_upd_other hp _ _ fm) by (intros EE; rewrite EE, sptr_eqb_refl in E; discriminate).
          unfold fgd_t3. rewrite (MT_upd_other g _ _ fm Hfg). rewrite (fgd_s2_MT_other fm Hfg). exact Mfm. }
      rewrite M4. unfold fm_next'. destruct (sptr_eqb fm hp); reflexivity.
    Qed.
    Lemma fgd_MT_fm : ltac2:(tb__ "0|0|
S3dS41S1A1S56S60Vfm;A2S42S1S6S42S0Vg;A2S89A2A2A3").
    Proof using Hfg Hfh Hhg Mfm Mhp. rewrite fgd_post_ring. apply MT_upd_same. Qed.
    Lemma fgd_MT_hp : ltac2:(tb__ "0|0|
S3eS3dS0Vhp;Vfm;A3A1S3dS41S1A1S56S60Vhp;A2S42S1S6S42S0Vpr2;A2S42S0Vg;A2A2A2A3F_;").
    Proof using Hfg Hfh Hhg Mfm Mhp. intros Hne. rewrite fgd_post_ring. rewrite (MT_upd_other fm _ _ hp Hne). unfold fgd_t4. apply MT_upd_same. Qed.
    Lemma fgd_MT_g_ring : ltac2:(tb__ "0|0|
S3dS41S1A1S56S60Vg;A2S42S1S6S42S0Vhp;A2S42S0Vfm;A2A2A2A3").
    Proof using Hfg Hfh Hhg Mfm Mhp.
      rewrite fgd_post_ring. rewrite (MT_upd_other fm _ _ g) by (intros E; exact (Hfg (eq_sym E))).
      unfold fgd_t4. rewrite (MT_upd_other hp _ _ g) by (intros E; exact (Hhg (eq_sym E))). unfold fgd_t3. apply MT_upd_same.
    Qed.
    Lemma fgd_MT_other_ring q : ltac2:(tb__ "0|0|
S3eS3dS0Vq;Vg;A3A1S3eS3dS0Vq;Vfm;A3A1S3eS3dS0Vq;Vhp;A3A1S3dS41S1A1S56S60Vq;A2S56Vs;Vq;A2A3F_;F_;F_;").
    Proof using Hfg Hfh Hhg Mfm Mhp.
      intros H1 H2 H3. rewrite fgd_post_ring. rewrite (MT_upd_other fm _ _ q H2). unfold fgd_t4. rewrite (MT_upd_other hp _ _ q H3).
      unfold fgd_t3. rewrite (MT_upd_other g _ _ q H1). apply fgd_s2_MT_other. exact H1.
    Qed.
    Lemma fgd_head_ring : ltac2:(tb__ "0|0|
S3dS41S0A1S4S60A1S42S0Vfm;A2A3").
    Proof using Hfg Hfh Hhg Mfm Mhp. rewrite fgd_post_ring. cbn [upd_meta set_metas st_free_meta_head]. rewrite <- Hfh. rewrite <- fgd_s2_head. reflexivity. Qed.
    Lemma fgd_seq_ring : ltac2:(tb__ "0|1|
S3fS3dS5eSfS60A1SfS65Vs;A1M0A1A3S3dS4bS5eA1S12S60A1S12G0A1A3A2").
    Proof using Hfg Hfh Hhg Mfm Mhp. rewrite fgd_post_ring. split; reflexivity. Qed.
  End Ring.

  Lemma fgd_MT_g_empty : ltac2:(tb__ "0|1|
S3dS41S0A1S4Vs;A1S46S0A1A3S3dS41S1A1S56S60Vg;A2S42S1S6S42S0Vg;A2M0G0A2A2A3F_;").
  Proof using . intros Hfh. rewrite (fgd_post_empty Hfh). cbn [MT set_free_meta_head st_metas upd_meta set_metas]. unfold MT. cbn [st_metas]. apply mlookup_mupdate_same. Qed.
  Lemma fgd_MT_other_empty q : ltac2:(tb__ "0|0|
S3dS41S0A1S4Vs;A1S46S0A1A3S3eS3dS0Vq;Vg;A3A1S3dS41S1A1S56S60Vq;A2S56Vs;Vq;A2A3F_;F_;").
  Proof using .
    intros Hfh Hq. rewrite (fgd_post_empty Hfh).
    change (MT (set_free_meta_head (Some g) (upd_meta g (MFree (Some g) (Some g)) fgd_s2)) q) with (MT (upd_meta g (MFree (Some g) (Some g)) fgd_s2) q).
    rewrite (MT_upd_other g _ _ q Hq). apply fgd_s2_MT_other. exact Hq.
  Qed.
  Lemma fgd_head_empty : ltac2:(tb__ "0|1|
S3dS41S0A1M0S4Vs;A1S46S0A1A3S3dG0S4S60A1S42S0Vg;A2A3F_;").
  Proof using . intros Hfh. rewrite (fgd_post_empty Hfh). reflexivity. Qed.
  Lemma fgd_seq_empty : ltac2:(tb__ "0|1|
S3dS41S0A1S4Vs;A1S46S0A1A3S3fS3dS5eSfS60A1SfS65Vs;A1M0A1A3S3dS4bS5eA1S12S60A1S12G0A1A3A2F_;").
  Proof using . intros Hfh. rewrite (fgd_post_empty Hfh). split; reflexivity. Qed.
End FreeGroupDirect.

Lemma set_usage_of_eq s sc v : ltac2:(tb__ "0|1|
S3dS9S2S43S44S2A2M0A2S38Vsc;Vv;Vs;A3SaS2G0S45S44S2S4aS1fS20Vsc;Vv;S33Vs;A1A3Vs;A2A4A3A3").
Proof. reflexivity. Qed.
Lemma record_seq_eq s sc : ltac2:(tb__ "0|1|
S3dS9S2S43S44S2A2M0A2S36Vsc;Vs;A2SaS2G0S45S44S2S4aS41S5eA1S2Lx;S29Vsc;A1S5eS19S20R1SfVs;A1S12Vs;A1A3Vs;A2Lk;Vs;X41x2A4A3A3").
Proof. unfold record_seq. destruct (bounce_idx sc); reflexivity. Qed.
Lemma active_hd_set_hd_same sc v s : ltac2:(tb__ "0|1|
S3fS6dZ0Vsc;A2S71Vsc;Z30A2A2S3dS48S50S41S0A1M0S32Vs;A1A2U30A3S3dG0S57S75Vsc;Vv;Vs;A3Vsc;A2Vv;A3F_;F_;").
Proof.
  intros Hsc Hlen. unfold active_hd, set_hd. cbn [st_active set_active]. rewrite nth_lupd, Nat.eqb_refl, Hlen.
  replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.
Lemma active_hd_set_hd_other sc v s c : ltac2:(tb__ "0|1|
S6dZ0M0Vc;A2S6dG0Vsc;A2S3eS3dS5eVc;Vsc;A3A1S3dS41S0A1S57S75Vsc;Vv;Vs;A3Vc;A2S57Vs;Vc;A2A3F_;F_;F_;").
Proof.
  intros Hc Hsc Hne. unfold active_hd, set_hd. cbn [st_active set_active]. rewrite nth_lupd.
  replace (Nat.eqb (Z.to_nat c) (Z.to_nat sc)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

Lemma MT_set_usage v t q : ltac2:(tb__ "0|0|
S3dS41S1A1S56S1fVv;Vt;A2Vq;A2S56Vt;Vq;A2A3"). Proof. reflexivity. Qed.
Lemma MT_set_unmap_seq v t q : ltac2:(tb__ "0|0|
S3dS41S1A1S56S19Vv;Vt;A2Vq;A2S56Vt;Vq;A2A3"). Proof. reflexivity. Qed.
Lemma MT_set_seq v t q : ltac2:(tb__ "0|0|
S3dS41S1A1S56S1eVv;Vt;A2Vq;A2S56Vt;Vq;A2A3"). Proof. reflexivity. Qed.
Lemma head_upd_meta p x t : ltac2:(tb__ "0|0|
S3dS41S0A1S4S5fVp;Vx;Vt;A3A1S4Vt;A1A3"). Proof. reflexivity. Qed.
Lemma head_set_hd c v t : ltac2:(tb__ "0|0|
S3dS41S0A1S4S75Vc;Vv;Vt;A3A1S4Vt;A1A3"). Proof. reflexivity. Qed.
Lemma head_set_usage v t : ltac2:(tb__ "0|0|
S3dS41S0A1S4S1fVv;Vt;A2A1S4Vt;A1A3"). Proof. reflexivity. Qed.
Lemma head_set_unmap_seq v t : ltac2:(tb__ "0|0|
S3dS41S0A1S4S19Vv;Vt;A2A1S4Vt;A1A3"). Proof. reflexivity. Qed.
Lemma head_set_seq v t : ltac2:(tb__ "0|0|
S3dS41S0A1S4S1eVv;Vt;A2A1S4Vt;A1A3"). Proof. reflexivity. Qed.
Lemma head_seq_post t : ltac2:(tb__ "0|0|
S3dS41S0A1S4S65Vt;A1A1S4Vt;A1A3").
Proof. unfold seq_post. destruct (st_seq t =? 255); reflexivity. Qed.
Lemma MT_seq_post t q : ltac2:(tb__ "0|0|
S3dS41S1A1S56S65Vt;A1Vq;A2S56Vt;Vq;A2A3").
Proof. unfold seq_post. destruct (st_seq t =? 255); reflexivity. Qed.

Section FreeGroupMapped.
  Local Open Scope mm_scope.
  Variables (X : list sptr) (U : Z -> Z) (s : astate) (g : sptr) (am : ameta) (i : Z).
  Hypothesis HI : ltac2:(tb__ "0|0|
S5aVX;S42S43S0S5eA2S45S0S5eVg;Vi;A4A2VU;Vs;A4").
  Hypothesis Hu : ltac2:(tb__ "0|0|
S5bVX;Vs;Vg;Vam;A4").
  Hypothesis HU : forall c, 0 <= U c.
  Hypothesis HR2g : ltac2:(tb__ "0|2|
S3eS3dS43S41S0A1M0G0A2S45G0G0ScVam;A1S7Vam;A1A4S45G0G0S46S0A1M1G1A4A3A1S3eS3dG0S57Vs;S5Vam;A1A2S42S0Vg;A2A3A1S3eS3dS5eS10Vam;A1Z0A3A1F_;F_;").
  Hypothesis Hall : ltac2:(tb__ "0|0|
S3dS5eS6eS67Vam;A1S13Vi;A1A2S24S11Vam;A1A1A3").
  Hypothesis Hsc : ltac2:(tb__ "0|1|
S3fS6dZ0S5Vam;A1M0A2S71G0Z30A2A2").
  Hypothesis Hml : am_maplen am <> 0.
  Hypothesis Hok : ltac2:(tb__ "0|0|
S3dS47S2dVs;Vg;Vam;A3S55A3").
  Let sc : Z := am_sc am.
  Lemma Mg : ltac2:(tb__ "0|0|
S3dS41S1A1S56Vs;Vg;A2S42S1S3Vam;A1A2A3"). Proof using Hu. exact (proj1 (usedX_MT _ _ _ _ Hu)). Qed.
  Lemma LenA : length (st_active s) = 48%nat. Proof using HI. exact (proj1 (inv_ctx HI)). Qed.

  Definition dq_post : astate := ltac2:(tb__ "0|8|
S41S0A1M0S2Lx;M1S7Vam;A1S0S47S2L_;M2S26R1Vg;A2S5fVg;S3S8S46S0A1M3G3Vam;A3A1M4S75Vsc;G3Vs;A3A3G1ScVam;A1S0S41S1A1S1Lx;M5S56Vs;R1A2S1R1Lx;M6S1aX41x2S1S5fR2S14R1S4dG0G0S17R1A1M7A3S42S0R3A2A3Vs;A3S2G5S56R1R4A2G6S1aX41x2S1S5fR5S14R1S42S0R4A2S4eG0G0G7A3A3R2A3S2G2S18S57Vs;Vsc;A2S42S0Vg;A2A2S75Vsc;S42S0R6A2R1A3R1X47x2S2S5fVg;G4R1A3Ts1c;Ts1b;Txn;Ts1a;Txp;Lp;Vs;X41x2X47x2Ln;Vs;X41x2").

  Definition act_post (t : astate) : astate := ltac2:(tb__ "0|1|
S41S0A1M0S2Lx;S7Vam;A1S0S47S2L_;S4fS53S26R1Vg;A2A1S18S57Vs;Vsc;A2S42S0Vg;A2A2A2S41S1A1S2Lx;S56Vt;R1A2S1S1S2Lm;R1G0G0Vt;Lnext;Lprev;Vt;SbS5fR3S3S93R1A1A1Vt;A3Lan;X1x3Lm;Vt;X41x2Vt;X47x2Ln;Vt;X41x2").
  Definition fgm_s1 : astate := act_post dq_post.
  Definition fgm_s2 : astate := ltac2:(tb__ "0|0|
S1fS20Vsc;S74S3cVs;Vsc;A2S6eS11Vam;A1Z1A2A2S33S7eA1A3S7eA2").
  Definition fgm_s3 : astate := seq_post fgm_s2.
  Definition fgm_s4 : astate := ltac2:(tb__ "0|0|
S41S5eA1S2Lx;S29Vsc;A1S5eS19S20R1SfS7fA1S12S7fA1A3S7fA2Lk;S7fX41x2").
  Definition fgm_s5 : astate := ltac2:(tb__ "0|1|
S5fVg;S6S46S0A1M0G0A2S84A3").
  Definition fgm_post : astate := fq_post fgm_s5 g.
  Definition fgm_res : option (nat * Z) := ltac2:(tb__ "0|0|
S42S43S48S5eA2S45S48S5eS2eS16Vam;A1A1S72S15Vam;A1Z1000A2A4A2").

  Hypothesis Hlinks : ltac2:(tb__ "0|2|
S0S3dS41S0A1M0S7Vam;A1S42S0R1A2A3S3eS3dS0R2Vg;A3A1S40S0S0S40S1S1S40S1S1S3fS3dG0ScVam;A1S42S0R3A2A3S3fS3eS3dS0R3Vg;A3A1S3fS3dS41S1A1M1S56Vs;R3A2S42S1R2A2A3S3dG1S56S5fR3S14R2S4dG0G0S17R2A1A3S42S0R6A2A3Vs;A3R6A2S42S1R1A2A3A2A2A2Lxn;A2Lxp;A2Lp;A2F_;F_;Fn;").
  Hypothesis HnU : ltac2:(tb__ "0|0|
S0S3dS41S0A1S7Vam;A1S42S0R1A2A3S40SbSbS3dS41S1A1S56Vs;R3A2S42S1S3R1A1A2A3Lan;A2F_;Fn;").
  Hypothesis HpU : ltac2:(tb__ "0|0|
S0S3dS41S0A1ScVam;A1S42S0R1A2A3S40SbSbS3dS41S1A1S56Vs;R3A2S42S1S3R1A1A2A3Lap;A2F_;Fp;").
  Hypothesis Hact : ltac2:(tb__ "0|1|
S0SbS3dS41S0A1M0S7Vam;A1S42S0R2A2A3S3eS3dS0R3Vg;A3A1S3dG0S57Vs;Vsc;A2S42S0Vg;A2A3S3dS41S1A1S56S7dR5A2S42S1S3R4A1A2A3S3dS5eS28R5A1Z0A3F_;F_;F_;F_;Fan;Fn;").
  Hypothesis HactU : ltac2:(tb__ "0|1|
S0S3dS41S0A1M0S7Vam;A1S42S0R1A2A3S3eS3dS0R2Vg;A3A1S3dG0S57Vs;Vsc;A2S42S0Vg;A2A3S40SbSbS3dS41S1A1S56S7dR5A2S42S1S3R1A1A2A3Lan;A2F_;F_;F_;Fn;").
  Hypothesis Hfree_ring : ltac2:(tb__ "0|2|
S0S3dS41S0A1M0S4Vs;A1S42S0R1A2A3S3fS3eS3dS0R2Vg;A3A1S40S0S0S40G0G0S40G0G0S40G0G0S3fS3dS41S1A1M1S56Vs;R6A2S42S1S6S42S0R4A2R3A2A2A3S3fS3eS3dS0R4Vg;A3A1S3dG1S56Vs;R4A2S42S1S6R2R1A2A2A3A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2A2F_;Ffm;").

  Lemma MT_dq_g : ltac2:(tb__ "0|1|
S3dS41S1A1S56S7dVg;A2S42S1S3S41S0A1SbLx;S7Vam;A1S0S8S46S0A1M0G0Vam;A3Ls0;Vam;X41x2A1A2A3").
  Proof using HR2g Hact HactU Hlinks HnU Hu.
    unfold dq_post. destruct (am_next am) as [n|] eqn:En; [|exact Mg].
    destruct (sptr_eqb n g) eqn:Eng; [apply MT_upd_same|].
    assert (Hng : n <> g) by (intros E; rewrite E, sptr_eqb_refl in Eng; discriminate).
    destruct (Hlinks n eq_refl Hng) as (p & xp & xn & Ep & Hpg & Mp & Mn). rewrite Ep. apply MT_upd_same.
  Qed.

  Lemma dequeue_gen p n xp xn : ltac2:(tb__ "0|6|
S3dS41S0A1M0ScVam;A1S42S0Vp;A2M1A3S3dG0S7Vam;A1S42S0Vn;A2M2A3S3eS3dS0Vn;Vg;A3A1S3eS3dS0Vp;Vg;A3A1S3dS41S1A1M3S56Vs;Vp;A2S42S1Vxp;A2A3S5fVp;S14Vxp;S4dG0G0S17Vxp;A1A3G2A3Vs;A3S2S3dG3S56R1Vn;A2S42S1Vxn;A2A3S5fVn;S14Vxn;G1S4eG0G0S17Vxn;A1A3A3R2A3S2S3dS9S2S43S44S2A2M4A2S2aS21Vsc;A1Vg;Vs;A3SaS2G4S45S44S2S4aS5fVg;S3S8S46S0A1M5G5Vam;A3A1S47S2L_;S18S57Vs;Vsc;A2S42S0Vg;A2A2S75Vsc;G2R1A3R1X47x2A3A4A3A3Ts1b;F_;Ts1a;F_;F_;F_;F_;F_;").
  Proof using Hu.
    intros Ep En Hng Hpg Mp s1a Mn s1b. unfold dequeue.
    rewrite (bind_eq _ _ s _ s (get_links_eq s g (MUsed am) Mg)). cbn [links_of fst snd]. rewrite Ep, En.
    cbn [osptr_eqb]. replace (sptr_eqb n g) with false by (symmetry; apply sptr_eqb_neq; exact Hng).
    rewrite (bind_eq _ _ s tt (if osptr_eqb (active_hd s sc) (Some g) then set_hd sc (Some n) s1b else s1b)).
    - apply (set_links_eq _ g (MUsed am)).
      destruct (osptr_eqb (active_hd s sc) (Some g)); rewrite ?MT_set_hd; unfold s1b, s1a;
        rewrite (MT_upd_other n _ _ g) by (intros E; exact (Hng (eq_sym E))); rewrite (MT_upd_other p _ _ g) by (intros E; exact (Hpg (eq_sym E))); exact Mg.
    - rewrite (bind_eq _ _ s tt s1a); [| apply (set_next_eq s p xp); exact Mp].
      rewrite (bind_eq _ _ s1a tt s1b); [| apply (set_prev_eq s1a n xn); exact Mn].
      rewrite (bind_eq _ _ s1b _ s1b (get_head_eq s1b sc)). unfold s1b, s1a. rewrite !active_hd_upd_meta.
      destruct (osptr_eqb (active_hd s sc) (Some g)); [apply set_head_eq | reflexivity].
  Qed.

  Theorem fgm_dq_eq : ltac2:(tb__ "0|6|
S3dS9S2S43S44S2A2M0A2S41S0A1M1S27S44A1M2Lx;S7Vam;A1S0SdS44S44S2cS73Vsc;Z30A2Z5A2S44SdG1S44S23S21Vsc;A1M3A1M4G1S18R1S42S0Vg;A2A2S47SdS44S44S2aG3Vg;A2S44SdG1S44G4G1S47G2Lactivate_new;R3G1G2Lhd';R1S0SdS5eS44S34R1A1S5eS1dS44S4aA2M5L_;A4Lh;G5X41x2G5X47x2Lhd';A4L_;A4Tactivate_new;Lhd;A4L_;A4Ls0;G5X41x2Vs;A1SaS2G0S45S44S2S4aS7eA4A3A3").
  Proof using HI HR2g Hact HactU Hlinks HnU Hsc Hu.
    unfold fgm_s1, act_post, dq_post. pose proof LenA as LA.
    destruct (am_next am) as [n|] eqn:En; [|reflexivity].
    rewrite (bind_eq _ _ s tt s) by (apply massert_true_eq; apply Z.ltb_lt; unfold sc; lia).
    rewrite (bind_eq _ _ s _ s (get_head_eq s sc)).
    destruct (sptr_eqb n g) eqn:Eng.
    -
      apply sptr_eqb_eq in Eng. subst n.
      rewrite (bind_eq _ _ s tt _ (dequeue_ring1 s sc g am Mg En)). unfold s1_empty.
      rewrite (bind_eq _ _ _ _ _ (get_head_eq _ sc)). rewrite active_hd_upd_meta, (active_hd_set_hd_same sc None s) by (try exact LA; unfold sc; lia).
      cbn [andb negb]. destruct (osptr_eqb (active_hd s sc) (Some g)); reflexivity.
    - assert (Hng : n <> g) by (intros E; rewrite E, sptr_eqb_refl in Eng; discriminate).
      destruct (Hlinks n eq_refl Hng) as (p & xp & xn & Ep & Hpg & Mp & Mn). rewrite Ep.
      rewrite Mp. set (s1a := upd_meta p (with_links xp (fst (links_of xp)) (Some n)) s). fold s1a in Mn. rewrite Mn.
      set (s1b := upd_meta n (with_links xn (Some p) (snd (links_of xn))) s1a).
      rewrite (bind_eq _ _ s tt _ (dequeue_gen p n xp xn Ep En Hng Hpg Mp Mn)). fold s1a. fold s1b.
      rewrite (bind_eq _ _ _ _ _ (get_head_eq _ sc)). rewrite active_hd_upd_meta.
      destruct (osptr_eqb (active_hd s sc) (Some g)) eqn:Ehd.
      + rewrite (active_hd_set_hd_same sc (Some n) s1b) by (try (unfold s1b, s1a; cbn; exact LA); unfold sc; lia).
        cbn [andb negb].
        assert (Hhd : active_hd s sc = Some g).
        { destruct (active_hd s sc) as [h|]; cbn in Ehd; [|discriminate]. apply sptr_eqb_eq in Ehd. rewrite Ehd. reflexivity. }
        set (t := upd_meta g (MUsed (am_set_links None None am)) (set_hd sc (Some n) s1b)).
        assert (Et : t = dq_post).
        { unfold t, dq_post. rewrite En, Eng, Ep, Mp. fold s1a. rewrite Mn. fold s1b. rewrite Ehd. reflexivity. }
        destruct (HactU n eq_refl Hng Hhd) as (an & Man). pose proof (Hact n an eq_refl Hng Hhd Man) as AV. rewrite <- Et in Man. rewrite Man.
        rewrite (bind_eq _ _ t _ _ (activate_group_eq t n an Man AV)). reflexivity.
      + cbn [andb negb]. reflexivity.
  Qed.

  Lemma MT_s1_g : ltac2:(tb__ "0|1|
S3dS41S1A1S56S7eVg;A2S42S1S3S41S0A1SbLx;S7Vam;A1S0S8S46S0A1M0G0Vam;A3Ls0;Vam;X41x2A1A2A3").
  Proof using HR2g Hact HactU Hlinks HnU Hu.
    pose proof MT_dq_g as MG. unfold fgm_s1, act_post.
    destruct (am_next am) as [n|]; [|exact MG].
    destruct (negb (sptr_eqb n g) && osptr_eqb (active_hd s sc) (Some g)) eqn:E; [|exact MG].
    apply andb_prop in E as [E1 E2]. destruct (MT dq_post n) as [[| |an]|]; try exact MG.
    rewrite MT_upd_other by (intros EE; rewrite EE, sptr_eqb_refl in E1; discriminate). exact MG.
  Qed.

  Lemma head_dq : ltac2:(tb__ "0|0|
S3dS41S0A1S4S7dA1S4Vs;A1A3").
  Proof using HR2g Hact HactU Hlinks HnU HpU.
    unfold dq_post. destruct (am_next am) as [n|]; [|reflexivity]. destruct (sptr_eqb n g); [reflexivity|].
    destruct (am_prev am) as [p|]; [|reflexivity]. rewrite head_upd_meta. destruct (osptr_eqb (active_hd s sc) (Some g)); reflexivity.
  Qed.
  Lemma head_act t : ltac2:(tb__ "0|0|
S3dS41S0A1S4S80Vt;A1A1S4Vt;A1A3").
  Proof using HR2g Hact HactU Hlinks HnU.
    unfold act_post. destruct (am_next am) as [n|]; [|reflexivity]. destruct (negb (sptr_eqb n g) && osptr_eqb (active_hd s sc) (Some g)); [|reflexivity].
    destruct (MT t n) as [[| |an]|]; reflexivity.
  Qed.
  Lemma MT_act_other t q : ltac2:(tb__ "0|0|
S0S3dS41S0A1S7Vam;A1S42S0R1A2A3S3eS3dS0Vq;R2A3A1F_;Fn;S3dS41S1A1S56S80Vt;A1Vq;A2S56Vt;Vq;A2A3F_;").
  Proof using HR2g Hact HactU Hlinks HnU.
    intros Hn. unfold act_post. destruct (am_next am) as [n|] eqn:En; [|reflexivity]. destruct (negb (sptr_eqb n g) && osptr_eqb (active_hd s sc) (Some g)); [|reflexivity].
    destruct (MT t n) as [[| |an]|]; try reflexivity. apply MT_upd_other. exact (Hn n eq_refl).
  Qed.
  Lemma head_fgm5 : ltac2:(tb__ "0|0|
S3dS41S0A1S4S83A1S4Vs;A1A3").
  Proof using HR2g Hact HactU Hlinks HnU HpU.
    unfold fgm_s5, fgm_s4, fgm_s3, fgm_s2, fgm_s1. rewrite head_upd_meta.
    destruct (bounce_idx sc) as [k|]; rewrite ?head_set_unmap_seq, head_seq_post, head_set_usage, head_act; apply head_dq.
  Qed.
  Lemma MT_dq_other q : ltac2:(tb__ "0|3|
S3eS3dS0Vq;Vg;A3A1S0S3dS41S0A1M0S7Vam;A1S42S0R1A2M1A3S3eS3dS0Vq;R2A3A1M2F_;Fn;S0S3dG0ScVam;A1G1A3G2F_;Fp;S3dS41S1A1S56S7dVq;A2S56Vs;Vq;A2A3F_;F_;F_;").
  Proof using HR2g Hact HactU Hlinks HnU HpU.
    intros Hq Hn Hp. unfold dq_post. destruct (am_next am) as [n|] eqn:En; [|reflexivity].
    destruct (sptr_eqb n g); [rewrite (MT_upd_other g _ _ q Hq), MT_set_hd; reflexivity|].
    destruct (am_prev am) as [p|] eqn:Ep; [|reflexivity].
    rewrite (MT_upd_other g _ _ q Hq).
    destruct (osptr_eqb (active_hd s sc) (Some g)); rewrite ?MT_set_hd;
      rewrite (MT_upd_other n _ _ q (Hn n eq_refl)); rewrite (MT_upd_other p _ _ q (Hp p eq_refl)); reflexivity.
  Qed.
  Lemma MT_fgm5_other q : ltac2:(tb__ "0|3|
S3eS3dS0Vq;Vg;A3A1S0S3dS41S0A1M0S7Vam;A1S42S0R1A2M1A3S3eS3dS0Vq;R2A3A1M2F_;Fn;S0S3dG0ScVam;A1G1A3G2F_;Fp;S3dS41S1A1S56S83Vq;A2S56Vs;Vq;A2A3F_;F_;F_;").
  Proof using HR2g Hact HactU Hlinks HnU HpU.
    intros Hq Hn Hp. unfold fgm_s5, fgm_s4, fgm_s3, fgm_s2, fgm_s1. rewrite (MT_upd_other g _ _ q Hq).
    destruct (bounce_idx sc) as [k|]; rewrite ?MT_set_unmap_seq, MT_seq_post, MT_set_usage, (MT_act_other _ q Hn); apply (MT_dq_other q Hq Hn Hp).
  Qed.

  Theorem fgm_eq fuel : ltac2:(tb__ "0|2|
S3dS9S2S43S41S43S48S5eA2A1M0S2A2M1A2SeS49Vfuel;A1Vg;Vi;Vs;A4SaS2G1S45G0S2S82S81A4A3A3").
  Proof using HI HR2g Hact HactU Hall Hfree_ring Hlinks Hml HnU Hok HpU Hsc Hu.
    pose proof fgm_dq_eq as DQ. pose proof MT_s1_g as M1. pose proof Hfree_ring as FR. pose proof head_fgm5 as HF5. pose proof MT_fgm5_other as MT5.
    pose proof HnU as NU. pose proof HpU as PU.
    cbn fix beta iota delta [nontrivial_free].
    rewrite (bind_eq _ _ s am s (getm_eq s g am Mg)). rewrite (bind_eq _ _ s s s (get_eq s)). cbn zeta.
    fold (nmask am). rewrite Hall, Z.eqb_refl, Hok. cbn [andb].
    fold sc. rewrite (bind_eq _ _ s tt fgm_s1 DQ).
    rewrite (bind_eq _ _ fgm_s1 _ fgm_s1 (getm_eq fgm_s1 g _ M1)).
    replace (am_sc match am_next am with Some _ => am_set_links None None am | None => am end) with sc by (destruct (am_next am); reflexivity).
    replace (am_last match am_next am with Some _ => am_set_links None None am | None => am end) with (am_last am) by (destruct (am_next am); reflexivity).
    replace (am_maplen match am_next am with Some _ => am_set_links None None am | None => am end) with (am_maplen am) by (destruct (am_next am); reflexivity).
    replace (am_mem match am_next am with Some _ => am_set_links None None am | None => am end) with (am_mem am) by (destruct (am_next am); reflexivity).
    replace (sc <? 48) with true by (symmetry; apply Z.ltb_lt; unfold sc; lia).
    rewrite (bind_eq _ _ fgm_s1 tt fgm_s2) by (unfold fgm_s2; apply set_usage_of_eq).
    replace (negb (am_maplen am =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Hml).
    rewrite (bind_eq _ _ fgm_s2 fgm_res fgm_s4).
    2:{ rewrite (bind_eq _ _ fgm_s2 tt fgm_s3) by (unfold fgm_s3; apply step_seq_eq).
        rewrite (bind_eq _ _ fgm_s3 tt fgm_s4) by (unfold fgm_s4; apply record_seq_eq). reflexivity. }
    unfold free_meta. rewrite (bind_eq _ _ fgm_s4 tt fgm_post); [reflexivity|].
    rewrite (bind_eq _ _ fgm_s4 tt fgm_s5 (setslot_eq _ g _)). unfold fgm_post. apply queue_free_eq.
    - unfold fgm_s5. apply MT_upd_same.
    -
      intros fm Hfm. rewrite HF5 in Hfm. destruct (FR fm Hfm) as (Hfg & hp & nx & pr2 & nx2 & Mf & Hpg & Mh).
      assert (NEQ : forall q x, MT s q = Some x -> (match x with MUsed _ => False | _ => True end) ->
                    (forall n, am_next am = Some n -> q <> n) /\ (forall p, am_prev am = Some p -> q <> p)).
      { intros q x Mq Hx. split.
        - intros n En ->. destruct (NU n En) as [an Mn]. rewrite Mn in Mq. injection Mq as <-. exact Hx.
        - intros p Ep ->. destruct (PU p Ep) as [ap Mp]. rewrite Mp in Mq. injection Mq as <-. exact Hx. }
      destruct (NEQ fm _ Mf I) as [N1 P1]. destruct (NEQ hp _ Mh I) as [N2 P2].
      split; [exact Hfg|]. exists (MFree (Some hp) nx), hp. rewrite (MT5 fm Hfg N1 P1). split; [exact Mf|]. split; [reflexivity|]. split; [exact Hpg|].
      rewrite (MT5 hp Hpg N2 P2), Mh. discriminate.
  Qed.

  Theorem fgm_nf_post fuel : ltac2:(tb__ "0|0|
S85S86S5Vam;A1A1S49Vfuel;A1A2S87VX;VU;Vs;S45S41S43S48S5eA2A1S2S82S81A4A4F_;").
  Proof using HI HR2g HU Hact HactU Hall Hfree_ring Hlinks Hml HnU Hok HpU Hsc Hu.
    intros Hf. pose proof (nontrivial_free_spec (S fuel) X U s g i am (nf_post X U s) HI Hu HU HR2g Hf (fun r Hr => Hr)) as T.
    rewrite fgm_eq in T. exact T.
  Qed.
End FreeGroupMapped.
