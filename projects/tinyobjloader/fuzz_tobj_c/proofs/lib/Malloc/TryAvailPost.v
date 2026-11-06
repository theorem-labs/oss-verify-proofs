(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "mslot"; "itree"; "IRet"; "MUsed"; "am_freed"; "bind"; "am_next"; "st_bounces"; "am_sc"; "ameta"; "bounce_idx"; "ones"; "ret"; "HActive"; "am_aidx"; "am_last"; "znth"; "links_of"; "try_avail"; "with_links"; "M"; "am_avail"; "am_set_avail"; "set_head"; "zset"; "am_mem"; "am_prev"; "dequeue"; "getm"; "set_bounces"; "setm"; "FModel"; "activate_group"; "am_maplen"; "am_set_aidx"; "am_set_links"; "decay_bounces"; "fail"; "get_head"; "massert"; "UNIT"; "alloc_slot"; "am_set_freed"; "class_size"; "ctz32"; "get"; "get_links"; "kreq"; "lowbit"; "modify"; "osptr_eqb"; "padd"; "put"; "set_links"; "set_next"; "set_prev"; "span_loop"; "sptr_eqb"; "st_active"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "option"; "Some"; "prod"; "pair"; "unit"; "bool"; "tt"; "None"; "app"; "nil"; "list"; "cons"; "fst"; "negb"; "snd"; "length"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "active_hd"; "loc"; "keys"; "LCtx"; "meta_bits"; "CTX_active"; "CTX_bounces"; "Inv"; "LMem"; "yields"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "set_hd"; "delta"; "meta_locs"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "land"; "eqb"; "add"; "le"; "ldiff"; "lt"; "mul"; "ltb"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost"; "step1"; "step3"; "step2"; "am_activate"; "act_of"; "am_final"; "s1_empty"; "s6"; "span_cnt"; "t_first"; "tail"; "hit_post"; "s4"; "s5"; "t_mask"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost.Tail"; "s4"; "s5"; "t_first"; "am_final"; "s6"; "t_mask"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost.Hit"; "hit_first"; "hit_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost.Step1"; "s1_deq"; "s1_empty"; "s1a"; "s1b"; "s1_rot"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost.Step2"; "s2_skip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost.Step3"; "s3_rot"; "s3_span"; "@Stdlib.Lists.List"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfSlot ImageUpd ImageDelta.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Lemma bind_eq {A B} (m : M A) (k : A -> M B) s a s1 : ltac2:(tb__ "0|1|
S3dS3S0S44VA;S0A2M0A2Vm;Vs;A1S4S0G0S45VA;S0Va;Vs1;A4A3A3S3dS3S0S44VB;S0A2A2S7VA;VB;Vm;Vk;Vs;A5Vk;Va;Vs1;A2A3F_;").
Proof. intros H. unfold bind. rewrite H. reflexivity. Qed.

Lemma ret_eq {A} (a : A) s : ltac2:(tb__ "0|1|
S3dS3S0S44VA;S0A2M0A2SeVA;Va;Vs;A3S4S0G0S45VA;S0Va;Vs;A4A3A3"). Proof. reflexivity. Qed.
Lemma get_eq s : ltac2:(tb__ "0|1|
S3dS3S0S44S0S0A2M0A2S2fVs;A1S4S0G0S45S0S0Vs;Vs;A4A3A3"). Proof. reflexivity. Qed.
Lemma modify_eq f s : ltac2:(tb__ "0|1|
S3dS3S0S44S46S0A2M0A2S33Vf;Vs;A2S4S0G0S45S46S0S48Vf;Vs;A1A4A3A3"). Proof. reflexivity. Qed.
Lemma put_eq s s0 : ltac2:(tb__ "0|1|
S3dS3S0S44S46S0A2M0A2S36Vs;Vs0;A2S4S0G0S45S46S0S48Vs;A4A3A3"). Proof. reflexivity. Qed.

Lemma getm_eq s p am : ltac2:(tb__ "0|1|
S3dS42S2A1S53Vs;Vp;A2S43S2S5Vam;A1A2A3S3dS3S0S44SbS0A2M0A2S1eVp;Vs;A2S4S0G0S45SbS0Vam;Vs;A4A3A3F_;").
Proof. intros H. unfold getm. rewrite (bind_eq _ _ s s s (get_eq s)). unfold MT in H. rewrite H. reflexivity. Qed.

Lemma setm_eq s p am : ltac2:(tb__ "0|1|
S3dS3S0S44S46S0A2M0A2S20Vp;Vam;Vs;A3S4S0G0S45S46S0S48S5eVp;S5Vam;A1Vs;A3A4A3A3").
Proof. reflexivity. Qed.

Lemma get_head_eq s sc : ltac2:(tb__ "0|2|
S3dS3S0S44S42S1A1M0S0A2M1A2S28SfVsc;A1Vs;A2S4S0G1S45G0S0S54Vs;Vsc;A2Vs;A4A3A3").
Proof. reflexivity. Qed.

Lemma set_head_eq s sc v : ltac2:(tb__ "0|1|
S3dS3S0S44S46S0A2M0A2S19SfVsc;A1Vv;Vs;A3S4S0G0S45S46S0S48S5fVsc;Vv;Vs;A3A4A3A3").
Proof. reflexivity. Qed.

Lemma massert_true_eq b site s : ltac2:(tb__ "0|1|
S3dS47Vb;S52A3S3dS3S0S44S46S0A2M0A2S29Vb;Vsite;Vs;A3S4S0G0S45S46S0S48Vs;A4A3A3F_;").
Proof. intros ->. reflexivity. Qed.

Lemma get_links_eq s p x : ltac2:(tb__ "0|3|
S3dS42S2A1S53Vs;Vp;A2S43S2Vx;A2A3S3dS3S0S44S44S42S1A1M0G0A2M1S0A2M2A2S30Vp;Vs;A2S4S0G2S45G1S0S13Vx;A1Vs;A4A3A3F_;").
Proof. intros H. unfold get_links. rewrite (bind_eq _ _ s s s (get_eq s)). unfold MT in H. rewrite H. reflexivity. Qed.

Lemma set_links_eq s p x pr nx : ltac2:(tb__ "0|1|
S3dS42S2A1S53Vs;Vp;A2S43S2Vx;A2A3S3dS3S0S44S46S0A2M0A2S37Vp;Vpr;Vnx;Vs;A4S4S0G0S45S46S0S48S5eVp;S15Vx;Vpr;Vnx;A3Vs;A3A4A3A3F_;").
Proof. intros H. unfold set_links. rewrite (bind_eq _ _ s s s (get_eq s)). unfold MT in H. rewrite H. reflexivity. Qed.

Lemma set_prev_eq s p x pr : ltac2:(tb__ "0|2|
S3dS42S2A1S53Vs;Vp;A2S43S2Vx;A2A3S3dS3S0S44S46S0A2M0A2S39Vp;Vpr;Vs;A3S4S0G0S45S46S0S48S5eVp;S15Vx;Vpr;S50S42S1A1M1G1S13Vx;A1A3A3Vs;A3A4A3A3F_;").
Proof. intros H. unfold set_prev. rewrite (bind_eq _ _ s _ s (get_links_eq s p x H)). apply set_links_eq. exact H. Qed.

Lemma set_next_eq s p x nx : ltac2:(tb__ "0|2|
S3dS42S2A1S53Vs;Vp;A2S43S2Vx;A2A3S3dS3S0S44S46S0A2M0A2S38Vp;Vnx;Vs;A3S4S0G0S45S46S0S48S5eVp;S15Vx;S4eS42S1A1M1G1S13Vx;A1A3Vnx;A3Vs;A3A4A3A3F_;").
Proof. intros H. unfold set_next. rewrite (bind_eq _ _ s _ s (get_links_eq s p x H)). apply set_links_eq. exact H. Qed.

Lemma decay_bounces_eq sc s : ltac2:(tb__ "0|2|
S3dS3S0S44S46S0A2M0A2S26Vsc;Vs;A2S4S0G0S45S46S0S48S42S41A1S0Lx;ScVsc;A1S41S12R1S9Vs;A1M1A2S41S47S0L_;S64R1Z0A2Vs;S1fS1aR2S62R1Z1A2G1A3Vs;A2X47x2Tb;Lk;Vs;X42x2A4A3A3").
Proof. unfold decay_bounces. destruct (bounce_idx sc); reflexivity. Qed.

Definition act_of (am : ameta) : Z := ones (am_aidx am).
Definition am_activate (am : ameta) : ameta := ltac2:(tb__ "0|2|
S18S63S6Vam;A1M0S70Vam;A1M1A2S2cS67G0G1A2Vam;A2A2").

Lemma activate_group_eq s m am : ltac2:(tb__ "0|1|
S3dS42S2A1S53Vs;Vm;A2S43S2S5Vam;A1A2A3S3dS41S17Vam;A1Z0A3S3dS3S0S44S41S0A2M0A2S22Vm;Vs;A2S4S0G0S45S41S0S63S6Vam;A1S70Vam;A1A2S5eVm;S5S6fVam;A1A1Vs;A3A4A3A3F_;F_;").
Proof.
  intros H Hav. unfold activate_group.
  rewrite (bind_eq _ _ s _ s (getm_eq s m am H)).
  rewrite (bind_eq _ _ s tt s); [| apply massert_true_eq; apply Z.eqb_eq; exact Hav].
  rewrite (bind_eq _ _ s tt _ (setm_eq s m _)). reflexivity.
Qed.

Section Hit.
  Variables (s : astate) (sc : Z) (m0 : sptr) (am0 : ameta).
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S3dS42S1A1S54Vs;Vsc;A2S43S1Vm0;A2A3").
  Hypothesis HM0 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs;Vm0;A2S43S2S5Vam0;A1A2A3").
  Hypothesis Hav : am_avail am0 <> 0.

  Definition hit_first : Z := lowbit (am_avail am0).
  Definition hit_post : astate := ltac2:(tb__ "0|0|
S5eVm0;S5S18S62S17Vam0;A1S81A2Vam0;A2A1Vs;A3").

  Theorem ta_hit : ltac2:(tb__ "0|1|
S3dS3S0S44S41S0A2M0A2S14Vsc;Vs;A2S4S0G0S45S41S0S81S82A4A3A3").
  Proof using HM0 Hav Hhd.
    unfold try_avail.
    rewrite (bind_eq _ _ s _ s (get_head_eq s sc)). rewrite Hhd.
    rewrite (bind_eq _ _ s _ s (getm_eq s m0 am0 HM0)).
    replace (negb (am_avail am0 =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Hav).
    rewrite (bind_eq _ _ s tt _ (setm_eq s m0 _)). reflexivity.
  Qed.
End Hit.

Definition step1 (sc : Z) (m0 : sptr) (am0 : ameta) : M (option sptr) := ltac2:(tb__ "0|3|
S47S16S42S1A1M0A1L_;S64S6Vam0;A1Z0A2S7S46G0S1dSfVsc;A1M1Vm0;A2S46S28G1A1L_;A4S7S46G0S19G1S8Vam0;A1M2A2S46SeG0G2A2L_;A4X47x2").

Definition step2 (sc : Z) (m1 : sptr) (am1 : ameta) : M sptr := ltac2:(tb__ "0|1|
S47S16S1A1M0L_;S64S6Vam1;A1SdS11Vam1;A1A1A2S42S1A1G0Lx;S8Vam1;A1S1S7S46S1S19SfVsc;A1S43S1R1A2A2S46SeS1R2A2L_;A4Lnx;S27S1S21Z6A1A2X42x2SeS1Vm1;A2X47x2").

Definition span_cnt (am2 : ameta) : Z := ltac2:(tb__ "0|1|
S2dSaVam2;A1A1S41S65S10Vam2;A1Z2A2S41S3aU12cR1S65S2aS69R2R1A2A2R2A4S41S47S41L_;S6aS65S11Vam2;A1Z1A2M0R1A2G0R1X47x2Tcnt1;Tcnt0;Tsize;").

Definition step3 (sc : Z) (m2 : sptr) (am2 : ameta) : M sptr := ltac2:(tb__ "0|4|
S47S16S1A1M0L_;M1S64S63S6Vam2;A1SdS10Vam2;A1A1A2Z0A2G1S4fS34S8Vam2;A1M2S43S1Vm2;A2A2A1S42S1A1G0Lx;G2S1S7S46S1S19SfVsc;A1S43S1R1A2A2S46SeS1R2A2L_;A4Lnx;S27S1S21Z7A1A2X42x2S7S46S1S20Vm2;S24S62S74Vam2;A1Z1A2Vam2;A2A2S46SeS1Vm2;A2M3L_;A4X47x2G3X47x2").

Definition tail (m3 : sptr) : M Z := ltac2:(tb__ "0|1|
S7S41S41S22Vm3;A1S41S7S46S41S29S4fS64R1Z0A2A1Z3A2S46S7SbS41S1eVm3;A1M0SbS7S46S41S26SaR1A1A1S46S32R4A1S41S7SbS41G0SbS7S46S41S20Vm3;S18S62R6R2A2R1A2A2S46SeS41R3A2L_;A4Lam3;A4Tfirst;L_;A4Lam3;A4L_;A4Lmask;A4").

Lemma try_avail_unfold sc s m0 am0 : ltac2:(tb__ "0|3|
S3dS42S1A1M0S54Vs;Vsc;A2S43S1Vm0;A2A3S3dS42S2A1S53Vs;Vm0;A2S43S2S5Vam0;A1A2A3S3dS41S17Vam0;A1Z0M1A3S3dS3S0S44S41S0A2A2S14Vsc;Vs;A2S7G0S41S6cVsc;Vm0;Vam0;A3G0G0S16S41A1Lom1;R1S1S7SbS41S1eR1A1M2SbS7S1S41S6eVsc;R2R1A3S1S7SbS41G2SbS7S1S41S6dVsc;R2R1A3S1S76R1A1Lm3;A4Lam2;A4Lm2;A4Lam1;A4Lm1;SeS41G1A2X42x2Lom1;Vs;A5A3F_;F_;F_;").
Proof.
  intros Hhd HM0 Hav. unfold try_avail.
  rewrite (bind_eq _ _ s _ s (get_head_eq s sc)). rewrite Hhd.
  rewrite (bind_eq _ _ s _ s (getm_eq s m0 am0 HM0)).
  replace (negb (am_avail am0 =? 0)) with false by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; exact Hav).
  reflexivity.
Qed.

Lemma active_hd_upd_meta q x t c : ltac2:(tb__ "0|0|
S3dS42S1A1S54S5eVq;Vx;Vt;A3Vc;A2S54Vt;Vc;A2A3").
Proof. reflexivity. Qed.
Lemma MT_set_hd c v t q : ltac2:(tb__ "0|0|
S3dS42S2A1S53S5fVc;Vv;Vt;A3Vq;A2S53Vt;Vq;A2A3").
Proof. reflexivity. Qed.

Section Step1.
  Variables (s : astate) (sc : Z) (m0 : sptr) (am0 : ameta).
  Hypothesis HM0 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs;Vm0;A2S43S2S5Vam0;A1A2A3").

  Definition s1_rot : astate := ltac2:(tb__ "0|0|
S5fVsc;S8Vam0;A1Vs;A3").
  Lemma step1_rot : ltac2:(tb__ "0|2|
S3fS3dS41S6Vam0;A1Z0A3A1S3dS3S0S44S42S1A1M0S0A2M1A2S6cVsc;Vm0;Vam0;Vs;A4S4S0G1S45G0S0S8Vam0;A1S87A4A3A3F_;").
  Proof using .
    intros Hf. unfold step1. replace (am_freed am0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hf).
    rewrite (bind_eq _ _ s tt _ (set_head_eq s sc _)). reflexivity.
  Qed.

  Definition s1_empty : astate := ltac2:(tb__ "0|1|
S5eVm0;S5S25S49S1A1M0G0Vam0;A3A1S5fVsc;G0Vs;A3A3").
  Lemma dequeue_ring1 : ltac2:(tb__ "0|1|
S3dS42S1A1S8Vam0;A1S43S1Vm0;A2A3S3dS3S0S44S46S0A2M0A2S1dSfVsc;A1Vm0;Vs;A3S4S0G0S45S46S0S48S84A4A3A3F_;").
  Proof using HM0.
    intros Hn. unfold dequeue.
    rewrite (bind_eq _ _ s _ s (get_links_eq s m0 (MUsed am0) HM0)). cbn [links_of snd fst]. rewrite Hn.
    cbn [osptr_eqb]. rewrite sptr_eqb_refl.
    rewrite (bind_eq _ _ s tt _ (set_head_eq s sc None)).
    apply (set_links_eq _ m0 (MUsed am0)). rewrite MT_set_hd. exact HM0.
  Qed.
  Lemma step1_empty : ltac2:(tb__ "0|3|
S3dS41S6Vam0;A1Z0A3S3dS42S1A1M0S8Vam0;A1S43S1Vm0;A2A3S3dG0S54S5fVsc;S49S1A1M1Vs;A3Vsc;A2G1A3S3dS3S0S44G0S0A2M2A2S6cVsc;Vm0;Vam0;Vs;A4S4S0G2S45G0S0G1S84A4A3A3F_;F_;F_;").
  Proof using HM0.
    intros Hf Hn Hhd'. unfold step1. rewrite Hf. cbn [Z.eqb].
    rewrite (bind_eq _ _ s tt _ (dequeue_ring1 Hn)). rewrite get_head_eq. unfold s1_empty. rewrite active_hd_upd_meta, Hhd'. reflexivity.
  Qed.

  Variables (p0 n0 : sptr) (xp xn : mslot).
  Hypothesis Hprev : ltac2:(tb__ "0|0|
S3dS42S1A1S1cVam0;A1S43S1Vp0;A2A3").
  Hypothesis Hnext : ltac2:(tb__ "0|0|
S3dS42S1A1S8Vam0;A1S43S1Vn0;A2A3").
  Hypothesis Hn0 : n0 <> m0.
  Hypothesis Hp0 : p0 <> m0.
  Hypothesis HXp : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs;Vp0;A2S43S2Vxp;A2A3").

  Definition s1a : astate := ltac2:(tb__ "0|1|
S5eVp0;S15Vxp;S4eS42S1A1M0G0S13Vxp;A1A3S43S1Vn0;A2A3Vs;A3").
  Hypothesis HXn : ltac2:(tb__ "0|0|
S3dS42S2A1S53S85Vn0;A2S43S2Vxn;A2A3").
  Definition s1b : astate := ltac2:(tb__ "0|1|
S5eVn0;S15Vxn;S43S1Vp0;A2S50S42S1A1M0G0S13Vxn;A1A3A3S85A3").
  Definition s1_deq : astate := ltac2:(tb__ "0|1|
S5eVm0;S5S25S49S1A1M0G0Vam0;A3A1S5fVsc;S43S1Vn0;A2S86A3A3").
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S3dS42S1A1S54Vs;Vsc;A2S43S1Vm0;A2A3").

  Lemma dequeue_deq : ltac2:(tb__ "0|1|
S3dS3S0S44S46S0A2M0A2S1dSfVsc;A1Vm0;Vs;A3S4S0G0S45S46S0S48S83A4A3A3").
  Proof using HM0 HXn HXp Hhd Hn0 Hnext Hp0 Hprev.
    unfold dequeue.
    rewrite (bind_eq _ _ s _ s (get_links_eq s m0 (MUsed am0) HM0)). cbn [links_of fst snd]. rewrite Hprev, Hnext.
    cbn [osptr_eqb]. replace (sptr_eqb n0 m0) with false by (symmetry; apply sptr_eqb_neq; exact Hn0).
    rewrite (bind_eq _ _ s tt (set_hd sc (Some n0) s1b)).
    - apply (set_links_eq _ m0 (MUsed am0)). rewrite MT_set_hd. unfold s1b, s1a.
      rewrite MT_upd_other by (intros E; exact (Hn0 (eq_sym E))). rewrite MT_upd_other by (intros E; exact (Hp0 (eq_sym E))). exact HM0.
    - rewrite (bind_eq _ _ s tt s1a); [| apply (set_next_eq s p0 xp); exact HXp].
      rewrite (bind_eq _ _ s1a tt s1b); [| apply (set_prev_eq s1a n0 xn); exact HXn].
      rewrite (bind_eq _ _ s1b _ s1b (get_head_eq s1b sc)).
      unfold s1b, s1a. rewrite !active_hd_upd_meta, Hhd. cbn [osptr_eqb]. rewrite sptr_eqb_refl.
      apply set_head_eq.
  Qed.
  Lemma step1_deq : ltac2:(tb__ "0|3|
S3dS41S6Vam0;A1Z0A3S3dS42S1A1M0S54S5fVsc;S43S1Vn0;A2M1S86A3Vsc;A2G1A3S3dS3S0S44G0S0A2M2A2S6cVsc;Vm0;Vam0;Vs;A4S4S0G2S45G0S0G1S83A4A3A3F_;F_;").
  Proof using HM0 HXn HXp Hhd Hn0 Hnext Hp0 Hprev.
    intros Hf Hhd'. unfold step1. rewrite Hf. cbn [Z.eqb].
    rewrite (bind_eq _ _ s tt _ dequeue_deq). rewrite get_head_eq. unfold s1_deq. rewrite active_hd_upd_meta, Hhd'. reflexivity.
  Qed.
End Step1.

Section Step2.
  Variables (s1 : astate) (sc : Z) (m1 : sptr) (am1 : ameta).

  Lemma step2_stay : ltac2:(tb__ "0|1|
S3fS3dS41S6Vam1;A1SdS11Vam1;A1A1A3A1S3dS3S0S44S1S0A2M0A2S6eVsc;Vm1;Vam1;Vs1;A4S4S0G0S45S1S0Vm1;Vs1;A4A3A3F_;").
  Proof using . intros H. unfold step2. replace (am_freed am1 =? ones (am_last am1)) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity. Qed.

  Definition s2_skip (n1 : sptr) : astate := ltac2:(tb__ "0|0|
S5fVsc;S43S1Vn1;A2Vs1;A3").
  Lemma step2_skip n1 : ltac2:(tb__ "0|1|
S3dS41S6Vam1;A1SdS11Vam1;A1A1A3S3dS42S1A1S8Vam1;A1S43S1Vn1;A2A3S3dS3S0S44S1S0A2M0A2S6eVsc;Vm1;Vam1;Vs1;A4S4S0G0S45S1S0Vn1;S8aVn1;A1A4A3A3F_;F_;").
  Proof using .
    intros H Hn. unfold step2. rewrite H, Z.eqb_refl, Hn.
    rewrite (bind_eq _ _ s1 tt _ (set_head_eq s1 sc _)). reflexivity.
  Qed.
End Step2.

Section Step3.
  Variables (s2 : astate) (sc : Z) (m2 : sptr) (am2 : ameta).

  Lemma step3_hit : ltac2:(tb__ "0|1|
S3fS3dS41S63S6Vam2;A1SdS10Vam2;A1A1A2Z0A3A1S3dS3S0S44S1S0A2M0A2S6dVsc;Vm2;Vam2;Vs2;A4S4S0G0S45S1S0Vm2;Vs2;A4A3A3F_;").
  Proof using . intros H. unfold step3. replace (Z.land _ _ =? 0) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity. Qed.

  Definition s3_rot (n2 : sptr) : astate := ltac2:(tb__ "0|0|
S5fVsc;S43S1Vn2;A2Vs2;A3").
  Lemma step3_rot n2 : ltac2:(tb__ "0|1|
S3dS41S63S6Vam2;A1SdS10Vam2;A1A1A2Z0A3S3dS42S1A1S8Vam2;A1S43S1Vn2;A2A3S3fS3dS1Vn2;Vm2;A3A1S3dS3S0S44S1S0A2M0A2S6dVsc;Vm2;Vam2;Vs2;A4S4S0G0S45S1S0Vn2;S8bVn2;A1A4A3A3F_;F_;F_;").
  Proof using .
    intros H Hn Hne. unfold step3. rewrite H, Z.eqb_refl, Hn. cbn [osptr_eqb].
    replace (sptr_eqb n2 m2) with false by (symmetry; apply sptr_eqb_neq; exact Hne). cbn [negb].
    rewrite (bind_eq _ _ s2 tt _ (set_head_eq s2 sc _)). reflexivity.
  Qed.

  Definition s3_span : astate := ltac2:(tb__ "0|0|
S5eVm2;S5S24S62S74Vam2;A1Z1A2Vam2;A2A1Vs2;A3").
  Lemma step3_span : ltac2:(tb__ "0|1|
S3dS41S63S6Vam2;A1SdS10Vam2;A1A1A2Z0A3S3dS42S1A1S8Vam2;A1S43S1Vm2;A2A3S3dS3S0S44S1S0A2M0A2S6dVsc;Vm2;Vam2;Vs2;A4S4S0G0S45S1S0Vm2;S8cA4A3A3F_;F_;").
  Proof using .
    intros H Hn. unfold step3. rewrite H, Z.eqb_refl, Hn. cbn [osptr_eqb]. rewrite sptr_eqb_refl. cbn [negb].
    rewrite (bind_eq _ _ s2 tt _ (setm_eq s2 m2 _)). reflexivity.
  Qed.
End Step3.

Section Tail.
  Variables (s3 : astate) (m3 : sptr) (am3 : ameta).
  Hypothesis HM3 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs3;Vm3;A2S43S2S5Vam3;A1A2A3").
  Hypothesis Hav3 : am_avail am3 = 0.
  Definition t_mask : Z := ltac2:(tb__ "0|0|
S63S6Vam3;A1S70Vam3;A1A2").
  Hypothesis Hmask : t_mask <> 0.
  Definition t_first : Z := lowbit t_mask.

  Definition s4 : astate := ltac2:(tb__ "0|0|
S5eVm3;S5S6fVam3;A1A1Vs3;A3").

  Definition s5 : astate := ltac2:(tb__ "0|1|
S42S41A1S0Lx;ScSaVam3;A1A1S41S12R1S9S7bA1M0A2S41S47S0L_;S64R1Z0A2S7bS1fS1aR2S62R1Z1A2G0A3S7bA2X47x2Tb;Lk;S7bX42x2").
  Definition am_final : ameta := ltac2:(tb__ "0|0|
S18S62S80S7dA2S6fVam3;A1A2").
  Definition s6 : astate := ltac2:(tb__ "0|0|
S5eVm3;S5S7eA1S7cA3").

  Lemma MT_s5 q : ltac2:(tb__ "0|0|
S3dS42S2A1S53S7cVq;A2S53S7bVq;A2A3").
  Proof using . unfold s5. destruct (bounce_idx (am_sc am3)) as [k|]; [|reflexivity]. destruct (_ =? 0); reflexivity. Qed.

  Lemma tail_eq : ltac2:(tb__ "0|1|
S3dS3S0S44S41S0A2M0A2S76Vm3;Vs3;A2S4S0G0S45S41S0S7dS7fA4A3A3").
  Proof using HM3 Hav3 Hmask.
    unfold tail.
    rewrite (bind_eq _ _ s3 t_mask s4 (activate_group_eq s3 m3 am3 HM3 Hav3)).
    rewrite (bind_eq _ _ s4 tt s4); [| apply massert_true_eq; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Hmask].
    assert (M4 : MT s4 m3 = Some (MUsed (am_activate am3))) by (unfold s4; apply MT_upd_same).
    rewrite (bind_eq _ _ s4 _ s4 (getm_eq s4 m3 _ M4)).
    change (am_sc (am_activate am3)) with (am_sc am3).
    rewrite (bind_eq _ _ s4 tt s5); [| rewrite decay_bounces_eq; reflexivity].
    rewrite (bind_eq _ _ s5 _ s5 (getm_eq s5 m3 (am_activate am3) ltac:(rewrite MT_s5; exact M4))).
    rewrite (bind_eq _ _ s5 tt s6 (setm_eq s5 m3 _)). reflexivity.
  Qed.
End Tail.

Section Miss.
  Variables (s : astate) (sc : Z) (m0 : sptr) (am0 : ameta).
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S3dS42S1A1S54Vs;Vsc;A2S43S1Vm0;A2A3").
  Hypothesis HM0 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs;Vm0;A2S43S2S5Vam0;A1A2A3").
  Hypothesis Hav : am_avail am0 = 0.

  Theorem ta_empty : ltac2:(tb__ "0|4|
S3dS41S6Vam0;A1Z0M0A3S3dS42S1A1M1S8Vam0;A1S43S1Vm0;A2A3S3dG1S54S5fVsc;S49S1A1M2Vs;A3Vsc;A2G2A3S3dS3S0S44S41S0A2M3A2S14Vsc;Vs;A2S4S0G3S45S41S0G0S72Vs;Vsc;Vm0;Vam0;A4A4A3A3F_;F_;F_;").
  Proof using HM0 Hav Hhd.
    intros Hf Hn Hhd'. rewrite (try_avail_unfold sc s m0 am0 Hhd HM0 Hav).
    rewrite (bind_eq _ _ s None _ (step1_empty s sc m0 am0 HM0 Hf Hn Hhd')). reflexivity.
  Qed.

  Variables (m1 : sptr) (s1 : astate) (am1 : ameta) (m2 : sptr) (s2 : astate) (am2 : ameta) (m3 : sptr) (s3 : astate) (am3 : ameta).
  Hypothesis S1 : ltac2:(tb__ "0|2|
S3dS3S0S44S42S1A1M0S0A2M1A2S6cVsc;Vm0;Vam0;Vs;A4S4S0G1S45G0S0S43S1Vm1;A2Vs1;A4A3A3").
  Hypothesis HM1 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs1;Vm1;A2S43S2S5Vam1;A1A2A3").
  Hypothesis S2 : ltac2:(tb__ "0|1|
S3dS3S0S44S1S0A2M0A2S6eVsc;Vm1;Vam1;Vs1;A4S4S0G0S45S1S0Vm2;Vs2;A4A3A3").
  Hypothesis HM2 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs2;Vm2;A2S43S2S5Vam2;A1A2A3").
  Hypothesis S3 : ltac2:(tb__ "0|1|
S3dS3S0S44S1S0A2M0A2S6dVsc;Vm2;Vam2;Vs2;A4S4S0G0S45S1S0Vm3;Vs3;A4A3A3").
  Hypothesis HM3 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs3;Vm3;A2S43S2S5Vam3;A1A2A3").
  Hypothesis Hav3 : am_avail am3 = 0.
  Hypothesis Hmask : t_mask am3 <> 0.

  Theorem ta_miss : ltac2:(tb__ "0|1|
S3dS3S0S44S41S0A2M0A2S14Vsc;Vs;A2S4S0G0S45S41S0S75Vam3;A1S73Vs3;Vm3;Vam3;A3A4A3A3").
  Proof using HM0 HM1 HM2 HM3 Hav Hav3 Hhd Hmask S1 S2 S3.
    rewrite (try_avail_unfold sc s m0 am0 Hhd HM0 Hav).
    rewrite (bind_eq _ _ s (Some m1) s1 S1).
    rewrite (bind_eq _ _ s1 am1 s1 (getm_eq s1 m1 am1 HM1)).
    rewrite (bind_eq _ _ s1 m2 s2 S2).
    rewrite (bind_eq _ _ s2 am2 s2 (getm_eq s2 m2 am2 HM2)).
    rewrite (bind_eq _ _ s2 m3 s3 S3).
    exact (tail_eq s3 m3 am3 HM3 Hav3 Hmask).
  Qed.
End Miss.

Section MaskNZ.
  Variables (X : list sptr) (U : Z -> Z) (s : astate) (sc : Z) (m0 : sptr) (am0 : ameta).
  Hypothesis HI : ltac2:(tb__ "0|0|
S5bVX;S49S44S1S41A2A1VU;Vs;A4").
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S3dS42S1A1S54Vs;Vsc;A2S43S1Vm0;A2A3").
  Hypothesis HM0 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs;Vm0;A2S43S2S5Vam0;A1A2A3").
  Hypothesis Hav : am_avail am0 = 0.
  Variables (m1 : sptr) (s1 : astate) (am1 : ameta) (m2 : sptr) (s2 : astate) (am2 : ameta) (m3 : sptr) (s3 : astate) (am3 : ameta).
  Hypothesis S1 : ltac2:(tb__ "0|2|
S3dS3S0S44S42S1A1M0S0A2M1A2S6cVsc;Vm0;Vam0;Vs;A4S4S0G1S45G0S0S43S1Vm1;A2Vs1;A4A3A3").
  Hypothesis HM1 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs1;Vm1;A2S43S2S5Vam1;A1A2A3").
  Hypothesis S2 : ltac2:(tb__ "0|1|
S3dS3S0S44S1S0A2M0A2S6eVsc;Vm1;Vam1;Vs1;A4S4S0G0S45S1S0Vm2;Vs2;A4A3A3").
  Hypothesis HM2 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs2;Vm2;A2S43S2S5Vam2;A1A2A3").
  Hypothesis S3 : ltac2:(tb__ "0|1|
S3dS3S0S44S1S0A2M0A2S6dVsc;Vm2;Vam2;Vs2;A4S4S0G0S45S1S0Vm3;Vs3;A4A3A3").
  Hypothesis HM3 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs3;Vm3;A2S43S2S5Vam3;A1A2A3").
  Hypothesis Hav3 : am_avail am3 = 0.

  Theorem ta_mask_nz : t_mask am3 <> 0.
  Proof using HI HM0 HM1 HM2 HM3 Hav Hav3 Hhd Hsc S1 S2 S3.
    intros Hz.
    pose proof (try_avail_spec X U s sc (fun _ => True) HI Hsc ltac:(intros; exact I) ltac:(intros; exact I)) as T.
    rewrite (try_avail_unfold sc s m0 am0 Hhd HM0 Hav) in T.
    rewrite (bind_eq _ _ s (Some m1) s1 S1) in T.
    rewrite (bind_eq _ _ s1 am1 s1 (getm_eq s1 m1 am1 HM1)) in T.
    rewrite (bind_eq _ _ s1 m2 s2 S2) in T.
    rewrite (bind_eq _ _ s2 am2 s2 (getm_eq s2 m2 am2 HM2)) in T.
    rewrite (bind_eq _ _ s2 m3 s3 S3) in T.
    unfold tail in T. rewrite (bind_eq _ _ s3 (t_mask am3) (s4 s3 m3 am3) (activate_group_eq s3 m3 am3 HM3 Hav3)) in T.
    rewrite Hz in T. cbn [Z.eqb negb massert] in T. unfold bind, fail in T. cbn in T. exact T.
  Qed.
End MaskNZ.

Section Deltas.
  Variable s : astate.
  Hypothesis ND : List.NoDup (keys s).

  Lemma ND_sh (sc : Z) v : ltac2:(tb__ "0|0|
S8dS1S56S5fVsc;Vv;Vs;A3A1A2"). Proof using ND. exact ND. Qed.

  Lemma delta_hit m0 am0 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs;Vm0;A2S43S2S5Vam0;A1A2A3S60Vs;S77Vs;Vm0;Vam0;A3S61Vm0;A1A3F_;").
  Proof using ND. intros HM0. unfold hit_post. apply (delta_su_keep s m0 am0); [exact ND | exact HM0 | apply same_shape_avail | reflexivity]. Qed.

  Lemma delta_empty sc m0 am0 : ltac2:(tb__ "0|1|
S66Z0Vsc;A2S3dS42S2A1S53Vs;Vm0;A2S43S2S5Vam0;A1A2A3S60Vs;S72Vs;Vsc;Vm0;Vam0;A4S4aS55S4dS55S57S65S59S69Z8M0Vsc;A2A2A1S4bS55A1A3S4dS55S5cS35S1bVam0;A1G0A2A1S61Vm0;A1A3A3A3F_;F_;").
  Proof using ND.
    intros Hsc HM0. unfold s1_empty. eapply delta_trans; [apply delta_sh; exact Hsc|].
    apply (delta_su _ m0 am0); [exact ND | rewrite MT_set_hd; exact HM0 | apply same_shape_links].
  Qed.
End Deltas.

Section TailFacts.
  Variables (s3 : astate) (m3 : sptr) (am3 : ameta).
  Hypothesis ND3 : List.NoDup (keys s3).
  Hypothesis HM3 : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs3;Vm3;A2S43S2S5Vam3;A1A2A3").

  Let s4' : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S78Vs3;Vm3;Vam3;A3").
  Let s5' : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S79Vs3;Vm3;Vam3;A3").
  Let s6' : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S73Vs3;Vm3;Vam3;A3").

  Lemma MT_s4 q : ltac2:(tb__ "0|1|
S3dS42S2A1M0S53Vs4';Vq;A2S47G0L_;S3bVq;Vm3;A2S43S2S5S6fVam3;A1A1A2S53Vs3;Vq;A2X47x2A3").
  Proof using . unfold s4', s4. destruct (sptr_eq_dec q m3) as [->|H]; [rewrite sptr_eqb_refl; apply MT_upd_same |]. rewrite (proj2 (sptr_eqb_neq q m3) H). apply MT_upd_other; exact H. Qed.

  Lemma MT_s6_same : ltac2:(tb__ "0|0|
S3dS42S2A1S53Vs6';Vm3;A2S43S2S5S71Vam3;A1A1A2A3").
  Proof using s3. unfold s6', s6. apply MT_upd_same. Qed.
  Lemma MT_s6_other q : ltac2:(tb__ "0|0|
S3fS3dS1Vq;Vm3;A3A1S3dS42S2A1S53Vs6';Vq;A2S53Vs3;Vq;A2A3F_;").
  Proof using am3. intros H. unfold s6', s6. rewrite MT_upd_other by exact H. rewrite MT_s5. unfold s4. apply MT_upd_other. exact H. Qed.

  Lemma active_hd_s6 c : ltac2:(tb__ "0|0|
S3dS42S1A1S54Vs6';Vc;A2S54Vs3;Vc;A2A3").
  Proof using am3 m3.
    unfold s6', s6, s5, s4. rewrite active_hd_upd_meta.
    destruct (bounce_idx (am_sc am3)) as [k|]; [|apply active_hd_upd_meta].
    destruct (_ =? 0); [apply active_hd_upd_meta|]. etransitivity; [|apply (active_hd_upd_meta m3 (MUsed (am_activate am3)) s3 c)]. reflexivity.
  Qed.

  Lemma keys_s6 : ltac2:(tb__ "0|0|
S3dS4cS1A1S56Vs6';A1S56Vs3;A1A3").
  Proof using HM3 s4' s5'.
    pose proof (MT_Some_In_keys _ _ _ HM3) as K3.
    assert (K4 : keys s4' = keys s3) by (unfold s4', s4; apply keys_upd_In; exact K3).
    assert (K5 : keys s5' = keys s4').
    { unfold s5', s5. fold s4'. destruct (bounce_idx (am_sc am3)) as [k|]; [|reflexivity]. destruct (_ =? 0); reflexivity. }
    unfold s6', s6. fold s5'. rewrite keys_upd_In; [rewrite K5, K4; reflexivity|].
    rewrite K5, K4. exact K3.
  Qed.

  Lemma st_bounces_s4 : ltac2:(tb__ "0|0|
S3dS4cS41A1S9Vs4';A1S9Vs3;A1A3").
  Proof using am3 m3. reflexivity. Qed.

  Lemma s5_out : ltac2:(tb__ "0|0|
S3dS42S41A1ScSaVam3;A1A1S49S41A1A3S3dS0Vs5';Vs4';A3F_;").
  Proof using m3 s3. intros H. unfold s5', s5. rewrite H. reflexivity. Qed.
  Lemma s5_zero k : ltac2:(tb__ "0|0|
S3dS42S41A1ScSaVam3;A1A1S43S41Vk;A2A3S3dS41S12Vk;S9Vs3;A1A2Z0A3S3dS0Vs5';Vs4';A3F_;F_;").
  Proof using m3. intros H Hz. unfold s5', s5. rewrite H. fold s4'. rewrite st_bounces_s4, Hz. reflexivity. Qed.
  Lemma s5_dec k : ltac2:(tb__ "0|1|
S3dS42S41A1ScSaVam3;A1A1S43S41Vk;A2A3S3fS3dS41S12Vk;S9Vs3;A1A2M0Z0A3A1S3dS0Vs5';S1fS1aVk;S62G0Z1A2S9Vs4';A1A3Vs4';A2A3F_;F_;").
  Proof using m3.
    intros H Hz. unfold s5', s5. rewrite H. fold s4'. rewrite st_bounces_s4.
    replace (znth k (st_bounces s3) =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). reflexivity.
  Qed.

  Lemma st_bounces_s6_same : ltac2:(tb__ "0|0|
S3dS0Vs5';Vs4';A3S3dS4cS41A1S9Vs6';A1S9Vs3;A1A3F_;").
  Proof using am3 m3. intros E. unfold s6', s6. fold s5'. rewrite E. reflexivity. Qed.
  Lemma st_bounces_s6_dec k : ltac2:(tb__ "0|2|
S3dS42S41A1ScSaVam3;A1A1S43S41Vk;A2A3S3fS3dS41S12Vk;S9Vs3;A1M0A2M1Z0A3A1S3dS4cS41A1S9Vs6';A1S1aVk;S62G1Z1A2G0A3A3F_;F_;").
  Proof using s4' s5'. intros H Hz. unfold s6', s6. fold s5'. rewrite (s5_dec k H Hz). reflexivity. Qed.

  Lemma bounce_idx_some sc : ltac2:(tb__ "0|1|
S3eS66Z7M0Vsc;A2S68Vsc;Z27A2A2S3dS42S41A1ScVsc;A1S43S41S62Vsc;G0A2A2A3F_;").
  Proof using . intros H. unfold bounce_idx. replace ((7 <=? sc) && (sc <? 39))%bool with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
  Lemma bounce_idx_none sc : ltac2:(tb__ "0|0|
S3fS3eS66Z7Vsc;A2S68Vsc;Z27A2A2A1S3dS42S41A1ScVsc;A1S49S41A1A3F_;").
  Proof using . intros H. unfold bounce_idx. destruct (7 <=? sc) eqn:E1; [|reflexivity]. destruct (sc <? 39) eqn:E2; [|reflexivity]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply H. lia. Qed.

  Lemma delta_s4 : ltac2:(tb__ "0|0|
S60Vs3;Vs4';S61Vm3;A1A3").
  Proof using HM3 ND3. unfold s4', s4. apply (delta_su_keep s3 m3 am3); [exact ND3 | exact HM3 | | reflexivity]. unfold am_activate. eapply same_shape_trans; [apply same_shape_freed | apply same_shape_avail]. Qed.

  Lemma delta_s6_of l5 : ltac2:(tb__ "0|1|
S60Vs4';Vs5';Vl5;A3S60Vs3;Vs6';S4aS55S4aS55S61Vm3;A1M0Vl5;A3G0A3A3F_;").
  Proof using HM3 ND3.
    intros D5. unfold s6', s6. fold s5'.
    eapply delta_trans; [eapply delta_trans; [apply delta_s4 | exact D5]|].
    apply (delta_su_keep s5' m3 (am_activate am3)).
    - pose proof D5 as (_&_&_&_&_&_&K5&_). pose proof delta_s4 as (_&_&_&_&_&_&K4&_). rewrite K5, K4. exact ND3.
    - unfold s5'. rewrite MT_s5. apply MT_upd_same.
    - unfold am_final. apply same_shape_avail.
    - reflexivity.
  Qed.

  Lemma delta_s6_same : ltac2:(tb__ "0|1|
S3dS0Vs5';Vs4';A3S60Vs3;Vs6';S4aS55S4aS55S61Vm3;A1M0S4bS55A1A3G0A3A3F_;").
  Proof using HM3 ND3. intros E. apply delta_s6_of. rewrite E. apply delta_refl. Qed.

  Lemma delta_s6_dec k : ltac2:(tb__ "0|2|
S3dS42S41A1ScSaVam3;A1A1S43S41Vk;A2A3S66Z0M0Vk;A2S3fS3dS41S12Vk;S9Vs3;A1A2G0A3A1S60Vs3;Vs6';S4aS55S4aS55S61Vm3;A1M1S4dS55S57S65S5aVk;A2A1S4bS55A1A3A3G1A3A3F_;F_;F_;").
  Proof using HM3 ND3. intros H Hk Hz. apply delta_s6_of. rewrite (s5_dec k H Hz). rewrite <- st_bounces_s4. apply delta_sb. exact Hk. Qed.

  Lemma am_final_fields : ltac2:(tb__ "0|3|
S3eS3dS42S1A1M0S1cS71Vam3;A1M1A1S1cVam3;A1A3S3eS3dG0S8G1A1S8Vam3;A1A3S3eS3dS1S1bG1A1S1bVam3;A1A3S3eS3dS41S17G1A1S62S7aVam3;A1S75Vam3;A1A2A3S3eS3dS41S6G1A1S67S6Vam3;A1SdS10Vam3;A1M2A1A2A3S3eS3dS41S58G1A1S58Vam3;A1A3S3eS3dS41S10G1A1G2A3S3eS3dS41SaG1A1SaVam3;A1A3S3eS3dS41S11G1A1S11Vam3;A1A3S3dS41S23G1A1S23Vam3;A1A3A2A2A2A2A2A2A2A2A2").
  Proof using . unfold am_final, am_activate, act_of. repeat split; reflexivity. Qed.
End TailFacts.

Lemma delta_sh_same s sc : ltac2:(tb__ "0|2|
S66Z0Vsc;A2S40S3fS3dS42S1A1M0S54Vs;Vsc;A2M1S49S1A1A3A1S89S6bVsc;A1S51G0S3cVs;A1A2A2A2S60Vs;S5fVsc;G1Vs;A3S4bS55A1A3F_;F_;").
Proof.
  intros Hsc _. unfold delta. repeat split; try reflexivity.
  intros c Hc. left.
  assert (E : set_hd sc (active_hd s sc) s = s).
  { unfold set_hd, active_hd. destruct s; cbn. unfold set_active; cbn. f_equal.
    generalize (Z.to_nat sc) as i. clear. intros i. revert i.
    induction st_active as [|x t IH]; intros [|i]; cbn; try reflexivity. f_equal. apply IH. }
  rewrite E in Hc. exact Hc.
Qed.

Lemma alloc_slot_of_try_avail sc req s f s' fuel : ltac2:(tb__ "0|1|
S3dS3S0S44S41S0A2M0A2S14Vsc;Vs;A2S4S0G0S45S41S0Vf;Vs';A4A3A3S3fS3dS41Vf;Z0A3A1S88U1Vfuel;A2S5dG0S2bVfuel;Vsc;Vreq;Vs;A4S4bS44S31S41A2A1S45S41S0S2eVf;A1Vs';A4A4F_;F_;F_;").
Proof.
  intros E Hf Hfuel. destruct fuel as [|fuel']; [lia|]. cbn [alloc_slot].
  unfold bind. rewrite E. cbn [ibind]. replace (f =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hf). reflexivity.
Qed.
