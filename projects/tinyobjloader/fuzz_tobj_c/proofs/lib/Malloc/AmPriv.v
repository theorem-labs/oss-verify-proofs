(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "st_avail_meta_count"; "st_free_meta_head"; "st_init_done"; "st_meta_alloc_shift"; "HActive"; "try_avail"; "IRet"; "itree"; "new_region"; "account_bounce"; "activate_group"; "decay_bounces"; "dequeue"; "dequeue_head"; "queue"; "record_seq"; "region"; "st_regions"; "step_seq"; "upd_region"; "@Corelib.Init.Datatypes"; "prod"; "unit"; "bool"; "option"; "nat"; "pair"; "fst"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AmPriv"; "pq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.DrvReach"; "ct"; "full_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AmPam"; "am_private_same"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost"; "mm_pre"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLemmasBase DrvReach.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition pq {A} (c : Z) (b : bool) (hd : option sptr) (sh : Z) (r : A * astate) : Prop :=
  st_avail_meta_count (snd r) = c /\ st_init_done (snd r) = b /\ st_free_meta_head (snd r) = hd /\ st_meta_alloc_shift (snd r) = sh.

Create HintDb pt.
Hint Extern 1 (_ <= _) => lia : pt.
Hint Extern 1 (st_avail_meta_count _ = _) => cbn; first [assumption | reflexivity | congruence] : pt.
Hint Extern 1 (st_init_done _ = _) => cbn; first [assumption | reflexivity | congruence] : pt.
Hint Extern 1 (st_free_meta_head _ = _) => cbn; first [assumption | reflexivity | congruence] : pt.
Hint Extern 1 (st_meta_alloc_shift _ = _) => cbn; first [assumption | reflexivity | congruence] : pt.

Ltac pt_conseq_step :=
  let HQ := fresh "HQ" in
  eapply ct_conseq; [solve [eauto 6 with pt nocore] | intros [? ?] HQ;
    lazymatch type of HQ with
    | _ /\ _ = _ => let EQ := fresh "EQ" in destruct HQ as [HQ EQ]; cbn [fst snd] in EQ; try subst
    | _ => idtac
    end;
    lazymatch type of HQ with
    | pq _ _ _ _ _ => unfold pq in HQ; cbn [fst snd] in HQ; destruct HQ as (? & ? & ? & ?)
    | _ => cbn [fst snd] in HQ
    end ].

Ltac ptstep :=
  lazymatch goal with
  | |- ct (bind _ _ _) _ => apply ct_bind
  | |- ct (ret _ _) _ => apply ct_ret
  | |- ct (get _) _ => apply ct_get
  | |- ct (put _ _) _ => apply ct_put
  | |- ct (modify _ _) _ => apply ct_modify
  | |- ct (setm _ _ _) _ => unfold setm at 1; apply ct_modify
  | |- ct (setslot _ _ _) _ => unfold setslot at 1; apply ct_modify
  | |- ct (set_usage_of _ _ _) _ => unfold set_usage_of at 1; apply ct_modify
  | |- ct (set_head _ _ _) _ => unfold set_head at 1
  | |- ct (get_head _ _) _ => unfold get_head at 1
  | |- ct (getm _ _) _ => apply ct_getm; intros ? ?
  | |- ct (get_links _ _) _ => apply ct_get_links; intros ?
  | |- ct (set_links _ _ _ _) _ => apply ct_set_links; intros ?
  | |- ct (set_prev _ _ _) _ => unfold set_prev at 1
  | |- ct (set_next _ _ _) _ => unfold set_next at 1
  | |- ct (massert _ _ _) _ => let Hm := fresh "Hm" in apply ct_massert; intros Hm; try (exfalso; discriminate Hm)
  | |- ct (mcheck _ _ _) _ => apply ct_mcheck; intros ?
  | |- ct (ask _ _) _ => let z := fresh "z" in apply ct_ask; intros z; destruct (z =? 0); cbn [negb]
  | |- ct (askz _ _) _ => apply ct_askz; intros ?
  | |- ct (fail _ _) _ => apply ct_fail
  | |- ct (IFail _) _ => exact I
  | |- ct (IRet _) _ => cbn [ct]
  | |- ct (match ?x with _ => _ end _) _ => destruct x eqn:?
  | |- ct (match ?x with _ => _ end) _ => destruct x eqn:?
  | |- ct _ (fun _ => ct _ _) => pt_conseq_step
  | |- ct _ _ => solve [eauto 6 with pt nocore]
  | |- pq _ _ _ _ _ => unfold pq; cq_unf; cbn [st_free_meta_head st_meta_alloc_shift] in *; solve [repeat split; first [assumption | congruence | reflexivity | auto] ]
  | |- True => exact I
  | |- forall _, _ => intros ?
  | |- _ => solve [ct_leaf]
  end.
Ltac ptauto := repeat (cbn beta iota zeta delta [fst snd negb andb orb]; ptstep).

Section Prims.
Implicit Types (s : astate) (c : Z) (b : bool) (hd : option sptr) (sh : Z).

  Lemma pt_queue c b hd sh k m s : ltac2:(tb__ "0|0|
S0S2S5Vs;A1Vc;A3S0S1bS7Vs;A1Vb;A3S0S1cS4A1S6Vs;A1Vhd;A3S0S2S8Vs;A1Vsh;A3S22S19S1aS3A2S13S9Vk;A1Vm;Vs;A3S21S1aVc;Vb;Vhd;Vsh;A5A3F_;F_;F_;F_;").
  Proof. intros E1 E2 E3 E4. unfold queue. ptauto. Qed.
  Hint Resolve pt_queue : pt.

  Lemma pt_dequeue c b hd sh k m s : ltac2:(tb__ "0|0|
S0S2S5Vs;A1Vc;A3S0S1bS7Vs;A1Vb;A3S0S1cS4A1S6Vs;A1Vhd;A3S0S2S8Vs;A1Vsh;A3S22S19S1aS3A2S11S9Vk;A1Vm;Vs;A3S21S1aVc;Vb;Vhd;Vsh;A5A3F_;F_;F_;F_;").
  Proof. intros E1 E2 E3 E4. unfold dequeue. ptauto. Qed.
  Hint Resolve pt_dequeue : pt.

  Lemma pt_dequeue_head c b hd sh k s : ltac2:(tb__ "0|1|
S0S2S5Vs;A1Vc;A3S0S1bS7Vs;A1Vb;A3S0S1cS4A1M0S6Vs;A1Vhd;A3S0S2S8Vs;A1Vsh;A3S22S19G0S3A2S12S9Vk;A1Vs;A2S21G0Vc;Vb;Vhd;Vsh;A5A3F_;F_;F_;F_;").
  Proof. intros E1 E2 E3 E4. unfold dequeue_head. ptauto. Qed.
  Hint Resolve pt_dequeue_head : pt.

  Lemma pt_step_seq c b hd sh s : ltac2:(tb__ "0|0|
S0S2S5Vs;A1Vc;A3S0S1bS7Vs;A1Vb;A3S0S1cS4A1S6Vs;A1Vhd;A3S0S2S8Vs;A1Vsh;A3S22S19S1aS3A2S17Vs;A1S21S1aVc;Vb;Vhd;Vsh;A5A3F_;F_;F_;F_;").
  Proof. intros E1 E2 E3 E4. unfold step_seq. ptauto. destruct (st_seq s =? 255); cq_unf; cbn [st_free_meta_head st_meta_alloc_shift] in *; repeat split; assumption. Qed.
  Hint Resolve pt_step_seq : pt.

  Lemma pt_record_seq c b hd sh sc s : ltac2:(tb__ "0|0|
S0S2S5Vs;A1Vc;A3S0S1bS7Vs;A1Vb;A3S0S1cS4A1S6Vs;A1Vhd;A3S0S2S8Vs;A1Vsh;A3S22S19S1aS3A2S14Vsc;Vs;A2S21S1aVc;Vb;Vhd;Vsh;A5A3F_;F_;F_;F_;").
  Proof. intros E1 E2 E3 E4. unfold record_seq. destruct (bounce_idx sc); ptauto. Qed.
  Hint Resolve pt_record_seq : pt.

  Lemma pt_account_bounce c b hd sh sc s : ltac2:(tb__ "0|0|
S0S2S5Vs;A1Vc;A3S0S1bS7Vs;A1Vb;A3S0S1cS4A1S6Vs;A1Vhd;A3S0S2S8Vs;A1Vsh;A3S22S19S1aS3A2SeVsc;Vs;A2S21S1aVc;Vb;Vhd;Vsh;A5A3F_;F_;F_;F_;").
  Proof. intros E1 E2 E3 E4. unfold account_bounce. destruct (bounce_idx sc); ptauto. destruct (negb _ && _); cq_unf; cbn [st_free_meta_head st_meta_alloc_shift] in *; repeat split; assumption. Qed.
  Hint Resolve pt_account_bounce : pt.

  Lemma pt_decay_bounces c b hd sh sc s : ltac2:(tb__ "0|0|
S0S2S5Vs;A1Vc;A3S0S1bS7Vs;A1Vb;A3S0S1cS4A1S6Vs;A1Vhd;A3S0S2S8Vs;A1Vsh;A3S22S19S1aS3A2S10Vsc;Vs;A2S21S1aVc;Vb;Vhd;Vsh;A5A3F_;F_;F_;F_;").
  Proof. intros E1 E2 E3 E4. unfold decay_bounces. destruct (bounce_idx sc); ptauto. destruct (_ =? 0); cq_unf; cbn [st_free_meta_head st_meta_alloc_shift] in *; repeat split; assumption. Qed.
  Hint Resolve pt_decay_bounces : pt.

  Lemma pt_new_region c b hd sh k len s : ltac2:(tb__ "0|1|
S0S2S5Vs;A1Vc;A3S0S1bS7Vs;A1Vb;A3S0S1cS4A1S6Vs;A1Vhd;A3S0S2S8Vs;A1Vsh;A3S22S19S1dS3A2M0SdVk;Vlen;Vs;A3G0S1S21S1dVc;Vb;Vhd;Vsh;R1A6S0S1dS1fS1dS3R1A3S20S15S16Vs;A1A2A3A2Lr;A3F_;F_;F_;F_;").
  Proof. intros E1 E2 E3 E4. unfold new_region. ptauto. split; [|reflexivity]. unfold pq. cq_unf. cbn [st_free_meta_head st_meta_alloc_shift] in *. repeat split; assumption. Qed.
  Lemma pt_new_region' c b hd sh k len s : ltac2:(tb__ "0|0|
S0S2S5Vs;A1Vc;A3S0S1bS7Vs;A1Vb;A3S0S1cS4A1S6Vs;A1Vhd;A3S0S2S8Vs;A1Vsh;A3S22S19S1dS3A2SdVk;Vlen;Vs;A3S21S1dVc;Vb;Vhd;Vsh;A5A3F_;F_;F_;F_;").
  Proof. intros E1 E2 E3 E4. eapply ct_conseq; [apply (pt_new_region c b hd sh k len s E1 E2 E3 E4)|]. intros a [H _]. exact H. Qed.
  Hint Resolve pt_new_region' : pt.

  Lemma pt_upd_region c b hd sh r f s : ltac2:(tb__ "0|0|
S0S2S5Vs;A1Vc;A3S0S1bS7Vs;A1Vb;A3S0S1cS4A1S6Vs;A1Vhd;A3S0S2S8Vs;A1Vsh;A3S22S19S1aS3A2S18Vr;Vf;Vs;A3S21S1aVc;Vb;Vhd;Vsh;A5A3F_;F_;F_;F_;").
  Proof. intros E1 E2 E3 E4. unfold upd_region. ptauto. Qed.
  Hint Resolve pt_upd_region : pt.

  Lemma pt_activate_group c b hd sh m s : ltac2:(tb__ "0|0|
S0S2S5Vs;A1Vc;A3S0S1bS7Vs;A1Vb;A3S0S1cS4A1S6Vs;A1Vhd;A3S0S2S8Vs;A1Vsh;A3S22S19S2S3A2SfVm;Vs;A2S21S2Vc;Vb;Vhd;Vsh;A5A3F_;F_;F_;F_;").
  Proof. intros E1 E2 E3 E4. unfold activate_group. ptauto. Qed.
  Hint Resolve pt_activate_group : pt.

  Lemma pt_try_avail c b hd sh sc s : ltac2:(tb__ "0|0|
S0S2S5Vs;A1Vc;A3S0S1bS7Vs;A1Vb;A3S0S1cS4A1S6Vs;A1Vhd;A3S0S2S8Vs;A1Vsh;A3S22S19S2S3A2SaVsc;Vs;A2S21S2Vc;Vb;Vhd;Vsh;A5A3F_;F_;F_;F_;").
  Proof. intros E1 E2 E3 E4. unfold try_avail. ptauto. Qed.
  Hint Resolve pt_try_avail : pt.
End Prims.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import AmPam FreeNtPost AllocGroupPost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem try_avail_private sc s r s' : ltac2:(tb__ "0|1|
S0ScS3S19S2S3A2M0A2SaVsc;Vs;A2SbS3G0S1eS2S3Vr;Vs';A4A3A3S24Vs;Vs';A2F_;").
Proof.
  intros E.
  pose proof (pt_try_avail _ _ _ _ sc s eq_refl eq_refl eq_refl eq_refl) as C. rewrite E in C.
  destruct C as (C1 & C2 & C3 & C4). cbn [snd] in C1, C2, C3, C4. unfold am_private_same. rewrite C1, C2, C3, C4. repeat split; reflexivity.
Qed.

Theorem mm_pre_private sc s : ltac2:(tb__ "0|0|
S24Vs;S25Vsc;Vs;A2A2").
Proof.
  unfold mm_pre, am_private_same, seq_post, ab_post.
  destruct (bounce_idx sc) as [k|]; [destruct (negb _ && _)%bool|]; destruct (st_seq _ =? 255); destruct s; cbn; repeat split; reflexivity.
Qed.

Theorem try_avail_full0 sc s first s' : ltac2:(tb__ "0|1|
S23Vs;A1S0ScS3S19S2S3A2M0A2SaVsc;Vs;A2SbS3G0S1eS2S3Vfirst;Vs';A4A3A3S1S0S2Vfirst;Z0A3S23Vs';A1A2F_;F_;").
Proof.
  intros F E.
  assert (C : ct (try_avail sc s) (fun r => fst r = 0 /\ fq r)).
  { unfold try_avail. ftauto.

    1: { exfalso. match goal with H : MT _ ?g = Some (MUsed ?am) |- _ =>
           pose proof (F g am (mlookup_In _ _ _ H)) as G; unfold gfull in G;
           match goal with Hb : negb (am_avail am =? 0) = true |- _ => rewrite (proj1 G) in Hb; discriminate Hb end end. }
    all: split; [reflexivity | fq_leaf]. }
  pose proof (ct_yields _ _ [] (first, s') C) as Y. cbn [fst snd] in Y.
  apply Y. rewrite E. reflexivity.
Qed.
