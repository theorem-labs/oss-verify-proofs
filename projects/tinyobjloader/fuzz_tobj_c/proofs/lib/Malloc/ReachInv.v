(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "prod"; "unit"; "option"; "bool"; "list"; "Some"; "pair"; "nat"; "tt"; "None"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "mslot"; "ameta"; "am_aidx"; "MUsed"; "am_last"; "st_metas"; "alloc_meta"; "alloc_slot"; "kreq"; "st_avail_meta_count"; "st_init_done"; "try_avail"; "IRet"; "account_bounce"; "activate_group"; "alloc_group"; "area_from_brk"; "area_from_mmap"; "decay_bounces"; "dequeue"; "dequeue_head"; "enframe"; "free_meta"; "itree"; "modify"; "new_region"; "open_area"; "queue"; "record_seq"; "set_head"; "set_links"; "set_next"; "set_prev"; "set_usage_of"; "setm"; "setslot"; "step_seq"; "upd_region"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReachInv"; "mstable"; "mq"; "iq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.DrvReach"; "ct"; "cq"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_fields"; "reach_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "Inv"; "yields"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfArith MallocWfFrame MallocWfRings MallocWfSlot DrvReach NestTier.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition iq {A} (r : A * astate) : Prop := st_init_done (snd r) = true /\ 0 <= st_avail_meta_count (snd r).

Lemma it_cq {A} (m : M A) s : ltac2:(tb__ "0|2|
S33S3S39S33S16Vs;A1R2A3S39S3S17Vs;A1R2A3S37S0VA;SbA2M0Vm;Vs;A1M1S38VA;R4R3A3A3F_;F_;Fb;Fc;S36S1S6S1SbS8Vs;A4A2S37G0G1S36VA;A1A3F_;F_;").
Proof.
  intros H [Hi Hc]. cbn [snd] in Hi, Hc. eapply ct_conseq; [apply (H _ _ eq_refl Hi)|].
  intros [a s'] [C I]. cbn [fst snd] in C, I. split; cbn [snd]; [exact I | rewrite C; exact Hc].
Qed.

Lemma it_alloc_meta s : ltac2:(tb__ "0|1|
S3dZ0S16Vs;A1A2S37S0S2ScA1M0SbA2S13Vs;A1S36G0A1A3F_;").
Proof.
  intros Hc. eapply ct_conseq; [apply (ct_alloc_meta _ _ s eq_refl eq_refl Hc)|].
  intros [om s'] (I & C & _). split; [exact I | exact C].
Qed.

Ltac it_leaf := eapply it_cq; [intros; eauto with ct nocore | first [assumption | split; assumption]].

Lemma it_alloc_slot_group : ltac2:(tb__ "0|2|
S7S3aS33S33SbS36S1S6S1SbS8R1A4A2M0S37S0S33SbA2S14R5R4R3R2A4S36S33A1A3F_;Fs;Freq;Fsc;S33S33SbG0S37S0S2ScA1M1SbA2S1cR5R4R3R2A4S36G1A1A3F_;Fs;Freq;Fsc;A2Ffuel;").
Proof.
  induction fuel as [|fuel [IHs IHg]]; (split; [intros sc req s Hs | intros sc req s Hs]); cbn [alloc_slot alloc_group].
  - apply ct_fail.
  - apply ct_fail.
  - apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [first s1] H1. cbn [fst snd].
    destruct (negb (first =? 0)); [apply ct_ret; exact H1|].
    apply ct_bind. eapply ct_conseq; [apply IHg; exact H1|]. intros [og s2] H2. cbn [fst snd].
    destruct og; apply ct_ret; exact H2.
  - apply ct_bind. eapply ct_conseq; [apply it_alloc_meta; exact (proj2 Hs)|]. intros [om s1] H1. cbn [fst snd].
    destruct om as [m|]; [|apply ct_ret; exact H1].
    apply ct_bind. apply ct_get. cbn [fst snd].
    destruct (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s1 sc) + UNIT).
    +
      apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [[] s2] H2. cbn [fst snd].
      apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [[] s3] H3. cbn [fst snd].
      apply ct_bind. apply ct_ask. intros z. cbn [fst snd]. destruct (negb (negb (z =? 0))).
      * apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [[] s4] H4. cbn [fst snd]. apply ct_ret. exact H4.
      * apply ct_bind. eapply ct_conseq; [it_leaf|].
        intros [r s4] H4. cbn [fst snd].
        apply ct_bind. apply ct_get. cbn [fst snd]. apply ct_bind. apply ct_put. cbn [fst snd].
        apply ct_bind. eapply ct_conseq; [it_leaf|].
        intros [[] s5] H5. apply ct_ret. exact H5.
    +
      apply ct_bind. eapply ct_conseq; [apply IHs; exact H1|]. intros [idx s2] H2. cbn [fst snd].
      destruct (idx <? 0).
      * apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [[] s3] H3. apply ct_ret. exact H3.
      * apply ct_bind. unfold get_head. apply ct_bind. apply ct_get. cbn [fst snd]. apply ct_ret. cbn [fst snd].
        destruct (nth _ (st_active s2) None) as [g|]; [|apply ct_fail].
        apply ct_bind. apply ct_getm. intros amg _. cbn [fst snd].
        apply ct_bind. apply ct_mcheck. intros _. cbn [fst snd].
        apply ct_bind. apply ct_get. cbn [fst snd].
        apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [p s3] H3. cbn [fst snd].
        apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [[] s4] H4. apply ct_ret. exact H4.
Qed.

Theorem alloc_slot_init : ltac2:(tb__ "0|0|
S4ScA1S2S0ScS33A2A1S33S33F_;S7S33S33SbS4S0S15S33A2A1S33SbS42RaR9R8R4A4S3aS3dZ0R7A2S3eR7Z30A2A2S43S0S33SbA2S14R9R8R7R6A4R5S6S33SbR4R3A4A4S39S3S17R4A1SaA3F_;F_;F_;Fs';Fr;Fktr;Fs;Freq;Fsc;Ffuel;FU;FR;FX;").
Proof.
  intros X R U fuel sc req s ktr r s' HI Hsc HY.
  pose proof (inv_keys HI) as (_ & _ & K3 & _ & Kc).
  destruct (st_init_done s) eqn:Ei.
  - exact (proj1 (ct_yields _ _ ktr (r, s') (proj1 (it_alloc_slot_group fuel) sc req s (conj Ei (proj1 Kc))) HY)).
  -
    pose proof (inv_ctx HI) as (LenA &_&_&_&_&_&_&_&_&_&_& CI & _). destruct (CI Ei) as (M & A & B & AC).
    assert (Hhd : nth (Z.to_nat sc) (st_active s) None = None).
    { destruct (nth (Z.to_nat sc) (st_active s) None) as [g|] eqn:E; [|reflexivity]. exfalso.
      destruct (inv_rings HI) as (_ & AR & _). destruct (AR sc Hsc) as (ms & Rg & _).
      unfold active_hd in Rg. rewrite E in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin _].
      destruct (ring_members_used _ _ _ _ _ _ Rg Hin) as (am & Hu & _). pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
      pose proof (MT_Some_In_keys _ _ _ Mg) as K. unfold keys in K. rewrite M in K. exact K. }
    destruct fuel as [|fuel]; [destruct ktr; cbn in HY; contradiction|].
    refine (proj1 (ct_yields _ iq ktr (r, s') _ HY : iq (r, s'))). cbn [alloc_slot].
    apply ct_bind. unfold try_avail. apply ct_bind. unfold get_head. apply ct_bind. apply ct_get. cbn [fst snd].
    apply ct_ret. cbn [fst snd]. rewrite Hhd. apply ct_ret. cbn [fst snd Z.eqb negb].
    apply ct_bind. eapply ct_conseq.
    + destruct fuel as [|fuel]; cbn [alloc_group]; [apply ct_fail|].
      apply ct_bind. eapply ct_conseq; [apply it_alloc_meta; exact (proj1 Kc)|]. intros [om s1] H1. cbn [fst snd].

      revert om s1 H1.
      assert (G := proj2 (it_alloc_slot_group (S fuel)) sc req).

      clear G. intros om s1 H1.
      destruct om as [m|]; [|apply ct_ret; exact H1].
      apply ct_bind. apply ct_get. cbn [fst snd].
      destruct (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s1 sc) + UNIT).
      * apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [[] s2] H2. cbn [fst snd].
        apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [[] s3] H3. cbn [fst snd].
        apply ct_bind. apply ct_ask. intros z. cbn [fst snd]. destruct (negb (negb (z =? 0))).
        -- apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [[] s4] H4. cbn [fst snd]. apply ct_ret. exact H4.
        -- apply ct_bind. eapply ct_conseq; [it_leaf|].
           intros [rr s4] H4. cbn [fst snd].
           apply ct_bind. apply ct_get. cbn [fst snd]. apply ct_bind. apply ct_put. cbn [fst snd].
           apply ct_bind. eapply ct_conseq; [it_leaf|].
           intros [[] s5] H5. apply ct_ret. exact H5.
      * apply ct_bind. eapply ct_conseq; [apply (proj1 (it_alloc_slot_group fuel)); exact H1|]. intros [idx s2] H2. cbn [fst snd].
        destruct (idx <? 0).
        -- apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [[] s3] H3. apply ct_ret. exact H3.
        -- apply ct_bind. unfold get_head. apply ct_bind. apply ct_get. cbn [fst snd]. apply ct_ret. cbn [fst snd].
           destruct (nth _ (st_active s2) None) as [g|]; [|apply ct_fail].
           apply ct_bind. apply ct_getm. intros amg _. cbn [fst snd].
           apply ct_bind. apply ct_mcheck. intros _. cbn [fst snd].
           apply ct_bind. apply ct_get. cbn [fst snd].
           apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [p s3] H3. cbn [fst snd].
           apply ct_bind. eapply ct_conseq; [it_leaf|]. intros [[] s4] H4. apply ct_ret. exact H4.
    + intros [og s2] H2. cbn [fst snd]. destruct og; apply ct_ret; exact H2.
Qed.

Definition mstable (s0 s1 : astate) : Prop := ltac2:(tb__ "0|3|
ScSeS39S2SdA1M0S41Vs1;R2A2S5SdS10R1A1A2M1A3S3bSeSeS3aS39G0S41Vs0;R4A2G1A3S3aS39S0S0S0S33ScA2S33A2S33A2S3fR3A1S3fR1A1A3S3cS3dSfR1A1SfR3A1M2A2S3dS11R3A1G2A2A2A2A2Lam;A2F_;Fam';Fg;").

Lemma mstable_refl s : mstable s s.
Proof. intros g am' M. exists am'. split; [exact M|]. split; [reflexivity | left; lia]. Qed.

Lemma mstable_trans s0 s1 s2 : ltac2:(tb__ "0|0|
S34Vs0;Vs1;A2S34Vs1;Vs2;A2S34Vs0;Vs2;A2F_;F_;").
Proof.
  intros H1 H2 g am'' M''. destruct (H2 g am'' M'') as (am' & M' & F' & A').
  destruct (H1 g am' M') as (am & M & F & A). exists am. split; [exact M|]. split; [congruence|].
  unfold reach_fields in F, F'. injection F as E1 E2 E3 E4. injection F' as E1' E2' E3' E4'. lia.
Qed.

Lemma mstable_same_metas s0 s1 : ltac2:(tb__ "0|0|
S39S4S0ScSdA2A1S12Vs1;A1S12Vs0;A1A3S34Vs0;Vs1;A2F_;").
Proof. intros E g am' M. exists am'. unfold MT in *. rewrite E in M. split; [exact M|]. split; [reflexivity | left; lia]. Qed.

Lemma mstable_upd s g x : ltac2:(tb__ "0|2|
SeS39SdVx;S10R1A1M0A3S3bSeSeS3aS39S2SdA1S41Vs;Vg;A2S5SdG0A2A3S3aS39S0S0S0S33ScA2S33A2S33A2S3fR3A1S3fR1A1A3S3cS3dSfR1A1SfR3A1M1A2S3dS11R3A1G1A2A2A2A2Lam;A2F_;Fam';S34Vs;S44Vg;Vx;Vs;A3A2F_;").
Proof.
  intros H q am' M. destruct (sptr_eq_dec q g) as [->|NE].
  - rewrite MT_upd_same in M. injection M as ->. exact (H am' eq_refl).
  - rewrite (MT_upd_other g _ s q NE) in M. exists am'. split; [exact M|]. split; [reflexivity | left; lia].
Qed.

Theorem reach_ok_mstable s0 s1 : ltac2:(tb__ "0|0|
S34Vs0;Vs1;A2S40Vs0;A1S40Vs1;A1F_;F_;").
Proof.
  intros H [HH HP]. split.
  - intros g am' g' bm' i' M' Hml M2' Hi' Hmem.
    destruct (H g am' M') as (am & M & F & _). destruct (H g' bm' M2') as (bm & M2 & F2 & _).
    unfold reach_fields in F, F2. injection F as E1 E2 E3 E4. injection F2 as F1' F2' F3' F4'.
    rewrite F4'. apply (HH g am g' bm i' M); [congruence | exact M2 | rewrite <- F3'; exact Hi' |].
    rewrite <- E2, Hmem. unfold slot_start, stride_of. rewrite F1', F2', F3', F4'. reflexivity.
  - intros g am' M' Hlt. destruct (H g am' M') as (am & M & F & LE).
    unfold reach_fields in F. injection F as E1 E2 E3 E4. rewrite E4.
    destruct LE as [LE|LE]; [|lia].
    assert (Hlt0 : am_aidx am < am_last am) by lia.
    pose proof (HP g am M Hlt0) as X0. pose proof (class_size_nonneg (am_sc am)). nia.
Qed.

Definition mq (s0 : astate) {A} (r : A * astate) : Prop := mstable s0 (snd r).

Lemma mq_modify_metas s0 s f (Q := @mq s0 unit) : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S39S4S0ScSdA2A1S12Vf;Vs;A1A1S12Vs;A1A3S37S0S1SbA2S25Vf;Vs;A2VQ;A3F_;F_;").
Proof. intros H E. apply ct_modify. unfold mq. cbn [snd]. eapply mstable_trans; [exact H | apply mstable_same_metas; exact E]. Qed.

Ltac mq_same := unfold mq; cbn [fst snd];
  match goal with Hm : mstable ?a _ |- mstable ?a _ => apply (mstable_trans _ _ _ Hm); apply mstable_same_metas; reflexivity end.

Lemma mq_setslot s0 s p x : ltac2:(tb__ "0|2|
S34Vs0;Vs;A2SeS39SdVx;S10R1A1M0A3S3bSeSeS3aS39S2SdA1S41Vs;Vp;A2S5SdG0A2A3S3aS39S0S0S0S33ScA2S33A2S33A2S3fR3A1S3fR1A1A3S3cS3dSfR1A1SfR3A1M1A2S3dS11R3A1G1A2A2A2A2Lam;A2F_;Fam';S37S0S1SbA2S30Vp;Vx;Vs;A3S35Vs0;S1A2A3F_;F_;").
Proof.
  intros H Hx. unfold setslot. apply ct_modify. unfold mq. cbn [snd].
  eapply mstable_trans; [exact H|]. change (set_metas (mupdate (st_metas s) p x) s) with (upd_meta p x s). apply mstable_upd. exact Hx.
Qed.

Lemma mq_set_links s0 s p pr nx : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S2bVp;Vpr;Vnx;Vs;A4S35Vs0;S1A2A3F_;").
Proof.
  intros H. unfold set_links. apply ct_bind. apply ct_get. cbn [fst snd].
  destruct (mlookup (st_metas s) p) as [x|] eqn:M; [|apply ct_fail].
  apply mq_setslot; [exact H|]. intros am' E. destruct x as [| |am]; cbn in E; try discriminate E.
  injection E as <-. exists am. split; [unfold MT; rewrite M; reflexivity|]. split; [destruct am; reflexivity | left; destruct am; cbn; lia].
Qed.

Lemma mq_set_prev s0 s p pr : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S2dVp;Vpr;Vs;A3S35Vs0;S1A2A3F_;").
Proof. intros H. unfold set_prev. apply ct_bind. apply ct_get_links. intros l. cbn [fst snd]. destruct l. apply mq_set_links. exact H. Qed.
Lemma mq_set_next s0 s p nx : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S2cVp;Vnx;Vs;A3S35Vs0;S1A2A3F_;").
Proof. intros H. unfold set_next. apply ct_bind. apply ct_get_links. intros l. cbn [fst snd]. destruct l. apply mq_set_links. exact H. Qed.

Lemma mq_set_head s0 s h v : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S2aVh;Vv;Vs;A3S35Vs0;S1A2A3F_;").
Proof. intros H. unfold set_head. destruct h; apply ct_modify; mq_same. Qed.

Lemma mq_setm s0 s p am' : ltac2:(tb__ "0|1|
S34Vs0;Vs;A2S3bSeSeS3aS39S2SdA1S41Vs;Vp;A2S5SdS10R1A1A2A3S3aS39S0S0S0S33ScA2S33A2S33A2S3fVam';A1S3fR1A1A3S3cS3dSfR1A1SfVam';A1M0A2S3dS11Vam';A1G0A2A2A2A2Lam;A2S37S0S1SbA2S2fVp;Vam';Vs;A3S35Vs0;S1A2A3F_;F_;").
Proof. intros H Hx. unfold setm. change (ct (setslot p (MUsed am') s) (@mq s0 unit)). apply mq_setslot; [exact H|]. intros am'' E. injection E as <-. exact Hx. Qed.

Create HintDb mq.
Hint Resolve mq_set_links mq_set_prev mq_set_next mq_set_head : mq.

Ltac mq_side :=
  eexists; split; [eassumption | split; [match goal with |- reach_fields ?a = reach_fields ?b => destruct b; reflexivity end | ]];
  first [ left; match goal with |- am_aidx ?b <= am_aidx ?a => destruct b; cbn; lia end | idtac ].
Ltac mqstep :=
  lazymatch goal with
  | |- ct (bind _ _ _) _ => apply ct_bind
  | |- ct (ret _ _) _ => apply ct_ret
  | |- ct (get _) _ => apply ct_get
  | |- ct (put _ _) _ => apply ct_put
  | |- ct (get_head _ _) _ => unfold get_head at 1
  | |- ct (getm _ _) _ => apply ct_getm; intros ? ?
  | |- ct (get_links _ _) _ => apply ct_get_links; intros ?
  | |- ct (massert _ _ _) _ => let Hm := fresh "Hm" in apply ct_massert; intros Hm
  | |- ct (mcheck _ _ _) _ => apply ct_mcheck; intros ?
  | |- ct (ask _ _) _ => let z := fresh "z" in apply ct_ask; intros z
  | |- ct (askz _ _) _ => apply ct_askz; intros ?
  | |- ct (fail _ _) _ => apply ct_fail
  | |- ct (IFail _) _ => exact I
  | |- ct (IRet _) _ => cbn [ct]
  | |- ct (match ?x with _ => _ end _) _ => destruct x eqn:?
  | |- ct (match ?x with _ => _ end) _ => destruct x eqn:?
  | |- ct (modify _ _) (fun _ => ct _ _) => match goal with Hb : mstable ?b _ |- _ => eapply (ct_conseq _ (@mq b _)); [apply ct_modify; mq_same | cbv beta; let Hq := fresh "Hq" in intros [? ?] Hq; unfold mq in Hq; cbn [fst snd] in Hq] end
  | |- ct (modify _ _) _ => apply ct_modify; mq_same
  | |- ct (setm _ _ ?st) (fun _ => ct _ _) => eapply ct_conseq; [match goal with Hm : mstable _ st |- _ => apply (mq_setm _ _ _ _ Hm); mq_side end | cbv beta; let Hq := fresh "Hq" in intros [? ?] Hq; unfold mq in Hq; cbn [fst snd] in Hq]
  | |- ct (setm _ _ ?st) _ => match goal with Hm : mstable _ st |- _ => apply (mq_setm _ _ _ _ Hm); mq_side end
  | |- ct _ (fun _ => ct _ _) => eapply ct_conseq; [solve [eauto 3 with mq nocore] | cbv beta; let Hq := fresh "Hq" in intros [? ?] Hq; unfold mq in Hq; cbn [fst snd] in Hq]
  | |- ct _ _ => solve [eauto 3 with mq nocore]
  | |- mq _ _ => unfold mq; cbn [fst snd]; solve [eassumption | mq_same]
  | |- forall _, _ => intros ?
  end.
Ltac mqauto := repeat (cbn beta iota zeta delta [fst snd negb andb orb]; mqstep).

Lemma mq_queue s0 s h m : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S28Vh;Vm;Vs;A3S35Vs0;S1A2A3F_;").
Proof. intros H. unfold queue. mqauto. Qed.
Hint Resolve mq_queue : mq.
Lemma mq_dequeue s0 s h m : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S20Vh;Vm;Vs;A3S35Vs0;S1A2A3F_;").
Proof. intros H. unfold dequeue. mqauto. Qed.
Hint Resolve mq_dequeue : mq.
Lemma mq_dequeue_head s0 s h : ltac2:(tb__ "0|1|
S34Vs0;Vs;A2S37S0S2ScA1M0SbA2S21Vh;Vs;A2S35Vs0;G0A2A3F_;").
Proof. intros H. unfold dequeue_head. mqauto. Qed.
Hint Resolve mq_dequeue_head : mq.
Lemma mq_free_meta s0 s m : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S23Vm;Vs;A2S35Vs0;S1A2A3F_;").
Proof.
  intros H. unfold free_meta. apply ct_bind. eapply ct_conseq; [apply (mq_setslot s0 s); [exact H | intros am' E; discriminate E]|].
  cbv beta. intros [[] s1] H1. unfold mq in H1. cbn [snd] in H1. mqauto.
Qed.
Hint Resolve mq_free_meta : mq.
Lemma mq_step_seq s0 s : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S31Vs;A1S35Vs0;S1A2A3F_;").
Proof. intros H. unfold step_seq. apply ct_modify. unfold mq. cbn [snd]. destruct (st_seq s =? 255); mq_same. Qed.
Lemma mq_record_seq s0 s sc : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S29Vsc;Vs;A2S35Vs0;S1A2A3F_;").
Proof. intros H. unfold record_seq. destruct (bounce_idx sc); mqauto. Qed.
Lemma mq_account_bounce s0 s sc : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S1aVsc;Vs;A2S35Vs0;S1A2A3F_;").
Proof. intros H. unfold account_bounce. destruct (bounce_idx sc); [|mqauto]. apply ct_modify. unfold mq; cbn [snd]. destruct (_ && _); mq_same. Qed.
Lemma mq_decay_bounces s0 s sc : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S1fVsc;Vs;A2S35Vs0;S1A2A3F_;").
Proof. intros H. unfold decay_bounces. destruct (bounce_idx sc); [|mqauto]. apply ct_modify. unfold mq; cbn [snd]. destruct (_ =? 0); mq_same. Qed.
Lemma mq_new_region s0 s k len : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S7SbA2S26Vk;Vlen;Vs;A3S35Vs0;S7A2A3F_;").
Proof. intros H. unfold new_region. mqauto. Qed.
Lemma mq_upd_region s0 s r f : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S32Vr;Vf;Vs;A3S35Vs0;S1A2A3F_;").
Proof. intros H. unfold upd_region. mqauto. Qed.
Lemma mq_set_usage_of s0 s sc v : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S1SbA2S2eVsc;Vv;Vs;A3S35Vs0;S1A2A3F_;").
Proof. intros H. unfold set_usage_of. mqauto. Qed.
Hint Resolve mq_step_seq mq_record_seq mq_account_bounce mq_decay_bounces mq_new_region mq_upd_region mq_set_usage_of : mq.

Lemma mq_activate_group s0 s m : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S33SbA2S1bVm;Vs;A2S35Vs0;S33A2A3F_;").
Proof. intros H. unfold activate_group. mqauto. Qed.
Hint Resolve mq_activate_group : mq.

Local Opaque span_loop.
Lemma mq_try_avail s0 s sc : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S33SbA2S18Vsc;Vs;A2S35Vs0;S33A2A3F_;").
Proof.
  intros H. unfold try_avail. mqauto.
  all: match goal with |- _ <= am_aidx (am_set_aidx ?c ?b) \/ _ =>
         pose proof (span_loop_ge 300 (am_aidx b + 2) (UNIT + class_size (am_sc b) * (am_aidx b + 2)) (class_size (am_sc b))) as SG;
         destruct (am_last b + 1 <? _) eqn:EE; [apply Z.ltb_lt in EE; right | apply Z.ltb_ge in EE; left]; clear - SG EE; destruct b; cbn in *; lia end.
Qed.
Local Transparent span_loop.
Hint Resolve mq_try_avail : mq.

Lemma mq_area_from_brk s0 s : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S3SbA2S1dVs;A1S35Vs0;S3A2A3F_;").
Proof. intros H. unfold area_from_brk. mqauto. Qed.
Lemma mq_area_from_mmap s0 s : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S3SbA2S1eVs;A1S35Vs0;S3A2A3F_;").
Proof. intros H. unfold area_from_mmap. mqauto. Qed.
Lemma mq_open_area s0 s nu : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0S3SbA2S27Vnu;Vs;A2S35Vs0;S3A2A3F_;").
Proof. intros H. unfold open_area. mqauto. Qed.
Hint Resolve mq_area_from_brk mq_area_from_mmap mq_open_area : mq.

Lemma mq_alloc_meta s0 s : ltac2:(tb__ "0|1|
S34Vs0;Vs;A2S37S0S2ScA1M0SbA2S13Vs;A1S35Vs0;G0A2A3F_;").
Proof.
  intros H. unfold alloc_meta. mqauto.
  all: try (eapply ct_conseq; [apply (mq_setslot s0); [eassumption | intros am' E; discriminate E] | cbv beta; let Hq := fresh "Hq" in intros [? ?] Hq; unfold mq in Hq; cbn [fst snd] in Hq]; mqauto).
Qed.
Hint Resolve mq_alloc_meta : mq.

Lemma mq_enframe s0 s g idx n ctr k : ltac2:(tb__ "0|0|
S34Vs0;Vs;A2S37S0ScSbA2S22Vg;Vidx;Vn;Vctr;Vk;Vs;A6S35Vs0;ScA2A3F_;").
Proof.
  intros H. unfold enframe. mqauto.
Qed.
Hint Resolve mq_enframe : mq.

Theorem try_avail_reach : ltac2:(tb__ "0|1|
S4ScA1S33S33F_;SbS33S33SbS42R6S9S0ScS33A2A1R5R4A4S3aS3dZ0R4A2S3eR4Z30A2A2S40R6A1S39S24SbS0S33SbA2M0A2S18R6R7A2S19SbG0S6S33SbR5R4A4A3A3S40R5A1F_;F_;F_;F_;Fs';Fr;Fsc;Fs;FU;FX;").
Proof.
  intros X U s sc r s' _ _ HR E.
  pose proof (mq_try_avail s s sc (mstable_refl s)) as C. rewrite E in C. cbn [ct] in C.
  exact (reach_ok_mstable s s' C HR).
Qed.

Theorem alloc_meta_reach : ltac2:(tb__ "0|1|
S4ScA1S2S0ScS33A2A1S33S33F_;SbS4S0S15S33A2A1ScSbS42R7R6R5R4A4S40R5A1S43S0S2ScA1M0SbA2S13R6A1R5S6G0SbS5ScR4A2R3A4A4S40R4A1F_;F_;F_;Fs';Fm;Fktr;Fs;FU;FR;FX;").
Proof.
  intros X R U s ktr m s' _ HR HY.
  exact (reach_ok_mstable s s' (ct_yields _ _ ktr (Some m, s') (mq_alloc_meta s s (mstable_refl s)) HY) HR).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
