(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "ameta"; "mslot"; "UNIT"; "MUsed"; "am_last"; "class_size"; "IB"; "am_sc"; "PGSZ"; "am_maplen"; "am_mem"; "slot_start"; "stride_of"; "alloc_slot"; "am_aidx"; "kreq"; "size_to_class"; "alloc_group"; "ask"; "bind"; "fail"; "get"; "ibind"; "initial_cnt"; "install_group"; "put"; "st_init_done"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "mul"; "div"; "eqb"; "ltb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReachSlot"; "wt"; "Xfree"; "group_postR"; "slot_postR"; "@Corelib.Init.Datatypes"; "prod"; "Some"; "option"; "bool"; "pair"; "snd"; "unit"; "None"; "list"; "fst"; "cons"; "nat"; "negb"; "true"; "orb"; "tt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "Inv"; "active_hd"; "usedX"; "yields"; "WF"; "zseq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase"; "itok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.DrvReach"; "ct"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "nested_host_classes"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "heads_below"; "new_am"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith"; "icands"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReachInv"; "mstable"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocLayout MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfArith MallocWfFrame MallocWfRingOps MallocWfSurgery MallocWfRings MallocWfMeta MallocWfSlot MallocWfGeom MallocWfGroup DrvReach NestTier ReachInv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma itok_ct_conj {A} (t : itree astate A) (Q : A -> Prop) (P : A -> Prop) : ltac2:(tb__ "0|0|
S48VA;Vt;VQ;A3S49VA;Vt;VP;A3S48VA;Vt;VA;S1eVQ;R1A1VP;R1A1A2La;A3F_;F_;").
Proof.
  induction t as [a | q sp k IH | f]; cbn; intros HQ HP; [split; assumption | | exact HQ].
  destruct HQ as [R K]. split; [exact R|]. intros z Hz. apply IH; [apply K; exact Hz | apply HP].
Qed.

Lemma itok_use_ct {A} (t : itree astate A) (P Q : A -> Prop) : ltac2:(tb__ "0|0|
S49VA;Vt;VP;A3S48VA;Vt;VA;VP;R1A1VQ;R2A1F_;La;A3S48VA;Vt;VQ;A3F_;F_;").
Proof. intros HP HQ. eapply itok_mono; [| exact (itok_ct_conj t _ P HQ HP)]. intros a [H1 H2]. exact (H1 H2). Qed.

Definition Xfree (X : list sptr) (s : astate) : Prop := ltac2:(tb__ "0|0|
S2S3S4bS2R2VX;A3S20S1fS32S4A1S41Vs;R3A2S31S4S6R2A1A2A3A1F_;Fam;Fx;").

Lemma Xfree_nil s : Xfree [] s. Proof. intros x am []. Qed.
Lemma Xfree_mstable X s s' : ltac2:(tb__ "0|0|
S52Vs;Vs';A2S2dVX;Vs;A2S2dVX;Vs';A2F_;F_;").
Proof. intros M F x am Hx E. destruct (M x am E) as (am0 & E0 & _). exact (F x am0 Hx E0). Qed.
Lemma Xfree_cons X m s : ltac2:(tb__ "0|0|
S2dVX;Vs;A2S3S20S1fS32S4A1S41Vs;Vm;A2S31S4S6R1A1A2A3A1Fam;S2dS3aS2Vm;VX;A3Vs;A2F_;F_;").
Proof. intros F Hm x am [<-|Hx]; [apply Hm | apply F; exact Hx]. Qed.
Lemma Xfree_tail X m s : ltac2:(tb__ "0|0|
S2dS3aS2Vm;VX;A3Vs;A2S2dVX;Vs;A2F_;").
Proof. intros F x am Hx. apply F. right. exact Hx. Qed.
Lemma used_of_MUsed X s g am : ltac2:(tb__ "0|0|
S2dVX;Vs;A2S1fS32S4A1S41Vs;Vg;A2S31S4S6Vam;A1A2A3S44VX;Vs;Vg;Vam;A4F_;F_;").
Proof.
  intros F M. unfold usedX, MTX. destruct (memb g X) eqn:E; [|exact M]. exfalso.
  exact (F g am (proj1 (memb_In _ _) E) M).
Qed.

Lemma reach_ok_install' s m am_new : ltac2:(tb__ "0|4|
S23Z0M0SfVam_new;A1A2S2S3S0S1fS32S4A1S41Vs;R3A2S31S4S6R2A1A2A3M1S1fS0ScR3A1G0A3S1eS23G0R3A2S23R3S7Vam_new;A1M2A2A2S20S1fS2SdR5A1SeVam_new;R4A2A3A1F_;F_;F_;Fi;Fam;Fg;S1fS0ScVam_new;A1G0A3S2S3S0G1S1eS23G0R2A2S23R2S7R3A1A2A2S1fS2SdVam_new;A1SeR4R3A2A3S4bS0SaR5A1S4aA3F_;F_;F_;Fi';Fam';Fg';F_;S25S11Vam_new;A1M3G2A2S25S26SbS5A2S27S8SaVam_new;A1A1S24G3Z2A2A2A2F_;S40Vs;A1S40S51Vm;S6Vam_new;A1Vs;A3A1F_;F_;F_;F_;F_;").
Proof.
  intros Hst Hnonest Hhost Hpart [HH HP]. split.
  - intros g am g' am' i' M Hml M' Hi' Emem.
    destruct (sptr_eq_dec g m) as [->|NE]; destruct (sptr_eq_dec g' m) as [->|NE'].
    + rewrite MT_upd_same in M, M'. injection M as <-. injection M' as <-. exfalso.
      unfold slot_start in Emem. destruct (am_mem am_new) as [r o]. cbn [padd] in Emem. injection Emem as E.
      assert (0 <= stride_of am_new * i') by nia. unfold UNIT in E. lia.
    + rewrite MT_upd_same in M. injection M as <-. rewrite (MT_upd_other m _ s g' NE') in M'.
      exact (Hhost Hml g' am' i' M' Hi' Emem).
    + rewrite MT_upd_same in M'. injection M' as <-. rewrite (MT_upd_other m _ s g NE) in M.
      exfalso. exact (Hnonest g am i' M Hml Hi' Emem).
    + rewrite (MT_upd_other m _ s g NE) in M. rewrite (MT_upd_other m _ s g' NE') in M'. exact (HH g am g' am' i' M Hml M' Hi' Emem).
  - intros g am M Hlt. destruct (sptr_eq_dec g m) as [->|NE].
    + rewrite MT_upd_same in M. injection M as <-. exact (Hpart Hlt).
    + rewrite (MT_upd_other m _ s g NE) in M. exact (HP g am M Hlt).
Qed.

Lemma install_reach s m sc cnt aidx maplen mem sl : ltac2:(tb__ "0|5|
S4fVmem;Vsc;Vcnt;Vaidx;Vmaplen;Vsl;A6S3S40Vs;A1S23Z0M0SfR2A1A2S2S3S0S1fS32S4A1M1S41Vs;R3A2S31S4S6R2A1A2M2A3M3S1fS0ScR3A1G0A3S1eS23G0R3A2S23R3S7R8A1A2A2S20S1fS2SdR5A1SeR9R4A2A3A1F_;F_;F_;Fi;Fam;Fg;S1fS0ScR4A1G0A3S2S3S0G3S1eS23G0R2A2S23R2S7R3A1A2A2S1fS2SdRaA1SeR4R3A2A3S4bS0SaR5A1S4aA3F_;F_;F_;Fi';Fam';Fg';F_;S25S11R5A1S7R5A1A2S25S26SbS5A2S27S8SaR6A1A1S24S11R6A1Z2A2A2A2F_;S49S30S36S1A2M4S1bVm;Vsc;Vcnt;Vaidx;Vmaplen;Vmem;Vsl;Vs;A8G4S1eS40S35S36S1R1A3A1S2S3S20S1fS2R2Vm;A3A1S1fG1S41S35S36S1R4A3R3A2G2A3S21S3S3S1fG1S41Vs;R5A2S31S4S6R1A1A2A3La0;A2F_;F_;Fa;Fx;A2Lr;A3F_;F_;F_;F_;F_;Tam1;").
Proof.
  intros am1 HR Hst Hnonest Hhost Hpart.
  unfold install_group. apply ct_bind. apply ct_get. cbn [fst snd].
  apply ct_bind. unfold set_usage_of. apply ct_modify. cbn [fst snd].
  set (s1 := set_usage _ s).
  assert (EM1 : forall g, MT s1 g = MT s g) by (intros g; reflexivity).
  apply ct_bind. unfold setm. apply ct_modify. cbn [fst snd].
  lazymatch goal with |- ct (queue ?h ?p _) ?Q => change (ct (queue h p (upd_meta m (MUsed am1) s1)) Q) end.
  assert (HR2 : reach_ok (upd_meta m (MUsed am1) s1)).
  { apply reach_ok_install'; [exact Hst | intros g am i M; rewrite EM1 in M; exact (Hnonest g am i M)
      | intros Hml g' am' i' M'; rewrite EM1 in M'; exact (Hhost Hml g' am' i' M') | exact Hpart
      | apply (reach_ok_same_metas s); [reflexivity | exact HR]]. }
  eapply ct_conseq; [apply (mq_queue _ _ (HActive sc) m (mstable_refl _))|].
  intros [[] s3] M3. unfold mq in M3. cbn [snd] in M3. split; [exact (reach_ok_mstable _ _ M3 HR2)|].
  cbn [snd]. intros x a Hx M. destruct (M3 x a M) as (a0 & M0 & _).
  rewrite (MT_upd_other m _ s1 x Hx), EM1 in M0. exists a0. exact M0.
Qed.

Lemma mm_aidx_partial sc cnt : ltac2:(tb__ "0|5|
S1eS23Z0M0Vsc;A2S25Vsc;Z30A2A2S23Z1M1Vcnt;A2S26S28S26Z1000S5A2S8Vsc;A1M2A2G1A2S0S33S0L_;M3S2aS26Vcnt;G1A2M4R1A2G4R1X33x2S0G3S2aR1G0A2G0R1X33x2S0S25R1G4A2S25S26SbS5A2S27G2S24R2Z2A2A2A2F_;Taidx;Ta1;Ta0;F_;F_;").
Proof.
  intros Hsc Hcnt a0 a1 aidx Hlt. pose proof (class_size_bounds sc Hsc) as [S16 _].
  change (4096 - UNIT) with 4080 in a0. change (PGSZ - UNIT) with 4080.
  pose proof (Z.mul_succ_div_gt 4080 (class_size sc) ltac:(lia)) as D.
  pose proof (Z.div_pos 4080 (class_size sc) ltac:(lia) ltac:(lia)) as D0.
  assert (Da : 4080 < class_size sc * (a0 + 2)) by (subst a0; replace (4080 / class_size sc - 1 + 2) with (Z.succ (4080 / class_size sc)) by lia; exact D).
  subst aidx a1.
  destruct (cnt - 1 <? a0) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1].
  - destruct (cnt - 1 <? 0) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]; lia.
  - destruct (a0 <? 0) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]; [|exact Da].
    subst a0. nia.
Qed.

Lemma nested_host_tab : ltac2:(tb__ "0|1|
S1fS33S4cS0S0S4cS0S0S3eS3cS2bS24S27S8R2A1M0R1A2S5A2S28SbZ2A2A2A1S4dS0S29S13S26S24S5S27R1G0A2A2S9A2A1A1S4aA3A2Lcnt;S50R1A1A3Lsc;S47Z0Z30A2A3S3dA3").
Proof. vm_compute. reflexivity. Qed.

Lemma nested_host sc u : ltac2:(tb__ "0|2|
S1eS23Z0Vsc;A2S25Vsc;Z30A2A2S23S24S27S8Vsc;A1M0S1aVsc;Vu;A2M1A2S5A2S28SbZ2A2A2S4bS0S13S26S24S5S27G1G0A2A2S9A2A1S4aA3F_;F_;").
Proof.
  intros Hsc Hn.
  pose proof nested_host_tab as T. rewrite forallb_forall in T.
  specialize (T sc ltac:(apply In_zseq; lia)). rewrite forallb_forall in T. specialize (T _ (initial_cnt_In sc u)).
  apply Bool.orb_prop in T as [T|T].
  - apply Bool.negb_true_iff in T. apply Z.leb_gt in T. lia.
  - apply existsb_exists in T as (h & Hh & E). apply Z.eqb_eq in E. rewrite E. exact Hh.
Qed.

Fixpoint wt {A : Type} (t : itree astate A) (Q : A -> Prop) : Prop :=
  match t with
  | IRet a => Q a
  | IFail _ => True
  | IAsk q snap k => forall z, answer_ok q z -> wt (k z) Q
  end.

Lemma wt_yields {A} (t : itree astate A) Q tr a : ltac2:(tb__ "0|0|
S2cVA;Vt;VQ;A3S45VA;Vt;Vtr;Va;A4VQ;Va;A1F_;F_;").
Proof.
  revert tr. induction t as [a' | q sp k IH | f]; intros tr H Y; destruct tr as [|[q' z] tr]; cbn in Y; try contradiction.
  - subst a'. exact H.
  - destruct Y as (-> & Az & Y). apply (IH z tr); [apply H; exact Az | exact Y].
Qed.

Lemma wt_conseq {A} (t : itree astate A) (Q Q' : A -> Prop) : ltac2:(tb__ "0|0|
S2cVA;Vt;VQ;A3VA;VQ;R1A1VQ';R2A1F_;Fa;S2cVA;Vt;VQ';A3F_;F_;").
Proof. induction t as [a | q sp k IH | f]; intros H HQ; cbn in *; [apply HQ, H | | exact I]. intros z Hz. apply IH; [apply H; exact Hz | exact HQ]. Qed.

Lemma wt_ibind {A B} (x : itree astate A) (K : A -> itree astate B) Q : ltac2:(tb__ "0|0|
S2cVA;Vx;VA;S2cVB;VK;R1A1VQ;A3La;A3S2cVB;S19S1VA;VB;Vx;VK;A5VQ;A3F_;").
Proof. induction x as [a | q sp k IH | f]; intros H; cbn in *; [exact H | | exact I]. intros z Hz. apply IH. apply H. exact Hz. Qed.

Lemma wt_ct {A} (t : itree astate A) Q : ltac2:(tb__ "0|0|
S49VA;Vt;VQ;A3S2cVA;Vt;VQ;A3F_;").
Proof. induction t as [a | q sp k IH | f]; cbn; intros H; [exact H | | exact I]. intros z _. apply IH. apply H. Qed.

Lemma wt_itok {A} (t : itree astate A) Q : ltac2:(tb__ "0|0|
S48VA;Vt;VQ;A3S2cVA;Vt;VQ;A3F_;").
Proof. induction t as [a | q sp k IH | f]; cbn; intros H; [exact H | | exact I]. intros z Hz. apply IH. apply (proj2 H). exact Hz. Qed.

Lemma wt_conj {A} (t : itree astate A) (Q1 Q2 : A -> Prop) : ltac2:(tb__ "0|0|
S2cVA;Vt;VQ1;A3S2cVA;Vt;VQ2;A3S2cVA;Vt;VA;S1eVQ1;R1A1VQ2;R1A1A2La;A3F_;F_;").
Proof.
  induction t as [a | q sp k IH | f]; cbn; intros H1 H2; [split; assumption | | exact I].
  intros z Hz. apply IH; [apply H1 | apply H2]; exact Hz.
Qed.

Lemma wt_frame {A} (t : itree astate A) (P Q : A -> Prop) : ltac2:(tb__ "0|0|
S49VA;Vt;VP;A3S48VA;Vt;VA;VP;R1A1VQ;R2A1F_;La;A3S2cVA;Vt;VQ;A3F_;F_;").
Proof.
  intros HP HQ. eapply wt_conseq; [exact (wt_conj t _ _ (wt_ct t P HP) (wt_itok t _ HQ))|].
  intros a [H1 H2]. exact (H2 H1).
Qed.

Section WtRules.
  Context {A B : Type}.
  Implicit Types (s : astate).
  Lemma wt_ret (a : A) s Q : Q (a, s) -> wt (ret a s) Q.
  Proof using . intros H. exact H. Qed.
  Lemma wt_bind (m : M B) (k : B -> M A) s Q : ltac2:(tb__ "0|2|
S2cS30VB;S1A2M0Vm;Vs;A1G0S2cS30VA;S1A2M1Vk;S39VB;S1R1A3S35VB;S1R1A3A2VQ;A3Lr;A3S2cG1S16VB;VA;Vm;Vk;Vs;A5VQ;A3F_;").
  Proof using . intros H. unfold bind. apply wt_ibind. eapply wt_conseq; [exact H|]. intros [b s']. cbn. intros X; exact X. Qed.
  Lemma wt_fail f s Q : ltac2:(tb__ "0|0|
S2cS30VA;S1A2S17VA;Vf;Vs;A3VQ;A3").
  Proof using . exact I. Qed.
  Lemma wt_get s (Q : astate * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S34S1S1Vs;Vs;A4A1S2cS30S1S1A2S18Vs;A1VQ;A3F_;").
  Proof using . intros H; exact H. Qed.
  Lemma wt_put s s' (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S34S36S1S3fVs';A4A1S2cS30S36S1A2S1cVs';Vs;A2VQ;A3F_;").
  Proof using . intros H; exact H. Qed.
  Lemma wt_ask q s (Q : bool * astate -> Prop) : ltac2:(tb__ "0|0|
S0VQ;S34S33S1S3cS29R1Z0A2A1Vs;A4A1Fz;S2cS30S33S1A2S15Vq;Vs;A2VQ;A3F_;").
  Proof using . intros H z _. cbn. apply H. Qed.
End WtRules.

Ltac wbinds := repeat lazymatch goal with |- wt (bind _ _ _) _ => apply wt_bind end.

Ltac mqin H := unfold mq in H; cbn [fst snd] in H.

Definition slot_postR (X : list sptr) (U : Z -> Z) (s : astate) (sc req : Z) (r : Z * astate) : Prop := ltac2:(tb__ "0|3|
S1eS4eVs;S35S0S1Vr;A3M0Vsc;A3S1eS1eS40G0A1S2dVX;G0A2A2S22S1eS1fS0S39S0S1Vr;A3M1N1A3S42VX;S37S30S2S0A2M2A1VU;G0A4A2S1eS23Z0G1A2S21S2S2S21S3S3S1eS42VX;S31G2S34S2S0R2G1A4A2VU;G0A4S1eS1fS32S2A1S43G0Vsc;A2S31S2R2A2A3S1eS44VX;G0R2R1A4S1eS1fS0SaR1A1Vsc;A3S1eS23S24Vreq;S9A2SfR1A1A2S23G1S7R1A1A2A2A2A2A2A2Lam;A2Lg;A2A2A2A2A2").

Definition group_postR (X : list sptr) (U : Z -> Z) (s : astate) (sc req : Z) (r : option sptr * astate) : Prop := ltac2:(tb__ "0|4|
S1eS4eVs;S35S32S2A1M0S1Vr;A3M1Vsc;A3S1eS1eS40G1A1S2dVX;G1A2A2G0OLx;S39G0S1Vr;A3S2S21S3S3S1eS42VX;S31S30S2S0A2M2S34S2S0R2Z0M3A4A2VU;G1A4S1eS1fG0S43G1Vsc;A2S31S2R2A2A3S1eS44VX;G1R2R1A4S1eS1fS0SaR1A1Vsc;A3S1eS23S24Vreq;S9A2SfR1A1A2S23G3S7R1A1A2A2A2A2A2A2Lam;A2Lm;S42VX;S37G2A1VU;G1A4X32x2A2A2").

Theorem alloc_reach fuel : ltac2:(tb__ "0|b|
S1eS38S2A1M0S0S0F_;M1S1S0S0S30S0S1A2M2OF_;S42R6S37S30S2S0A2A1R5R4A4M3S2dR7R5A2M4S40R6A1M5S1eS23Z0R6A2M6S25R6Z30A2A2M7G6S23S24R7S9A2S8R8A1A2M8G2S2fRdRcRbRaR9R1A6R9R2A1F_;Fr;S2cG2S10Vfuel;RaR9RbA4R8A3F_;F_;F_;F_;F_;F_;F_;FQ;Freq;Fsc;Fs;FU;FX;G0G1S1S0S0S30S32S2A1M9S1A2MaOF_;G3G4G5G7G6G8S1fG9S43RaR9A2S37S2A1A3GaS2eReRdRcRbRaR1A6RaR2A1F_;Fr;S2cGaS14Vfuel;RbRaRcA4R9A3F_;F_;F_;F_;F_;F_;F_;F_;FQ;Freq;Fsc;Fs;FU;FX;A2").
Proof.
  induction fuel as [|f [IHs IHg]].
  { split; intros; exact I. }
  split.
  -
    intros X U s sc req Q HI HXf HR Hsc Hreq Hfit HQ.
    cbn fix beta iota delta [alloc_slot]. wbinds.
    eapply wt_frame; [apply (mq_try_avail s s sc (mstable_refl s))|].
    eapply try_avail_spec; [exact HI | exact Hsc | |].
    + intros s1 HI1 Hhd1 EH1 UB1. msimp. intros M1. mqin M1. cbn [Z.eqb negb]. wbinds.
      eapply IHg; [exact HI1 | exact (Xfree_mstable _ _ _ M1 HXf) | exact (reach_ok_mstable _ _ M1 HR)
                 | exact Hsc | exact Hreq | exact Hfit | exact Hhd1 |].
      intros [og s2] [HB [[HR2 HX2] Hpost]]. msimp. cbn [fst snd] in HB, HR2, HX2, Hpost.
      assert (HB' : heads_below s s2 sc) by (intros c Hc; rewrite (HB c Hc); apply EH1; lia).
      destruct og as [g|].
      * apply wt_ret. apply HQ; unfold group_postR, slot_postR; cbn [fst snd]; split; [exact HB'|]. split; [split; [exact HR2 | exact HX2]|]. right. cbn [fst snd]. split; [lia|].
        destruct Hpost as (am & H1 & H2 & H3 & H4 & H5 & H6). exists g, am. repeat (split; [assumption|]). exact H6.
      * apply wt_ret. apply HQ; unfold group_postR, slot_postR; cbn [fst snd]; split; [exact HB'|]. split; [split; [exact HR2 | exact HX2]|]. left. split; [reflexivity | exact Hpost].
    + intros first s1 (Hnz & g & am & HI1 & Hhd1 & U1 & Sc1 & Str1 & Hidx & EH1 & UB1). msimp. intros M1. mqin M1.
      destruct (first =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|]. cbn [negb].
      apply wt_ret. apply HQ; unfold group_postR, slot_postR; cbn [fst snd]; split; [intros c Hc; apply EH1; lia|].
      split; [split; [exact (reach_ok_mstable _ _ M1 HR) | exact (Xfree_mstable _ _ _ M1 HXf)]|]. right. cbn [fst snd].
      split; [lia|]. exists g, am. repeat (split; [assumption|]). split; [lia | lia].
  -
    intros X U s sc req Q HI HXf HR Hsc Hreq Hfit Hhd HQ.
    pose proof (class_size_bounds sc Hsc) as [S16 Smax].
    cbn fix beta iota delta [alloc_group]. wbinds.
    eapply wt_frame; [apply (mq_alloc_meta s s (mstable_refl s))|].
    eapply alloc_meta_spec; [exact HI | |].
    { intros s1 HI1 Fr1 EU1 UB1. msimp. intros M1. mqin M1. apply wt_ret. apply HQ; unfold group_postR, slot_postR; cbn [fst snd]; split;
        [|split; [split; [exact (reach_ok_mstable _ _ M1 HR) | exact (Xfree_mstable _ _ _ M1 HXf)] | exact HI1]].
      intros c Hc. destruct Fr1 as (EA & _). unfold active_hd. rewrite EA. reflexivity. }
    intros m s1 HI1 NX Km Mm Fr1 EU1 UB1. msimp. intros M1. mqin M1.
    assert (HR1 : reach_ok s1) by exact (reach_ok_mstable _ _ M1 HR).
    assert (HXf1 : Xfree (m :: X) s1).
    { apply Xfree_cons; [exact (Xfree_mstable _ _ _ M1 HXf)|]. intros am E. destruct Mm as [Mm|Mm]; rewrite Mm in E; discriminate E. }
    clear M1.
    wbinds. apply wt_get. msimp. cbn zeta.
    pose proof Fr1 as (EA1 & EUs1 & _ & Len1 & Emc1).
    assert (Hhd1 : active_hd s1 sc = None) by (unfold active_hd; rewrite EA1; exact Hhd).
    pose proof (initial_cnt_facts sc (usage_of s1 sc) Hsc) as (Hc0 & Hc0s & Hc026).
    set (cnt0 := initial_cnt sc (usage_of s1 sc)) in *.
    assert (FRESH : forall q a, usedX (m :: X) s1 q a -> (prid (am_mem a) < length (st_regions s1))%nat).
    { intros q a Hu. apply EU1 in Hu. pose proof (used_group_prid_lt _ _ _ _ q a HI Hu). lia. }
    destruct (PGSZ / 2 <? class_size sc * cnt0 + UNIT) eqn:Ebr.
    +
      set (plan := mmap_plan s1 sc req cnt0 (usage_of s1 sc)).
      destruct plan as [cnt needed] eqn:Ep. subst plan. cbn [fst snd].
      pose proof (mmap_plan_facts s1 sc req cnt0 (usage_of s1 sc) cnt needed Hsc Hc0 Hc0s Hreq Hfit Hc026 Ep)
        as (Hcnt & Hcs & Hc26 & Nmod & N4096 & Nmax & Nfit & Nreq & Npr).
      wbinds. eapply wt_frame; [apply (mq_account_bounce s1 s1 sc (mstable_refl s1))|].
      eapply account_bounce_spec; [exact HI1|]. intros s2 HI2 (Em2 & Ea2 & Er2 & Eu2 & Ec2 & _). msimp. intros M2. mqin M2.
      wbinds. eapply wt_frame; [apply (mq_step_seq s1 s2 M2)|].
      eapply step_seq_spec; [exact HI2|]. intros s3 HI3 (Em3 & Ea3 & Er3 & Eu3 & Ec3 & _). msimp. intros M3. mqin M3.
      wbinds. apply wt_ask. intros z. msimp.
      assert (EU3 : forall q a, usedX (m :: X) s3 q a <-> usedX (m :: X) s1 q a).
      { intros q a. unfold usedX, MTX, MT. rewrite Em3, Em2. tauto. }
      destruct (z =? 0); cbn [negb].
      *
        wbinds. eapply wt_frame; [apply (mq_free_meta s1 s3 m M3)|].
        eapply free_meta_spec; [exact HI3 | left; reflexivity |]. intros s4 HI4 Sb4 Ea4 EU4 UB4. msimp. intros M4. mqin M4.
        apply wt_ret. apply HQ; unfold group_postR, slot_postR; cbn [fst snd]; split; [|split].
        -- intros c Hc. unfold active_hd. rewrite Ea4, Ea3, Ea2, EA1. reflexivity.
        -- split; [exact (reach_ok_mstable _ _ M4 HR1) | exact (Xfree_tail _ m _ (Xfree_mstable _ _ _ M4 HXf1))].
        -- cbn [fst snd]. rewrite (remove_head_notin m X NX) in HI4. exact HI4.
      *
        rewrite (page_round_fixed needed Nmod).
        wbinds. eapply wt_frame; [apply (mq_new_region s1 s3 RkMap needed M3)|].
        eapply new_region_spec; [exact HI3 | | reflexivity | unfold PGSZ in N4096; lia]. intros s4 HI4 Es4. msimp. intros M4. mqin M4.
        wbinds. apply wt_get. msimp. wbinds. apply wt_put. msimp.
        set (r := length (st_regions s3)).
        set (s5 := set_mmap_counter (Z.land (st_mmap_counter s4 + 1) (2 ^ 32 - 1)) s4).
        pose proof (inv_ctx HI4) as (_&_&_&_&_&_&_&_&C9&_).
        assert (HI5 : Inv (m :: X) None U s5) by (apply Inv_set_mmap_counter; [exact HI4 | apply land32_range; lia]).
        assert (EU5 : forall q a, usedX (m :: X) s5 q a <-> usedX (m :: X) s1 q a).
        { intros q a. rewrite <- EU3. unfold usedX, MTX, MT. subst s5 s4. cbn. tauto. }
        assert (M5 : mstable s1 s5).
        { apply (mstable_trans _ _ _ M4). apply mstable_same_metas. subst s5 s4. reflexivity. }
        assert (HXf5 : Xfree (m :: X) s5) by exact (Xfree_mstable _ _ _ M5 HXf1).
        assert (Hr5 : region_of s5 r = Some (mkRegion RkMap needed [] true)).
        { subst s5 s4 r. unfold region_of. cbn [st_regions set_mmap_counter set_regions]. apply region_of_app_new. }
        set (aidx := if (if cnt - 1 <? (4096 - UNIT) / class_size sc - 1 then cnt - 1 else (4096 - UNIT) / class_size sc - 1) <? 0 then 0
                     else if cnt - 1 <? (4096 - UNIT) / class_size sc - 1 then cnt - 1 else (4096 - UNIT) / class_size sc - 1).
        assert (Haidx : 0 <= aidx <= cnt - 1).
        { subst aidx. destruct (cnt - 1 <? (4096 - UNIT) / class_size sc - 1) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1];
            (destruct (_ <? 0) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]); lia. }
        assert (Hml : 1 <= needed / 4096).
        { apply Z.div_le_lower_bound; unfold PGSZ in *; lia. }
        assert (Hml' : needed / 4096 * 4096 = needed).
        { pose proof (Z_div_mod_eq_full needed 4096). unfold PGSZ in Nmod. lia. }
        wbinds. eapply wt_frame.
        { apply (install_reach s5 m sc cnt aidx (needed / 4096) (SP r 0) slot_zero).
          - apply (reach_ok_mstable _ _ M5 HR1).
          - rewrite new_am_stride. destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)); unfold UNIT; lia.
          - intros q a i Mq _ _ Emem. apply (used_of_MUsed (m :: X) s5 q a HXf5) in Mq. apply EU5 in Mq.
            pose proof (FRESH q a Mq) as Hlt. pose proof (f_equal prid Emem) as Epm.
            rewrite prid_slot_start in Epm. cbn [am_mem new_am prid] in Epm. rewrite <- Er2, <- Er3 in Hlt. subst r. lia.
          - cbn [am_maplen new_am]. intros H0. exfalso. lia.
          - cbn [am_aidx am_last am_sc new_am]. exact (mm_aidx_partial sc cnt Hsc ltac:(clear -Hcnt; lia)). }
        eapply (install_group_spec X U s5 m sc cnt aidx (needed / 4096) (SP r 0) slot_zero).
        -- exact HI5.
        -- exact NX.
        -- exact Hsc.
        -- exact Hcnt.
        -- exact Haidx.
        -- lia.
        -- unfold active_hd. subst s5 s4. cbn [st_active set_mmap_counter set_regions]. rewrite Ea3, Ea2. exact Hhd1.
        -- left. split; [reflexivity | lia].
        --
           right. cbn [am_sc am_last am_maplen new_am]. rewrite new_am_stride.
           split; [exact Hsc|]. split; [|split].
           ++ intros Hlt. destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
              ** apply andb_prop in E as [E _]. apply Z.eqb_eq in E. split; [exact E|]. rewrite new_am_allocated by lia. reflexivity.
              ** lia.
           ++ intros H26. right. specialize (Hc26 H26). lia.
           ++ destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
              ** apply andb_prop in E as [E _]. apply Z.eqb_eq in E. rewrite E. unfold UNIT. lia.
              ** replace (cnt - 1 + 1) with cnt by lia. exact Hcs.
        --
           intros _. exists r, (mkRegion RkMap needed [] true). cbn [am_mem am_maplen am_last new_am rg_kind rg_live rg_len].
           split; [reflexivity|]. split; [exact Hr5|]. split; [reflexivity|]. split; [reflexivity|].
           rewrite new_am_stride. unfold PGSZ. split; [lia|]. split.
           { destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
             ++ apply andb_prop in E as [E _]. apply Z.eqb_eq in E. rewrite E. unfold UNIT. lia.
             ++ destruct (Z.eq_dec cnt 1) as [->|Hne1].
                { exfalso. cbn [Z.sub Z.eqb] in E. destruct (needed / 4096 =? 0) eqn:E2; [apply Z.eqb_eq in E2; lia | discriminate]. }
                replace (cnt - 1 + 1) with cnt by lia. specialize (Nfit ltac:(lia)). lia. }
           cbn [am_sc new_am]. intros Hl0 _. specialize (Npr ltac:(lia)). unfold PGSZ in Npr |- *. lia.
        -- intros H0. lia.
        -- intros q a Hu Hp. exfalso. apply EU5 in Hu. pose proof (FRESH q a Hu). cbn [prid] in Hp. rewrite <- Er2, <- Er3 in H. subst r. lia.
        -- intros _ q a Hu _ Hp. apply EU5 in Hu. pose proof (FRESH q a Hu). cbn [prid] in Hp. rewrite <- Er2, <- Er3 in H. subst r. lia.
        -- intros s6 HI6 Hhd6 U6 EH6 Er6 Ec6 UB6. msimp. intros [HR6 HK6]. cbn [snd] in HR6, HK6.
           apply wt_ret. apply HQ; unfold group_postR, slot_postR; cbn [fst snd]; split; [|split].
           ++ intros c Hc. rewrite (EH6 c ltac:(lia) ltac:(lia)). unfold active_hd. subst s5 s4. cbn [st_active set_mmap_counter set_regions].
              rewrite Ea3, Ea2, EA1. reflexivity.
           ++ split; [exact HR6|].

              intros x ax Hx Mx. destruct (sptr_eq_dec x m) as [->|Hxm].
              { apply (proj1 (memb_false_notIn m X) NX). exact Hx. }
              destruct (HK6 x ax Hxm Mx) as [a0 M0]. exact (HXf5 x a0 (or_intror Hx) M0).
           ++ cbn [fst snd]. eexists. split; [exact HI6|]. split; [exact Hhd6|]. split; [exact U6|].
              pose proof (links_fields (Some m) (Some m) (new_am (SP r 0) sc cnt aidx (needed / 4096) slot_zero)) as (_ & Ll & Ls & _).
              rewrite Ls, Ll. cbn [am_sc am_last new_am]. split; [reflexivity|]. split; [|lia].
              rewrite (strip_stride _ (new_am (SP r 0) sc cnt aidx (needed / 4096) slot_zero)) by (unfold strip; reflexivity).
              rewrite new_am_stride. destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)); unfold UNIT, IB in *; lia.
    +
      apply Z.ltb_ge in Ebr.
      pose proof (nested_facts sc cnt0 Hsc ltac:(lia) Hc026 Ebr) as NF. cbv zeta in NF.
      destruct NF as (H23 & Hc2 & Htot & Hj & Hj48 & Hjfit & Hjlt).
      set (total := UNIT + cnt0 * class_size sc - IB) in *. set (j := size_to_class total) in *.
      wbinds.
      eapply (IHs (m :: X) U s1 j total); [exact HI1 | exact HXf1 | exact HR1 | exact Hj48 | lia | exact Hjfit |].
      intros [idx s2] [HB2 [[HR2 HX2] Hpost]]. msimp. cbn [fst snd] in HB2, HR2, HX2, Hpost.
      destruct (idx <? 0) eqn:Eneg.
      *
        apply Z.ltb_lt in Eneg. destruct Hpost as [[_ HI2] | [Hge _]]; [|cbn [fst] in Hge; lia]. cbn [snd] in HI2.
        wbinds. eapply wt_frame; [apply (mq_free_meta s2 s2 m (mstable_refl s2))|].
        eapply free_meta_spec; [exact HI2 | left; reflexivity |]. intros s3 HI3 Sb3 Ea3 EU3 UB3. msimp. intros M3. mqin M3.
        apply wt_ret. apply HQ; unfold group_postR, slot_postR; cbn [fst snd]; split; [|split].
        -- intros c Hc. pose proof (HB2 c ltac:(lia)) as E. unfold active_hd in E |- *. rewrite Ea3, E, EA1. reflexivity.
        -- split; [exact (reach_ok_mstable _ _ M3 HR2) | exact (Xfree_tail _ m _ (Xfree_mstable _ _ _ M3 HX2))].
        -- cbn [fst snd]. rewrite (remove_head_notin m X NX) in HI3. exact HI3.
      * apply Z.ltb_ge in Eneg. destruct Hpost as [[Hm1 _] | [_ (g & am & HI2 & Hhd2 & U2 & Sc2 & Str2 & Hidx2)]]; [cbn [fst] in Hm1; lia|].
        cbn [fst snd] in HI2, Hhd2, U2, Hidx2, HB2.
        wbinds. apply wt_itok. apply itok_get_head. msimp. change (nth (Z.to_nat j) (st_active s2) None) with (active_hd s2 j). rewrite Hhd2. msimp.
        pose proof (inv_groups HI2 g am U2) as G2. pose proof G2 as ((_ & _ & Glen & _) & Gml & _ & Gcl & _).
        assert (Hstr : stride_of am = class_size j).
        { destruct Gcl as [(C63 & _) | (_ & _ & C26 & _)]; [lia|]. specialize (C26 ltac:(lia)).
          unfold stride_of. rewrite Sc2. destruct C26 as [C|C]; [rewrite C|].
          - destruct (am_last am =? 0); reflexivity.
          - destruct (am_last am =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
        wbinds. apply wt_itok. eapply itok_getm; [exact (proj1 (usedX_MT _ _ _ _ U2))|]. msimp.
        wbinds. apply wt_itok. apply itok_mcheck; [rewrite Hstr; apply Z.eqb_refl|]. msimp.
        wbinds. apply wt_get. msimp.
        pose proof (inv_ctx HI2) as (_&_&_&_&_&_&_&_&C9&_).
        wbinds. eapply wt_frame; [apply (mq_enframe s2 s2 g idx (class_size j - IB) (st_mmap_counter s2) FGroup (mstable_refl s2))|].
        eapply (enframe_spec (m :: X) U s2 g idx (class_size j - IB) (st_mmap_counter s2) FGroup am);
          [exact HI2 | exact U2 | pose proof (class_size_bounds j Hj48); unfold IB; lia | rewrite Hstr; lia | lia | intros _; rewrite Hstr; reflexivity | intros H63; exfalso; lia
          | intros _ _; rewrite Sc2; exact Hhd2 |].
        intros off s3 hdr Hoff Hofit Hoff0 Es3 HI3. msimp. intros M3. mqin M3. specialize (Hoff0 eq_refl). subst off. rewrite Z.mul_0_r, padd_0.
        set (am' := upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame 0 (class_size j - IB) FGroup)))) in Es3.
        pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some (mkFrame 0 (class_size j - IB) FGroup)))) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am' in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
        assert (U3 : usedX (m :: X) s3 g am').
        { rewrite Es3. apply usedX_upd. left. pose proof (usedX_MT _ _ _ _ U2) as [_ NXg]. auto. }
        assert (Hext1 : group_extent (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk) = total).
        { unfold group_extent. rewrite new_am_stride. cbn [am_last new_am Z.eqb andb negb].
          destruct (cnt0 - 1 =? 0); cbn [andb]; subst total; (replace (cnt0 - 1 + 1) with cnt0 by lia); lia. }
        assert (HX3 : Xfree (m :: X) s3) by exact (Xfree_mstable _ _ _ M3 HX2).
        assert (Htot2 : 0 < total <= class_size j - IB).
        { pose proof Hjfit as HJ. subst total. unfold UNIT, IB in *. split; [nia | lia]. }
        pose proof (stride_pos _ _ _ _ _ G2) as Sp.
        wbinds. eapply wt_frame.
        { apply (install_reach s3 m sc cnt0 (cnt0 - 1) 0 (slot_start am idx) slot_junk).
          - exact (reach_ok_mstable _ _ M3 HR2).
          - rewrite new_am_stride. replace ((cnt0 - 1 =? 0) && negb (0 =? 0)) with false by (destruct (cnt0 - 1 =? 0); reflexivity). lia.
          -
            intros q a i Mq Hml0 Hi Emem.
            apply (used_of_MUsed (m :: X) s3 q a HX3) in Mq.
            pose proof (f_equal prid Emem) as Ep. rewrite prid_slot_start in Ep. cbn [am_mem new_am] in Ep. rewrite prid_slot_start in Ep.
            pose proof (f_equal poff Emem) as Eo. rewrite poff_slot_start in Eo. rewrite new_am_stride in Eo.
            replace ((cnt0 - 1 =? 0) && negb (0 =? 0)) with false in Eo by (destruct (cnt0 - 1 =? 0); reflexivity).
            cbn [am_mem new_am] in Eo. rewrite poff_slot_start in Eo.
            pose proof (inv_groups HI3 q a Mq) as Gq. pose proof (stride_pos _ _ _ _ _ Gq) as Sq. pose proof (extent_pos _ _ _ _ _ Gq) as Xq.
            cbn [am_last new_am] in Hi.
            assert (Hi_sz : 0 <= class_size sc * i <= class_size sc * (cnt0 - 1))
              by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
            assert (Hsidx : 0 <= stride_of am * idx) by (apply Z.mul_nonneg_nonneg; lia).
            pose proof Mq as Hu. rewrite Es3 in Hu.
            destruct (nested_lam (m :: X) U s2 g idx am hdr (class_size j - IB) q a sc cnt0 HI2 U2 ltac:(rewrite Hstr; reflexivity)
                        ltac:(rewrite Hext1; exact Htot2) Hu Ep) as [D | [I | P]].
            + unfold spans_disjoint in D. rewrite Hext1 in D. cbn [am_mem new_am] in D. rewrite poff_slot_start in D.
              subst total. unfold UNIT, IB in *. lia.
            + destruct I as (j' & fr' & c & ac & Hj' & Hfr' & Hk' & Uc & Mlc & Memc & Lo & Hi' & Fit).
              cbn [am_mem new_am] in Lo. rewrite Memc, !poff_slot_start in Lo.
              assert (0 <= stride_of a * j') by (apply Z.mul_nonneg_nonneg; lia). unfold UNIT in *. lia.
            + destruct P as (j' & fr' & Hj' & Hfr' & Hk' & Est & Fit).
              pose proof (f_equal poff Est) as Eo'. rewrite !poff_slot_start in Eo'.
              assert (0 <= stride_of a * j') by (apply Z.mul_nonneg_nonneg; lia). unfold UNIT in *. lia.
          -
            intros _ g' a' i' M' Hi' Emem. cbn [am_mem new_am] in Emem.
            apply (used_of_MUsed (m :: X) s3 g' a' HX3) in M'.
            rewrite <- (Fss idx) in Emem.
            destruct (slot_starts_distinct (m :: X) None U s3 HI3 g am' idx g' a' i' U3 M' ltac:(rewrite Fl; lia) Hi' Emem) as [<- <-].
            pose proof (usedX_fun _ _ _ _ _ M' U3) as ->.
            rewrite Fsc, Sc2. exact (nested_host sc (usage_of s1 sc) Hsc Ebr).
          - cbn [am_aidx am_last new_am]. intros H0. lia. }
        eapply (install_group_spec X U s3 m sc cnt0 (cnt0 - 1) 0 (slot_start am idx) slot_junk).
        -- exact HI3.
        -- exact NX.
        -- exact Hsc.
        -- lia.
        -- lia.
        -- lia.
        -- rewrite Es3. unfold active_hd. cbn. pose proof (HB2 sc ltac:(lia)) as E. unfold active_hd in E. rewrite E, EA1. exact Hhd.
        -- right. split; reflexivity.
        -- right. cbn [am_sc am_last am_maplen new_am]. rewrite new_am_stride. cbn [Z.eqb andb negb].
           replace ((cnt0 - 1 =? 0) && false) with false by (destruct (cnt0 - 1 =? 0); reflexivity).
           split; [exact Hsc|]. split; [lia|]. split; [auto|]. replace (cnt0 - 1 + 1) with cnt0 by lia. exact Hc0s.
        -- intros H0. cbn in H0. lia.
        -- intros _. exists g, am', idx, (mkFrame 0 (class_size j - IB) FGroup). rewrite Fl, Fsc, Fss. cbn [fr_kind fr_n].
           split; [exact U3|]. split; [lia|]. split.
           { unfold am'. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity. }
           split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. subst total. unfold UNIT, IB in *. nia.
        -- intros q a Hu Hp. rewrite prid_slot_start in Hp. rewrite Es3 in Hu.
           destruct (nested_lam (m :: X) U s2 g idx am hdr (class_size j - IB) q a sc cnt0 HI2 U2 ltac:(rewrite Hstr; reflexivity)
                       ltac:(rewrite Hext1; exact Htot2) Hu Hp) as [D | [I | P]].
           ++ left. exact D.
           ++ right; left. rewrite Es3. exact I.
           ++ right; right. split; [reflexivity|]. exact P.
        -- intros H0. lia.
        -- intros s4 HI4 Hhd4 U4 EH4 Er4 Ec4 UB4. msimp. intros [HR4 HK4]. cbn [snd] in HR4, HK4.
           apply wt_ret. apply HQ; unfold group_postR, slot_postR; cbn [fst snd]; split; [|split].
           ++ intros c Hc. rewrite (EH4 c ltac:(lia) ltac:(lia)). rewrite Es3. unfold active_hd. cbn [st_active upd_meta set_metas].
              pose proof (HB2 c ltac:(lia)) as E. unfold active_hd in E. rewrite E, EA1. reflexivity.
           ++ split; [exact HR4|].
              intros x ax Hx Mx. destruct (sptr_eq_dec x m) as [->|Hxm].
              { apply (proj1 (memb_false_notIn m X) NX). exact Hx. }
              destruct (HK4 x ax Hxm Mx) as [a0 M0]. exact (HX3 x a0 (or_intror Hx) M0).
           ++ cbn [fst snd]. eexists. split; [exact HI4|]. split; [exact Hhd4|]. split; [exact U4|].
              pose proof (links_fields (Some m) (Some m) (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk)) as (_ & Ll & Ls & _).
              rewrite Ls, Ll. cbn [am_sc am_last new_am]. split; [reflexivity|]. split; [|lia].
              rewrite (strip_stride _ (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk)) by (unfold strip; reflexivity).
              rewrite new_am_stride. cbn [Z.eqb andb negb]. replace ((cnt0 - 1 =? 0) && false) with false by (destruct (cnt0 - 1 =? 0); reflexivity). lia.
Qed.

Theorem alloc_slot_reach : ltac2:(tb__ "0|1|
S1S0S0S3bS38S30S12S0A2A1S0S1S46R7A1S40R8A1S1eS23Z0R8A2M0S25R8Z30A2A2G0S23S24R9S9A2S8RaA1A2S45S30S0S1A2S10R9RbRaRcA4R8S34S0S1R7R6A4A4S40R7A1F_;F_;F_;F_;F_;F_;Fs';Fr;Fktr;Ffuel;Freq;Fsc;Fs;").
Proof.
  intros s sc req fuel ktr r s' HW HR Hsc Hreq Hfit HY.
  exact (proj1 (proj1 (proj2 (wt_yields _ _ ktr (r, s')
           (proj1 (alloc_reach fuel) [] U0 s sc req (slot_postR [] U0 s sc req) HW (Xfree_nil s) HR Hsc Hreq Hfit (fun _ H => H)) HY)))).
Qed.

Theorem alloc_slot_init_asi : ltac2:(tb__ "0|0|
S38S2A1S32S30S2S0A2A1S0S0F_;S1S0S0S3bS38S30S12S0A2A1S0S1S42RaR9R8R7A4S1eS23Z0R7A2S25R7Z30A2A2S45S30S0S1A2S10R6R8R7R9A4R5S34S0S1R4R3A4A4S1fS33S1dR4A1S3dA3F_;F_;F_;Fs';Fr;Fktr;Ffuel;Freq;Fsc;Fs;FU;FR;FX;").
Proof. intros X R U s sc req fuel ktr r s'. apply alloc_slot_init. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
