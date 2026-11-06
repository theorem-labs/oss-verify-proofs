(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "kreq"; "ibind"; "bind"; "get"; "ret"; "@Corelib.Init.Datatypes"; "prod"; "bool"; "pair"; "list"; "nil"; "option"; "app"; "Some"; "false"; "fst"; "option_map"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "yields"; "WF"; "U0"; "allocated"; "usedX"; "@Corelib.Init.Logic"; "eq"; "ex"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocCalloc"; "calloc_m"; "is_allzero_am"; "is_allzero_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMalloc"; "malloc_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase"; "itok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfRepr MallocWfMalloc MallocWfMain MallocCalloc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Lemma yields_ibind_inv {A B} (t : itree astate A) (k : A -> itree astate B) tr b : ltac2:(tb__ "0|2|
S13VB;S3S0VA;VB;Vt;Vk;A5Vtr;Vb;A4S19SaS7S2S1bA2M0A1M1G1S19G1G1S19VA;VA;S1aS18G1Vtr;SdG0R3R2A3A3S1aS13VA;Vt;R3R1A4S13VB;Vk;R1A1R2Vb;A4A2A2La;A2Ltr2;A2Ltr1;A2F_;").
Proof.
  revert tr. induction t as [a | q snap c IH | f]; cbn; intros tr Hy.
  - exists [], tr, a. cbn. auto.
  - destruct tr as [|[q' z] tr']; [destruct Hy|]. destruct Hy as (-> & Hz & Hy).
    destruct (IH z tr' Hy) as (tr1 & tr2 & a & -> & H1 & H2).
    exists ((q, z) :: tr1), tr2, a. cbn. auto.
  - destruct tr; destruct Hy.
Qed.

Lemma yields_ibind {A B} (t : itree astate A) (k : A -> itree astate B) tr1 tr2 a b : ltac2:(tb__ "0|0|
S13VA;Vt;Vtr1;Va;A4S13VB;Vk;Va;A1Vtr2;Vb;A4S13VB;S3S0VA;VB;Vt;Vk;A5SdS7S2S1bA2Vtr1;Vtr2;A3Vb;A4F_;F_;").
Proof.
  revert tr1. induction t as [a' | q snap c IH | f]; cbn; intros tr1 H1 H2.
  - destruct tr1; [subst; exact H2 | destruct H1].
  - destruct tr1 as [|[q' z] tr']; [destruct H1|]. destruct H1 as (-> & Hz & H1). cbn. split; [reflexivity|]. split; [exact Hz|].
    apply IH; assumption.
  - destruct tr1; destruct H1.
Qed.

Lemma yields_bind_inv {A B} (m : M A) (k : A -> M B) s tr b : ltac2:(tb__ "0|3|
S13S7VB;S0A2M0S4VA;VB;Vm;Vk;Vs;A5Vtr;Vb;A4S19SaS7S2S1bA2M1A1M2G2S19G2G2S19VA;VA;S19S0S0S1aS18G2Vtr;SdG1R4R3A3A3S1aS13S7VA;S0A2Vm;Vs;A1R4S9VA;S0R2R1A4A4S13G0Vk;R2R1A2R3Vb;A4A2A2Ls1;A2La;A2Ltr2;A2Ltr1;A2F_;").
Proof.
  intros Hy. unfold bind in Hy. apply yields_ibind_inv in Hy as (tr1 & tr2 & [a s1] & E & H1 & H2).
  exists tr1, tr2, a, s1. auto.
Qed.

Lemma yields_ret_inv {A} (a : A) s tr r : ltac2:(tb__ "0|2|
S13S7VA;S0A2M0S6VA;Va;Vs;A3Vtr;Vr;A4S1aS18SaS7S2S1bA2M1A1Vtr;SbG1A1A3S18G0Vr;S9VA;S0Va;Vs;A4A3A2F_;").
Proof. cbn. destruct tr; [intros <-; auto | intros []]. Qed.

Lemma yields_get_inv s tr r : ltac2:(tb__ "0|2|
S13S7S0S0A2M0S5Vs;A1Vtr;Vr;A4S1aS18SaS7S2S1bA2M1A1Vtr;SbG1A1A3S18G0Vr;S9S0S0Vs;Vs;A4A3A2F_;").
Proof. cbn. destruct tr; [intros <-; auto | intros []]. Qed.

Lemma is_allzero_m_defined s n p s' : ltac2:(tb__ "0|0|
S21SbS1A1S15Vs;Vn;S9ScS1A1S0SeS1Vp;A2Vs';A4A5S19S8S8S18ScS8A1S20Vs';Vp;A2SeS8R1A2A3Lb;A2F_;").
Proof.
  intros [HI Hpost]. cbn [fst snd] in *.
  destruct Hpost as (g & am & idx & off & (Hu & Hidx & Hfr & ->) & _).
  assert (HF : In (g, am, idx, mkFrame off n FUser) (frames s')).
  { apply frames_intro; [exact HI | | exact Hidx | exact Hfr]. exact (proj1 (usedX_MT _ _ _ _ Hu)). }
  pose proof (get_meta_ok s' g am idx (mkFrame off n FUser) HI HF) as GM.
  cbn beta in GM. destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfind).
  unfold is_allzero_m. unfold frame_ptr in Hfind. cbn [fr_off] in Hfind. rewrite Hfind.
  pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as HMT. unfold MT in HMT.
  unfold lookup_used. rewrite HMT. eexists. reflexivity.
Qed.

Theorem calloc_m_itok s m n : ltac2:(tb__ "0|4|
S14Vs;A1S1cZ0M0Vm;A2S1cG0Vn;A2S22S7ScS7S1S8A2M1A1M2S0A2M3S1eVm;Vn;Vs;A3G3S21SbS1A1S15Vs;S1dVm;Vn;A2S9ScS1A1S0S11G1S1S10S1S8A2S10G2S0R1A3A4S12G2S0R1A3A4A5Lr;A3F_;F_;F_;").
Proof.
  intros HW Hm Hn. unfold calloc_m.
  destruct (calloc_overflows m n) eqn:Eov.
  - apply itok_ret. cbn. split; [exact HW | apply ub_same_refl].
  - apply itok_bind. eapply itok_mono; [| apply (malloc_spec U0 s (m * n) (malloc_post [] U0 s (m * n)) HW ltac:(nia)); intros r Hr; exact Hr].
    intros [op s'] Hpost. cbn [fst snd].
    destruct op as [p|].
    + apply itok_bind. apply itok_get. cbn [fst snd].
      destruct (is_allzero_m_defined s (m * n) p s' Hpost) as [b Hb]. rewrite Hb.
      destruct b; apply itok_ret; cbn [fst snd option_map]; exact Hpost.
    + apply itok_ret. exact Hpost.
Qed.

Theorem calloc_safe : calloc_safe_stmt.
Proof. intros s m n HW Hm Hn. eapply itok_safe. apply calloc_m_itok; [exact HW | lia | lia]. Qed.

Theorem calloc_wf : ltac2:(tb__ "0|2|
S0S1bS1bSaS7S2S1bA2A1ScS7S1S8A2A1M0S0S14R6A1S1cZ0R6A2M1G1S13S7G0S0A2S1eR8R7R9A3R6S9G0S0R5R4A4A4S14R5A1F_;F_;F_;F_;Fs';Fr;Ftr;Fn;Fm;Fs;").
Proof.
  intros s m n tr r s' HW Hm Hn Hy.
  exact (proj1 (itok_yields _ _ tr (r, s') (calloc_m_itok s m n HW Hm Hn) Hy)).
Qed.

Theorem calloc_is_malloc : calloc_is_malloc_stmt.
Proof.
  intros s m n tr r s' HW Hm Hn Hov Hy. unfold calloc_m in Hy. rewrite Hov in Hy.
  apply yields_bind_inv in Hy as (tr1 & tr2 & op & s1 & -> & H1 & H2).
  destruct op as [p|].
  - apply yields_bind_inv in H2 as (tr3 & tr4 & s2 & s3 & -> & H3 & H4).
    apply yields_get_inv in H3 as [-> E]. injection E as E1 E2. subst s2 s3.
    pose proof (itok_yields _ _ tr1 (Some p, s1) (malloc_spec U0 s (m * n) _ HW ltac:(nia) (fun r H => H)) H1) as Hpost.
    destruct (is_allzero_m_defined s (m * n) p s1 Hpost) as [b Hb]. rewrite Hb in H4.
    destruct b; apply yields_ret_inv in H4 as [-> E]; injection E as E3 E4; subst r s'; cbn [option_map fst]; rewrite !app_nil_r; exact H1.
  - apply yields_ret_inv in H2 as [-> E]. injection E as E3 E4. subst r s'. cbn [option_map]. rewrite app_nil_r. exact H1.
Qed.

Lemma existing_slot_not_allzero s g am i : ltac2:(tb__ "0|0|
S14Vs;A1S17SbS1A1Vs;Vg;Vam;A4S1cZ0Vi;A2S18S8S16Vam;Vi;A2SfA3S18S8S1fVam;A1SfA3F_;F_;F_;F_;").
Proof.
  intros HW Hu Hi Hal.
  pose proof (inv_groups HW g am Hu) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  unfold is_allzero_am. apply orb_false_intro.
  - destruct Gcl as [(C63 & Cl & Cml & Cav & Cfr & _) | (Csc & _)].
    +
      exfalso. unfold allocated in Hal. rewrite Cav, Cfr in Hal. cbn in Hal.
      rewrite Z.testbit_0_l in Hal. discriminate.
    + apply Z.leb_gt. lia.
  - destruct Gcl as [(C63 & Cl & Cml & Cav & Cfr & _) | (Csc & Cund & _)].
    + exfalso. unfold allocated in Hal. rewrite Cav, Cfr in Hal. cbn in Hal.
      rewrite Z.testbit_0_l in Hal. discriminate.
    + apply Z.ltb_ge. destruct (Z_lt_dec (stride_of am) (class_size (am_sc am))) as [Hlt|Hge]; [|lia].
      exfalso. destruct (Cund Hlt) as [Hl Ha0].

      destruct Gm as (Hlast & _ & _ & Hav & Hfr & _ & Habove & _).
      destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite Ha0 in Hal; discriminate|].
      destruct (Habove i ltac:(lia)) as [A B].
      unfold allocated in Hal. rewrite Z.lor_spec, A, B in Hal. discriminate.
Qed.
