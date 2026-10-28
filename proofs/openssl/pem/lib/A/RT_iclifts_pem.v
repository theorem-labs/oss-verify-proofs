(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_prim_defs RT_iface RT_state RT_rep RT_facts RT_facts0 RT_sep RT_artfacts RT_icfacts I_consts I_qck R_m2s I_strncmpw R_isPoisoned I_lift RT_iclifts RT_iface_pem I_ut I_memcpyw I_memcmpw I_memcmp I_strcpy I_amemmove I_lift_pem RT_gshacc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rta_lib_ro_at : forall Σ m a cs, ART RTA Σ m -> In (a, cs) LIB_RO -> ro_cells asegs m a cs.
Proof. intros Σ m a cs HA Hin. exact (proj1 (Forall_forall _ _) (rta_lib_ro Σ m HA) (a, cs) Hin). Qed.

Lemma rta_untouched : forall Σ m, ART RTA Σ m -> img_untouched m.
Proof. intros Σ m HA. pose proof (rta_client_consts Σ m HA) as (_ & _ & _ & _ & U). exact U. Qed.

Lemma rta_m2s : forall Σ m, ART RTA Σ m -> m2s_cells m.
Proof. intros Σ m HA. exact (proj2 (proj2 (proj2 (proj2 (rta_ic Σ m HA))))). Qed.

Lemma rta_mcmp : forall Σ m, ART RTA Σ m -> icells_mcmp m.
Proof.
  intros Σ m HA. pose proof (rta_sc Σ m HA) as (G70 & G2 & SHC & AI & _). pose proof (rta_untouched Σ m HA) as U.
  unfold icells_mcmp. split; [exact G70|]. split; [exact G2|].
  split; [apply (ut_ro_cells m _ _ U); [cbn; tauto | vm_compute; reflexivity | unfold IMG_UT_LO; lia | unfold IMG_UT_HI; cbn; lia]|].
  split; [exact SHC|]. split; [exact AI|].
  split; apply (rta_lib_ro_at Σ m _ _ HA); unfold LIB_RO; repeat (first [left; reflexivity | right]).
Qed.

Lemma rta_scpy : forall Σ m, ART RTA Σ m -> icells_scpy m.
Proof.
  intros Σ m HA. pose proof (rta_sc Σ m HA) as (_ & _ & SHC & AI & _). pose proof (rta_untouched Σ m HA) as U.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
  destruct IC as (_ & _ & _ & _ & _ & _ & RS & _).
  unfold icells_scpy.
  split; [apply (ut_ro_cells m _ _ U); [cbn; tauto | vm_compute; reflexivity | unfold IMG_UT_LO; lia | unfold IMG_UT_HI; cbn; lia]|].
  split; [apply (ut_ro_cells m _ _ U); [cbn; tauto | vm_compute; reflexivity | unfold IMG_UT_LO; lia | unfold IMG_UT_HI; cbn; lia]|].
  split; [apply (ut_ro_cells m _ _ U); [cbn; tauto | vm_compute; reflexivity | unfold IMG_UT_LO; lia | unfold IMG_UT_HI; cbn; lia]|].
  split; [exact RS|]. split; [exact SHC| exact AI].
Qed.

Theorem rta_memcmp : memcmp_icontract RTA.
Proof. exact (memcmp_lift RTA rta_art_facts rip_proof rta_m2s rta_shw rta_mcmp). Qed.
Theorem rta_strcpy : strcpy_icontract RTA.
Proof. exact (strcpy_lift RTA rta_art_facts rip_proof rta_m2s rta_shw rta_scpy). Qed.
Lemma rta_icm : forall Σ m, ART RTA Σ m -> icells m.
Proof. intros Σ m HA. exact (proj1 (rta_ic Σ m HA)). Qed.
Theorem rta_asan_memmove : memmove_icontract RTA e_asan_memmove.
Proof. exact (asan_memmove_lift RTA rta_art_facts rip_proof rta_m2s rta_shw rta_icm). Qed.

(* [comment removed for export] *)
Lemma rim_off_shadow : forall p n, 1 <= n -> region_in_mem p n -> (p + n <= 0x7fff8000 \/ 0x10007fff8000 <= p) /\ p + n <= 2^47.
Proof. intros p n Hn RIM. unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. Qed.

Theorem rta_live_mem : live_mem_fact RTA.
Proof.
  intros Σ m p n HA Hin Hn. apply rim_off_shadow; [exact Hn|].
  apply (rta_shw Σ m p n HA ltac:(lia)). left. exists p, n. split; [exact Hin| lia].
Qed.

Theorem rta_live_hi : live_hi_fact RTA.
Proof.
  intros Σ m p n HA Hin Hn. cbn [ART rt_live RTA] in *. unfold rtA_live in *.
  destruct (geo_live Σ m HA p n Hin) as [(c & i & Hc & Hi & -> & Y1 & Y2 & Y3 & Y4 & Y5)|(sc & Hs & Hq & Hn' & -> & Y1 & Y5)].
  - pose proof (geo_grant Σ m HA (l_PRB (lay Σ)) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
    pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). unfold l_ACEIL, STACK_WIN, rb, kUserCap, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
    destruct G4 as [G4|G4]; lia.
  - exfalso. pose proof (ART_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
    pose proof (proj1 (Forall_forall _ _) HSF sc Hs) as (Hsn & _). lia.
Qed.

Theorem rta_frame_mem : frame_mem_fact RTA.
Proof.
  intros Σ m f k HA Hin.
  assert (K : 1 <= fs_size k - 8).
  { unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)). lia. }
  replace (f + fs_size k - 8) with (f + (fs_size k - 8)) by lia.
  apply rim_off_shadow; [exact K|].
  apply (rta_shw Σ m f (fs_size k - 8) HA ltac:(lia)). right. left. exists f, k. split; [exact Hin| lia].
Qed.

Theorem rta_art_facts_pem : art_facts_pem RTA A_GOBJ.
Proof. exact (mkAFP RTA A_GOBJ rta_acc_global rta_gsh_byte rta_live_mem rta_live_hi rta_frame_mem). Qed.
