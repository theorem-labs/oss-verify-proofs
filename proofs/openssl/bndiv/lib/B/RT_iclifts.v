(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface RT_state RT_rep RT_facts RT_artfacts RT_icfacts I_consts I_qck R_m2s I_memcpyw I_memsetw I_memchrw I_strnlenw I_strlen I_strncmpw R_isPoisoned I_lift I_lift2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rta_shw : forall Σ m p n, ART RTA Σ m -> 0 < n -> rng_class RTA Σ p n -> qc_words m p n /\ region_in_mem p n.
Proof.
  intros Σ m p n HA Hn HC. cbn [ART rt_live rt_frames rt_sp0 RTA] in *. unfold rtA_live, rtA_frames, rtA_sp0 in *.
  destruct HC as [(p0 & k0 & Hin & H1 & H2)|[(f & k & Hin & H1 & H2)|[(H1 & H2)|(H1 & H2)]]].
  - exact (rta_shw_live Σ m HA p0 k0 p n Hin H1 H2 ltac:(lia)).
  - exact (rta_shw_frame Σ m HA f k p n Hin H1 H2 ltac:(lia)).
  - exact (rta_shw_stack Σ m HA p n H1 H2 ltac:(lia)).
  - exact (rta_shw_img Σ m HA p n H1 H2 ltac:(lia)).
Qed.

Lemma rta_ic : forall Σ m, ART RTA Σ m -> icells m /\ icells_ms m /\ icells_mc m /\ icells_sn m /\ m2s_cells m.
Proof. intros Σ m HA. exact (rta_icells_all Σ m HA). Qed.
Lemma rta_sl : forall Σ m, ART RTA Σ m -> icells_sl m.
Proof. intros Σ m HA. exact (rta_icells_sl Σ m HA). Qed.
Lemma rta_sc : forall Σ m, ART RTA Σ m -> icells_sc m.
Proof. intros Σ m HA. exact (rta_icells_sc Σ m HA). Qed.

Theorem rta_memcpy : memcpy_icontract RTA e_memcpy.
Proof. exact (memcpy_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.
Theorem rta_memset : memset_icontract RTA e_memset.
Proof. exact (memset_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.
Theorem rta_memchr : memchr_icontract RTA.
Proof. exact (memchr_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.
Theorem rta_strnlen : strnlen_icontract RTA.
Proof. exact (strnlen_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.
Theorem rta_strlen : strlen_icontract RTA.
Proof. exact (strlen_lift RTA rta_art_facts rip_proof rta_ic rta_shw rta_sl). Qed.
Theorem rta_asan_memset : memset_icontract RTA e_asan_memset.
Proof. exact (asan_memset_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.
Theorem rta_asan_memcpy : memcpy_icontract RTA e_asan_memcpy.
Proof. exact (asan_memcpy_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.
Theorem rta_strncmp : strncmp_icontract RTA.
Proof. exact (strncmp_lift RTA rta_art_facts rip_proof rta_ic rta_shw rta_sc). Qed.
