(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zm2 RT_rep Zjb Zi7 Zkl Zbo I_qck R_m2s Zc5 Zc7 Zc0 Zcj Zcg Zn9 I_lift Zbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rta_shw : forall Σ m p n, ART RTA Σ m -> 0 < n -> rng_class RTA Σ p n -> qc_words m p n /\ region_in_mem p n.
Proof.
  intros Σ m p n HA Hn HC. cbn [ART rt_live rt_frames rt_sp0 RTA] in *. unfold rtA_live, rtA_frames, rtA_sp0 in *.
  destruct HC as [(p0 & k0 & Hin & H1 & H2)|[(f & k & Hin & H1 & H2)|[(H1 & H2)|(H1 & H2)]]].
  - destruct (vis_range_real (ann Σ) (live Σ) p0 k0 p n Hin H1 H2 Hn) as (n0 & Hin0 & H1' & H2'). exact (rta_shw_live Σ m HA p0 n0 p n Hin0 H1' H2' ltac:(lia)).
  - exact (rta_shw_frame Σ m HA f k p n Hin H1 H2 ltac:(lia)).
  - exact (rta_shw_stack Σ m HA p n H1 H2 ltac:(lia)).
  - exact (rta_shw_img Σ m HA p n H1 H2 ltac:(lia)).
Qed.

Lemma rta_ic : forall Σ m, ART RTA Σ m -> icells m /\ icells_ms m /\ icells_mc m /\ icells_sn m /\ m2s_cells m.
Proof. intros Σ m HA. exact (rta_icells_all Σ m HA). Qed.
Lemma rta_sl : forall Σ m, ART RTA Σ m -> icells_sl m.
Proof. intros Σ m HA. exact (rta_icells_sl Σ m HA). Qed.

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
