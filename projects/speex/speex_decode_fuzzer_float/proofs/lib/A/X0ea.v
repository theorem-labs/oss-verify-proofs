(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0fy X0fg X0d7 X0bw X0e9
X03z X04v X0hi X04g X04k X04c X053 X050 X0hg X048 X049.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X16j X161 X13s X12h X14u X0ux X0vt X183 X0ve X0vi X0va X0w1 X0vy X181 X0v6 X0v7.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ve OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vi OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0va OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vy OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X181 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v7.
Import ListNotations.
Open Scope Z_scope.

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
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

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
