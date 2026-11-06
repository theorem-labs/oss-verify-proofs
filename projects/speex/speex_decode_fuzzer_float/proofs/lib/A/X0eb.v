(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cj X1dd.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X03z X0hg X0hn X04g X053 X04e X0jc X0fy X0fg X0d7 X0bw X0e9 X0ea X0eh X04a.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0ux X181 X188 X0ve X0w1 X0vc X19t X16j X161 X13s X12h X14u X14v X152 X0v8.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X181 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ve OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vc OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X152 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v8.
Import ListNotations.
Open Scope Z_scope.

Lemma rta_asan_memmove : memmove_icontract RTA e_asan_memmove.
Proof. exact (asan_memmove_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.
Lemma rta_memmove : memmove_icontract RTA e_memmove.
Proof. exact (memmove_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.

Lemma rta_cmp : forall Σ m, ART RTA Σ m -> icells_cmp m.
Proof.
intros Σ m HA. pose proof (rta_io Σ m HA) as IO.
pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & (P1 & _) & _).
pose proof (rta_ic Σ m HA) as (_ & _ & _ & (_ & _ & _ & _ & _ & AI & _) & _).
split; [exact (proj1 P1)|]. split; [exact (io_ro_at m IO 0xfdee8 _ ltac:(io_in))|]. split; [exact AI|].
exact (io_ro_at m IO 0x1976e6 _ ltac:(io_in)).
Qed.
Theorem rta_bcmp : bcmp_icontract RTA.
Proof. exact (bcmp_lift RTA rta_art_facts rip_proof rta_ic rta_shw rta_cmp). Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Lemma rta_asan_memmove : memmove_icontract RTA e_asan_memmove.
Proof. exact (asan_memmove_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.
Lemma rta_memmove : memmove_icontract RTA e_memmove.
Proof. exact (memmove_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.

Lemma rta_cmp : forall Σ m, ART RTA Σ m -> icells_cmp m.
Proof.
intros Σ m HA. pose proof (rta_io Σ m HA) as IO.
pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & (P1 & _) & _).
pose proof (rta_ic Σ m HA) as (_ & _ & _ & (_ & _ & _ & _ & _ & AI & _) & _).
split; [exact (proj1 P1)|]. split; [exact (io_ro_at m IO 0xf5668 _ ltac:(io_in))|]. split; [exact AI|].
exact (io_ro_at m IO 0x18eea6 _ ltac:(io_in)).
Qed.
Theorem rta_bcmp : bcmp_icontract RTA.
Proof. exact (bcmp_lift RTA rta_art_facts rip_proof rta_ic rta_shw rta_cmp). Qed.
