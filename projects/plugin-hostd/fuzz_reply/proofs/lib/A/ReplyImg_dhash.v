(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-dhash-A of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record), for a Theorem Labs lane's cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row img-dhash-A; a closed fact of reply's image A, fuzz_reply.asan, at its
   closed symbol record TfibB, A/AD2l.v).
   Reuse search: proof-index dhash_img_A dhash_img (2026-10-30 06:2xZ, exit 0): 0 hits anywhere.

   Row dhash_img (frame CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) row 45): the witness-only premise of the cf layer's F1 depot_spec_a / _d at
   cgif (YGcfInstF1Wcgif.v:131 / :135), `forall t, as_dhash B t = <the unit's depot hash> t`. Lane W's instances fix
   B := TfibB, so the row is stated AT TfibB, with the unit's depot hash tfib_dhash (lib/Reusable/YF0p.v, image-free):
   TfibB's field is `as_dhash := tfib_dhash` (A/AD2l.v:34), so each instance is eq_refl. No kit change. The B twin is
   dhash_img_B (lib/B/ReplyImg_dhash.v, a Theorem Labs lane, the same statement at reply B's TfibB). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YF0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l.

(* dhash_img at image A's closed record TfibB: its depot hash is the unit's tfib_dhash. *)
Lemma dhash_img_A : forall t, as_dhash TfibB t = tfib_dhash t.
Proof. intros t. reflexivity. Qed.
