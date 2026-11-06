(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AsanPlan AsanPlanSound. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import MainDefs Img_utf8_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition RSm_utf8_ubsan : list (Z * nat) := [(0x3a000, 7168%nat); (0x56000, 3072%nat); (0x5a000, 2048%nat); (0x77000, 2048%nat); (0x7c000, 6144%nat); (0x9a000, 6144%nat); (0xa4000, 2048%nat); (0xa7000, 2048%nat); (0xb2000, 5120%nat); (0xbc000, 10240%nat); (0xc8000, 2048%nat); (0xce000, 6144%nat)]%Z.
(* [comment removed for export] *)
Definition ITm_utf8_ubsan : itab := mk_itab_ranges SEGS_utf8_ubsan RSm_utf8_ubsan.
Lemma ITm_utf8_ubsan_eq : ITm_utf8_ubsan = mk_itab_ranges SEGS_utf8_ubsan RSm_utf8_ubsan.
Proof. reflexivity. Qed.
Lemma ITm_utf8_ubsan_ok : itab_sound SEGS_utf8_ubsan ITm_utf8_ubsan.
Proof. exact (itab_sound_of_eq _ _ _ ITm_utf8_ubsan_eq). Qed.
