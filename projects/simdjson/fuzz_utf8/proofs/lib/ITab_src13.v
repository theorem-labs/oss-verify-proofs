(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AsanPlan AsanPlanSound. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import MainDefs Img_src13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition RSm_src13 : list (Z * nat) := [(0x3a000, 6144%nat); (0x4d000, 2048%nat); (0x50000, 2048%nat); (0x6d000, 2048%nat); (0x72000, 6144%nat); (0x90000, 6144%nat); (0x9a000, 2048%nat); (0x9d000, 2048%nat); (0xa8000, 5120%nat); (0xb2000, 10240%nat); (0xbe000, 2048%nat); (0xc3000, 7168%nat)]%Z.
(* [comment removed for export] *)
Definition ITm_src13 : itab := mk_itab_ranges SEGS_src13 RSm_src13.
Lemma ITm_src13_eq : ITm_src13 = mk_itab_ranges SEGS_src13 RSm_src13.
Proof. reflexivity. Qed.
Lemma ITm_src13_ok : itab_sound SEGS_src13 ITm_src13.
Proof. exact (itab_sound_of_eq _ _ _ ITm_src13_eq). Qed.
