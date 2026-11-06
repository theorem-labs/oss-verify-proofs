(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YN02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0h YP0r YP0c YP0e YP07 YP04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Theorem do_jinv_proved : forall data fs, jinv (leaf_shape data fs) (driver_tree data).
Proof.
intros data fs. unfold driver_tree, driver_m.
pose proof wf_init as HW.
jwalk.
all: apply jinv_mbind;
[ eapply jinv_malloc_nonesome;
[ eassumption
| unfold payload_len, HDR_MIN, config_len, dlen in *; bool_hyps; lia
| intros; cbv beta iota; cbn [tset ret fst snd leaf_shape]; apply t_eq_refl
| intros; cbv beta iota; cbn [tset ret fst snd leaf_shape]; apply t_eq_refl ]
| intros ? [?|] ? ?; cbv beta iota; exact I ].
Qed.
End a.
