(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF6w YF6x.
Import ListNotations. Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Lemma sweep_hi : sweep clz_okb (Z.to_nat 32771) 32768 = true.
Proof. img_case; lazymatch goal with |- ?l_ = _ => vm_cast_no_check (@eq_refl _ l_) end. Qed.
Lemma clz_index : forall p, 18 <= p <= 65538 -> Z.lxor (clzS (4096 * p)) 63 = Z.log2 p + 12.
Proof.
intros p Hp. destruct (Z_lt_le_dec p 32768) as [Hlt|Hge].
- pose proof (sweep_val _ _ _ sweep_lo p) as H. rewrite Z2Nat.id in H by (img_try (clear; img_lia)). specialize (H ltac:(img_lia)).
cbv beta in H. apply Z.eqb_eq in H. img_exact H.
- pose proof (sweep_val _ _ _ sweep_hi p) as H. rewrite Z2Nat.id in H by (img_try (clear; img_lia)). specialize (H ltac:(img_lia)).
cbv beta in H. apply Z.eqb_eq in H. img_exact H.
Qed.
