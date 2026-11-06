(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YFi8.v (donor image sha256 1c29845fe605), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0m. From OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB Require Import YFi6 YFi7.
Import ListNotations. Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Lemma sweep_hi : sweep clz_okb (Z.to_nat 32771) 32768 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma clz_index : forall p, 18 <= p <= 65538 -> Z.lxor (clzS (4096 * p)) 63 = Z.log2 p + 12.
Proof.
intros p Hp. destruct (Z_lt_le_dec p 32768) as [Hlt|Hge].
- pose proof (sweep_val _ _ _ sweep_lo p) as H. rewrite Z2Nat.id in H by (clear; lia). specialize (H ltac:(lia)).
cbv beta in H. apply Z.eqb_eq in H. exact H.
- pose proof (sweep_val _ _ _ sweep_hi p) as H. rewrite Z2Nat.id in H by (clear; lia). specialize (H ltac:(lia)).
cbv beta in H. apply Z.eqb_eq in H. exact H.
Qed.
