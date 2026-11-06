(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFi8.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_knock/proofs/lib/A/AFi8.v (donor image sha256 61768cf4739b), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AFi8.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from libdiginet/fuzz_codec's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AFi8.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YFi6 YFi7.
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
