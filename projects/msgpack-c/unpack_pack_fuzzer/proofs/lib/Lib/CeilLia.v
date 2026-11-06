(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import LiaTuning.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac inst_ceil :=
  repeat match goal with
  | |- context [@alloc_ceiling ?e] => is_evar e; lazymatch goal with C : ceiling |- _ => unify e C end
  | H : context [@alloc_ceiling ?e] |- _ => is_evar e; lazymatch goal with C : ceiling |- _ => unify e C end
  end.

Ltac pose_ceil_if_relevant :=
  inst_ceil;
  lazymatch goal with
  | H : (0x7fff7f800000 <= _ <= 0x7fffff800000)%Z |- _ => idtac
  | |- context [@alloc_ceiling _] => try pose proof alloc_ceiling_range' as CEIL_RANGE
  | H : context [@alloc_ceiling _] |- _ => try pose proof alloc_ceiling_range' as CEIL_RANGE
  | |- _ => idtac
  end.

Ltac lia ::=
  pose_ceil_if_relevant;
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
