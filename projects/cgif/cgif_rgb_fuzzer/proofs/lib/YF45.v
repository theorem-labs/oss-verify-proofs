(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF44.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Lemma sweep_lo : sweep clz_okb (Z.to_nat 32750) 18 = true.
Proof. img_case; lazymatch goal with |- ?l_ = _ => vm_cast_no_check (@eq_refl _ l_) end. Qed.
