(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Class Band : Type := mkBand {
band_lo : Z;
band_lo_range : 0x7fff7f800000 <= band_lo <= 0x7fffff800000;
band_guard : word
}.

Ltac band_range_hook :=
try (match goal with
| |- context [@band_lo ?B] => pose proof (@band_lo_range B)
| _ : context [@band_lo ?B] |- _ => pose proof (@band_lo_range B)
end).

Ltac Zify.zify_pre_hook ::= band_range_hook. Ltac mkr__zify_pre_hook_0 := band_range_hook.

Local Example band_test1 {BAND : Band} (lo a : Z) : band_lo <= lo -> a < 0x3b000 -> a < lo.
Proof. intros. lia. Qed.
Local Example band_test2 {BAND : Band} (x : Z) : x <= band_lo -> x < 2^64.
Proof. intros. lia. Qed.
