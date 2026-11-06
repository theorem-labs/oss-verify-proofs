(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Class HeapCeil : Type := mkHeapCeil {
  hceil : Z ;
  hceil_range : 0x7fff7f800000 <= hceil <= 0x7fffff800000
}.

(* [comment removed for export] *)
Ltac hcb :=
  let K := fresh "HCEILB" in
  pose proof (hceil_range : 0x7fff7f800000 <= hceil <= 0x7fffff800000) as K.

Section Facts.
  Context {HCEIL : HeapCeil}.
  Lemma hceil_lo : 0x7fff7f800000 <= hceil.  Proof. hcb. lia. Qed.
  Lemma hceil_hi : hceil <= 0x7fffff800000.  Proof. hcb. lia. Qed.
  Lemma hceil_pos : 0 < hceil.                Proof. hcb. lia. Qed.
  Lemma hceil_lt_2p47 : hceil < 2^47.         Proof. hcb. lia. Qed.
  Lemma hceil_lt_2p63 : hceil < 2^63.         Proof. hcb. lia. Qed.
  Lemma hceil_lt_2p64 : hceil + 2^24 < 2^64.  Proof. hcb. lia. Qed.
End Facts.
