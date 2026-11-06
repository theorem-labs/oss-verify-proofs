(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_errnonst.v (commit eb934de95d13, blob 019ba35ac137) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m AD2l.
Import ListNotations.
Local Open Scope Z_scope.

Definition meets4 (e : Z) (r : Z * Z) : bool := (fst r <? e + 4) && (e <? fst r + snd r).

Lemma nstatic_of_check : forall (owned : list (Z * Z)) (e : Z),
  existsb (meets4 e) owned = false ->
  forall a, e <= a < e + 4 -> ~ Exists (in_zr a) owned.
Proof.
  intros owned e H a Ha Hx. apply Exists_exists in Hx. destruct Hx as [r [Hin Hz]].
  assert (Hm : meets4 e r = true).
  { unfold meets4, in_zr in *. apply andb_true_intro. split; apply Z.ltb_lt; lia. }
  assert (existsb (meets4 e) owned = true) by (apply existsb_exists; eauto). congruence.
Qed.

Lemma errno_nstatic_check_A : existsb (meets4 (as_errno TfibB)) (as_owned_static TfibB) = false.
Proof. vm_compute. reflexivity. Qed.

Theorem errno_nstatic_A :
  forall a, as_errno TfibB <= a < as_errno TfibB + 4 -> ~ Exists (in_zr a) (as_owned_static TfibB).
Proof. exact (nstatic_of_check _ _ errno_nstatic_check_A). Qed.

Print Assumptions errno_nstatic_A.
