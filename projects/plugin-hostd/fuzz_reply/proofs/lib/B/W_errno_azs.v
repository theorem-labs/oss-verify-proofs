(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: copied from lib/A/W_ERRL_x.v (its lemma errno_azs) to image B's names.
   rule 24: no function proved (kind: invariant lemma: errno's four bytes lie in a zero-shadow range of the instance).
   [errno_azs] : azs B (as_errno B) 4 (W_contract.v:284 azs), the drain stages' HERRZ at image B, from the start-up
   table alone: YF0m's Tfib_zero_shadow range (0x5d90e0, 0x5fc000 - 0x5d90e0) (YF0m.v:818) holds
   [TFIB_ERRNO, TFIB_ERRNO + 4) = [0x5d994c, 0x5d9950) (YF0m.v:21), so every AR state reads shadow 0 there
   (W_contract.v:410 azs_range_addressable).  Image A's twin: lib/A/W_ERRL_x.v errno_azs, the same script. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_errno_azs.v, with its module paths changed; 5 lines of the source are left out. *)
(* [errno_azs] : azs B (as_errno B) 4 (W_contract.v:315 azs), the drain stages' HERRZ at image B, from the start-up
   table alone: YF0m's Tfib_zero_shadow range (0x5d90e0, 0x5fc000 - 0x5d90e0) (YF0m.v:820) holds
   [TFIB_ERRNO, TFIB_ERRNO + 4) = [0x5d994c, 0x5d9950) (YF0m.v:21), so every AR state reads shadow 0 there
   (W_contract.v:444 azs_range_addressable).  rule 24: no function proved (kind: invariant lemma: errno's four bytes
   lie in a zero-shadow range of the instance).  Image A's twin: lib/A/W_ERRL_x.v errno_azs, the same script. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m W_contract.
Import ListNotations.
Local Open Scope Z_scope.

Lemma errno_azs : forall B, TfibSyms B -> azs B (as_errno B) 4.
Proof.
  intros B TS. unfold azs. rewrite (@ts_zsh B TS), (@ts_errno B TS).
  exists (0x5d90e0, 0x5fc000 - 0x5d90e0). split.
  - unfold Tfib_zero_shadow. repeat (first [left; reflexivity | right]).
  - vm_compute. repeat split; first [reflexivity | discriminate | (let H := fresh in intro H; discriminate H)].
Qed.
