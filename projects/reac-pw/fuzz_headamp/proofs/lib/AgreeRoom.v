(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v at bc49657c087a; module path, this image's values, LLVM_K from check_inject. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths and module names changed; 79 of its 98 lines of code are new or changed and 48 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/SlotAgree.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/SlotAgree.v, with its module paths changed; 9 of its 22 lines of code are new or changed and 85 lines of the source are left out. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO03.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import AllocSlots.
Local Open Scope Z_scope.

Definition NONHEAP_CF : Z := 2 ^ 31.

Definition room_cf (md : Model) (b : sbound) (n : Z) : Prop :=
  room_slots b n /\ LIVE_BOUND (sb_cap b) (sb_bytes b + n) + NONHEAP_CF <= vm_limit (m_vmmaps md).

Lemma LIVE_BOUND_mono : forall c c' y y', 0 <= c <= c' -> y <= y' -> LIVE_BOUND c y <= LIVE_BOUND c' y'.
Proof.
  intros c c' y y' Hc Hy. unfold LIVE_BOUND, AREA_BOUND, P2, NA, HCAP.
  assert (D : (13 * c + 48) / METAS_PER_AREA <= (13 * c' + 48) / METAS_PER_AREA)
    by (apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | lia]).
  unfold OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable.YO03.MMAX, PGSZ in *. nia.
Qed.

Lemma room_cf_of_bound : forall X Y md b n, LIVE_BOUND X Y + NONHEAP_CF <= vm_limit (m_vmmaps md) ->
  room_slots b n -> 0 <= sb_cap b <= X -> sb_bytes b + n <= Y -> room_cf md b n.
Proof.
  intros X Y md b n Hl Hr Hc Hb. split; [exact Hr|].
  pose proof (LIVE_BOUND_mono (sb_cap b) X (sb_bytes b + n) Y Hc Hb). lia.
Qed.
