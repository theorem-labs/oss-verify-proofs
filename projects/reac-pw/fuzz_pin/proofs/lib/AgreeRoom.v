(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v; 94 of its 156 lines of code are new or changed and 400 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocPackCf.v, with its module paths and module names changed; 74 of its 98 lines of code are new or changed and 132 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/SlotAgree.v, with its module paths changed; 8 of its 22 lines of code are new or changed and 84 lines of the source are left out. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YO03.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import AllocSlots.
Local Open Scope Z_scope.

Definition NONHEAP_CF : Z := 2 ^ 31.

Definition room_cf (md : Model) (b : sbound) (n : Z) : Prop :=
  room_slots b n /\ LIVE_BOUND (sb_cap b) (sb_bytes b + n) + NONHEAP_CF <= vm_limit (m_vmmaps md).

Lemma LIVE_BOUND_mono : forall c c' y y', 0 <= c <= c' -> y <= y' -> LIVE_BOUND c y <= LIVE_BOUND c' y'.
Proof.
  intros c c' y y' Hc Hy. unfold LIVE_BOUND, AREA_BOUND, P2, NA, HCAP.
  assert (D : (13 * c + 48) / METAS_PER_AREA <= (13 * c' + 48) / METAS_PER_AREA)
    by (apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | lia]).
  unfold OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable.YO03.MMAX, PGSZ in *. nia.
Qed.

Lemma room_cf_of_bound : forall X Y md b n, LIVE_BOUND X Y + NONHEAP_CF <= vm_limit (m_vmmaps md) ->
  room_slots b n -> 0 <= sb_cap b <= X -> sb_bytes b + n <= Y -> room_cf md b n.
Proof.
  intros X Y md b n Hl Hr Hc Hb. split; [exact Hr|].
  pose proof (LIVE_BOUND_mono (sb_cap b) X (sb_bytes b + n) Y Hc Hb). lia.
Qed.
