(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge Image.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs.
Import ListNotations.
Open Scope Z_scope.

Lemma a0_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x609000 <= z) -> find_segment asegs z n = None.
Proof.
  intros z n Hn Hz. unfold asegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Asan.Asan_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Asan.Asan_segment_000)) with 0x22000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Asan.Asan_segment_001)) with 0x32000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Asan.Asan_segment_001)) with 0x77000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Asan.Asan_segment_002)) with 0xa9000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Asan.Asan_segment_002)) with 0x2000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Asan.Asan_segment_003)) with 0xab000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Asan.Asan_segment_003)) with 0x55e000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x22000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x32000 z); destruct (Z.leb_spec0 (z + n) (0x32000 + 0x77000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xa9000 z); destruct (Z.leb_spec0 (z + n) (0xa9000 + 0x2000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xab000 z); destruct (Z.leb_spec0 (z + n) (0xab000 + 0x55e000)); cbn [andb]; try lia.
  all: reflexivity.
Qed.

Lemma stk_hi_wmono : forall (m m' : word -> option byte) lo hi, stk asegs m lo hi -> wmono asegs m m' -> 0x609000 <= lo -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) WM Hlo. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw _]. pose proof (WM _ Hw) as Hw'. split; [exact Hw'|].
  unfold wview in Hw'. unfold mrd. destruct (m' (wa a)) as [b|]; [exists b; reflexivity|].
  rewrite a0_find_segment_none in Hw'; [congruence| lia | rewrite wa_unsigned by lia; lia].
Qed.
