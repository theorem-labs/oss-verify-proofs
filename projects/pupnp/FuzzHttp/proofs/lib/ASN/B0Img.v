(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Image.
From OSSVerify.pupnp.FuzzHttp.images Require Export AsanUbsan.
Import ListNotations.
Open Scope Z_scope.

Definition bsegs : list Segment := AsanUbsan.M.loaded_segments.
Definition b_init_pc : N := AsanUbsan.M.init_pc.
Definition b_phdrs : PhdrInfo := AsanUbsan.M.phdrs.

Lemma b_find_segment_1 : forall z, 0 <= z ->
  find_segment bsegs z 1 =
    if (0x10000 <=? z) && (z + 1 <=? 0x32000) then Some AsanUbsan_segment_000
    else if (0x32000 <=? z) && (z + 1 <=? 0xaa000) then Some AsanUbsan_segment_001
    else if (0xaa000 <=? z) && (z + 1 <=? 0xac000) then Some AsanUbsan_segment_002
    else if (0xac000 <=? z) && (z + 1 <=? 0x609000) then Some AsanUbsan_segment_003
    else None.
Proof. intros z Hz. reflexivity. Qed.

Lemma b_ro_addr : forall a : word,
  ro_addr bsegs a = ((0x10000 <=? bv_unsigned a) && (bv_unsigned a <? 0xaa000))%bool.
Proof.
  intros a. unfold ro_addr. rewrite b_find_segment_1 by (pose proof (bv_unsigned_in_range 64 a); lia).
  pose proof (bv_unsigned_in_range 64 a) as R.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x32000);
  destruct (Z.leb_spec0 0x32000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0xaa000);
  destruct (Z.leb_spec0 0xaa000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0xac000);
  destruct (Z.leb_spec0 0xac000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x609000);
  destruct (Z.ltb_spec0 (bv_unsigned a) 0xaa000); cbn; try reflexivity; lia.
Qed.

Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x609000 <= z) ->
  find_segment bsegs z n = None.
Proof.
  intros z n Hn Hz. unfold bsegs, AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base AsanUbsan_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_000)) with 0x22000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_001)) with 0x32000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_001)) with 0x78000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_002)) with 0xaa000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_002)) with 0x2000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_003)) with 0xac000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_003)) with 0x55d000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x22000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x32000 z); destruct (Z.leb_spec0 (z + n) (0x32000 + 0x78000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0xaa000 z); destruct (Z.leb_spec0 (z + n) (0xaa000 + 0x2000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0xac000 z); destruct (Z.leb_spec0 (z + n) (0xac000 + 0x55d000)); cbn [andb]; try lia; reflexivity.
Qed.
