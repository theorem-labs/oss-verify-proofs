(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import AsanHexScan.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma plain_hex2 : hexscanZ Plain_seg_bytes_002 0 28672 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma plain_hex3 : hexscanZ Plain_seg_bytes_003 0 212992 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma p_rw_window : forall (m : word -> option byte) (x : word),
  0xca000 <= bv_unsigned x < 0x105000 -> wview psegs m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  rewrite p_find_segment_1 by lia.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned x)); [|lia]. destruct (Z.leb_spec0 (bv_unsigned x + 1) 0x3b000); [lia|]. cbn [andb].
  destruct (Z.leb_spec0 0x3b000 (bv_unsigned x)); [|lia]. destruct (Z.leb_spec0 (bv_unsigned x + 1) 0xca000); [lia|]. cbn [andb].
  destruct (Z.leb_spec0 0xca000 (bv_unsigned x)); [|lia]. destruct (Z.leb_spec0 (bv_unsigned x + 1) 0xd1000); cbn [andb].
  - cbn -[segment_byte_at]. apply (segment_byte_at_someZ _ 28672); [exact plain_hex2 | rewrite Z2N.id by lia; lia].
  - destruct (Z.leb_spec0 0xd1000 (bv_unsigned x)); [|lia]. destruct (Z.leb_spec0 (bv_unsigned x + 1) 0x105000); [|lia]. cbn [andb].
    cbn -[segment_byte_at]. apply (segment_byte_at_someZ _ 212992); [exact plain_hex3 | rewrite Z2N.id by lia; lia].
Qed.
