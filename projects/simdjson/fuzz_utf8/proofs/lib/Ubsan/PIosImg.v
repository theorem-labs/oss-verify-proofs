(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: copied from simdjson/fuzz_minifyimpl's proofs/lib/Ubsan/PIosImg.v: module paths and target names, 6 image addresses for simdjson/fuzz_utf8's ubsan binary. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import AsanHexScan.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma plain_hex2 : hexscanZ Ubsan_seg_bytes_002 0 28672 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma plain_hex3 : hexscanZ Ubsan_seg_bytes_003 0 212992 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma p_rw_window : forall (m : word -> option byte) (x : word),
  0xd4000 <= bv_unsigned x < 0x10f000 -> wview usegs m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  rewrite u_find_segment_1 by lia.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned x)); [|lia]. destruct (Z.leb_spec0 (bv_unsigned x + 1) 0x3a000); [lia|]. cbn [andb].
  destruct (Z.leb_spec0 0x3a000 (bv_unsigned x)); [|lia]. destruct (Z.leb_spec0 (bv_unsigned x + 1) 0xd4000); [lia|]. cbn [andb].
  destruct (Z.leb_spec0 0xd4000 (bv_unsigned x)); [|lia]. destruct (Z.leb_spec0 (bv_unsigned x + 1) 0xdb000); cbn [andb].
  - cbn -[segment_byte_at]. apply (segment_byte_at_someZ _ 28672); [exact plain_hex2 | rewrite Z2N.id by lia; lia].
  - destruct (Z.leb_spec0 0xdb000 (bv_unsigned x)); [|lia]. destruct (Z.leb_spec0 (bv_unsigned x + 1) 0x10f000); [|lia]. cbn [andb].
    cbn -[segment_byte_at]. apply (segment_byte_at_someZ _ 212992); [exact plain_hex3 | rewrite Z2N.id by lia; lia].
Qed.
