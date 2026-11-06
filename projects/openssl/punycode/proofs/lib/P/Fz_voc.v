(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require StoreOk.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Image.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require WpEngine LibKit StrKit KBridge.
From OSSVerify.Proofs.openssl.punycode.lib.LibP Require PCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Abbreviation W z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Lemma PSEGS_psegs : PCode.PSEGS = psegs. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma find_segment_off : forall segs lo hi,
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi)) segs = true ->
  forall a, a < lo \/ hi <= a -> find_segment segs a 1 = None.
Proof.
  induction segs as [|seg segs IH]; intros lo hi H a Ha; cbn [find_segment forallb] in *; [reflexivity|].
  apply andb_prop in H as (H1 & H2). apply andb_prop in H1 as (B1 & B2). apply Z.leb_le in B1, B2.
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a) as [L1|L1]; destruct (Z.leb_spec (a + 1) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg))) as [L2|L2];
    cbn [andb]; try (exact (IH lo hi H2 a Ha)). exfalso. lia.
Qed.

Lemma psegs_hull_b : forallb (fun seg => (0x10000 <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? 0x30e000)) psegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seg_rom_off : forall a : word, bv_unsigned a < 0x10000 \/ 0x30e000 <= bv_unsigned a -> seg_rom psegs a = None.
Proof.
  intros a H. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (find_segment_off psegs 0x10000 0x30e000 psegs_hull_b (bv_unsigned a) H). reflexivity.
Qed.
(* [comment removed for export] *)
Definition mrd_offP := KBridge.mrd_off psegs 0x10000 0x30e000 seg_rom_off.
Definition bytes_offP := KBridge.bytes_off psegs 0x10000 0x30e000 seg_rom_off.
Definition rd_ok_bytesP := KBridge.rd_ok_bytes psegs 0x10000 0x30e000 seg_rom_off.
Definition rd_ok_stkP := KBridge.rd_ok_stk psegs 0x10000 0x30e000 seg_rom_off.

(* [comment removed for export] *)
Lemma ro_addr_P : forall i, 0x10000 <= i < 0x27b000 -> ro_addr psegs (W i) = true.
Proof.
  intros i Hi. unfold ro_addr. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  unfold psegs, Plain.M.loaded_segments, Plain.Plain_loaded_segments. cbn [find_segment].
  unfold Plain.Plain_segment_000, Plain.Plain_segment_001. cbn [seg_base seg_size].
  destruct (Z_lt_dec i 0xdc000) as [L|L].
  - rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  - rewrite (proj2 (Z.leb_le (Z.of_N 65536) i)) by lia. rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [andb].
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

Lemma img_ok_ro : forall (m : word -> option byte) lo hi, mem_inv psegs m -> 0x10000 <= lo -> hi <= 0x27b000 -> LibKit.img_ok m lo hi.
Proof.
  intros m lo hi MI H1 H2 i Hi. destruct (m (W i)) as [b|] eqn:E; [| reflexivity].
  pose proof (mem_inv_ro psegs m (W i) b MI E) as R. rewrite ro_addr_P in R by lia. discriminate R.
Qed.
