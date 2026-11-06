(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition FBITMASK : Z := 0x11358.
Definition fbitmask_bytes : list byte := Eval vm_compute in match image_bytes psegs FBITMASK 128 with Some bs => bs | None => [] end.

Lemma fbitmask_at : forall m, mem_inv psegs m -> bytes_at psegs m FBITMASK fbitmask_bytes.
Proof.
  intros m MI. pose proof (ro_cells_image psegs m FBITMASK fbitmask_bytes MI ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma fbytes_eq_unsigned : forall a b : list byte, map (@bv_unsigned 8) a = map (@bv_unsigned 8) b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn [map] in H. injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Lemma fbitmask_rd : forall m nb a, mem_inv psegs m -> 0 <= nb <= 31 -> a = wa (FBITMASK + 4 * nb) ->
  ov_read_bytes psegs m a 4 = Some (le4 (Z_to_bv 64 (2^nb - 1))).
Proof.
  intros m nb a MI H ->.
  rewrite (bytes_at_read psegs m FBITMASK fbitmask_bytes (4 * nb) 4 (fbitmask_at m MI)) by (change (length fbitmask_bytes) with 128%nat; lia).
  f_equal. assert (C : exists k : nat, (k <= 31)%nat /\ nb = Z.of_nat k) by (exists (Z.to_nat nb); lia).
  destruct C as (k & Hk & ->). do 32 (destruct k as [|k]; [apply fbytes_eq_unsigned; vm_compute; reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Lemma fland_mask_lt : forall x nb, 0 <= nb -> 0 <= Z.land x (2^nb - 1) < 2^nb.
Proof.
  intros x nb Hn. replace (2^nb - 1) with (Z.ones nb) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.
