(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seg0B : exists s rest, bsegs = s :: rest /\ seg_base s = 0x10000%N /\ seg_size s = 0x34000%N /\ seg_writable s = false.
Proof. unfold bsegs. lazymatch goal with |- context [?l = _ :: _] => let l' := eval hnf in l in lazymatch l' with ?s :: ?r => exists s, r; split; [reflexivity|]; repeat split; vm_compute; reflexivity end end. Qed.

Lemma ro_addr_seg0B : forall x, 0x10000 <= x < 0x44000 -> ro_addr bsegs (Z_to_bv 64 x) = true.
Proof.
intros x Hx. destruct seg0B as (s & rest & E & B & S & Wr). unfold ro_addr. rewrite E. cbn [find_segment]. rewrite B, S.
rewrite (unsigned_small64 x) by lia.
replace (Z.of_N 65536 <=? x) with true by (symmetry; apply Z.leb_le; lia).
replace (x + 1 <=? Z.of_N 65536 + Z.of_N 212992) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb]. rewrite Wr. reflexivity.
Qed.

Lemma ro_cells_rodataB : forall (m m' : word -> option byte) A cs, mem_inv bsegs m -> mem_inv bsegs m' ->
0x10000 <= A -> A + Z.of_nat (cells_size cs) <= 0x44000 -> ro_cells bsegs m A cs -> ro_cells bsegs m' A cs.
Proof.
intros m m' A cs MI MI' HA HB [WF (B0 & B1 & BA)]. split; [exact WF|]. split; [exact B0|]. split; [exact B1|].
intros i Hi. rewrite <- (BA i Hi).
assert (Li : Z.of_nat (length (cells_bytes cs)) = Z.of_nat (cells_size cs)) by (rewrite cells_bytes_length by exact WF; reflexivity).
assert (RO : ro_addr bsegs (wa (A + Z.of_nat i)) = true) by (apply ro_addr_seg0B; lia).
unfold mrd. destruct (m' (wa (A + Z.of_nat i))) eqn:E1; [pose proof (mem_inv_ro bsegs _ _ _ MI' E1); congruence|].
destruct (m (wa (A + Z.of_nat i))) eqn:E2; [pose proof (mem_inv_ro bsegs _ _ _ MI E2); congruence|]. reflexivity.
Qed.
