(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 State MemProofs.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import St.
Open Scope Z_scope.
Unset Lia Cache.

Definition LOW_N : nat := Z.to_nat 77920.
Definition low_readable_b : bool :=
  forallb (fun i : nat => match memory_read asegs (Z_to_bv 64 (0x10000 + Z.of_nat i)) 1 with Some (_ :: _) => true | _ => false end) (seq 0 LOW_N).
Lemma low_readable_ok : low_readable_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma low_readable : forall (m : word -> option byte) a, 0x10000 <= a < 0x22c60 -> rb asegs m a <> None.
Proof.
  intros m a Ha. pose proof (proj1 (forallb_forall _ _) low_readable_ok (Z.to_nat (a - 0x10000))) as X.
  specialize (X ltac:(apply in_seq; unfold LOW_N; lia)). cbv beta in X. rewrite Z2Nat.id in X by lia.
  replace (0x10000 + (a - 0x10000)) with a in X by lia.
  destruct (memory_read asegs (Z_to_bv 64 a) 1) as [[|b rest]|] eqn:MR; try discriminate X.
  exact (MemP.rb_rom asegs m a b rest MR).
Qed.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import St.
Open Scope Z_scope.
Unset Lia Cache.

Definition LOW_N : nat := Z.to_nat 77920.
Definition low_readable_b : bool :=
  forallb (fun i : nat => match memory_read bsegs (Z_to_bv 64 (0x10000 + Z.of_nat i)) 1 with Some (_ :: _) => true | _ => false end) (seq 0 LOW_N).
Lemma low_readable_ok : low_readable_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma low_readable : forall (m : word -> option byte) a, 0x10000 <= a < 0x22d00 -> rb bsegs m a <> None.
Proof.
  intros m a Ha. pose proof (proj1 (forallb_forall _ _) low_readable_ok (Z.to_nat (a - 0x10000))) as X.
  specialize (X ltac:(apply in_seq; unfold LOW_N; lia)). cbv beta in X. rewrite Z2Nat.id in X by lia.
  replace (0x10000 + (a - 0x10000)) with a in X by lia.
  destruct (memory_read bsegs (Z_to_bv 64 a) 1) as [[|b rest]|] eqn:MR; try discriminate X.
  exact (MemP.rb_rom bsegs m a b rest MR).
Qed.
End TwinB.
