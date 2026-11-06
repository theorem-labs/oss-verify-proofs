(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK14 YK1a YK0u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState}.
Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.
Fixpoint zstores (m : word -> option byte) (d : word) (ws : list (Z * nat)) : word -> option byte :=
match ws with
| [] => m
| (o, n) :: ws' => zstores (wbytes m (Z_to_bv 64 (bv_unsigned d + o)) (zeros n)) d ws'
end.
Definition covers_off (i : Z) (on : Z * nat) : bool :=
(fst on <=? i) && (i <? fst on + Z.of_nat (snd on)).
Definition ws_inb (ws : list (Z * nat)) (N : Z) : bool :=
forallb (fun on => (0 <=? fst on) && (fst on + Z.of_nat (snd on) <=? N)) ws.
Fixpoint iota_Z (i : Z) (k : nat) : list Z :=
match k with O => [] | S k' => i :: iota_Z (i + 1) k' end.
Definition ws_cover (ws : list (Z * nat)) (N : nat) : bool :=
forallb (fun i => existsb (covers_off i) ws) (iota_Z 0 N).
Lemma forallb_In : forall {A} (f : A -> bool) l x, forallb f l = true -> In x l -> f x = true.
Proof.
induction l as [|y l IH]; intros x H Hin; [contradiction|].
cbn in H. apply andb_true_iff in H as [Hy Hl].
destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

Lemma existsb_false_forall : forall {A} (f : A -> bool) l,
existsb f l = false -> forall x, In x l -> f x = false.
Proof.
induction l as [|y l IH]; intros H x Hin; [contradiction|].
cbn in H. apply orb_false_iff in H as [Hy Hl].
destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

Lemma length_zeros : forall n, length (zeros n) = n.
Proof. intro n. apply repeat_length. Qed.



Section c.
Variable d : word.
Variable N : Z.
Hypothesis Hnw : bv_unsigned d + N < 2^64.



End c.
End b.
