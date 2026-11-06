(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface RT_iface2 D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import AFrameKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition fr_room {AR : ARun} (d : nat) (st : ST) (OW LB : list block) : Prop :=
  fr_depth_ok d /\ cnt_bal st OW + Z.of_nat (length LB) + 65 + 2 * Z.of_nat d <= LIVE_MAX.

Lemma fr_room_depth : forall {AR : ARun} d st OW LB, fr_room d st OW LB -> fr_depth_ok d.
Proof. intros AR d st OW LB [H _]. exact H. Qed.

Lemma fr_room_le : forall {AR : ARun} d d' st OW LB, fr_room d st OW LB -> (d' <= d)%nat -> fr_room d' st OW LB.
Proof. intros AR d d' st OW LB [H1 H2] L. split; [exact (fr_depth_le d d' H1 L) | lia]. Qed.

Lemma fr_room_eq : forall {AR : ARun} d st OW st' OW' LB, fr_room d st OW LB -> cnt_eq st OW st' OW' -> fr_room d st' OW' LB.
Proof. intros AR d st OW st' OW' LB [H1 H2] E. unfold cnt_eq in E. split; [exact H1 | lia]. Qed.

Lemma fr_room_intro : forall {AR : ARun} d st OW LB, @ar_FR AR = [] -> (d <= FRAMES_MAX)%nat ->
  cnt_bal st OW + Z.of_nat (length LB) + 65 + 2 * Z.of_nat d <= LIVE_MAX -> fr_room d st OW LB.
Proof. intros AR d st OW LB E Hd H. split; [unfold fr_depth_ok; rewrite E; cbn [length]; lia | exact H]. Qed.

Lemma fr_room_push : forall {AR : ARun} d f k st OW LB (objs : list block), fr_room (S d) st OW LB -> (length objs <= 2)%nat ->
  (length (@ar_FR AR) < FRAMES_MAX)%nat /\ @fr_room (push AR f k) d st OW (objs ++ LB) /\ cnt_ok st OW (objs ++ LB).
Proof.
  intros AR d f k st OW LB objs [H1 H2] L. destruct (fr_depth_push d f k H1) as [X Y].
  assert (E : Z.of_nat (length (objs ++ LB)) <= Z.of_nat (length LB) + 2) by (rewrite length_app; lia).
  split; [exact X|]. split; [split; [exact Y | lia] | unfold cnt_ok; lia].
Qed.

Lemma fr_room_callee : forall {AR : ARun} d d' st OW st' OW' LB, fr_room d st OW LB -> cnt_eq st OW st' OW' -> (d' <= d)%nat -> fr_room d' st' OW' LB.
Proof. intros AR d d' st OW st' OW' LB H E L. exact (fr_room_le d d' st' OW' LB (fr_room_eq d st OW st' OW' LB H E) L). Qed.
