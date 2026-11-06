(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ACnt24 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Stdlib.ZArith.BinInt.Z.le"; "cnt24"; "Stdlib.ZArith.BinInt.Z.add"; "C24MAX"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "win24"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.lt"].


Definition win24 (n : Z) : bool := (5889 <=? n) && (n <=? 7936).
Definition C24MAX : Z := 262144.

Definition cnt24 (LB : list blk) : Z := Z.of_nat (length (filter (fun b => win24 (snd b)) LB)).

Lemma cnt24_nil : cnt24 [] = 0.
Proof. reflexivity. Qed.

Lemma cnt24_nonneg : forall LB, 0 <= cnt24 LB.
Proof. intros. unfold cnt24. lia. Qed.

Lemma cnt24_cons : forall b LB, cnt24 (b :: LB) = cnt24 LB + (if win24 (snd b) then 1 else 0).
Proof.
  intros b LB. unfold cnt24. cbn [filter]. destruct (win24 (snd b)); cbn [length]; lia.
Qed.

Lemma cnt24_cons_le : forall b LB, cnt24 LB <= cnt24 (b :: LB) <= cnt24 LB + 1.
Proof. intros b LB. rewrite cnt24_cons. destruct (win24 (snd b)); cbv iota; lia. Qed.

(* [comment removed for export] *)
Lemma cnt24_cons_out : forall A n LB, win24 n = false -> cnt24 ((A, n) :: LB) = cnt24 LB.
Proof. intros A n LB H. rewrite cnt24_cons. cbn [snd]. rewrite H. lia. Qed.

Lemma cnt24_cons_small : forall A n LB, n < 5889 -> cnt24 ((A, n) :: LB) = cnt24 LB.
Proof. intros A n LB H. apply cnt24_cons_out. unfold win24. apply andb_false_iff. left. apply Z.leb_gt. exact H. Qed.

Lemma cnt24_cons_big : forall A n LB, 7936 < n -> cnt24 ((A, n) :: LB) = cnt24 LB.
Proof. intros A n LB H. apply cnt24_cons_out. unfold win24. apply andb_false_iff. right. apply Z.leb_gt. exact H. Qed.

Lemma cnt24_app : forall L1 L2, cnt24 (L1 ++ L2) = cnt24 L1 + cnt24 L2.
Proof. intros. unfold cnt24. rewrite filter_app, length_app. apply Nat2Z.inj_add. Qed.

Lemma cnt24_le_length : forall LB, cnt24 LB <= Z.of_nat (length LB).
Proof. intros. unfold cnt24. apply Nat2Z.inj_le. apply filter_length_le. Qed.

Lemma cnt24_lb_remove : forall A LB, cnt24 (lb_remove A LB) <= cnt24 LB.
Proof.
  induction LB as [|b r IH]; cbn [lb_remove]; [lia|].
  destruct (Z.eqb (fst b) A).
  - pose proof (cnt24_cons_le b r). lia.
  - rewrite !cnt24_cons. destruct (win24 (snd b)); cbv iota; lia.
Qed.

Lemma cnt24_lb_remove_all : forall nodes LB, cnt24 (lb_remove_all nodes LB) <= cnt24 LB.
Proof.
  induction nodes as [|a r IH]; intros LB; cbn [lb_remove_all]; [lia|].
  pose proof (IH (lb_remove a LB)). pose proof (cnt24_lb_remove a LB). lia.
Qed.

Lemma cnt24_filter : forall (f : blk -> bool) LB, cnt24 (filter f LB) <= cnt24 LB.
Proof.
  induction LB as [|b r IH]; cbn [filter]; [lia|].
  destruct (f b); rewrite ?cnt24_cons; destruct (win24 (snd b)); cbv iota; lia.
Qed.

(* [comment removed for export] *)
Lemma cnt24_incl : forall L1 L2, NoDup L1 -> incl L1 L2 -> cnt24 L1 <= cnt24 L2.
Proof.
  intros L1 L2 ND HI. unfold cnt24. apply Nat2Z.inj_le. apply NoDup_incl_length.
  - apply NoDup_filter. exact ND.
  - intros b Hb. apply filter_In in Hb. apply filter_In. split; [apply HI; exact (proj1 Hb)| exact (proj2 Hb)].
Qed.

(* [comment removed for export] *)
Lemma win24_lit_premise : forall n (LB : list blk), win24 n = false -> win24 n = true -> cnt24 LB < C24MAX.
Proof. intros n LB H1 H2. rewrite H1 in H2. discriminate. Qed.

Ltac c24_lit := first [ apply win24_lit_premise; reflexivity | let W := fresh "W" in intros W; vm_compute in W; discriminate W ].

(* [comment removed for export] *)
Lemma cnt24_room : ltac2:(CDefT.buildp (gd_tbl_ACnt24 ()) "Pn,$0.PLBc,(1.$2.)Pbase,$0.PK,$0.P,(3.(4.R3.)R2.)P,(3.(5.R3.R2.)$6.)P,(3.+1.R3.)P,(7.$8.(9.R7.)$:.)(;.(4.R7.)$6.)")
(* [comment removed for export] *).
Proof. intros. lia. Qed.

(* [comment removed for export] *)
Definition c24_transition : Prop := forall LB : list blk, cnt24 LB < C24MAX.
Lemma c24_of_transition : c24_transition -> forall n (LB : list blk), win24 n = true -> cnt24 LB < C24MAX.
Proof. intros T n LB _. apply T. Qed.
