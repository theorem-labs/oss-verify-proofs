(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition img_rw_okb (a : Z) : bool :=
  match seg_rom usegs (wa a), wview usegs (fun _ => None) (wa a) with Some _, Some _ => true | _, _ => false end.
Fixpoint rng_okb (n : nat) (a : Z) : bool := match n with O => true | S n' => img_rw_okb a && rng_okb n' (a + 1) end.

Lemma rng_okb_spec : forall n a, rng_okb n a = true -> forall x, a <= x < a + Z.of_nat n -> img_rw_okb x = true.
Proof.
  induction n as [|n IH]; intros a H x Hx; [lia|]. cbn [rng_okb] in H. apply andb_prop in H. destruct H as [H1 H2].
  destruct (Z.eq_dec x a) as [->|NE]; [exact H1|]. apply (IH (a + 1) H2). lia.
Qed.

Lemma cimg_img_ok :
  rng_okb (Z.to_nat (0x31d000 - 0x2c0638)) 0x2c0638 && rng_okb (Z.to_nat (0x31dab0 - 0x31d4a8)) 0x31d4a8 && rng_okb 8 0x32e030 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma cimg_addr_ok : forall a, cimg_addr a -> img_rw_okb a = true.
Proof.
  intros a Ha. pose proof cimg_img_ok as H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  unfold cimg_addr in Ha. destruct Ha as [[Ha _]|[Ha|[Ha|Ha]]].
  - apply (rng_okb_spec _ _ H1). lia.
  - apply (rng_okb_spec _ _ H2). lia.
  - apply (rng_okb_spec _ _ H2). lia.
  - apply (rng_okb_spec _ _ H3). lia.
Qed.

Lemma cimg_byte : forall m a, cimg m -> cimg_addr a -> exists b, mrd usegs m (wa a) = Some b /\ wview usegs m (wa a) <> None.
Proof.
  intros m a C Ha. pose proof (cimg_addr_ok a Ha) as OK. unfold img_rw_okb in OK.
  assert (AR : 0 <= a < 2^64) by (unfold cimg_addr, RMallocRep.RGOT_SSP in Ha; lia).
  assert (NONE : m (wa a) = None) by (apply C; rewrite wa_unsigned by lia; exact Ha).
  destruct (seg_rom usegs (wa a)) as [b|] eqn:Er; [|discriminate].
  destruct (wview usegs (fun _ => None) (wa a)) as [bw|] eqn:Ew; [|discriminate].
  exists b. split; [unfold mrd; rewrite NONE; exact Er|]. unfold wview in *. rewrite NONE. intros X. rewrite X in Ew. discriminate.
Qed.

(* [comment removed for export] *)
Lemma cimg_cell1 : forall m d, cimg m -> cimg_addr d -> exists b, rw_cells usegs m d [CB 1 [b]].
Proof.
  intros m d C Hd. destruct (cimg_byte m d C Hd) as (b & RD & WR).
  assert (AR : 0 <= d < 2^64) by (unfold cimg_addr, RMallocRep.RGOT_SSP in Hd; lia).
  exists b. split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
    assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact RD.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r. exact WR.
Qed.

Lemma cimg_cells : forall n m d, cimg m -> (0 < n)%nat -> (forall x, d <= x < d + Z.of_nat n -> cimg_addr x) -> exists bs, rw_cells usegs m d [CB n bs].
Proof.
  intros n m d C. revert d. induction n as [|n IH]; intros d Hn HR; [lia|].
  destruct (cimg_cell1 m d C (HR d ltac:(lia))) as [b Hb].
  destruct n as [|n].
  - exists [b]. exact Hb.
  - destruct (IH (d + 1) ltac:(lia)) as [bs Hbs]. { intros x Hx. apply HR. lia. }
    exists ([b] ++ bs). change (S (S n)) with (1 + S n)%nat. eapply rw_cells_CB_join; [exact Hb|]. exact Hbs.
Qed.

(* [comment removed for export] *)
Lemma cimg_C8 : forall m d, cimg m -> (forall x, d <= x < d + 8 -> cimg_addr x) -> exists w : word, rw_cells usegs m d [C8 w].
Proof.
  intros m d C HR. destruct (cimg_cells 8 m d C ltac:(lia) HR) as [bs H].
  pose proof (rw_cells_CB_length usegs m d _ _ H) as LEN.
  exists (le_bytes_to_word bs). eapply rw_cells_recast; [exact H| cbn; auto| | reflexivity].
  cbn [cells_bytes cbytes]. rewrite le8_le_bytes_to_word by exact LEN. reflexivity.
Qed.
End WithCeiling0.
