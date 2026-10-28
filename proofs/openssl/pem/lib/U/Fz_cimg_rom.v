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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition rom_byte (a : Z) : byte := match seg_rom usegs (wa a) with Some b => b | None => Z_to_bv 8 0 end.
Fixpoint rom_bytes (n : nat) (a : Z) : list byte := match n with O => [] | S n' => rom_byte a :: rom_bytes n' (a + 1) end.
Definition img_w64 (a : Z) : Z := bv_unsigned (le_bytes_to_word (rom_bytes 8 a)).

Lemma rom_bytes_length : forall n a, length (rom_bytes n a) = n.
Proof. induction n as [|n IH]; intros a; cbn [rom_bytes length]; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma img_w64_range : forall a, 0 <= img_w64 a < 2^64.
Proof. intros a. unfold img_w64. pose proof (bv_unsigned_in_range _ (le_bytes_to_word (rom_bytes 8 a))) as R. change (bv_modulus 64) with (2^64) in R. exact R. Qed.

Lemma cimg_byte_rom : forall m a, cimg m -> cimg_addr a -> mrd usegs m (wa a) = Some (rom_byte a) /\ wview usegs m (wa a) <> None.
Proof.
  intros m a C Ha. pose proof (cimg_addr_ok a Ha) as OK. unfold img_rw_okb in OK. unfold rom_byte.
  assert (AR : 0 <= a < 2^64) by (unfold cimg_addr, RMallocRep.RGOT_SSP in Ha; lia).
  assert (NONE : m (wa a) = None) by (apply C; rewrite wa_unsigned by lia; exact Ha).
  destruct (seg_rom usegs (wa a)) as [b|] eqn:Er; [|discriminate].
  destruct (wview usegs (fun _ => None) (wa a)) as [bw|] eqn:Ew; [|discriminate].
  split; [unfold mrd; rewrite NONE; exact Er|]. unfold wview in *. rewrite NONE. intros X. rewrite X in Ew. discriminate.
Qed.

Lemma cimg_cell1_rom : forall m d, cimg m -> cimg_addr d -> rw_cells usegs m d [CB 1 [rom_byte d]].
Proof.
  intros m d C Hd. destruct (cimg_byte_rom m d C Hd) as (RD & WR).
  assert (AR : 0 <= d < 2^64) by (unfold cimg_addr, RMallocRep.RGOT_SSP in Hd; lia).
  split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
    assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact RD.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r. exact WR.
Qed.

Lemma cimg_cells_rom : forall n m d, cimg m -> (0 < n)%nat -> (forall x, d <= x < d + Z.of_nat n -> cimg_addr x) -> rw_cells usegs m d [CB n (rom_bytes n d)].
Proof.
  intros n m d C. revert d. induction n as [|n IH]; intros d Hn HR; [lia|].
  pose proof (cimg_cell1_rom m d C (HR d ltac:(lia))) as Hb.
  destruct n as [|n].
  - exact Hb.
  - assert (Hbs : rw_cells usegs m (d + 1) [CB (S n) (rom_bytes (S n) (d + 1))]) by (apply IH; [lia|]; intros x Hx; apply HR; lia).
    change (S (S n)) with (1 + S n)%nat. change (rom_bytes (1 + S n) d) with ([rom_byte d] ++ rom_bytes (S n) (d + 1)).
    eapply rw_cells_CB_join; [exact Hb|]. exact Hbs.
Qed.

(* [comment removed for export] *)
Lemma img_w64_cell : forall m a, cimg m -> (forall x, a <= x < a + 8 -> cimg_addr x) -> rw_cells usegs m a [C8 (Z_to_bv 64 (img_w64 a))].
Proof.
  intros m a C HR. pose proof (cimg_cells_rom 8 m a C ltac:(lia) HR) as H.
  unfold img_w64. rewrite Z_to_bv_bv_unsigned.
  eapply rw_cells_recast; [exact H| cbn; auto| | reflexivity].
  cbn [cells_bytes cbytes]. rewrite le8_le_bytes_to_word by (apply rom_bytes_length). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint etab (T : Z) (n : nat) : Prop := match n with O => img_w64 T = 0 | S n' => img_w64 T <> 0 /\ etab (T + 16) n' end.
Fixpoint etab_okb (T : Z) (n : nat) : bool := match n with O => img_w64 T =? 0 | S n' => negb (img_w64 T =? 0) && etab_okb (T + 16) n' end.

Lemma etab_okb_spec : forall n T, etab_okb T n = true -> etab T n.
Proof.
  induction n as [|n IH]; intros T H; cbn [etab etab_okb] in *; [apply Z.eqb_eq; exact H|].
  apply andb_prop in H. destruct H as [H1 H2]. split; [| exact (IH _ H2)]. intros E. rewrite E in H1. discriminate.
Qed.

(* [comment removed for export] *)
Definition trange (T : Z) (n : nat) : Prop := forall x, T <= x < T + 16 * (Z.of_nat n + 1) -> cimg_addr x.
Lemma trange_next : forall T n, trange T (S n) -> trange (T + 16) n.
Proof. intros T n H x Hx. apply H. lia. Qed.

(* [comment removed for export] *)
Definition tread (T : Z) (n : nat) : Prop :=
  trange T n \/ (n = 0%nat /\ 0x10000 <= T /\ T + 16 <= 0x2c0000 /\ ro_bytes_b usegs T (cells_bytes [C8 (Z_to_bv 64 0)]) = true).
Lemma tread_trange : forall T n, tread T (S n) -> trange T (S n).
Proof. intros T n [H|(E & _)]; [exact H| discriminate E]. Qed.
Lemma tread_first : forall m T n, cimg m -> mem_inv usegs m -> etab T n -> tread T n ->
  ro_cells usegs m T [C8 (Z_to_bv 64 (img_w64 T))] /\ 0x10000 <= T /\ T + 16 <= 0x32e038.
Proof.
  intros m T n C MI ETAB [TR|(-> & LO & HI & RO)].
  - split; [exact (proj1 (img_w64_cell m T C ltac:(intros x Hx; apply TR; lia)))|].
    pose proof (TR T ltac:(lia)) as X. pose proof (TR (T + 15) ltac:(lia)) as Y. unfold cimg_addr, RMallocRep.RGOT_SSP in X, Y. lia.
  - split; [| lia]. cbn [etab] in ETAB. rewrite ETAB. split; [cbn; auto|].
    apply ro_bytes_at; [exact MI| lia| cbn; lia| apply (ro_bytes_b_sound usegs); exact RO].
Qed.
End WithCeiling0.
