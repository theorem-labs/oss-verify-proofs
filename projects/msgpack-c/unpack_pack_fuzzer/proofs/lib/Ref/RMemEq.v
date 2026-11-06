(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_MallocHINV A_Malloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition memeq (m m' : word -> option byte) : Prop := forall x, m' x = m x.

Lemma memeq_refl m : memeq m m. Proof. intros x; reflexivity. Qed.
Lemma memeq_sym m m' : memeq m m' -> memeq m' m. Proof. intros H x; symmetry; apply H. Qed.
Lemma memeq_trans m1 m2 m3 : memeq m1 m2 -> memeq m2 m3 -> memeq m1 m3.
Proof. intros H1 H2 x. rewrite (H2 x). apply H1. Qed.

Lemma memeq_write_same : forall m a bs,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall i, (i < length bs)%nat -> m (wa (a + Z.of_nat i)) = nth_error bs i) ->
  memeq m (write_to_mem m (wa a) bs).
Proof.
  intros m a bs Ha Hl Hb x. rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
  rewrite <- (Hb (Z.to_nat (bv_unsigned x - a))) by lia.
  replace (a + Z.of_nat (Z.to_nat (bv_unsigned x - a))) with (bv_unsigned x) by lia.
  unfold wa. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma memeq_write : forall m m' a bs, memeq m m' -> memeq (write_to_mem m a bs) (write_to_mem m' a bs).
Proof.
  intros m m' a bs. revert m m' a. induction bs as [|b bs IH]; intros m m' a H; cbn [write_to_mem]; [exact H|].
  apply IH. intros x. destruct (bv_eqb x a); [reflexivity| apply H].
Qed.

Section WithSegs.
Variable segs : list MemImageType.Segment.

Lemma mrd_memeq m m' x : memeq m m' -> mrd segs m' x = mrd segs m x.
Proof. intros H. unfold mrd. rewrite (H x). reflexivity. Qed.

Lemma wview_memeq m m' x : memeq m m' -> wview segs m' x = wview segs m x.
Proof. intros H. unfold wview. rewrite (H x). reflexivity. Qed.

Lemma rdn_memeq m m' : memeq m m' -> forall n x, rdn segs m' x n = rdn segs m x n.
Proof.
  intros H. induction n as [|n IH]; intros x; [reflexivity|]. cbn [rdn]. rewrite (H x), IH. reflexivity.
Qed.

Lemma ov_read_bytes_memeq m m' x n : memeq m m' -> ov_read_bytes segs m' x n = ov_read_bytes segs m x n.
Proof. intros H. rewrite !ov_rdn. apply rdn_memeq. exact H. Qed.

Lemma bytes_at_memeq m m' a bs : memeq m m' -> bytes_at segs m a bs -> bytes_at segs m' a bs.
Proof. intros H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi. rewrite (mrd_memeq m m') by exact H. auto. Qed.

Lemma wr_at_memeq m m' a n : memeq m m' -> wr_at segs m a n -> wr_at segs m' a n.
Proof. intros H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi. rewrite (wview_memeq m m') by exact H. auto. Qed.

Lemma cells_at_memeq m m' A cs : memeq m m' -> cells_at segs m A cs -> cells_at segs m' A cs.
Proof. intros H [H1 H2]. split; [exact H1| eapply bytes_at_memeq; eauto]. Qed.

Lemma rw_cells_memeq m m' A cs : memeq m m' -> rw_cells segs m A cs -> rw_cells segs m' A cs.
Proof. intros H [H1 H2]. split; [eapply cells_at_memeq; eauto| eapply wr_at_memeq; eauto]. Qed.

Lemma ro_cells_memeq m m' A cs : memeq m m' -> ro_cells segs m A cs -> ro_cells segs m' A cs.
Proof. intros H H1. eapply cells_at_memeq; eauto. Qed.

Lemma u8arr_memeq m m' A bs : memeq m m' -> u8arr segs m A bs -> u8arr segs m' A bs.
Proof. intros H [H1 H2]. split; [eapply bytes_at_memeq; eauto| eapply wr_at_memeq; eauto]. Qed.

Lemma u64arr_memeq m m' A ws : memeq m m' -> u64arr segs m A ws -> u64arr segs m' A ws.
Proof. intros H [H1 H2]. split; [eapply bytes_at_memeq; eauto| eapply wr_at_memeq; eauto]. Qed.

Lemma stk_memeq m m' lo hi : memeq m m' -> stk segs m lo hi -> stk segs m' lo hi.
Proof.
  intros H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  rewrite (wview_memeq m m'), (mrd_memeq m m') by exact H. auto.
Qed.

Lemma mem_inv_memeq m m' : memeq m m' -> mem_inv segs m -> mem_inv segs m'.
Proof. intros H MI a b Hb. rewrite (H a) in Hb. eapply MI; eauto. Qed.

End WithSegs.

Lemma rmrep_memeq st m m' : memeq m m' -> rmrep st m -> rmrep st m'.
Proof.
  intros H (WF & CX & GL & AR & GR & SH). split; [exact WF|].
  split. { destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
           split; [eapply rw_cells_memeq; eauto|]. split; [eapply u64arr_memeq; eauto|]. split; [eapply u64arr_memeq; eauto|].
           split; [eapply u8arr_memeq; eauto|]. split; [eapply u8arr_memeq; eauto|]. eapply rw_cells_memeq; eauto. }
  split. { destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals.
           split; [eapply rw_cells_memeq; eauto|]. split; [eapply rw_cells_memeq; eauto|]. split; [eapply rw_cells_memeq; eauto|].
           split; [eapply rw_cells_memeq; eauto|]. eapply rw_cells_memeq; eauto. }
  split. { intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). split; [eapply rw_cells_memeq; eauto|].
           split; [intros k Hk; eapply rw_cells_memeq; eauto| eapply rw_cells_memeq; eauto]. }
  split. { intros b gh Hb. destruct (GR b gh Hb) as (w8 & R1 & R2). exists w8. split; [eapply rw_cells_memeq; eauto| exact R2]. }
  intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [S1 S2]. split; [eapply wr_at_memeq; eauto|].
  intros o v Ho Hc. destruct (S2 o v Ho Hc) as [B1 B2]. split; [eapply bytes_at_memeq; eauto| exact B2].
Qed.

Lemma RHEAP_memeq s LB m m' : memeq m m' -> RHEAP s LB m -> RHEAP s LB m'.
Proof.
  intros H (st & LB0 & P & E & MR & HI). exists st, LB0. split; [exact P|]. split; [exact E|].
  split; [eapply rmrep_memeq; eauto| exact HI].
Qed.

Lemma rauxv_ok_memeq m m' B : memeq m m' -> rauxv_ok m B -> rauxv_ok m' B.
Proof.
  intros H (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & A1 & A2 & A3 & REST).
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd.
  split; [eapply rw_cells_memeq; eauto|]. split; [eapply bytes_at_memeq; eauto|]. split; [eapply bytes_at_memeq; eauto| exact REST].
Qed.

Lemma rheap_pres_memeq_r LB SP m m1 m2 : memeq m1 m2 -> rheap_pres LB SP m m1 -> rheap_pres LB SP m m2.
Proof.
  intros H HP a Ha Hc. destruct (HP a Ha Hc) as [E W]. rewrite (H (wa a)). split; [exact E|].
  intros Hw. rewrite (wview_memeq rsegs m1 m2) by exact H. auto.
Qed.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface.
Import RMallocRep.TwinB RMallocTree.TwinB RMalloc_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition memeq (m m' : word -> option byte) : Prop := forall x, m' x = m x.

Lemma memeq_refl m : memeq m m. Proof. intros x; reflexivity. Qed.
Lemma memeq_sym m m' : memeq m m' -> memeq m' m. Proof. intros H x; symmetry; apply H. Qed.
Lemma memeq_trans m1 m2 m3 : memeq m1 m2 -> memeq m2 m3 -> memeq m1 m3.
Proof. intros H1 H2 x. rewrite (H2 x). apply H1. Qed.

Lemma memeq_write_same : forall m a bs,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall i, (i < length bs)%nat -> m (wa (a + Z.of_nat i)) = nth_error bs i) ->
  memeq m (write_to_mem m (wa a) bs).
Proof.
  intros m a bs Ha Hl Hb x. rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
  rewrite <- (Hb (Z.to_nat (bv_unsigned x - a))) by lia.
  replace (a + Z.of_nat (Z.to_nat (bv_unsigned x - a))) with (bv_unsigned x) by lia.
  unfold wa. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma memeq_write : forall m m' a bs, memeq m m' -> memeq (write_to_mem m a bs) (write_to_mem m' a bs).
Proof.
  intros m m' a bs. revert m m' a. induction bs as [|b bs IH]; intros m m' a H; cbn [write_to_mem]; [exact H|].
  apply IH. intros x. destruct (bv_eqb x a); [reflexivity| apply H].
Qed.

Section WithSegs.
Variable segs : list MemImageType.Segment.

Lemma mrd_memeq m m' x : memeq m m' -> mrd segs m' x = mrd segs m x.
Proof. intros H. unfold mrd. rewrite (H x). reflexivity. Qed.

Lemma wview_memeq m m' x : memeq m m' -> wview segs m' x = wview segs m x.
Proof. intros H. unfold wview. rewrite (H x). reflexivity. Qed.

Lemma rdn_memeq m m' : memeq m m' -> forall n x, rdn segs m' x n = rdn segs m x n.
Proof.
  intros H. induction n as [|n IH]; intros x; [reflexivity|]. cbn [rdn]. rewrite (H x), IH. reflexivity.
Qed.

Lemma ov_read_bytes_memeq m m' x n : memeq m m' -> ov_read_bytes segs m' x n = ov_read_bytes segs m x n.
Proof. intros H. rewrite !ov_rdn. apply rdn_memeq. exact H. Qed.

Lemma bytes_at_memeq m m' a bs : memeq m m' -> bytes_at segs m a bs -> bytes_at segs m' a bs.
Proof. intros H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi. rewrite (mrd_memeq m m') by exact H. auto. Qed.

Lemma wr_at_memeq m m' a n : memeq m m' -> wr_at segs m a n -> wr_at segs m' a n.
Proof. intros H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi. rewrite (wview_memeq m m') by exact H. auto. Qed.

Lemma cells_at_memeq m m' A cs : memeq m m' -> cells_at segs m A cs -> cells_at segs m' A cs.
Proof. intros H [H1 H2]. split; [exact H1| eapply bytes_at_memeq; eauto]. Qed.

Lemma rw_cells_memeq m m' A cs : memeq m m' -> rw_cells segs m A cs -> rw_cells segs m' A cs.
Proof. intros H [H1 H2]. split; [eapply cells_at_memeq; eauto| eapply wr_at_memeq; eauto]. Qed.

Lemma ro_cells_memeq m m' A cs : memeq m m' -> ro_cells segs m A cs -> ro_cells segs m' A cs.
Proof. intros H H1. eapply cells_at_memeq; eauto. Qed.

Lemma u8arr_memeq m m' A bs : memeq m m' -> u8arr segs m A bs -> u8arr segs m' A bs.
Proof. intros H [H1 H2]. split; [eapply bytes_at_memeq; eauto| eapply wr_at_memeq; eauto]. Qed.

Lemma u64arr_memeq m m' A ws : memeq m m' -> u64arr segs m A ws -> u64arr segs m' A ws.
Proof. intros H [H1 H2]. split; [eapply bytes_at_memeq; eauto| eapply wr_at_memeq; eauto]. Qed.

Lemma stk_memeq m m' lo hi : memeq m m' -> stk segs m lo hi -> stk segs m' lo hi.
Proof.
  intros H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  rewrite (wview_memeq m m'), (mrd_memeq m m') by exact H. auto.
Qed.

Lemma mem_inv_memeq m m' : memeq m m' -> mem_inv segs m -> mem_inv segs m'.
Proof. intros H MI a b Hb. rewrite (H a) in Hb. eapply MI; eauto. Qed.

End WithSegs.

Lemma rmrep_memeq st m m' : memeq m m' -> rmrep st m -> rmrep st m'.
Proof.
  intros H (WF & CX & GL & AR & GR & SH). split; [exact WF|].
  split. { destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
           split; [eapply rw_cells_memeq; eauto|]. split; [eapply u64arr_memeq; eauto|]. split; [eapply u64arr_memeq; eauto|].
           split; [eapply u8arr_memeq; eauto|]. split; [eapply u8arr_memeq; eauto|]. eapply rw_cells_memeq; eauto. }
  split. { destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals.
           split; [eapply rw_cells_memeq; eauto|]. split; [eapply rw_cells_memeq; eauto|]. split; [eapply rw_cells_memeq; eauto|].
           split; [eapply rw_cells_memeq; eauto|]. eapply rw_cells_memeq; eauto. }
  split. { intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). split; [eapply rw_cells_memeq; eauto|].
           split; [intros k Hk; eapply rw_cells_memeq; eauto| eapply rw_cells_memeq; eauto]. }
  split. { intros b gh Hb. destruct (GR b gh Hb) as (w8 & R1 & R2). exists w8. split; [eapply rw_cells_memeq; eauto| exact R2]. }
  intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [S1 S2]. split; [eapply wr_at_memeq; eauto|].
  intros o v Ho Hc. destruct (S2 o v Ho Hc) as [B1 B2]. split; [eapply bytes_at_memeq; eauto| exact B2].
Qed.

Lemma RHEAP_memeq s LB m m' : memeq m m' -> RHEAP s LB m -> RHEAP s LB m'.
Proof.
  intros H (st & LB0 & P & E & MR & HI). exists st, LB0. split; [exact P|]. split; [exact E|].
  split; [eapply rmrep_memeq; eauto| exact HI].
Qed.

Lemma rauxv_ok_memeq m m' B : memeq m m' -> rauxv_ok m B -> rauxv_ok m' B.
Proof.
  intros H (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & A1 & A2 & A3 & REST).
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd.
  split; [eapply rw_cells_memeq; eauto|]. split; [eapply bytes_at_memeq; eauto|]. split; [eapply bytes_at_memeq; eauto| exact REST].
Qed.

Lemma rheap_pres_memeq_r LB SP m m1 m2 : memeq m1 m2 -> rheap_pres LB SP m m1 -> rheap_pres LB SP m m2.
Proof.
  intros H HP a Ha Hc. destruct (HP a Ha Hc) as [E W]. rewrite (H (wa a)). split; [exact E|].
  intros Hw. rewrite (wview_memeq rsegs m1 m2) by exact H. auto.
Qed.

End CEIL.
End TwinB.
