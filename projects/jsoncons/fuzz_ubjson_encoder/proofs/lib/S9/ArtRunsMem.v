(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemSplit ArtMem ArtRuns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma art_le_bytes_zero : forall n, (n <= 8)%nat -> word_to_le_bytes n (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) n.
Proof. intros n Hn. do 9 (destruct n as [|n]; [vm_compute; reflexivity|]). exfalso. lia. Qed.

Lemma art_store_ok_ext : forall segs n (m1 m2 : word -> option byte) (a : word),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> m1 x = m2 x) ->
  store_ok segs m1 a n = store_ok segs m2 a n.
Proof.
  intros segs n. induction n as [|n IH]; intros m1 m2 a Hnw Hext; [reflexivity|].
  cbn [store_ok]. unfold wview. rewrite (Hext a) by (pose proof (u64_range a); lia).
  destruct n as [|n']; [reflexivity|].
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; rewrite !Nat2Z.inj_succ in Hnw; lia).
  rewrite (IH m1 m2 (a + 1)%bv) by (rewrite Hu1; first [rewrite !Nat2Z.inj_succ in *; lia | intros x Hx; apply Hext; rewrite !Nat2Z.inj_succ in *; lia]).
  reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.
#[local] Abbreviation cell := (cell segs).
#[local] Abbreviation wr := (wr segs).
#[local] Abbreviation wok := (wok segs).

Lemma art_cell_agree : forall (M M' : word -> option byte) a (n : nat) v,
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> M' x = M x) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  cell M a n v -> cell M' a n v.
Proof.
  intros M M' a n v AG Ha Hn C. unfold ArtMem.cell in *. rewrite <- C.
  apply rdn_ext. rewrite art_u_lit by lia. lia.
  intros x Hx. rewrite art_u_lit in Hx by lia. apply AG. lia.
Qed.

Lemma art_wr_of_defined : forall (M : word -> option byte) a n, 0 <= a -> a + n < 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + n -> M x <> None) -> wr M a n.
Proof.
  intros M a n Ha Hn D d k Hd Hk. apply store_ok_of_all.
  - rewrite art_u_lit by lia. lia.
  - intros x Hx. rewrite art_u_lit in Hx by lia. unfold wview. destruct (M x) eqn:E; [discriminate|]. exfalso. apply (D x); [lia|exact E].
Qed.

Lemma art_wr_of_wview : forall (M : word -> option byte) a n, 0 <= a -> a + n < 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + n -> wview segs M x <> None) -> wr M a n.
Proof.
  intros M a n Ha Hn D d k Hd Hk. apply store_ok_of_all.
  - rewrite art_u_lit by lia. lia.
  - intros x Hx. rewrite art_u_lit in Hx by lia. apply D. lia.
Qed.
Lemma art_wr_wview : forall (M : word -> option byte) a n, 0 <= a -> a + n < 2 ^ 64 -> wr M a n ->
  forall x : word, a <= bv_unsigned x < a + n -> wview segs M x <> None.
Proof.
  intros M a n Ha Hn W x Hx.
  pose proof (W (bv_unsigned x - a) 1%nat ltac:(lia) ltac:(cbn; lia)) as OK.
  replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in OK by lia. rewrite Z_to_bv_bv_unsigned in OK.
  apply (store_ok_all segs M 1 x); [pose proof (u64_range x); cbn; lia | exact OK | cbn; lia].
Qed.
Lemma wr_join : forall (M : word -> option byte) a n m, 0 <= a -> 0 <= n -> 0 <= m -> a + n + m < 2 ^ 64 ->
  wr M a n -> wr M (a + n) m -> wr M a (n + m).
Proof.
  intros M a n m Ha Hn Hm Hb W1 W2. apply art_wr_of_wview; [lia|lia|]. intros x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) (a + n)) as [L|G].
  - apply (art_wr_wview M a n); [lia|lia|exact W1|lia].
  - apply (art_wr_wview M (a + n) m); [lia|lia|exact W2|lia].
Qed.

Lemma art_zfill_grows : forall M r len, mem_grows M (art_zfill M r len).
Proof. intros M r len x Hx. unfold art_zfill. destruct ((r <=? bv_unsigned x) && (bv_unsigned x <? r + len)); [discriminate|exact Hx]. Qed.
Lemma wr_zfill : forall M r len, 0 <= r -> r + len < 2 ^ 64 -> wr (art_zfill M r len) r len.
Proof. intros M r len Hr Hl. apply art_wr_of_defined; [lia|lia|]. intros x Hx. rewrite art_zfill_in by lia. discriminate. Qed.
Lemma wr_zfill_other : forall M r len a n, wr M a n -> wr (art_zfill M r len) a n.
Proof. intros. eapply wr_grows; [apply art_zfill_grows|assumption]. Qed.
Lemma wok_zfill_other : forall M r len a n, wok M a n -> wok (art_zfill M r len) a n.
Proof. intros. eapply wok_grows; [apply art_zfill_grows|assumption]. Qed.
Lemma cell_zfill_other : forall M r len a n v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> apart r len a (Z.of_nat n) ->
  cell M a n v -> cell (art_zfill M r len) a n v.
Proof. intros M r len a n v Ha Hn A C. eapply art_cell_agree; [|exact Ha|exact Hn|exact C]. intros x Hx. apply art_zfill_out. unfold apart in A. lia. Qed.
Lemma cell_zfill_zero : forall M r len a n, (n <= 8)%nat -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> r <= a -> a + Z.of_nat n <= r + len ->
  cell (art_zfill M r len) a n 0.
Proof.
  intros M r len a n Hn8 Ha Hn Hlo Hhi. unfold ArtMem.cell. rewrite art_le_bytes_zero by exact Hn8.
  apply rdn_const. rewrite art_u_lit by lia. lia.
  intros x Hx. rewrite art_u_lit in Hx by lia. apply art_zfill_in. lia.
Qed.

Lemma art_reveal_grows : forall M lo hi, mem_grows M (art_reveal M lo hi).
Proof. intros M lo hi x Hx. unfold art_reveal. destruct ((lo <=? bv_unsigned x) && (bv_unsigned x <? hi)); [|exact Hx]. destruct (M x); [discriminate|contradiction]. Qed.
Lemma wr_reveal : forall M lo hi, 0 <= lo -> hi < 2 ^ 64 -> wr (art_reveal M lo hi) lo (hi - lo).
Proof. intros M lo hi Hlo Hhi. apply art_wr_of_defined; [lia|lia|]. intros x Hx. apply art_reveal_defined. lia. Qed.
Lemma wr_reveal_other : forall M lo hi a n, wr M a n -> wr (art_reveal M lo hi) a n.
Proof. intros. eapply wr_grows; [apply art_reveal_grows|assumption]. Qed.

Lemma cell_reveal_other : forall M lo hi a n v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> apart lo (hi - lo) a (Z.of_nat n) ->
  cell M a n v -> cell (art_reveal M lo hi) a n v.
Proof. intros M lo hi a n v Ha Hn A C. eapply art_cell_agree; [|exact Ha|exact Hn|exact C]. intros x Hx. apply art_reveal_out. unfold apart in A. lia. Qed.

Lemma cell_unmap_other : forall M r len a n v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> apart r len a (Z.of_nat n) ->
  cell M a n v -> cell (art_unmap M r len) a n v.
Proof. intros M r len a n v Ha Hn A C. eapply art_cell_agree; [|exact Ha|exact Hn|exact C]. intros x Hx. apply art_unmap_out. unfold apart in A. lia. Qed.
Lemma wr_unmap_other : forall M r len a n, 0 <= a -> a + n < 2 ^ 64 -> apart r len a n -> wr M a n -> wr (art_unmap M r len) a n.
Proof.
  intros M r len a n Ha Hn A W d k Hd Hk. pose proof (W d k Hd Hk) as OK.
  destruct (Nat.eq_dec k 0) as [->|NZ]; [reflexivity|].
  rewrite (art_store_ok_ext segs k (art_unmap M r len) M); [exact OK| |]; [rewrite art_u_lit by lia; lia|].
  intros x Hx. rewrite art_u_lit in Hx by lia. apply art_unmap_out. unfold apart in A. lia.
Qed.

End WithSegs.
