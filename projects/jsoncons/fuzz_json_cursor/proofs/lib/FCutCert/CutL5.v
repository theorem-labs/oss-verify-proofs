(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutHeap.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CL5.
Section WithSegs.
Variable segs : list Segment.

Lemma u_lin : forall E e v, lden E (lin_of e) = v -> 0 <= v < 2 ^ 64 -> bv_unsigned (edenot E e) = v.
Proof.
  intros E e v H Hv. pose proof (lin_of_sound E e) as [q Hq]. unfold uE in Hq. rewrite H in Hq.
  pose proof (u64_range (edenot E e)) as Hu. unfold two64 in Hu. nia.
Qed.
Lemma elen_lin : forall E e v, lden E (lin_of e) = v -> 0 <= v < 2 ^ 64 -> elenZ E e = v.
Proof. intros. unfold elenZ. apply u_lin; assumption. Qed.
Lemma estart_lin : forall E b o v, lden E (lin_of b) = v -> 0 <= v < 2 ^ 64 -> estart E (SA b o) = v + o.
Proof. intros E b o v H Hv. unfold estart. cbn [a_base a_off]. rewrite (u_lin E b v H Hv). reflexivity. Qed.
Lemma adenot_start : forall E a n, flat E a n -> adenot E a = Z_to_bv 64 (estart E a).
Proof.
  intros E a n Hfl. apply bv_eq. rewrite (flat_u E a n Hfl). rewrite Z_to_bv_unsigned. unfold bv_wrap. symmetry. apply Z.mod_small.
  destruct Hfl as (F1 & F2 & _). change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma krange_intro : forall E M e lo hi v, lden E (lin_of e) = v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> kentry_ok segs E M (KRange e lo hi).
Proof. intros E M e lo hi v H Hv Hr. cbn [kentry_ok]. rewrite (u_lin E e v H Hv). exact Hr. Qed.
Lemma kalign_intro : forall E M e m v, lden E (lin_of e) = v -> 0 <= v < 2 ^ 64 -> 0 < m -> v mod m = 0 -> kentry_ok segs E M (KAlign e m).
Proof. intros E M e m v H Hv Hm Hr. cbn [kentry_ok]. rewrite (u_lin E e v H Hv). split; assumption. Qed.
Lemma kdisj_intro : forall E M a1 n1 a2 n2 A1 N1 A2 N2, estart E a1 = A1 -> elenZ E n1 = N1 -> estart E a2 = A2 -> elenZ E n2 = N2 ->
  (A1 + N1 <= A2 \/ A2 + N2 <= A1) -> kentry_ok segs E M (KDisj a1 n1 a2 n2).
Proof. intros E M a1 n1 a2 n2 A1 N1 A2 N2 <- <- <- <- H. exact H. Qed.

Lemma kword64_intro : forall E M a v A z, estart E a = A -> 0 <= A -> A + 8 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z ->
  L5.u64_at segs M A z -> kentry_ok segs E M (KWord a 8 v).
Proof.
  intros E M a v A z Ha H0 H8 Hv Hu. cbn [kentry_ok].
  assert (Hfl : flat E a (Z.of_nat 8)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (adenot_start E a _ Hfl), Ha, Hv. exact Hu.
Qed.
Lemma kunk_intro : forall E M a n A N, estart E a = A -> elenZ E n = N -> 0 <= A -> A + N <= 2 ^ 64 -> A < 2 ^ 64 ->
  L5.defined M A N -> kentry_ok segs E M (KUnk a n).
Proof.
  intros E M a n A N Ha Hn H0 H1 H2 Hd. cbn [kentry_ok]. rewrite Ha, Hn.
  split; [unfold flat; rewrite Ha; pose proof (u64_range (edenot E n)); unfold elenZ in Hn; lia|]. intros i Hi. apply Hd. exact Hi.
Qed.
Lemma kwr_intro : forall E M a n A N, estart E a = A -> elenZ E n = N -> 0 <= A -> A + N <= 2 ^ 64 -> A < 2 ^ 64 ->
  L5.defined M A N -> kentry_ok segs E M (KWr a n).
Proof.
  intros E M a n A N Ha Hn H0 H1 H2 Hd. pose proof (kunk_intro E M a n A N Ha Hn H0 H1 H2 Hd) as HU.
  cbn [kentry_ok]. split; [exact (proj1 HU)|]. intros dd m Hdd Hm. exact (kunk_store_ok segs E M a n dd m HU Hdd Hm).
Qed.
Lemma overlay_byte : forall (M : word -> option byte) (x : word) b, rdn segs M x 1 = Some [b] -> M x <> None -> M x = Some b.
Proof. intros M x b H Hd. cbn [rdn] in H. destruct (M x) as [b'|]; [|contradiction]. injection H as ->. reflexivity. Qed.
Lemma kblob_intro : forall E M a n id A (bs : list Z), estart E a = A -> elenZ E n = Z.of_nat (length bs) -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 -> A < 2 ^ 64 ->
  eb E id = map (Z_to_bv 8) bs -> L5.bytes_at segs M A bs -> L5.defined M A (Z.of_nat (length bs)) -> kentry_ok segs E M (KBlob a n id).
Proof.
  intros E M a n id A bs Ha Hn H0 H1 H2 Hb HB Hd. cbn [kentry_ok]. rewrite Ha, Hn, Hb, length_map.
  split; [unfold flat; rewrite Ha; lia|]. split; [reflexivity|]. intros i Hi.
  specialize (HB (Z.to_nat i) ltac:(lia)). unfold L5.u8_at in HB. rewrite Z2Nat.id in HB by lia.
  rewrite (overlay_byte M _ _ HB (Hd i Hi)). f_equal. symmetry. exact (map_nth (Z_to_bv 8) bs 0 (Z.to_nat i)).
Qed.

Lemma kword64_elim : forall E M a v A z, kentry_ok segs E M (KWord a 8 v) -> estart E a = A -> bv_unsigned (edenot E v) = z -> L5.u64_at segs M A z.
Proof.
  intros E M a v A z (_ & Hfl & Hr) Ha Hv. unfold L5.u64_at. rewrite <- Ha, <- (adenot_start E a _ Hfl), Hr. rewrite <- Hv, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma kword8_zero_elim : forall E M a A, kentry_ok segs E M (KWord a 1 (ELit 0)) -> estart E a = A -> L5.u8_at segs M A 0.
Proof. intros E M a A (_ & Hfl & Hr) Ha. unfold L5.u8_at. rewrite <- Ha, <- (adenot_start E a _ Hfl), Hr. reflexivity. Qed.
Lemma kblob_elim : forall E M a n id A (bs : list Z), kentry_ok segs E M (KBlob a n id) -> estart E a = A -> eb E id = map (Z_to_bv 8) bs ->
  L5.bytes_at segs M A bs /\ elenZ E n = Z.of_nat (length bs).
Proof.
  intros E M a n id A bs (Hfl & Hl & Hz) Ha Hb. rewrite Hb, length_map in Hl. split; [|symmetry; exact Hl].
  intros i Hi. unfold L5.u8_at. cbn [rdn]. rewrite <- Ha, (Hz (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id, Hb.
  rewrite (map_nth (Z_to_bv 8) bs 0 i). reflexivity.
Qed.
Lemma kunk_elim : forall E M a n A N, kentry_ok segs E M (KUnk a n) -> estart E a = A -> elenZ E n = N -> L5.defined M A N.
Proof. intros E M a n A N [_ Hz] <- <- i Hi. apply Hz. exact Hi. Qed.

Lemma bytes_at_app : forall M p (s1 s2 : list Z), L5.bytes_at segs M p s1 -> L5.bytes_at segs M (p + Z.of_nat (length s1)) s2 -> L5.bytes_at segs M p (s1 ++ s2).
Proof.
  intros M p s1 s2 H1 H2 i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length s1)) as [Hlt|Hge].
  - rewrite app_nth1 by exact Hlt. apply H1. exact Hlt.
  - rewrite app_nth2 by exact Hge. replace (p + Z.of_nat i) with (p + Z.of_nat (length s1) + Z.of_nat (i - length s1)) by lia. apply H2. lia.
Qed.
End WithSegs.
End CL5.
