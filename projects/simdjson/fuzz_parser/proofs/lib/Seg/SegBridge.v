(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require PropExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKitA PIosKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S. Import AxSymRun3.
Open Scope Z_scope.

Module SB.
Section S.
Variable segs : list Segment.
Variable E : env.
Variable m : word -> option byte.

Lemma u64s : forall i, 0 <= i < 2^64 -> bv_unsigned (Z_to_bv 64 i) = i.
Proof. intros i Hi. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus; cbn; lia]. Qed.

Lemma kb_range : forall e lo hi, lo <= bv_unsigned (edenot E e) <= hi -> kentry_ok segs E m (KRange e lo hi).
Proof. intros e lo hi H. exact H. Qed.

Lemma kb_align : forall e k, 0 < k -> bv_unsigned (edenot E e) mod k = 0 -> kentry_ok segs E m (KAlign e k).
Proof. intros e k H1 H2. split; assumption. Qed.

Lemma kb_disj : forall a1 n1 a2 n2,
  estart E a1 + elenZ E n1 <= estart E a2 \/ estart E a2 + elenZ E n2 <= estart E a1 -> kentry_ok segs E m (KDisj a1 n1 a2 n2).
Proof. intros a1 n1 a2 n2 H. exact H. Qed.

(* [comment removed for export] *)
Lemma kb_word : forall b k w v,
  (0 < w <= 8)%nat -> 0 <= bv_unsigned (edenot E b) + k ->
  bytes_at segs m (bv_unsigned (edenot E b) + k) (word_to_le_bytes w (edenot E v)) ->
  kentry_ok segs E m (KWord (SA b k) w v).
Proof.
  intros b k w v Hw H0 HB. cbn [kentry_ok]. pose proof (bytes_at_bound segs m _ _ HB) as [A1 A2].
  rewrite length_word_to_le_bytes in A2.
  assert (Hst : estart E (SA b k) = bv_unsigned (edenot E b) + k) by reflexivity.
  split; [lia|]. split; [unfold flat; rewrite Hst; lia|].
  assert (Had : adenot E (SA b k) = wa (bv_unsigned (edenot E b) + k)).
  { unfold adenot, AS.PropExec.v_addi. cbn [a_base a_off]. reflexivity. }
  rewrite Had. pose proof (bytes_at_rdn segs m _ _ 0 w HB ltac:(rewrite length_word_to_le_bytes; lia)) as Hr.
  rewrite Z.add_0_r in Hr. cbn [skipn] in Hr. rewrite <- (length_word_to_le_bytes w (edenot E v)) in Hr at 2.
  rewrite firstn_all in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma kb_wr : forall b k len,
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + bv_unsigned (edenot E len) <= 2^64 ->
  bv_unsigned (edenot E b) + k < 2^64 ->
  (forall x : word, bv_unsigned (edenot E b) + k <= bv_unsigned x < bv_unsigned (edenot E b) + k + bv_unsigned (edenot E len) ->
                    wview segs m x <> None) ->
  kentry_ok segs E m (KWr (SA b k) len).
Proof.
  intros b k len H0 H1 H2 Hw. cbn [kentry_ok]. unfold elenZ, estart. cbn [a_base a_off].
  pose proof (bv_unsigned_in_range 64 (edenot E len)) as RL. unfold bv_modulus in RL. cbn in RL.
  split; [unfold flat, estart, elenZ; cbn [a_base a_off]; lia|].
  intros d mm Hd Hdm. destruct mm as [|mm]; [reflexivity|].
  apply AS.StoreOk.store_ok_of_all; rewrite u64s by lia; [lia|].
  intros x Hx. apply Hw. lia.
Qed.

(* [comment removed for export] *)
Lemma kb_unk : forall b k len,
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + bv_unsigned (edenot E len) <= 2^64 ->
  bv_unsigned (edenot E b) + k < 2^64 ->
  (forall i, 0 <= i < bv_unsigned (edenot E len) -> m (Z_to_bv 64 (bv_unsigned (edenot E b) + k + i)) <> None) ->
  kentry_ok segs E m (KUnk (SA b k) len).
Proof.
  intros b k len H0 H1 H2 Hd. cbn [kentry_ok]. unfold elenZ, estart. cbn [a_base a_off].
  pose proof (bv_unsigned_in_range 64 (edenot E len)) as RL. unfold bv_modulus in RL. cbn in RL.
  split; [unfold flat, estart, elenZ; cbn [a_base a_off]; lia|]. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_overlay : forall A bs, bytes_at segs m A bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> AS.PropExec.seg_rom segs (Z_to_bv 64 (A + i)) = None) ->
  forall i, 0 <= i < Z.of_nat (length bs) -> m (Z_to_bv 64 (A + i)) <> None.
Proof.
  intros A bs (B1 & B2 & HB) Hrom i Hi. specialize (HB (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in HB by lia.
  unfold mrd, wa in HB. specialize (Hrom i Hi). unfold AS.PropExec.seg_rom in Hrom.
  destruct (m (Z_to_bv 64 (A + i))) as [x|]; [discriminate|].
  exfalso. destruct (nth_error bs (Z.to_nat i)) eqn:En; [|apply nth_error_None in En; lia].
  unfold seg_rom in HB. destruct (memory_read segs (Z_to_bv 64 (A + i)) 1) as [[|y ys]|]; discriminate.
Qed.

(* [comment removed for export] *)
Lemma kb_img : forall lo hi, 0 <= lo -> hi <= 2^64 ->
  (forall a : word, lo <= bv_unsigned a < hi -> m a = None) -> kentry_ok segs E m (KImg lo hi).
Proof. intros lo hi H1 H2 H. exact (kn_img segs E m lo hi H1 H2 H). Qed.

(* [comment removed for export] *)
Lemma kx_word : forall b k w v, kentry_ok segs E m (KWord (SA b k) w v) ->
  bytes_at segs m (bv_unsigned (edenot E b) + k) (word_to_le_bytes w (edenot E v)).
Proof.
  intros b k w v (Hw & Hfl & Hrd). pose proof Hfl as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4. cbn [a_base a_off] in F1, F2, F4.
  unfold adenot, AS.PropExec.v_addi in Hrd. cbn [a_base a_off] in Hrd.
  split; [exact F1|]. split; [rewrite length_word_to_le_bytes; exact F4|].
  intros i Hi. rewrite length_word_to_le_bytes in Hi. exact (rdn_nth segs m w _ _ F1 F4 Hrd i Hi).
Qed.

End S.

(* [comment removed for export] *)
Lemma kx_rw8 : forall segs E m m' b k v (old : word),
  kentry_ok segs E m' (KWord (SA b k) 8 v) -> rw_cells segs m (bv_unsigned (edenot E b) + k) [C8 old] -> wmono segs m m' ->
  rw_cells segs m' (bv_unsigned (edenot E b) + k) [C8 (edenot E v)].
Proof.
  intros segs E m m' b k v old HK [[_ _] (W1 & W2 & W3)] HW. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le8. exact (kx_word segs E m' b k 8 v HK).
  - split; [exact W1|]. split; [exact W2|]. intros i Hi. apply HW. apply W3. exact Hi.
Qed.

End SB.
