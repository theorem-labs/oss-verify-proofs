(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLearn SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjInvPath SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Ghost S2G2 S2Lin S2WalkVC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Local Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma u_rng : forall (w : word), 0 <= u w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. exact H. Qed.

Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> u (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.

Lemma u_litm : forall z, u (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma u_esub2 : forall E a b, u (edenot E (esub2 a b)) = (u (edenot E a) - u (edenot E b)) mod 2 ^ 64.
Proof. intros E a b. unfold esub2. cbn [edenot]. rewrite alu_sub. unfold v_sub. apply u_litm. Qed.

Lemma u_eaddl : forall E a k, u (edenot E (eaddl a k)) = (u (edenot E a) + k mod 2 ^ 64) mod 2 ^ 64.
Proof. intros E a k. unfold eaddl. cbn [edenot]. rewrite alu_add. unfold v_add. rewrite !u_litm. reflexivity. Qed.

Lemma u_emul' : forall E k a, u (edenot E (emul k a)) = ((k mod 2 ^ 64) * u (edenot E a)) mod 2 ^ 64.
Proof. intros E k a. rewrite u_emul. rewrite u_litm. reflexivity. Qed.

Lemma u_add_gen : forall E a b, u (edenot E (EAlu ALU_ADD a b)) = (u (edenot E a) + u (edenot E b)) mod 2 ^ 64.
Proof. intros E a b. cbn [edenot]. rewrite alu_add. unfold v_add. apply u_litm. Qed.

Lemma alu_or_u : forall a b : word, u (alu64 ALU_OR a b) = Z.lor (u a) (u b).
Proof. intros a b. cbn [alu64 alu]. apply bv_or_unsigned. Qed.
Lemma alu_and_u : forall a b : word, u (alu64 ALU_AND a b) = Z.land (u a) (u b).
Proof. intros a b. cbn [alu64 alu]. apply bv_and_unsigned. Qed.

(* [comment removed for export] *)
Lemma sub_exact : forall x y lo hi, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 63 -> 0 <= lo -> hi < 2 ^ 63 ->
  lo <= (x - y) mod 2 ^ 64 <= hi -> lo <= x - y <= hi.
Proof.
  intros x y lo hi Hx Hy Hlo Hhi H. destruct (Z_le_gt_dec y x) as [L|G].
  - rewrite Z.mod_small in H by lia. exact H.
  - replace ((x - y) mod 2 ^ 64) with (x - y + 2 ^ 64) in H; [lia|].
    rewrite <- (Z.mod_small (x - y + 2 ^ 64) (2 ^ 64)) by lia. rewrite <- Z.add_mod_idemp_r by lia.
    rewrite Z.mod_same by lia. rewrite Z.add_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma krange_den : forall segs E m e lo hi, kentry_ok segs E m (KRange e lo hi) -> lo <= u (edenot E e) <= hi.
Proof. intros segs E m e lo hi H. exact H. Qed.

Lemma kimp_ok : forall segs E m kn K, know_ok segs E m kn -> kimp segs kn K = true -> kentry_ok segs E m K.
Proof. intros segs E m kn K HK H. exact (ST.kimplied_ok segs E m kn K HK H). Qed.

Lemma kimp_range : forall segs E m kn e lo hi, know_ok segs E m kn -> kimp segs kn (KRange e lo hi) = true ->
  lo <= u (edenot E e) <= hi.
Proof. intros segs E m kn e lo hi HK H. exact (kimp_ok segs E m kn _ HK H). Qed.

(* [comment removed for export] *)
Lemma kimp_sub : forall segs E m kn a b lo hi, know_ok segs E m kn -> kimp segs kn (KRange (esub2 a b) lo hi) = true ->
  0 <= lo -> hi < 2 ^ 63 -> u (edenot E b) < 2 ^ 63 -> lo <= u (edenot E a) - u (edenot E b) <= hi.
Proof.
  intros segs E m kn a b lo hi HK H Hlo Hhi Hb. pose proof (kimp_range segs E m kn _ _ _ HK H) as R. rewrite u_esub2 in R.
  pose proof (u_rng (edenot E a)). pose proof (u_rng (edenot E b)). apply sub_exact; lia.
Qed.

(* [comment removed for export] *)
Lemma rel_den : forall E a X, u (edenot E (rel a X)) = (u (adenot E a) - u (edenot E X)) mod 2 ^ 64.
Proof.
  intros E a X. unfold rel. rewrite nsub_den. rewrite alu_sub. unfold v_sub. rewrite u_litm. f_equal.
  unfold adenot, v_addi, eaddl. cbn [edenot]. rewrite alu_add. unfold v_add.
  rewrite !u_litm. f_equal. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rel_addr : forall E a X, u (edenot E X) + u (edenot E (rel a X)) < 2 ^ 64 ->
  u (adenot E a) = u (edenot E X) + u (edenot E (rel a X)).
Proof.
  intros E a X H. rewrite rel_den in *. pose proof (u_rng (adenot E a)). pose proof (u_rng (edenot E X)).
  destruct (Z_le_gt_dec (u (edenot E X)) (u (adenot E a))) as [L|G].
  - rewrite Z.mod_small by lia. lia.
  - exfalso. replace ((u (adenot E a) - u (edenot E X)) mod 2 ^ 64) with (u (adenot E a) - u (edenot E X) + 2 ^ 64) in H; [lia|].
    rewrite <- (Z.mod_small (u (adenot E a) - u (edenot E X) + 2 ^ 64) (2 ^ 64)) by lia.
    rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mod_same by lia. rewrite Z.add_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mbytes_rdn : forall segs M a bs i w, mbytes M a bs -> 0 <= a -> 0 <= i -> i + Z.of_nat w <= Z.of_nat (length bs) ->
  a + Z.of_nat (length bs) <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 (a + i)) w = Some (firstn w (skipn (Z.to_nat i) bs)).
Proof.
  intros segs M a bs i w H Ha Hi Hw Hb. revert i Hi Hw.
  induction w as [|w IH]; intros i Hi Hw; [reflexivity|].
  cbn [rdn]. rewrite (H i) by lia.
  replace (Z_to_bv 64 (a + i) + 1)%bv with (Z_to_bv 64 (a + (i + 1))).
  2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia.
      change (bv_unsigned (1%bv : word)) with 1. f_equal. lia. }
  rewrite (IH (i + 1)) by lia.
  destruct (skipn (Z.to_nat i) bs) as [|b r] eqn:Hs.
  - exfalso. pose proof (f_equal (@length byte) Hs) as L. rewrite length_skipn in L. cbn in L. lia.
  - replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    assert (Hn : nth (Z.to_nat i) bs (Z_to_bv 8 0) = b).
    { rewrite <- (firstn_skipn (Z.to_nat i) bs), app_nth2; rewrite length_firstn; [|lia].
      replace (Z.to_nat i - Nat.min (Z.to_nat i) (length bs))%nat with 0%nat by lia. rewrite Hs. reflexivity. }
    rewrite Hn. rewrite <- (skipn_skipn 1 (Z.to_nat i)). rewrite Hs. reflexivity.
Qed.

Lemma u32bytes_cell : forall l j, 0 <= j < zlength l ->
  firstn 4 (skipn (Z.to_nat (4 * j)) (u32bytes l)) = word_to_le_bytes 4 (Z_to_bv 64 (znth l j)).
Proof.
  induction l as [|x l IH]; intros j Hj; unfold zlength in Hj; cbn [length] in Hj; [lia|].
  cbn [u32bytes]. destruct (Z.eq_dec j 0) as [->|N].
  - replace (znth (x :: l) 0) with x by reflexivity. change (Z.to_nat (4 * 0)) with 0%nat. rewrite skipn_O.
    rewrite firstn_app. assert (L4 : length (word_to_le_bytes 4 (Z_to_bv 64 x)) = 4%nat)
      by (unfold word_to_le_bytes; apply length_Z_to_le_bytes).
    rewrite L4, firstn_all2 by lia. replace (4 - 4)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
  - replace (Z.to_nat (4 * j)) with (4 + Z.to_nat (4 * (j - 1)))%nat by lia.
    assert (L4 : length (word_to_le_bytes 4 (Z_to_bv 64 x)) = 4%nat)
      by (unfold word_to_le_bytes; apply length_Z_to_le_bytes).
    rewrite skipn_app. rewrite L4. rewrite skipn_all2 by (rewrite L4; lia). cbn [app].
    replace (4 + Z.to_nat (4 * (j - 1)) - 4)%nat with (Z.to_nat (4 * (j - 1))) by lia.
    rewrite IH by (unfold zlength; lia). unfold znth. destruct (j <? 0) eqn:J; [lia|].
    destruct (j - 1 <? 0) eqn:J1; [lia|]. replace (Z.to_nat j) with (S (Z.to_nat (j - 1))) by lia. reflexivity.
Qed.

Lemma le4_val : forall x, 0 <= x < 2 ^ 32 -> bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 x)) = x.
Proof.
  intros x Hx. unfold word_to_le_bytes. rewrite u_lit by lia. rewrite bytes_le_to_Z_of_le_bytes by lia.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). apply Z.mod_small. lia.
Qed.

Lemma bufbytes_nth : forall d i, Forall (fun c => 0 <= c < 256) d -> 0 <= i < zlength d + 64 ->
  nth (Z.to_nat i) (bufbytes d) (Z_to_bv 8 0) = Z_to_bv 8 (byte_at d i).
Proof.
  intros d i HF Hi. unfold bufbytes, byte_at. rewrite map_nth.
  f_equal. destruct (Z_lt_ge_dec i (zlength d)) as [L|G].
  - rewrite app_nth1 by (unfold zlength in L; lia). reflexivity.
  - rewrite app_nth2 by (unfold zlength in G; lia). rewrite nth_repeat. rewrite nth_overflow by (unfold zlength in G; lia). reflexivity.
Qed.

Lemma byte_at_rng : forall d i, Forall (fun c => 0 <= c < 256) d -> 0 <= byte_at d i < 256.
Proof.
  intros d i HF. unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat i) (length d)) as [L|G].
  - apply (proj1 (Forall_forall _ _) HF). apply nth_In. exact L.
  - rewrite nth_overflow by exact G. lia.
Qed.

(* [comment removed for export] *)
Section S1.
  Variables (data idxs : list Z).
  Local Notation n := (zlength idxs - 3).
  Hypothesis HS : S1OUT data idxs n.

  Lemma idx_rng : forall j, 0 <= j <= n + 2 -> 0 <= znth idxs j <= zlength data.
  Proof.
    intros j Hj. destruct HS as [Hn Hl Hlt Hinc [H0 [H1 H2]] Hstr].
    destruct (Z_lt_ge_dec j n) as [L|G]; [pose proof (Hlt j ltac:(lia)); lia|].
    destruct (Z.eq_dec j n) as [->|N1]; [lia|]. destruct (Z.eq_dec j (n + 1)) as [->|N2]; [lia|].
    replace j with (n + 2) by lia. lia.
  Qed.

  Lemma idx_real : forall j, 0 <= j <= n + 1 -> znth idxs j < zlength data -> j < n.
  Proof.
    intros j Hj H. destruct HS as [Hn Hl Hlt Hinc [H0 [H1 H2]] Hstr].
    destruct (Z_lt_ge_dec j n) as [L|G]; [exact L|]. exfalso.
    destruct (Z.eq_dec j n) as [->|N1]; [lia|]. replace j with (n + 1) in H by lia. lia.
  Qed.

  Lemma idx_mono : forall j, 0 <= j -> j + 1 <= n -> znth idxs j < znth idxs (j + 1).
  Proof.
    intros j Hj H. destruct HS as [Hn Hl Hlt Hinc [H0 [H1 H2]] Hstr].
    destruct (Z.eq_dec (j + 1) n) as [E|N].
    - rewrite E, H0. pose proof (Hlt j ltac:(lia)). lia.
    - apply Hinc. lia.
  Qed.
End S1.

Lemma zlength_u32 : forall l, Z.of_nat (length (u32bytes l)) = 4 * zlength l.
Proof. intros l. rewrite u32bytes_length. unfold zlength. lia. Qed.
