(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Module ZChkCrc.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZChkAdl.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZChkAdl.ZChkArith.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.


Definition CF (c : Z) (d : list byte) (k : nat) : Z := crc_fold c (firstn k (bZ d)).

Lemma CF_0 : forall c d, CF c d 0 = c. Proof. reflexivity. Qed.

Lemma CF_step : forall c d k, (k < length d)%nat ->
  CF c d (S k) = crc_step (CF c d k) (bnth d k).
Proof.
  intros c d k Hk. unfold CF.
  assert (Hf : firstn (S k) (bZ d) = firstn k (bZ d) ++ [bnth d k]).
  { rewrite <- bZ_nth. apply (firstn_S_snoc (bZ d) 0 k).
    rewrite bZ_length. exact Hk. }
  rewrite Hf, crc_fold_app. reflexivity.
Qed.

Lemma CF_full : forall c d, CF c d (length d) = crc_fold c (bZ d).
Proof.
  intros c d. unfold CF. rewrite firstn_all2 by (rewrite bZ_length; lia).
  reflexivity.
Qed.


Lemma split8 : forall u, Z.lxor (Z.land u 255) (Z.shiftl (Z.shiftr u 8) 8) = u.
Proof.
  intro u. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec, Z.land_spec, Z.shiftl_spec by lia.
  replace 255 with (Z.ones 8) by reflexivity.
  destruct (Z.lt_ge_cases n 8) as [Hlt|Hge].
  - rewrite (Z.ones_spec_low 8 n) by lia.
    rewrite (Z.testbit_neg_r (Z.shiftr u 8) (n - 8)) by lia.
    destruct (Z.testbit u n); reflexivity.
  - rewrite (Z.ones_spec_high 8 n) by lia.
    rewrite Z.shiftr_spec by lia.
    replace (n - 8 + 8) with n by lia.
    destruct (Z.testbit u n); reflexivity.
Qed.

Lemma shiftr8_lxor_byte : forall c b, 0 <= b < 256 ->
  Z.shiftr (Z.lxor c b) 8 = Z.shiftr c 8.
Proof.
  intros c b Hb. rewrite shiftr_lxor.
  replace (Z.shiftr b 8) with 0; [apply Z.lxor_0_r|].
  symmetry. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small.
  change (2 ^ 8) with 256. lia.
Qed.

Lemma xtn8_shiftl8 : forall w, 0 <= w -> xtn 8 (Z.shiftl w 8) = w.
Proof.
  intros w Hw. replace 8 with (Z.of_nat 8) by reflexivity.
  apply xtn_shiftl_exact. exact Hw.
Qed.

Definition ctidx (c b : Z) : Z := Z.land (Z.lxor c b) 255.

Lemma ctidx_range : forall c b, 0 <= ctidx c b < 256.
Proof.
  intros c b. unfold ctidx. rewrite Zland_255. apply Z.mod_pos_bound. lia.
Qed.

Theorem crc_step_tab : forall c b, 0 <= c -> 0 <= b < 256 ->
  crc_step c b = Z.lxor (crc_tab (ctidx c b)) (Z.shiftr c 8).
Proof.
  intros c b Hc Hb.
  assert (Hu : 0 <= Z.lxor c b) by (apply Z.lxor_nonneg; lia).
  unfold crc_step, crc_tab, ctidx.
  transitivity (Z.lxor (xtn 8 (Z.land (Z.lxor c b) 255))
                       (xtn 8 (Z.shiftl (Z.shiftr (Z.lxor c b) 8) 8))).
  { rewrite <- xtn_xor. f_equal. symmetry. apply split8. }
  f_equal. rewrite xtn8_shiftl8 by (apply Z.shiftr_nonneg; exact Hu).
  apply shiftr8_lxor_byte. exact Hb.
Qed.

Lemma crc_tab_range : forall i, 0 <= i < 4294967296 -> 0 <= crc_tab i < 4294967296.
Proof. intros i Hi. unfold crc_tab. apply xtn_range. exact Hi. Qed.

Lemma crc_tab_range256 : forall i, 0 <= i < 256 -> 0 <= crc_tab i < 4294967296.
Proof. intros i Hi. apply crc_tab_range. lia. Qed.


Definition ctabbyte (f : Z -> Z) (j : Z) : byte :=
  Z_to_bv 8 ((f (j / 4) / 2 ^ (8 * (j mod 4))) mod 256).

Definition ctabword (f : Z -> Z) (i : Z) : list byte :=
  [ctabbyte f (4 * i); ctabbyte f (4 * i + 1);
   ctabbyte f (4 * i + 2); ctabbyte f (4 * i + 3)].

Lemma div4_off : forall i r, 0 <= r < 4 -> (4 * i + r) / 4 = i /\ (4 * i + r) mod 4 = r.
Proof.
  intros i r Hr. replace (4 * i + r) with (r + i * 4) by ring. split.
  - rewrite Z.div_add by lia. rewrite (Z.div_small r 4) by lia. lia.
  - rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma lor_shiftl8_byte : forall b X, 0 <= b < 256 -> 0 <= X ->
  Z.lor b (Z.shiftl X 8) = b + 256 * X.
Proof.
  intros b X Hb HX.
  assert (Hd : Z.land b (Z.shiftl X 8) = 0)
    by (apply (land_shiftl_disj b X 8); [change (2 ^ 8) with 256; lia | lia | lia]).
  rewrite (lor_lxor_disj b (Z.shiftl X 8) Hd).
  rewrite <- Z.add_nocarry_lxor by exact Hd.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. ring.
Qed.

Lemma ctabword_len : forall f i, length (ctabword f i) = 4%nat.
Proof. reflexivity. Qed.

Lemma shiftr_lt64 : forall a k, 0 <= k -> 0 <= a < 2 ^ 64 -> 0 <= Z.shiftr a k < 2 ^ 64.
Proof. intros a k Hk Ha. apply (Zshiftr_lt_pow2 a k 64); lia. Qed.

Lemma land255_lt : forall a, 0 <= Z.land a 255 < 256.
Proof. intro a. rewrite Zland_255. apply Z.mod_pos_bound. lia. Qed.


Lemma probe_step_tab_0 : crc_step 0 0 = Z.lxor (crc_tab 0) 0.
Proof. rewrite (crc_step_tab 0 0) by lia. reflexivity. Qed.

Lemma probe_step_tab_val : crc_step 4294967295 49 = 2082672712.
Proof. vm_compute. reflexivity. Qed.

Lemma shiftr_lt32 : forall a k, 0 <= k -> 0 <= a < 4294967296 ->
  0 <= Z.shiftr a k < 4294967296.
Proof.
  intros a k Hk Ha. change 4294967296 with (2 ^ 32) in *.
  apply (Zshiftr_lt_pow2 a k 32); lia.
Qed.

Lemma ctidx_comm : forall c b, Z.land (Z.lxor b c) 255 = ctidx c b.
Proof. intros c b. unfold ctidx. rewrite Z.lxor_comm. reflexivity. Qed.

Lemma crc_step_tab_c : forall c b, 0 <= c -> 0 <= b < 256 ->
  crc_step c b = Z.lxor (Z.shiftr c 8) (crc_tab (ctidx c b)).
Proof.
  intros c b Hc Hb. rewrite (crc_step_tab c b Hc Hb). apply Z.lxor_comm.
Qed.
End ZChkCrc.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32Base.ZChkCrc.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ListFacts.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.

Module CrcBraid.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Btauto.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma xtnl_locked : { f : nat -> Z -> Z | f = xtn }. Proof. exists xtn. reflexivity. Qed.
Definition xtnl : nat -> Z -> Z := proj1_sig xtnl_locked.
Lemma xtnl_eq : xtnl = xtn. Proof. exact (proj2_sig xtnl_locked). Qed.
Lemma xtnl_at : forall n c, xtnl n c = xtn n c. Proof. intros. rewrite xtnl_eq. reflexivity. Qed.

Lemma xtnl_xor : forall n a b, xtnl n (Z.lxor a b) = Z.lxor (xtnl n a) (xtnl n b).
Proof. intros. rewrite !xtnl_at. apply xtn_xor. Qed.
Lemma xtnl_0 : forall n, xtnl n 0 = 0.
Proof. intros. rewrite xtnl_at. apply xtn_0. Qed.
Lemma xtnl_range : forall n c, 0 <= c < 4294967296 -> 0 <= xtnl n c < 4294967296.
Proof. intros. rewrite xtnl_at. apply xtn_range. assumption. Qed.

Ltac xor_ac :=
  apply Z.bits_inj'; intros ?n ?Hn; rewrite !Z.lxor_spec;
  repeat match goal with |- context [Z.testbit ?x ?m] => generalize (Z.testbit x m); intro end;
  btauto.

Definition comb5 (x0 x1 x2 x3 x4 : Z) : Z :=
  Z.lxor (xtnl 160 x0) (Z.lxor (xtnl 128 x1) (Z.lxor (xtnl 96 x2) (Z.lxor (xtnl 64 x3) (xtnl 32 x4)))).

Lemma comb5_xor : forall a0 a1 a2 a3 a4 b0 b1 b2 b3 b4,
  comb5 (Z.lxor a0 b0) (Z.lxor a1 b1) (Z.lxor a2 b2) (Z.lxor a3 b3) (Z.lxor a4 b4)
  = Z.lxor (comb5 a0 a1 a2 a3 a4) (comb5 b0 b1 b2 b3 b4).
Proof. intros. unfold comb5. rewrite !xtnl_xor. xor_ac. Qed.

Lemma comb5_0 : comb5 0 0 0 0 0 = 0.
Proof. unfold comb5. rewrite !xtnl_0. reflexivity. Qed.

Lemma comb5_shift : forall x0 x1 x2 x3 x4,
  comb5 (xtnl 160 x0) (xtnl 160 x1) (xtnl 160 x2) (xtnl 160 x3) (xtnl 160 x4)
  = xtnl 160 (comb5 x0 x1 x2 x3 x4).
Proof.
  intros. unfold comb5. rewrite !xtnl_xor. rewrite !xtnl_at.
  rewrite <- !xtn_add. cbn [Nat.add]. reflexivity.
Qed.

Lemma crc_word4 : forall q b0 b1 b2 b3,
  0 <= b0 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 ->
  crc_step (crc_step (crc_step (crc_step q b0) b1) b2) b3 = xtnl 32 (Z.lxor q (wordLE b0 b1 b2 b3)).
Proof. intros. rewrite xtnl_at. apply crc_step4; assumption. Qed.

Lemma fold_word : forall q b0 b1 b2 b3,
  0 <= b0 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 ->
  crc_fold q [b0; b1; b2; b3] = xtnl 32 (Z.lxor q (wordLE b0 b1 b2 b3)).
Proof. intros. cbn [crc_fold fold_left]. apply crc_word4; assumption. Qed.

Lemma fold_block : forall q b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19,
  Forall (fun b => 0 <= b) [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19] ->
  crc_fold q [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19]
  = Z.lxor (xtnl 160 q) (comb5 (wordLE b0 b1 b2 b3) (wordLE b4 b5 b6 b7) (wordLE b8 b9 b10 b11)
                            (wordLE b12 b13 b14 b15) (wordLE b16 b17 b18 b19)).
Proof.
  intros. repeat match goal with H : Forall _ (_ :: _) |- _ => inversion_clear H end.
  change [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19]
    with ([b0;b1;b2;b3] ++ ([b4;b5;b6;b7] ++ ([b8;b9;b10;b11] ++ ([b12;b13;b14;b15] ++ [b16;b17;b18;b19])))).
  rewrite !crc_fold_app. rewrite !fold_word by assumption.
  unfold comb5. rewrite !xtnl_at. rewrite !xtn_xor. rewrite <- !xtn_add. cbn [Nat.add].
  xor_ac.
Qed.

Definition lane_step (l w : Z) : Z := xtnl 160 (Z.lxor l w).

Lemma lane_step_range : forall l w, 0 <= l < 4294967296 -> 0 <= w < 4294967296 ->
  0 <= lane_step l w < 4294967296.
Proof. intros. unfold lane_step. apply xtnl_range. apply lxor_bound32; assumption. Qed.

Lemma lane_step_braid : forall x, 0 <= x < 4294967296 ->
  braid_round4 (byteZ x 0) (byteZ x 1) (byteZ x 2) (byteZ x 3) = xtnl 160 x.
Proof.
  intros x Hx. rewrite braid_round4_xtn by (apply (proj1 (byteZ_range _ _))).
  rewrite wordLE_bytes by exact Hx. symmetry. apply xtnl_at.
Qed.

Definition combine (l0 l1 l2 l3 l4 w0 w1 w2 w3 w4 : Z) : Z :=
  xtnl 32 (Z.lxor (xtnl 32 (Z.lxor (xtnl 32 (Z.lxor (xtnl 32 (Z.lxor (xtnl 32 (Z.lxor l0 w0)) (Z.lxor l1 w1))) (Z.lxor l2 w2))) (Z.lxor l3 w3))) (Z.lxor l4 w4)).

Lemma combine_split : forall l0 l1 l2 l3 l4 w0 w1 w2 w3 w4,
  combine l0 l1 l2 l3 l4 w0 w1 w2 w3 w4 = Z.lxor (comb5 l0 l1 l2 l3 l4) (comb5 w0 w1 w2 w3 w4).
Proof.
  intros. unfold combine, comb5. rewrite !xtnl_at.
  rewrite !xtn_xor. rewrite <- !xtn_add. cbn [Nat.add].
  xor_ac.
Qed.

Definition binv (l0 l1 l2 l3 l4 q : Z) : Prop := comb5 l0 l1 l2 l3 l4 = xtnl 160 q.

Lemma binv_init : forall c, binv c 0 0 0 0 c.
Proof. intros c. unfold binv, comb5. rewrite !xtnl_0, !Z.lxor_0_r. reflexivity. Qed.

Lemma binv_step : forall l0 l1 l2 l3 l4 q w0 w1 w2 w3 w4 q',
  binv l0 l1 l2 l3 l4 q ->
  q' = Z.lxor (xtnl 160 q) (comb5 w0 w1 w2 w3 w4) ->
  binv (lane_step l0 w0) (lane_step l1 w1) (lane_step l2 w2) (lane_step l3 w3) (lane_step l4 w4) q'.
Proof.
  intros l0 l1 l2 l3 l4 q w0 w1 w2 w3 w4 q' HI Hq. unfold binv in *. unfold lane_step.
  rewrite comb5_shift, comb5_xor, HI, Hq. reflexivity.
Qed.

Lemma binv_combine : forall l0 l1 l2 l3 l4 q w0 w1 w2 w3 w4,
  binv l0 l1 l2 l3 l4 q ->
  combine l0 l1 l2 l3 l4 w0 w1 w2 w3 w4 = Z.lxor (xtnl 160 q) (comb5 w0 w1 w2 w3 w4).
Proof. intros * HI. rewrite combine_split. unfold binv in HI. rewrite HI. reflexivity. Qed.

Lemma probe_fold_block :
  crc_fold 305419896 [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20]
  = Z.lxor (xtn 160 305419896)
      (Z.lxor (xtn 160 (wordLE 1 2 3 4)) (Z.lxor (xtn 128 (wordLE 5 6 7 8)) (Z.lxor (xtn 96 (wordLE 9 10 11 12))
        (Z.lxor (xtn 64 (wordLE 13 14 15 16)) (xtn 32 (wordLE 17 18 19 20)))))).
Proof. vm_compute. reflexivity. Qed.
End CrcBraid.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32Base.CrcBraid.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CrcRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrcRod.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".

Definition FT : nat -> Z -> Z := fun f x =>
  match f with 0%nat => crc_tab (x mod 256) | S k => braid_tab k (x mod 256) end.

Lemma FT0_small : forall x, 0 <= x < 256 -> FT 0 x = crc_tab x.
Proof. intros x Hx. unfold FT. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma FT_bound : forall f x, 0 <= FT f x < 2 ^ 32.
Proof.
  intros f x. unfold FT. destruct f.
  - apply crc_tab_range. apply Z.mod_pos_bound. lia.
  - apply braid_tab_range. apply Z.mod_pos_bound. lia.
Qed.

Lemma step_eq : forall c b, 0 <= c -> 0 <= b < 256 ->
  Z.lxor (c / 2 ^ 8) (crc_tab ((Z.lxor b c) mod 2 ^ 8 mod 256)) = crc_step c b.
Proof.
  intros c b Hc Hb. rewrite Z.mod_mod by lia.
  rewrite (crc_step_tab_c c b Hc Hb). rewrite Z.shiftr_div_pow2 by lia. f_equal.
  unfold ctidx. f_equal. rewrite Z.lxor_comm. change 255 with (Z.ones 8).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma In_skipn_w {A} (x : A) : forall i (l : list A), In x (skipn i l) -> In x l.
Proof.
  induction i as [|i IH]; intros [|y l] H; cbn in H; try exact H.
  right. apply IH. exact H.
Qed.

Lemma crc_step_range : forall c b, 0 <= c < 2 ^ 32 -> 0 <= b < 256 -> 0 <= crc_step c b < 2 ^ 32.
Proof. intros. unfold crc_step. apply xtn_range. apply lxor_bound32; lia. Qed.

Lemma mod64_mod32 : forall a, (a mod 2 ^ 64) mod 2 ^ 32 = a mod 2 ^ 32.
Proof.
  intros a. rewrite <- Znumtheory.Zmod_div_mod; try lia.
  exists (2 ^ 32). reflexivity.
Qed.

Lemma byteZ_0 : forall x, (x mod 2 ^ 8) mod 256 = byteZ (x mod 2 ^ 32) 0.
Proof.
  intros x. unfold byteZ. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change 256 with (2 ^ 8).
  rewrite Z.mod_mod by lia. rewrite <- Znumtheory.Zmod_div_mod; try lia. exists (2 ^ 24); reflexivity.
Qed.

Lemma byteZ_k : forall x k, 0 <= k ->
  ((x mod 2 ^ 32) / 2 ^ k mod 2 ^ 8) mod 256 = Z.land (Z.shiftr (x mod 2 ^ 32) k) 255.
Proof.
  intros x k Hk. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change 256 with (2 ^ 8).
  rewrite Z.mod_mod by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma byteZ_1 : forall x, ((x mod 2 ^ 32) / 2 ^ 8 mod 2 ^ 8) mod 256 = byteZ (x mod 2 ^ 32) 1.
Proof. intros. unfold byteZ. apply byteZ_k; lia. Qed.
Lemma byteZ_2 : forall x, ((x mod 2 ^ 32) / 2 ^ 16 mod 2 ^ 8) mod 256 = byteZ (x mod 2 ^ 32) 2.
Proof. intros. unfold byteZ. apply byteZ_k; lia. Qed.
Lemma byteZ_3 : forall x, ((x mod 2 ^ 32) / 2 ^ 24) mod 256 = byteZ (x mod 2 ^ 32) 3.
Proof.
  intros x. unfold byteZ. cbn [Z.of_nat Z.mul Pos.mul Pos.of_succ_nat].
  rewrite Z.shiftr_div_pow2 by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  reflexivity.
Qed.

Lemma braid_round4_fold : forall a b c d,
  braid_round4 a b c d = Z.lxor (braid_tab 0 a) (Z.lxor (braid_tab 1 b) (Z.lxor (braid_tab 2 c) (braid_tab 3 d))).
Proof. intros. reflexivity. Qed.

Lemma lane_bridge : forall w r x t0 t1 t2 t3 e,
  0 <= w < 2 ^ 32 -> 0 <= r ->
  x = Z.lxor (szwrap 32 w) r ->
  t0 = braid_tab 0 ((x mod 2 ^ 8) mod 256) ->
  t1 = braid_tab 1 (((x mod 2 ^ 32) / 2 ^ 8 mod 2 ^ 8) mod 256) ->
  t2 = braid_tab 2 (((x mod 2 ^ 32) / 2 ^ 16 mod 2 ^ 8) mod 256) ->
  t3 = braid_tab 3 (((x mod 2 ^ 32) / 2 ^ 24) mod 256) ->
  e mod 2 ^ 32 = Z.lxor t0 (Z.lxor t1 (Z.lxor t2 t3)) ->
  e mod 2 ^ 32 = lane_step (r mod 2 ^ 32) w.
Proof.
  intros w r x t0 t1 t2 t3 e Hw Hr Hx H0 H1 H2 H3 He.
  assert (Hxm : x mod 2 ^ 32 = Z.lxor w (r mod 2 ^ 32)).
  { subst x. rewrite lxor_mod, szwrap_eqm, (Z.mod_small w) by lia. reflexivity. }
  rewrite He, H0, H1, H2, H3. rewrite byteZ_0, byteZ_1, byteZ_2, byteZ_3.
  rewrite <- braid_round4_fold.
  rewrite lane_step_braid by (apply Z.mod_pos_bound; lia).
  rewrite Hxm. unfold lane_step. rewrite Z.lxor_comm. reflexivity.
Qed.

Lemma lane_close : forall t0 t1 t2 t3,
  0 <= t0 < 2 ^ 32 -> 0 <= t1 < 2 ^ 32 -> 0 <= t2 < 2 ^ 32 -> 0 <= t3 < 2 ^ 32 ->
  (Z.lxor (szwrap 32 t2) (Z.lxor (Z.lxor (szwrap 32 t0) (szwrap 32 t3)) (szwrap 32 t1))) mod 2 ^ 32
  = Z.lxor t0 (Z.lxor t1 (Z.lxor t2 t3)).
Proof.
  intros t0 t1 t2 t3 B0 B1 B2 B3.
  rewrite !lxor_mod, !szwrap_eqm by lia.
  rewrite (Z.mod_small t0), (Z.mod_small t1), (Z.mod_small t2), (Z.mod_small t3) by lia.
  xor_ac.
Qed.

Lemma lor_shl8 : forall a b, 0 <= a < 256 -> 0 <= b -> Z.lor a (Z.shiftl b 8) = a + 256 * b.
Proof.
  intros a b Ha Hb.
  assert (D : Z.land a (Z.shiftl b 8) = 0) by (apply land_shiftl_disj; [cbn; lia| lia | lia]).
  rewrite <- (Z.lxor_lor a _ D), <- (Z.add_nocarry_lxor a _ D), Z.shiftl_mul_pow2 by lia.
  change (2 ^ 8) with 256. lia.
Qed.

Lemma wstep : forall c, 0 <= c < 2 ^ 32 ->
  Z.lxor (c / 2 ^ 8) (crc_tab ((c mod 2 ^ 8) mod 256)) = xtn 8 c.
Proof.
  intros c Hc. rewrite Z.mod_mod by lia.
  replace (xtn 8 c) with (crc_step c 0) by (unfold crc_step; rewrite Z.lxor_0_r; reflexivity).
  rewrite (crc_step_tab_c c 0) by lia. rewrite Z.shiftr_div_pow2 by lia. f_equal.
  unfold ctidx. rewrite Z.lxor_0_r. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma mod8_of_mod32 : forall v, v mod 2 ^ 8 = (v mod 2 ^ 32) mod 2 ^ 8.
Proof. intros v. symmetry. rewrite <- Znumtheory.Zmod_div_mod; try lia. exists (2 ^ 24); reflexivity. Qed.

Lemma sh8_small : forall v, 0 <= (v mod 2 ^ 32) / 2 ^ 8 < 2 ^ 32.
Proof.
  intros v. pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma DS_A : forall v,
  (Z.lxor ((v mod 2 ^ 32) / 2 ^ 8) (szwrap 32 (crc_tab ((v mod 2 ^ 8) mod 256)))) mod 2 ^ 32 = xtn 8 (v mod 2 ^ 32).
Proof.
  intros v. pose proof (sh8_small v). pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)).
  assert (HT : 0 <= crc_tab ((v mod 2 ^ 8) mod 256) < 2 ^ 32) by (unfold crc_tab; apply xtn_range; pose proof (Z.mod_pos_bound (v mod 2 ^ 8) 256); lia).
  rewrite lxor_mod, szwrap_eqm, (Z.mod_small (_ / _)), (Z.mod_small (crc_tab _)) by lia.
  rewrite (mod8_of_mod32 v). apply wstep. lia.
Qed.

Lemma DS_B : forall v,
  (Z.lxor (szwrap 32 (crc_tab ((v mod 2 ^ 8) mod 256))) ((v mod 2 ^ 32) / 2 ^ 8)) mod 2 ^ 32 = xtn 8 (v mod 2 ^ 32).
Proof. intros v. rewrite Z.lxor_comm. apply DS_A. Qed.

Lemma DS_AX : forall v x,
  (Z.lxor (Z.lxor ((v mod 2 ^ 32) / 2 ^ 8) x) (szwrap 32 (crc_tab ((v mod 2 ^ 8) mod 256)))) mod 2 ^ 32
  = Z.lxor (xtn 8 (v mod 2 ^ 32)) (x mod 2 ^ 32).
Proof.
  intros v x. rewrite <- DS_A. rewrite <- (lxor_mod _ x) by lia. f_equal. xor_ac.
Qed.

Lemma DS_fin : forall v,
  Z.lxor (crc_tab ((v mod 2 ^ 8) mod 256)) ((v mod 2 ^ 32) / 2 ^ 8) = xtn 8 (v mod 2 ^ 32).
Proof. intros v. rewrite Z.lxor_comm, (mod8_of_mod32 v). apply wstep. apply Z.mod_pos_bound. lia. Qed.

Lemma xtn8_4 : forall c, xtn 8 (xtn 8 (xtn 8 (xtn 8 c))) = xtnl 32 c.
Proof. intros c. rewrite xtnl_at. rewrite <- !xtn_add. reflexivity. Qed.

Lemma xw_mod : forall w r, 0 <= w < 2 ^ 32 ->
  (Z.lxor (szwrap 32 w) r) mod 2 ^ 32 = Z.lxor (r mod 2 ^ 32) w.
Proof. intros w r Hw. rewrite lxor_mod, szwrap_eqm, (Z.mod_small w) by lia. apply Z.lxor_comm. Qed.


Lemma step_eqR : forall c b, 0 <= c -> 0 <= b < 256 ->
  Z.lxor (crc_tab ((Z.lxor b c) mod 2 ^ 8 mod 256)) (c / 2 ^ 8) = crc_step c b.
Proof. intros. rewrite Z.lxor_comm. apply step_eq; assumption. Qed.

Lemma land_m8_lo : forall x, 0 <= x < 8 -> Z.land x (-8) = 0.
Proof.
  intros x Hx.
  assert (E : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7) by lia.
  repeat (destruct E as [->|E]; [reflexivity|]). subst. reflexivity.
Qed.
Lemma land_m8_hi : forall x, 8 <= x < 16 -> Z.land x (-8) = 8.
Proof.
  intros x Hx.
  assert (E : x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15) by lia.
  repeat (destruct E as [->|E]; [reflexivity|]). subst. reflexivity.
Qed.

Definition c0_of (crc : Z) : Z := (Z.lxor crc (-1)) mod 2 ^ 32.
Lemma c0_range : forall crc, 0 <= c0_of crc < 2 ^ 32.
Proof. intros. unfold c0_of. apply Z.mod_pos_bound. lia. Qed.
Definition MASK : Z := 4294967295.
Definition hide (Q : Prop) : Prop := Q.
