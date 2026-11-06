(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainR.v (commit 67deba317dfb, blob e7c4b7ca0d39) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFeu AFey.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMdrainQ.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.

Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma len_of_bytes : forall (l : list batch) (bound : Z),
(forall b, In b l -> kBatchBytes <= b_bytes b) -> sum_bytes l <= bound ->
kBatchBytes * Z.of_nat (length l) <= bound.
Proof.
induction l as [|b t IH]; intros bound HB HS; cbn [length]; [cbn in HS |- *; unfold kBatchBytes; lia|].
rewrite AFey.sum_bytes_cons in HS.
assert (HT : sum_bytes t <= bound - b_bytes b) by lia.
pose proof (IH (bound - b_bytes b) (fun b' Hb' => HB b' (or_intror Hb')) HT) as R.
pose proof (HB b (or_introl eq_refl)). rewrite Nat2Z.inj_succ. unfold kBatchBytes in *. lia.
Qed.

Section lists.
Variable ly : alayout.
Variables (L0 Lk ex : list batch).

Hypothesis HB0 : forall b, In b L0 ->
  kHighMemBeg <= addrb ly b /\ addrb ly b + kBatchBytes <= ASAN_CEIL /\ addrb ly b mod 8192 = 0 /\
  (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Hypothesis HN0 : forall k, In k (flat_map b_items L0) -> 0 <= ck_n k.
Hypothesis HS0 : sum_bytes L0 <= 2 ^ 31.

Hypothesis HIN : forall b, In b (Lk ++ ex) -> In (b_self b) (map b_self L0).
Hypothesis HSUM : sum_bytes Lk + kBatchBytes * Z.of_nat (length ex) = sum_bytes L0.
Hypothesis HEX : forall b, In b ex -> b_items b = [].
Hypothesis HITEMS : flat_map b_items Lk = flat_map b_items L0.

Lemma addr_in : forall b, In b (Lk ++ ex) ->
kHighMemBeg <= addrb ly b /\ addrb ly b + kBatchBytes <= ASAN_CEIL /\ addrb ly b mod 8192 = 0.
Proof.
intros b Hb. pose proof (HIN b Hb) as HS.
apply in_map_iff in HS as (b0 & HE & Hb0). destruct (HB0 b0 Hb0) as (A1 & A2 & A3 & _).
unfold addrb in *. rewrite <- HE in *. split; [exact A1 | split; [exact A2 | exact A3]].
Qed.

Lemma b_bytes_lb_L0 : forall b, In b L0 -> kBatchBytes <= b_bytes b.
Proof.
intros b Hb. apply b_bytes_lb. intros k Hk. apply HN0. apply in_flat_map. exists b. split; [exact Hb | exact Hk].
Qed.

Lemma b_bytes_lb_Lk : forall b, In b Lk -> kBatchBytes <= b_bytes b.
Proof.
intros b Hb. apply b_bytes_lb. intros k Hk. apply HN0. rewrite <- HITEMS. apply in_flat_map.
exists b. split; [exact Hb | exact Hk].
Qed.

Lemma b_bytes_ex : forall b, In b ex -> b_bytes b = kBatchBytes.
Proof. intros b Hb. unfold b_bytes. rewrite (HEX b Hb). cbn [fold_right]. lia. Qed.

Lemma len_L0 : Z.of_nat (length L0) <= 2 ^ 18.
Proof.
pose proof (len_of_bytes L0 (2 ^ 31) b_bytes_lb_L0 HS0) as R. unfold kBatchBytes in R. lia.
Qed.

Lemma kept_len_range : 0 <= Z.of_nat (length Lk) <= 2 ^ 40.
Proof.
pose proof (len_of_bytes Lk (2 ^ 31) b_bytes_lb_Lk) as R.
assert (HK : sum_bytes Lk <= 2 ^ 31).
{ assert (0 <= kBatchBytes * Z.of_nat (length ex)) by (unfold kBatchBytes; lia). lia. }
pose proof (R HK) as R2. unfold kBatchBytes in R2. lia.
Qed.

Lemma sum_nonneg_of : forall l : list batch, (forall b, In b l -> kBatchBytes <= b_bytes b) -> 0 <= sum_bytes l.
Proof.
induction l as [|b t IH]; intros HB.
- rewrite AFey.sum_bytes_nil. lia.
- rewrite AFey.sum_bytes_cons.
  pose proof (HB b (or_introl eq_refl)) as H1.
  pose proof (IH (fun b' Hb' => HB b' (or_intror Hb'))) as H2.
  unfold kBatchBytes in H1. lia.
Qed.

Lemma ext_len_range : 0 <= Z.of_nat (length ex) <= 2 ^ 40.
Proof.
pose proof (sum_nonneg_of Lk b_bytes_lb_Lk) as HK. unfold kBatchBytes in *. lia.
Qed.

Lemma fa_range : forall l, (forall b, In b l -> In b (Lk ++ ex)) ->
0 <= fa ly l 0 < ASAN_CEIL /\ fa ly l 0 mod 8192 = 0.
Proof.
intros [|b t] Hl; cbn [fa].
- ceil. unfold ASAN_CEIL. splits; [lia | lia | reflexivity].
- destruct (addr_in b (Hl b (or_introl eq_refl))) as (A1 & A2 & A3).
  unfold kHighMemBeg, kBatchBytes in *. split; [lia | exact A3].
Qed.

Lemma la_range : forall l, (forall b, In b l -> In b (Lk ++ ex)) ->
0 <= la ly l < ASAN_CEIL /\ la ly l mod 8192 = 0.
Proof.
intros l Hl. unfold la. destruct (rev l) as [|b t] eqn:ER.
- ceil. unfold ASAN_CEIL. splits; [lia | lia | reflexivity].
- assert (Hin : In b l).
  { rewrite <- (rev_involutive l), ER. cbn [rev]. apply in_app_iff. right. left. reflexivity. }
  destruct (addr_in b (Hl b Hin)) as (A1 & A2 & A3).
  unfold kHighMemBeg, kBatchBytes in *. split; [lia | exact A3].
Qed.

Lemma kept_bytes_range : 0 <= sum_bytes L0 - kBatchBytes * Z.of_nat (length ex) <= 2 ^ 31.
Proof.
pose proof (sum_nonneg_of Lk b_bytes_lb_Lk) as HK.
pose proof HSUM as HS. pose proof HS0 as HB.
assert (HL : (0 <= Z.of_nat (length ex))%Z) by apply Nat2Z.is_nonneg.
unfold kBatchBytes in *. lia.
Qed.

End lists.
End d.
