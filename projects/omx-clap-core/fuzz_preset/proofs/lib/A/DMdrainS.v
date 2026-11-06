(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainS.v (commit 67deba317dfb, blob 5476445454b6) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMdrainQ DMdrainR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section vals.
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

Local Notation lcnt := (Z.of_nat (length Lk)).
Local Notation lfirst := (fa ly Lk 0).
Local Notation lbytes := (sum_bytes L0 - kBatchBytes * Z.of_nat (length ex)).
Local Notation tcnt := (Z.of_nat (length ex)).
Local Notation tlast := (la ly ex).

Lemma rj_Hl : 0 <= lcnt <= 2 ^ 40 /\ 0 <= lfirst < ASAN_CEIL /\ lfirst mod 8192 = 0 /\ 0 <= lbytes <= 2 ^ 31.
Proof.
assert (KL : 0 <= Z.of_nat (length Lk) <= 2 ^ 40) by (eapply kept_len_range; eassumption).
assert (F : 0 <= fa ly Lk 0 < ASAN_CEIL /\ fa ly Lk 0 mod 8192 = 0).
{ eapply fa_range; try eassumption. intros b Hb. apply in_app_iff. left. exact Hb. }
assert (KB : 0 <= sum_bytes L0 - kBatchBytes * Z.of_nat (length ex) <= 2 ^ 31)
  by (eapply kept_bytes_range; eassumption).
destruct F as [F1 F2]. splits; first [exact F2 | lia].
Qed.

Lemma rj_Ht : 0 <= tcnt <= 2 ^ 40 /\ 0 <= tlast < ASAN_CEIL /\ tlast mod 8192 = 0.
Proof.
assert (EL : 0 <= Z.of_nat (length ex) <= 2 ^ 40) by (eapply ext_len_range; eassumption).
assert (L : 0 <= la ly ex < ASAN_CEIL /\ la ly ex mod 8192 = 0).
{ eapply la_range; try eassumption. intros b Hb. apply in_app_iff. right. exact Hb. }
destruct L as [L1 L2]. splits; first [exact L2 | lia].
Qed.

Lemma rj_kept_bytes : sum_bytes Lk = lbytes.
Proof. lia. Qed.

End vals.
End d.
